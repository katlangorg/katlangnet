using System.Text;

namespace KatLang.Tests;

/// <summary>
/// Generates and pins <c>lean/CoreTests/FrontEndDecisionCases.lean</c>: the Lean front-end specification functions
/// checked against the C# front end's own decisions on every program of the four differential corpora
/// (<see cref="SemanticExplorerCorpus"/>, <c>LanguageSpecCorpus</c>, the SEM-2B generated corpus's identity-prelude
/// members and the tutorial's source fences).
///
/// <para>The other generated corpora hand Lean a tree the C# front end already elaborated, so they compare
/// EVALUATION of that tree. This one compares the elaboration decisions themselves: for each classified name the
/// owner chain C# resolved it in and C#'s verdict, guarded as <c>selectOwnedDeclaration chain name == …</c> and
/// <c>elaboratesToParameter chain name == …</c>; for each open head <c>elaborateOpenHead</c>; for each clause family
/// <c>familyLiftingSignature?</c>; for each candidate name of an inferring level <c>shouldTreatAsImplicitParam</c>;
/// for each forwarded binding <c>forwardingSource</c>; for each declaring level <c>conflictingOwnedNames</c> and, at
/// each innermost level, <c>validOwnedDeclarations</c>; and the whole <c>liftingSlotRole</c> table. See
/// <see cref="FrontEndDecisionCorpus"/> for what counts as C#'s decision and as its input.</para>
///
/// <para>If a C# decision changes, this test fails (regenerate and review the diff); if Lean's specification
/// function disagrees with the recorded decision, <c>lake build CoreTests</c> fails on the guard.</para>
///
/// Regenerate with:
///   $env:KATLANG_REGENERATE_FRONT_END_DECISIONS = "1"
///   dotnet test .\KatLang.slnx --filter FrontEndDecisionLeanArtifact
/// That run writes the artifact and then fails by design (see <see cref="ArtifactRegeneration"/>); review the
/// diff, clear the flag, rerun.
/// </summary>
public class FrontEndDecisionLeanArtifactTests
{
    private const string ArtifactRelativePath = "lean/CoreTests/FrontEndDecisionCases.lean";

    /// <summary>
    /// The supplied positions the role table is compared on: every position of the longest builtin signature and
    /// two surplus positions beyond it.
    /// </summary>
    private static readonly int RolePositions =
        Enum.GetValues<BuiltinId>().Max(static builtin => BuiltinRegistry.GetBuiltin(builtin).PlainSignature.Parameters.Count) + 2;

    [Fact]
    public void GeneratedLeanArtifact_MatchesCurrentFrontEndDecisions()
    {
        var expected = GenerateArtifact();
        var path = Path.Combine(RepoRoot.Find(), ArtifactRelativePath);
        var flag = RegenerationFlags.FrontEndDecisions;

        ArtifactRegeneration.VerifyOrRegenerate(
            flag,
            ArtifactRelativePath,
            regenerate: () => expected,
            verify: () =>
            {
                Assert.True(File.Exists(path),
                    $"{ArtifactRelativePath} is missing. Set {flag}=1 and rerun this test to generate it (that run fails by design).");

                var actual = File.ReadAllText(path).ReplaceLineEndings("\n");
                Assert.True(expected == actual,
                    $"{ArtifactRelativePath} is out of date with the C# front end's current decisions. " +
                    $"Set {flag}=1 and rerun this test to regenerate it (that run fails by design), review the diff, and run " +
                    "`lake build CoreTests` to check the Lean side. " +
                    SemanticExplorerLeanArtifactTests.DescribeFirstDifference(expected, actual));
            },
            afterRegenerating: "run `lake build CoreTests` to check the Lean side");
    }

    /// <summary>
    /// Pins which programs contribute nothing and why. A program leaves the differential only through one of the
    /// enumerated reasons, and the counts move only in a reviewed diff. A reviewed Lean/C# disagreement is excluded
    /// by exact id with its class and a witness; more than a handful is an owner review, not more exclusions.
    /// </summary>
    [Fact]
    public void SkippedPrograms_AreExactlyTheEnumeratedReasons()
    {
        var skipped = FrontEndDecisionCorpus.Programs
            .Where(static program => program.Skip is not null)
            .GroupBy(static program => (program.Corpus, Reason: program.Skip!.Value))
            .ToDictionary(static group => group.Key, static group => group.Count());

        Assert.Equal(
            new Dictionary<(string, FrontEndSkip), int>
            {
                [(FrontEndDecisionCorpus.ExplorerCorpus, FrontEndSkip.SyntaxError)] = ExpectedExplorerSyntaxErrors,
                [(FrontEndDecisionCorpus.LanguageSpecCorpus, FrontEndSkip.SyntaxError)] = ExpectedSpecSyntaxErrors,
                [(FrontEndDecisionCorpus.SemanticGeneratedCorpus, FrontEndSkip.SyntaxError)] = ExpectedSemanticGeneratedSyntaxErrors,
                [(FrontEndDecisionCorpus.TutorialCorpusName, FrontEndSkip.SyntaxError)] = ExpectedTutorialSyntaxErrors,
                [(FrontEndDecisionCorpus.TutorialCorpusName, FrontEndSkip.UnresolvedLoad)] = ExpectedTutorialUnresolvedLoads,
            },
            skipped.Where(static pair => pair.Key.Reason != FrontEndSkip.ReviewedDrift).ToDictionary());

        var known = FrontEndDecisionCorpus.Programs.Select(static program => $"{program.Corpus}/{program.Id}").ToHashSet(StringComparer.Ordinal);
        Assert.All(FrontEndDecisionCorpus.ReviewedDriftById, pair =>
        {
            Assert.True(known.Contains(pair.Key), $"{pair.Key} names no corpus program.");
            Assert.False(string.IsNullOrWhiteSpace(pair.Value.Class), pair.Key);
            Assert.False(string.IsNullOrWhiteSpace(pair.Value.Witness), pair.Key);
        });
        Assert.True(FrontEndDecisionCorpus.ReviewedDriftById.Count <= 5,
            "More than five programs excluded as reviewed drift: this needs an owner review, not more exclusions.");
    }

    private const int ExpectedExplorerSyntaxErrors = 7;
    private const int ExpectedSpecSyntaxErrors = 35;
    private const int ExpectedSemanticGeneratedSyntaxErrors = 4;
    private const int ExpectedTutorialSyntaxErrors = 3;
    private const int ExpectedTutorialUnresolvedLoads = 2;

    private const string CollectorShapeWitness = "forwarding-single-collector-by-shape";

    [Fact]
    public void CollectorShapeFinding_PinsBothNamesAndTheWrittenOccurrence()
    {
        var hits = from program in FrontEndDecisionCorpus.Programs
                   from level in program.Levels
                   from source in level.Forwardings
                   where source.Requested is not null
                   select (program.Corpus, program.Id, level.Index, source);
        Assert.Equal((FrontEndDecisionCorpus.LanguageSpecCorpus, CollectorShapeWitness, 2,
            new FrontEndForwarding("items", FrontEndForwardingKind.Own, 0, "xs")), Assert.Single(hits));
    }

    /// <summary>
    /// Coverage ratchet: the number of decisions each specification function is checked on may only be RAISED (or
    /// lowered in a reviewed diff that deliberately removes corpus cases), so a walk that silently stops reaching a
    /// kind of occurrence cannot pass.
    /// </summary>
    [Fact]
    public void CoverageRatchet_GuardedDecisionsCannotSilentlyShrink()
    {
        var totals = Totals.Of(FrontEndDecisionCorpus.Programs);

        Assert.True(totals.Programs >= MinimumPrograms, $"guarded programs {totals.Programs} < {MinimumPrograms}");
        Assert.True(totals.NameOccurrences >= MinimumNameOccurrences, $"name occurrences {totals.NameOccurrences} < {MinimumNameOccurrences}");
        Assert.True(totals.ParameterVerdicts >= MinimumParameterVerdicts, $"parameter verdicts {totals.ParameterVerdicts} < {MinimumParameterVerdicts}");
        Assert.True(totals.OpenHeads >= MinimumOpenHeads, $"open heads {totals.OpenHeads} < {MinimumOpenHeads}");
        Assert.True(totals.ParameterOpenHeads >= MinimumParameterOpenHeads, $"parameter-owned open heads {totals.ParameterOpenHeads} < {MinimumParameterOpenHeads}");
        Assert.True(totals.Families >= MinimumFamilies, $"clause families {totals.Families} < {MinimumFamilies}");
        Assert.True(totals.UnnameableFamilies >= MinimumUnnameableFamilies, $"unnameable families {totals.UnnameableFamilies} < {MinimumUnnameableFamilies}");
        Assert.True(totals.ForwardedLevels >= MinimumForwardedLevels, $"levels with a forwarded parameter {totals.ForwardedLevels} < {MinimumForwardedLevels}");
        Assert.True(totals.PromotionsOverChain >= MinimumPromotionsOverChain, $"promotion decisions over an owner chain {totals.PromotionsOverChain} < {MinimumPromotionsOverChain}");
        Assert.True(totals.PromotionsOverTree >= MinimumPromotionsOverTree, $"promotion decisions over an encoded tree {totals.PromotionsOverTree} < {MinimumPromotionsOverTree}");
        Assert.True(totals.PromotedNames >= MinimumPromotedNames, $"promoted names {totals.PromotedNames} < {MinimumPromotedNames}");
        Assert.True(totals.ResolvedThroughOpen >= MinimumResolvedThroughOpen, $"names resolved through an open {totals.ResolvedThroughOpen} < {MinimumResolvedThroughOpen}");
        Assert.True(totals.ForwardingOwn >= MinimumForwardingOwn, $"own forwarding sources {totals.ForwardingOwn} < {MinimumForwardingOwn}");
        Assert.True(totals.ForwardingCaptured >= MinimumForwardingCaptured, $"captured forwarding sources {totals.ForwardingCaptured} < {MinimumForwardingCaptured}");
        Assert.True(totals.ForwardingForwarded >= MinimumForwardingForwarded, $"forwarded forwarding sources {totals.ForwardingForwarded} < {MinimumForwardingForwarded}");
        Assert.True(totals.CollisionLevels >= MinimumCollisionLevels, $"collision-checked levels {totals.CollisionLevels} < {MinimumCollisionLevels}");
        Assert.True(totals.ConflictingLevels >= MinimumConflictingLevels, $"levels with a reported collision {totals.ConflictingLevels} < {MinimumConflictingLevels}");
        Assert.True(totals.ValidityChains >= MinimumValidityChains, $"validity-checked chains {totals.ValidityChains} < {MinimumValidityChains}");
        Assert.True(totals.GuardedAmbiguousOpen >= 9);
        Assert.True(totals.ForwardingUnavailable >= 4);
        Assert.Equal(0, totals.UnattributedLifts);
        Assert.Equal(0, totals.FinalTreeNoCounterpart);
    }

    private const int MinimumPrograms = 3976;
    private const int MinimumNameOccurrences = 17439;
    private const int MinimumParameterVerdicts = 6058;
    private const int MinimumOpenHeads = 92;
    private const int MinimumParameterOpenHeads = 9;
    private const int MinimumFamilies = 97;
    private const int MinimumUnnameableFamilies = 18;
    private const int MinimumForwardedLevels = 60;
    private const int MinimumPromotionsOverChain = 8214;
    private const int MinimumPromotionsOverTree = 64;
    private const int MinimumPromotedNames = 154;
    private const int MinimumResolvedThroughOpen = 33;
    private const int MinimumForwardingOwn = 33;
    private const int MinimumForwardingCaptured = 9;
    private const int MinimumForwardingForwarded = 92;
    private const int MinimumCollisionLevels = 222;
    private const int MinimumConflictingLevels = 8;
    private const int MinimumValidityChains = 210;

    /// <summary>
    /// MANUALLY REVIEWED goldens of the collector, one per kind of decision. Everything else in the artifact is
    /// recorded from C# and checked by Lean; these are checked against the language rules by a reader, so a
    /// change to how a chain is rebuilt or a verdict is read shows here as a reviewed diff, not as a regenerated
    /// file. Each expected text is the block the artifact holds for that program, with the block prefix `p`.
    /// </summary>
    [Theory]
    [MemberData(nameof(ReviewedGoldens))]
    public void Collector_RendersTheReviewedGolden(string source, string expected)
    {
        var program = FrontEndDecisionCorpus.Collect("golden", "reviewed", source);

        Assert.Null(program.Skip);
        Assert.Equal(
            expected.ReplaceLineEndings("\n"),
            RenderProgram(program).Replace(PrefixPlaceholder, "p", StringComparison.Ordinal));
    }

    public static IEnumerable<object[]> ReviewedGoldens()
    {
        // A captured ancestor parameter beats a farther property: the prelude alias `pi` is the outermost level. `Inner`'s
        // `pi` is owned by an enclosing parameter, so promotion is not asked about it; `Outer`'s declarations meet its
        // parameter.
        yield return new object[]
        {
            "Outer(pi) = {\n    Inner = pi + 1\n    Inner\n}\nOuter(7)",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["Outer"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := ["pi"], properties := ["Inner"] } :: p_0
            def p_2 : List OwnerLevel := { parameters := [], properties := [] } :: p_1
            #guard selectOwnedDeclaration p_2 "pi" == .parameter 1
            #guard elaboratesToParameter p_2 "pi" == true
            #guard selectOwnedDeclaration p_1 "Inner" == .property 0
            #guard elaboratesToParameter p_1 "Inner" == false
            #guard selectOwnedDeclaration p_0 "Outer" == .property 0
            #guard elaboratesToParameter p_0 "Outer" == false
            #guard promotes p_0 "Outer" == some false
            #guard ownedConflicts p_1 == []
            #guard validOwnedDeclarations p_2 == true

            """,
        };

        // A parameter-owned open head elaborates to a parameter read; the name it would have opened stays unowned. The
        // root's names resolve to its properties.
        yield return new object[]
        {
            "Lib = {\n    public X = 7\n}\nOther = {\n    public X = 8\n}\nF(Lib) = {\n    open Lib\n    X, Lib.X\n}\nF(Other)",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "Other", "F"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p_0
            def p_2 : List OwnerLevel := { parameters := [], properties := [] } :: p_1
            def p_3 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p_0
            def p_4 : List OwnerLevel := { parameters := [], properties := [] } :: p_3
            def p_5 : List OwnerLevel := { parameters := ["Lib"], properties := [] } :: p_0
            #guard selectOwnedDeclaration p_5 "Lib" == .parameter 0 -- x2
            #guard openHead? (elaborateOpenHead p_5 "Lib") == some (true, "Lib")
            #guard selectOwnedDeclaration p_5 "X" == .none -- x2
            #guard elaboratesToParameter p_5 "X" == false -- x2
            #guard elaboratesToParameter p_5 "Lib" == true
            #guard selectOwnedDeclaration p_0 "F" == .property 0
            #guard elaboratesToParameter p_0 "F" == false
            #guard selectOwnedDeclaration p_0 "Other" == .property 0
            #guard elaboratesToParameter p_0 "Other" == false
            #guard promotes p_0 "F" == some false
            #guard promotes p_0 "Other" == some false

            """,
        };

        // The never-called root's inferred name is a parameter for a reference and owns no open head (the callable chain
        // `p_0c`). Its phantom signature meets only the root's own declarations; promotion over the root's opening chain is
        // not asked, as the front end rejects the program (the path `Lib.Sub` is not public).
        yield return new object[]
        {
            "open Lib.Sub\nLib = {\n    Sub = {\n        public Q(x) = x + 1\n    }\n}\nQ(5)",
            """
            def p_0 : List OwnerLevel := { parameters := ["Q"], properties := ["Lib"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := [], properties := ["Sub"] } :: p_0
            def p_2 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p_1
            def p_3 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p_2
            def p_0c : List OwnerLevel := { parameters := [], properties := ["Lib"] } :: prelude
            #guard selectOwnedDeclaration p_0c "Lib" == .property 0
            #guard openHead? (elaborateOpenHead p_0c "Lib") == some (false, "Lib")
            #guard selectOwnedDeclaration p_3 "x" == .parameter 0
            #guard elaboratesToParameter p_3 "x" == true
            #guard selectOwnedDeclaration p_0 "Q" == .parameter 0
            #guard elaboratesToParameter p_0 "Q" == true
            -- promotion at level 0 of "Q" omitted (the program has an invalid open target)
            #guard ownedConflicts p_0 == []

            """,
        };

        // A forwarded parameter is recorded apart from the name-resolution parameters, and its source is a forwarded
        // parameter; a builtin is a prelude property, so it resolves.
        yield return new object[]
        {
            "G = count + 0\nG((1, 2, 3))",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["G"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["collection"] } :: p_0
            #guard selectOwnedDeclaration p_1 "count" == .property 2
            #guard elaboratesToParameter p_1 "count" == false
            #guard selectOwnedDeclaration p_0 "G" == .property 0
            #guard elaboratesToParameter p_0 "G" == false
            #guard promotes p_0 "G" == some false
            #guard promotes p_1 "count" == some false
            #guard forwardingSource p_1 true "collection" == .forwardedParameter

            """,
        };

        // A clause body's level owns its head's binders, and the family's lifting signature is the name its clauses agree
        // on.
        yield return new object[]
        {
            "F(0) = 1\nF(n) = 2\nF(1, 2)",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := [], properties := [] } :: p_0
            def p_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p_0
            #guard selectOwnedDeclaration p_0 "F" == .property 0
            #guard elaboratesToParameter p_0 "F" == false
            #guard promotes p_0 "F" == some false
            #guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

            """,
        };

        // A level whose chain writes an `open` asks promotion over the encoded pre-exposure tree, at its property path: `X`
        // resolves through the open, `y` is promoted.
        yield return new object[]
        {
            "Lib = {\n    public X = 7\n}\nF = {\n    open Lib\n    X + y\n}\nF(1)",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["Lib", "F"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := [], properties := ["X"] } :: p_0
            def p_2 : List OwnerLevel := { parameters := [], properties := [] } :: p_1
            def p_3 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p_0
            def p_tree : Expr :=
              .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "X" (alg [] [] [] [.num 7])] []), privateProp "F" (alg ["y"] [.resolve "Lib"] [] [(.binary .add (.resolve "X") (.param "y"))])] [(.call (.resolve "F") [.num 1])])
            def p_s3 : Option (Algorithm × EvalCtx) := treeSite p_tree [.property "F"]
            #guard selectOwnedDeclaration p_3 "Lib" == .property 1
            #guard openHead? (elaborateOpenHead p_3 "Lib") == some (false, "Lib")
            #guard selectOwnedDeclaration p_3 "X" == .none
            #guard elaboratesToParameter p_3 "X" == false
            #guard selectOwnedDeclaration p_3 "y" == .parameter 0
            #guard elaboratesToParameter p_3 "y" == true
            #guard selectOwnedDeclaration p_0 "F" == .property 0
            #guard elaboratesToParameter p_0 "F" == false
            #guard promotes p_0 "F" == some false
            #guard promotesIn p_s3 "X" == some false
            #guard promotesIn p_s3 "y" == some true

            """,
        };

        // Forwarding sources: `B` receives a forwarded `y`, the closed `C(y)` reuses its own `y`, `G` reuses the `y` of the
        // enclosing `F(y)`. `H`'s property `x` collides with its parameter `x`, which makes the chain of `x`'s body
        // invalid.
        yield return new object[]
        {
            "A = y + 1\nB = A * 2\nC(y) = A * 3\nF(y) = {\n    G = A * 10\n    G\n}\nH(x) = {\n    x = 1\n    x + 2\n}\nB(1) + C(2) + F(3) + H(4)",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["A", "B", "C", "F", "H"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p_0
            def p_2 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["y"] } :: p_0
            def p_3 : List OwnerLevel := { parameters := ["y"], properties := [] } :: p_0
            def p_4 : List OwnerLevel := { parameters := ["y"], properties := ["G"] } :: p_0
            def p_5 : List OwnerLevel := { parameters := [], properties := [] } :: p_4
            def p_6 : List OwnerLevel := { parameters := ["x"], properties := ["x"] } :: p_0
            def p_7 : List OwnerLevel := { parameters := [], properties := [] } :: p_6
            #guard selectOwnedDeclaration p_1 "y" == .parameter 0
            #guard elaboratesToParameter p_1 "y" == true
            #guard selectOwnedDeclaration p_2 "A" == .property 1
            #guard elaboratesToParameter p_2 "A" == false
            #guard selectOwnedDeclaration p_3 "A" == .property 1
            #guard elaboratesToParameter p_3 "A" == false
            #guard selectOwnedDeclaration p_5 "A" == .property 2
            #guard elaboratesToParameter p_5 "A" == false
            #guard selectOwnedDeclaration p_4 "G" == .property 0
            #guard elaboratesToParameter p_4 "G" == false
            #guard selectOwnedDeclaration p_6 "x" == .parameter 0
            #guard elaboratesToParameter p_6 "x" == true
            #guard selectOwnedDeclaration p_0 "B" == .property 0
            #guard elaboratesToParameter p_0 "B" == false
            #guard selectOwnedDeclaration p_0 "C" == .property 0
            #guard elaboratesToParameter p_0 "C" == false
            #guard selectOwnedDeclaration p_0 "F" == .property 0
            #guard elaboratesToParameter p_0 "F" == false
            #guard selectOwnedDeclaration p_0 "H" == .property 0
            #guard elaboratesToParameter p_0 "H" == false
            #guard promotes p_0 "B" == some false
            #guard promotes p_0 "C" == some false
            #guard promotes p_0 "F" == some false
            #guard promotes p_0 "H" == some false
            #guard promotes p_1 "y" == some true
            #guard promotes p_2 "A" == some false
            #guard forwardingSource p_2 true "y" == .forwardedParameter
            #guard forwardingSource p_3 false "y" == .ownParameter
            #guard promotes p_5 "A" == some false
            #guard forwardingSource p_5 true "y" == .capturedParameter 1
            #guard ownedConflicts p_4 == []
            #guard ownedConflicts p_6 == ["x"]
            #guard validOwnedDeclarations p_5 == true
            #guard validOwnedDeclarations p_7 == false

            """,
        };

        // The root's phantom `Q` is checked against the root's own declarations only: `F`'s property `Q` meets `F`'s
        // parameter over the CALLABLE chain `p_3c`, where it does not collide (over `p_3` it would collide with the
        // phantom).
        yield return new object[]
        {
            "Lib = {\n    public Q = 1\n}\nF(x) = {\n    Q = x\n    Q\n}\nQ + F(1)",
            """
            def p_0 : List OwnerLevel := { parameters := ["Q"], properties := ["Lib", "F"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := [], properties := ["Q"] } :: p_0
            def p_2 : List OwnerLevel := { parameters := [], properties := [] } :: p_1
            def p_3 : List OwnerLevel := { parameters := ["x"], properties := ["Q"] } :: p_0
            def p_4 : List OwnerLevel := { parameters := [], properties := [] } :: p_3
            def p_0c : List OwnerLevel := { parameters := [], properties := ["Lib", "F"] } :: prelude
            def p_3c : List OwnerLevel := { parameters := ["x"], properties := ["Q"] } :: p_0c
            def p_4c : List OwnerLevel := { parameters := [], properties := [] } :: p_3c
            #guard selectOwnedDeclaration p_4 "x" == .parameter 1
            #guard elaboratesToParameter p_4 "x" == true
            #guard selectOwnedDeclaration p_3 "Q" == .property 0
            #guard elaboratesToParameter p_3 "Q" == false
            #guard selectOwnedDeclaration p_0 "Q" == .parameter 0
            #guard elaboratesToParameter p_0 "Q" == true
            #guard selectOwnedDeclaration p_0 "F" == .property 0
            #guard elaboratesToParameter p_0 "F" == false
            #guard promotes p_0 "Q" == some true
            #guard promotes p_0 "F" == some false
            #guard ownedConflicts p_0 == []
            #guard ownedConflicts p_3c == []
            #guard validOwnedDeclarations p_4c == true

            """,
        };

    }

    private sealed record Totals(
        int Programs,
        int NameOccurrences,
        int ParameterVerdicts,
        int DotFallbacks,
        int OpenHeads,
        int ParameterOpenHeads,
        int Families,
        int UnnameableFamilies,
        int SkippedFamilies,
        int Levels,
        int ForwardedLevels,
        int FinalTreeConfirmed,
        int FinalTreeNoSpan,
        int FinalTreeNoCounterpart,
        int InferringLevels,
        int PromotionsOverChain,
        int PromotionsOverTree,
        int PromotedNames,
        int ResolvedNames,
        int ResolvedThroughOpen,
        int NotAskedEnclosingParameter,
        int NotAskedNotParticipating,
        int NotAskedPreludeOnly,
        int GuardedAmbiguousOpen,
        int UnguardedRejected,
        int UnguardedUnspellable,
        int UnguardedNoPath,
        int TreePrograms,
        int ForwardingOwn,
        int ForwardingCaptured,
        int ForwardingForwarded,
        int ForwardingUnavailable,
        int AttributedLifts,
        int UnattributedLifts,
        int CollisionLevels,
        int ConflictingLevels,
        int ConflictingNames,
        int ValidityChains,
        int InvalidChains)
    {
        public static Totals Of(IEnumerable<FrontEndProgram> programs)
        {
            var guarded = programs.Where(static program => program.Skip is null).ToList();
            var occurrences = guarded.SelectMany(static program => program.Occurrences).ToList();
            var names = occurrences.Where(static occurrence => occurrence.Site != FrontEndSite.OpenHead).ToList();
            var heads = occurrences.Where(static occurrence => occurrence.Site == FrontEndSite.OpenHead).ToList();
            var families = guarded.SelectMany(static program => program.Families).ToList();
            var levels = guarded.SelectMany(static program => program.Levels.Select(level => (Program: program, Level: level))).ToList();
            var promotions = levels
                .SelectMany(static pair => pair.Level.Promotions.Select(promotion => (pair.Program, pair.Level, Promotion: promotion)))
                .ToList();
            var asked = promotions.Where(static entry => entry.Promotion.IsAsked).ToList();
            var forwardings = levels.SelectMany(static pair => pair.Level.Forwardings).ToList();
            int Class(FrontEndPromotionClass promotionClass) => promotions.Count(entry => entry.Promotion.Class == promotionClass);
            return new(
                guarded.Count,
                names.Count,
                names.Count(static occurrence => occurrence.IsParameter),
                names.Count(static occurrence => occurrence.Site == FrontEndSite.DotFallback),
                heads.Count,
                heads.Count(static occurrence => occurrence.IsParameter),
                families.Count(static family => family.SkipReason is null),
                families.Count(static family => family.SkipReason is null && family.Expected == "none"),
                families.Count(static family => family.SkipReason is not null),
                guarded.Sum(static program => program.Levels.Count),
                guarded.Sum(static program => program.Levels.Count(static level => level.Forwarded.Count > 0)),
                guarded.Sum(static program => program.FinalTree.Confirmed),
                guarded.Sum(static program => program.FinalTree.NoSpan),
                guarded.Sum(static program => program.FinalTree.NoCounterpart),
                levels.Count(static pair => pair.Level.Infers),
                asked.Count(static entry => PromotionSite(entry.Program, entry.Level) == SiteKind.Chain),
                asked.Count(static entry => PromotionSite(entry.Program, entry.Level) == SiteKind.Tree),
                asked.Count(static entry => entry.Promotion.Class == FrontEndPromotionClass.Promoted && PromotionSite(entry.Program, entry.Level) != SiteKind.None),
                asked.Count(static entry => entry.Promotion.Class == FrontEndPromotionClass.Resolves && PromotionSite(entry.Program, entry.Level) != SiteKind.None),
                asked.Count(static entry => entry.Promotion.Class == FrontEndPromotionClass.Resolves && entry.Promotion.ThroughOpen && PromotionSite(entry.Program, entry.Level) != SiteKind.None),
                Class(FrontEndPromotionClass.EnclosingParameter),
                Class(FrontEndPromotionClass.NotParticipating),
                Class(FrontEndPromotionClass.PreludeOnly),
                asked.Count(static entry => entry.Promotion.Class == FrontEndPromotionClass.AmbiguousOpen && PromotionSite(entry.Program, entry.Level) != SiteKind.None),
                asked.Count(static entry => PromotionSite(entry.Program, entry.Level) == SiteKind.None && entry.Program.TreeSkipReason == FrontEndDecisionCorpus.InvalidOpenTarget),
                asked.Count(static entry => PromotionSite(entry.Program, entry.Level) == SiteKind.None && entry.Program.TreeSkipReason == FrontEndDecisionCorpus.UnspellableLiteral),
                asked.Count(static entry => PromotionSite(entry.Program, entry.Level) == SiteKind.None && entry.Program.TreeSkipReason is null),
                guarded.Count(static program => program.Tree is not null),
                forwardings.Count(static forwarding => forwarding.Kind == FrontEndForwardingKind.Own),
                forwardings.Count(static forwarding => forwarding.Kind == FrontEndForwardingKind.Captured),
                forwardings.Count(static forwarding => forwarding.Kind == FrontEndForwardingKind.Forwarded),
                forwardings.Count(static forwarding => forwarding.Kind == FrontEndForwardingKind.Unavailable),
                guarded.Sum(static program => program.Lifts.Attributed),
                guarded.Sum(static program => program.Lifts.Unattributed),
                levels.Count(static pair => GuardsCollisions(pair.Level)),
                levels.Count(static pair => pair.Level.Conflicts.Count > 0),
                levels.Sum(static pair => pair.Level.Conflicts.Count),
                levels.Count(static pair => GuardsValidity(pair.Level)),
                levels.Count(static pair => GuardsValidity(pair.Level) && !ValidityExpected(pair.Level)));
        }
    }

    internal static string GenerateArtifact()
    {
        var programs = FrontEndDecisionCorpus.Programs;
        var totals = Totals.Of(programs);
        var skipped = programs.Where(static program => program.Skip is not null).ToList();
        string CorpusCount(string corpus) => $"{programs.Count(program => program.Corpus == corpus)}";

        // Programs whose levels and decisions are identical (the explorer corpus is templates x values, and a
        // template's names rarely depend on the value) share ONE block, in first-occurrence order. Nothing is
        // sampled: a block is the exact text every member program renders to.
        var blocks = new List<(string Body, List<FrontEndProgram> Members)>();
        var blockOf = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var program in programs.Where(static program => program.Skip is null))
        {
            var body = RenderProgram(program);
            if (blockOf.TryGetValue(body, out var known))
            {
                blocks[known].Members.Add(program);
            }
            else
            {
                blockOf.Add(body, blocks.Count);
                blocks.Add((body, [program]));
            }
        }

        var builder = new StringBuilder();
        builder.Append($"""
            import KatLang

            /-!
            GENERATED FILE - DO NOT EDIT BY HAND.

            Front-end decision differential: the Lean front-end specification functions of `lean/KatLang.lean`
            against the decisions the C# front end made on every program of four corpora: the semantic explorer
            (tests/KatLang.Tests/SemanticExplorerCorpus.cs), the language specification
            (tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs), the SEM-2B generated corpus
            (fuzz/KatLang.ParserFuzz/Semantic/SemanticCorpus.cs, every base, alpha-rename and declaration-reorder source with
            `trace(x) = x` and `wait(x) = x` prepended, as lean/CoreTests/SemanticGeneratedCases.lean encodes it) and
            the tutorial's source fences (tutorial.md, by ordinal). Lean has no front end: the other generated
            corpora evaluate a tree C# already elaborated, so they take these decisions as INPUT. Here each
            decision is an expectation. FD-F1 below pins a reported difference at the named occurrence.

            What is compared (generator: tests/KatLang.Tests/FrontEndDecisionCorpus.cs):
            - `selectOwnedDeclaration` — C#'s owned-binding fact for the name in its scope (parameter or
              property, with the deciding level's position in the chain; the fact parameter detection's rewrite
              and `ElaboratedScopeLookup.SelectOwnedDeclaration` read);
            - `elaboratesToParameter` — the node parameter detection left for the occurrence (`Expr.Param` or
              `Expr.Resolve`), which the complete pipeline's tree was checked to keep for every written name
              it still holds;
            - `elaborateOpenHead` — the node detection left as the head of each static `open` target, over the
              chain of CALLABLE bindings (the never-called program root's phantom signature omitted: chains `_c`);
            - `familyLiftingSignature?` — `ImplicitArgumentResolver.DeriveFamilyLiftingSignature` on each clause
              family's heads;
            - `shouldTreatAsImplicitParam` (promotion) — for each candidate name of an inferring level (a name its
              rows write), the detection operation's `IsInput` verdict: `some true` for an inferred input, `some false`
              for a resolved declaration and `ambiguousAt` for the matching ambiguous lookup error. Asked as
              `promotes chain name` over a lookup site built from the owner chain when no level of the chain writes
              an `open` (each level an algorithm declaring its property names, wired under Lean's `preludeAlg`), and as
              `promotesIn site name` over the ENCODED resolved tree before exposure classification when one does (`treeSite`: the root
              wired as `runResultM` wires it, then each property or branch body on the level's path), since open resolution
              needs the real providers. Not asked, as Lean's probe is not that decision: a name an established
              parameter binding owns (the caller excludes it; FD-1 checks the binding), a free name no reading of
              which participates (a dot fallback no receiver can select, the OD-B parameter-rooted path), a C#
              prelude member Lean's prelude does not model (`Math` members, `load`; Lean's prelude is pinned below);
              and, over an encoded tree only, a program with an invalid open target or an unsupported literal or anonymous block address;
            - `forwardingSource` — each requested capture of a lifted call against the corresponding synthesized
              argument, in order (including repeated names). The entire set of lifts agrees with the resolver's
              synthesis counter. An argument reads a parameter added to this level, one it already owned or the
              nearest enclosing binding. A closed value operand that stays bare identifies an unavailable source
              when its callee requires just that binding. FD-F1 (spec/forwarding-single-collector-by-shape) records
              the by-shape exception: the callee requests xs, C# supplies the caller's items, Lean answers unavailable;
            - `conflictingOwnedNames` (as `ownedConflicts chain`) — the properties of each declaring level the
              complete pipeline's `ParameterPropertyCollisionValidator` reported, located by declaration span. The
              root's phantom signature is checked against the root's own declarations only (chain `p_0`), and every
              nested level against the callable chain, as that validator does; `validOwnedDeclarations` over the
              same chain of every innermost level;
            - `liftingSlotRole` — `FormulaLiftingRoles.SlotRole` on every callee kind, positions 0..{RolePositions - 1},
              with and without a known position. This one is the whole table, not per occurrence: which kind a
              written call's callee has is implicit-argument resolution's private classification and is not
              recoverable from the elaborated tree without re-implementing it.

            Each chain is rebuilt from the DETECTED tree's nesting (a body's stored parameter patterns and
            property names, a clause body's head binders), innermost level first, ending in the prelude's
            property level. `forwarded` lists the parameters automatic forwarding added afterwards (the resolved
            signature minus the detected one); the owner walk never reads it. Identical guards of one program
            are emitted once, with their multiplicity, and programs whose levels and guards are identical share
            one block that names every one of them ({blocks.Count} blocks): nothing is sampled.

            Partition:
            - corpus programs: {programs.Count} (explorer {CorpusCount(FrontEndDecisionCorpus.ExplorerCorpus)}, spec {CorpusCount(FrontEndDecisionCorpus.LanguageSpecCorpus)}, SEM-2B {CorpusCount(FrontEndDecisionCorpus.SemanticGeneratedCorpus)}, tutorial {CorpusCount(FrontEndDecisionCorpus.TutorialCorpusName)})
            - skipped, the parser rejected the source: {skipped.Count(static program => program.Skip == FrontEndSkip.SyntaxError)}
            - skipped, an unresolved `load` directive (module elaboration is async-only): {skipped.Count(static program => program.Skip == FrontEndSkip.UnresolvedLoad)}
            - skipped, parameter inference refused as circular: {skipped.Count(static program => program.Skip == FrontEndSkip.UndecidedInference)}
            - excluded by exact id, a reviewed Lean/C# disagreement (class and witness in
              `FrontEndDecisionCorpus.ReviewedDriftById`): {skipped.Count(static program => program.Skip == FrontEndSkip.ReviewedDrift)}
            - guarded programs: {totals.Programs} ({totals.Levels} scope levels, {totals.ForwardedLevels} with a forwarded parameter)
            - name occurrences: {totals.NameOccurrences} ({totals.ParameterVerdicts} parameters, {totals.DotFallbacks} dot-edge fallback names)
            - of those names and heads, the same node in the complete pipeline's tree (matched by source span):
              {totals.FinalTreeConfirmed}; with no source span to match by (names the parser synthesized, such as the plumbing of an
              assignment deconstruction): {totals.FinalTreeNoSpan}; with no node of that span and name left there: {totals.FinalTreeNoCounterpart}
            - open heads: {totals.OpenHeads} ({totals.ParameterOpenHeads} parameter-owned)
            - clause families: {totals.Families} ({totals.UnnameableFamilies} with no lifting signature); skipped, a head with no Lean spelling: {totals.SkippedFamilies}
            - promotion: {totals.InferringLevels} inferring levels; {totals.PromotionsOverChain + totals.PromotionsOverTree} decisions guarded ({totals.PromotionsOverChain} over an owner chain, {totals.PromotionsOverTree} over an encoded tree
              of {totals.TreePrograms} programs): {totals.PromotedNames} promoted, {totals.ResolvedNames} resolved ({totals.ResolvedThroughOpen} through an open), {totals.GuardedAmbiguousOpen} ambiguous; not asked: {totals.NotAskedEnclosingParameter} owned
              by an enclosing parameter, {totals.NotAskedNotParticipating} not participating, {totals.NotAskedPreludeOnly} a C#-only prelude member;
              not guarded over an encoded tree: {totals.UnguardedRejected} in a program with an invalid open, {totals.UnguardedUnspellable} in a program the encoder cannot spell, {totals.UnguardedNoPath} with no property path
            - forwarding: {totals.ForwardingOwn + totals.ForwardingCaptured + totals.ForwardingForwarded} reads ({totals.ForwardingOwn} own, {totals.ForwardingCaptured} captured, {totals.ForwardingForwarded} forwarded) in {totals.AttributedLifts} lifted calls;
              {totals.ForwardingUnavailable} unavailable sources at closed value operands; unattributed lifts: {totals.UnattributedLifts}
            - declaration validity: {totals.CollisionLevels} declaring levels checked ({totals.ConflictingLevels} with a reported collision, {totals.ConflictingNames} names);
              {totals.ValidityChains} innermost chains checked ({totals.InvalidChains} invalid)

            Regenerate from the repo root with:
              $env:KATLANG_REGENERATE_FRONT_END_DECISIONS = "1"
              dotnet test .\KatLang.slnx --filter FrontEndDecisionLeanArtifact
            -/

            namespace FrontEndDecisionCases
            open KatLang


            """.ReplaceLineEndings("\n"));

        AppendSharedDefinitions(builder);
        AppendRoleTable(builder);

        var guardedIds = new List<string>();
        for (var index = 0; index < blocks.Count; index++)
        {
            var (body, members) = blocks[index];
            var first = members[0];
            builder.Append($"-- {first.Corpus}/{first.Id}: {first.Source.Replace("\n", " \\n ")}\n");
            if (members.Count > 1)
            {
                builder.Append($"-- the same levels and decisions, {members.Count - 1} more:\n");
                foreach (var line in Wrap(members.Skip(1).Select(static member => $"{member.Corpus}/{member.Id}")))
                    builder.Append($"--   {line}\n");
            }

            builder.Append(body.Replace(PrefixPlaceholder, $"p{index}", StringComparison.Ordinal));
            builder.Append('\n');
            guardedIds.AddRange(members.Select(static member => $"{member.Corpus}/{member.Id}"));
        }

        // One literal for all four corpora exceeds Lean's term-elaboration recursion limit.
        var partitions = new List<string>();
        foreach (var corpus in programs.GroupBy(static program => program.Corpus))
        {
            var list = $"{corpus.Key}GuardedIds";
            partitions.Add(list);
            SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, list,
                guardedIds.Where(id => id.StartsWith(corpus.Key + "/", StringComparison.Ordinal)).ToList(),
                corpus.Count(program => program.Skip is null),
                $"Machine-checked partition count: {corpus.Key} ids from the block-emission loop against its corpus.");
        }

        builder.Append($"def guardedProgramIds : List String := {string.Join(" ++ ", partitions)}\n");
        builder.Append($"#guard guardedProgramIds.length == {totals.Programs}\n\n");
        SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, "skippedProgramIds",
            skipped.Select(static program => $"{program.Corpus}/{program.Id}").ToList(), programs.Count - totals.Programs,
            "The programs that contribute no guard (the reasons are counted in the partition above).");

        builder.Append("end FrontEndDecisionCases\n");
        return builder.ToString();
    }

    private static void AppendSharedDefinitions(StringBuilder builder)
    {
        var prelude = FrontEndDecisionCorpus.PreludeProperties();
        builder.Append("/-- The outermost level of every chain: the property names of C#'s semantic prelude, which owns no parameter. -/\n");
        builder.Append($"def prelude : List OwnerLevel :=\n  [{{ parameters := [], properties := [{Names(prelude)}] }}]\n\n");
        builder.Append("""
            /-- Every member of Lean's own prelude is a property of that level, so a name the Lean evaluator would find
                there is one the chains below end in as well. -/
            def preludeMemberNames : List Ident :=
              match preludeAlg with
              | .mk _ _ _ properties _ _ => properties.map (·.name)
              | _ => []
            #guard !preludeMemberNames.isEmpty
            #guard preludeMemberNames.all (fun name => prelude.any (fun level => level.properties.contains name))

            """.ReplaceLineEndings("\n"));
        builder.Append("/- Lean's prelude is EXACTLY the builtins: a C# prelude member outside this list is one Lean does not model, and\n");
        builder.Append("   promotion is not asked about a name that resolves to it. -/\n");
        builder.Append($"#guard preludeMemberNames == [{Names(FrontEndDecisionCorpus.LeanPreludeNames)}]\n\n");
        builder.Append("""
            /-- What `elaborateOpenHead` produced, as comparable data (`Expr` has no `BEq`): whether the head is a
                parameter read, and its name. -/
            def openHead? : Expr -> Option (Bool × Ident)
              | .param name => some (true, name)
              | .resolve name => some (false, name)
              | _ => none

            /-- One clause of a family, by its head. `familyLiftingSignature?` reads the heads only, so every clause
                takes the same empty body. -/
            def clause (head : Pattern) : CondBranch := ⟨head, alg [] [] [] []⟩

            /-- `conflictingOwnedNames` of a chain's innermost level against the levels enclosing it. -/
            def ownedConflicts : List OwnerLevel -> List Ident
              | [] => []
              | owner :: ancestors => conflictingOwnedNames owner ancestors

            /-- The promotion probe at a static lookup site. Keep an ambiguous lookup distinct from a missing site
                or any other failure. -/
            def promotionAt (site : Option (Algorithm × EvalCtx)) (name : Ident) : Option (Except Error Bool) :=
              site.map fun (owner, ctx) =>
                match (shouldTreatAsImplicitParam owner name ctx).run EvalState.empty with
                | .ok (promoted, _) => .ok promoted
                | .error e => .error e

            def promotesIn (site : Option (Algorithm × EvalCtx)) (name : Ident) : Option Bool := do
              (← promotionAt site name).toOption

            def ambiguousAt (site : Option (Algorithm × EvalCtx)) (name : Ident) : Bool :=
              match promotionAt site name with
              | some (.error (.ambiguousOpen found _)) => found == name
              | _ => false

            /-- The lookup site of a chain no level of which writes an `open`: every level below the prelude as an algorithm
                declaring the level's property names, each wired under the one enclosing it as the evaluator wires a
                nested algorithm (`wireToCaller`) and pushed, outermost first. No lookup reads a property's body unless an
                open does, so the bodies are empty. The chain's outermost level, C#'s prelude, is Lean's own `preludeAlg`. -/
            def chainSite (chain : List OwnerLevel) : Algorithm × EvalCtx :=
              chain.dropLast.reverse.foldl
                (fun (site : Algorithm × EvalCtx) (level : OwnerLevel) =>
                  let wired := wireToCaller site.2
                    (alg [] [] (level.properties.map fun name => privateProp name (alg [] [] [] [])) [])
                  (wired, site.2.push wired))
                (preludeAlg, { callStack := [preludeAlg] })

            def promotes (chain : List OwnerLevel) (name : Ident) : Option Bool :=
              promotesIn (some (chainSite chain)) name

            inductive SiteStep where
              | property (name : Ident)
              | branch (family : Ident) (index : Nat)

            /-- The lookup site of a level of an encoded program, reached from the root by property and branch steps: the root wired
                under the prelude as `runResultM` wires it (declarations identified first), then each property body wired
                to its owner (`childOfInContext`) and pushed. -/
            def treeSite (program : Expr) (path : List SiteStep) : Option (Algorithm × EvalCtx) :=
              match (identifyPropertyExpr program).run' 0 with
              | .algorithmExpr root =>
                  let base : EvalCtx := { callStack := [preludeAlg] }
                  let wired := wireToCaller base root
                  path.foldlM
                    (fun (site : Algorithm × EvalCtx) step => do
                      let body ← match step with
                        | .property name => (site.1.lookupPropDefAny? name).map (·.alg)
                        | .branch name i => do
                            let family ← site.1.lookupPropDefAny? name
                            let branch ← family.alg.branches[i]?
                            pure branch.body
                      let child := childOfInContext site.1 body site.2
                      pure (child, site.2.push child))
                    (wired, base.push wired)
              | _ => none


            """.ReplaceLineEndings("\n"));
    }

    /// <summary>
    /// The whole <c>liftingSlotRole</c> table against <see cref="FormulaLiftingRoles.SlotRole"/>: every callee kind
    /// (each builtin its own), every position of <see cref="RolePositions"/>, known and after a spread.
    /// </summary>
    private static void AppendRoleTable(StringBuilder builder)
    {
        builder.Append($"-- liftingSlotRole: every callee kind, supplied positions 0..{RolePositions - 1}, position known (true) and after a spread (false).\n");
        var callees = new List<(string Lean, LiftingCallee Callee)>
        {
            (".dynamic", LiftingCallee.Dynamic),
            (".user", LiftingCallee.User),
            (".family", LiftingCallee.Family),
            (".strictValue", LiftingCallee.StrictValue),
        };
        foreach (var builtin in Enum.GetValues<BuiltinId>())
            callees.Add(($"(.builtin .{builtin}Builtin)", LiftingCallee.OfBuiltin(builtin)));

        foreach (var (lean, callee) in callees)
        {
            foreach (var known in new[] { true, false })
            {
                var roles = Enumerable.Range(0, RolePositions)
                    .Select(position => FormulaLiftingRoles.SlotRole(callee, position, known) == LiftingRole.Callable ? ".callable" : ".value");
                builder.Append(
                    $"#guard (List.range {RolePositions}).map (fun position => liftingSlotRole {lean} position {(known ? "true" : "false")}) == " +
                    $"[{string.Join(", ", roles)}]\n");
            }
        }

        builder.Append($"-- {callees.Count} callee kinds, {callees.Count * 2 * RolePositions} roles.\n\n");
    }

    /// <summary>
    /// Stands for a block's definition prefix until its block index is known. A control character, which
    /// <see cref="LeanAstEncoder.QuoteString"/> refuses, so no emitted name can contain it.
    /// </summary>
    private const string PrefixPlaceholder = "\u0001";

    private static IEnumerable<string> Wrap(IEnumerable<string> ids)
    {
        var line = new StringBuilder();
        foreach (var id in ids)
        {
            if (line.Length > 0 && line.Length + id.Length + 2 > 110)
            {
                yield return line.ToString();
                line.Clear();
            }

            if (line.Length > 0)
                line.Append(", ");
            line.Append(id);
        }

        if (line.Length > 0)
            yield return line.ToString();
    }

    /// <summary>Where a level's promotion decisions are asked.</summary>
    private enum SiteKind
    {
        /// <summary>Not guarded (see the partition).</summary>
        None,

        /// <summary>Over the owner chain: no level of the chain writes an <c>open</c>.</summary>
        Chain,

        /// <summary>Over the encoded pre-exposure tree, at the level's property or clause-branch path.</summary>
        Tree,
    }

    private static SiteKind PromotionSite(FrontEndProgram program, FrontEndLevel level)
        => !level.HasOpens ? SiteKind.Chain
            : program.Tree is not null && level.Path is not null ? SiteKind.Tree
            : SiteKind.None;

    /// <summary>One program's level definitions and guards, with <see cref="PrefixPlaceholder"/> for the definition prefix.</summary>
    private static string RenderProgram(FrontEndProgram program)
    {
        var builder = new StringBuilder();
        const string prefix = PrefixPlaceholder;

        // A level's definition IS its chain: the level consed onto its enclosing level's chain.
        string Chain(FrontEndLevel? level, bool callable) => level is null || level.Index < 0
            ? "prelude"
            : $"{prefix}_{level.Index}{(callable && HasCallableVariant(level) ? "c" : "")}";

        // The chain the collision validator checks a level's declarations against: the root's own, with its phantom
        // signature; every other level's callable chain.
        string CollisionChain(FrontEndLevel level) => Chain(level, callable: !level.IsNeverCalledRoot);

        foreach (var level in program.Levels)
        {
            builder.Append($"def {Chain(level, callable: false)} : List OwnerLevel := {Level(level, callable: false)} :: {Chain(level.Parent, callable: false)}\n");
        }

        // The callable chain differs only where the never-called root's signature is omitted, and is emitted only
        // for the levels an open head is classified in or whose declarations are checked against it, and the levels
        // enclosing them.
        var callableLevels = new HashSet<FrontEndLevel>();
        foreach (var level in program.Levels.Where(static level => HasCallableVariant(level)
                     && (level.HasOpenHead || !level.IsNeverCalledRoot && (GuardsCollisions(level) || GuardsValidity(level)))))
        {
            for (var current = level; current is not null && current.Index >= 0; current = current.Parent)
                callableLevels.Add(current);
        }

        foreach (var level in program.Levels.Where(callableLevels.Contains))
        {
            builder.Append($"def {Chain(level, callable: true)} : List OwnerLevel := {Level(level, callable: true)} :: {Chain(level.Parent, callable: true)}\n");
        }

        // A level whose chain writes an open asks promotion over the encoded tree, at a site of its own.
        var treeLevels = program.Levels
            .Where(level => PromotionSite(program, level) == SiteKind.Tree && level.Promotions.Any(static promotion => promotion.IsAsked))
            .ToList();
        if (treeLevels.Count > 0)
        {
            builder.Append($"def {prefix}_tree : Expr :=\n  {program.Tree}\n");
            foreach (var level in treeLevels)
            {
                var steps = level.Path!.Select(step => step.Branch is { } index
                    ? $".branch {LeanAstEncoder.QuoteString(step.Property)} {index}"
                    : $".property {LeanAstEncoder.QuoteString(step.Property)}");
                builder.Append($"def {prefix}_s{level.Index} : Option (Algorithm × EvalCtx) := treeSite {prefix}_tree [{string.Join(", ", steps)}]\n");
            }
        }

        var guards = new List<string>();
        var multiplicity = new Dictionary<string, int>(StringComparer.Ordinal);
        void Guard(string guard)
        {
            if (multiplicity.TryGetValue(guard, out var count))
            {
                multiplicity[guard] = count + 1;
                return;
            }

            multiplicity.Add(guard, 1);
            guards.Add(guard);
        }

        foreach (var occurrence in program.Occurrences)
        {
            var name = LeanAstEncoder.QuoteString(occurrence.Name);
            if (occurrence.Site == FrontEndSite.OpenHead)
            {
                var chain = Chain(occurrence.Level, callable: true);
                Guard($"#guard selectOwnedDeclaration {chain} {name} == {occurrence.Owned}");
                Guard($"#guard openHead? (elaborateOpenHead {chain} {name}) == some ({(occurrence.IsParameter ? "true" : "false")}, {name})");
            }
            else
            {
                var chain = Chain(occurrence.Level, callable: false);
                Guard($"#guard selectOwnedDeclaration {chain} {name} == {occurrence.Owned}");
                Guard($"#guard elaboratesToParameter {chain} {name} == {(occurrence.IsParameter ? "true" : "false")}");
            }
        }

        foreach (var level in program.Levels)
        {
            var site = PromotionSite(program, level);
            foreach (var promotion in level.Promotions.Where(static promotion => promotion.IsAsked))
            {
                var expected = promotion.Class == FrontEndPromotionClass.Promoted ? "some true" : "some false";
                var name = LeanAstEncoder.QuoteString(promotion.Name);
                var probe = site switch
                {
                    SiteKind.Chain => $"promotes {Chain(level, callable: false)} {name}",
                    SiteKind.Tree => $"promotesIn {prefix}_s{level.Index} {name}",
                    _ => null,
                };
                if (probe is null)
                {
                    Guard($"-- promotion at level {level.Index} of {name} omitted ({program.TreeSkipReason ?? "no property path"})");
                    continue;
                }

                if (promotion.Class == FrontEndPromotionClass.AmbiguousOpen)
                    Guard($"#guard ambiguousAt {prefix}_s{level.Index} {name}");
                else
                    Guard($"#guard {probe} == {expected}");
            }

            foreach (var forwarding in level.Forwardings)
            {
                var source = forwarding.Kind switch
                {
                    FrontEndForwardingKind.Own => ".ownParameter",
                    FrontEndForwardingKind.Captured => $".capturedParameter {forwarding.Level}",
                    FrontEndForwardingKind.Forwarded => ".forwardedParameter",
                    FrontEndForwardingKind.Unavailable => ".unavailable",
                    _ => throw new InvalidOperationException($"Unknown forwarding source {forwarding.Kind}."),
                };
                var name = LeanAstEncoder.QuoteString(forwarding.Requested ?? forwarding.Name);
                var probe = $"forwardingSource {Chain(level, callable: false)} {(level.Infers ? "true" : "false")} {name}";
                if (forwarding.Requested is null)
                    Guard($"#guard {probe} == {source}");
                else if (program.Corpus == FrontEndDecisionCorpus.LanguageSpecCorpus && program.Id == CollectorShapeWitness
                         && level.Index == 2 && forwarding == new FrontEndForwarding("items", FrontEndForwardingKind.Own, 0, "xs"))
                    Guard($"#guard {probe} == .unavailable -- FD-F1: C# supplies {source} \"{forwarding.Name}\" by shape");
                else
                    throw new InvalidOperationException($"{program.Corpus}/{program.Id} at level {level.Index}: {probe}, C# supplies {source} '{forwarding.Name}'. Review this by-shape occurrence.");
            }
        }

        foreach (var level in program.Levels.Where(GuardsCollisions))
            Guard($"#guard ownedConflicts {CollisionChain(level)} == [{Names(level.Conflicts)}]");
        foreach (var level in program.Levels.Where(GuardsValidity))
            Guard($"#guard validOwnedDeclarations {CollisionChain(level)} == {(ValidityExpected(level) ? "true" : "false")}");

        foreach (var guard in guards)
            builder.Append(multiplicity[guard] == 1 ? $"{guard}\n" : $"{guard} -- x{multiplicity[guard]}\n");

        foreach (var family in program.Families)
        {
            builder.Append(family.SkipReason is { } reason
                ? $"-- family {family.Name}: not guarded ({reason})\n"
                : $"#guard familyLiftingSignature? [{family.LeanHeads}] == {family.Expected} -- family {family.Name}\n");
        }

        return builder.ToString();
    }

    /// <summary>Whether the level's callable chain differs from its chain: it lies under a never-called root that infers or receives a name.</summary>
    private static bool HasCallableVariant(FrontEndLevel level)
    {
        for (var current = level; current is not null; current = current.Parent)
        {
            if (current.IsNeverCalledRoot)
                return current.Parameters.Count > 0 || current.Forwarded.Count > 0;
        }

        return false;
    }

    /// <summary>
    /// The levels of a level's collision chain, innermost first, each with whether its signature counts there: the
    /// never-called root's counts only against the root's own declarations.
    /// </summary>
    private static IEnumerable<(FrontEndLevel Level, bool Signed)> CollisionChainOf(FrontEndLevel tip)
    {
        for (var current = tip; current is { Index: >= 0 }; current = current.Parent)
            yield return (current, !current.IsNeverCalledRoot || ReferenceEquals(current, tip));
    }

    private static bool Signs(FrontEndLevel level, bool signed) => signed && (level.Parameters.Count > 0 || level.Forwarded.Count > 0);

    /// <summary>
    /// Whether the level's declarations are checked: it declares a property and some level of its collision chain
    /// binds a name (otherwise no property can conflict, in Lean or in C#).
    /// </summary>
    private static bool GuardsCollisions(FrontEndLevel level)
        => level.Conflicts.Count > 0 || level.Properties.Count > 0 && CollisionChainOf(level).Any(static entry => Signs(entry.Level, entry.Signed));

    /// <summary>
    /// Whether the validity of the level's collision chain is checked: the level is innermost (no level is declared
    /// under it) and some level of the chain declares a property at or below a level that binds a name there.
    /// </summary>
    private static bool GuardsValidity(FrontEndLevel level)
    {
        if (level.HasChildLevel)
            return false;
        var declaresBelow = false;
        foreach (var (current, signed) in CollisionChainOf(level))
        {
            declaresBelow |= current.Properties.Count > 0;
            if (declaresBelow && Signs(current, signed))
                return true;
        }

        return false;
    }

    /// <summary>
    /// C#'s validity of the level's collision chain: no collision reported at any level of it whose declarations are
    /// checked against it — every level but a never-called root above the innermost one, whose signature is omitted
    /// there.
    /// </summary>
    private static bool ValidityExpected(FrontEndLevel level)
        => CollisionChainOf(level).All(static entry => !entry.Signed && entry.Level.IsNeverCalledRoot || entry.Level.Conflicts.Count == 0);

    private static string Level(FrontEndLevel level, bool callable)
    {
        var phantom = callable && level.IsNeverCalledRoot;
        var parameters = phantom ? [] : level.Parameters;
        var forwarded = phantom || level.Forwarded.Count == 0 ? "" : $", forwarded := [{Names(level.Forwarded)}]";
        return $"{{ parameters := [{Names(parameters)}], properties := [{Names(level.Properties)}]{forwarded} }}";
    }

    private static string Names(IEnumerable<string> names) => string.Join(", ", names.Select(LeanAstEncoder.QuoteString));
}
