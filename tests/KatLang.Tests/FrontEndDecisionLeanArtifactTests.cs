using System.Text;

namespace KatLang.Tests;

/// <summary>
/// Generates and pins <c>lean/CoreTests/FrontEndDecisionCases.lean</c>: the Lean front-end specification functions
/// checked against the C# front end's own decisions on every program of the two differential corpora
/// (<see cref="SemanticExplorerCorpus"/> and <c>LanguageSpecCorpus</c>).
///
/// <para>The other generated corpora hand Lean a tree the C# front end already elaborated, so they compare
/// EVALUATION of that tree. This one compares the elaboration decisions themselves: for each classified name the
/// owner chain C# resolved it in and C#'s verdict, guarded as <c>selectOwnedDeclaration chain name == …</c> and
/// <c>elaboratesToParameter chain name == …</c>; for each open head <c>elaborateOpenHead</c>; for each clause family
/// <c>familyLiftingSignature?</c>; and the whole <c>liftingSlotRole</c> table. See
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
    }

    private const int MinimumPrograms = 3098;
    private const int MinimumNameOccurrences = 8187;
    private const int MinimumParameterVerdicts = 2615;
    private const int MinimumOpenHeads = 83;
    private const int MinimumParameterOpenHeads = 4;
    private const int MinimumFamilies = 58;
    private const int MinimumUnnameableFamilies = 12;
    private const int MinimumForwardedLevels = 49;

    /// <summary>
    /// MANUALLY REVIEWED goldens of the collector, one per kind of decision. Everything else in the artifact is
    /// recorded from C# and checked by Lean; these five are checked against the language rules by a reader, so a
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
        // A captured ancestor parameter beats a farther property: the prelude alias `pi` is the outermost level.
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

            """,
        };

        // A parameter-owned open head elaborates to a parameter read; the name it would have opened stays unowned.
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

            """,
        };

        // The never-called root's inferred name is a parameter for a reference and owns no open head (the callable chain `p_0c`).
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

            """,
        };

        // A forwarded parameter is recorded apart from the name-resolution parameters; a builtin is a prelude property.
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

            """,
        };

        // A clause body's level owns its head's binders, and the family's lifting signature is the name its clauses agree on.
        yield return new object[]
        {
            "F(0) = 1\nF(n) = 2\nF(1, 2)",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["F"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := [], properties := [] } :: p_0
            def p_2 : List OwnerLevel := { parameters := ["n"], properties := [] } :: p_0
            #guard selectOwnedDeclaration p_0 "F" == .property 0
            #guard elaboratesToParameter p_0 "F" == false
            #guard familyLiftingSignature? [clause (.litInt 0), clause (.bind "n")] == some [.capture { name := "n" }] -- family F

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
        int FinalTreeNoCounterpart)
    {
        public static Totals Of(IEnumerable<FrontEndProgram> programs)
        {
            var guarded = programs.Where(static program => program.Skip is null).ToList();
            var occurrences = guarded.SelectMany(static program => program.Occurrences).ToList();
            var names = occurrences.Where(static occurrence => occurrence.Site != FrontEndSite.OpenHead).ToList();
            var heads = occurrences.Where(static occurrence => occurrence.Site == FrontEndSite.OpenHead).ToList();
            var families = guarded.SelectMany(static program => program.Families).ToList();
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
                guarded.Sum(static program => program.FinalTree.NoCounterpart));
        }
    }

    internal static string GenerateArtifact()
    {
        var programs = FrontEndDecisionCorpus.Programs;
        var totals = Totals.Of(programs);
        var skipped = programs.Where(static program => program.Skip is not null).ToList();

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
            against the decisions the C# front end made on every program of the two differential corpora
            (tests/KatLang.Tests/SemanticExplorerCorpus.cs and
            tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs). Lean has no front end: the other generated
            corpora evaluate a tree C# already elaborated, so they take these decisions as INPUT. Here each
            decision is an expectation, and a failing `#guard` is a Lean/C# divergence on that decision.

            What is compared (generator: tests/KatLang.Tests/FrontEndDecisionCorpus.cs):
            - `selectOwnedDeclaration` — C#'s owned-binding fact for the name in its scope (parameter or
              property, with the deciding level's position in the chain; the fact parameter detection's rewrite
              and `ElaboratedScopeLookup.SelectOwnedDeclaration` read);
            - `elaboratesToParameter` — the node parameter detection left for the occurrence (`Expr.Param` or
              `Expr.Resolve`), which the complete pipeline's tree was checked to keep for every written name
              it still holds;
            - `elaborateOpenHead` — the node detection left as the head of each static `open` target, over the
              chain of CALLABLE bindings (the never-called program root's inferred signature omitted);
            - `familyLiftingSignature?` — `ImplicitArgumentResolver.DeriveFamilyLiftingSignature` on each clause
              family's heads;
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
            - corpus programs: {programs.Count}
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

        SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, "guardedProgramIds", guardedIds, totals.Programs,
            "Machine-checked partition count: the id list is built by the loop that emits the guards above,\n" +
            "while the expected total is computed from the corpus partition, so a generation bug fails `lake build`.");
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

            /-- What `elaborateOpenHead` produced, as comparable data (`Expr` has no `BEq`): whether the head is a
                parameter read, and its name. -/
            def openHead? : Expr -> Option (Bool × Ident)
              | .param name => some (true, name)
              | .resolve name => some (false, name)
              | _ => none

            /-- One clause of a family, by its head. `familyLiftingSignature?` reads the heads only, so every clause
                takes the same empty body. -/
            def clause (head : Pattern) : CondBranch := ⟨head, alg [] [] [] []⟩


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

    /// <summary>One program's level definitions and guards, with <see cref="PrefixPlaceholder"/> for the definition prefix.</summary>
    private static string RenderProgram(FrontEndProgram program)
    {
        var builder = new StringBuilder();
        const string prefix = PrefixPlaceholder;

        // A level's definition IS its chain: the level consed onto its enclosing level's chain.
        string Chain(FrontEndLevel? level, bool callable) => level is null || level.Index < 0
            ? "prelude"
            : $"{prefix}_{level.Index}{(callable && HasCallableVariant(level) ? "c" : "")}";

        foreach (var level in program.Levels)
        {
            builder.Append($"def {Chain(level, callable: false)} : List OwnerLevel := {Level(level, callable: false)} :: {Chain(level.Parent, callable: false)}\n");
        }

        // The callable chain differs only where the never-called root's signature is omitted, and is emitted only
        // for the levels an open head is classified in and the levels enclosing them.
        var callableLevels = new HashSet<FrontEndLevel>();
        foreach (var level in program.Levels.Where(static level => level.HasOpenHead && HasCallableVariant(level)))
        {
            for (var current = level; current is not null && current.Index >= 0; current = current.Parent)
                callableLevels.Add(current);
        }

        foreach (var level in program.Levels.Where(callableLevels.Contains))
        {
            builder.Append($"def {Chain(level, callable: true)} : List OwnerLevel := {Level(level, callable: true)} :: {Chain(level.Parent, callable: true)}\n");
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

    /// <summary>Whether the level's callable chain differs from its chain: it lies under a never-called root that infers a name.</summary>
    private static bool HasCallableVariant(FrontEndLevel level)
    {
        for (var current = level; current is not null; current = current.Parent)
        {
            if (current.IsNeverCalledRoot)
                return current.Parameters.Count > 0;
        }

        return false;
    }

    private static string Level(FrontEndLevel level, bool callable)
    {
        var parameters = callable && level.IsNeverCalledRoot ? [] : level.Parameters;
        var forwarded = level.Forwarded.Count == 0 ? "" : $", forwarded := [{Names(level.Forwarded)}]";
        return $"{{ parameters := [{Names(parameters)}], properties := [{Names(level.Properties)}]{forwarded} }}";
    }

    private static string Names(IEnumerable<string> names) => string.Join(", ", names.Select(LeanAstEncoder.QuoteString));
}
