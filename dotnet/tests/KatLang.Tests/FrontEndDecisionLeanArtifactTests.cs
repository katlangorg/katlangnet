using System.Text;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// Generates and pins <c>lean/CoreTests/FrontEndDecisionCases.lean</c>: the Lean front-end specification functions
/// checked against the C# front end's own decisions on every program of the four differential corpora
/// (<see cref="SemanticExplorerCorpus"/>, <c>LanguageSpecCorpus</c>, the SEM-2B generated corpus's identity-prelude
/// members and the tutorial's source fences) and on the members of the front-end witnesses
/// (<see cref="FrontEndWitnesses"/>).
///
/// <para>The other generated corpora hand Lean a tree the C# front end already elaborated, so they compare
/// EVALUATION of that tree. This one compares the elaboration decisions themselves: for each classified name the
/// owner chain C# resolved it in and C#'s verdict, guarded as <c>selectOwnedDeclaration chain name == …</c> and
/// <c>elaboratesToParameter chain name == …</c>; for each open head <c>elaborateOpenHead</c>; for each clause family
/// <c>familyLiftingSignature?</c>; for each candidate name of an inferring level <c>shouldTreatAsImplicitParam</c>;
/// for each forwarded binding and each refused forward that names one binding <c>forwardingSource</c>; for each
/// declaring level <c>conflictingOwnedNames</c> and, at each innermost level, <c>validOwnedDeclarations</c>; and
/// <c>liftingSlotRole</c>, as the whole table and at every written slot whose role the pipeline's output shows. See
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

    /// <summary>
    /// THE BY-SHAPE SUPPLY, pinned occurrence by occurrence: the program, the level of the reference, the caller's own
    /// collector C# read, the callee's name for it, and what forwarding BY NAME has for that name there — nothing
    /// (FD-F1) or an enclosing parameter binding (FD-F2). A new occurrence, or one of another class, is a reviewed
    /// diff here, never a regenerated guard.
    /// </summary>
    [Fact]
    public void ByShapeSupplies_AreExactlyTheReviewedOccurrences()
    {
        var hits = (from program in FrontEndDecisionCorpus.Programs
                    from level in program.Levels
                    from source in level.Forwardings
                    where source.Requested is not null
                    select $"{program.Corpus}/{program.Id} level {level.Index}: {source.Kind} {source.Name} for {source.Requested}, by name {source.ByName}").ToArray();

        Assert.Equal(
            [
                "spec/forwarding-single-collector-by-shape level 2: Own items for xs, by name .unavailable",
                "witness/by-shape-supply-under-two-names level 2: Own items for xs, by name .unavailable",
                "witness/by-shape-supply-under-two-names/alpha-rename level 2: Own w4 for w2, by name .unavailable",
                "witness/by-shape-supply-under-two-names/declaration-reorder level 1: Own items for xs, by name .unavailable",
                "witness/by-shape-supply-of-a-sequence-group level 2: Own items for xs, by name .unavailable",
                "witness/by-shape-supply-of-a-sequence-group/alpha-rename level 2: Own w4 for w2, by name .unavailable",
                "witness/by-shape-supply-of-a-sequence-group/declaration-reorder level 1: Own items for xs, by name .unavailable",
                "witness/by-shape-supply-beside-an-enclosing-binding level 3: Own items for xs, by name .capturedParameter 1",
                "witness/by-shape-supply-beside-an-enclosing-binding/alpha-rename level 3: Own w5 for w2, by name .capturedParameter 1",
                "witness/by-shape-supply-beside-an-enclosing-binding/declaration-reorder level 2: Own items for xs, by name .capturedParameter 1",
            ],
            hits);
    }

    /// <summary>
    /// The decisions each witness was written to show, as a reader checks them against the language rules: every slot
    /// role the output shows, every forwarding read, every refused forward and what it is attributed to. Hand-written,
    /// never regenerated.
    /// </summary>
    private static readonly IReadOnlyDictionary<string, string[]> WitnessDecisions = new Dictionary<string, string[]>
    {
        // `Use = Pick(1, Inc)` is `Use(x) = Pick(1, Inc(x))`.
        ["family-argument-is-a-value"] =
        [
            "Value: Pick [Family] position 1 <- Inc",
            "read in (): x Forwarded",
        ],
        // `Use = Apply(Inc, 4)` keeps `Inc` and gains no parameter.
        ["user-argument-keeps-the-callable"] =
        [
            "Callable: Apply [User] position 0 <- Inc",
            "Callable: Keep [User] position 0 <- Inc",
        ],
        // `f(Inc)` keeps `Inc` although `Twice` binds its `x`; the root row's `Twice(Run, 3)` keeps `Run`.
        ["dynamic-callee-keeps-the-callable"] =
        [
            "Callable: f [Dynamic] position 0 <- Inc",
            "Callable: Twice [User] position 0 <- Run",
        ],
        // `Use = abs(Inc)` is `Use(x) = abs(Inc(x))`.
        ["strict-value-argument-is-a-value"] =
        [
            "Value: abs [StrictValue] position 0 <- Inc",
            "Value: abs [StrictValue] position 0 <- Lit",
            "read in (): x Forwarded",
        ],
        // `Lifted = Abs(Inc)` is `Lifted(x) = Abs(Inc(x))`; `Kept = Held(Inc)` keeps `Inc`.
        ["alias-takes-its-targets-kind"] =
        [
            "Value: Abs [StrictValue] position 0 <- Inc",
            "Callable: Held [User] position 0 <- Inc",
            "read in (): x Forwarded",
        ],
        // `Late` keeps both references after the spread; `Wide` and `Early` each lift `Inc` and gain `x`.
        ["spread-ends-known-positions"] =
        [
            "Callable: reduce [builtin reduce] position 1 after a spread <- Add",
            "Callable: reduce [builtin reduce] position 2 after a spread <- Inc",
            "Value: take [builtin take] position 1 after a spread <- Inc",
            "Callable: reduce [builtin reduce] position 1 <- Add",
            "Value: reduce [builtin reduce] position 2 <- Inc",
            "read in (): x Forwarded",
            "read in (): x Forwarded",
        ],
        // `Inc.Apply(4)` is `Apply(Inc, 4)`; `Inc.Pick(2)` is `Pick(Inc(x), 2)` in `Lifted(x)`.
        ["fallback-receiver-is-slot-zero"] =
        [
            "Callable: Apply [User] position 0 <- Inc",
            "Value: Pick [Family] position 0 <- Inc",
            "read in (): x Forwarded",
        ],
        ["runtime-receiver-decides-nothing"] = ["Callable: .Go [Dynamic] position 0 <- Inc"],
        ["one-unbound-name-among-several"] = ["unavailable in (x): k"],
        ["two-unbound-names-share-one-refusal"] = ["unattributed: 1 bare reference, 2 unbound names"],
        ["bare-forwarding-reports-each-parameter"] =
        [
            "unavailable in (p): q",
            "unavailable in (p): r",
            "bare forwarding of Mix: 2 reports, attributed [q, r]",
        ],
        ["by-shape-supply-under-two-names"] = ["read in (items): items by shape for xs, by name .unavailable"],
        ["member-calls-and-bare-forwarding"] =
        [
            "Callable: .Mix [User] position 0 <- Inc",
            "Callable: .Mix [User] position 0 <- Inc",
            "Value: .Abs [StrictValue] position 0 <- Inc",
            "read in (): x Forwarded",
            "unavailable in (p): q",
            "bare forwarding of Mix: 2 reports, attributed [q]",
        ],
        ["by-shape-supply-of-a-sequence-group"] = ["read in (items): items by shape for xs, by name .unavailable"],
        ["by-shape-supply-under-one-name"] = ["read in (xs): xs Own"],
        ["by-shape-supply-beside-an-enclosing-binding"] = ["read in (items): items by shape for xs, by name .capturedParameter 1"],
    };

    [Fact]
    public void Witnesses_ShowTheReviewedDecisions()
    {
        Assert.Equal(FrontEndWitnesses.All.Select(static witness => witness.Id).Order(StringComparer.Ordinal),
            WitnessDecisions.Keys.Order(StringComparer.Ordinal));
        Assert.All(FrontEndWitnesses.All, witness =>
        {
            Assert.False(string.IsNullOrWhiteSpace(witness.Shows), witness.Id);
            var program = Witness(witness.Id);
            Assert.True(program.Skip is null, witness.Id);
            Assert.Equal(WitnessDecisions[witness.Id], Decisions(program));
        });
    }

    /// <summary>
    /// THE MEMBER RELATION of a witness, as the SEM-2B corpus states it for its own members: the alpha-rename shows the
    /// base member's decisions name for name under the rename map, and the declaration-reorder shows them unchanged —
    /// a front-end decision is a decision about bindings, and neither transformation changes one. The alpha-rename
    /// must also rename EVERY name the base program binds.
    /// </summary>
    [Fact]
    public void Witnesses_KeepTheirDecisionsUnderRenamingAndReordering()
    {
        Assert.All(FrontEndWitnesses.All, witness =>
        {
            var map = witness.RenameMap;
            Assert.NotEmpty(map);
            Assert.Equal(map.Count, map.Values.Distinct(StringComparer.Ordinal).Count());
            var members = witness.Members;
            Assert.Equal([SemanticMember.BaseRole, SemanticMember.AlphaRenameRole, SemanticMember.DeclarationReorderRole],
                members.Select(static member => member.Role));
            Assert.All(members, member => Assert.True(Witness(member.Id).Skip is null, member.Id));
            Assert.True(witness.Declarations.Count >= 2, $"{witness.Id}: a declaration-reorder needs two root declarations.");
            Assert.NotEqual(members[0].Source, members[2].Source);

            var renamedTokens = Lexer.Tokenize(members[1].Source).Tokens
                .Where(static token => token.Kind == TokenKind.Identifier)
                .Select(token => members[1].Source.Substring(token.Position, token.Length))
                .ToHashSet(StringComparer.Ordinal);
            Assert.DoesNotContain(map.Keys, renamedTokens.Contains);
            Assert.All(map.Values, fresh => Assert.Contains(fresh, renamedTokens));

            string Renamed(string name) => map.GetValueOrDefault(name, name);
            var baseMember = Witness(members[0].Id);
            Assert.Equal(Decisions(baseMember, Renamed).Order(StringComparer.Ordinal),
                Decisions(Witness(members[1].Id)).Order(StringComparer.Ordinal));
            Assert.Equal(Decisions(baseMember).Order(StringComparer.Ordinal),
                Decisions(Witness(members[2].Id)).Order(StringComparer.Ordinal));
        });
    }

    private static FrontEndProgram Witness(string id)
        => FrontEndDecisionCorpus.Programs.Single(program => program.Corpus == FrontEndDecisionCorpus.WitnessCorpus && program.Id == id);

    /// <summary>
    /// The lifting and forwarding decisions of one program, one line each, with every written name passed through
    /// <paramref name="rename"/>: the slot roles shown, the forwarding reads and refusals by the names their level binds,
    /// and what was left unattributed.
    /// </summary>
    private static IReadOnlyList<string> Decisions(FrontEndProgram program, Func<string, string>? rename = null)
    {
        string Name(string name) => name.StartsWith('.') ? "." + Name(name[1..]) : rename?.Invoke(name) ?? name;
        var lines = new List<string>();
        foreach (var role in program.SlotRoles)
        {
            var kind = role.Kind.Kind == LiftingCalleeKind.Builtin ? $"builtin {role.Kind.Builtin}" : role.Kind.Kind.ToString();
            lines.Add($"{role.Role}: {Name(role.Callee)} [{kind}] position {role.Position}{(role.PositionKnown ? "" : " after a spread")} <- {Name(role.Reference)}");
        }

        foreach (var level in program.Levels)
        {
            var binds = $"({string.Join(", ", level.Parameters.Select(Name))})";
            foreach (var forwarding in level.Forwardings)
            {
                lines.Add(forwarding.Kind switch
                {
                    FrontEndForwardingKind.Unavailable => $"unavailable in {binds}: {Name(forwarding.Name)}",
                    FrontEndForwardingKind.Captured => $"read in {binds}: {Name(forwarding.Name)} captured at {forwarding.Level}",
                    _ when forwarding.Requested is { } requested => $"read in {binds}: {Name(forwarding.Name)} by shape for {Name(requested)}, by name {forwarding.ByName}",
                    _ => $"read in {binds}: {Name(forwarding.Name)} {forwarding.Kind}",
                });
            }
        }

        if (program.Lifts.MultiNameRefusals > 0)
            lines.Add($"unattributed: {program.Lifts.MultiNameRefusals} bare reference, {program.Lifts.MultiNameRefusalNames} unbound names");
        foreach (var refusal in program.BareRefusals)
            lines.Add($"bare forwarding of {Name(refusal.Callee)}: {refusal.Reports} reports, attributed [{string.Join(", ", refusal.Attributed.Select(Name))}]");
        return lines;
    }

    /// <summary>
    /// WHAT THE OUTPUT SHOWS ABOUT SLOT ROLES, pinned: every supplied slot of every written call falls in exactly one
    /// class, no written call is lost between detection and the complete tree, and the roles shown reach every callee
    /// kind, both roles, and positions known and after a spread.
    /// </summary>
    [Fact]
    public void SlotRoles_AreShownForEveryCalleeKindAndRole()
    {
        var guarded = FrontEndDecisionCorpus.Programs.Where(static program => program.Skip is null).ToList();
        var totals = Totals.Of(FrontEndDecisionCorpus.Programs);
        Assert.Equal(0, totals.NoFinalCounterpartSlots);
        Assert.Equal(totals.WrittenPositions,
            totals.ShownValue + totals.ShownCallable + totals.RefusedOrCallable + totals.NoRoleSensitiveReference + totals.CalleeNotRead
            + totals.PositionNotRead + totals.ReceiverOutsideSupply + totals.SynthesizedCallSlots + totals.NoFinalCounterpartSlots);
        Assert.All(guarded, static program => Assert.Equal(program.WrittenPositions, program.SlotOutcomes.Values.Sum()));
        Assert.Equal(totals.ShownValue + totals.ShownCallable, guarded.Sum(static program => program.SlotRoles.Count));

        var shown = guarded.SelectMany(static program => program.SlotRoles).ToList();
        Assert.Equal(Enum.GetValues<LiftingCalleeKind>().Order(), shown.Select(static role => role.Kind.Kind).Distinct().Order());
        foreach (var kind in Enum.GetValues<LiftingCalleeKind>())
        {
            // A family and a strict-value callee give every slot the value role, a user and a dynamic callee the
            // callable role; a builtin gives both.
            var roles = shown.Where(role => role.Kind.Kind == kind).Select(static role => role.Role).Distinct().Order().ToArray();
            Assert.Equal(kind switch
            {
                LiftingCalleeKind.Family or LiftingCalleeKind.StrictValue => [LiftingRole.Value],
                LiftingCalleeKind.User or LiftingCalleeKind.Dynamic => [LiftingRole.Callable],
                _ => new[] { LiftingRole.Value, LiftingRole.Callable },
            }, roles);
        }

        Assert.Contains(shown, static role => !role.PositionKnown && role.Role == LiftingRole.Value);
        Assert.Contains(shown, static role => !role.PositionKnown && role.Role == LiftingRole.Callable);

        Assert.Equal(0, totals.CalleeNotRead);
        Assert.True(totals.ReportedValue >= 3);
    }

    /// <summary>
    /// FD-P1: promotion is decided at DETECTION, on declarations no pass has classified, so its Lean probe is asked over
    /// the resolved tree BEFORE exposure classification. These are the probes that depend on it. The list is the result
    /// of a Lean control, not of a C# criterion: the same artifact generated with every tree taken from the COMPLETE
    /// pipeline (after exposure classification) fails <c>lake env lean</c> at exactly these seven guards — each
    /// <c>promotesIn … == some false</c>, a name C# resolves through an open whose member or provider exposure later
    /// makes local-only, which a lookup over the classified tree refuses (control run 2026-11-20; rerun it when the
    /// list or the encoding changes). The test pins what C# can check: each is a guarded resolved probe over an encoded
    /// tree, that tree holds no local-only exposure, and the program's complete tree does.
    /// </summary>
    [Fact]
    public void Promotion_FindsDeclarationsBeforeExposureClassifiesThem()
    {
        Assert.All(ExposureSensitivePromotions, entry =>
        {
            var program = FrontEndDecisionCorpus.Programs.Single(program => $"{program.Corpus}/{program.Id}" == entry.Program);
            Assert.Null(program.Skip);
            var level = program.Levels[entry.Level];
            Assert.Equal(SiteKind.Tree, PromotionSite(program, level));
            var promotion = Assert.Single(level.Promotions, promotion => promotion.Name == entry.Name);
            Assert.Equal(FrontEndPromotionClass.Resolves, promotion.Class);

            var afterExposure = LeanAstEncoder.EncodeProgram(SourceProvenance.ParseAllowingDiagnostics(program.Source).Root);
            Assert.True(HoldsLocalOnlyExposure(afterExposure), $"{entry.Program}: the complete pipeline's tree holds no local-only exposure.");
        });

        Assert.All(FrontEndDecisionCorpus.Programs.Where(static program => program.Tree is not null), static program =>
            Assert.False(HoldsLocalOnlyExposure(program.Tree!), $"{program.Corpus}/{program.Id}: an encoded tree holds a local-only exposure."));
    }

    private static bool HoldsLocalOnlyExposure(string encodedTree)
        => encodedTree.Contains("privateLocalProp", StringComparison.Ordinal) || encodedTree.Contains("publicLocalProp", StringComparison.Ordinal);

    private static readonly (string Program, int Level, string Name)[] ExposureSensitivePromotions =
    [
        ("explorer/special__openLocalOnlyCapturedParamsOutsideOwner", 1, "X"),
        ("spec/open-local-only-member-read-by-inferring-sibling", 4, "X"),
        ("spec/open-local-only-through-reference", 6, "Q"),
        ("spec/open-local-only-enclosing-level", 5, "Q"),
        ("spec/open-block-headed-reference-keeps-requirement", 6, "Q"),
        ("spec/ownership-open-provided-captured-member-read-by-sibling-is-local-only", 4, "X"),
        ("spec/ownership-open-head-between-opener-and-settling-level-charges-the-capture", 5, "X"),
    ];

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
        Assert.True(totals.ForwardingUnavailable >= MinimumForwardingUnavailable, $"unavailable sources {totals.ForwardingUnavailable} < {MinimumForwardingUnavailable}");
        Assert.True(totals.UnavailableFromBareForwarding >= MinimumUnavailableFromBareForwarding, $"unavailable sources from bare-forwarding reports {totals.UnavailableFromBareForwarding} < {MinimumUnavailableFromBareForwarding}");
        Assert.True(totals.ShownValue >= MinimumShownValue, $"value roles shown {totals.ShownValue} < {MinimumShownValue}");
        Assert.True(totals.ShownCallable >= MinimumShownCallable, $"callable roles shown {totals.ShownCallable} < {MinimumShownCallable}");
        Assert.True(totals.MultiNameRefusals >= MinimumMultiNameRefusals, $"multi-name refusals {totals.MultiNameRefusals} < {MinimumMultiNameRefusals}");
        Assert.Equal(0, totals.UnattributedLifts);
        Assert.Equal(0, totals.FinalTreeNoCounterpart);
    }

    private const int MinimumPrograms = 4024;
    private const int MinimumNameOccurrences = 17778;
    private const int MinimumParameterVerdicts = 6169;
    private const int MinimumOpenHeads = 92;
    private const int MinimumParameterOpenHeads = 9;
    private const int MinimumFamilies = 106;
    private const int MinimumUnnameableFamilies = 21;
    private const int MinimumForwardedLevels = 81;
    private const int MinimumPromotionsOverChain = 8364;
    private const int MinimumPromotionsOverTree = 70;
    private const int MinimumPromotedNames = 154;
    private const int MinimumResolvedThroughOpen = 36;
    private const int MinimumForwardingOwn = 45;
    private const int MinimumForwardingCaptured = 9;
    private const int MinimumForwardingForwarded = 113;
    private const int MinimumCollisionLevels = 225;
    private const int MinimumConflictingLevels = 8;
    private const int MinimumValidityChains = 213;
    private const int MinimumForwardingUnavailable = 20;
    private const int MinimumUnavailableFromBareForwarding = 13;
    private const int MinimumShownValue = 35;
    private const int MinimumShownCallable = 335;
    private const int MinimumMultiNameRefusals = 3;

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

        // A slot role the output shows: `Inc` fills position 1 of the clause family `Pick`, a VALUE slot, so it is lifted
        // and `Use` receives a forwarded `x`. The family's lifting signature names its positions `n` and `v`.
        yield return new object[]
        {
            "Inc(x) = x + 1\nPick(0, v) = 0\nPick(n, v) = v\nUse = Pick(1, Inc)\nUse(4)",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["Use", "Inc", "Pick"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := [], properties := [], forwarded := ["x"] } :: p_0
            def p_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p_0
            def p_3 : List OwnerLevel := { parameters := ["v"], properties := [] } :: p_0
            def p_4 : List OwnerLevel := { parameters := ["n", "v"], properties := [] } :: p_0
            #guard selectOwnedDeclaration p_1 "Pick" == .property 1
            #guard elaboratesToParameter p_1 "Pick" == false
            #guard selectOwnedDeclaration p_1 "Inc" == .property 1
            #guard elaboratesToParameter p_1 "Inc" == false
            #guard selectOwnedDeclaration p_2 "x" == .parameter 0
            #guard elaboratesToParameter p_2 "x" == true
            #guard selectOwnedDeclaration p_4 "v" == .parameter 0
            #guard elaboratesToParameter p_4 "v" == true
            #guard selectOwnedDeclaration p_0 "Use" == .property 0
            #guard elaboratesToParameter p_0 "Use" == false
            #guard promotes p_0 "Use" == some false
            #guard promotes p_1 "Pick" == some false
            #guard promotes p_1 "Inc" == some false
            #guard forwardingSource p_1 true "x" == .forwardedParameter
            #guard liftingSlotRole .family 1 true == .value -- Pick: Inc
            #guard familyLiftingSignature? [clause (.sequenceValue [.litInt 0, .bind "v"]), clause (.sequenceValue [.bind "n", .bind "v"])] == some [.capture { name := "n" }, .capture { name := "v" }] -- family Pick

            """,
        };

        // A refused forward that names one binding: the closed `Use(x)` binds `x`, so of the two names `Scale` requests
        // only `k` is unavailable.
        yield return new object[]
        {
            "Scale(x, k) = x * k\nUse(x) = Scale + 0\nUse(3)",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["Scale", "Use"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := ["x", "k"], properties := [] } :: p_0
            def p_2 : List OwnerLevel := { parameters := ["x"], properties := [] } :: p_0
            #guard selectOwnedDeclaration p_1 "x" == .parameter 0
            #guard elaboratesToParameter p_1 "x" == true
            #guard selectOwnedDeclaration p_1 "k" == .parameter 0
            #guard elaboratesToParameter p_1 "k" == true
            #guard selectOwnedDeclaration p_2 "Scale" == .property 1
            #guard elaboratesToParameter p_2 "Scale" == false
            #guard selectOwnedDeclaration p_0 "Use" == .property 0
            #guard elaboratesToParameter p_0 "Use" == false
            #guard promotes p_0 "Use" == some false
            #guard forwardingSource p_2 false "k" == .unavailable

            """,
        };

        // The same operand where `Use(p)` binds neither name: one bare reference, two unbound names, no guard.
        yield return new object[]
        {
            "Scale(x, k) = x * k\nUse(p) = Scale + 0\nUse(3)",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["Scale", "Use"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := ["x", "k"], properties := [] } :: p_0
            def p_2 : List OwnerLevel := { parameters := ["p"], properties := [] } :: p_0
            #guard selectOwnedDeclaration p_1 "x" == .parameter 0
            #guard elaboratesToParameter p_1 "x" == true
            #guard selectOwnedDeclaration p_1 "k" == .parameter 0
            #guard elaboratesToParameter p_1 "k" == true
            #guard selectOwnedDeclaration p_2 "Scale" == .property 1
            #guard elaboratesToParameter p_2 "Scale" == false
            #guard selectOwnedDeclaration p_0 "Use" == .property 0
            #guard elaboratesToParameter p_0 "Use" == false
            #guard promotes p_0 "Use" == some false
            -- 1 refused forward(s) not attributed: 2 unbound names share the bare reference(s)

            """,
        };

        // Bare forwarding reports each parameter it cannot supply: `Use(p) = Mix` supplies `p` and refuses `q` and `r`.
        yield return new object[]
        {
            "Mix(p, q, r) = p + q + r\nUse(p) = Mix\nUse(1)",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["Mix", "Use"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := ["p", "q", "r"], properties := [] } :: p_0
            def p_2 : List OwnerLevel := { parameters := ["p"], properties := [] } :: p_0
            #guard selectOwnedDeclaration p_1 "p" == .parameter 0
            #guard elaboratesToParameter p_1 "p" == true
            #guard selectOwnedDeclaration p_1 "q" == .parameter 0
            #guard elaboratesToParameter p_1 "q" == true
            #guard selectOwnedDeclaration p_1 "r" == .parameter 0
            #guard elaboratesToParameter p_1 "r" == true
            #guard selectOwnedDeclaration p_2 "Mix" == .property 1
            #guard elaboratesToParameter p_2 "Mix" == false
            #guard selectOwnedDeclaration p_0 "Use" == .property 0
            #guard elaboratesToParameter p_0 "Use" == false
            #guard promotes p_0 "Use" == some false
            #guard forwardingSource p_2 false "q" == .unavailable
            #guard forwardingSource p_2 false "r" == .unavailable

            """,
        };

        // The by-shape supply beside an enclosing binding (FD-F2): `Use`'s own collector `items` is the read, and by
        // name the callee's `xs` is `Outer`'s parameter, one level out.
        yield return new object[]
        {
            "Get([*xs]) = xs.count\nOuter(*xs) = {\n    Use(*items) = [Get][0]\n    Use(3, 4)\n}\nOuter(1, 2, 3)",
            """
            def p_0 : List OwnerLevel := { parameters := [], properties := ["Get", "Outer"] } :: prelude
            def p_1 : List OwnerLevel := { parameters := ["xs"], properties := [] } :: p_0
            def p_2 : List OwnerLevel := { parameters := ["xs"], properties := ["Use"] } :: p_0
            def p_3 : List OwnerLevel := { parameters := ["items"], properties := [] } :: p_2
            #guard selectOwnedDeclaration p_1 "xs" == .parameter 0
            #guard elaboratesToParameter p_1 "xs" == true
            #guard selectOwnedDeclaration p_1 "count" == .property 2
            #guard elaboratesToParameter p_1 "count" == false
            #guard selectOwnedDeclaration p_3 "Get" == .property 2
            #guard elaboratesToParameter p_3 "Get" == false
            #guard selectOwnedDeclaration p_2 "Use" == .property 0
            #guard elaboratesToParameter p_2 "Use" == false
            #guard selectOwnedDeclaration p_0 "Outer" == .property 0
            #guard elaboratesToParameter p_0 "Outer" == false
            #guard promotes p_0 "Outer" == some false
            #guard forwardingSource p_3 false "items" == .ownParameter -- by shape, for the callee's "xs"
            #guard forwardingSource p_3 false "xs" == .capturedParameter 1 -- FD-F2: by name; C# supplies .ownParameter "items" by shape
            #guard ownedConflicts p_2 == []
            #guard validOwnedDeclarations p_3 == true

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
        int InvalidChains,
        int ByShapeSupplies,
        int ByShapeBesideEnclosingBinding,
        int UnavailableFromBareForwarding,
        int BareRefusalsOfForm,
        int MultiNameRefusals,
        int MultiNameRefusalNames,
        int WrittenCalls,
        int WrittenPositions,
        int ReceiverOutsideSupply,
        int ShownValue,
        int ReportedValue,
        int ShownCallable,
        int RefusedOrCallable,
        int NoRoleSensitiveReference,
        int CalleeNotRead,
        int PositionNotRead,
        int SynthesizedCallSlots,
        int NoFinalCounterpartSlots,
        int RoleProgramsShown)
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
            int Slots(FrontEndSlotOutcome outcome) => guarded.Sum(program => program.SlotOutcomes.GetValueOrDefault(outcome));
            var bareRefusals = guarded.SelectMany(static program => program.BareRefusals).ToList();
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
                levels.Count(static pair => GuardsValidity(pair.Level) && !ValidityExpected(pair.Level)),
                forwardings.Count(static forwarding => forwarding.Requested is not null),
                forwardings.Count(static forwarding => forwarding.Requested is not null && ByShapeFinding(forwarding) == EnclosingBindingShapeFindingId),
                bareRefusals.Sum(static refusal => refusal.Attributed.Count),
                bareRefusals.Sum(static refusal => refusal.Reports - refusal.Attributed.Count),
                guarded.Sum(static program => program.Lifts.MultiNameRefusals),
                guarded.Sum(static program => program.Lifts.MultiNameRefusalNames),
                guarded.Sum(static program => program.WrittenCalls),
                guarded.Sum(static program => program.WrittenPositions),
                Slots(FrontEndSlotOutcome.ReceiverOutsideSupply),
                Slots(FrontEndSlotOutcome.ShownValue) + Slots(FrontEndSlotOutcome.ReportedValue),
                Slots(FrontEndSlotOutcome.ReportedValue),
                Slots(FrontEndSlotOutcome.ShownCallable),
                Slots(FrontEndSlotOutcome.RefusedOrCallable),
                Slots(FrontEndSlotOutcome.NoRoleSensitiveReference),
                Slots(FrontEndSlotOutcome.CalleeNotRead),
                Slots(FrontEndSlotOutcome.PositionNotRead),
                Slots(FrontEndSlotOutcome.SynthesizedCall),
                Slots(FrontEndSlotOutcome.NoFinalCounterpart),
                guarded.Count(static program => program.SlotRoles.Count > 0));
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
            (dotnet/tests/KatLang.Tests/SemanticExplorerCorpus.cs), the language specification
            (dotnet/tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs), the SEM-2B generated corpus
            (fuzz/KatLang.ParserFuzz/Semantic/SemanticCorpus.cs, every base, alpha-rename and declaration-reorder source with
            `trace(x) = x` and `wait(x) = x` prepended, as lean/CoreTests/SemanticGeneratedCases.lean encodes it) and
            the tutorial's source fences (tutorial.md, by ordinal); and on the front-end witnesses
            (dotnet/tests/KatLang.Tests/FrontEndWitnesses.cs), each a base program with its alpha-rename and its
            declaration-reorder, the two SEM-2B transformations. Lean has no front end: the other generated
            corpora evaluate a tree C# already elaborated, so they take these decisions as INPUT. Here each
            decision is an expectation. FD-F1 and FD-F2 below record the by-shape supply at each named occurrence.

            What is compared (generator: dotnet/tests/KatLang.Tests/FrontEndDecisionCorpus.cs):
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
              and, over an encoded tree only, a program with an invalid open target or an unsupported literal or anonymous block address.
              Promotion is decided at DETECTION, on declarations no pass has classified yet: an encoded tree holds every
              property as written (no local-only exposure), so a member or provider the complete pipeline later makes
              local-only is found here as C# found it (FD-P1: seven probes answer otherwise over a tree taken after
              exposure classification, pinned by `Promotion_FindsDeclarationsBeforeExposureClassifiesThem`);
            - `forwardingSource` — each requested capture of a lifted call against the corresponding synthesized
              argument, in order (including repeated names). The entire set of lifts agrees with the resolver's
              synthesis counter. An argument reads a parameter added to this level, one it already owned or the
              nearest enclosing binding. A REFUSED forward is `.unavailable` where the refusal names one binding: a
              closed value operand that stays bare although its callee requires supplied arguments, when exactly one
              requested name has no parameter binding there; and a closed lone row whose bare forwarding reported
              `UnforwardableParameter` naming an unbound fixed capture, including a report beside a pattern mismatch. A bare
              reference whose callee leaves two or more names unbound is ONE observation for all of them and is
              not attributed, and a bare-forwarding refusal of a pattern's FORM is `bareForwardingArgument`'s
              decision, not this function's: both are counted and left as comments.
              THE BY-SHAPE SUPPLY (KatLang.lean, "Implicit argument resolution": a caller whose whole written list is
              one collector re-supplies a callee whose whole list is one group holding a lone collector, by shape
              rather than by name) is the language's rule, and `forwardingSource` decides by NAME only. Each such
              occurrence therefore holds two guards: the read C# emitted, the caller's own collector
              (`.ownParameter`), and this function's answer for the callee's name — `.unavailable` (FD-F1: by name
              nothing would be supplied) or `.capturedParameter` (FD-F2: by name an ENCLOSING binding of that name
              would be, and the rule does not say which wins);
            - `conflictingOwnedNames` (as `ownedConflicts chain`) — the properties of each declaring level the
              complete pipeline's `ParameterPropertyCollisionValidator` reported, located by declaration span. The
              root's phantom signature is checked against the root's own declarations only (chain `p_0`), and every
              nested level against the callable chain, as that validator does; `validOwnedDeclarations` over the
              same chain of every innermost level;
            - `liftingSlotRole` — `FormulaLiftingRoles.SlotRole` on every callee kind, positions 0..{RolePositions - 1},
              with and without a known position: the whole table. And PER WRITTEN CALL, at every supplied slot whose
              role the pipeline's OUTPUT shows. A diagnostic of kind UnliftableClauseFamily at the slot's own reference
              identifies a value role. The tree alone shows the decision where a slot holds a bare reference whose
              callee has a nameable lifting signature that requires supplied arguments: in a VALUE role it is the
              synthesized call the complete tree holds there, and in a CALLABLE role it stays as written although
              nothing could have refused its lift (an inferring body, or a closed one that binds every requested
              name). The callee's KIND is read from its Q3 invocation endpoint, never from the resolver's private
              classification, and its row of C#'s table must give the role shown, or generation throws; a selected
              fallback `R.F(args)` is the call `F(R, args)`, and an edge the runtime decides gives its arguments a
              dynamic callee. Every other slot shows no role (the partition says why): the kinds `user` and `dynamic`
              give one row and cannot be told apart by any output, nor can `family` and `strictValue`.

            Each chain is rebuilt from the DETECTED tree's nesting (a body's stored parameter patterns and
            property names, a clause body's head binders), innermost level first, ending in the prelude's
            property level. `forwarded` lists the parameters automatic forwarding added afterwards (the resolved
            signature minus the detected one); the owner walk never reads it. Identical guards of one program
            are emitted once, with their multiplicity, and programs whose levels and guards are identical share
            one block that names every one of them ({blocks.Count} blocks): nothing is sampled.

            Partition:
            - corpus programs: {programs.Count} (explorer {CorpusCount(FrontEndDecisionCorpus.ExplorerCorpus)}, spec {CorpusCount(FrontEndDecisionCorpus.LanguageSpecCorpus)}, SEM-2B {CorpusCount(FrontEndDecisionCorpus.SemanticGeneratedCorpus)}, tutorial {CorpusCount(FrontEndDecisionCorpus.TutorialCorpusName)},
              witness {CorpusCount(FrontEndDecisionCorpus.WitnessCorpus)}: {FrontEndWitnesses.All.Count} witnesses, three members each)
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
              {totals.ByShapeSupplies} of the own reads supplied by shape under another name ({totals.ByShapeSupplies - totals.ByShapeBesideEnclosingBinding} FD-F1, {totals.ByShapeBesideEnclosingBinding} FD-F2); unattributed lifts: {totals.UnattributedLifts}
            - refused forwards: {totals.ForwardingUnavailable} unavailable sources ({totals.ForwardingUnavailable - totals.UnavailableFromBareForwarding} at closed value operands, {totals.UnavailableFromBareForwarding} from bare-forwarding reports);
              not attributed: {totals.MultiNameRefusals} bare references whose callee leaves {totals.MultiNameRefusalNames} names unbound between them,
              {totals.BareRefusalsOfForm} bare-forwarding refusals of a pattern's form
            - slot roles: {totals.WrittenCalls} call nodes, {totals.WrittenPositions} positions including dot receivers; role shown at {totals.ShownValue + totals.ShownCallable} slots of {totals.RoleProgramsShown} programs
              ({totals.ShownValue} value, including {totals.ReportedValue} unliftable-family reports; {totals.ShownCallable} callable: an available lift not made); not shown: {totals.NoRoleSensitiveReference} hold no
              role-sensitive reference, {totals.RefusedOrCallable} stay bare where a requested name is unbound (refused or callable);
              {totals.ReceiverOutsideSupply} receivers outside the argument supply; not read: {totals.CalleeNotRead} with no static callee classification, {totals.PositionNotRead} after an inserted spread, {totals.SynthesizedCallSlots} of a call
              the parser synthesized, {totals.NoFinalCounterpartSlots} with no counterpart in the complete tree
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

        // One literal for all the corpora exceeds Lean's term-elaboration recursion limit.
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
                string Probe(string name) => $"forwardingSource {Chain(level, callable: false)} {(level.Infers ? "true" : "false")} {LeanAstEncoder.QuoteString(name)}";
                Guard($"#guard {Probe(forwarding.Name)} == {source}{(forwarding.Requested is null ? "" : $" -- by shape, for the callee's {LeanAstEncoder.QuoteString(forwarding.Requested)}")}");
                if (forwarding.Requested is { } requested)
                {
                    // The by-shape supply: the read above is the caller's own collector, and `forwardingSource`, which
                    // decides by NAME, answers for the callee's name as forwarding by name would.
                    var finding = ByShapeFinding(forwarding)
                        ?? throw new InvalidOperationException(
                            $"{program.Corpus}/{program.Id} at level {level.Index}: by name '{requested}' is {forwarding.ByName}, yet C# supplies '{forwarding.Name}' by shape. Review this occurrence.");
                    Guard($"#guard {Probe(requested)} == {forwarding.ByName} -- {finding}: by name; C# supplies {source} {LeanAstEncoder.QuoteString(forwarding.Name)} by shape");
                }
            }
        }

        foreach (var role in program.SlotRoles)
        {
            Guard($"#guard liftingSlotRole {CalleeKindTerm(role.Kind)} {role.Position} {(role.PositionKnown ? "true" : "false")} == " +
                $"{(role.Role == LiftingRole.Value ? ".value" : ".callable")} -- {LeanComment(role.Callee)}: {LeanComment(role.Reference)}");
        }

        if (program.Lifts.MultiNameRefusals > 0)
        {
            Guard($"-- {program.Lifts.MultiNameRefusals} refused forward(s) not attributed: {program.Lifts.MultiNameRefusalNames} unbound names share the bare reference(s)");
        }

        foreach (var refusal in program.BareRefusals.Where(static refusal => refusal.Attributed.Count < refusal.Reports))
        {
            Guard($"-- bare forwarding of {LeanComment(refusal.Callee)} refused at level {refusal.Level.Index}: {refusal.Reports - refusal.Attributed.Count} report(s) of a pattern's form (bareForwardingArgument, not forwardingSource)");
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

    internal const string CollectorShapeFindingId = "FD-F1";
    internal const string EnclosingBindingShapeFindingId = "FD-F2";

    /// <summary>
    /// The finding a by-shape supply is recorded under, by what forwarding BY NAME has for the callee's name: nothing
    /// (FD-F1, the rule as the language states it), or an enclosing parameter binding (FD-F2, where the two rules each
    /// have an answer). Null for anything else, which is no reviewed class.
    /// </summary>
    private static string? ByShapeFinding(FrontEndForwarding forwarding)
        => forwarding.ByName is ".unavailable" ? CollectorShapeFindingId
            : forwarding.ByName is { } source && source.StartsWith(".capturedParameter ", StringComparison.Ordinal) ? EnclosingBindingShapeFindingId
            : null;

    /// <summary>A callee kind as a Lean <c>LiftingCalleeKind</c> term, spelled as the role table spells it.</summary>
    private static string CalleeKindTerm(LiftingCallee callee) => callee.Kind switch
    {
        LiftingCalleeKind.Dynamic => ".dynamic",
        LiftingCalleeKind.User => ".user",
        LiftingCalleeKind.Family => ".family",
        LiftingCalleeKind.StrictValue => ".strictValue",
        LiftingCalleeKind.Builtin => $"(.builtin .{callee.Builtin}Builtin)",
        _ => throw new InvalidOperationException($"Unknown callee kind {callee.Kind}."),
    };

    /// <summary>A written name inside a Lean line comment: one line, as written.</summary>
    private static string LeanComment(string text) => text.ReplaceLineEndings(" ");

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
