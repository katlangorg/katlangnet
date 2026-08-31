namespace KatLang.Tests;

/// <summary>
/// Golden fidelity guard for the <c>open</c>/visibility differential family.
///
/// <para>
/// A differential case only compares Lean against C# if BOTH sides run the same
/// program. Track 9 found 109 cases where they did not: the Lean side declared
/// <c>publicProp "X"</c> for source whose <c>X</c> elaborates as PRIVATE. That
/// mistake is invisible in a green suite, because a wrong-but-consistent pair of
/// programs still agrees with itself.
/// </para>
///
/// <para>
/// The corpus now DERIVES every Lean program from the source's real elaborated
/// AST through <see cref="LeanAstEncoder"/>, so same-program fidelity holds by
/// construction — which makes the meaningful check the ENCODING itself. This
/// family is where the encoding carries the semantics under test (visibility,
/// exposure, open ordering and dedup, implicit-parameter promotion), so every
/// derived program here is pinned against manually reviewed golden Lean text.
/// The goldens are hand-maintained constants, never produced by the encoder at
/// assertion time; an encoder change that altered exposure metadata, open
/// encoding, or parameter promotion fails these pins by name.
/// </para>
/// </summary>
public class OpenVisibilityCorpusFidelityTests
{
    // ----- reviewed golden fragments -------------------------------------------

    private const string LibPublicX =
        "privateProp \"Lib\" (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 101])] [])";

    private const string LibPrivateX =
        "privateProp \"Lib\" (alg [] [] [privateProp \"X\" (alg [] [] [] [.num 101])] [])";

    private const string LibPublicSX =
        "privateProp \"Lib\" (alg [] [] [publicProp \"S\" (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 101])] [])] [])";

    private const string ResolveA = ".resolve \"A\"";

    private const string CallA707 = "(.call (.resolve \"A\") [.num 707])";

    private static string Golden(string props, string output)
        => $".algorithmExpr (alg [] [] [{props}] [{output}])";

    /// <summary>
    /// The reviewed golden Lean program for every case of the family, keyed by
    /// the corpus ValueId. Property ORDER matters and follows the real
    /// elaboration (clause definitions such as <c>Lib(p) = ...</c> are
    /// elaborated per same-name clause group and appended after plain
    /// properties).
    /// </summary>
    private static readonly IReadOnlyDictionary<string, string> GoldenPrograms =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["openPublicMember"] = Golden(
                LibPublicX + ", privateProp \"A\" (alg [] [.resolve \"Lib\"] [] [.resolve \"X\"])",
                ResolveA),

            // `open` never exposes a private member, so `X` is unresolvable and
            // the front end promotes it to an implicit parameter of `A`.
            ["openPrivateMemberHidden"] = Golden(
                LibPrivateX + ", privateProp \"A\" (alg [\"X\"] [.resolve \"Lib\"] [] [.param \"X\"])",
                CallA707),

            // Public but NOT exported: the member depends on its owner's parameter.
            ["openLocalOnlyCapturedParamsHidden"] = Golden(
                "privateProp \"A\" (alg [] [.resolve \"Lib\"] [] [.resolve \"X\"]), "
                    + "privateProp \"Lib\" (alg [\"p\"] [] [publicLocalProp \"X\" .localCapturedAncestorParams "
                    + "(alg [] [] [] [(.binary .add (.param \"p\") (.num 101))])] [.resolve \"X\"])",
                ResolveA),

            ["openTwoProvidersAmbiguous"] = Golden(
                "privateProp \"L1\" (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 101])] []), "
                    + "privateProp \"L2\" (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 202])] []), "
                    + "privateProp \"A\" (alg [] [.resolve \"L1\", .resolve \"L2\"] [] [.resolve \"X\"])",
                ResolveA),

            // Duplicate NAMED targets deduplicate first-occurrence-wins, so they
            // are one provider and never a spurious ambiguity (Lean: resolveAllOpens).
            ["openDuplicateTargetDedup"] = Golden(
                LibPublicX + ", privateProp \"A\" (alg [] [.resolve \"Lib\", .resolve \"Lib\"] [] [.resolve \"X\"])",
                ResolveA),

            ["openDuplicateDottedTargetDedup"] = Golden(
                LibPublicSX + ", privateProp \"A\" (alg [] [(.dotCall (.resolve \"Lib\") \"S\" none), "
                    + "(.dotCall (.resolve \"Lib\") \"S\" none)] [] [.resolve \"X\"])",
                ResolveA),

            // Inline blocks get positional keys and are NEVER deduplicated, so two
            // structurally identical blocks really are two providers.
            ["openDuplicateInlineBlocksAmbiguous"] = Golden(
                "privateProp \"A\" (alg [] [(.algorithmExpr (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 101])] [])), "
                    + "(.algorithmExpr (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 202])] []))] [] [.resolve \"X\"])",
                ResolveA),

            ["openInlineBlock"] = Golden(
                "privateProp \"A\" (alg [] [(.algorithmExpr (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 101])] []))] "
                    + "[] [.resolve \"X\"])",
                ResolveA),

            ["openInlineBlockPrivateHidden"] = Golden(
                "privateProp \"A\" (alg [\"X\"] [(.algorithmExpr (alg [] [] [privateProp \"X\" (alg [] [] [] [.num 101])] []))] "
                    + "[] [.param \"X\"])",
                CallA707),

            ["openDottedPath"] = Golden(
                LibPublicSX + ", privateProp \"A\" (alg [] [(.dotCall (.resolve \"Lib\") \"S\" none)] [] [.resolve \"X\"])",
                ResolveA),

            // A dotted open path requires every member after the lexical head to
            // be public, so a private intermediate provides nothing.
            ["openDottedPathPrivateIntermediate"] = Golden(
                "privateProp \"Lib\" (alg [] [] [privateProp \"S\" (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 101])] [])] []), "
                    + "privateProp \"A\" (alg [\"X\"] [(.dotCall (.resolve \"Lib\") \"S\" none)] [] [.param \"X\"])",
                CallA707),

            // Ownership-first: an owned property always beats an opened one.
            ["openLocalShadowsOpenedName"] = Golden(
                LibPublicX
                    + ", privateProp \"A\" (alg [] [.resolve \"Lib\"] [privateProp \"X\" (alg [] [] [] [.num 202])] [.resolve \"X\"])",
                ResolveA),

            ["openAncestorPropertyWins"] = Golden(
                LibPublicX
                    + ", privateProp \"A\" (alg [] [] [privateProp \"X\" (alg [] [] [] [.num 202]), "
                    + "privateProp \"Inner\" (alg [] [.resolve \"Lib\"] [] [.resolve \"X\"])] [.resolve \"Inner\"])",
                ResolveA),

            // A nested `open` is visible to descendants but never leaks outward.
            ["openParentScopeReachesChild"] = Golden(
                LibPublicX
                    + ", privateProp \"A\" (alg [] [.resolve \"Lib\"] [privateProp \"Inner\" (alg [] [] [] [.resolve \"X\"])] "
                    + "[.resolve \"Inner\"])",
                ResolveA),

            ["openNestedDoesNotLeakOutward"] = Golden(
                LibPublicX
                    + ", privateProp \"A\" (alg [\"X\"] [] [privateProp \"Inner\" (alg [] [.resolve \"Lib\"] [] [.resolve \"X\"])] "
                    + "[.param \"X\"])",
                CallA707),

            // The open head resolves by direct lexical lookup, which sees a
            // private sibling defined later in the same body.
            ["openHeadDefinedLater"] = Golden(
                "privateProp \"A\" (alg [] [.resolve \"Lib\"] [] [.resolve \"X\"]), " + LibPublicX,
                ResolveA),

            // The prelude is the outermost lexical scope, so ownership-first
            // reaches the builtin before opens are consulted.
            ["openBuiltinNameCollision"] = Golden(
                "privateProp \"Lib\" (alg [] [] [publicProp \"count\" (alg [] [] [] [.num 101])] []), "
                    + "privateProp \"A\" (alg [] [.resolve \"Lib\"] [] "
                    + "[(.call (.resolve \"count\") [(.listLiteral [.num 1, .num 2, .num 3])])])",
                ResolveA),

            // A builtin is never a legal open target; validation runs over the
            // whole open list before any name is resolved through it.
            ["openBuiltinTargetIsIllegal"] = Golden(
                LibPublicX + ", privateProp \"A\" (alg [] [.resolve \"count\", .resolve \"Lib\"] [] [.resolve \"X\"])",
                ResolveA),

            // Structural dot access deliberately ignores visibility; `open` does
            // not. Pinning both spellings keeps the two rules from collapsing.
            ["structuralDotSeesPrivateMember"] = Golden(
                LibPrivateX,
                "(.dotCall (.resolve \"Lib\") \"X\" none)"),

            // A member `open` must not expose cannot become a SECOND provider.
            ["openPrivateMemberIsNotASecondProvider"] = Golden(
                "privateProp \"Pub\" (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 101])] []), "
                    + "privateProp \"Lib\" (alg [] [] [privateProp \"X\" (alg [] [] [] [.num 202])] []), "
                    + "privateProp \"A\" (alg [] [.resolve \"Pub\", .resolve \"Lib\"] [] [.resolve \"X\"])",
                ResolveA),

            ["openLocalOnlyMemberIsNotASecondProvider"] = Golden(
                "privateProp \"Pub\" (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 101])] []), "
                    + "privateProp \"A\" (alg [] [.resolve \"Pub\", .resolve \"Lib\"] [] [.resolve \"X\"]), "
                    + "privateProp \"Lib\" (alg [\"p\"] [] [publicLocalProp \"X\" .localCapturedAncestorParams "
                    + "(alg [] [] [] [(.binary .add (.param \"p\") (.num 202))])] [.resolve \"X\"])",
                ResolveA),
        };

    private static IReadOnlyList<ExplorerCase> Family()
        => SemanticExplorerCorpus.AllCases()
            .Where(static c => c.TemplateId == "special"
                && (c.ValueId.StartsWith("open", StringComparison.Ordinal)
                    || c.ValueId.StartsWith("structuralDot", StringComparison.Ordinal)))
            .ToList();

    public static TheoryData<string> FamilyIds()
    {
        var data = new TheoryData<string>();
        foreach (var explorerCase in Family())
            data.Add(explorerCase.ValueId);
        return data;
    }

    [Theory]
    [MemberData(nameof(FamilyIds))]
    public void DerivedLeanProgramMatchesReviewedGolden(string valueId)
    {
        var explorerCase = Family().Single(c => c.ValueId == valueId);
        Assert.True(
            GoldenPrograms.TryGetValue(valueId, out var golden),
            $"'{valueId}' has no reviewed golden Lean program in this test; add one deliberately.");
        Assert.True(
            golden == explorerCase.LeanProgram,
            $"Open/visibility case '{valueId}': the Lean program derived from the real elaborated AST "
            + "does not match the reviewed golden.\n"
            + $"Golden:\n{golden}\n"
            + $"Derived from real elaborated AST:\n{explorerCase.LeanProgram}");
    }

    /// <summary>Every golden belongs to a live corpus case — no orphaned pins.</summary>
    [Fact]
    public void EveryGoldenHasALiveCorpusCase()
    {
        var ids = Family().Select(c => c.ValueId).ToHashSet(StringComparer.Ordinal);
        foreach (var golden in GoldenPrograms.Keys)
            Assert.Contains(golden, ids);
    }

    /// <summary>
    /// The family must keep covering every visibility/lookup behavior the task
    /// of pinning it exists for. A case removed or renamed away shows up here
    /// rather than as a quietly narrower corpus.
    /// </summary>
    [Fact]
    public void FamilyCoversEveryPinnedVisibilityBehavior()
    {
        var ids = Family().Select(c => c.ValueId).ToHashSet(StringComparer.Ordinal);

        string[] required =
        [
            "openPublicMember",                     // public member exposed
            "openPrivateMemberHidden",              // private member not exposed
            "openLocalOnlyCapturedParamsHidden",    // public but not exported
            "openTwoProvidersAmbiguous",            // two-provider ambiguity
            "openDuplicateTargetDedup",             // duplicate named target is one provider
            "openDuplicateDottedTargetDedup",
            "openDuplicateInlineBlocksAmbiguous",   // inline blocks are never deduplicated
            "openInlineBlock",                      // inline-block interaction
            "openInlineBlockPrivateHidden",
            "openDottedPath",                       // dotted-path provider
            "openDottedPathPrivateIntermediate",
            "openLocalShadowsOpenedName",           // local shadowing
            "openAncestorPropertyWins",             // ownership-first through the parent chain
            "openParentScopeReachesChild",          // nested scope sees an ancestor's open
            "openNestedDoesNotLeakOutward",         // ... and never the reverse
            "openHeadDefinedLater",
            "openBuiltinNameCollision",             // builtin-name collision
            "openBuiltinTargetIsIllegal",
            "structuralDotSeesPrivateMember",       // structural access is not exposure
            "openPrivateMemberIsNotASecondProvider",     // hidden members never add ambiguity
            "openLocalOnlyMemberIsNotASecondProvider",
        ];

        foreach (var id in required)
            Assert.Contains(id, ids);
    }

    /// <summary>
    /// The encoder must stay fail-loud. An encoder that quietly approximated an
    /// unfamiliar node would reintroduce exactly the fidelity gap it guards.
    /// Grace is consumed and stripped by front-end elaboration (no elaborated
    /// tree contains one) and NativeCall exists only inside prelude/host
    /// wrapper bodies — both are deliberate exclusions, not gaps.
    /// </summary>
    [Fact]
    public void EncoderRejectsNodesItDoesNotModel()
    {
        var grace = new Expr.Grace(new Expr.Resolve("a"), -1);
        Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeExpr(grace));

        var native = new Expr.NativeCall("abs", ["value"]);
        Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeExpr(native));

        // Algorithm.User and Algorithm.Conditional are modelled; Algorithm.Builtin
        // is not (a prelude member never appears inside a source program's AST).
        var builtin = new Algorithm.Builtin(BuiltinId.count);
        Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeAlgorithm(builtin));
    }
}
