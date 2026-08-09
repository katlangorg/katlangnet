namespace KatLang.Tests;

/// <summary>
/// Corpus-fidelity guard for the <c>open</c>/visibility differential family.
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
/// Visibility and exposure ARE the semantics this family tests, and the front
/// end additionally reshapes unresolvable names into implicit parameters, so
/// every declared Lean program here is checked against the encoding of the
/// source's real elaborated AST rather than reviewed by eye.
/// </para>
/// </summary>
public class OpenVisibilityCorpusFidelityTests
{
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
            data.Add(explorerCase.Id);
        return data;
    }

    [Theory]
    [MemberData(nameof(FamilyIds))]
    public void DeclaredLeanProgramMatchesRealElaboration(string caseId)
    {
        var explorerCase = Family().Single(c => c.Id == caseId);
        Assert.NotNull(explorerCase.LeanProgram);

        var parsed = Parser.Parse(explorerCase.Source);
        Assert.False(
            parsed.HasErrors,
            $"[{caseId}] " + string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));

        Assert.Equal(LeanAstEncoder.EncodeProgram(parsed.Root), explorerCase.LeanProgram);
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
    /// </summary>
    [Fact]
    public void EncoderRejectsNodesItDoesNotModel()
    {
        var unmodelled = new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2));
        Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeExpr(unmodelled));

        // Algorithm.User and Algorithm.Conditional are modelled; Algorithm.Builtin
        // is not (a prelude member never appears inside a source program's AST).
        var builtin = new Algorithm.Builtin(BuiltinId.count);
        Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeAlgorithm(builtin));
    }
}
