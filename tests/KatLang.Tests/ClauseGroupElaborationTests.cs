namespace KatLang.Tests;

/// <summary>
/// Clause-family build state has ONE owner in the parser (<c>ClauseGroupBuilder</c>,
/// one instance per same-name family per body). These tests pin what that
/// ownership must preserve: the exact ordered diagnostic sequence
/// <c>(Code, Message, Span)</c> for every clause-family failure mode, the
/// first-seen family order (observable through appended property order and
/// through the order of family diagnostics), the isolation of one family's state
/// from another's, the equivalence of the public and plain property spellings,
/// and every historical "does a clause family with this name exist?" question
/// (the duplicate-definition checks of plain, public, and deconstruction
/// declarations).
/// </summary>
public class ClauseGroupElaborationTests
{
    // ── exact diagnostics: (Code, Message, Span), in emission order ─────────

    private const string DuplicateBranchF = "Duplicate branch pattern for conditional algorithm 'F'.";
    private const string VisibilityMismatchF = "All clauses of 'F' must use the same public modifier. Either mark every clause public or none of them.";
    private const string DuplicatePropertyA = "Property 'A' is already defined.";

    private static string ArityMismatch(string name, int branch, int arity)
        => $"All branches of conditional algorithm '{name}' must have the same top-level pattern arity. Expected 1 (from first branch), but branch {branch} has arity {arity}.";

    private static string OutputArityMismatch(string name, int branch, int arity)
        => $"All branches of conditional algorithm '{name}' must have the same top-level output arity. Expected 1 (from first branch), but branch {branch} has output arity {arity}.";

    private sealed record DiagnosticCase(
        string Id,
        string Source,
        IReadOnlyList<(DiagnosticCode Code, string Message, SourceSpan Span)> Expected);

    private static readonly IReadOnlyList<DiagnosticCase> DiagnosticCases =
    [
        new("dupPattern.literal",
            "F(1) = 100\nF(1) = 200\nF(1)",
            [(DiagnosticCode.DuplicateBranchPattern, DuplicateBranchF, new SourceSpan(2, 1, 2, 10))]),

        new("dupPattern.alphaEquivalentBinders",
            "Equal(x, x) = 1\nEqual(a, a) = 0\nEqual(1, 1)",
            [(DiagnosticCode.DuplicateBranchPattern, "Duplicate branch pattern for conditional algorithm 'Equal'.", new SourceSpan(2, 1, 2, 15))]),

        new("dupPattern.severalInWrittenOrder",
            "F(0) = 0\nF(1) = 1\nF(2) = 2\nF(1) = 11\nF(0) = 10\nF(3)",
            [
                (DiagnosticCode.DuplicateBranchPattern, DuplicateBranchF, new SourceSpan(4, 1, 4, 9)),
                (DiagnosticCode.DuplicateBranchPattern, DuplicateBranchF, new SourceSpan(5, 1, 5, 9)),
            ]),

        // The mismatch is anchored on the NAME token of the offending clause; after a
        // `public` modifier that token sits at column 8.
        new("visibility.plainThenPublic",
            "F(0) = 0\npublic F(x) = 1\nF(1)",
            [(DiagnosticCode.ClauseVisibilityMismatch, VisibilityMismatchF, new SourceSpan(2, 8, 2, 8))]),

        new("visibility.publicThenPlain",
            "public F(0) = 0\nF(x) = 1\nF(1)",
            [(DiagnosticCode.ClauseVisibilityMismatch, VisibilityMismatchF, new SourceSpan(2, 1, 2, 1))]),

        // Only the clause disagreeing with the FIRST clause's visibility is reported.
        new("visibility.thirdClauseAgreesWithFirst",
            "F(0) = 0\npublic F(1) = 1\nF(x) = 2\nF(1)",
            [(DiagnosticCode.ClauseVisibilityMismatch, VisibilityMismatchF, new SourceSpan(2, 8, 2, 8))]),

        new("arity.patternMismatch",
            "F(0) = 0\nF(x, y) = 1\nF(1)",
            [(DiagnosticCode.BranchArityMismatch, ArityMismatch("F", 2, 2), new SourceSpan(2, 1, 2, 11))]),

        new("arity.outputMismatch",
            "F(0) = 0\nF(x) = 1, 2\nF(1)",
            [(DiagnosticCode.BranchOutputArityMismatch, OutputArityMismatch("F", 2, 2), new SourceSpan(2, 1, 2, 11))]),

        // Pattern arity is validated before output arity, both on the same clause span.
        new("arity.bothMismatchPatternFirst",
            "F(0) = 0\nF(x, y) = 1, 2\nF(1)",
            [
                (DiagnosticCode.BranchArityMismatch, ArityMismatch("F", 2, 2), new SourceSpan(2, 1, 2, 14)),
                (DiagnosticCode.BranchOutputArityMismatch, OutputArityMismatch("F", 2, 2), new SourceSpan(2, 1, 2, 14)),
            ]),

        new("arity.laterBranchNumbering",
            "F(0) = 0\nF(1) = 1\nF(a, b) = 2\nF(1)",
            [(DiagnosticCode.BranchArityMismatch, ArityMismatch("F", 3, 2), new SourceSpan(3, 1, 3, 11))]),

        new("collecting.inConditionalFamily",
            "F(0) = 0\nF(*xs) = 1\nF(1)",
            [(DiagnosticCode.InvalidCollectingBinding, "Collecting bindings are only supported in ordinary explicit parameter lists for 'F'.", new SourceSpan(2, 1, 2, 10))]),

        new("grace.inConditionalBody",
            "F(0) = 0\nF(x) = ~y + x\nF(1)",
            [(DiagnosticCode.InvalidGraceMarker, "Grace is not allowed in conditional branch bodies for 'F'.", new SourceSpan(2, 8, 2, 9))]),

        // In-loop duplicate detection precedes the post-loop family validation, so the
        // duplicate is reported before the arity mismatch even though both belong to F.
        new("recovery.duplicateThenArity",
            "F(0) = 0\nF(0) = 1\nF(x, y) = 2\nF(1)",
            [
                (DiagnosticCode.DuplicateBranchPattern, DuplicateBranchF, new SourceSpan(2, 1, 2, 8)),
                (DiagnosticCode.BranchArityMismatch, ArityMismatch("F", 3, 2), new SourceSpan(3, 1, 3, 11)),
            ]),

        // ---- "does a clause family named A exist?" — every historical consumer ----
        // A plain property after a family: the property branch consults the family set.
        new("duplicate.familyThenPlainProperty",
            "A(0) = 1\nA(x) = 2\nA = 5\nA(1)",
            [(DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(3, 1, 3, 1))]),

        // A public property after a family: the public branch consults the family set.
        new("duplicate.familyThenPublicProperty",
            "A(0) = 1\nA(x) = 2\npublic A = 5\nA(1)",
            [(DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(3, 8, 3, 8))]),

        // A deconstruction target after a family: the binding-pattern parser consults it.
        new("duplicate.familyThenDeconstruction",
            "A(0) = 1\nA(x) = 2\nA, B = (1, 2)\nA(1)",
            [(DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(3, 1, 3, 1))]),

        // The reverse direction consults the declared-property set: every clause of the
        // family collides with the earlier plain/public/deconstruction declaration.
        new("duplicate.plainPropertyThenFamily",
            "A = 5\nA(0) = 1\nA(x) = 2\nA(1)",
            [
                (DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(2, 1, 2, 1)),
                (DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(3, 1, 3, 1)),
            ]),

        new("duplicate.publicPropertyThenFamily",
            "public A = 5\nA(0) = 1\nA(x) = 2\nA(1)",
            [
                (DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(2, 1, 2, 1)),
                (DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(3, 1, 3, 1)),
            ]),

        new("duplicate.deconstructionThenFamily",
            "A, B = (1, 2)\nA(0) = 1\nA(x) = 2\nA(1)",
            [
                (DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(2, 1, 2, 1)),
                (DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(3, 1, 3, 1)),
            ]),

        // ---- public/plain property spellings share one mechanic ----
        new("property.plainDuplicate",
            "A = 5\nA = 6\nA",
            [(DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(2, 1, 2, 1))]),

        new("property.publicDuplicate",
            "public A = 5\npublic A = 6\nA",
            [(DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(2, 8, 2, 8))]),

        new("property.plainThenPublicDuplicate",
            "A = 5\npublic A = 6\nA",
            [(DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(2, 8, 2, 8))]),

        new("property.publicThenPlainDuplicate",
            "public A = 5\nA = 6\nA",
            [(DiagnosticCode.DuplicateProperty, DuplicatePropertyA, new SourceSpan(2, 1, 2, 1))]),

        new("property.plainInParentheses",
            "(A = 1, 2)",
            [(DiagnosticCode.DeclarationInParentheses, "A property declaration is not allowed inside parentheses. Use a `{ ... }` block for a scoped algorithm.", new SourceSpan(1, 2, 1, 2))]),

        new("property.publicInParentheses",
            "(public A = 1, 2)",
            [(DiagnosticCode.DeclarationInParentheses, "A property declaration is not allowed inside parentheses. Use a `{ ... }` block for a scoped algorithm.", new SourceSpan(1, 9, 1, 9))]),

        // ---- family order is FIRST-SEEN source order, never alphabetical ----
        // Families Z, A, M are declared in that order; M's duplicate is caught in the
        // parse loop (first), then the post-loop validation visits Z, then A.
        new("order.nonAlphabeticFamilies",
            "Z(0) = 0\nZ(x, y) = 1\nA(0) = 0\nA(1) = 1, 2\nM(0) = 0\nM(0) = 1\nZ(1), A(1), M(0)",
            [
                (DiagnosticCode.DuplicateBranchPattern, "Duplicate branch pattern for conditional algorithm 'M'.", new SourceSpan(6, 1, 6, 8)),
                (DiagnosticCode.BranchArityMismatch, ArityMismatch("Z", 2, 2), new SourceSpan(2, 1, 2, 11)),
                (DiagnosticCode.BranchOutputArityMismatch, OutputArityMismatch("A", 2, 2), new SourceSpan(4, 1, 4, 11)),
            ]),

        // Interleaving clauses of different families does not change family order:
        // Z was seen first (line 1), then A (line 2), then M (line 4).
        new("order.interleavedFamilies",
            "Z(0) = 0\nA(0) = 0\nZ(x, y) = 1\nM(0) = 0\nA(1) = 1, 2\nM(0) = 1\nZ(1)",
            [
                (DiagnosticCode.DuplicateBranchPattern, "Duplicate branch pattern for conditional algorithm 'M'.", new SourceSpan(6, 1, 6, 8)),
                (DiagnosticCode.BranchArityMismatch, ArityMismatch("Z", 2, 2), new SourceSpan(3, 1, 3, 11)),
                (DiagnosticCode.BranchOutputArityMismatch, OutputArityMismatch("A", 2, 2), new SourceSpan(5, 1, 5, 11)),
            ]),
    ];

    public static TheoryData<string> DiagnosticCaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var diagnosticCase in DiagnosticCases)
            data.Add(diagnosticCase.Id);
        return data;
    }

    [Theory]
    [MemberData(nameof(DiagnosticCaseIds))]
    public void ClauseFamilyDiagnostics_AreExactAndOrdered(string caseId)
    {
        var diagnosticCase = DiagnosticCases.Single(c => c.Id == caseId);
        var diagnostics = Parser.ParseSyntax(diagnosticCase.Source).Diagnostics;

        Assert.Equal(
            diagnosticCase.Expected,
            diagnostics.Select(d => (d.Code, d.Message, d.Span)).ToList());
        Assert.All(diagnostics, d => Assert.Equal(DiagnosticSeverity.Error, d.Severity));
    }

    // ── first-seen family order in the elaborated property list ─────────────

    /// <summary>Value-comparable shape of one elaborated property: declaration spans as <c>line:column</c>.</summary>
    private static (string Name, bool IsPublic, string DeclarationSpans, int? BranchCount) Describe(Property property)
        => (property.Name,
            property.IsPublic,
            string.Join(";", property.DeclarationSpans.Select(static span => $"{span.StartLineNumber}:{span.StartColumn}")),
            property.Value is Algorithm.Conditional conditional ? conditional.Branches.Count : null);

    [Fact]
    public void ClauseFamilies_AreAppendedAfterPlainPropertiesInFirstSeenOrder()
    {
        // Z is first seen on line 2, A on line 4; the plain properties P, Q, R keep
        // their in-loop positions and both families follow in first-seen order.
        var root = SourceProvenance.ParseValid(
            "P = 1\nZ(0) = 0\nQ = 2\nA(0) = 0\nZ(x) = x\nR = 3\nA(y) = y\nZ(1), A(1), P, Q, R").Root;

        Assert.Equal(
            [
                ("P", false, "1:1", null),
                ("Q", false, "3:1", null),
                ("R", false, "6:1", null),
                ("Z", false, "2:1;5:1", 2),
                ("A", false, "4:1;7:1", 2),
            ],
            root.Properties.Select(Describe).ToList());

        Assert.Equal([1m, 1m, 1m, 2m, 3m], KatLangEngine.EvaluateToAtoms(
            "P = 1\nZ(0) = 0\nQ = 2\nA(0) = 0\nZ(x) = x\nR = 3\nA(y) = y\nZ(1), A(1), P, Q, R").ToArray());
    }

    [Fact]
    public void PublicAndPlainFamilies_KeepTheirOwnVisibilityAndOrder()
    {
        var root = SourceProvenance.ParseValid(
            "public Z(0) = 0\nA(0) = 0\npublic Z(x) = x\nA(y) = y\nZ(1), A(1)").Root;

        Assert.Equal(
            [
                ("Z", true, "1:8;3:8", 2),
                ("A", false, "2:1;4:1", 2),
            ],
            root.Properties.Select(Describe).ToList());
    }

    [Fact]
    public void RecoveryTree_KeepsInLoopDeclarationsBeforeTheCollidingFamily()
    {
        // The deconstruction's synthetic source and its targets are appended in the
        // parse loop; the colliding family A is appended by the post-loop elaboration.
        var root = SourceProvenance.ParseAllowingDiagnostics("A(0) = 1\nA(x) = 2\nA, B = (1, 2)\nA(1)").Root;

        Assert.Equal(
            [
                ("$deconstruct$0", false, "", null),
                ("A", false, "3:1", null),
                ("B", false, "3:4", null),
                ("A", false, "1:1;2:1", 2),
            ],
            root.Properties.Select(Describe).ToList());
    }

    [Fact]
    public void InvalidFirstClause_StillEstablishesFamilyOrderAndDeclarationIdentity()
    {
        // Z's FIRST clause is invalid once the family is known to be conditional:
        // Grace is forbidden in a true conditional branch body. Recovery still keeps
        // that clause as Z's first branch/declaration and, crucially, records Z as the
        // first-seen family before A. Dropping invalid clauses from the ordering state
        // would reorder the appended families to A, Z and change Z's canonical
        // declaration identity.
        const string source = "Z(0) = ~x\nA(0) = 0\nZ(x) = x\nA(y) = y\nZ(1)";
        var syntax = Parser.ParseSyntax(source);

        Assert.Equal(
            [(DiagnosticCode.InvalidGraceMarker, "Grace is not allowed in conditional branch bodies for 'Z'.", new SourceSpan(1, 8, 1, 9))],
            syntax.Diagnostics.Select(d => (d.Code, d.Message, d.Span)).ToList());
        Assert.Equal(
            [
                ("Z", false, "1:1;3:1", 2),
                ("A", false, "2:1;4:1", 2),
            ],
            syntax.Root.Properties.Select(Describe).ToList());
    }

    // ── one family's state never leaks into another's ───────────────────────

    [Fact]
    public void Families_DoNotShareDuplicatePatternState()
    {
        // F(0)/G(0) and F(x)/G(y) are pairwise match-equivalent ACROSS families; a
        // shared pattern index would flag G's clauses as duplicates of F's.
        var provenance = SourceProvenance.ParseValid("F(0) = 1\nG(0) = 2\nF(x) = 3\nG(y) = 4\nF(0) + G(0)");
        Assert.Equal([3m], KatLangEngine.EvaluateToAtoms(provenance.Source).ToArray());
    }

    [Fact]
    public void Families_DoNotShareVisibilityState()
    {
        // F is a public family, G a plain one, interleaved; a shared visibility flag
        // would report a clause-visibility mismatch on G (or F).
        var root = SourceProvenance.ParseValid("public F(0) = 1\nG(0) = 2\npublic F(x) = 3\nG(y) = 4\nF(0) + G(0)").Root;

        Assert.Equal(
            [
                ("F", true, "1:8;3:8", 2),
                ("G", false, "2:1;4:1", 2),
            ],
            root.Properties.Select(Describe).ToList());
    }

    [Fact]
    public void Families_DoNotShareClauseSpansOrBranches()
    {
        // Only F's re-declared F(0) is a duplicate, anchored on ITS clause; G keeps
        // exactly its own two clauses and its own two declaration spans.
        var source = "F(0) = 1\nG(0) = 2\nF(0) = 3\nG(1) = 4\nF(1), G(1)";
        var syntax = Parser.ParseSyntax(source);

        Assert.Equal(
            [(DiagnosticCode.DuplicateBranchPattern, DuplicateBranchF, new SourceSpan(3, 1, 3, 8))],
            syntax.Diagnostics.Select(d => (d.Code, d.Message, d.Span)).ToList());

        var root = SourceProvenance.ParseAllowingDiagnostics(source).Root;
        Assert.Equal(
            [
                ("F", false, "1:1;3:1", 2),
                ("G", false, "2:1;4:1", 2),
            ],
            root.Properties.Select(Describe).ToList());
    }

    // ── public/plain property spellings ─────────────────────────────────────

    [Fact]
    public void PublicAndPlainPropertyDefinitions_DifferOnlyInVisibility()
    {
        var root = SourceProvenance.ParseValid("A = 1\npublic B = 2\nA + B").Root;

        Assert.Equal(
            [
                ("A", false, "1:1", null),
                ("B", true, "2:8", null),
            ],
            root.Properties.Select(Describe).ToList());
        Assert.Equal([3m], KatLangEngine.EvaluateToAtoms("A = 1\npublic B = 2\nA + B").ToArray());
    }

    // ── structural closure: one owner, no parallel per-family dictionaries ───

    [Fact]
    public void ParserSource_ClauseFamilyStateHasOneOwner()
    {
        var source = ReadParserSource();
        var start = source.IndexOf("private ParsedAlgorithmBody ParseAlgorithmBodyParts(", StringComparison.Ordinal);
        var end = source.IndexOf("private static SourceSpan? CombineSpans(", StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start, "Expected the ParseAlgorithmBodyParts .. CombineSpans region in Parser.cs.");
        var bodyRegion = source[start..end];

        // Exactly one per-family map — the builder map — and no second per-family
        // collection keyed by family name.
        Assert.Equal(1, CountOccurrences(bodyRegion, "new Dictionary<string, ClauseGroupBuilder>"));
        Assert.Equal(1, CountOccurrences(bodyRegion, "new Dictionary<string,"));
        Assert.DoesNotContain("Dictionary<string, List<CondBranch>>", source, StringComparison.Ordinal);
        Assert.DoesNotContain("Dictionary<string, List<SourceSpan>>", source, StringComparison.Ordinal);
        Assert.DoesNotContain("Dictionary<string, HashSet<Pattern>>", source, StringComparison.Ordinal);

        // The two property spellings share one definition routine.
        Assert.Equal(1, CountOccurrences(bodyRegion, "ParsePropertyDefinition(isPublic: true)"));
        Assert.Equal(1, CountOccurrences(bodyRegion, "ParsePropertyDefinition(isPublic: false)"));
    }

    private static int CountOccurrences(string text, string needle)
    {
        var count = 0;
        for (var index = text.IndexOf(needle, StringComparison.Ordinal);
            index >= 0;
            index = text.IndexOf(needle, index + needle.Length, StringComparison.Ordinal))
        {
            count++;
        }

        return count;
    }

    private static string ReadParserSource()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory); current is not null; current = current.Parent)
        {
            var candidate = Path.Combine(current.FullName, "src", "KatLang", "Parser.cs");
            if (File.Exists(candidate))
                return File.ReadAllText(candidate);
        }

        throw new InvalidOperationException("src/KatLang/Parser.cs was not found above the test output directory.");
    }
}
