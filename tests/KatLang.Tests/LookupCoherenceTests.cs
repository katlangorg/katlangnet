using System.Numerics;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Declaration-identity coherence across KatLang's three independent name-lookup
/// views:
/// <list type="number">
/// <item>the RUNTIME evaluator (<c>Evaluator.LookupLexical</c> / <c>ResolveAlg</c>,
/// mirrored by Lean <c>lookupLexical</c> / <c>resolveAlg</c>),</item>
/// <item>the EDITOR semantic model (<c>ElaboratedScopeLookup</c> via
/// <c>SemanticModelBuilder</c>),</item>
/// <item>the FRONT-END parameter detector (<c>ElaboratedScopeLookup</c> via
/// <c>ParameterDetector</c>), whose verdict is observable in the elaborated AST
/// as an implicit parameter.</item>
/// </list>
///
/// <para>
/// Views 2 and 3 share <c>ElaboratedScopeLookup</c>; view 1 re-implements the
/// same ownership-first / public-only-through-<c>open</c> / ambiguity rules
/// independently. Nothing previously asserted that they select the SAME
/// declaration, only that each of them resolved something.
/// </para>
///
/// <para>
/// Every candidate declaration in a case yields a UNIQUE sentinel value
/// (101, 202, 303, ...), so the runtime's observed value names exactly which
/// declaration ran. <see cref="AssertRuntimeSentinelMatchesDeclaration"/> then
/// closes the loop by requiring the sentinel to live on the very source line
/// the editor reported as the declaration. Cases where no unique declaration
/// should be chosen assert that outcome on both sides instead — runtime
/// <c>ambiguousOpen</c>/<c>unknownName</c> or implicit-parameter promotion
/// against editor <c>Unresolved</c>/<c>ImplicitParameterReference</c>.
/// </para>
///
/// <para>
/// Note the deliberate asymmetry this suite must NOT flatten: the editor is
/// error-tolerant by design, so a program that fails to evaluate for a reason
/// unrelated to the probed identifier may still carry a correct editor
/// resolution. Such cases use <see cref="Tolerated"/> and state the runtime
/// error explicitly.
/// </para>
/// </summary>
public class LookupCoherenceTests
{
    // ----- expectation model --------------------------------------------------

    private abstract record Expectation;

    /// <summary>The probed reference resolves to a specific source declaration.</summary>
    private sealed record Declared(
        string Name,
        int Occurrence,
        IdentifierClassification Classification = IdentifierClassification.PropertyReference)
        : Expectation;

    /// <summary>The probed reference resolves to a prelude builtin (no source declaration).</summary>
    private sealed record Builtin : Expectation;

    /// <summary>No unique declaration exists: ambiguity, or a name nothing provides.</summary>
    private sealed record NoDeclaration(
        IdentifierClassification Classification = IdentifierClassification.Unresolved)
        : Expectation;

    /// <summary>
    /// The front end found no property declaration, so the name became an
    /// implicit parameter of the algorithm at <paramref name="OwnerPath"/>.
    /// </summary>
    private sealed record ImplicitParameter(string OwnerPath) : Expectation;

    /// <summary>
    /// The editor legitimately resolves a declaration the runtime never reaches,
    /// because evaluation fails for a reason outside this identifier's own lookup.
    /// </summary>
    private sealed record Tolerated(string Name, int Occurrence) : Expectation;

    /// <param name="Id">Stable case id.</param>
    /// <param name="Source">Program. Candidate declarations use unique sentinels >= 100.</param>
    /// <param name="ReferenceName">Identifier probed.</param>
    /// <param name="ExpectedRuntime">Hand-written canonical neutral observation.</param>
    /// <param name="Expected">Hand-written canonical lookup outcome.</param>
    /// <param name="ReferenceOccurrence">
    /// 1-based token occurrence of the probed reference. <c>null</c> selects the
    /// last occurrence, which is where most cases place the reference; the
    /// open-head-defined-later case needs an explicit index because its
    /// declaration comes after its reference in source order.
    /// </param>
    private sealed record LookupCase(
        string Id,
        string Source,
        string ReferenceName,
        string ExpectedRuntime,
        Expectation Expected,
        int? ReferenceOccurrence = null);

    // ----- the matrix ---------------------------------------------------------

    private static readonly IReadOnlyList<LookupCase> Cases =
    [
        // ---- exposure through `open` ----------------------------------------
        new("exposure.openPublicMember",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib\n    X\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        new("exposure.openPrivateMemberIsHidden",
            "Lib = {\n    X = 101\n}\nA = {\n    open Lib\n    X\n}\nA(707)",
            "X", "ok raw=707 n=1", new ImplicitParameter("root.A")),

        new("exposure.openPrivateMemberDoesNotShadowOuter",
            "X = 303\nLib = {\n    X = 101\n}\nA = {\n    open Lib\n    X\n}\nA",
            "X", "ok raw=303 n=1", new Declared("X", 1)),

        new("exposure.openLocalOnlyCapturedAncestorParamsIsHidden",
            "Lib(p) = {\n    public X = p + 101\n    X\n}\nA = {\n    open Lib\n    X\n}\nA",
            "X", "err unknownName", new NoDeclaration()),

        // A declaration inside a conditional branch body is never reachable BY NAME from
        // outside the conditional: `open Lib` provides Lib's own members (the family F), and
        // the family exposes no structural members, so the branch's X is not provided.
        new("exposure.openDoesNotReachBranchDeclarations",
            "Lib = {\n    public F(0) = {\n        public X = 101\n        X\n    }\n    public F(n) = n\n}\nA = {\n    open Lib\n    X\n}\nA(707)",
            "X", "ok raw=707 n=1", new ImplicitParameter("root.A")),

        // An inline block in a branch body's OWN open list is a provider for that branch: its
        // exported public member is visible to the branch in all three views.
        new("exposure.openInlineBlockInsideBranchIsVisibleToTheBranch",
            "F(0) = {\n    open { public X = 101 }\n    X\n}\nF(n) = n\nF(0)",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        // A self-contained library DECLARED in a branch body classifies exactly like one
        // declared in a parameterized body, so a body nested in that branch may open it and
        // all three views select the branch-local declaration.
        new("exposure.openBranchLocalLibraryFromNestedBody",
            "F(0) = {\n    Lib = {\n        public X = 101\n    }\n    G = {\n        open Lib\n        X\n    }\n    G\n}\nF(n) = n\nF(0)",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        // A branch-local member that captures the branch's pattern binder is local-only for
        // the same reason a parameter-capturing member is, so `open Lib` hides it exactly as
        // exposure.openLocalOnlyCapturedAncestorParamsIsHidden does for a parameter.
        new("exposure.openBranchLocalBinderCapturingMemberIsHidden",
            "F(0) = 0\nF(n) = {\n    Lib = {\n        public X = n + 101\n    }\n    G = {\n        open Lib\n        X\n    }\n    G\n}\nF(5)",
            "X", "err unknownName", new NoDeclaration()),

        // The family-level rule in all three views: a structural path into a branch body is
        // refused at the family (runtime localOnlyProperty with the family-level reason), the
        // editor leaves the member unresolved, and the detector promotes nothing — the branch
        // declaration's own Exported classification never enters into it.
        new("exposure.structuralDotDoesNotReachBranchDeclarations",
            "F(0) = {\n    Lib = { public X = 101 }\n    Lib.X\n}\nF(n) = n\nF.Lib",
            "Lib", "err localOnlyProperty", new NoDeclaration()),

        // Structural dot access deliberately sees private members; `open` does not.
        new("exposure.structuralDotSeesPrivateMember",
            "Lib = {\n    X = 101\n}\nLib.X",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        new("exposure.structuralDotRejectsLocalOnlyMember",
            "Lib(p) = {\n    public X = p + 101\n    X\n}\nB = {\n    Lib.X\n}\nB",
            "X", "err localOnlyProperty", new NoDeclaration()),

        // ---- provider topology ----------------------------------------------
        new("providers.twoProvidersAreAmbiguous",
            "L1 = {\n    public X = 101\n}\nL2 = {\n    public X = 202\n}\nA = {\n    open L1, L2\n    X\n}\nA",
            "X", "err ambiguousOpen", new NoDeclaration()),

        // Duplicate NAMED targets deduplicate first-occurrence-wins, so they are
        // one provider, not an ambiguity (Lean/evaluator: resolveAllOpens).
        new("providers.duplicateNamedTargetIsOneProvider",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib, Lib\n    X\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        new("providers.tripleDuplicateNamedTargetIsOneProvider",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib, Lib, Lib\n    X\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        new("providers.duplicateDottedTargetIsOneProvider",
            "Lib = {\n    public S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S, Lib.S\n    X\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        new("providers.duplicateAmongDistinctTargetsIsOneProvider",
            "Lib = {\n    public X = 101\n}\nOther = {\n    public Y = 202\n}\nA = {\n    open Lib, Other, Lib\n    X\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        new("providers.duplicateTargetInParentScopeIsOneProvider",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib, Lib\n    Inner = {\n        X\n    }\n    Inner\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        // Distinct spellings are distinct providers even when only one supplies
        // the name: `M = L` provides nothing, so `X` stays unique.
        new("providers.aliasSpellingIsADistinctProvider",
            "L = {\n    public X = 101\n}\nM = L\nA = {\n    open L, M\n    X\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        // Inline blocks get positional keys and are NEVER deduplicated, so two
        // structurally identical blocks really are two providers.
        new("providers.duplicateInlineBlocksAreAmbiguous",
            "A = {\n    open { public X = 101 }, { public X = 202 }\n    X\n}\nA",
            "X", "err ambiguousOpen", new NoDeclaration()),

        new("providers.inlineBlockExposesPublicMember",
            "A = {\n    open { public X = 101 }\n    X\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        new("providers.inlineBlockHidesPrivateMember",
            "A = {\n    open { X = 101 }\n    X\n}\nA(707)",
            "X", "ok raw=707 n=1", new ImplicitParameter("root.A")),

        new("providers.dottedPathProvider",
            "Lib = {\n    public S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S\n    X\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        new("providers.dottedPathThroughPrivateIntermediateFails",
            "Lib = {\n    S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S\n    X\n}\nA(707)",
            "X", "ok raw=707 n=1", new ImplicitParameter("root.A")),

        // An open head is resolved by direct lexical lookup only — never through
        // another open in the same list.
        new("providers.openHeadIsNotVisibleThroughAnotherOpen",
            "Outer = {\n    public Lib = {\n        public X = 101\n    }\n}\nA = {\n    open Outer, Lib\n    X\n}\nA(707)",
            "X", "ok raw=707 n=1", new ImplicitParameter("root.A")),

        // ---- scope -----------------------------------------------------------
        new("scope.parentScopeOpenReachesChild",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib\n    Inner = {\n        X\n    }\n    Inner\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        new("scope.childOpenDoesNotLeakOutward",
            "Lib = {\n    public X = 101\n}\nA = {\n    Inner = {\n        open Lib\n        X\n    }\n    X\n}\nA(707)",
            "X", "ok raw=707 n=1", new ImplicitParameter("root.A")),

        new("scope.innerOpenShadowsOuterOpen",
            "L1 = {\n    public X = 101\n}\nL2 = {\n    public X = 202\n}\nA = {\n    open L1\n    Inner = {\n        open L2\n        X\n    }\n    Inner\n}\nA",
            "X", "ok raw=202 n=1", new Declared("X", 2)),

        new("scope.braceBlockOpenDoesNotLeakOutward",
            "Lib = {\n    public X = 101\n}\nA = {\n    Q = {\n        open Lib\n        X\n    }\n    Q, X\n}\nA(707)",
            "X", "ok raw=S[101, 707] n=1", new ImplicitParameter("root.A")),

        new("scope.openHeadMayBeDefinedLaterInTheSameBody",
            "A = {\n    open Lib\n    X\n}\nLib = {\n    public X = 101\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 2), ReferenceOccurrence: 1),

        // ---- ownership-first --------------------------------------------------
        new("ownership.localPropertyBeatsOpenedName",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib\n    X = 202\n    X\n}\nA",
            "X", "ok raw=202 n=1", new Declared("X", 2)),

        new("ownership.ancestorPropertyBeatsOpenedName",
            "Lib = {\n    public X = 101\n}\nA = {\n    X = 202\n    Inner = {\n        open Lib\n        X\n    }\n    Inner\n}\nA",
            "X", "ok raw=202 n=1", new Declared("X", 2)),

        new("ownership.explicitParameterBeatsOpenedName",
            "Lib = {\n    public X = 101\n}\nA(X) = {\n    open Lib\n    X\n}\nA(707)",
            "X", "ok raw=707 n=1",
            new Declared("X", 2, IdentifierClassification.ExplicitParameterReference)),

        // ---- builtin collision -------------------------------------------------
        // The prelude is the outermost lexical scope, so it is reached by the
        // ownership-first parent walk BEFORE opens are consulted.
        new("builtin.builtinBeatsOpenedName",
            "Lib = {\n    public count = 101\n}\nA = {\n    open Lib\n    count([1, 2, 3])\n}\nA",
            "count", "ok raw=3 n=1", new Builtin()),

        new("builtin.localPropertyBeatsBuiltin",
            "A = {\n    count = 101\n    count\n}\nA",
            "count", "ok raw=101 n=1", new Declared("count", 1)),

        new("builtin.openedMathMemberResolvesToBuiltin",
            "A = {\n    open Math\n    Abs(-101)\n}\nA",
            "Abs", "ok raw=101 n=1", new Builtin()),

        // A builtin is never a legal open target. The runtime validates the whole
        // open list before resolving any name, so the illegal target fails the
        // lookup; the editor flags that target separately (see the
        // BuiltinOpenTarget test below) and still resolves X from the good
        // provider. Deliberately different contracts, pinned here.
        new("builtin.illegalBuiltinOpenTargetPoisonsRuntimeLookupOnly",
            "Lib = {\n    public X = 101\n}\nA = {\n    open count, Lib\n    X\n}\nA",
            "X", "err illegalInOpen", new Tolerated("X", 1)),

        // ---- access form --------------------------------------------------------
        new("form.zeroArgCallOnOpenedName",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib\n    X()\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),

        // `1.F` is the lexical call `F(1)`; the receiver picks the opened
        // declaration, and `a * 101` keeps the observed value exactly the
        // declaration's own sentinel.
        new("form.dotCallOnOpenedFunction",
            "Lib = {\n    public F(a) = a * 101\n}\nA = {\n    open Lib\n    1.F\n}\nA",
            "F", "ok raw=101 n=1", new Declared("F", 1)),

        new("form.structuralDotOnProviderIgnoresOpen",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib\n    X = 202\n    Lib.X\n}\nA",
            "X", "ok raw=101 n=1", new Declared("X", 1)),
    ];

    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var lookupCase in Cases)
            data.Add(lookupCase.Id);
        return data;
    }

    private static LookupCase Case(string id) => Cases.Single(c => c.Id == id);

    // ----- the relation -------------------------------------------------------

    [Theory]
    [MemberData(nameof(CaseIds))]
    public void RuntimeEditorAndFrontEndSelectTheSameDeclaration(string caseId)
    {
        var lookupCase = Case(caseId);
        var parsed = Parser.Parse(lookupCase.Source);
        Assert.False(
            parsed.HasErrors,
            $"[{caseId}] unexpected parse diagnostics: " +
            string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));

        AssertSentinelsAreUnique(lookupCase);

        // View 1 — runtime.
        var runtime = SemanticExplorerHarness.Observe(caseId, lookupCase.Source).Neutral;
        Assert.Equal(lookupCase.ExpectedRuntime, runtime);

        // View 2 — editor.
        var model = SemanticModelBuilder.Build(parsed);
        var referenceToken = TokenSite(lookupCase.Source, lookupCase.ReferenceName, lookupCase.ReferenceOccurrence);
        var resolution = model.FindResolutionAt(referenceToken.Line, referenceToken.Column);
        Assert.True(
            resolution is not null,
            $"[{caseId}] no editor resolution at the probed site " +
            $"{lookupCase.ReferenceName}@{referenceToken.Line}:{referenceToken.Column}.");

        // View 3 — front-end parameter detection, read off the elaborated AST.
        var implicitOwners = ImplicitParameterOwners(parsed.Root, lookupCase.ReferenceName);

        switch (lookupCase.Expected)
        {
            case Declared(var name, var occurrence, var classification):
            {
                Assert.Equal(classification, resolution!.Classification);
                var declarationToken = TokenSite(lookupCase.Source, name, occurrence);
                AssertDeclarationIs(caseId, resolution, declarationToken);

                // The sentinel loop only closes for PROPERTY declarations, whose
                // body is written on the declaration line. A parameter's observed
                // value comes from the call site, so there is nothing on its
                // declaration line to match; identity is already pinned by the
                // exact declaration span above.
                if (classification == IdentifierClassification.PropertyReference)
                    AssertRuntimeSentinelMatchesDeclaration(lookupCase, declarationToken);

                Assert.Empty(implicitOwners);
                break;
            }

            case Builtin:
                Assert.Equal(IdentifierClassification.Builtin, resolution!.Classification);
                Assert.Null(resolution.ResolvedDeclaration);
                Assert.Empty(implicitOwners);
                break;

            case NoDeclaration(var classification):
                Assert.Equal(classification, resolution!.Classification);
                Assert.Null(resolution.ResolvedDeclaration);
                Assert.Empty(implicitOwners);
                break;

            case ImplicitParameter(var ownerPath):
                Assert.Equal(IdentifierClassification.ImplicitParameterReference, resolution!.Classification);
                Assert.Null(resolution.ResolvedDeclaration);
                Assert.Equal([ownerPath], implicitOwners);
                break;

            case Tolerated(var name, var occurrence):
            {
                Assert.Equal(IdentifierClassification.PropertyReference, resolution!.Classification);
                AssertDeclarationIs(caseId, resolution, TokenSite(lookupCase.Source, name, occurrence));
                Assert.StartsWith("err ", lookupCase.ExpectedRuntime, StringComparison.Ordinal);
                Assert.Empty(implicitOwners);
                break;
            }

            default:
                throw new InvalidOperationException($"Unhandled expectation for '{caseId}'.");
        }
    }

    /// <summary>
    /// A builtin is never a legal <c>open</c> target on either side: the runtime
    /// raises <c>illegalInOpen</c>, and the editor refuses to treat the target as
    /// a provider (it classifies the target site, not the names it would supply).
    /// </summary>
    [Fact]
    public void BuiltinOpenTargetIsRejectedByBothViews()
    {
        const string source = "A = {\n    open count\n    1\n}\nA";
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors);

        var model = SemanticModelBuilder.Build(parsed);
        var target = TokenSite(source, "count", occurrence: null);
        var resolution = model.FindResolutionAt(target.Line, target.Column);

        Assert.NotNull(resolution);
        Assert.Equal(OccurrenceKind.OpenTargetReference, resolution.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Unresolved, resolution.Classification);
        Assert.Null(resolution.ResolvedDeclaration);

        // Unused here, so the runtime never resolves the open list at all.
        Assert.Equal("ok raw=1 n=1", SemanticExplorerHarness.Observe("openBuiltinUnused", source).Neutral);

        // Forcing a lookup through that list reaches the same verdict.
        const string forced = "Lib = {\n    public X = 101\n}\nA = {\n    open count, Lib\n    X\n}\nA";
        Assert.Equal("err illegalInOpen", SemanticExplorerHarness.Observe("openBuiltinForced", forced).Neutral);
    }

    /// <summary>
    /// Every case must probe a site the semantic model actually classifies, and
    /// every declaration a case names must exist. Guards the corpus itself
    /// against silently degenerating into vacuous assertions.
    /// </summary>
    [Fact]
    public void EveryCaseProbesASourceBackedSite()
    {
        Assert.NotEmpty(Cases);
        Assert.Equal(Cases.Count, Cases.Select(c => c.Id).Distinct(StringComparer.Ordinal).Count());

        foreach (var lookupCase in Cases)
        {
            var parsed = Parser.Parse(lookupCase.Source);
            Assert.False(parsed.HasErrors, $"[{lookupCase.Id}] parse errors.");

            var site = TokenSite(lookupCase.Source, lookupCase.ReferenceName, lookupCase.ReferenceOccurrence);
            var model = SemanticModelBuilder.Build(parsed);
            Assert.True(
                model.FindResolutionAt(site.Line, site.Column) is not null,
                $"[{lookupCase.Id}] probed site is not a semantic identifier occurrence.");
        }
    }

    /// <summary>
    /// Outcome coverage: the matrix must keep exercising every lookup verdict.
    /// A refactor that accidentally collapsed one outcome into another would
    /// otherwise leave a green but far weaker suite.
    /// </summary>
    [Fact]
    public void MatrixCoversEveryLookupOutcome()
    {
        Assert.Contains(Cases, c => c.Expected is Declared);
        Assert.Contains(Cases, c => c.Expected is Builtin);
        Assert.Contains(Cases, c => c.Expected is NoDeclaration);
        Assert.Contains(Cases, c => c.Expected is ImplicitParameter);
        Assert.Contains(Cases, c => c.Expected is Tolerated);

        Assert.Contains(Cases, c => c.ExpectedRuntime == "err ambiguousOpen");
        Assert.Contains(Cases, c => c.ExpectedRuntime == "err unknownName");
        Assert.Contains(Cases, c => c.ExpectedRuntime == "err localOnlyProperty");
        Assert.Contains(Cases, c => c.ExpectedRuntime == "err illegalInOpen");

        // Distinct-sentinel resolutions: the cases where declaration identity is
        // genuinely observable rather than merely "something resolved".
        var identityCases = Cases.Count(c =>
            c.Expected is Declared && c.ExpectedRuntime.StartsWith("ok raw=", StringComparison.Ordinal));
        Assert.True(identityCases >= 15, $"Only {identityCases} declaration-identity cases.");
    }

    // ----- helpers ------------------------------------------------------------

    private static void AssertDeclarationIs(string caseId, IdentifierResolution resolution, (int Line, int Column) site)
    {
        var declaration = resolution.ResolvedDeclaration;
        Assert.True(declaration is not null, $"[{caseId}] editor reported no declaration.");
        Assert.Equal(site.Line, declaration!.Span.StartLineNumber);
        Assert.Equal(site.Column, declaration.Span.StartColumn);
    }

    /// <summary>
    /// Closes the identity loop: the value the runtime produced must be the
    /// sentinel written on the line the editor named as the declaration. Both
    /// views therefore agree on WHICH declaration, not merely that one exists.
    /// </summary>
    private static void AssertRuntimeSentinelMatchesDeclaration(LookupCase lookupCase, (int Line, int Column) site)
    {
        if (!TryReadSentinel(lookupCase.ExpectedRuntime, out var sentinel))
            return;

        var declarationLine = lookupCase.Source.Split('\n')[site.Line - 1];
        Assert.True(
            Sentinels(declarationLine).Contains(sentinel),
            $"[{lookupCase.Id}] runtime produced sentinel {sentinel}, but the declaration the editor " +
            $"chose is on line {site.Line} (\"{declarationLine.Trim()}\"), which does not define it.");
    }

    private static bool TryReadSentinel(string neutral, out int sentinel)
    {
        sentinel = 0;
        const string prefix = "ok raw=";
        if (!neutral.StartsWith(prefix, StringComparison.Ordinal))
            return false;

        var raw = neutral[prefix.Length..];
        var end = raw.IndexOf(' ');
        if (end >= 0)
            raw = raw[..end];

        return int.TryParse(raw, out sentinel) && sentinel >= 100;
    }

    /// <summary>Sentinel literals (>= 100) written in a source fragment.</summary>
    private static IReadOnlyList<int> Sentinels(string text)
    {
        var (tokens, _) = Lexer.Tokenize(text);
        return tokens
            .Where(static token => token.Kind == TokenKind.Number)
            .Select(static token => token.NumValue)
            .Where(static value => value >= 100 && Decimal128.IsInteger(value))
            .Select(static value => (int)value)
            .ToList();
    }

    /// <summary>
    /// Sentinels must be pairwise distinct so no two candidate declarations can
    /// produce observationally identical results.
    /// </summary>
    private static void AssertSentinelsAreUnique(LookupCase lookupCase)
    {
        var sentinels = Sentinels(lookupCase.Source);
        Assert.Equal(sentinels.Count, sentinels.Distinct().Count());
    }

    /// <summary>
    /// Source position of an identifier token. <paramref name="occurrence"/> is
    /// 1-based; <c>null</c> selects the last occurrence (the probed reference,
    /// which every case places after all candidate declarations).
    /// </summary>
    private static (int Line, int Column) TokenSite(string source, string name, int? occurrence)
    {
        var (tokens, _) = Lexer.Tokenize(source);
        var matches = tokens
            .Where(token => token.Kind == TokenKind.Identifier && token.StringValue == name)
            .ToList();

        Assert.NotEmpty(matches);
        var token = occurrence is null ? matches[^1] : matches[occurrence.Value - 1];
        return (token.Line, token.Column);
    }

    /// <summary>
    /// Paths of every elaborated algorithm that carries <paramref name="name"/>
    /// as an INFERRED parameter — present in <see cref="Algorithm.Parameters"/>
    /// but absent from the source-backed <see cref="Algorithm.ExplicitParameters"/>.
    /// This is the front end's lookup verdict made structural: the detector only
    /// promotes a name to an implicit parameter when <c>ElaboratedScopeLookup</c>
    /// found no property declaration for it.
    /// </summary>
    private static IReadOnlyList<string> ImplicitParameterOwners(Algorithm root, string name)
    {
        var found = new List<string>();
        Walk(root, "root", name, found);
        return found;

        static void Walk(Algorithm algorithm, string path, string name, List<string> found)
        {
            var isParameter = algorithm.Parameters.Any(parameter => parameter.Name == name);
            var isExplicit = algorithm.ExplicitParameters.Any(parameter => parameter.Name == name);
            if (isParameter && !isExplicit)
                found.Add(path);

            foreach (var property in algorithm.Properties)
                Walk(property.Value, $"{path}.{property.Name}", name, found);
        }
    }
}
