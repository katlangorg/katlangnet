namespace KatLang.Tests;

/// <summary>
/// Equivalence relation between the evaluator's TWO independently implemented
/// lexical-lookup paths.
///
/// <list type="bullet">
/// <item><b>Twin 1</b> — <c>Evaluator.LookupLexical</c>, the binding-carrying
/// path. Reached by a bare name in VALUE position (<c>X</c>), which feeds the
/// zero-argument property cache.</item>
/// <item><b>Twin 2</b> — <c>Evaluator.LookupLexicalResolvedAlgorithm</c>, the
/// resolve-only fast path. Reached by a name in ALGORITHM position: a call
/// callee (<c>X()</c>) or a dot-call target (<c>X.string</c>), both of which go
/// through <c>ResolveAlg</c> / <c>ResolveNamedAlgorithm</c>.</item>
/// </list>
///
/// <para>
/// Each twin re-implements ownership-first ordering, opened-provider lookup,
/// open-target dedup, ambiguity, scope-level precedence, and prelude fallback.
/// Track 10 mutated only the fast path and found that no pre-existing test
/// covered it; this relation makes both paths independently observable on the
/// SAME scenario, so a rule that drifts on one side alone cannot hide behind
/// the other.
/// </para>
///
/// <para>
/// Declaration identity is observable because every candidate declaration in a
/// scenario carries a unique sentinel (101 / 202 / 303). Expectations are
/// hand-written per spelling rather than asserted to be equal, because two
/// spellings legitimately differ where the resolved thing is not a
/// zero-argument property — a parameter cannot be called, and a builtin's arity
/// applies to the written argument list. <see cref="SameSelectionScenarios"/>
/// pins which scenarios must agree exactly.
/// </para>
/// </summary>
public class LookupTwinEquivalenceTests
{
    /// <param name="Id">Stable scenario id.</param>
    /// <param name="Template">Program with <c>{0}</c> at the probe position.</param>
    /// <param name="ExpectedBare">Canonical observation for <c>X</c> (twin 1).</param>
    /// <param name="ExpectedCalled">Canonical observation for <c>X()</c> (twin 2).</param>
    /// <param name="ExpectedDotTarget">
    /// Canonical observation for <c>X.string</c> (twin 2 via the dot-call target
    /// position), or <c>null</c> where the resolved value has no string form.
    /// </param>
    private sealed record TwinScenario(
        string Id,
        string Template,
        string ExpectedBare,
        string ExpectedCalled,
        string? ExpectedDotTarget);

    private const string ProbeName = "X";

    private static readonly IReadOnlyList<TwinScenario> Scenarios =
    [
        // ---- opened-provider lookup -----------------------------------------
        new("openedProvider",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib\n    {0}\n}\nA",
            "ok raw=101 n=1", "ok raw=101 n=1", "ok raw='101' n=1"),

        // ---- ownership-first --------------------------------------------------
        new("localBeatsOpen",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib\n    X = 202\n    {0}\n}\nA",
            "ok raw=202 n=1", "ok raw=202 n=1", "ok raw='202' n=1"),

        new("ancestorBeatsOpen",
            "Lib = {\n    public X = 101\n}\nA = {\n    X = 202\n    Inner = {\n        open Lib\n        {0}\n    }\n    Inner\n}\nA",
            "ok raw=202 n=1", "ok raw=202 n=1", "ok raw='202' n=1"),

        // ---- open-target dedup -------------------------------------------------
        new("duplicateOpenTargetIsOneProvider",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib, Lib\n    {0}\n}\nA",
            "ok raw=101 n=1", "ok raw=101 n=1", "ok raw='101' n=1"),

        new("duplicateDottedOpenTargetIsOneProvider",
            "Lib = {\n    public S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S, Lib.S\n    {0}\n}\nA",
            "ok raw=101 n=1", "ok raw=101 n=1", "ok raw='101' n=1"),

        // ---- ambiguity ----------------------------------------------------------
        new("twoProvidersAmbiguous",
            "L1 = {\n    public X = 101\n}\nL2 = {\n    public X = 202\n}\nA = {\n    open L1, L2\n    {0}\n}\nA",
            "err ambiguousOpen", "err ambiguousOpen", "err ambiguousOpen"),

        new("duplicateInlineBlocksAmbiguous",
            "A = {\n    open { public X = 101 }, { public X = 202 }\n    {0}\n}\nA",
            "err ambiguousOpen", "err ambiguousOpen", "err ambiguousOpen"),

        // ---- scope-level precedence -----------------------------------------------
        new("innerOpenShadowsOuterOpen",
            "L1 = {\n    public X = 101\n}\nL2 = {\n    public X = 202\n}\nA = {\n    open L1\n    Inner = {\n        open L2\n        {0}\n    }\n    Inner\n}\nA",
            "ok raw=202 n=1", "ok raw=202 n=1", "ok raw='202' n=1"),

        new("parentOpenReachesChild",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib\n    Inner = {\n        {0}\n    }\n    Inner\n}\nA",
            "ok raw=101 n=1", "ok raw=101 n=1", "ok raw='101' n=1"),

        // ---- exposure ---------------------------------------------------------------
        // These use TWO providers on purpose. The evaluator's open-exposure
        // filter is unobservable in the obvious `open Lib` + private `X` shape:
        // the front end has already decided `X` resolves to nothing and turned
        // it into an implicit parameter, so the evaluator never performs the
        // lookup and a leak in its filter cannot be seen. Pairing the hidden
        // member with a VISIBLE provider of the same name keeps the front end's
        // decision unchanged (one hit, no parameter) while making the filter's
        // verdict decide between "resolves to the public one" and "ambiguous".
        // Track 11 mutants A5-A8 survived the entire suite without these.
        new("privateMemberIsNotASecondProvider",
            "Pub = {\n    public X = 101\n}\nLib = {\n    X = 202\n}\nA = {\n    open Pub, Lib\n    {0}\n}\nA",
            "ok raw=101 n=1", "ok raw=101 n=1", "ok raw='101' n=1"),

        new("localOnlyMemberIsNotASecondProvider",
            "Pub = {\n    public X = 101\n}\nLib(p) = {\n    public X = p + 202\n    X\n}\nA = {\n    open Pub, Lib\n    {0}\n}\nA",
            "ok raw=101 n=1", "ok raw=101 n=1", "ok raw='101' n=1"),

        // The ownership-first controls that the shapes above replaced: an
        // ancestor property still wins over an open that provides nothing.
        new("ancestorBeatsHiddenOpenMember",
            "X = 303\nLib = {\n    X = 101\n}\nA = {\n    open Lib\n    {0}\n}\nA",
            "ok raw=303 n=1", "ok raw=303 n=1", "ok raw='303' n=1"),

        new("dottedPathProvider",
            "Lib = {\n    public S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S\n    {0}\n}\nA",
            "ok raw=101 n=1", "ok raw=101 n=1", "ok raw='101' n=1"),

        new("inlineBlockProvider",
            "A = {\n    open { public X = 101 }\n    {0}\n}\nA",
            "ok raw=101 n=1", "ok raw=101 n=1", "ok raw='101' n=1"),

        // A child's `open` must never leak to its parent. `X` at A's level is
        // therefore an implicit parameter, which is where the spellings
        // legitimately diverge: a parameter is a value, so it can be a dot-call
        // receiver (value intrinsics are tried before ResolveAlg) but never a
        // callee.
        new("childOpenDoesNotLeakOutward",
            "Lib = {\n    public X = 101\n}\nA = {\n    Inner = {\n        open Lib\n        X\n    }\n    {0}\n}\nA(303)",
            "ok raw=303 n=1", "err notAnAlgorithm", "ok raw='303' n=1"),
    ];

    /// <summary>
    /// Scenarios whose resolved declaration is a zero-argument property, so all
    /// three spellings MUST observe the same value. Anything not listed here has
    /// a documented reason to differ.
    /// </summary>
    private static readonly HashSet<string> SameSelectionScenarios =
        Scenarios.Where(static s => s.Id != "childOpenDoesNotLeakOutward")
            .Select(static s => s.Id)
            .ToHashSet(StringComparer.Ordinal);

    public static TheoryData<string> ScenarioIds()
    {
        var data = new TheoryData<string>();
        foreach (var scenario in Scenarios)
            data.Add(scenario.Id);
        return data;
    }

    [Theory]
    [MemberData(nameof(ScenarioIds))]
    public void BothLookupTwinsSelectTheSameDeclaration(string scenarioId)
    {
        var scenario = Scenarios.Single(s => s.Id == scenarioId);

        var bare = Observe(scenario, ProbeName);
        var called = Observe(scenario, $"{ProbeName}()");
        var dotTarget = Observe(scenario, $"{ProbeName}.string");

        Assert.Equal(scenario.ExpectedBare, bare);
        Assert.Equal(scenario.ExpectedCalled, called);
        if (scenario.ExpectedDotTarget is { } expectedDotTarget)
            Assert.Equal(expectedDotTarget, dotTarget);

        if (!SameSelectionScenarios.Contains(scenarioId))
            return;

        // Twin 1 vs twin 2 on the same scenario. Stated relationally as well as
        // absolutely: if a future rule change moves both expectations together,
        // this still asserts the two implementations moved together too.
        Assert.Equal(StripStringForm(bare), StripStringForm(dotTarget));
        Assert.Equal(bare, called);
    }

    /// <summary>
    /// The relation is only meaningful if each spelling actually reaches its own
    /// twin. Twin 2 is the resolve-only path used from algorithm position; if a
    /// refactor routed callee resolution back through <c>LookupLexical</c>, the
    /// equivalence above would go vacuous without any test noticing.
    ///
    /// <para>
    /// The two branches are distinguishable deterministically on a property with
    /// no output: the value-position branch reports it as a PROPERTY access
    /// ("Property 'P' has no defined output"), the algorithm-position branch as
    /// a CALL ("Cannot call 'P' ..."). Same declaration, same defect, different
    /// path — so both really are being exercised above.
    /// </para>
    /// </summary>
    [Fact]
    public void BareAndCalledSpellingsExerciseDifferentEvaluatorPaths()
    {
        const string noOutput = "A = {\n    P = {\n        Q = 1\n    }\n    {0}\n}\nA";

        Assert.Contains(
            "Property 'P' has no defined output",
            FailureMessage(noOutput.Replace("{0}", "P", StringComparison.Ordinal)),
            StringComparison.Ordinal);

        Assert.Contains(
            "Cannot call 'P' because it has no defined output",
            FailureMessage(noOutput.Replace("{0}", "P()", StringComparison.Ordinal)),
            StringComparison.Ordinal);
    }

    private static string FailureMessage(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));

        var result = Evaluator.Run(new Expr.Block(parsed.Root));
        Assert.True(result.IsError, $"Expected an evaluation failure for:\n{source}");
        return KatLangError.FromEvalError(result.Error).Message;
    }

    /// <summary>
    /// Corpus guard: the scenario set must keep covering every rule both twins
    /// duplicate, so a deletion shows up here rather than as a quietly weaker
    /// relation.
    /// </summary>
    [Fact]
    public void ScenariosCoverEveryDuplicatedLookupRule()
    {
        var ids = Scenarios.Select(static s => s.Id).ToHashSet(StringComparer.Ordinal);

        string[] required =
        [
            "openedProvider",
            "localBeatsOpen",
            "ancestorBeatsOpen",
            "duplicateOpenTargetIsOneProvider",
            "duplicateDottedOpenTargetIsOneProvider",
            "twoProvidersAmbiguous",
            "duplicateInlineBlocksAmbiguous",
            "innerOpenShadowsOuterOpen",
            "parentOpenReachesChild",
            "privateMemberIsNotASecondProvider",
            "localOnlyMemberIsNotASecondProvider",
            "ancestorBeatsHiddenOpenMember",
            "dottedPathProvider",
            "inlineBlockProvider",
            "childOpenDoesNotLeakOutward",
        ];

        foreach (var id in required)
            Assert.Contains(id, ids);

        Assert.Equal(Scenarios.Count, ids.Count);
    }

    /// <summary>
    /// Prelude fallback, which both twins reach through the parent chain rather
    /// than through opens. Written separately because the discriminating probes
    /// are not a plain <c>X</c> substitution.
    /// </summary>
    [Fact]
    public void BothTwinsReachThePreludeThroughTheParentChain()
    {
        // The builtin wins over an opened same-named property, so a bare
        // reference is the zero-argument arity error of `count`, NOT 101.
        const string builtinBeatsOpen = "Lib = {\n    public count = 101\n}\nA = {\n    open Lib\n    count\n}\nA";
        const string builtinBeatsOpenCalled = "Lib = {\n    public count = 101\n}\nA = {\n    open Lib\n    count()\n}\nA";
        const string builtinBeatsOpenApplied =
            "Lib = {\n    public count = 101\n}\nA = {\n    open Lib\n    count([1, 2, 3])\n}\nA";

        Assert.Equal("err arity", SemanticExplorerHarness.Observe("bboBare", builtinBeatsOpen).Neutral);
        Assert.Equal("err arity", SemanticExplorerHarness.Observe("bboCalled", builtinBeatsOpenCalled).Neutral);
        Assert.Equal("ok raw=3 n=1", SemanticExplorerHarness.Observe("bboApplied", builtinBeatsOpenApplied).Neutral);

        // ... and an owned property wins over the builtin on both twins.
        const string localBeatsBuiltin = "A = {\n    count = 101\n    count\n}\nA";
        const string localBeatsBuiltinCalled = "A = {\n    count = 101\n    count()\n}\nA";

        Assert.Equal("ok raw=101 n=1", SemanticExplorerHarness.Observe("lbbBare", localBeatsBuiltin).Neutral);
        Assert.Equal("ok raw=101 n=1", SemanticExplorerHarness.Observe("lbbCalled", localBeatsBuiltinCalled).Neutral);
    }

    private static string Observe(TwinScenario scenario, string probe)
        => SemanticExplorerHarness
            .Observe($"{scenario.Id}::{probe}", scenario.Template.Replace("{0}", probe, StringComparison.Ordinal))
            .Neutral;

    /// <summary>
    /// <c>X.string</c> observes the same declaration as <c>X</c> but renders it
    /// as a string, so the relational comparison drops the quotes.
    /// </summary>
    private static string StripStringForm(string neutral)
        => neutral.Replace("raw='", "raw=", StringComparison.Ordinal)
            .Replace("' n=", " n=", StringComparison.Ordinal);
}
