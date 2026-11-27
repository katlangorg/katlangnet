using System.Text;

namespace KatLang.Tests;

using Mode = PropertyExposureResolver.SettlementShareMode;

/// <summary>
/// THE OFF-CHAIN GAP, prepared for an owner decision (<c>docs/design/offchain-exposure-owner-decision-brief-2026-11.md</c>).
/// These tests pin the CURRENT contract on the brief's witnesses: the exact-key share answers a settlement that looked up an
/// owner off its site's chain for its exact key only, and once any settlement of a resolution has made such a lookup, the
/// resolution solves no further component equations (<c>SettlementShare.SawOffChainLookup</c>). Compare the production
/// classifications with <see cref="Mode.ExactBoundOwners"/> and, where they diverge, <see cref="Mode.Unshared"/>.
/// Public-engine runs locate the access checks. The cost controls count settlement frames and component completions.
/// </summary>
public sealed class OffChainExposureDecisionTests
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private static T InMode<T>(Mode mode, Func<T> work)
    {
        var previous = PropertyExposureResolver.SettlementShareModeForTesting.Value;
        PropertyExposureResolver.SettlementShareModeForTesting.Value = mode;
        try { return work(); }
        finally { PropertyExposureResolver.SettlementShareModeForTesting.Value = previous; }
    }

    /// <summary>The eager parse of a clean <paramref name="source"/>: every property's metadata and the counters.</summary>
    private static (string Metadata, FrontEndTraversalObservations Observations) Parse(string source)
    {
        var observations = new FrontEndTraversalObservations();
        var parsed = Parser.ParseObserved(source, options: null, observations);
        Assert.Empty(parsed.Diagnostics);
        return (ExposureSettlementFrameChargeTests.Metadata(parsed.Root), observations);
    }

    private static Algorithm.User Root(string source) => SourceProvenance.ParseValid(source).Root;

    private static Algorithm.User RootIn(Mode mode, string source) => InMode(mode, () => Root(source));

    private static Property Member(Algorithm root, params string[] path) => ExposureOpenChainComplexityTests.Member(root, path);

    private static void AssertRequires(Property property, params (string Name, int Depth)[] requirements)
        => ExposureOpenChainComplexityTests.AssertRequires(property, requirements);

    private static RunResult RunClean(string source)
    {
        SourceProvenance.ParseValid(source);
        return KatLangEngine.Run(source);
    }

    private static string Value(string source) => Assert.IsType<RunResult.Success>(RunClean(source)).ToDisplayString();

    private static void AssertRefused(string source, string member, int line, int column)
    {
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(RunClean(source)).Errors);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, error.Code);
        Assert.Equal(new SourcePosition(line, column), error.Span?.Start);
        var inner = error.Source;
        while (inner is EvalError.WithContext context)
            inner = context.Inner;
        Assert.Equal(member, Assert.IsType<EvalError.LocalOnlyProperty>(inner).PropertyName);
    }

    /// <summary>Production publishes exactly the exact-key share's metadata (the documented contract of the gap).</summary>
    private static void AssertExactKeyMetadata(string source)
        => Assert.Equal(InMode(Mode.ExactBoundOwners, () => Parse(source)).Metadata, Parse(source).Metadata);

    // ── Witnesses ───────────────────────────────────────────────────────────

    // RES-08's own example, with a reader inside F: Box.R's check of F.A is made in R's scope, where F is no static ancestor.
    private const string BoxR = "Box = { public R = if(false, F.A, 0) }\n";

    /// <summary>
    /// A CHECK THAT CAN NEVER PASS (RES-08; Q1–Q3 (a): a written dot path is checked at its reading site) is charged to a
    /// reader inside the owner when the reader's key is its own. <c>Box.R</c> requires nothing, as RES-08 states, but
    /// <c>H(k) = Box.R + k</c> inside <c>F(y)</c> settles <c>R</c>'s seed from <c>H</c>'s site, where <c>F</c> is on the chain,
    /// and is published local-only on <c>y</c>: reading it from outside <c>F</c> is refused at <c>H</c> although no read of
    /// <c>y</c> can ever succeed through <c>R</c>. The unshared settlement agrees (the asking-site rule keeps it). Under the
    /// check-site rule <c>H</c> is exported and <c>F.H(1)</c> is <c>1</c>. The census records the same divergence for its
    /// re-entry readers (<c>census-gaps.txt</c>, M2 <c>model-false-admission</c>).
    /// </summary>
    [Fact]
    public void ACheckThatCanNeverPass_IsChargedToAReaderInsideTheOwner()
    {
        const string owner = "F(y) = {\nA = y + 1\npublic H(k) = Box.R + k\nH(1)\n}\n" + BoxR;
        AssertExactKeyMetadata(owner + "0\n");
        var root = Root(owner + "0\n");
        AssertRequires(Member(root, "Box", "R"));
        AssertRequires(Member(root, "F", "H"), ("y", 0));
        AssertRequires(Member(RootIn(Mode.Unshared, owner + "0\n"), "F", "H"), ("y", 0));
        AssertRefused(owner + "F.H(1)\n", "H", 7, 1);
        Assert.Equal("1", Value(owner + "F(5)\n"));
        Assert.Equal("0", Value(owner + "Box.R\n"));
    }

    /// <summary>
    /// The same never-passing check, through a key the exact-key share already holds: <c>Box.R</c>'s own settlement (from
    /// <c>Box</c>, where <c>F</c> is off the chain) answers the parameterless <c>H = Box.R</c> inside <c>F</c>, which is
    /// published exported and reads <c>0</c> from outside, as RES-08 requires; the unshared settlement charges <c>y</c>. The
    /// rule document's off-chain example behaves alike: <c>H = K.M(1)</c> is exported while <c>H(y) = K.M(1) + y</c>, whose
    /// key differs, requires <c>x</c>. Under the check-site rule both forms are exported; under the asking-site rule alone
    /// both require <c>F</c>'s <c>x</c>. In the Box example the enclosing parameter is <c>y</c>.
    /// </summary>
    [Fact]
    public void TheExactKeyShareAnswersTheSameCheck_DependingOnTheKey()
    {
        const string boxReader = "F(y) = {\nA = y + 1\npublic H = Box.R\nH\n}\n" + BoxR;
        AssertExactKeyMetadata(boxReader + "0\n");
        AssertRequires(Member(Root(boxReader + "0\n"), "F", "H"));
        AssertRequires(Member(RootIn(Mode.Unshared, boxReader + "0\n"), "F", "H"), ("y", 0));
        Assert.Equal("0", Value(boxReader + "F.H\n"));

        const string library = "K = { public M(z) = F.G + z }\n";
        const string plain = library + "F(x) = {\npublic G = x + 1\npublic H = K.M(1)\n0\n}\n0\n";
        const string withParameter = library + "F(x) = {\npublic G = x + 1\npublic H(y) = K.M(1) + y\n0\n}\n0\n";
        AssertExactKeyMetadata(plain);
        AssertExactKeyMetadata(withParameter);
        AssertRequires(Member(Root(plain), "F", "H"));
        AssertRequires(Member(Root(withParameter), "F", "H"), ("x", 0));
        AssertRequires(Member(RootIn(Mode.Unshared, plain), "F", "H"), ("x", 0));
        AssertRequires(Member(RootIn(Mode.Unshared, withParameter), "F", "H"), ("x", 0));
    }

    /// <summary>
    /// The latent check: the off-chain read itself is refused where the evaluator makes it, at <c>G</c> inside <c>K.M</c>, on
    /// every route, while <c>H</c> passes its own check from outside <c>F</c> (and inside <c>F</c>). A reader that never
    /// demands the read (a lazy list slot it does not select) runs: <c>F.H</c> with <c>H = [K.M(1), 7][1]</c> is <c>7</c>.
    /// The check-site rule keeps all four outcomes; the asking-site rule alone would refuse both reads from outside at
    /// <c>H</c>, the second one a program that runs today.
    /// </summary>
    [Fact]
    public void TheLatentCheck_FailsAtTheMemberTheEvaluatorChecks()
    {
        const string library = "K = { public M(z) = F.G + z }\n";
        const string demanding = library + "F(x) = {\npublic G = x + 1\npublic H = K.M(1)\nH\n}\n";
        const string lazy = library + "F(x) = {\npublic G = x + 1\npublic H = [K.M(1), 7][1]\nH\n}\n";
        AssertExactKeyMetadata(demanding + "0\n");
        AssertExactKeyMetadata(lazy + "0\n");
        AssertRefused(demanding + "F.H\n", "G", 1, 21);
        AssertRefused(demanding + "F(5)\n", "G", 1, 21);
        Assert.Equal("7", Value(lazy + "F.H\n"));
        Assert.Equal("7", Value(lazy + "F(5)\n"));
        AssertRequires(Member(RootIn(Mode.Unshared, lazy + "0\n"), "F", "H"), ("x", 0));
    }

    /// <summary>
    /// A DETACHED READ SETTLED FIRST hides a requirement whose check CAN pass. <c>W = F.G</c> inside <c>F</c> needs an
    /// activation of <c>F</c>, which every reader inside <c>F</c> has, so <c>W</c> and its reader <c>X</c> are local-only on
    /// <c>x</c>, and <c>F.X</c> is refused at <c>X</c>. Adding the unrelated root read <c>R = F.W</c>, settled first from the
    /// root where <c>F</c> is off the chain, makes the exact-key share hand its answer (nothing) to <c>W</c>'s and <c>X</c>'s
    /// settlements: both are published exported and <c>F.X</c> reads <c>7</c>. The unshared settlement, the asking-site rule
    /// and the check-site rule all publish the program without <c>R</c>'s classification for both programs.
    /// </summary>
    [Fact]
    public void ADetachedReadSettledFirst_HidesARequirementThatCanPass()
    {
        const string owner = "F(x) = {\npublic G = x + 1\npublic W = F.G\npublic X = [W, 7][1]\nX\n}\n";
        const string withRootRead = owner + "R = F.W\n";
        AssertExactKeyMetadata(owner + "0\n");
        AssertExactKeyMetadata(withRootRead + "0\n");

        var alone = Root(owner + "0\n");
        AssertRequires(Member(alone, "F", "W"), ("x", 0));
        AssertRequires(Member(alone, "F", "X"), ("x", 0));
        AssertRefused(owner + "F.X\n", "X", 7, 1);

        var hidden = Root(withRootRead + "0\n");
        AssertRequires(Member(hidden, "R"));
        AssertRequires(Member(hidden, "F", "W"));
        AssertRequires(Member(hidden, "F", "X"));
        Assert.Equal("7", Value(withRootRead + "F.X\n"));

        var unshared = RootIn(Mode.Unshared, withRootRead + "0\n");
        AssertRequires(Member(unshared, "F", "W"), ("x", 0));
        AssertRequires(Member(unshared, "F", "X"), ("x", 0));
    }

    /// <summary>
    /// THE RESOLUTION-WIDE GUARD IS LOAD-BEARING. Inside <c>F</c>, two libraries read each other and <c>K.M(1)</c>; <c>K.M</c>'s
    /// own settlement made an off-chain lookup first, so the members are settled by the ordinary walk, which takes that
    /// settlement's exact-key answer: <c>B0</c>, <c>B1</c> and <c>R</c> are exported and <c>F.R</c> reads <c>7</c>. Component
    /// equations solve a fresh discovery walk with no share, which computes the unshared settlement's answer (local-only on
    /// <c>x</c>; measured in a scratch build without the guard, where <c>F.R</c> is refused at <c>R</c>). A narrower guard
    /// must therefore refuse this component: the brief's option B admits a component after an off-chain lookup only when its
    /// discovery makes none and every settlement it reaches stands from every site.
    /// </summary>
    [Fact]
    public void TheResolutionWideGuard_KeepsTheExactKeyAnswersOfALaterComponent()
    {
        const string program = "K = { public M(z) = F.G + z }\nF(x) = {\npublic G = x + 1\n"
            + "L0 = {\nopen L1\npublic B0 = if(1 < 0, B1, [K.M(1), 7][1])\n}\n"
            + "L1 = {\nopen L0\npublic B1 = if(1 < 0, B0, [K.M(1), 7][1])\n}\n"
            + "public R = L0.B0\n0\n}\n";
        AssertExactKeyMetadata(program + "0\n");
        var root = Root(program + "0\n");
        AssertRequires(Member(root, "F", "L0", "B0"));
        AssertRequires(Member(root, "F", "L1", "B1"));
        AssertRequires(Member(root, "F", "R"));
        Assert.Equal("7", Value(program + "F.R\n"));

        var unshared = RootIn(Mode.Unshared, program + "0\n");
        AssertRequires(Member(unshared, "F", "L0", "B0"), ("x", 1));
        AssertRequires(Member(unshared, "F", "L1", "B1"), ("x", 1));
        AssertRequires(Member(unshared, "F", "R"), ("x", 0));
    }

    // ── Costs ───────────────────────────────────────────────────────────────

    /// <summary>
    /// An all-to-all component of <paramref name="libraries"/> libraries, each <c>L{i}</c> opening the others and reading
    /// each one's member, with an unrelated off-chain read <c>OffK.M</c> declared before it (<c>first</c>), after it
    /// (<c>last</c>) or absent (<c>none</c>).
    /// </summary>
    internal static string ComponentWithUnrelatedOffChainRead(int libraries, string offChain)
    {
        const string off = "OffF(y) = {\npublic G = y + 1\n0\n}\nOffK = { public M(z) = OffF.G + z }\n";
        var source = new StringBuilder(offChain == "first" ? off : "");
        for (var i = 0; i < libraries; i++)
        {
            var others = Enumerable.Range(0, libraries).Where(j => j != i).ToArray();
            source.Append($"L{i} = {{\n  open {string.Join(", ", others.Select(j => $"L{j}"))}\n");
            source.Append($"  public F{i}(n) = if(n < 1, 0, {string.Join(" + ", others.Select(j => $"F{j}(n - 1)"))})\n}}\n");
        }
        if (offChain == "last") source.Append(off);
        return source.Append("L0.F0(2)\n").ToString();
    }

    /// <summary>
    /// The second residual: once any settlement of a resolution has looked up an owner off its site's chain, no component
    /// equations are solved for the rest of it, so an UNRELATED off-chain read declared before an all-to-all component takes
    /// the component from 184 / 692 frames (4 / 8 libraries) to 831 / 29,091, while the same read declared after it costs two
    /// frames more than none. The metadata of the libraries is the same in all three programs. Under options B and C the
    /// read declared first costs what the read declared last costs.
    /// </summary>
    [Theory]
    [InlineData(4, 184, 831, 186, 6)]
    [InlineData(8, 692, 29_091, 694, 14)]
    public void AnUnrelatedOffChainRead_DisablesComponentEquationsForTheRestOfTheResolution(int libraries, long none, long first,
        long last, long completions)
    {
        var plain = Parse(ComponentWithUnrelatedOffChainRead(libraries, "none"));
        var before = Parse(ComponentWithUnrelatedOffChainRead(libraries, "first"));
        var after = Parse(ComponentWithUnrelatedOffChainRead(libraries, "last"));
        Assert.Equal(none, plain.Observations.RequiredAncestorSettlementFrames);
        Assert.Equal(first, before.Observations.RequiredAncestorSettlementFrames);
        Assert.Equal(last, after.Observations.RequiredAncestorSettlementFrames);
        Assert.Equal(completions, plain.Observations.SettlementComponentCompletions);
        Assert.Equal(0, before.Observations.SettlementComponentCompletions);
        Assert.Equal(completions, after.Observations.SettlementComponentCompletions);

        static string Libraries(string metadata)
            => string.Concat(metadata.Split('\n').Where(line => line.StartsWith(".L", StringComparison.Ordinal)).Select(line => line + "\n"));
        Assert.Equal(Libraries(plain.Metadata), Libraries(before.Metadata));
        Assert.Equal(Libraries(plain.Metadata), Libraries(after.Metadata));
        Assert.Equal("0", Value(ComponentWithUnrelatedOffChainRead(libraries, "first")));
    }

    /// <summary>
    /// The branching chain over the off-chain terminal (<c>P{i}.A</c> reads <c>P{i-1}.A</c> and <c>P{i-2}.A</c>; <c>P0.A</c>
    /// reads <c>F.G</c>, whose owner is on no level of any link's chain) grows by about 1.6 per link — 600 and 4,354 frames
    /// at 8 and 12 links (a 1 KB program of 24 links is refused by the default work bound) — while the same chain over
    /// <c>x + 1</c> is linear (52 and 84). Every link is exported in both. Under option C the off-chain chain takes 8N − 4
    /// frames (60 and 92); option B leaves it as it is.
    /// </summary>
    [Theory]
    [InlineData(8, 600, 52)]
    [InlineData(12, 4_354, 84)]
    public void TheBranchingOffChainTerminal_IsExponential_AndItsOnChainControlLinear(int links, long offChain, long control)
    {
        static string Branching(int links, string terminal)
        {
            var source = new StringBuilder(terminal == "F.G + x" ? "F(y) = {\npublic G = y + 1\n0\n}\n" : "");
            source.Append($"P0 = {{ public A(x) = {terminal} }}\nP1 = {{ public A(x) = P0.A(1) + 1 }}\n");
            for (var i = 2; i <= links; i++) source.Append($"P{i} = {{ public A(x) = P{i - 1}.A(1) + P{i - 2}.A(1) }}\n");
            return source.Append("0\n").ToString();
        }

        var off = Branching(links, "F.G + x");
        var on = Branching(links, "x + 1");
        Assert.Equal(offChain, Parse(off).Observations.RequiredAncestorSettlementFrames);
        Assert.Equal(control, Parse(on).Observations.RequiredAncestorSettlementFrames);
        AssertExactKeyMetadata(off);
        foreach (var source in new[] { off, on })
        {
            var root = Root(source);
            for (var i = 0; i <= links; i++)
                AssertRequires(Member(root, $"P{i}", "A"));
        }
    }
}
