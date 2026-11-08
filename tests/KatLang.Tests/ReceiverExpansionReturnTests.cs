using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Receiver expansion returning through a transparent body with members still pending below it (static-structure query
/// contracts, receiver expansion). Expansion navigates a stack of pending members: a transparent body pushes its own
/// row's members, a carrier consumes one and continues at that member's body. The first-expansion recipe
/// (<c>ReceiverExpansionCycle</c>) records only the first transparent body it reaches, so for <c>C = A.M.abs</c> with
/// <c>A = B</c> and <c>B = { public M = C }</c> it finishes at B while <c>.M.abs</c> is still pending, misses the return
/// <c>B.M = C</c>, and valid source reached "An invocation target must be conclusive after A1 admission." The
/// continuation-aware completion (<c>ReceiverExpansionNav</c>/<c>End</c> summaries and the <c>ReceiverExpansionVerdict</c>
/// closure observer) keeps every pending member; revisiting an in-place expansion while none of the members below it
/// has been consumed proves the return, and reaching a body again after they were consumed does not
/// (<c>B.M.M.N</c> with <c>M = B</c> is <c>B.N</c>).
/// </summary>
public sealed class ReceiverExpansionReturnTests
{
    private const string HandCases = """
        ### V01 N1 minimal, fallback
        #= compiles
        A = B
        --
        B = { public M = C
         0 }
        --
        C = A.M.abs

        ### V01i inlined control
        #= compiles
        B = { public M = C
         0 }
        --
        C = B.M.abs

        ### V02 link ending
        #= compiles
        A = B
        --
        B = { public M = C
         0 }
        --
        C = A.M.Algorithm

        ### V03 string ending
        #= compiles
        A = B
        --
        B = { public M = C
         0 }
        --
        C = A.M.string

        ### V04 user fallback ending
        #= compiles
        Inc(v) = v + 1
        --
        A = B
        --
        B = { public M = C
         0 }
        --
        C = A.M.Inc

        ### V05 two-level bare chain
        #= compiles
        A = A2
        --
        A2 = B
        --
        B = { public M = C
         0 }
        --
        C = A.M.abs

        ### V06 reference through a member path
        #= compiles
        L = { public Sub = { public M = C
          0 }
         0 }
        --
        A = L.Sub
        --
        C = A.M.abs

        ### V06i inlined control
        #= compiles
        L = { public Sub = { public M = C
          0 }
         0 }
        --
        C = L.Sub.M.abs

        ### V07 longer member path
        #= compiles
        A = B
        --
        B = { public M = { public N = C
          0 }
         0 }
        --
        C = A.M.N.abs

        ### V08 a root row reads the body
        #= err EvaluationDepthExceeded
        A = B
        --
        B = { public M = C
         0 }
        --
        C = A.M.abs
        --
        @last C

        ### V08i inlined control with the same row
        #= err EvaluationDepthExceeded
        B = { public M = C
         0 }
        --
        C = B.M.abs
        --
        @last C

        ### V09 braced carrier instead of a reference
        #= compiles
        A = { B }
        --
        B = { public M = C
         0 }
        --
        C = A.M.abs

        ### V10 the member returns through a second reference
        #= compiles
        A = B
        --
        B = { public M = D
         0 }
        --
        D = C
        --
        C = A.M.abs

        ### V11 member reference to the reference itself
        #= compiles
        A = B
        --
        B = { public M = A
         0 }
        --
        C = A.M.abs

        ### V12 no return: the member is a constant
        #= ok 5
        A = B
        --
        B = { public M = 5
         0 }
        --
        C = A.M.abs
        --
        @last C

        ### V13 no return: the member is a block with abs
        #= ok 7
        A = B
        --
        B = { public M = { public abs = 7 }
         0 }
        --
        C = A.M.abs
        --
        @last C

        ### V14 reference to a member reference, cycle through the reference
        #= compiles
        A = B.M
        --
        B = { public M = C
         0 }
        --
        C = A.abs

        ### V15 reference opened from a module-like holder
        #= compiles
        Lib = { public B = { public M = C
          0 }
         0 }
        --
        A = Lib.B
        --
        C = A.M.abs

        ### V16 nested owner
        #= ok 0
        O = { A = B
         B = { public M = C
          0 }
         C = A.M.abs
         0 }
        --
        @last O

        ### V17 parameterized owner
        #= ok 1
        O(p) = { A = B
         B = { public M = C
          0 }
         C = A.M.abs
         p }
        --
        @last O(1)

        ### V18 reference chain through a member, two bodies loop
        #= compiles
        A = B
        --
        B = { public M = C.N
         0 }
        --
        C = A.M.abs

        ### W1 contract witness: receiver expansion returns to A, P infers x
        #= compiles
        F(v) = 0
        --
        A = A.F
        --
        P = A.x

        ### W1r the witness read through P with a callable argument
        #= ok 1
        Inc(v) = v + 1
        --
        F(v) = 0
        --
        A = A.F
        --
        P = A.x
        --
        @last P(Inc)

        ### W2 contract witness: B references A
        #= compiles
        A = B.F
        --
        B = A

        ### X1 mutual loop through first expansions
        #= compiles
        X = Y.abs
        --
        Y = X.abs

        ### X2 mutual loop, mixed endings
        #= err EvaluationDepthExceeded
        X = Y.abs
        --
        Y = X.string
        --
        @last X

        ### V19 the member returns through a member path of the origin
        #= compiles
        A = B
        --
        B = { public M = U
         0 }
        --
        U = C.N
        --
        C = A.M.abs

        ### V19i inlined twin
        #= compiles
        B = { public M = U
         0 }
        --
        U = C.N
        --
        C = B.M.abs

        ### V20 no reference at all: a self member
        #= compiles
        B = { public M = B
         public N = C
         0 }
        --
        C = B.M.N.abs

        ### V21 a deep bare chain into the loop
        #= compiles
        A1 = B
        --
        A2 = A1
        --
        A3 = A2
        --
        B = { public M = C
         0 }
        --
        C = A3.M.abs

        ### V22 two loops through one holder
        #= compiles
        A = B
        --
        B = { public M = C1
         public N = C2
         0 }
        --
        C1 = A.M.abs
        --
        C2 = A.N.abs

        ### V23 a loop seen through an open
        #= ok 5
        A = B
        --
        B = { public M = C
         0 }
        --
        C = A.M.abs
        --
        K = { open A
         5 }
        --
        @last K

        ### V24 the loop body read by another body
        #= ok 7
        A = B
        --
        B = { public M = C
         0 }
        --
        C = A.M.abs
        --
        D = C.abs
        --
        @last 7

        ### V25 member path reference chain into the loop
        #= compiles
        L = { public Sub = { public M = C
          0 }
         0 }
        --
        A = L.Sub
        --
        A2 = A
        --
        C = A2.M.abs

        ### P01 a self member revisited with a shorter path: C is an alias of Q
        #= ok 5
        Q = { public V = 5 }
        --
        B = { public M = B
         public N = Q
         0 }
        --
        C = B.M.M.N
        --
        @last C.V

        ### P01i inlined: B.M.M is B
        #= ok 5
        Q = { public V = 5 }
        --
        B = { public M = B
         public N = Q
         0 }
        --
        C = B.N
        --
        @last C.V

        ### P02 the same path ending at a constant member
        #= ok 5
        Q = { public V = 5 }
        --
        B = { public M = B
         public N = Q
         0 }
        --
        C = B.M.M.N.V
        --
        @last C

        ### P03 the same through a reference A = B
        #= ok 5
        Q = { public V = 5 }
        --
        A = B
        --
        B = { public M = A
         public N = Q
         0 }
        --
        C = A.M.M.N
        --
        @last C.V

        ### R01 the minimal example demanded through a final row
        #= ok 7
        A = B
        --
        B = { public M = C
         0 }
        --
        C = A.M.abs
        --
        @last 7

        ### R02 the link ending with a final row
        #= ok 7
        A = B
        --
        B = { public M = C
         0 }
        --
        C = A.M.Algorithm
        --
        @last 7

        ### R03 the self member with a final row
        #= ok 7
        B = { public M = B
         public N = C
         0 }
        --
        C = B.M.N.abs
        --
        @last 7
        """;

    private static readonly IReadOnlyList<DeclarationOrderCases.Case> Parsed = DeclarationOrderCases.Parse(HandCases);

    public static TheoryData<string> CaseIds() => new(Parsed.Select(static c => c.Id));

    [Theory]
    [MemberData(nameof(CaseIds))]
    public void EveryDeclarationOrderGivesTheCanonicalOutcome(string id)
    {
        var value = DeclarationOrderCases.Single(Parsed, id);
        Assert.NotNull(value.Expected);
        Assert.Equal(value.Expected, DeclarationOrderCases.OutcomeInEveryOrder(value));
    }

    /// <summary>An inlined twin (the reference replaced by its target) has its original's outcome in every order.</summary>
    [Theory]
    [InlineData("V01", "V01i")]
    [InlineData("V06", "V06i")]
    [InlineData("V08", "V08i")]
    [InlineData("V19", "V19i")]
    [InlineData("P01", "P01i")]
    public void AnInlinedTwinAgrees(string original, string twin)
        => Assert.Equal(DeclarationOrderCases.OutcomeInEveryOrder(DeclarationOrderCases.Single(Parsed, original)),
            DeclarationOrderCases.OutcomeInEveryOrder(DeclarationOrderCases.Single(Parsed, twin)));

    [Fact]
    public void TheCaseTableIsNotVacuous()
    {
        var expected = Parsed.Select(static c => c.Expected!).ToArray();
        Assert.Equal(Parsed.Count, Parsed.Select(static c => c.Id).Distinct().Count());
        Assert.True(expected.Count(static e => e == "compiles") >= 20);
        Assert.True(expected.Count(static e => e == "err EvaluationDepthExceeded") >= 3);
        Assert.True(expected.Count(static e => e.StartsWith("ok ", StringComparison.Ordinal)) >= 10);
        Assert.Equal(498, Parsed.Sum(static c => DeclarationOrderCases.Orders(c).Count()));
    }

    // ── The reference-inlining law (Appendix B of the brief): 3 references x 8 members x 7 paths x 3 readers ──

    [Fact]
    public void TheReferenceInliningLawHoldsInBothDeclarationOrders()
    {
        (string[] Decls, string Target)[] references = [(["A = B"], "B"), (["A = A2", "A2 = B"], "B"), (["A = L.Sub"], "L.Sub")];
        (string Member, string[] Extra)[] members =
        [
            ("C", []), ("D", ["D = C"]), ("A", []), ("5", []), ("{ public abs = 7 }", []), ("{ public N = C }", []),
            ("{ public N = 6 }", []), ("C + 1", []),
        ];
        string[] paths = ["M.abs", "M.Algorithm", "M.string", "M.Inc", "M.N.abs", "M", "M.N"];
        string[] readers = ["", "C", "C + 0"];
        var classes = new Dictionary<string, int>(StringComparer.Ordinal);
        var pairs = 0;
        foreach (var (decls, target) in references)
        foreach (var (member, extra) in members)
        foreach (var path in paths)
        foreach (var reader in readers)
        {
            var block = "{ public M = " + member + "\n 0 }";
            var shared = new List<string> { "Inc(v) = v + 1", target == "B" ? "B = " + block : "L = { public Sub = " + block + "\n 0 }" };
            shared.AddRange(extra);
            shared.AddRange(decls);
            var viaReference = TwoOrders([.. shared, "C = A." + path], reader);
            var inlined = TwoOrders([.. shared, "C = " + target + "." + path], reader);
            Assert.True(viaReference == inlined, $"C = A.{path} gave {viaReference}, C = {target}.{path} gave {inlined}\n{string.Join("\n", shared)}");
            classes[viaReference] = classes.GetValueOrDefault(viaReference) + 1;
            pairs++;
        }
        Assert.Equal(504, pairs);
        Assert.True(classes.GetValueOrDefault("compiles") > 0);
        Assert.True(classes.GetValueOrDefault("err EvaluationDepthExceeded") > 0);
        Assert.Contains(classes.Keys, static k => k.StartsWith("ok ", StringComparison.Ordinal));
        Assert.True(classes.Count >= 6, string.Join(", ", classes.Select(static p => $"{p.Value}x {p.Key}")));
    }

    // ── The revisit grammar (Appendix C), stratified ──

    /// <summary>
    /// A holder <c>B</c> whose two members name the holder, other bodies or nested blocks, bare, member-path and chained
    /// references, multi-member paths and readers. The full grammar is 14,784 programs; this stratum keeps every program
    /// whose first member <c>m1</c> names the holder, the reader or the reference (every host exception of the unfixed
    /// baseline is in it: 180 of them, all with <c>m1</c> in <c>B, C, A</c>), plus a front-end-only control stratum of the
    /// other members against <c>m2</c> in <c>B, C</c>. Each runs as written and reversed; a program reading through the
    /// reference <c>A</c> must agree with its inlined twin.
    /// </summary>
    [Fact]
    public void TheRevisitGrammarHasNoHostExceptionOrderDependenceOrInliningDisagreement()
    {
        string[] memberRows = ["B", "C", "A", "Q", "5", "{ public N = C }", "{ public M = B }", "C + 1"];
        (string[] Decls, string Target)[] refs = [([], ""), (["A = B"], "B"), (["A = B.M"], "B.M"), (["A = A2", "A2 = B"], "B")];
        string[] paths = ["M", "M.M", "M.N", "M.M.N", "M.N.M", "M.abs", "M.M.abs", "M.N.abs", "M.Algorithm", "M.M.Algorithm", "M.N.N"];
        var classes = new Dictionary<string, int>(StringComparer.Ordinal);
        int programs = 0, twins = 0;
        foreach (var m1 in memberRows)
        foreach (var m2 in memberRows)
        {
            var returning = m1 is "B" or "C" or "A";
            if (!returning && m2 is not ("B" or "C")) continue;
            string[] readers = returning ? ["", "C", "C.V"] : [""];
            foreach (var (decls, target) in refs)
            foreach (var head in decls.Length == 0 ? ["B"] : new[] { "A", "B" })
            foreach (var path in paths)
            foreach (var reader in readers)
            {
                var shared = new List<string> { "Q = { public V = 5 }", "B = { public M = " + m1 + "\n public N = " + m2 + "\n 0 }" };
                shared.AddRange(decls);
                var outcome = TwoOrders([.. shared, "C = " + head + "." + path], reader);
                classes[outcome] = classes.GetValueOrDefault(outcome) + 1;
                programs++;
                if (head != "A") continue;
                var inlined = TwoOrders([.. shared, "C = " + target + "." + path], reader);
                Assert.True(outcome == inlined, $"C = A.{path} gave {outcome}, C = {target}.{path} gave {inlined}\n{string.Join("\n", shared)}");
                twins++;
            }
        }
        Assert.Equal(6314, programs);
        Assert.True(twins > 2000, twins.ToString());
        foreach (var expected in new[] { "compiles", "ok 5", "err EvaluationDepthExceeded", "err UnresolvedImplicitParams" })
            Assert.True(classes.GetValueOrDefault(expected) > 0, expected + ": " + string.Join(", ", classes.Select(static p => $"{p.Value}x {p.Key}")));
    }

    private static string TwoOrders(List<string> decls, string reader)
    {
        var tail = reader.Length == 0 ? "" : reader + "\n";
        var forward = DeclarationOrderCases.Outcome(string.Join("\n", decls) + "\n" + tail);
        var reversed = DeclarationOrderCases.Outcome(string.Join("\n", Enumerable.Reverse(decls)) + "\n" + tail);
        Assert.True(forward == reversed, $"order-dependent: {forward} / reversed {reversed}\n{string.Join("\n", decls)}\n{tail}");
        return forward;
    }

    // ── Query-level classification ──

    private static StaticStructureQueries Model(string source, CancellationToken cancellationToken = default)
        => new(SourceProvenance.ParseSyntaxValidRoot(source), new(1_000_000, 4, 100_000, 4_000_000), cancellationToken: cancellationToken);

    private static StaticScopeKey At(StaticStructureQueries q, string path)
    {
        var scope = q.Root;
        foreach (var part in path.Split('.'))
            scope = q.BodyIn(scope, q.BodyOf(scope).Properties.Single(p => p.Name == part).Value);
        return scope;
    }

    private static StaticQueryKey Walk(StaticScopeKey scope, StaticQueryProjection projection, StaticCycleCheck stratum = StaticCycleCheck.Formation)
        => StaticQueryKey.Project(StaticQueryKind.TargetWalk, scope, projection, stratum: stratum);

    /// <summary>
    /// The return is decided by the verdict, not by the first-expansion recipe: the recipe's cycle is No (A expands to
    /// the carrier B), the body's own summary stays undecided (it waits on its own expansion), and the verdict proves the
    /// pending return. C is then its own calculation namespace (<c>.abs</c>) or a runtime link (<c>.Algorithm</c>), and
    /// its invocation target is conclusive.
    /// </summary>
    [Theory]
    [InlineData("A = B\nB = { public M = C\n 0 }\nC = A.M.abs\n0", false)]
    [InlineData("A = B\nB = { public M = C\n 0 }\nC = A.M.Algorithm\n0", true)]
    [InlineData("B = { public M = B\n public N = C\n 0 }\nC = B.M.N.abs\n0", false)]
    public void APendingReturnIsDecidedByTheVerdict_AndKeepsTheRowClass(string source, bool runtimeLink)
    {
        var expected = runtimeLink ? StaticFactKind.Runtime : StaticFactKind.Structure;
        foreach (var stratum in new[] { StaticCycleCheck.None, StaticCycleCheck.Lower, StaticCycleCheck.Formation })
        {
            var q = Model(source);
            var c = At(q, "C");
            var structure = q.Get(StaticQueryKey.TargetWalk(c, stratum));
            Assert.Equal(expected, structure.Kind);
            Assert.Same(c, structure.Scope);
            Assert.Equal(StaticFactKind.No, q.Get(Walk(c, StaticQueryProjection.ReceiverExpansionCycle, stratum)).Kind);
            Assert.Equal(StaticFactKind.Unknown, q.Get(Walk(c, StaticQueryProjection.ReceiverExpansionNav, stratum)).Kind);
            Assert.Equal(StaticFactKind.Yes, q.Get(Walk(c, StaticQueryProjection.ReceiverExpansionVerdict, stratum)).Kind);
            Assert.Equal(StaticFactKind.Yes, q.Get(Walk(c, StaticQueryProjection.OpenReceiverExpansionVerdict, stratum)).Kind);
            Assert.NotEqual(StaticFactKind.Unknown, q.Get(StaticQueryKey.Project(StaticQueryKind.TargetWalk, c, StaticQueryProjection.InvocationTarget)).Kind);
        }
    }

    /// <summary>
    /// The terminating control: consuming the M members reaches B.N. Its own summary decides it (Q), no verdict is
    /// needed, and C is an alias of Q with Q's identity.
    /// </summary>
    [Theory]
    [InlineData("Q = { public V = 5 }\nB = { public M = B\n public N = Q\n 0 }\nC = B.M.M.N\n0")]
    [InlineData("Q = { public V = 5 }\nA = B\nB = { public M = A\n public N = Q\n 0 }\nC = A.M.M.N\n0")]
    public void ConsumedMembersAreNoReturn_TheTargetKeepsItsIdentity(string source)
    {
        var q = Model(source);
        var c = At(q, "C");
        var queue = At(q, "Q");
        Assert.Same(queue, q.Get(StaticQueryKey.TargetWalk(c, StaticCycleCheck.Formation)).Scope);
        // Its own summary reaches the member body B.N, whose row Q the ordinary walk then follows.
        var nav = q.Get(Walk(c, StaticQueryProjection.ReceiverExpansionNav));
        Assert.Equal(StaticFactKind.Structure, nav.Kind);
        Assert.Same(At(q, "B.N"), nav.Scope);
        Assert.Equal(StaticFactKind.No, q.Get(Walk(c, StaticQueryProjection.ReceiverExpansionVerdict)).Kind);
    }

    /// <summary>
    /// The first-expansion recipe still owns its own returns (X1, W1, W2): those programs never create the
    /// continuation-aware summaries, so a ring of first expansions keeps its linear path-cycle cost.
    /// </summary>
    [Theory]
    [InlineData("X = Y.abs\nY = X.abs\n0", "X")]
    [InlineData("F(v) = 0\nA = A.F\nP = A.x\n0", "A")]
    [InlineData("F(v)=0\nA = B.F\nB = A\n0", "A")]
    public void AFirstExpansionReturnNeverReadsTheSummaries(string source, string name)
    {
        var observations = Observe(source, out var diagnostics);
        Assert.Empty(diagnostics);
        Assert.DoesNotContain(observations.StaticQueryEvaluations.Keys, static key => key.Projection is StaticQueryProjection.ReceiverExpansionNav
            or StaticQueryProjection.OpenReceiverExpansionNav or StaticQueryProjection.ReceiverExpansionVerdict or StaticQueryProjection.OpenReceiverExpansionVerdict);
        var q = Model(source);
        var scope = At(q, name);
        Assert.Equal(StaticFactKind.Refused, q.Get(Walk(scope, StaticQueryProjection.ReceiverExpansionCycle)).Kind);
        Assert.Same(scope, q.Get(StaticQueryKey.TargetWalk(scope, StaticCycleCheck.Formation)).Scope);
    }

    /// <summary>The production detection and resolution passes over one admitted operation, observed.</summary>
    internal static FrontEndTraversalObservations Observe(string source, out DiagnosticBag diagnostics)
        => Observe(source, out diagnostics, out _);

    internal static FrontEndTraversalObservations Observe(string source, out DiagnosticBag diagnostics, out StaticQueryStatistics statistics)
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(source);
        var operation = StaticStructureAdmission.Create(root).Operation;
        var observations = new FrontEndTraversalObservations();
        diagnostics = new DiagnosticBag();
        var modules = new ModuleUnits();
        var detected = ParameterDetector.DetectPrevalidated(root, null, observations, diagnostics, modules, operation);
        ImplicitArgumentResolver.ResolvePrevalidated(detected.Root, observations, diagnostics, null, modules, operation);
        statistics = operation.Queries.Statistics;
        return observations;
    }

    /// <summary>
    /// Query-demand independence: Inputs, receiver structure, target cycles, the invocation target, open structure and
    /// open providers, in every stratum and both binding modes, are demanded in many orders within one operation and
    /// always reach the same final facts.
    /// </summary>
    [Theory]
    [InlineData("A = B\nB = { public M = C\n 0 }\nC = A.M.abs\nK = { open A\n 5 }\n0", "C", "K")]
    [InlineData("A = B\nB = { public M = C\n 0 }\nC = A.M.Algorithm\nK = { open C\n 5 }\n0", "C", "K")]
    [InlineData("B = { public M = B\n public N = C\n 0 }\nC = B.M.N.abs\nK = { open C\n 5 }\n0", "C", "K")]
    [InlineData("A = A.Algorithm\nB = { open C\n M }\nC = A.abs\n0", "C", "B")]
    public void FinalFactsDoNotDependOnQueryDemandOrder(string source, string body, string opener)
    {
        var strata = new[] { StaticCycleCheck.None, StaticCycleCheck.Lower, StaticCycleCheck.Formation };
        StaticQueryKey[] Requests(StaticStructureQueries q)
        {
            var scope = At(q, body);
            var keys = new List<StaticQueryKey> { StaticQueryKey.Inputs(scope),
                StaticQueryKey.Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.InvocationTarget),
                StaticQueryKey.OpenProviders(At(q, opener), StaticCycleCheck.Formation) };
            foreach (var stratum in strata)
            {
                keys.Add(StaticQueryKey.TargetWalk(scope, stratum));
                keys.Add(Walk(scope, StaticQueryProjection.OpenStructure, stratum));
                keys.Add(Walk(scope, StaticQueryProjection.TargetCycle, stratum));
                keys.Add(Walk(scope, StaticQueryProjection.ReceiverExpansionVerdict, stratum));
                keys.Add(Walk(scope, StaticQueryProjection.OpenReceiverExpansionVerdict, stratum));
            }
            return [.. keys];
        }
        string? expected = null;
        for (var pass = 0; pass < 12; pass++)
        {
            var q = Model(source);
            var requests = Requests(q);
            var order = pass switch
            {
                0 => requests,
                1 => requests.Reverse().ToArray(),
                _ => requests.OrderBy(k => (Array.IndexOf(requests, k) * 7 + pass * 5) % requests.Length).ToArray(),
            };
            foreach (var key in order) q.Get(key);
            var facts = string.Join(" | ", requests.Select(k => Describe(q, q.Get(k))));
            expected ??= facts;
            Assert.Equal(expected, facts);
        }
    }

    private static string Describe(StaticStructureQueries q, StaticFact fact)
    {
        var text = fact.Kind.ToString();
        if (fact.Scope is { } scope)
            text += "@" + (q.BodyOf(q.Root).Properties.FirstOrDefault(p => ReferenceEquals(q.BodyIn(q.Root, p.Value), scope))?.Name ?? "nested");
        if (fact.Data is string[] names) text += "[" + string.Join(",", names) + "]";
        return text;
    }

    // ── Public routes ──

    [Theory]
    [InlineData("A = B\nB = { public M = C\n 0 }\nC = A.M.abs\n7", "7")]
    [InlineData("A = B\nB = { public M = C\n 0 }\nC = A.M.Algorithm\n7", "7")]
    [InlineData("B = { public M = B\n public N = C\n 0 }\nC = B.M.N.abs\n7", "7")]
    [InlineData("A = B\nB = { public M = C\n 0 }\nC = A.M.abs\nK = { open A\n 5 }\nK", "5")]
    [InlineData("Q = { public V = 5 }\nB = { public M = B\n public N = Q\n 0 }\nC = B.M.M.N\nC.V", "5")]
    public async Task EveryPublicRouteAgrees(string source, string value)
    {
        SourceProvenance.ParseValid(source);
        var observed = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", observed.Kind);
        Assert.Equal(value, observed.Value);
        var model = SemanticModelBuilder.Build(Parser.Parse(source));
        Assert.Equal("C", Assert.Single(model.FindProperties("C")).DisplaySignature);
    }

    [Fact]
    public async Task ADemandedRecursiveCalculationFailsLikeItsInlinedTwin_OnEveryRoute()
    {
        // A depth the async twin reaches before its host-stack backstop; both twins use the same options.
        var limits = new EvaluationLimits { MaxDepth = 16 };
        var viaReference = await SixRouteAgreement.OnEveryRouteAsync("A = B\nB = { public M = C\n 0 }\nC = A.M.abs\nC", limits: limits);
        var inlined = await SixRouteAgreement.OnEveryRouteAsync("B = { public M = C\n 0 }\nC = B.M.abs\nC", limits: limits);
        Assert.Equal("err", viaReference.Kind);
        Assert.StartsWith("EvaluationDepthExceeded:", Assert.Single(viaReference.Errors), StringComparison.Ordinal);
        Assert.Equal(inlined.Kind, viaReference.Kind);
        Assert.Equal(inlined.Errors.Select(static e => e[..e.IndexOf(':')]), viaReference.Errors.Select(static e => e[..e.IndexOf(':')]));
    }

    [Fact]
    public void TheWitnessKeepsItsInferredParameter_InTheEditor()
    {
        const string source = "F(v) = 0\nA = A.F\nP = A.x\n0";
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        Assert.Equal("P(x)", Assert.Single(model.FindProperties("P")).DisplaySignature);
    }

    // ── Failure and lifetime boundaries ──

    private static string Ring(int size)
    {
        var text = new System.Text.StringBuilder();
        for (var i = 1; i <= size; i++) text.Append($"A{i} = B{i}\nB{i} = {{ public M = C{i % size + 1}\n 0 }}\nC{i} = A{i}.M.abs\n");
        return text.Append("7\n").ToString();
    }

    /// <summary>
    /// A cancellation inside a verdict walk faults the operation: the walk's charge observes the token, the ledger
    /// fails, and nothing is published afterwards.
    /// </summary>
    [Fact]
    public void CancellationInsideAVerdictWalkFaultsTheOperation()
    {
        using var cancellation = new CancellationTokenSource();
        var q = Model(Ring(8), cancellation.Token);
        var steps = 0;
        q.ReceiverExpansionWalkStepForTesting = () => { if (++steps == 3) cancellation.Cancel(); };
        var c = At(q, "C1");
        var error = Assert.ThrowsAny<OperationCanceledException>(() => q.Get(StaticQueryKey.TargetWalk(c, StaticCycleCheck.Formation)));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.True(steps >= 3);
        Assert.True(q.Resources.IsFailed);
        Assert.Throws<InvalidOperationException>(() => q.Get(StaticQueryKey.TargetWalk(c, StaticCycleCheck.Formation)));
    }

    [Fact]
    public void TheWalkObservesTheHookAndCompletesWithoutIt()
    {
        var q = Model(Ring(8));
        var steps = 0;
        q.ReceiverExpansionWalkStepForTesting = () => steps++;
        Assert.Equal(StaticFactKind.Yes, q.Get(Walk(At(q, "C1"), StaticQueryProjection.ReceiverExpansionVerdict)).Kind);
        Assert.True(steps > 0);
    }

    /// <summary>A low static budget is the resource refusal, never a host exception or an inference failure.</summary>
    [Fact]
    public void ALowStaticBudgetIsAResourceRefusal()
    {
        var source = Ring(48);
        var tight = Parser.Parse(source, new RunOptions { SourceProcessingLimits = new() { MaxStaticStructureBytes = 256 * 1024 } });
        var refusal = Assert.Single(tight.Diagnostics, static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, refusal.Code);
        Assert.False(Parser.Parse(source).HasErrors);
        var q = new StaticStructureQueries(SourceProvenance.ParseSyntaxValidRoot(source), new(2_000, 4, 100_000, 4_000_000));
        Assert.Throws<StaticQueryLimitExceededException>(() => q.Get(StaticQueryKey.TargetWalk(At(q, "C1"), StaticCycleCheck.Formation)));
        Assert.Throws<InvalidOperationException>(() => q.Get(StaticQueryKey.TargetWalk(At(q, "C2"), StaticCycleCheck.Formation)));
    }

    // ── Scheduling of decision observers ──

    private sealed class Observed(List<int> order) : IStaticQueryDefinition<int, int>
    {
        public StaticQueryStep<int> Compute(int key, StaticQueryReader<int, int> reader)
        {
            order.Add(key);
            if (key == 0) { reader.Read(1); reader.Read(2); reader.Read(3); }
            return StaticQueryStep.Complete(key == 0 ? 0 : 1);
        }

        public int Initial(int key) => 0;
        public bool IsClosureObserver(int key) => key != 0;
        public bool IsDecisionObserver(int key) => key == 3;
        public int PathCycleValue => -1;
        public bool ValueEquals(int left, int right) => left == right;
        public bool IsRefinement(int before, int after) => before == 0 || before == after;
    }

    [Fact]
    public void ADecisionObserverRunsBeforeTheOtherClosureObservers()
    {
        var order = new List<int>();
        var engine = new StaticQueryEngine<int, int>(new Observed(order));
        engine.Get(0);
        // Each observer's answer re-runs its ordinary reader (0) before the next observer.
        Assert.Equal([3, 1, 2], order.Where(static key => key != 0));
        Assert.Equal(0, order[0]);
    }
}
