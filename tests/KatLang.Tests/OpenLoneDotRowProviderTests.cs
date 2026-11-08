namespace KatLang.Tests;

/// <summary>
/// An <c>open</c> whose target body is a lone dot row (Lean <c>openStructure</c>, <c>Evaluator.OpenStructure</c>,
/// ownership-and-lookup OD-C). A body that is no transparent reference is its own namespace and the provider rule judges
/// it; a reference's head resolves DIRECTLY (its own declarations and declaring chain, never an open), its member steps
/// through declared members, and a reference whose head only an open provides is unresolved. Before this correction the
/// open stratum (1) answered <c>Missing</c> for every row that was no reference, so calculation links were silently
/// accepted, runtime links were refused, and a later receiver-return answer was a forbidden <c>Missing → Structure</c>
/// refinement (a host exception that depended on query order), and (2) found receiver returns through OPENS while the
/// target itself resolved directly. Each case is run in every declaration order.
/// </summary>
public sealed class OpenLoneDotRowProviderTests
{
    private const string Cases = """
        ### K01 cycle head, link
        #= compiles
        P5 = { open P3
         Z }
        --
        P6 = P6
        --
        P3 = P6.Algorithm

        ### N01 cycle head, fallback row
        #= compiles
        P5 = { open P3
         Z }
        --
        P6 = P6
        --
        P3 = P6.abs

        ### N02 cycle head, string row
        #= compiles
        P5 = { open P3
         Z }
        --
        P6 = P6
        --
        P3 = P6.string

        ### N03 cycle head, Invoke row
        #= compiles
        P5 = { open P3
         Z }
        --
        P6 = P6
        --
        P3 = P6.Invoke

        ### N04 cycle head, Arguments row
        #= compiles
        P5 = { open P3
         Z }
        --
        P6 = P6
        --
        P3 = P6.Arguments

        ### N07 link over a member of a cyclic head
        #= compiles
        P5 = { open P3
         Z }
        --
        P6 = { public M = P6.M }
        --
        P3 = P6.M.Algorithm

        ### N10 two providers, one link
        #= compiles
        Lib = { public F(x) = x }
        --
        P5 = { open Lib, P3
         F + Z }
        --
        P6 = P6
        --
        P3 = P6.Algorithm

        ### C14 mutual pair head
        #= compiles
        P6 = P7
        --
        P7 = P6
        --
        P5 = {open P3
         Z + 0 }
        --
        P3 = P6.Algorithm

        ### Y2 self-link inside the provider, reached through open
        #= front UnresolvedOpenTarget
        @first open Q
        --
        Q = { public S = S.Algorithm }
        --
        A = { open B
         M }
        --
        B = S.Algorithm

        ### Y1 the same, opened again
        #= front IllegalInOpen+UnresolvedOpenTarget
        @first open Q
        --
        Q = { public S = S.Algorithm }
        --
        A = { open B
         M }
        --
        B = S.Algorithm
        --
        K = { open A
         5 }

        ### Y4 receiver cycle through a head only an open provides
        #= compiles
        @first open Q
        --
        Q = { public S = B.string }
        --
        B = S
        --
        K = { open A
         M }
        --
        A = B.abs

        ### L01 calculation link
        #= front IllegalInOpen
        Mk(t) = t + 1
        --
        L = Mk.Algorithm
        --
        K = { open L
         5 }
        --
        @last K

        ### L05 runtime link
        #= ok 5
        Cap(meta r) = r
        --
        Inc(x) = x + 1
        --
        L = Cap(Inc(1)).Algorithm
        --
        K = { open L
         5 }
        --
        @last K

        ### L06 reference to a calculation link
        #= front IllegalInOpen
        Mk(t) = t + 1
        --
        L = Mk.Algorithm
        --
        A = L
        --
        K = { open A
         5 }
        --
        @last K

        ### L07 dotted open through a member link
        #= front IllegalInOpen
        Mk(t) = t + 1
        --
        Lib = { public L = Mk.Algorithm
         0 }
        --
        K = { open Lib.L
         5 }
        --
        @last K

        ### T10 parameterized fallback row
        #= front IllegalInOpen
        Add(x, y) = x + y
        --
        P6 = Add.abs
        --
        P2 = { open P6
         1 }
        --
        @last P2

        ### T15 family receiver through a fallback
        #= front IllegalInOpen
        P4(0) = 0
        P4(n) = n + 1
        --
        P1 = P4.abs
        --
        P2 = { open P1
         7 }
        --
        @last P2

        ### T11 number receiver: a calculation, opens nothing
        #= ok 1
        P6 = 5.abs
        --
        P2 = { open P6
         1 }
        --
        @last P2

        ### A2 call receiver: a calculation
        #= ok 5
        Mk(t) = t + 1
        --
        L = Mk(1).abs
        --
        K = { open L
         5 }
        --
        @last K

        ### A6 known receiver, prelude fallback
        #= ok 5
        Lib = { public X = 1 }
        --
        L = Lib.abs
        --
        K = { open L
         5 }
        --
        @last K

        ### A7 known receiver, member then fallback
        #= ok 5
        Lib = { public X = 1 }
        --
        L = Lib.X.abs
        --
        K = { open L
         5 }
        --
        @last K

        ### T12 head only an open provides, member hit: a reference, unresolved
        #= front UnresolvedOpenTarget
        Lib = { public B = { public X = 1 } }
        --
        K = { open Lib
         A = B.X
         M = { open A
          1 }
         M }
        --
        @last K

        ### B2 head only an open provides, fallback miss: a calculation
        #= ok 5
        Q = { public S = { public X = 1 } }
        --
        K = { open Q
         L = S.abs
         M = { open L
          5 }
         M }
        --
        @last K

        ### B3 link whose head only an open provides
        #= front UnresolvedOpenTarget
        Q = { public S = { public X = 1 } }
        --
        K = { open Q
         L = S.Algorithm
         M = { open L
          5 }
         M }
        --
        @last K

        ### B3z the same, with a lookup that reaches the open
        #= front UnresolvedOpenTarget
        Q = { public S = { public X = 1 } }
        --
        K(z) = { open Q
         L = S.Algorithm
         R(y) = { open L
          y.Nope }
         R(z) }
        --
        @last K(5)

        ### B7 parameterized callee that only an open provides, through a fallback row
        #= front IllegalInOpen
        Lib = { public Add(x, y) = x + y }
        --
        K = { open Lib
         L = Add.abs
         M = { open L
          5 }
         M }
        --
        @last K

        ### B7d the same through a written path
        #= front IllegalInOpen
        Lib = { public Add(x, y) = x + y }
        --
        L = Lib.Add.abs
        --
        K = { open L
         5 }
        --
        @last K

        ### B8 reference to a link whose head only an open provides
        #= front UnresolvedOpenTarget
        Q = { public S = { public X = 1 } }
        --
        K = { open Q
         L = S.Algorithm
         A = L
         M = { open A
          5 }
         M }
        --
        @last K

        ### B9 member of a reference whose head only an open provides
        #= front UnresolvedOpenTarget
        Q = { public S = { public X = 1 } }
        --
        K = { open Q
         P7 = S
         L = P7.X
         M = { open L
          5 }
         M }
        --
        @last K

        ### B10 link over that reference
        #= front UnresolvedOpenTarget
        Q = { public S = { public X = 1 } }
        --
        K = { open Q
         P7 = S
         L = P7.Algorithm
         M = { open L
          5 }
         M }
        --
        @last K

        ### B11 a declared string member makes the row a reference
        #= front UnresolvedOpenTarget
        Q = { public S = { public string = { public X = 1 } } }
        --
        K = { open Q
         L = S.string
         M = { open L
          5 }
         M }
        --
        @last K

        ### B12 fallback on that reference: a calculation
        #= ok 5
        Q = { public S = { public X = 1 } }
        --
        K = { open Q
         P7 = S
         L = P7.abs
         M = { open L
          5 }
         M }
        --
        @last K

        ### B13 calculation link whose head only an open provides
        #= front IllegalInOpen
        Lib = { public Mk(t) = t + 1 }
        --
        K = { open Lib
         L = Mk.Algorithm
         M = { open L
          5 }
         M }
        --
        @last K

        ### B14 reference to a parameterized calculation whose head only an open provides
        #= front IllegalInOpen
        Lib = { public Add(x, y) = x + y }
        --
        K = { open Lib
         L = Add.abs
         A = L
         M = { open A
          5 }
         M }
        --
        @last K

        ### B15 reference to a calculation link whose head only an open provides
        #= front IllegalInOpen
        Lib = { public Mk(t) = t + 1 }
        --
        K = { open Lib
         L = Mk.Algorithm
         A = L
         M = { open A
          5 }
         M }
        --
        @last K

        ### B16 reference to a closed calculation whose head only an open provides
        #= ok 5
        Q = { public S = { public X = 1 } }
        --
        K = { open Q
         L = S.abs
         A = L
         M = { open A
          5 }
         M }
        --
        @last K

        ### B17 dotted open to a parameterized calculation whose head only an open provides
        #= front IllegalInOpen
        Lib = { public Add(x, y) = x + y }
        --
        K = { open Lib
         B = { public L = Add.abs
          0 }
         M = { open B.L
          5 }
         M }
        --
        @last K

        ### C3 receiver cycle through an open, link
        #= front UnresolvedOpenTarget
        @first open Q
        --
        Q = { public S = P3 }
        --
        P3 = S.Algorithm
        --
        K = { open P3
         Z }

        ### C5 receiver cycle through an inline open
        #= front IllegalInOpen
        @first open { public S = P3 }
        --
        P3 = S.abs
        --
        K = { open P3
         Z }

        ### C2 receiver cycle through an open, intermediate reference: a calculation
        #= compiles
        @first open Q
        --
        Q = { public S = P3 }
        --
        P7 = S
        --
        P3 = P7.abs
        --
        K = { open P3
         Z }

        ### C4 the same with a string row
        #= compiles
        @first open Q
        --
        Q = { public S = P3 }
        --
        P7 = S
        --
        P3 = P7.string
        --
        K = { open P3
         Z }

        ### H01 a self-link read through a fallback row and opened (retained in the receiver-expansion evidence)
        #= compiles
        A = A.Algorithm
        --
        B = { open C
         M }
        --
        C = A.abs

        ### H02 the same, demanded
        #= ok 5
        A = A.Algorithm
        --
        B = { open C
         5 }
        --
        C = A.abs
        --
        @last B
        """;

    private static readonly IReadOnlyList<DeclarationOrderCases.Case> Parsed = DeclarationOrderCases.Parse(Cases);

    public static TheoryData<string> CaseIds() => new(Parsed.Select(static c => c.Id));

    [Theory]
    [MemberData(nameof(CaseIds))]
    public void EveryDeclarationOrderGivesThePinnedOutcome(string id)
    {
        var value = DeclarationOrderCases.Single(Parsed, id);
        Assert.NotNull(value.Expected);
        Assert.Equal(value.Expected, DeclarationOrderCases.OutcomeInEveryOrder(value));
    }

    [Fact]
    public void TheCaseTableExercisesEveryVerdictClass()
    {
        var expected = Parsed.Select(static c => c.Expected!).ToArray();
        Assert.Equal(Parsed.Count, Parsed.Select(static c => c.Id).Distinct().Count());
        Assert.Contains(expected, static e => e == "compiles");
        Assert.Contains(expected, static e => e.StartsWith("ok ", StringComparison.Ordinal));
        Assert.Contains(expected, static e => e == "front IllegalInOpen");
        Assert.Contains(expected, static e => e == "front UnresolvedOpenTarget");
        Assert.Contains(expected, static e => e == "front IllegalInOpen+UnresolvedOpenTarget");
        Assert.True(Parsed.Sum(static c => DeclarationOrderCases.Orders(c).Count()) >= 300);
    }

    private static StaticStructureQueries Model(string source)
        => new(SourceProvenance.ParseSyntaxValidRoot(source), new(1_000_000, 4, 100_000, 4_000_000));

    private static StaticScopeKey At(StaticStructureQueries q, string path)
    {
        var scope = q.Root;
        foreach (var part in path.Split('.'))
            scope = q.BodyIn(scope, q.BodyOf(scope).Properties.Single(p => p.Name == part).Value);
        return scope;
    }

    private static StaticQueryKey Open(StaticScopeKey scope, StaticQueryProjection projection)
        => StaticQueryKey.Project(StaticQueryKind.TargetWalk, scope, projection, stratum: StaticCycleCheck.Formation);

    /// <summary>
    /// A miss is a stable negative fact: the open structure of a reference whose head no direct lookup provides is
    /// <c>Missing</c> and keeps its TERMINAL (the body whose own row stays unresolved), and the open's provider fact
    /// carries the same terminal, so completion can tell a reference (unresolved) from a body that is its own namespace.
    /// The ordinary walk of the same body never reads through that question.
    /// </summary>
    [Theory]
    [InlineData("Q = { public S = { public X = 1 } }\nK = { open Q\n L = S.Algorithm\n M = { open L\n  5 }\n M }\n0", "K.L", "K.M")]
    [InlineData("Q = { public S = { public X = 1 } }\nK = { open Q\n L = S.Algorithm\n A = L\n M = { open A\n  5 }\n M }\n0", "K.L", "K.M")]
    public void ADirectMissKeepsItsTerminal_InEveryQueryDemandOrder(string source, string terminal, string opener)
    {
        foreach (var reversed in new[] { false, true })
        {
            var q = Model(source);
            var body = At(q, terminal);
            var openerScope = At(q, opener);
            var requests = new[]
            {
                StaticQueryKey.OpenProviders(openerScope, StaticCycleCheck.Formation),
                Open(body, StaticQueryProjection.OpenStructure),
                Open(body, StaticQueryProjection.OpenReceiverExpansionCycle),
                StaticQueryKey.TargetWalk(body, StaticCycleCheck.Formation),
            };
            foreach (var key in reversed ? requests.Reverse() : requests) q.Get(key);
            var open = q.Get(Open(body, StaticQueryProjection.OpenStructure));
            Assert.Equal(StaticFactKind.Missing, open.Kind);
            Assert.Same(body, open.Scope);
            var provided = q.Get(StaticQueryKey.Project(StaticQueryKind.OpenProviders, openerScope, StaticQueryProjection.OpenTarget,
                stratum: StaticCycleCheck.Formation, node: q.BodyOf(openerScope).Opens[0]));
            Assert.Equal(StaticFactKind.Providers, provided.Kind);
            Assert.Empty(Assert.IsType<StaticScopeKey[]>(provided.Data));
            Assert.Same(body, provided.Scope);
        }
    }

    /// <summary>
    /// A runtime link (<c>.Algorithm</c> over a call) is its own namespace in the open stratum and stays a runtime
    /// fact in the ordinary stratum; neither is a miss.
    /// </summary>
    [Fact]
    public void ARuntimeLinkIsItsOwnOpenNamespace_AndARuntimeFactOrdinarily()
    {
        var q = Model("Cap(meta r) = r\nInc(x) = x + 1\nL = Cap(Inc(1)).Algorithm\nK = { open L\n 5 }\n0");
        var link = At(q, "L");
        var open = q.Get(Open(link, StaticQueryProjection.OpenStructure));
        Assert.Equal(StaticFactKind.Structure, open.Kind);
        Assert.Same(link, open.Scope);
        Assert.Equal(StaticFactKind.Runtime, q.Get(StaticQueryKey.TargetWalk(link, StaticCycleCheck.Formation)).Kind);
    }

    /// <summary>
    /// Ordinary and direct receiver expansion are different questions: the head <c>S</c> of <c>P3 = S.Algorithm</c>
    /// is provided only by the root's <c>open Q</c>. The ordinary expansion follows that open into <c>Q.S = P3</c> and
    /// finds the pending return; the direct expansion (OD-C) never reads through an open, so it stops at the head.
    /// </summary>
    [Fact]
    public void OrdinaryAndDirectReceiverExpansionsReadTheirOwnHeadBinding()
    {
        foreach (var reversed in new[] { false, true })
        {
            var q = Model("open Q\nQ = { public S = P3 }\nP3 = S.Algorithm\nK = { open P3\n Z }\n0");
            var p3 = At(q, "P3");
            var requests = new[]
            {
                Open(p3, StaticQueryProjection.ReceiverExpansionStep),
                Open(p3, StaticQueryProjection.OpenReceiverExpansionStep),
                Open(p3, StaticQueryProjection.OpenStructure),
                StaticQueryKey.TargetWalk(p3, StaticCycleCheck.Formation),
            };
            foreach (var key in reversed ? requests.Reverse() : requests) q.Get(key);
            var ordinary = q.Get(Open(p3, StaticQueryProjection.ReceiverExpansionStep));
            Assert.Equal(StaticFactKind.ExpansionPending, ordinary.Kind);
            Assert.Same(At(q, "Q.S"), ordinary.Scope);
            Assert.Equal(StaticFactKind.Refused, q.Get(Open(p3, StaticQueryProjection.ReceiverExpansionCycle)).Kind);
            Assert.Equal(StaticFactKind.No, q.Get(Open(p3, StaticQueryProjection.OpenReceiverExpansionStep)).Kind);
            Assert.Equal(StaticFactKind.No, q.Get(Open(p3, StaticQueryProjection.OpenReceiverExpansionCycle)).Kind);
            // Ordinarily the pending return makes the link a runtime link; the open target is unresolved instead.
            Assert.Equal(StaticFactKind.Runtime, q.Get(StaticQueryKey.TargetWalk(p3, StaticCycleCheck.Formation)).Kind);
            var open = q.Get(Open(p3, StaticQueryProjection.OpenStructure));
            Assert.Equal(StaticFactKind.Missing, open.Kind);
            Assert.Same(p3, open.Scope);
        }
    }

    /// <summary>
    /// The refinement race: in the open stratum the guard and the direct row target must agree whatever query is
    /// demanded first. Every permutation of the open-stratum questions reaches the same final facts.
    /// </summary>
    [Theory]
    [InlineData("P5 = { open P3\n Z }\nP6 = P6\nP3 = P6.Algorithm\n0", "P3")]
    [InlineData("open Q\nQ = { public S = B.string }\nB = S\nK = { open A\n M }\nA = B.abs\n0", "A")]
    [InlineData("A = A.Algorithm\nB = { open C\n M }\nC = A.abs\n0", "C")]
    public void OpenStratumFactsDoNotDependOnQueryDemandOrder(string source, string target)
    {
        var projections = new[]
        {
            StaticQueryProjection.OpenStructure, StaticQueryProjection.OpenRowTarget, StaticQueryProjection.OpenReceiverExpansionCycle,
            StaticQueryProjection.OpenReceiverExpansionStep, StaticQueryProjection.Default, StaticQueryProjection.TargetCycle,
        };
        string? expected = null;
        foreach (var order in DeclarationOrderCases.Permutations(projections.Length))
        {
            var q = Model(source);
            var scope = At(q, target);
            foreach (var index in order) q.Get(Open(scope, projections[index]));
            var facts = string.Join(" | ", projections.Select(p => Describe(q, scope, q.Get(Open(scope, p)))));
            expected ??= facts;
            Assert.Equal(expected, facts);
        }
    }

    // Scopes are named by their top-level declaration, so facts compare across fresh models.
    private static string Describe(StaticStructureQueries q, StaticScopeKey self, StaticFact fact)
    {
        if (fact.Scope is null) return fact.Kind.ToString();
        if (ReferenceEquals(fact.Scope, self)) return fact.Kind + "@self";
        var named = q.BodyOf(q.Root).Properties.FirstOrDefault(p => ReferenceEquals(q.BodyIn(q.Root, p.Value), fact.Scope));
        return fact.Kind + "@" + (named?.Name ?? "other");
    }
}
