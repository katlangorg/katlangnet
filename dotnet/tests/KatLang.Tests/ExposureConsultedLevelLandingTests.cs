using System.Security.Cryptography;
using System.Text;

namespace KatLang.Tests;

using Mode = PropertyExposureResolver.SettlementShareMode;

/// <summary>
/// THE CONSULTED LEVEL IS A LANDING (<c>docs/design/language-rules/evaluator-and-hosting.md</c>, SETTLEMENT SHARE; C# exposure
/// implementation only, no Lean rule). When the site's chain holds an open target's consulted level, the walk is settled AT that
/// level (owner decision Q2). Finding the level is therefore a site lookup that lands at its depth, exactly as finding an owner
/// there does. Before November 28 2026 it landed nowhere. A settlement keyed ABOVE the consulted level, such as a navigated
/// member's seed anchored at a shared ancestor, took the walk from a reader inside the level and was kept as answering every
/// site. It then answered a reader outside the level, which checks the walk from a shallower shared level, where the consulted
/// level's owners are on no level of its chain. That reader published those requirements with owner depth -1: a capture with no
/// reachable owning activation, which the evaluator refuses wherever the member is read. This breaks THE INVARIANT of owner
/// decision Q1 that <see cref="ExposureCensus.CensusRunner.UnsuppliedRequirements"/> checks. The unshared settlement charges
/// that reader nothing of the consulted level, because such a check can never pass from there (Q1). The healthy result omits
/// the requirement entirely, and a same-named parameter of the reader's own owner keeps its own, reachable capture.
/// <para>The off-chain decision's archived differential found the defect on the fuzz input <c>g44_03532.kat</c>
/// (<c>docs/design/offchain-exposure-owner-decision-brief-2026-11.md</c>): production and the exact-metadata S1 variant published
/// four <c>z@-1</c> captures that the unshared settlement omits. Neither off-chain policy of that brief is adopted here. An owner
/// lookup that finds no owner still raises no landing (THE OFF-CHAIN GAP).</para>
/// </summary>
public sealed class ExposureConsultedLevelLandingTests
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private static T InMode<T>(Mode mode, Func<T> work)
    {
        var previous = PropertyExposureResolver.SettlementShareModeForTesting.Value;
        PropertyExposureResolver.SettlementShareModeForTesting.Value = mode;
        try { return work(); }
        finally { PropertyExposureResolver.SettlementShareModeForTesting.Value = previous; }
    }

    private sealed record Published(Diagnostic[] Diagnostics, string Metadata, Algorithm.User Root, FrontEndTraversalObservations Observations);

    /// <summary>
    /// The archived comparison's front-end settings: <see cref="Parser.ParseObserved"/> with default options apart from a
    /// source-processing token. The diagnostics are kept, as a recovery tree's metadata is published with them.
    /// </summary>
    private static Published Parse(string source, Mode mode)
        => InMode(mode, () =>
        {
            var observations = new FrontEndTraversalObservations();
            using var cancellation = new CancellationTokenSource();
            var parsed = Parser.ParseObserved(source, new RunOptions { SourceProcessingCancellationToken = cancellation.Token }, observations);
            return new Published([.. parsed.Diagnostics],
                ExposureSettlementFrameChargeTests.Metadata(parsed.Root), parsed.Root, observations);
        });

    /// <summary>
    /// Every share mode publishes the unshared settlement's diagnostics and metadata, and no declaration of the tree, those
    /// written inside expressions included, publishes a requirement that no level of its chain can supply.
    /// </summary>
    private static Published AssertEveryModeIsTheUnsharedSettlement(string source)
    {
        var unshared = Parse(source, Mode.Unshared);
        var production = Parse(source, Mode.Footprint);
        Assert.Empty(ExposureCensus.CensusRunner.UnsuppliedRequirements(unshared.Root));
        foreach (var published in new[] { production, Parse(source, Mode.ExactBoundOwners) })
        {
            Assert.Empty(ExposureCensus.CensusRunner.UnsuppliedRequirements(published.Root));
            Assert.Equal(unshared.Diagnostics, published.Diagnostics);
            Assert.Equal(unshared.Metadata, published.Metadata);
        }

        return production;
    }

    private static Property Member(Algorithm root, params string[] path) => ExposureOpenChainComplexityTests.Member(root, path);

    private static void AssertRequires(Property property, params (string Name, int Depth)[] requirements)
        => ExposureOpenChainComplexityTests.AssertRequires(property, requirements);

    private static async Task<RunResult[]> BothEngines(string source)
    {
        SourceProvenance.ParseValid(source);
        // RunAsync with a sync-only configuration delegates to the sync evaluator; an unused async operation routes the
        // run through the async twin.
        var operations = HostOperations.Create(HostOperation.CreateAsync("UnusedConsultedLevelProbe",
            static (_, _) => throw new InvalidOperationException("The route marker must never execute.")));
        return [KatLangEngine.Run(source), await KatLangEngine.RunAsync(source),
            await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations })];
    }

    private static string Outcome(RunResult result)
    {
        if (result is RunResult.Success success)
            return success.ToDisplayString();
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, error.Code);
        var inner = error.Source;
        while (inner is EvalError.WithContext context)
            inner = context.Inner;
        return "refused at " + Assert.IsType<EvalError.LocalOnlyProperty>(inner).PropertyName;
    }

    // ── The fuzz input ──────────────────────────────────────────────────────

    /// <summary>
    /// The archived input <c>g44_03532.kat</c> verbatim (SHA-256 <c>B554439651DBF4ACA5F6055EB9061C1BF68D854903E030D6B20B17246F736E3B</c>
    /// with LF lines and a final LF). It needs no module input.
    /// </summary>
    internal const string FuzzInput = """
        Y(q, z) = C
        P(x) = {
          M = {
            public C(p, x) = x
            public Y = {
              L = {
                open M.N, P.C.L
                public Q(x, z) = x
                public N = Q - M
                public Y(z) = B.Y(z)
                public M = M
                N(X) - x - P + B * C - x * M * x
              }
              C(L.X)
            }
            Q
          }
          public Y(p) = {
            open Y.A
            public X = { C.N.B } - C + p - P - Y.X
            public P = {
              open P.C
              public N(z) = L
              public M = { { M } }
              P - N + 0 - 1 + M - M
            }
            public C(y, q) = {
              C(q, z) = {
                public B(z) = y - P.P.Y * P + L + z
                X.A - M.A
              }
              public N = {
                A = { { { y } } } - N.B.Y(L) - P - P.C * L
                public L = M - P(Q) * p
                public X = { 8 }
                public Q(z) = Q(Y)
                p - 3 + 4
              }
              X
            }
            X.Y
          }
          public N(x, q) = P.P.P
          L(z, q) = {
            public C = C + N + x * x * z + q + Y(Q.C(Y))
            x
          }
          N
        }
        L = {
          open Q
          public B = L.X
          X(z, x) = {
            Q = {
              open X.X
              public P(z) = {
                open B
                public P = P
                public C = L(L) - M.L.Y - A.P * P.M
                public Y = C
                Q(N) * A(9)
              }
              X + L + C.L - B(X(L)) * Y.A - L.L.Y
            }
            N
          }
          Y(y) = { y }
          P.Y.Y - N + { C.L } * 2
        }
        B(y, z) = {
          public X = {
            P = {
              open C.C
              public Q(p) = {
                B = y - Q + 6 + Y.Q.L(Q) + 6
                public Y(p) = A + y * C + M({ y }) + y
                public A(p, y) = P + z
                Q = 1
                { P.Q }
              }
              P.N - A(z) * { M(N) } * z + A.X(X.B)
            }
            y
          }
          Q(q) = {
            public B(p) = {
              open C.B, C.B
              B = X.A
              public P(x, z) = Y * L.M + B.A.M
              M = M
              Q.N
            }
            L(z) = {
              open Y, X.C
              M = {
                X = C.M
                public N = 7
                B = L * P.X.M * Y
                public M = N.B.Y(A)
                Q
              }
              N(p) = z
              public X = {
                public C = P.Q - 4 + M(A(P)) + N + Q.C
                public A = A * z + q * { C }
                C.B
              }
              C
            }
            public P(p, z) = {
              public X = {
                X = B * y
                public C = M.Q
                public B = Y.C - A.A * y * B.N.A - p - { q } * P
                Y.C.L + N.C - A
              }
              N(q) = q - Y({ M }) + Q - P * Y.C(X(X.B)) - q * Q.L.M
              A + 5 * Y * P(C) * { { y } } - C.C
            }
            { A }
          }
          L
        }
        N

        """;

    // The input's diagnostics, in reporting order: recovery publishes the metadata below WITH them.
    private static readonly string[] FuzzInputDiagnostics =
    [
        "UndeclaredIdentifier [1:11, 1:12)",
        "UndeclaredIdentifier [30:11, 30:12)",
        "UndeclaredIdentifier [76:31, 76:32)",
        "UndeclaredIdentifier [76:35, 76:36)",
        "UndeclaredIdentifier [89:36, 89:37)",
        "UndeclaredIdentifier [108:7, 108:8)",
        "UndeclaredIdentifier [118:7, 118:8)",
        "UndeclaredIdentifier [118:21, 118:22)",
        "UndeclaredIdentifier [117:39, 117:40)",
        "UnforwardableParameter [23:21, 23:22)",
        "UnforwardableParameter [39:7, 39:8)",
        "UnforwardableParameter [48:3, 48:4)",
        "ParameterPropertyCollision [59:16, 59:17)",
        "ParameterPropertyCollision [8:16, 8:17)",
        "ParameterPropertyCollision [77:16, 77:17)",
        "UnresolvedOpenTarget [51:8, 51:9)",
        "UnresolvedOpenTarget [55:12, 55:15)",
        "IllegalInOpen [57:14, 57:15)",
        "UnresolvedOpenTarget [7:14, 7:17)",
        "UnresolvedOpenTarget [7:19, 7:24)",
        "UnresolvedOpenTarget [19:10, 19:13)",
        "UnresolvedOpenTarget [22:12, 22:15)",
        "UnresolvedOpenTarget [73:12, 73:15)",
        "UnresolvedOpenTarget [87:12, 87:15)",
        "UnresolvedOpenTarget [87:17, 87:20)",
        "IllegalInOpen [94:12, 94:13)",
        "IllegalInOpen [94:15, 94:18)",
    ];

    /// <summary>
    /// The archived input. <c>B.Q.L(z)</c> holds <c>open Y, X.C</c>, and its member <c>M.B</c> reads <c>P.X.M</c>. That navigates
    /// into its sibling <c>P(p, z)</c>, whose seed reads <c>Q.L.M</c> back, and <c>Q.L</c>'s seed holds the walk of <c>X.C</c>.
    /// From <c>M.B</c> the walk is settled at <c>L</c>, its consulted level, and charges <c>L</c>'s <c>z</c>. <c>P</c>'s own
    /// members read the same anchored seed, where <c>L</c> is on no level of their chain. Production published that <c>z</c>
    /// on <c>P.X</c>, <c>P.X.X</c>, <c>P.X.B</c> and <c>P.N</c> with owner depth -1, next to their own <c>z</c> of <c>P</c>. Now
    /// they keep only their own, as the unshared settlement does, and the reader inside <c>L</c> keeps <c>L</c>'s.
    /// </summary>
    [Fact]
    public void TheFuzzInput_PublishesEveryCaptureAtAReachableOwner_InEveryShareMode()
    {
        Assert.Equal("B554439651DBF4ACA5F6055EB9061C1BF68D854903E030D6B20B17246F736E3B",
            Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(FuzzInput))));
        var published = AssertEveryModeIsTheUnsharedSettlement(FuzzInput);
        Assert.Equal(FuzzInputDiagnostics, published.Diagnostics.Select(diagnostic => $"{diagnostic.Code} {diagnostic.Span}"));

        var root = published.Root;
        AssertRequires(Member(root, "B", "Q", "P", "X"), ("p", 0), ("q", 1), ("y", 2), ("z", 0));
        AssertRequires(Member(root, "B", "Q", "P", "X", "X"), ("A", 0), ("p", 1), ("q", 2), ("y", 3), ("z", 1));
        AssertRequires(Member(root, "B", "Q", "P", "X", "B"), ("A", 0), ("p", 1), ("q", 2), ("y", 3), ("z", 1));
        AssertRequires(Member(root, "B", "Q", "P", "N"), ("p", 0), ("q", 1), ("y", 2), ("z", 0));
        // The reader inside the consulted level: L's own z, one level up from M, is a real requirement.
        AssertRequires(Member(root, "B", "Q", "L", "M", "B"), ("q", 2), ("y", 3), ("z", 1));
        AssertRequires(Member(root, "B", "Q", "L", "N"), ("z", 0));
    }

    /// <summary>
    /// The input minimized line by line while production kept a negative depth, with its braces closed. It keeps that shape
    /// and seven recovery diagnostics, among them the unresolved <c>open Y</c> and the illegal <c>open X.C</c>, whose walk is
    /// still settled. <c>P.X</c> and its member <c>N</c> keep <c>P</c>'s <c>z</c> at its own depth, and the reader
    /// <c>L.B</c> keeps <c>L</c>'s.
    /// </summary>
    [Fact]
    public void TheMinimizedInput_ChargesAReaderOutsideTheConsultedLevelNothingOfIt()
    {
        const string source = """
            Q(q) = {
              public B(p) = {
              }
              L(z) = {
                open Y, X.C
                B = L * P.X.M * Y
                public X = {
                  public C = P.Q - 4 + M(A(P)) + N + Q.C
                  public A = A * z + q * { C }
                }
              }
              public P(p, z) = {
                public X = {
                  Y.C.L + N.C - A
                  N(q) = q - Y({ M }) + Q - P * Y.C(X(X.B)) - q * Q.L.M
                }
              }
            }

            """;
        string[] diagnostics =
        [
            "ExplicitParametersRequireOutput [1:3, 1:4)",
            "ExplicitParametersRequireOutput [2:12, 2:13)",
            "ExplicitParametersRequireOutput [4:5, 4:6)",
            "ExplicitParametersRequireOutput [12:12, 12:13)",
            "UndeclaredIdentifier [15:59, 15:60)",
            "UnresolvedOpenTarget [5:10, 5:11)",
            "IllegalInOpen [5:13, 5:16)",
        ];
        var published = AssertEveryModeIsTheUnsharedSettlement(source);
        Assert.Equal(diagnostics, published.Diagnostics.Select(diagnostic => $"{diagnostic.Code} {diagnostic.Span}"));

        var root = published.Root;
        AssertRequires(Member(root, "Q", "P", "X"), ("p", 0), ("q", 1), ("z", 0));
        AssertRequires(Member(root, "Q", "P", "X", "N"), ("C", 0), ("Y", 0), ("p", 1), ("q", 2), ("z", 1));
        AssertRequires(Member(root, "Q", "L", "B"), ("q", 1), ("z", 0));
        AssertRequires(Member(root, "Q", "L", "X", "A"), ("q", 2), ("z", 1));
    }

    // ── A clean program of the same shape ───────────────────────────────────

    /// <summary>
    /// The shape without a diagnostic. <c>L(z)</c> opens <c>T.U</c>, whose value reads <c>z</c> and <c>q</c>. Its reader
    /// <c>B</c> navigates into the sibling <c>P</c>, whose <c>X</c> passes <c>Q.L</c> to <c>Apply</c>, so <c>L</c>'s own seed,
    /// with the walk, is settled at the root from both. <paramref name="row"/> is <c>Q</c>'s output row.
    /// </summary>
    private static string Clean(string row) => $$"""
        Apply(f) = 0
        Q(q) = {
          L(z) = {
            open T.U
            T = {
              public U = {
                public C = 1
                z + q
              }
            }
            public B = P.X
            B + C
          }
          P(p) = {
            public X = Q.L.Apply
            X
          }
          {{row}}
        }
        Q(5)

        """;

    /// <summary>
    /// The healthy classification. <c>P.X</c> requires <c>Q</c>'s <c>q</c> only. <c>L</c>'s <c>z</c> is on no level of its
    /// chain, so the walk's check can never pass from there and charges nothing (Q1), and <c>P</c> has no <c>z</c> of its own.
    /// The accepted controls keep real ownership. <c>L.B</c> reads the walk from inside <c>L</c> and requires <c>L</c>'s
    /// <c>z</c>, and the walk's member <c>T.U</c> requires both.
    /// </summary>
    [Fact]
    public void AWalkSettledAtItsConsultedLevel_AnswersNoReaderOutsideIt()
    {
        var published = AssertEveryModeIsTheUnsharedSettlement(Clean("P.X"));
        Assert.Empty(published.Diagnostics);
        var root = published.Root;
        AssertRequires(Member(root, "Q", "P", "X"), ("q", 1));
        AssertRequires(Member(root, "Q", "P"), ("q", 0));
        AssertRequires(Member(root, "Q", "L", "B"), ("q", 1), ("z", 0));
        AssertRequires(Member(root, "Q", "L", "T", "U"), ("q", 2), ("z", 1));
        AssertRequires(Member(root, "Q", "L", "T", "U", "C"));
    }

    /// <summary>
    /// What the capture position decides at run time, on both engines. Read inside <c>Q</c> and outside <c>L</c>, <c>P.X</c> is
    /// accessible: production refused it with <c>LocalOnlyProperty(X)</c> because of the unreachable <c>z@-1</c>, and so it
    /// refused <c>L(3)</c>, whose <c>B</c> reads <c>P.X</c> inside <c>L</c>'s activation. The real requirement still refuses:
    /// <c>L.B</c> read without an activation of <c>L</c> is <c>LocalOnlyProperty(B)</c>.
    /// </summary>
    [Theory]
    [InlineData("P.X", "0")]
    [InlineData("L(3)", "1")]
    [InlineData("P.X + L(3)", "1")]
    [InlineData("L.B", "refused at B")]
    public async Task TheReachableCapture_DecidesEveryRead_OnBothEngines(string row, string expected)
    {
        foreach (var result in await BothEngines(Clean(row)))
            Assert.Equal(expected, Outcome(result));
    }

    // ── Work, cancellation and retention ────────────────────────────────────

    /// <summary>
    /// Production still reuses settlements within the share's capacity and charges fewer frames for these inputs than
    /// the unshared settlement. Every frame costs one unit on the static ledger (<c>ExposureSettlementFrameChargeTests</c>).
    /// </summary>
    [Fact]
    public void TheInputs_ReuseBoundedSettlements_AndChargeFewerFramesThanUnshared()
    {
        foreach (var source in new[] { Clean("P.X + L(3)"), FuzzInput })
        {
            var production = Parse(source, Mode.Footprint).Observations;
            var exact = Parse(source, Mode.ExactBoundOwners).Observations;
            var unshared = Parse(source, Mode.Unshared).Observations;
            Assert.True(production.SettlementShareHits > 0);
            Assert.True(production.SettlementShareStores > 0);
            Assert.InRange(production.SettlementShareRetainedWeight, 1L, PropertyExposureResolver.SettlementShare.DefaultCapacity);
            Assert.InRange(production.RequiredAncestorSettlementFrames, 1L, unshared.RequiredAncestorSettlementFrames - 1);
            Assert.InRange(exact.RequiredAncestorSettlementFrames, 1L, unshared.RequiredAncestorSettlementFrames);
            Assert.Equal(0L, unshared.SettlementShareHits);
        }
    }

    /// <summary>
    /// Cancellation at the first, middle or last settlement checkpoint surfaces with its token. A fresh parse does the
    /// same work and publishes the same reachable metadata as the uninterrupted parse.
    /// </summary>
    [Fact]
    public void Cancellation_AtSettlementCheckpoints_AllowsAFreshParseWithReachableCaptures()
    {
        var source = Clean("P.X + L(3)");
        var expected = Parse(source, Mode.Footprint);
        var frames = expected.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ExposureSettlementFrame);
        Assert.True(frames > 2);
        foreach (var ordinal in new[] { 1, frames / 2, frames })
        {
            using var cancellation = new CancellationTokenSource();
            var observations = new FrontEndTraversalObservations
            {
                CheckpointReached = (kind, reached) =>
                {
                    if (kind == FrontEndCancellationCheckpoint.ExposureSettlementFrame && reached == ordinal)
                        cancellation.Cancel();
                },
            };
            var error = Assert.Throws<OperationCanceledException>(() => Parser.ParseObserved(
                source, new RunOptions { SourceProcessingCancellationToken = cancellation.Token }, observations));
            Assert.Equal(cancellation.Token, error.CancellationToken);
            Assert.Equal(ordinal, observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ExposureSettlementFrame));

            var again = Parse(source, Mode.Footprint);
            Assert.Equal(expected.Diagnostics, again.Diagnostics);
            Assert.Equal(expected.Metadata, again.Metadata);
            Assert.Empty(ExposureCensus.CensusRunner.UnsuppliedRequirements(again.Root));
            Assert.Equal(expected.Observations.RequiredAncestorSettlementFrames, again.Observations.RequiredAncestorSettlementFrames);
        }
    }
}
