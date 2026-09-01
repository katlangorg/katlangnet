namespace KatLang.Tests;

/// <summary>
/// Regression matrix for how an ordinary dot edge's lexical fallback
/// participates in property dependency/exposure analysis.
///
/// The rule (see <c>AstHelpers.LexicalFallbackIsUnconditional</c> and the
/// <c>PropertyDependencyGraphBuilder</c> DotCall arm): the stored fallback is
/// an ordinary elaborated name expression and flows through the SAME
/// expression dependency walk as a written callee name — but only when the
/// edge's resolution facts make the fallback the unconditional selection
/// (<see cref="LexicalFallbackSelection.Always"/>: the receiver's
/// algorithm-position capability makes structural resolution statically
/// impossible). A CONDITIONAL fallback — a receiver that may resolve
/// structurally at runtime, including every lexical NAME receiver this
/// scope-free view cannot resolve — contributes nothing, so a
/// structurally-resolving property is never made LocalOnly by an unreached
/// fallback that happens to name a parameter.
///
/// This is deliberately the MUST-selection question, distinct from implicit
/// parameter inference's MAY-selection question (a fallback that CAN be
/// selected must be representable in the inferred signature). The two are
/// pinned apart by <c>GraceDotCompositionTests.MayVsMust_*</c>.
///
/// Graced sources are a CONTROL family here: `a~.t` is the same ordinary
/// dot edge as `a.t`, so every graced case must classify exactly like its
/// ungraced twin — Grace changes only the enclosing signature's
/// parameter order.
///
/// Every case pins BOTH the exposure classification and the runtime
/// result/error, so classification changes can never silently diverge from
/// evaluation semantics.
/// </summary>
public class DotCallFallbackExposureTests
{
    private static Algorithm ParseValidRoot(string source)
        => SourceProvenance.ParseValid(source).Root;

    private static Property FindProperty(Algorithm root, params string[] path)
    {
        var current = root;
        Property? found = null;
        foreach (var segment in path)
        {
            found = Assert.Single(current.Properties, property => property.Name == segment);
            current = found.Value;
        }

        return found!;
    }

    private static void AssertExposureAndResult(
        string source,
        PropertyExposure expectedExposure,
        string expectedDisplay,
        params string[] propertyPath)
    {
        var root = ParseValidRoot(source);
        Assert.Equal(expectedExposure, FindProperty(root, propertyPath).Exposure);

        var run = KatLangEngine.Run(source);
        var success = Assert.IsType<RunResult.Success>(run);
        Assert.Equal(expectedDisplay, success.ToDisplayString());
    }

    // ── 1-4: the captured-parameter equivalence family ──────────────────────

    [Fact]
    public void DirectCall_CapturedParameters_LocalOnly()
        => AssertExposureAndResult(
            """
            Outer(a, t) = {
                P = t(a)
                P
            }
            Outer(1, {x+1})
            """,
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "2",
            "Outer", "P");

    [Fact]
    public void PostfixGraceDot_CapturedParameters_LocalOnly()
        => AssertExposureAndResult(
            """
            Outer(a, t) = {
                P = a~.t
                P
            }
            Outer(1, {x+1})
            """,
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "2",
            "Outer", "P");

    [Fact]
    public void PrefixMemberGraceDot_CapturedParameters_LocalOnly()
        => AssertExposureAndResult(
            """
            Outer(a, t) = {
                P = a.~t
                P
            }
            Outer(1, {x+1})
            """,
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "2",
            "Outer", "P");

    [Fact]
    public void OrdinaryDot_CertainMissReceiver_FallbackParameterMarksLocalOnly()
        // A numeric receiver can never resolve structurally, so the ordinary
        // edge's Param fallback is the unconditional selection and marks the
        // capture exactly like `t(5)`.
        => AssertExposureAndResult(
            """
            Outer(t) = {
                P = 5.t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "6",
            "Outer", "P");

    [Fact]
    public void SiblingNameReceiver_ConditionalFallback_StaysExported_InBothSpellings()
    {
        // A NAME receiver is not resolvable by this scope-free view, so the
        // fallback stays conditional and is not charged — even though the
        // runtime does take it here. That imprecision is the long-standing
        // exposure policy (a conditional fallback is treated as unselected),
        // and both spellings inherit it identically.
        AssertExposureAndResult(
            """
            Outer(t) = {
                Five = 5
                P = Five.t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.Exported,
            "6",
            "Outer", "P");

        AssertExposureAndResult(
            """
            Outer(t) = {
                Five = 5
                P = Five~.t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.Exported,
            "6",
            "Outer", "P");
    }

    // ── 5-6: structural winner, both spellings ─────────────────────────────

    [Fact]
    public void OrdinaryDot_HiddenParamName_StructuralWinnerStaysExported()
    {
        // The sibling receiver declares the member, so structural resolution
        // may (and does) win; the CONDITIONAL Param fallback is excluded and
        // P keeps exported structural/open access.
        AssertExposureAndResult(
            """
            Outer(t) = {
                Obj = {
                    public t = 42
                    0
                }
                P = Obj.t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.Exported,
            "42",
            "Outer", "P");

        // The exported classification is load-bearing: structural access on
        // the parameterized owner works precisely because P stays Exported.
        var structuralAccess = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            """
            Outer(t) = {
                Obj = {
                    public t = 42
                    0
                }
                public P = Obj.t
                P
            }
            Outer.P
            """));
        Assert.Equal("42", structuralAccess.ToDisplayString());
    }

    [Fact]
    public void GracedDot_SameShape_ClassifiesExactlyLikeTheOrdinaryEdge()
        // The marker does not bypass structural lookup, so this is the same
        // structural winner as the ungraced twin above: Exported, and 42.
        => AssertExposureAndResult(
            """
            Outer(t) = {
                Obj = {
                    public t = 42
                    0
                }
                P = Obj~.t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.Exported,
            "42",
            "Outer", "P");

    [Fact]
    public void LiteralReceiver_MemberHitExcludesFallback_MemberMissIncludesIt()
    {
        // A literal algorithm receiver is statically decidable on the node:
        // member present → structural certainty → Exported; member absent →
        // the fallback is unconditional → LocalOnly.
        AssertExposureAndResult(
            """
            Outer(t) = {
                P = {public t = 42
                0}.t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.Exported,
            "42",
            "Outer", "P");

        AssertExposureAndResult(
            """
            Outer(t) = {
                P = {public u = 1
                0}.t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "1",
            "Outer", "P");
    }

    // ── 7: local parameter vs captured parameter ────────────────────────────

    [Fact]
    public void LocalParameters_OwnedHere_StayExported()
        // a and t are P's OWN parameters: the fallback walk strips self-owned
        // names exactly like every other expression walk.
        => AssertExposureAndResult(
            """
            Outer = {
                P(a, t) = a.t
                P(3, {x*2})
            }
            Outer
            """,
            PropertyExposure.Exported,
            "6",
            "Outer", "P");

    // ── 8: same-name visible property shadowing ─────────────────────────────

    [Fact]
    public void VisiblePropertyShadow_KeepsResolveFallback_Exported()
    {
        // The visible root property `t` keeps the edge's fallback as
        // Resolve("t") in both spellings. Neither captures the ancestor
        // parameter, and both resolve structurally on the member-bearing
        // receiver (42) — the marker only reorders inferred parameters.
        AssertExposureAndResult(
            """
            t(x) = 99
            Obj = {
                public t = 42
                0
            }
            Outer(t) = {
                P = Obj.t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.Exported,
            "42",
            "Outer", "P");

        AssertExposureAndResult(
            """
            t(x) = 99
            Obj = {
                public t = 42
                0
            }
            Outer(t) = {
                P = Obj~.t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.Exported,
            "42",
            "Outer", "P");
    }

    // ── 9-11: opened, ambiguous, and builtin fallback callees ───────────────

    [Fact]
    public void GracedEdgeFallback_ResolvesThroughOpen_Exported()
        => AssertExposureAndResult(
            """
            Lib = {
                public Inc(x) = x + 1
            }
            Outer = {
                open Lib
                v = 5
                P = v~.Inc
                P
            }
            Outer
            """,
            PropertyExposure.Exported,
            "6",
            "Outer", "P");

    [Fact]
    public void GracedEdgeFallback_AmbiguousOpenStaysExported_RuntimeReportsAmbiguity()
    {
        // Static analysis records only a visible-name edge; the ambiguity is
        // the runtime lookup's verdict, exactly as for a plain call.
        var source =
            """
            A = {
                public Pick(x) = 1
            }
            B = {
                public Pick(x) = 2
            }
            Outer = {
                open A, B
                v = 5
                P = v~.Pick
                P
            }
            Outer
            """;
        var root = ParseValidRoot(source);
        Assert.Equal(PropertyExposure.Exported, FindProperty(root, "Outer", "P").Exposure);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        Assert.Contains(failure.Errors, error => error.Message.Contains("ambiguous", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void GracedEdgeBuiltinFallback_ContributesNothing_Exported()
        => AssertExposureAndResult(
            """
            Outer = {
                S = 1, 2, 3
                P = S~.count
                P
            }
            Outer
            """,
            PropertyExposure.Exported,
            "3",
            "Outer", "P");

    // ── 12-15: chains, nested bodies, argument slots, capture receivers ─────

    [Fact]
    public void Chained_GracedThenOrdinaryString_MarksInnerCapture()
        => AssertExposureAndResult(
            """
            Outer(a, t) = {
                P = a~.t.string
                P
            }
            Outer(1, {x+1})
            """,
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "2",
            "Outer", "P");

    [Fact]
    public void GracedEdgeInsideCallSlot_ClassifiesLikeTheOrdinaryEdge()
    {
        // (Postfix Grace on a chained dot result rejects under the one-name law, so the
        // two-step pipeline is written as an ordinary call around the edge.)
        // The name receiver keeps the fallback conditional in both spellings.
        AssertExposureAndResult(
            """
            Inc(x) = x + 1
            Outer(t) = {
                v = 5
                P = Inc(v.t)
                P
            }
            Outer({x*3})
            """,
            PropertyExposure.Exported,
            "16",
            "Outer", "P");

        AssertExposureAndResult(
            """
            Inc(x) = x + 1
            Outer(t) = {
                v = 5
                P = Inc(v~.t)
                P
            }
            Outer({x*3})
            """,
            PropertyExposure.Exported,
            "16",
            "Outer", "P");
    }

    [Fact]
    public void GracedEdgeInsideNestedPropertyScope_MarksBothLevels()
        => AssertExposureAndResult(
            """
            Outer(a, t) = {
                P = {
                    Q = a~.t
                    Q
                }
                P
            }
            Outer(1, {x+1})
            """,
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "2",
            "Outer", "P");

    [Fact]
    public void GracedEdgeInsideCallArguments_MarksCapture()
    {
        var source =
            """
            Outer(a, t) = {
                P = count((a~.t, 9))
                P
            }
            Outer(1, {x+1})
            """;
        var root = ParseValidRoot(source);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            FindProperty(root, "Outer", "P").Exposure);

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal("2", success.ToDisplayString());
    }

    [Fact]
    public void CaptureReceiver_SuppressesStructuralIdentity_FallbackMarks()
        // A capture receiver never exposes structural members, so the ordinary
        // edge's Param fallback is unconditional and marks the capture.
        => AssertExposureAndResult(
            """
            Outer(t) = {
                Obj = {
                    public t = 42
                    0
                }
                P = (Obj).t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "1",
            "Outer", "P");

    // ── 16-17: direct-call equivalences ─────────────────────────────────────

    [Fact]
    public void DirectCall_And_GracedDot_AgreeOnClassificationAndResult()
    {
        var direct = ParseValidRoot(
            """
            Outer(a, t) = {
                P = t(a)
                P
            }
            Outer(1, {x+1})
            """);
        var graced = ParseValidRoot(
            """
            Outer(a, t) = {
                P = a~.t
                P
            }
            Outer(1, {x+1})
            """);
        Assert.Equal(
            FindProperty(direct, "Outer", "P").Exposure,
            FindProperty(graced, "Outer", "P").Exposure);
    }

    [Fact]
    public void DirectStructuralReference_And_OrdinaryDot_AgreeWhenStructuralWins()
    {
        // `Obj.t` (structural winner) classifies like referencing the sibling
        // object directly: no captured-parameter requirement in either form.
        var structural = ParseValidRoot(
            """
            Outer(t) = {
                Obj = {
                    public t = 42
                    0
                }
                P = Obj.t
                P
            }
            Outer({x+1})
            """);
        var reference = ParseValidRoot(
            """
            Outer(t) = {
                Obj = {
                    public t = 42
                    0
                }
                P = Obj
                P
            }
            Outer({x+1})
            """);
        Assert.Equal(PropertyExposure.Exported, FindProperty(structural, "Outer", "P").Exposure);
        Assert.Equal(PropertyExposure.Exported, FindProperty(reference, "Outer", "P").Exposure);
    }

    // ── Dependency-graph facts: fallback flows through the ordinary walk ────

    [Fact]
    public void Graph_GracedEdge_SeedsRequiredAncestorNames_LikeTheOrdinaryEdge()
    {
        static IReadOnlyList<string> RequiredNames(string source)
        {
            var outer = Assert.IsType<Algorithm.User>(
                Assert.Single(ParseValidRoot(source).Properties, property => property.Name == "Outer").Value);
            var graph = PropertyDependencyGraphBuilder.BuildSummaries(outer);
            return graph[0].RequiredAncestorOwnedParameterNames;
        }

        // A direct call requires BOTH names; the dot edge requires only the
        // receiver, because its parameter-named fallback is conditional. The
        // graced source belongs to the DOT family, not the call family.
        var direct = RequiredNames(
            """
            Outer(a, t) = {
                P = t(a)
                P
            }
            Outer(1, {x+1})
            """);
        var ordinaryDot = RequiredNames(
            """
            Outer(a, t) = {
                P = a.t
                P
            }
            Outer(1, {x+1})
            """);
        var graced = RequiredNames(
            """
            Outer(a, t) = {
                P = a~.t
                P
            }
            Outer(1, {x+1})
            """);

        Assert.Equal(["a", "t"], direct);
        Assert.Equal(["a"], ordinaryDot);
        Assert.Equal(ordinaryDot, graced);
    }

    [Fact]
    public void Graph_UnconditionalSiblingFallback_CreatesSummarySiblingEdge()
    {
        // An UNCONDITIONAL fallback participates like a written callee name:
        // the certain-miss numeric receiver's `.t` beside a sibling property
        // `t` records the summary sibling edge the runtime genuinely uses.
        var root = ParseValidRoot(
            """
            Outer = {
                t(x) = x + 10
                P = 5.t
                P
            }
            Outer
            """);
        var outer = Assert.IsType<Algorithm.User>(
            Assert.Single(root.Properties, property => property.Name == "Outer").Value);
        var graph = PropertyDependencyGraphBuilder.BuildSummaries(outer);
        Assert.True(graph.TryGetPropertyIndex("P", out var pIndex));
        Assert.True(graph.TryGetPropertyIndex("t", out var tIndex));
        Assert.Equal([tIndex], graph[pIndex].SummarySiblingDependencyIndices);
        // The fallback is a CALLED name: it never contributes to the sibling
        // evaluation-order channel, matching Call function position.
        var orderGraph = PropertyDependencyGraphBuilder.BuildDependencyOrder(outer);
        Assert.Empty(orderGraph[pIndex].SiblingDependencyIndices);
    }

    // ── The static certainty predicate mirrors evaluator dispatch ───────────

    [Fact]
    public void CertaintyPredicate_AgreesWithEvaluatorDispatch()
    {
        // Certain-miss receiver shapes: the runtime MUST take the fallback.
        // The lexical marker Chosen(x) = 77 observes fallback selection.
        string[] certainMissReceivers =
        [
            "5",
            "'text'",
            "(1, 2)",
            "[1, 2]",
            "(1 + 2)",
            "(1, 2):0",
            "Id(3)",
        ];
        foreach (var receiver in certainMissReceivers)
        {
            var source = $"Id(x) = x\nChosen(x) = 77\n{receiver}.Chosen";
            var root = SourceProvenance.ParseValid(source).Root;
            var dotCall = Assert.IsType<Expr.DotCall>(root.Output[^1]);
            Assert.True(dotCall.LexicalFallbackIsUnconditional(), $"expected unconditional for receiver {receiver}");

            var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
            Assert.Equal("77", success.ToDisplayString());
        }

        // Structurally-possible shapes: the predicate must stay conditional.
        var structuralSource =
            """
            Chosen(x) = 77
            Obj = {
                public Chosen = 42
                0
            }
            Obj.Chosen
            """;
        var structuralRoot = SourceProvenance.ParseValid(structuralSource).Root;
        var structuralDot = Assert.IsType<Expr.DotCall>(structuralRoot.Output[^1]);
        Assert.False(structuralDot.LexicalFallbackIsUnconditional());
        var structuralRun = Assert.IsType<RunResult.Success>(KatLangEngine.Run(structuralSource));
        Assert.Equal("42", structuralRun.ToDisplayString());

        // The ordinary-dot string intrinsic pre-empts the fallback everywhere.
        var stringSource = "string(x) = 0\n5.string";
        var stringRoot = SourceProvenance.ParseValid(stringSource).Root;
        var stringDot = Assert.IsType<Expr.DotCall>(stringRoot.Output[^1]);
        Assert.False(stringDot.LexicalFallbackIsUnconditional());
        var stringRun = Assert.IsType<RunResult.Success>(KatLangEngine.Run(stringSource));
        Assert.Equal("5", stringRun.ToDisplayString());
    }

    [Fact]
    public void SelectionClassification_IsTheOneSharedFact_AndUnconditionalIsItsAlwaysProjection()
    {
        static Expr.DotCall LastEdge(string source)
            => Assert.IsType<Expr.DotCall>(SourceProvenance.ParseValid(source).Root.Output[^1]);

        static LexicalFallbackSelection SelectionOf(Expr.DotCall edge)
            => edge.GetLexicalFallbackSelection(
                edge.Target.UnwrapGraceOperand().GetStaticStructuralMemberProvider());

        // Never: the receiver's statically known algorithm declares the
        // member, or the dot-only string intrinsic pre-empts both channels.
        var memberHit = LastEdge("Obj = {\n    public t = 42\n    0\n}\n{public t = 1\n0}.t");
        Assert.Equal(LexicalFallbackSelection.Never, SelectionOf(memberHit));
        Assert.Equal(LexicalFallbackSelection.Never, SelectionOf(LastEdge("5.string")));

        // A property declared inside a conditional branch is a structural
        // local-only error at runtime, not a lexical miss, so it is also Never.
        var conditionalBranchBody = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("t", new Algorithm.User(null, [], [], [], [new Expr.Num(1m)]))],
            Output: [new Expr.Num(0m)]);
        var conditionalReceiver = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.Bind("x"), conditionalBranchBody)]);
        var conditionalMember = new Expr.DotCall(
            new Expr.AlgorithmExpr(conditionalReceiver),
            "t");
        Assert.Equal(LexicalFallbackSelection.Never, SelectionOf(conditionalMember));

        // Always: no structural channel can exist on the receiver.
        Assert.Equal(LexicalFallbackSelection.Always, SelectionOf(LastEdge("5.t")));
        Assert.Equal(LexicalFallbackSelection.Always, SelectionOf(LastEdge("{public u = 1\n0}.t")));

        // Conditional: runtime-valued receivers (parameters, and lexical names
        // this scope-free view cannot resolve).
        Assert.Equal(LexicalFallbackSelection.Conditional, SelectionOf(LastEdge("V = 5\nV.t")));
        Assert.Equal(
            LexicalFallbackSelection.Conditional,
            SelectionOf(Assert.IsType<Expr.DotCall>(
                SourceProvenance.ParseValid("K(a) = a.t\nK(1)").Root.Properties[0].Value.Output[0])));

        // The exposure predicate is exactly the Always projection.
        foreach (var source in new[] { "5.t", "{public u = 1\n0}.t", "5.string", "V = 5\nV.t" })
        {
            var edge = LastEdge(source);
            Assert.Equal(
                SelectionOf(edge) == LexicalFallbackSelection.Always,
                edge.LexicalFallbackIsUnconditional());
        }
    }

    [Fact]
    public void StructuralMemberProviderClassification_IsExhaustiveAndFailLoud()
    {
        var leaf = new Expr.Num(1m);
        var samples = new Dictionary<Type, Expr>
        {
            [typeof(Expr.Param)] = new Expr.Param("x"),
            [typeof(Expr.Num)] = leaf,
            [typeof(Expr.StringLiteral)] = new Expr.StringLiteral("x"),
            [typeof(Expr.Unary)] = new Expr.Unary(UnaryOp.Minus, leaf),
            [typeof(Expr.Binary)] = new Expr.Binary(BinaryOp.Add, leaf, leaf),
            [typeof(Expr.Index)] = new Expr.Index(leaf, leaf),
            [typeof(Expr.SequenceConstruct)] = new Expr.SequenceConstruct(leaf, leaf),
            [typeof(Expr.EmptySequence)] = new Expr.EmptySequence(0),
            [typeof(Expr.SequenceSpread)] = new Expr.SequenceSpread(leaf),
            [typeof(Expr.ListLiteral)] = new Expr.ListLiteral(OutputBundle.Empty),
            [typeof(Expr.Resolve)] = new Expr.Resolve("x"),
            [typeof(Expr.DotCall)] = new Expr.DotCall(leaf, "F"),
            [typeof(Expr.Grace)] = new Expr.Grace(new Expr.Resolve("x"), 1),
            [typeof(Expr.AlgorithmExpr)] = new Expr.AlgorithmExpr(new Algorithm.Builtin(BuiltinId.@count)),
            [typeof(Expr.Capture)] = new Expr.Capture(OutputBundle.Empty),
            [typeof(Expr.Call)] = new Expr.Call(new Expr.Resolve("F"), OutputBundle.Empty),
            [typeof(Expr.NativeCall)] = new Expr.NativeCall("F", []),
        };

        var declaredVariants = typeof(Expr)
            .GetNestedTypes(System.Reflection.BindingFlags.Public)
            .Where(type => typeof(Expr).IsAssignableFrom(type))
            .ToHashSet();
        Assert.True(
            declaredVariants.SetEquals(samples.Keys),
            $"Static structural-member samples drifted. Declared: {string.Join(", ", declaredVariants.Select(t => t.Name).Order())}; sampled: {string.Join(", ", samples.Keys.Select(t => t.Name).Order())}");

        foreach (var (type, sample) in samples)
        {
            var provider = sample.GetStaticStructuralMemberProvider();
            var expected = type == typeof(Expr.Resolve)
                ? StaticStructuralMemberProviderKind.LexicalReference
                : type == typeof(Expr.Param)
                    ? StaticStructuralMemberProviderKind.RuntimeParameter
                    : type == typeof(Expr.AlgorithmExpr)
                        ? StaticStructuralMemberProviderKind.KnownAlgorithm
                        : StaticStructuralMemberProviderKind.DefinitelyAbsent;
            Assert.Equal(expected, provider.Kind);
        }
    }
}
