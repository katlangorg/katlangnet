using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Regression matrix for how an ordinary dot edge's lexical fallback
/// participates in property dependency/exposure analysis.
///
/// The rule (see <c>AstHelpers.LexicalFallbackMayBeSelected</c> and the
/// <c>PropertyDependencyGraphBuilder</c> DotCall arm): the stored fallback is
/// an ordinary elaborated name expression and flows through the SAME
/// expression dependency walk as a written callee name whenever the fallback
/// MAY be the selected resolution at runtime. The deciding fact is the
/// detector's SCOPE-AWARE verdict stamped on the elaborated edge
/// (<c>Expr.DotCall.ElaboratedFallbackSelection</c>): a receiver that declares
/// the member (<see cref="LexicalFallbackSelection.Never"/>) never selects the
/// fallback, so a structurally-resolving property is never made LocalOnly by
/// an unreached fallback that happens to name a parameter; a receiver known
/// to lack it (<see cref="LexicalFallbackSelection.Always"/>: a literal, a
/// call result, a sibling whose value has no such member) always selects it,
/// so a parameter-naming fallback marks the capture exactly like the direct
/// call would; a runtime-valued receiver may. The scope-free raw shape
/// classification is only the fallback for unstamped (host-built) edges,
/// where an unresolved lexical reference stays Conditional and is treated as
/// MAY-selected — the safe direction.
///
/// This is the same MAY-selection question implicit parameter inference asks
/// (a fallback that CAN be selected must be representable in the inferred
/// signature), consumed from the same shared classification; the earlier
/// MUST-selection rule left a property whose value the runtime derives from a
/// parameter-naming fallback exported, which let structural navigation read a
/// dynamic binding through it and would have let the run-wide zero-argument
/// property cache of an exported binding serve one activation's value to
/// another (F3). The DEFINITE questions stay separate and still take no
/// fallback contribution: the closed explicit-parameter-list rule and the
/// conditional-branch full-input-specification rule
/// (<c>GraceDotCompositionTests.MayVsMust_*</c>).
///
/// Graced sources are a CONTROL family here: `a~.t` is the same ordinary
/// dot edge as `a.t`, so every graced case must classify exactly like its
/// ungraced twin — Grace changes only the enclosing signature's
/// parameter order.
///
/// Valid cases pin exposure and runtime results; the invalid literal collision
/// additionally pins recovery exposure and rejection before evaluation.
/// </summary>
public class DotCallFallbackExposureTests
{
    [Fact]
    public void OpenedReceiver_ExposureRemovalPropagatesThroughSeveralProviders()
    {
        const string source = """
            open Fallback
            Make(x) = {
                public Box = { g = 42
                    x }
                0
            }
            Middle(g) = {
                open Make
                public Box2 = { h = 42
                    Box.g }
                0
            }
            Fallback = { public Box = 5
                public Box2 = 7 }
            Outer(h) = {
                open Middle
                P = Box2.h
                P
            }
            Outer({x+1}), Outer({x*10})
            """;
        // Make.Box is removed first, then Middle.Box2 loses its structural proof,
        // then Outer.P loses its own proof. One refresh would still export P.
        AssertExposureAndResult(source, PropertyExposure.LocalOnlyCapturedAncestorParameters,
            $"8{Environment.NewLine}70", "Outer", "P");
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void OpenedReceiver_RemovedByExposure_UsesTheAncestorProvidersFallback(bool chained)
    {
        var source = $$"""
            open Fallback
            Make(x) = {
                public Data = {
                    {{(chained ? "Sub = { f = 42 }" : "f = 42")}}
                    x
                }
                0
            }
            Fallback = { public Data = {{(chained ? "{ Sub = 5 }" : "5")}} }
            Outer(f) = {
                open Make
                P = Data.{{(chained ? "Sub.f" : "f")}}
                P
            }
            Outer({x+1}), Outer({x*10})
            """;

        // Detection initially sees Make.Data's structural f. Exposure removes that
        // opened provider, so runtime selects Fallback.Data and Outer.f instead.
        AssertExposureAndResult(source, PropertyExposure.LocalOnlyCapturedAncestorParameters,
            $"6{Environment.NewLine}50", "Outer", "P");

        var parsed = SourceProvenance.ParseValid(source);
        var edge = Assert.IsType<Expr.DotCall>(Assert.Single(FindProperty(parsed.Root, "Outer", "P").Value.Output));
        Assert.Equal(LexicalFallbackSelection.Always, edge.ElaboratedFallbackSelection);
        var span = edge.MemberSpan!;
        var member = SemanticModelBuilder.Build(parsed.Parsed).FindResolutionAt(span.StartLineNumber, span.StartColumn);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, member!.Classification);
        Assert.Equal(OccurrenceKind.ExplicitParameterDefinition, member.ResolvedDeclaration!.Kind);

        var structural = SourceProvenance.ParseValid(source.Replace("Outer({x+1}), Outer({x*10})", "Outer.P"));
        var result = Evaluator.Run(new Expr.AlgorithmExpr(structural.Root));
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context) error = context.Inner;
        Assert.Equal("P", Assert.IsType<EvalError.LocalOnlyProperty>(error).PropertyName);

        // With no capture the nearer provider remains eligible: its structural f
        // really wins, and a same-named caller parameter must not hide P.
        AssertExposureAndResult(source.Replace("\n        x", "\n        0"),
            PropertyExposure.Exported, $"42{Environment.NewLine}42", "Outer", "P");
    }

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
    public void SiblingNameReceiver_CertainMiss_FallbackParameterMarksLocalOnly_InBothSpellings()
    {
        // A sibling NAME receiver is unresolvable by the scope-free view, but the
        // detector resolved it: `Five`'s algorithm declares no member `t`, so the
        // stamped verdict is Always — the runtime takes the Param fallback and P's
        // value depends on `t`. The earlier policy left P exported here (a
        // conditional fallback was treated as unselected), which let a run-wide
        // cached P serve a second activation of Outer; both spellings now classify
        // the capture identically.
        AssertExposureAndResult(
            """
            Outer(t) = {
                Five = 5
                P = Five.t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
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
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "6",
            "Outer", "P");

        // The classification is what keeps two activations apart: each call of
        // Outer reads its own `t` through P, and structural navigation into the
        // parameterized owner is refused as local-only instead of reading a
        // dynamic binding.
        var twoActivations = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            """
            Outer(t) = {
                Five = 5
                P = Five.t
                P
            }
            Outer({x+1}), Outer({x*10})
            """));
        Assert.Equal($"6{Environment.NewLine}50", twoActivations.ToDisplayString());
    }

    // ── 5-6: structural winner, both spellings ─────────────────────────────

    [Fact]
    public void OrdinaryDot_HiddenParamName_StructuralWinnerStaysExported()
    {
        // The outer-scope receiver declares the member, so structural resolution
        // definitively wins; the Never-selected Param fallback is excluded and
        // P keeps exported structural/open access.
        AssertExposureAndResult(
            """
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

        // The exported classification is load-bearing: structural access on
        // the parameterized owner works precisely because P stays Exported.
        var structuralAccess = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            """
            Obj = {
                public t = 42
                0
            }
            Outer(t) = {
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

    [Fact]
    public void LiteralReceiver_MemberHitExcludesFallback_MemberMissIncludesIt()
    {
        // A literal algorithm receiver is statically decidable on the node:
        // member present → structural certainty → Exported; member absent →
        // the fallback is unconditional → LocalOnly.
        const string collision = """
            Outer(t) = {
                P = {public t = 42
                0}.t
                P
            }
            Outer({x+1})
            """;
        // This structural-hit shape is now invalid source: the literal's t property
        // conflicts with Outer.t. Recovery must still exclude the unreachable fallback.
        var recovery = SourceProvenance.ParseAllowingDiagnostics(collision);
        Assert.Equal(DiagnosticCode.ParameterPropertyCollision, Assert.Single(recovery.Diagnostics).Code);
        Assert.Equal(PropertyExposure.Exported, FindProperty(recovery.Root, "Outer", "P").Exposure);
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(collision));
        AssertExposureAndResult(collision.Replace("Outer(t)", "Outer(q)"),
            PropertyExposure.Exported, "42", "Outer", "P");

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
    public void FartherProperty_DoesNotOverrideCapturedFallback_StaysExported()
    {
        // The captured parameter beats the root property `t` in the stored
        // Param("t") fallback in both spellings. Neither charges the ancestor
        // parameter to exposure, and both resolve structurally on the member-bearing
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
        // The sibling receiver `v` declares no member `t`, so the stamped verdict is
        // Always and the parameter-naming fallback marks the capture through the
        // transparent argument slot — in both spellings.
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
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
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
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
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
            Obj = {
                public t = 42
                0
            }
            Outer(t) = {
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
        // `Obj.t` (structural winner) classifies like referencing the outer-scope
        // object directly: no captured-parameter requirement in either form.
        var structural = ParseValidRoot(
            """
            Obj = {
                public t = 42
                0
            }
            Outer(t) = {
                P = Obj.t
                P
            }
            Outer({x+1})
            """);
        var reference = ParseValidRoot(
            """
            Obj = {
                public t = 42
                0
            }
            Outer(t) = {
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

        // A direct call requires BOTH names, and so does the dot edge: its
        // receiver is a runtime parameter, so the parameter-named fallback MAY
        // be selected and is charged like the written callee. (The earlier rule
        // charged only CERTAIN selections and left the edge requiring just the
        // receiver.) The graced source belongs to the DOT family, not the call
        // family, and classifies identically.
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
        Assert.Equal(["a", "t"], ordinaryDot);
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
            Assert.Equal(LexicalFallbackSelection.Always, dotCall.ElaboratedFallbackSelection);
            Assert.True(dotCall.LexicalFallbackMayBeSelected(), $"expected a selectable fallback for receiver {receiver}");

            var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
            Assert.Equal("77", success.ToDisplayString());
        }

        // A structural winner: the detector resolved the sibling receiver and found
        // the member, so the stamped verdict is Never and the fallback is not
        // selectable (the scope-free raw view alone would only say Conditional).
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
        Assert.Equal(LexicalFallbackSelection.Never, structuralDot.ElaboratedFallbackSelection);
        Assert.False(structuralDot.LexicalFallbackMayBeSelected());
        var structuralRun = Assert.IsType<RunResult.Success>(KatLangEngine.Run(structuralSource));
        Assert.Equal("42", structuralRun.ToDisplayString());

        // The ordinary-dot string intrinsic pre-empts the fallback everywhere.
        var stringSource = "string(x) = 0\n5.string";
        var stringRoot = SourceProvenance.ParseValid(stringSource).Root;
        var stringDot = Assert.IsType<Expr.DotCall>(stringRoot.Output[^1]);
        Assert.Equal(LexicalFallbackSelection.Never, stringDot.ElaboratedFallbackSelection);
        Assert.False(stringDot.LexicalFallbackMayBeSelected());
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

        // The exposure predicate is the MAY projection of the STAMPED scope-aware
        // verdict, which the detector derives from the same shared classification
        // with its elaborated scope: it agrees with the raw shape view wherever
        // that view is decided, and decides the lexical-name receiver the raw view
        // cannot (`V` is a known algorithm without `t`: Always, selectable).
        foreach (var source in new[] { "5.t", "{public u = 1\n0}.t", "5.string" })
        {
            var edge = LastEdge(source);
            Assert.Equal(SelectionOf(edge), edge.ElaboratedFallbackSelection);
            Assert.Equal(
                SelectionOf(edge) != LexicalFallbackSelection.Never,
                edge.LexicalFallbackMayBeSelected());
        }

        var siblingEdge = LastEdge("V = 5\nV.t");
        Assert.Equal(LexicalFallbackSelection.Conditional, SelectionOf(siblingEdge));
        Assert.Equal(LexicalFallbackSelection.Always, siblingEdge.ElaboratedFallbackSelection);
        Assert.True(siblingEdge.LexicalFallbackMayBeSelected());

        // An unstamped edge (a host-built tree) falls back to the raw shape view,
        // where the undecided lexical receiver is treated as MAY-selected.
        var unstamped = new Expr.DotCall(new Expr.Resolve("V"), "t");
        Assert.Null(unstamped.ElaboratedFallbackSelection);
        Assert.True(unstamped.LexicalFallbackMayBeSelected());
        Assert.False(new Expr.DotCall(new Expr.Num(5m), "string").LexicalFallbackMayBeSelected());
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
