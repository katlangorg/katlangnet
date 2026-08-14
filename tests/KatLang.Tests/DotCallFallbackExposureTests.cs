namespace KatLang.Tests;

/// <summary>
/// Regression matrix for how the elaborated dot-edge lexical-fallback identity
/// participates in property dependency/exposure analysis.
///
/// The rule (see <c>AstHelpers.LexicalFallbackIsUnconditional</c> and the
/// <c>PropertyDependencyGraphBuilder</c> DotCall arm): the stored fallback is
/// an ordinary elaborated name expression and flows through the SAME
/// expression dependency walk as a written callee name — but only when the
/// edge's resolution facts make the fallback the unconditional selection
/// (every extension edge; an ordinary edge whose algorithm-position
/// capability makes structural resolution statically impossible). A CONDITIONAL fallback — a
/// receiver that may resolve structurally at runtime — contributes nothing,
/// so a structurally-resolving property is never made LocalOnly by an
/// unreached fallback that happens to name a parameter.
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
    public void ExtensionDot_CapturedParameters_LocalOnly_TildeDot()
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
    public void ExtensionDot_CapturedParameters_LocalOnly_DotTilde()
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
    public void ExtensionDot_CertainReceiverlessCapture_MarksLocalOnly()
        => AssertExposureAndResult(
            """
            Outer(t) = {
                P = 5~.t
                P
            }
            Outer({x+1})
            """,
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "6",
            "Outer", "P");

    // ── 5-6: structural winner vs extension bypass ──────────────────────────

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
    public void ExtensionDot_SameShape_BypassesStructuralAndMarksLocalOnly()
        // The extension edge is unconditional: the member is the captured
        // parameter, so P is LocalOnly and evaluates t(Obj-value) = 0+1.
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
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "1",
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
        // The visible root property `t` keeps the member's fallback identity
        // Resolve("t") for both edges, so neither captures the parameter:
        // ordinary resolves structurally (42), extension calls lexical t (99).
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
            "99",
            "Outer", "P");
    }

    // ── 9-11: opened, ambiguous, builtin fallbacks ──────────────────────────

    [Fact]
    public void OpenedCallableFallback_ResolvesLexically_Exported()
        => AssertExposureAndResult(
            """
            Lib = {
                public Inc(x) = x + 1
            }
            Outer = {
                open Lib
                P = 5~.Inc
                P
            }
            Outer
            """,
            PropertyExposure.Exported,
            "6",
            "Outer", "P");

    [Fact]
    public void AmbiguousOpenFallback_StaysExported_RuntimeReportsAmbiguity()
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
                P = 5~.Pick
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
    public void BuiltinFallback_ContributesNothing_Exported()
        => AssertExposureAndResult(
            """
            Outer = {
                P = (1, 2, 3)~.count
                P
            }
            Outer
            """,
            PropertyExposure.Exported,
            "3",
            "Outer", "P");

    // ── 12-15: chains, nested bodies, argument slots, capture receivers ─────

    [Fact]
    public void Chained_ExtensionThenOrdinaryString_MarksInnerCapture()
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
    public void Chained_TwoExtensionEdges_MarksCapturedMember()
        => AssertExposureAndResult(
            """
            Inc(x) = x + 1
            Outer(t) = {
                P = 5~.t~.Inc
                P
            }
            Outer({x*3})
            """,
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            "16",
            "Outer", "P");

    [Fact]
    public void FallbackInsideNestedPropertyScope_MarksBothLevels()
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
    public void FallbackInsideCallArguments_MarksCapture()
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
    public void DirectCall_And_ExtensionDot_AgreeOnClassificationAndResult()
    {
        var direct = ParseValidRoot(
            """
            Outer(a, t) = {
                P = t(a)
                P
            }
            Outer(1, {x+1})
            """);
        var extension = ParseValidRoot(
            """
            Outer(a, t) = {
                P = a~.t
                P
            }
            Outer(1, {x+1})
            """);
        Assert.Equal(
            FindProperty(direct, "Outer", "P").Exposure,
            FindProperty(extension, "Outer", "P").Exposure);
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
    public void Graph_ExtensionFallback_SeedsRequiredAncestorNames_LikeDirectCall()
    {
        static IReadOnlyList<string> RequiredNames(string source)
        {
            var outer = Assert.IsType<Algorithm.User>(
                Assert.Single(ParseValidRoot(source).Properties, property => property.Name == "Outer").Value);
            var graph = PropertyDependencyGraphBuilder.Build(outer);
            return graph[0].RequiredAncestorOwnedParameterNames;
        }

        var direct = RequiredNames(
            """
            Outer(a, t) = {
                P = t(a)
                P
            }
            Outer(1, {x+1})
            """);
        var extension = RequiredNames(
            """
            Outer(a, t) = {
                P = a~.t
                P
            }
            Outer(1, {x+1})
            """);

        Assert.Equal(["a", "t"], direct);
        Assert.Equal(direct, extension);
    }

    [Fact]
    public void Graph_SiblingResolveFallback_CreatesSummarySiblingEdge()
    {
        // An unconditional Resolve fallback participates like a written callee
        // name: `5~.t` beside a sibling property `t` records the summary
        // sibling edge the runtime resolution genuinely uses.
        var outer = Assert.IsType<Algorithm.User>(
            Assert.Single(ParseValidRoot(
                """
                Outer = {
                    t(x) = x + 10
                    P = 5~.t
                    P
                }
                Outer
                """).Properties, property => property.Name == "Outer").Value);
        var graph = PropertyDependencyGraphBuilder.Build(outer);
        Assert.True(graph.TryGetPropertyIndex("P", out var pIndex));
        Assert.True(graph.TryGetPropertyIndex("t", out var tIndex));
        Assert.Equal([tIndex], graph[pIndex].SummarySiblingDependencyIndices);
        // The fallback is a CALLED name: it never contributes to the sibling
        // evaluation-order channel, matching Call function position.
        Assert.Empty(graph[pIndex].SiblingDependencyIndices);
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
