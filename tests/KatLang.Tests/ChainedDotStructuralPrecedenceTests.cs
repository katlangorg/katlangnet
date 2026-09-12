using KatLang.Semantics;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// The property-first / extension-fallback law of dot syntax holds at EVERY
/// level of a chained dot expression. For <c>receiver.Q</c>: if the receiver
/// exposes an accessible (exported) structural member <c>Q</c>, that member is
/// selected; only otherwise is <c>Q</c> resolved lexically and applied as the
/// extension call <c>Q(receiver)</c>. A receiver that is itself an argumentless
/// dot edge (<c>Lib.Sub</c> in <c>Lib.Sub.Q</c>) is therefore navigated
/// structurally (<c>Evaluator.ResolveDotReceiver</c>, Lean
/// <c>resolveDotReceiver</c>) instead of being lifted to a memberless dot
/// result — which is what used to turn <c>Lib.Sub.Q</c> into <c>Q(Lib.Sub)</c>
/// whenever a same-named extension was visible, and into a phantom implicit
/// parameter otherwise.
///
/// <para>The static twin of that resolution
/// (<see cref="AstHelpers.ResolveStaticStructuralMemberProvider"/>) drives
/// parameter detection, the editor's semantic model, and dependency analysis,
/// so runtime and front-end agree on every chain shape pinned here.</para>
/// </summary>
public class ChainedDotStructuralPrecedenceTests
{
    private const string NestedLibrary =
        """
        Lib = {
            public Sub = {
                public Q = 1
            }
        }
        """;

    private const string LocalOnlyIntermediate =
        """
        G(x) = {
            public Sub = {
                public Q = 1
                x
            }
            0
        }
        """;

    private const string ConditionalIntermediate =
        """
        C(0) = {
            public Q = {
                public R = 1
            }
            0
        }
        C(1) = 2
        """;

    // ── Helpers ──────────────────────────────────────────────────────────────

    private static string Display(string source)
    {
        var run = KatLangEngine.Run(source);
        var success = Assert.IsType<RunResult.Success>(run);
        return success.ToDisplayString().Replace("\r\n", "\n", StringComparison.Ordinal);
    }

    private static EvalError InnermostErrorOf(string source)
    {
        var result = EvalFull(source);
        Assert.True(result.IsError, "Expected an evaluation error but the program evaluated successfully.");
        return Innermost(result.Error);
    }

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

    private static IReadOnlyList<string> ParamsOf(string source, string propertyName = "K")
    {
        var root = SourceProvenance.ParseValid(source).Root;
        return Assert.Single(root.Properties, p => p.Name == propertyName).Value.Params;
    }

    private static SemanticModel Model(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));
        return SemanticModelBuilder.Build(parsed);
    }

    private static IdentifierResolution ResolutionAt(SemanticModel model, int line, int column)
        => Assert.IsType<IdentifierResolution>(model.FindResolutionAt(line, column));

    private static void AssertSpanStartsAt(SourceSpan? span, int line, int column)
    {
        Assert.NotNull(span);
        Assert.Equal((line, column), (span.StartLineNumber, span.StartColumn));
    }

    private static Expr.DotCall LastEdge(string source)
        => Assert.IsType<Expr.DotCall>(SourceProvenance.ParseValid(source).Root.Output[^1]);

    /// <summary>
    /// The sync generic strategy and the async twin must agree on the outcome
    /// AND on the operational counters for every chain shape (the twin is a
    /// sync-delegating mirror; a receiver-resolution change that reached only
    /// one family would show up here first).
    /// </summary>
    private static async Task AssertTwinPathMatches(string source)
    {
        var ast = AsyncEvaluationHarness.Ast(source);
        var (sync, syncBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (twin, twinBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(
                ast,
                zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(twin));
        Assert.Equal(syncBudget.ConsumedSteps, twinBudget.ConsumedSteps);
        Assert.Equal(syncBudget.PeakDepth, twinBudget.PeakDepth);
    }

    // ── 1. A structural member beats a same-named visible extension ─────────

    [Fact]
    public void StructuralMember_BeatsRootVisibleExtension()
    {
        var source = NestedLibrary + "\n\nQ(x) = 99\n\nLib.Sub.Q";

        Assert.Equal("1", Display(source));
        AssertEvalCounted(source, 1, Atom(1));
    }

    [Fact]
    public void StructuralMember_BeatsNestedVisibleExtension()
    {
        // The extension is declared in the enclosing algorithm of the access
        // site — nearer than the root — and still loses to the receiver's member.
        var source = NestedLibrary + "\n\nOuter = {\n    Q(x) = 99\n    Lib.Sub.Q\n}\n\nOuter";

        Assert.Equal("1", Display(source));
    }

    [Fact]
    public void StructuralMember_BeatsSameNamedParameterOfTheAccessingAlgorithm()
    {
        // `Q` is a parameter of K (the fallback identity elaborates to Param(Q)),
        // but the receiver's own member still wins — exactly as for `Obj.t`.
        var structural = NestedLibrary + "\n\nK(Q) = Lib.Sub.Q\n\nK({x + 1})";
        Assert.Equal("1", Display(structural));

        // Without the member, the parameter channel is reached with the chained
        // receiver's VALUE injected — the ordinary extension law for parameters.
        var fallback = "Lib = {\n    public Sub = {\n        20\n    }\n}\n\nK(Q) = Lib.Sub.Q\n\nK({x * 2})";
        Assert.Equal("40", Display(fallback));
    }

    [Fact]
    public void StructuralMember_BeatsExtension_ThroughEveryLevelOfADeeperChain()
    {
        var source =
            """
            A = {
                public B = {
                    public C = {
                        public D = 7
                    }
                }
            }
            B(x) = 91
            C(x) = 92
            D(x) = 93

            A.B.C.D
            """;

        Assert.Equal("7", Display(source));
    }

    // ── 2-3. Extension fallback still applies, and composes along a chain ───

    [Fact]
    public void ExtensionFallback_StillAppliesOnAMemberlessReceiver()
        => Assert.Equal("4", Display("Q(x) = x + 1\n3.Q"));

    [Fact]
    public void ChainedExtensionFallback_ComposesLikeNestedCalls()
    {
        var source =
            """
            A = x + 7
            B = x * 5

            3.A.B
            B(A(3))
            B(3.A)
            """;

        Assert.Equal("50\n50\n50", Display(source));
    }

    [Theory]
    [InlineData("Q(x) = x * 10\n[1, 2, 3].count.Q", "30")]
    [InlineData("Q(x) = x > 3\nMath.Pi.Q", "1")]
    [InlineData("Q(x) = x + 1\n'ab'.count.Q", "2")]
    [InlineData("Q(x) = x + 1\n(1, 2).count.Q", "3")]
    public void ValueReceivers_KeepFallingBackAlongTheChain(string source, string expected)
        => Assert.Equal(expected, Display(source));

    // ── 4. Intermediate structural access keeps its existing behavior ───────

    [Fact]
    public void IntermediateMember_KeepsItsExistingValueBehavior()
    {
        // A container without output is still not a value ...
        AssertEvalFailsWithMissingOutput(NestedLibrary + "\n\nLib.Sub");

        // ... while a container with output is, and its member is reachable
        // through it without evaluating that output.
        var withOutput = "Lib = {\n    public Sub = {\n        public Q = 1\n        5\n    }\n}\n\nLib.Sub\nLib.Sub.Q";
        Assert.Equal("5\n1", Display(withOutput));
    }

    [Fact]
    public void ParameterizedContainer_NavigatesExactlyLikeTheFirstLevel()
    {
        // `F.Q` already navigated a parameterized container at level one; the
        // chained edge is identity navigation too, so no call is required.
        var source =
            """
            G(x) = {
                public Sub = {
                    public Q = 1
                }
                x
            }
            Q(v) = 99

            G.Sub.Q
            """;

        Assert.Equal("1", Display(source));
    }

    // ── 5-6. Nested structural chains, private members, argument-bearing edges

    [Fact]
    public void NestedStructuralChain_TraversesAccessibleMembers()
    {
        var source =
            """
            A = {
                public B = {
                    public C = {
                        public D = 7
                    }
                }
            }

            A.B.C.D
            """;

        Assert.Equal("7", Display(source));
        AssertEvalCounted(source, 1, Atom(7));
    }

    [Fact]
    public void PrivateIntermediateMember_IsReachableStructurally()
    {
        // Structural dot access ignores `public` (but not exposure), at every level.
        var source = "Lib = {\n    Sub = {\n        public Q = 1\n    }\n}\n\nQ(x) = 99\n\nLib.Sub.Q";
        Assert.Equal("1", Display(source));

        var privateLeaf = "Lib = {\n    public Sub = {\n        Q = 1\n    }\n}\n\nQ(x) = 99\n\nLib.Sub.Q";
        Assert.Equal("1", Display(privateLeaf));
    }

    [Fact]
    public void ArgumentBearingEdge_OnAChainedReceiver_CallsTheStructuralMember()
    {
        var source = "Lib = {\n    public Sub = {\n        public Q(y) = y + 1\n    }\n}\n\nQ(x) = 99\n\nLib.Sub.Q(5)";
        Assert.Equal("6", Display(source));
    }

    [Fact]
    public void ExplicitEmptyArguments_MakeTheReceiverAValue()
    {
        // `Lib.Sub()` is a CALL — a value — so `.Q` on it is the extension call
        // over that value, never structural navigation.
        var source = "Lib = {\n    public Sub = {\n        public Q = 1\n        5\n    }\n}\n\nQ(x) = x * 10\n\nLib.Sub().Q";
        Assert.Equal("50", Display(source));
    }

    [Fact]
    public void ParenthesizedChainedReceiver_IsRedundantGroupingOfTheChain()
    {
        // Parentheses around a single dot expression are ordinary redundant
        // grouping (the parser keeps a capture layer only around a bare name,
        // the `(Obj).V` case), so `(Lib.Sub).Q` IS `Lib.Sub.Q` and navigates.
        var source = "Lib = {\n    public Sub = {\n        public Q = 1\n        5\n    }\n}\n\nQ(x) = x * 10\n\n(Lib.Sub).Q";
        var edge = LastEdge(source);
        Assert.IsType<Expr.DotCall>(edge.Target);
        Assert.Equal("1", Display(source));
    }

    // ── 8. Accessibility: the established one-level rule holds at every level

    [Fact]
    public void LocalOnlyIntermediateMember_IsAnError_NeverAFallback()
    {
        // The established rule for a declared but local-only member is a hard
        // LocalOnlyProperty error even when a same-named extension is visible.
        var chained = InnermostErrorOf(LocalOnlyIntermediate + "\nQ(v) = 99\n\nG.Sub.Q");
        var localOnly = Assert.IsType<EvalError.LocalOnlyProperty>(chained);
        Assert.Equal(("G", "Sub", PropertyExposure.LocalOnlyCapturedAncestorParameters),
            (localOnly.ObjectDesc, localOnly.PropertyName, localOnly.Exposure));

        // Exactly the error that evaluating the intermediate edge itself reports.
        Assert.Equal(localOnly with { Span = null }, InnermostErrorOf(LocalOnlyIntermediate + "\nG.Sub"));
    }

    [Fact]
    public void ConditionalIntermediateMember_IsAnError_NeverAFallback()
    {
        var chained = InnermostErrorOf(ConditionalIntermediate + "\nR(v) = 99\n\nC.Q.R");
        var localOnly = Assert.IsType<EvalError.LocalOnlyProperty>(chained);
        Assert.Equal(("C", "Q", PropertyExposure.LocalOnlyConditionalAlgorithm),
            (localOnly.ObjectDesc, localOnly.PropertyName, localOnly.Exposure));
    }

    [Theory]
    [InlineData(LocalOnlyIntermediate, "G.Sub", "\n    .Q")]
    [InlineData(LocalOnlyIntermediate, "G.Sub", "\n    .Q.R")]
    [InlineData(LocalOnlyIntermediate, "G.Sub", "\n    .filter({x > 0}).count")]
    [InlineData(ConditionalIntermediate, "C.Q", "\n    .R")]
    [InlineData(ConditionalIntermediate, "C.Q", "\n    .R.S")]
    [InlineData(ConditionalIntermediate, "C.Q", "\n    .filter({x > 0}).count")]
    public async Task InaccessibleIntermediate_PreservesTheFailingEdgeSpan(
        string declarations, string receiver, string tail)
    {
        // Keep every tail name bound so the root's unresolved-input check
        // cannot pre-empt the structural failure under test.
        var prefix = declarations + "\nR(v) = 99\nS(v) = 99\n";
        var direct = EvalFull(prefix + receiver);
        Assert.True(direct.IsError);
        var expected = Assert.IsType<EvalError.LocalOnlyProperty>(Innermost(direct.Error));
        Assert.NotNull(direct.Error.Span);

        var ast = AsyncEvaluationHarness.Ast(prefix + receiver + tail);
        var plain = Evaluator.Run(ast);
        Assert.True(plain.IsError);
        Assert.Equal(direct.Error.Span, plain.Error.Span);

        foreach (var optimized in new[] { false, true })
        {
            var (counted, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: optimized);
            Assert.True(counted.IsError);
            var error = Assert.IsType<EvalError.LocalOnlyProperty>(Innermost(counted.Error));
            Assert.Equal((expected.ObjectDesc, expected.PropertyName, expected.Exposure),
                (error.ObjectDesc, error.PropertyName, error.Exposure));
            Assert.Equal(direct.Error.Span, counted.Error.Span);
        }

        var (twin, _) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            ast, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));
        Assert.True(twin.IsError);
        Assert.IsType<EvalError.LocalOnlyProperty>(Innermost(twin.Error));
        Assert.Equal(direct.Error.Span, twin.Error.Span);
    }

    [Fact]
    public void LocalOnlyLeafMember_IsAnError_AtTheEndOfAChain()
    {
        var source =
            """
            G(x) = {
                public Sub = {
                    public Q = x
                }
                0
            }
            Q(v) = 99

            G.Sub.Q
            """;

        var localOnly = Assert.IsType<EvalError.LocalOnlyProperty>(InnermostErrorOf(source));
        Assert.Equal(("G.Sub", "Q"), (localOnly.ObjectDesc, localOnly.PropertyName));
    }

    // ── The `.string` intrinsic over chained receivers ───────────────────────

    [Fact]
    public void StringIntrinsic_OnAChainedStructuralReceiver_ReadsTheMemberValue()
        => Assert.Equal("7", Display("Lib = {\n    public Sub = {\n        7\n    }\n}\n\nLib.Sub.string"));

    [Fact]
    public void StringIntrinsic_OnAChainedExtensionResult_ReadsTheCallValue()
        => Assert.Equal("10", Display("A = x + 7\n3.A.string"));

    [Fact]
    public void StringIntrinsic_OnAChainedStructuralReceiver_IsDepthBoundedLikeTheFirstLevel()
    {
        // A structurally navigated chain receiver is a name-resolved property
        // that can re-enter its own body; it takes the same depth-charged funnel
        // as a bare `Sub.string`, so self-reference is a deterministic depth
        // verdict rather than a native stack backstop.
        var chained = EvalFull("Lib = {\n    public Sub = {\n        Lib.Sub.string\n    }\n}\n\nLib.Sub.string");
        Assert.True(chained.IsError);
        Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(chained.Error));

        var firstLevel = EvalFull("Sub = {\n    Sub.string\n}\n\nSub.string");
        Assert.True(firstLevel.IsError);
        Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(firstLevel.Error));
    }

    // ── Open paths and the free-call/dot-call law are unchanged ─────────────

    [Fact]
    public void OpenPath_StillChainsStructurally()
        => Assert.Equal("1", Display(NestedLibrary + "\n\nR = {\n    open Lib.Sub\n    Q\n}\n\nR"));

    [Fact]
    public void FreeCallDotCallLaw_HoldsWhenStructuralLookupDoesNotApply()
    {
        var source =
            """
            Lib = {
                public Sub = {
                    5
                }
            }
            F(a, b) = a * 100 + b

            Lib.Sub.F(2)
            F(Lib.Sub, 2)
            """;

        Assert.Equal("502\n502", Display(source));
    }

    // ── Sync / counted / async twin / optimizer parity ───────────────────────

    [Theory]
    [InlineData(NestedLibrary + "\n\nQ(x) = 99\n\nLib.Sub.Q")]
    [InlineData("A = x + 7\nB = x * 5\n\n3.A.B")]
    [InlineData("A = {\n    public B = {\n        public C = {\n            public D = 7\n        }\n    }\n}\n\nA.B.C.D")]
    [InlineData("Lib = {\n    public Sub = {\n        7\n    }\n}\n\nLib.Sub.string")]
    [InlineData(LocalOnlyIntermediate + "\nQ(v) = 99\n\nG.Sub.Q")]
    [InlineData("Lib = {\n    public Sub = {\n        public Q = 1\n        5\n    }\n}\n\nQ(x) = x * 10\n\n(Lib.Sub).Q")]
    public async Task AsyncTwinPath_MatchesTheSyncGenericStrategy(string source)
        => await AssertTwinPathMatches(source);

    [Fact]
    public void SequencePipelineOptimizer_SeesTheSameStructuralShadowing()
    {
        // `Sub` declares `filter`: the fused filter/count pipeline must not be
        // recognized over a structurally shadowed member — both strategies
        // report the structural member's arity error.
        var shadowed = "Lib = {\n    public Sub = {\n        public filter = 5\n        1, 5, 9\n    }\n}\nBig(x) = x > 3\n\nLib.Sub.filter(Big).count";
        var generic = EvalFull(shadowed, enableLoopOptimization: true, enableSequencePipelineOptimization: false);
        var fused = EvalFull(shadowed, enableLoopOptimization: true, enableSequencePipelineOptimization: true);
        Assert.True(generic.IsError);
        Assert.True(fused.IsError);
        Assert.IsType<EvalError.ArityMismatch>(Innermost(generic.Error));
        Assert.IsType<EvalError.ArityMismatch>(Innermost(fused.Error));

        // Without the shadow, the chained receiver's VALUE feeds the fused
        // pipeline exactly like the generic dotted sequence-builtin view.
        var open = "Lib = {\n    public Sub = {\n        1, 5, 9\n    }\n}\nBig(x) = x > 3\n\nLib.Sub.filter(Big).count";
        Assert.Equal("2", Display(open));
        var genericOpen = EvalFull(open, enableLoopOptimization: true, enableSequencePipelineOptimization: false);
        var fusedOpen = EvalFull(open, enableLoopOptimization: true, enableSequencePipelineOptimization: true);
        Assert.False(genericOpen.IsError);
        Assert.False(fusedOpen.IsError);
        Assert.Equal(genericOpen.Value, fusedOpen.Value, Result.ValueComparer);
    }

    // ── Front end: signature inference agrees with the runtime ──────────────

    [Fact]
    public void SignatureInference_NeverInfersAStructurallyOwnedChainedMember()
    {
        Assert.Empty(ParamsOf(NestedLibrary + "\n\nK = Lib.Sub.Q\n\nK"));
        Assert.Empty(ParamsOf(NestedLibrary + "\n\nQ(x) = 99\nK = Lib.Sub.Q\n\nK"));
    }

    [Fact]
    public void SignatureInference_StillInfersAChainedMemberTheReceiverLacks()
    {
        // `Sub` is statically known WITHOUT `R`: the fallback is unconditionally
        // selected and its callable participates, exactly as for `Obj.r`.
        Assert.Equal(new[] { "R" }, ParamsOf(NestedLibrary + "\n\nK = Lib.Sub.R\n\nK({x + 1})"));

        // A miss at an INNER level makes every outer edge a value edge: both
        // names participate, in source order.
        Assert.Equal(new[] { "Missing", "Q" }, ParamsOf(NestedLibrary + "\n\nK = Lib.Missing.Q\n\nK({x}, {x})"));
    }

    [Fact]
    public void StaticClassification_MirrorsRuntimeReceiverResolution()
    {
        var root = SourceProvenance.ParseValid(NestedLibrary + "\n\nLib.Sub.Q").Root;
        var lib = Assert.Single(root.Properties, p => p.Name == "Lib").Value;
        StaticStructuralMemberProvider Resolve(string name)
            => name == "Lib"
                ? new(StaticStructuralMemberProviderKind.KnownAlgorithm, lib)
                : new(StaticStructuralMemberProviderKind.LexicalReference);

        // The chained receiver `Lib.Sub` IS Sub's algorithm for a scope-aware consumer.
        var edge = LastEdge(NestedLibrary + "\n\nLib.Sub.Q");
        var receiver = edge.Target.ResolveStaticStructuralMemberProvider(Resolve);
        Assert.Equal(StaticStructuralMemberProviderKind.KnownAlgorithm, receiver.Kind);
        Assert.Same(Assert.Single(lib.Properties, p => p.Name == "Sub").Value, receiver.Algorithm);
        Assert.Equal(LexicalFallbackSelection.Never, edge.GetLexicalFallbackSelection(receiver));

        // A missing leaf on that known receiver: the fallback is unconditional.
        var missingLeaf = LastEdge(NestedLibrary + "\n\nLib.Sub.R");
        Assert.Equal(
            LexicalFallbackSelection.Always,
            missingLeaf.GetLexicalFallbackSelection(missingLeaf.Target.ResolveStaticStructuralMemberProvider(Resolve)));

        // A missing INNER member makes the chained receiver a value.
        var missingInner = LastEdge(NestedLibrary + "\n\nLib.Missing.Q");
        Assert.Equal(
            StaticStructuralMemberProviderKind.DefinitelyAbsent,
            missingInner.Target.ResolveStaticStructuralMemberProvider(Resolve).Kind);

        // The scope-free view cannot resolve `Lib`, so the chained receiver stays
        // conditional — the MUST-selection predicate never charges it.
        Assert.Equal(
            LexicalFallbackSelection.Conditional,
            edge.GetLexicalFallbackSelection(edge.Target.GetStaticStructuralMemberProvider()));
        Assert.False(edge.LexicalFallbackIsUnconditional());

        // A local-only or conditional-branch intermediate member is a known
        // failure: no outer edge is ever reached, so nothing is selected there.
        var localOnlyRoot = SourceProvenance.ParseValid(LocalOnlyIntermediate + "\nG.Sub.Q").Root;
        var g = Assert.Single(localOnlyRoot.Properties, p => p.Name == "G").Value;
        var localOnlyEdge = Assert.IsType<Expr.DotCall>(localOnlyRoot.Output[^1]);
        var failing = localOnlyEdge.Target.ResolveStaticStructuralMemberProvider(
            name => name == "G"
                ? new(StaticStructuralMemberProviderKind.KnownAlgorithm, g)
                : new(StaticStructuralMemberProviderKind.LexicalReference));
        Assert.Equal(StaticStructuralMemberProviderKind.KnownFailure, failing.Kind);
        Assert.Equal(LexicalFallbackSelection.Never, localOnlyEdge.GetLexicalFallbackSelection(failing));
    }

    [Fact]
    public void Exposure_ChainedStructuralWinner_StaysExportedDespiteAHiddenParameterName()
    {
        // The chain analogue of OrdinaryDot_HiddenParamName_StructuralWinnerStaysExported:
        // `q` is a captured parameter name, but Sub owns `q`, so P never depends on it.
        var source =
            """
            Lib = {
                public Sub = {
                    public q = 42
                }
            }
            Outer(q) = {
                P = Lib.Sub.q
                P
            }

            Outer({x + 1})
            """;

        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(PropertyExposure.Exported, FindProperty(root, "Outer", "P").Exposure);
        Assert.Equal("42", Display(source));
    }

    // ── 9. Semantic model parity ────────────────────────────────────────────

    [Fact]
    public void SemanticModel_ChainedMember_NavigatesToTheStructuralDeclaration()
    {
        var source = NestedLibrary + "\n\nQ(x) = 99\n\nLib.Sub.Q";
        var model = Model(source);

        var declarations = model.FindDeclarations("Q");
        Assert.Equal(2, declarations.Count);
        var structural = Assert.Single(declarations, d => d.Span.StartLineNumber == 3);
        AssertSpanStartsAt(structural.Span, 3, 16);

        var member = ResolutionAt(model, 9, 9);
        Assert.Equal(OccurrenceKind.DotMemberReference, member.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, member.Classification);
        Assert.Equal(structural, member.ResolvedDeclaration);

        var property = Assert.IsType<PropertyInfo>(model.FindPropertyAt(9, 9));
        Assert.Equal("Q", property.Name);
        AssertSpanStartsAt(property.Declaration?.Span, 3, 16);

        var intermediate = ResolutionAt(model, 9, 5);
        Assert.Equal(IdentifierClassification.PropertyReference, intermediate.Classification);
        AssertSpanStartsAt(intermediate.ResolvedDeclaration?.Span, 2, 12);
    }

    [Fact]
    public void SemanticModel_ChainedExtension_NavigatesToTheLexicalCallable()
    {
        var model = Model("A = x + 7\nB = x * 5\n\n3.A.B");

        var outer = ResolutionAt(model, 4, 5);
        Assert.Equal(OccurrenceKind.DotMemberReference, outer.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, outer.Classification);
        AssertSpanStartsAt(outer.ResolvedDeclaration?.Span, 2, 1);

        var inner = ResolutionAt(model, 4, 3);
        Assert.Equal(IdentifierClassification.PropertyReference, inner.Classification);
        AssertSpanStartsAt(inner.ResolvedDeclaration?.Span, 1, 1);
    }

    [Fact]
    public void SemanticModel_LocalOnlyIntermediate_LeavesTheWholeTailUnresolved()
    {
        // Runtime errors at `Sub`; the editor must not claim `Q` resolves anywhere.
        var model = Model(LocalOnlyIntermediate + "\nQ(v) = 99\n\nG.Sub.Q");

        Assert.Equal(IdentifierClassification.Unresolved, ResolutionAt(model, 10, 3).Classification);
        var leaf = ResolutionAt(model, 10, 7);
        Assert.Equal(IdentifierClassification.Unresolved, leaf.Classification);
        Assert.Null(leaf.ResolvedDeclaration);
    }

    [Fact]
    public void SemanticModel_DeeperChain_ClassifiesEveryLevelStructurally()
    {
        var source = "A = {\n    public B = {\n        public C = {\n            public D = 7\n        }\n    }\n}\nD(x) = 93\n\nA.B.C.D";
        var model = Model(source);

        AssertSpanStartsAt(ResolutionAt(model, 10, 3).ResolvedDeclaration?.Span, 2, 12);
        AssertSpanStartsAt(ResolutionAt(model, 10, 5).ResolvedDeclaration?.Span, 3, 16);
        var leaf = ResolutionAt(model, 10, 7);
        Assert.Equal(IdentifierClassification.PropertyReference, leaf.Classification);
        AssertSpanStartsAt(leaf.ResolvedDeclaration?.Span, 4, 20);
    }

    // ── 7. Loaded modules ───────────────────────────────────────────────────

    private const string ModuleUrl = "https://katlang.org/chained/lib.kat";

    private static RunOptions ModuleOptions(string moduleSource)
        => new()
        {
            DownloadCode = (url, _) => url == ModuleUrl
                ? ValueTask.FromResult(moduleSource)
                : throw new Exception($"404: {url}"),
        };

    [Fact]
    public async Task LoadedModule_ChainedStructuralAccess_BeatsAVisibleExtension()
    {
        var options = ModuleOptions("public Sub = {\n    public Q = 1\n}");
        var source = $"Lib = load('{ModuleUrl}')\nQ(x) = 99\n\nLib.Sub.Q";

        Assert.Equal("1", await KatLangEngine.EvaluateToStringAsync(source, options));

        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors);
        var model = SemanticModelBuilder.Build(parsed);
        var member = ResolutionAt(model, 4, 9);
        Assert.Equal(IdentifierClassification.PropertyReference, member.Classification);
        // Module-provided declarations are locationless in the document model.
        Assert.Null(member.ResolvedDeclaration);
        Assert.NotNull(member.ResolvedProperty);
    }

    [Fact]
    public async Task LoadedModule_ChainedExtensionFallback_StillApplies()
    {
        var options = ModuleOptions("public Sub = {\n    5\n}");
        var source = $"Lib = load('{ModuleUrl}')\nQ(x) = x * 10\n\nLib.Sub.Q";

        Assert.Equal("50", await KatLangEngine.EvaluateToStringAsync(source, options));
    }
}
