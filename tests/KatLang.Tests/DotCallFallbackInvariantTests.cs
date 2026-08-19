namespace KatLang.Tests;

/// <summary>
/// The elaborated DotCall phase contract
/// (<see cref="DotCallElaborationInvariant"/>):
///
/// RAW / HOST-COMPATIBLE AST — <c>LexicalFallback</c> may be null, meaning
/// exactly <c>Resolve(Name)</c> and nothing else.
///
/// ELABORATED SOURCE AST (including diagnostic recovery) — no
/// <see cref="Expr.Grace"/> survives, and every dot fallback is explicit: exactly
/// <c>Resolve(Name)</c> or <c>Param(Name)</c> with the identifier equal to the
/// structural member name. The parser constructs
/// <c>Resolve(Name)</c> for every edge and <see cref="ParameterDetector"/>
/// owns both the <c>null → Resolve(Name)</c> normalization and the Param
/// rewrite, so the contract holds by construction; these tests are its
/// permanent enforcement (the repository's guarded-by-tests pattern for
/// producer invariants). Grace composed with dot syntax leaves NO trace: <c>a~.t</c> /
/// <c>a.~t</c> parse to the same ordinary <see cref="Expr.DotCall"/> as
/// <c>a.t</c>. The former carries temporary postfix Grace on the receiver;
/// the latter carries temporary prefix Grace on the fallback occurrence.
/// Parameter detection consumes both, so an elaborated graced source is structurally
/// indistinguishable from its ungraced twin except for any ordinary Grace
/// effect on the enclosing parameter order.
/// Lean twin: the <c>dotMember</c> arm of <c>postElabInvariant</c>
/// (CoreTests <c>dotMemberFallbackCoherence*</c> guards).
/// </summary>
public class DotCallFallbackInvariantTests
{
    private static Expr.DotCall SingleOutputDotCall(Algorithm root)
        => Assert.IsType<Expr.DotCall>(root.Output[^1]);

    private static void AssertElaborated(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        var violation = DotCallElaborationInvariant.CheckElaborated(provenance.Root);
        Assert.True(
            violation is null,
            $"Elaborated DotCall contract violated: {violation?.Description}{Environment.NewLine}Source:{Environment.NewLine}{source}");
    }

    // ── 1. Raw host-built null keeps documented plain lexical semantics ─────

    [Fact]
    public void HostBuiltNullFallback_MeansResolveName_Exactly()
    {
        var dotCall = new Expr.DotCall(new Expr.Num(5m), "Double");
        Assert.Null(dotCall.LexicalFallback);
        var effective = Assert.IsType<Expr.Resolve>(dotCall.EffectiveLexicalFallback);
        Assert.Equal("Double", effective.Name);

        // Evaluation of the raw tree resolves the member lexically.
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties:
            [
                new Property("Double", new Algorithm.User(
                    Parent: null,
                    Parameters: [new ParameterDeclaration("x")],
                    Opens: [],
                    Properties: [],
                    Output: [new Expr.Binary(BinaryOp.Mul, new Expr.Param("x"), new Expr.Num(2m))])),
            ],
            Output: [dotCall]);
        var run = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.False(run.IsError);
        Assert.Equal(10m, Assert.IsType<Result.Atom>(run.Value).Value);
    }

    // ── 2-6: elaboration always stores the explicit expected identity ───────

    [Fact]
    public void ElaboratedOrdinaryDot_HasNonNullFallback()
    {
        var root = SourceProvenance.ParseValid("Obj = {public V = 42}\nObj.V").Root;
        var dotCall = SingleOutputDotCall(root);
        Assert.NotNull(dotCall.LexicalFallback);
        AssertElaborated("Obj = {public V = 42}\nObj.V");
    }

    [Fact]
    public void UnknownOrdinaryMember_ElaboratesToResolveName()
    {
        var root = SourceProvenance.ParseValid("Obj = {public V = 42}\nObj.V").Root;
        var fallback = Assert.IsType<Expr.Resolve>(SingleOutputDotCall(root).LexicalFallback);
        Assert.Equal("V", fallback.Name);
    }

    [Fact]
    public void KnownParameterOrdinaryMember_ElaboratesToParamName()
    {
        var root = SourceProvenance.ParseValid("K(a, t) = a.t\nK(7, {a+1})").Root;
        var k = Assert.IsType<Algorithm.User>(root.Properties[0].Value);
        var fallback = Assert.IsType<Expr.Param>(Assert.IsType<Expr.DotCall>(k.Output[0]).LexicalFallback);
        Assert.Equal("t", fallback.Name);
    }

    [Fact]
    public void GracedImplicitMember_ElaboratesToTheOrdinaryDotEdge()
    {
        // LAW: after elaboration there is no Grace state left to observe —
        // `K = a~.t` is the ordinary dot edge `a.t` whose fallback carries the
        // front-end's Param decision for `t`. The parser's ordering Grace is
        // consumed and stripped by parameter detection. Base order a,t plus
        // postfix Grace on a yields t,a.
        var graced = SourceProvenance.ParseValid("K = a~.t\nK({a+1}, 7)").Root;
        var gracedK = Assert.IsType<Algorithm.User>(graced.Properties[0].Value);
        Assert.Equal(["t", "a"], gracedK.Params);

        var ungraced = SourceProvenance.ParseValid("K = a.t\nK(7, {a+1})").Root;
        var ungracedK = Assert.IsType<Algorithm.User>(ungraced.Properties[0].Value);
        Assert.Equal(["a", "t"], ungracedK.Params);

        foreach (var body in new[] { gracedK.Output[0], ungracedK.Output[0] })
        {
            var edge = Assert.IsType<Expr.DotCall>(body);
            Assert.Equal("t", edge.Name);
            Assert.Equal("a", Assert.IsType<Expr.Param>(edge.Target).Name);
            Assert.Equal("t", Assert.IsType<Expr.Param>(edge.LexicalFallback).Name);
            Assert.Null(edge.Args);
        }
    }

    [Fact]
    public void GracedKnownLexicalMember_ElaboratesToTheOrdinaryResolveFallback()
    {
        // The marker does NOT imply Param: a visible declaration keeps the
        // ordinary Resolve fallback, exactly like the ungraced edge.
        var root = SourceProvenance.ParseValid("Known(x) = x + 1\nv = 5\nv~.Known").Root;
        var edge = SingleOutputDotCall(root);
        Assert.Equal("Known", edge.Name);
        Assert.Equal("Known", Assert.IsType<Expr.Resolve>(edge.LexicalFallback).Name);
        Assert.Equal("v", Assert.IsType<Expr.Resolve>(edge.Target).Name);
    }

    // ── 7-8: the checker rejects incoherent hand-built edges ────────────────

    [Fact]
    public void Checker_RejectsFallbackNameMismatch()
    {
        var root = new Algorithm.User(null, [], [], [], [
            new Expr.DotCall(new Expr.Num(1m), "t")
            {
                LexicalFallback = new Expr.Resolve("u"),
            },
        ]);
        var violation = DotCallElaborationInvariant.CheckElaborated(root);
        Assert.NotNull(violation);
        Assert.Contains("does not match member name", violation.Description);
    }

    [Fact]
    public void Checker_RejectsArbitraryFallbackExpressionKinds()
    {
        var root = new Algorithm.User(null, [], [], [], [
            new Expr.DotCall(new Expr.Num(1m), "t")
            {
                LexicalFallback = new Expr.Num(5m),
            },
        ]);
        var violation = DotCallElaborationInvariant.CheckElaborated(root);
        Assert.NotNull(violation);
        Assert.Contains("must be Resolve or Param", violation.Description);
    }

    [Fact]
    public void Checker_RejectsNullFallback()
    {
        var nullFallback = new Algorithm.User(null, [], [], [], [
            new Expr.DotCall(new Expr.Num(1m), "t"),
        ]);
        Assert.Contains(
            "null",
            DotCallElaborationInvariant.CheckElaborated(nullFallback)!.Description,
            StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void Checker_RejectsLeakedGraceAnnotation()
    {
        var leaked = new Expr.Grace(new Expr.Resolve("a"), -1);
        var root = new Algorithm.User(null, [], [], [], [leaked]);

        var violation = DotCallElaborationInvariant.CheckElaborated(root);

        Assert.NotNull(violation);
        Assert.Same(leaked, violation.Expression);
        Assert.Contains("Grace remains after elaboration", violation.Description);
    }

    [Fact]
    public void CoreOpenFormRule_AcceptsOnlyArgumentlessDotEdges()
    {
        var ordinary = new Expr.DotCall(new Expr.Resolve("M"), "C")
        {
            LexicalFallback = new Expr.Resolve("C"),
        };
        var explicitEmptyArgs = ordinary with { Args = OutputBundle.Empty };

        Assert.True(ordinary.IsCoreOpenForm());
        Assert.False(explicitEmptyArgs.IsCoreOpenForm());
    }

    [Fact]
    public void FrontEndFingerprint_IncludesDotEdgeAndGraceOccurrenceFacts()
    {
        static string Fingerprint(Expr edge)
        {
            var root = new Algorithm.User(null, [], [], [], [edge]);
            return global::KatLang.ParserFuzz.FrontEndFingerprint.ComputeParseResult(root, []);
        }

        var baseline = new Expr.DotCall(new Expr.Num(1m), "F")
        {
            LexicalFallback = new Expr.Resolve("F"),
            MemberSpan = new SourceSpan(1, 4, 1, 4),
        };
        var paramFallback = baseline with { LexicalFallback = new Expr.Param("F") };

        Assert.NotEqual(Fingerprint(baseline), Fingerprint(paramFallback));

        // Receiver-postfix and member-prefix Grace are ordinary Grace nodes on
        // different semantic name occurrences. Their raw fingerprints retain
        // both position and weight without any source-origin provenance bit.
        var receiverPostfix = baseline with
        {
            Target = new Expr.Grace(new Expr.Resolve("a"), +1),
        };
        var memberPrefix = baseline with
        {
            Target = new Expr.Resolve("a"),
            LexicalFallback = new Expr.Grace(new Expr.Resolve("F"), -1),
        };
        Assert.NotEqual(Fingerprint(baseline), Fingerprint(receiverPostfix));
        Assert.NotEqual(Fingerprint(baseline), Fingerprint(memberPrefix));
        Assert.NotEqual(Fingerprint(receiverPostfix), Fingerprint(memberPrefix));
    }

    // ── 2 (sweep): the whole canonical corpus satisfies the contract ────────

    [Fact]
    public void EveryLanguageSpecSource_SatisfiesTheElaboratedContract()
    {
        var checkedCases = 0;
        foreach (var specCase in LanguageSpec.LanguageSpecCorpus.AllCases())
        {
            var parse = Parser.Parse(specCase.Source);
            var violation = DotCallElaborationInvariant.CheckElaborated(parse.Root);
            Assert.True(
                violation is null,
                $"Spec case '{specCase.Id}' violated the DotCall contract: {violation?.Description}");
            checkedCases++;
        }

        Assert.True(checkedCases > 100, $"Sweep covered only {checkedCases} cases — corpus wiring changed?");
    }

    [Fact]
    public void RepresentativeGracedAndChainedSources_SatisfyTheContract()
    {
        string[] sources =
        [
            "K(a, t) = a.t\nK(7, {a+1})",
            "K(a, t) = a~.t\nK(7, {a+1})",
            "K = a.~t\nK({a+1}, 7)",
            "K(a, t) = a~.t.string\nK(7, {a+1})",
            "Inc(x) = x + 1\nv = 5\nv~.Inc",
            "Mean(*Vector) = Vector.sum / Vector.count\nV = 1, 2, 2.718\nV~.Mean",
            "Obj = {public V = 42}\nK(a, V) = a.V\nK(Obj, {a+1})",
            "x, *rest = (1, 2, 3)\nrest.count",
            "A = {\n    public X = 1, 2, 3\n}\nA.X",
        ];
        foreach (var source in sources)
            AssertElaborated(source);
    }

    // ── 9: diagnostic recovery still completes phase normalization ─────────

    [Fact]
    public void DiagnosticRecoveryTree_StillSatisfiesThePhaseContract()
    {
        // Recovery may preserve a useful ordinary-call shape, but it may not
        // leak Grace or an incoherent dot fallback into later tooling.
        var recovery = Parser.Parse("K = f(x)~.t");
        Assert.True(recovery.HasErrors);
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(recovery.Root));
    }

    // ── 10: the C# → Lean encoding never serializes a semantic null ─────────

    [Fact]
    public void LeanEncoding_NormalizesHostNullToTheOrdinarySugar()
    {
        var hostNode = new Expr.DotCall(new Expr.Resolve("A"), "count");
        Assert.Null(hostNode.LexicalFallback);
        Assert.Equal("(.dotCall (.resolve \"A\") \"count\" none)", LeanAstEncoder.EncodeExpr(hostNode));

        var paramFallback = new Expr.DotCall(new Expr.Param("a"), "t")
        {
            LexicalFallback = new Expr.Param("t"),
        };
        Assert.Equal(
            "(.dotMember (.param \"a\") \"t\" (.param \"t\") none)",
            LeanAstEncoder.EncodeExpr(paramFallback));
    }

    // ── 12-13: rewriters preserve the stored identity and provenance ────────

    [Fact]
    public void FrontEndRewriters_PreserveFallbackIdentityAndSpans()
    {
        var provenance = SourceProvenance.ParseValid(
            """
            Obj = {
                public V = 42
                0
            }
            K(a, t) = a~.t.string
            K(7, {a+1})
            Obj.V
            """);
        var k = Assert.IsType<Algorithm.User>(
            Assert.Single(provenance.Root.Properties, property => property.Name == "K").Value);
        var outerChain = Assert.IsType<Expr.DotCall>(k.Output[0]);

        // The full pipeline (detector, implicit-argument resolution, exposure
        // resolution) ran; the inner graced source is the ordinary dot
        // edge `a.t` (its ordering grace consumed and stripped) with both its
        // stored facts intact, and the outer `.string` edge kept its identity
        // and spans.
        var innerEdge = Assert.IsType<Expr.DotCall>(outerChain.Target);
        Assert.Equal("t", innerEdge.Name);
        Assert.Equal("a", Assert.IsType<Expr.Param>(innerEdge.Target).Name);
        Assert.Equal("t", Assert.IsType<Expr.Param>(innerEdge.LexicalFallback).Name);
        Assert.NotNull(innerEdge.MemberSpan);
        Assert.NotNull(outerChain.MemberSpan);
        Assert.Equal("string", Assert.IsType<Expr.Resolve>(outerChain.LexicalFallback).Name);

        Assert.Null(DotCallElaborationInvariant.CheckElaborated(provenance.Root));
    }

    [Fact]
    public async Task ModuleElaborationPath_PreservesGracedDotFacts()
    {
        // Regression family: a module-path rebuild once silently dropped
        // stored dot-edge facts. Both spellings must survive the load-enabled
        // pipeline as the SAME structural edge — 42 twice.
        var run = await KatLangEngine.RunAsync(
            """
            V(x) = 99
            Obj = {
                public V = 42
                0
            }

            Obj.V
            Obj~.V
            """,
            new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("public C = 5") });
        var success = Assert.IsType<RunResult.Success>(run);
        Assert.Equal($"42{Environment.NewLine}42", success.ToDisplayString());
    }

    [Fact]
    public void HostTreeWithGracedOpenTarget_LeavesNoGraceAfterElaboration()
    {
        // An open target has no parameter inference to reorder. Source can't
        // produce this (the parser rejects and unwraps it), but a host tree
        // can — and "no Grace survives elaboration" must hold in EVERY
        // position, opens included.
        var hostRoot = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [new Expr.Grace(new Expr.Resolve("Lib"), -1)],
            Properties: [],
            Output: [new Expr.Num(0m)]);

        var (detected, _) = ParameterDetector.Detect(hostRoot);

        Assert.Equal("Lib", Assert.IsType<Expr.Resolve>(Assert.Single(detected.Opens)).Name);
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(detected));
    }

    [Fact]
    public void HostTreeThroughDetector_IsNormalizedToExplicitFallback()
    {
        // The detector owns null → Resolve(Name): a raw host tree entering
        // Detect leaves with every dot edge explicit.
        var hostRoot = new Algorithm.User(null, [], [], [
            new Property("Use", new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.DotCall(new Expr.Resolve("Data"), "count")])),
        ], [new Expr.Num(0m)]);

        var (detected, diagnostics) = ParameterDetector.Detect(hostRoot);
        Assert.Empty(diagnostics);
        var use = Assert.IsType<Algorithm.User>(
            Assert.Single(detected.Properties, property => property.Name == "Use").Value);
        var dotCall = Assert.IsType<Expr.DotCall>(use.Output[0]);
        var fallback = Assert.IsType<Expr.Resolve>(dotCall.LexicalFallback);
        Assert.Equal("count", fallback.Name);
    }
}
