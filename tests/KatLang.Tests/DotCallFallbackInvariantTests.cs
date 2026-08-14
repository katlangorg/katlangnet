namespace KatLang.Tests;

/// <summary>
/// The elaborated dot-edge phase contract
/// (<see cref="DotCallElaborationInvariant"/>):
///
/// RAW / HOST-COMPATIBLE AST — <c>LexicalFallback</c> may be null, meaning
/// exactly <c>Resolve(Name)</c> and nothing else.
///
/// ELABORATED, DIAGNOSTIC-FREE SOURCE AST — the fallback is always explicit:
/// exactly <c>Resolve(Name)</c> or <c>Param(Name)</c> with the identifier
/// equal to the structural member name, and the extension marker span agrees
/// with the resolution mode. The parser constructs <c>Resolve(Name)</c> for
/// every edge and <see cref="ParameterDetector"/> owns both the
/// <c>null → Resolve(Name)</c> normalization and the Param rewrite, so the
/// contract holds by construction; these tests are its permanent enforcement
/// (the repository's guarded-by-tests pattern for producer invariants).
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
            $"Elaborated dot-edge contract violated: {violation?.Description}{Environment.NewLine}Source:{Environment.NewLine}{source}");
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
    public void ExtensionImplicitMember_ElaboratesToParamName()
    {
        var root = SourceProvenance.ParseValid("K = a~.t\nK(7, {a+1})").Root;
        var k = Assert.IsType<Algorithm.User>(root.Properties[0].Value);
        var dotCall = Assert.IsType<Expr.DotCall>(k.Output[0]);
        Assert.Equal(DotResolutionMode.ExtensionOnly, dotCall.ResolutionMode);
        var fallback = Assert.IsType<Expr.Param>(dotCall.LexicalFallback);
        Assert.Equal("t", fallback.Name);
    }

    [Fact]
    public void ExtensionKnownLexicalMember_ElaboratesToResolveName()
    {
        // ExtensionOnly does NOT imply Param: a visible declaration keeps the
        // ordinary Resolve identity.
        var root = SourceProvenance.ParseValid("Known(x) = x + 1\n5~.Known").Root;
        var dotCall = SingleOutputDotCall(root);
        Assert.Equal(DotResolutionMode.ExtensionOnly, dotCall.ResolutionMode);
        var fallback = Assert.IsType<Expr.Resolve>(dotCall.LexicalFallback);
        Assert.Equal("Known", fallback.Name);
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
    public void Checker_RejectsNullFallback_AndMarkerModeDisagreement()
    {
        var nullFallback = new Algorithm.User(null, [], [], [], [
            new Expr.DotCall(new Expr.Num(1m), "t"),
        ]);
        Assert.Contains(
            "null",
            DotCallElaborationInvariant.CheckElaborated(nullFallback)!.Description,
            StringComparison.OrdinalIgnoreCase);

        var markerless = new Algorithm.User(null, [], [], [], [
            new Expr.DotCall(new Expr.Num(1m), "t")
            {
                LexicalFallback = new Expr.Resolve("t"),
                ResolutionMode = DotResolutionMode.ExtensionOnly,
            },
        ]);
        Assert.Contains(
            "ExtensionMarkerSpan",
            DotCallElaborationInvariant.CheckElaborated(markerless)!.Description);
    }

    [Fact]
    public void Checker_RejectsInvalidResolutionModeValue()
    {
        var root = new Algorithm.User(null, [], [], [], [
            new Expr.DotCall(new Expr.Num(1m), "t")
            {
                LexicalFallback = new Expr.Resolve("t"),
                ResolutionMode = (DotResolutionMode)42,
            },
        ]);

        var violation = DotCallElaborationInvariant.CheckElaborated(root);
        Assert.NotNull(violation);
        Assert.Contains("invalid value 42", violation.Description);
    }

    [Fact]
    public void CoreOpenFormRule_AcceptsOnlyOrdinaryArgumentlessDotEdges()
    {
        var ordinary = new Expr.DotCall(new Expr.Resolve("M"), "C")
        {
            LexicalFallback = new Expr.Resolve("C"),
        };
        var extension = ordinary with
        {
            ResolutionMode = DotResolutionMode.ExtensionOnly,
            ExtensionMarkerSpan = new SourceSpan(1, 2, 1, 2),
        };
        var explicitEmptyArgs = ordinary with { Args = OutputBundle.Empty };

        Assert.True(ordinary.IsCoreOpenForm());
        Assert.False(extension.IsCoreOpenForm());
        Assert.False(explicitEmptyArgs.IsCoreOpenForm());
    }

    [Fact]
    public void FrontEndFingerprint_IncludesEveryStoredDotEdgeFact()
    {
        static string Fingerprint(Expr.DotCall edge)
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
        var extension = baseline with
        {
            ResolutionMode = DotResolutionMode.ExtensionOnly,
            ExtensionMarkerSpan = new SourceSpan(1, 2, 1, 2),
        };
        var differentMarker = extension with
        {
            ExtensionMarkerSpan = new SourceSpan(1, 3, 1, 3),
        };

        Assert.NotEqual(Fingerprint(baseline), Fingerprint(paramFallback));
        Assert.NotEqual(Fingerprint(baseline), Fingerprint(extension));
        Assert.NotEqual(Fingerprint(extension), Fingerprint(differentMarker));
    }

    // ── 2 (sweep): the whole canonical corpus satisfies the contract ────────

    [Fact]
    public void EveryParseableLanguageSpecSource_SatisfiesTheElaboratedContract()
    {
        var checkedCases = 0;
        foreach (var specCase in LanguageSpec.LanguageSpecCorpus.AllCases())
        {
            if (specCase.Outcome == LanguageSpec.SpecOutcome.ParseError)
                continue;

            var parse = Parser.Parse(specCase.Source);
            // Recovery trees are exempt from valid-source invariants by
            // repository policy; the corpus's evaluating cases parse cleanly.
            if (parse.HasErrors)
                continue;

            var violation = DotCallElaborationInvariant.CheckElaborated(parse.Root);
            Assert.True(
                violation is null,
                $"Spec case '{specCase.Id}' violated the dot-edge contract: {violation?.Description}");
            checkedCases++;
        }

        Assert.True(checkedCases > 100, $"Sweep covered only {checkedCases} cases — corpus wiring changed?");
    }

    [Fact]
    public void RepresentativeExtensionAndChainSources_SatisfyTheContract()
    {
        string[] sources =
        [
            "K(a, t) = a.t\nK(7, {a+1})",
            "K(a, t) = a~.t\nK(7, {a+1})",
            "K = a.~t\nK(7, {a+1})",
            "K(a, t) = a~.t.string\nK(7, {a+1})",
            "Dub(x) = x * 2\nInc(x) = x + 1\n5~.Inc~.Dub",
            "Mean(*Vector) = Vector.sum / Vector.count\n(1, 2, 2.718)~.Mean",
            "Obj = {public V = 42}\nK(a, V) = a.V\nK(Obj, {a+1})",
            "x, *rest = (1, 2, 3)\nrest.count",
            "A = {\n    public X = 1, 2, 3\n}\nA.X",
        ];
        foreach (var source in sources)
            AssertElaborated(source);
    }

    // ── 9: diagnostic recovery is not rejected by valid-source invariants ───

    [Fact]
    public void DiagnosticRecoveryTrees_AreExemptFromTheValidSourceSweep()
    {
        // The sweep's contract applies to diagnostic-free elaborations only;
        // a recovery tree is simply outside the checker's domain. This pins
        // the exemption policy so the sweep can never start failing merely
        // because recovery output shapes changed.
        var recovery = Parser.Parse("K(a, t) = a~.~t\nK(7, {a+1})");
        Assert.True(recovery.HasErrors);
        // No assertion on CheckElaborated: recovery output is out of contract.
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
            "(.dotMember (.param \"a\") \"t\" (.param \"t\") .ordinary none)",
            LeanAstEncoder.EncodeExpr(paramFallback));
    }

    // ── 12-13: rewriters preserve the stored identity and provenance ────────

    [Fact]
    public void FrontEndRewriters_PreserveFallbackIdentityModeAndSpans()
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
        var innerExtension = Assert.IsType<Expr.DotCall>(outerChain.Target);

        // The full pipeline (detector, implicit-argument resolution, exposure
        // resolution) ran; the extension edge kept its identity and spans.
        Assert.Equal(DotResolutionMode.ExtensionOnly, innerExtension.ResolutionMode);
        Assert.NotNull(innerExtension.ExtensionMarkerSpan);
        Assert.NotNull(innerExtension.MemberSpan);
        Assert.Equal("t", Assert.IsType<Expr.Param>(innerExtension.LexicalFallback).Name);
        Assert.Equal(DotResolutionMode.Ordinary, outerChain.ResolutionMode);
        Assert.Equal("string", Assert.IsType<Expr.Resolve>(outerChain.LexicalFallback).Name);

        Assert.Null(DotCallElaborationInvariant.CheckElaborated(provenance.Root));
    }

    [Fact]
    public void ModuleElaborationPath_PreservesExtensionEdges()
    {
        // Regression for the module-path rebuild that silently degraded
        // extension edges to ordinary dots (dropping mode + fallback): the
        // load-enabled pipeline must evaluate `Obj~.V` as the extension call.
        var run = KatLangEngine.Run(
            """
            V(x) = 99
            Obj = {
                public V = 42
                0
            }

            Obj.V
            Obj~.V
            """,
            new RunOptions { DownloadCode = _ => "public C = 5" });
        var success = Assert.IsType<RunResult.Success>(run);
        Assert.Equal($"42{Environment.NewLine}99", success.ToDisplayString());
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
