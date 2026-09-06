namespace KatLang.Tests;

public class PropertyExposureResolverTests
{
    [Fact]
    public void Build_SummarySiblingCycle_RemainsSeparateFromDirectSiblingDependencyFacts()
    {
        var algorithm = BuildUserAlgorithmBeforeExposure(
            "Algo",
            """
            Algo(x) = {
                Left = {
                    InnerLeft = Right
                    InnerLeft
                }
                Right = {
                    InnerRight = Left
                    InnerRight
                    x
                }
                x
            }
            """);

        var orderGraph = PropertyDependencyGraphBuilder.BuildDependencyOrder(algorithm);
        var graph = PropertyDependencyGraphBuilder.BuildSummaries(algorithm);
        var leftNode = graph[PropertyIndex(graph, "Left")];
        var rightNode = graph[PropertyIndex(graph, "Right")];

        // The processing-order channel sees the nested references too (the resolver rewrites
        // InnerLeft while processing Left and reads Right's signature there): a direct
        // sibling cycle, which the topological order resolves by declaration order. The
        // summary channel's facts are computed independently and stay exactly as before.
        Assert.Equal([PropertyIndex(graph, "Right")], orderGraph[PropertyIndex(graph, "Left")].SiblingDependencyIndices);
        Assert.Equal([PropertyIndex(graph, "Right")], leftNode.SummarySiblingDependencyIndices);
        Assert.Empty(leftNode.SummaryVisiblePropertyDependencyNames);
        Assert.Empty(leftNode.RequiredAncestorOwnedParameterNames);

        Assert.Equal([PropertyIndex(graph, "Left")], orderGraph[PropertyIndex(graph, "Right")].SiblingDependencyIndices);
        Assert.Equal([PropertyIndex(graph, "Left")], rightNode.SummarySiblingDependencyIndices);
        Assert.Empty(rightNode.SummaryVisiblePropertyDependencyNames);
        Assert.Equal(["x"], rightNode.RequiredAncestorOwnedParameterNames);
    }

    [Fact]
    public void Parse_SummarySiblingCycle_StillRequiresExposureFixpoint()
    {
        var result = Parser.Parse(
            """
            Algo(x) = {
                Left = {
                    InnerLeft = Right
                    InnerLeft
                }
                Right = {
                    InnerRight = Left
                    InnerRight
                    x
                }
                x
            }
            """);

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));

        var algorithm = Assert.IsType<Algorithm.User>(Assert.Single(result.Root.Properties).Value);
        var left = Assert.Single(algorithm.Properties, property => property.Name == "Left");
        var right = Assert.Single(algorithm.Properties, property => property.Name == "Right");

        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, left.Exposure);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, right.Exposure);

        var leftBody = Assert.IsType<Algorithm.User>(left.Value);
        var rightBody = Assert.IsType<Algorithm.User>(right.Value);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(leftBody.Properties).Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(rightBody.Properties).Exposure);
    }

    [Fact]
    public void Parse_PublicTopLevelApiCallingPrivateHelperWithCapturedNestedLocal_RemainsExported()
    {
        var result = Parser.Parse(
            """
            PrivateHelper(Candidate) = {
                Step = Candidate + 1
                Step
            }

            public PublicApi(N) = PrivateHelper(N)
            """);

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));

        var privateHelper = Assert.Single(result.Root.Properties, property => property.Name == "PrivateHelper");
        Assert.False(privateHelper.IsPublic);
        Assert.Equal(PropertyExposure.Exported, privateHelper.Exposure);

        var helperBody = Assert.IsType<Algorithm.User>(privateHelper.Value);
        var step = Assert.Single(helperBody.Properties, property => property.Name == "Step");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, step.Exposure);

        var publicApi = Assert.Single(result.Root.Properties, property => property.Name == "PublicApi");
        Assert.True(publicApi.IsPublic);
        Assert.Equal(PropertyExposure.Exported, publicApi.Exposure);
    }

    /// <summary>
    /// The builder's LOCAL summary fixed point must expand transitively: a nested body's
    /// two-level local chain (B = A, A captures x) makes the body's output requirement
    /// reach x THROUGH B. A pre-fixed-point (base-seed) summary would instead report a
    /// phantom visible dependency on the local name A and lose the capture entirely.
    /// </summary>
    [Fact]
    public void Build_NestedLocalPropertyChain_ExpandsTransitivelyThroughTheLocalFixedPoint()
    {
        var algorithm = BuildUserAlgorithmBeforeExposure(
            "Outer",
            """
            Outer(x) = {
                P = {
                    A = x + 1
                    B = A
                    B
                }
                x
            }
            """);

        var graph = PropertyDependencyGraphBuilder.BuildSummaries(algorithm);

        Assert.Equal(["x"], graph[PropertyIndex(graph, "P")].RequiredAncestorOwnedParameterNames);
        Assert.Empty(graph[PropertyIndex(graph, "P")].SummaryVisiblePropertyDependencyNames);
    }

    [Fact]
    public void Parse_NestedLocalPropertyChain_IsLocalOnly()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                P = {
                    A = x + 1
                    B = A
                    B
                }
                x
            }
            """);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "P").Exposure);
    }

    [Fact]
    public void Build_AncestorCaptureInsideTransparentLayers_SeedsRequiredAncestorNames()
    {
        var algorithm = BuildUserAlgorithmBeforeExposure(
            "Outer",
            """
            Outer(x) = {
                Helper(y) = y + 10
                Direct = x + 1
                Grouped = (x, 1)
                Called = Helper(x)
                x
            }
            """);

        var graph = PropertyDependencyGraphBuilder.BuildSummaries(algorithm);

        Assert.Equal(["x"], graph[PropertyIndex(graph, "Direct")].RequiredAncestorOwnedParameterNames);
        Assert.Equal(["x"], graph[PropertyIndex(graph, "Grouped")].RequiredAncestorOwnedParameterNames);
        Assert.Equal(["x"], graph[PropertyIndex(graph, "Called")].RequiredAncestorOwnedParameterNames);
        Assert.Empty(graph[PropertyIndex(graph, "Helper")].RequiredAncestorOwnedParameterNames);
    }

    [Fact]
    public void Parse_AncestorCaptureInParenthesizedGroup_IsLocalOnly()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Direct = x + 1
                Grouped = (x, 1)
                x
            }
            """);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "Direct").Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "Grouped").Exposure);
    }

    [Fact]
    public void Parse_AncestorCaptureInCallArguments_IsLocalOnly()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Helper(y) = y + 10
                Called = Helper(x)
                x
            }
            """);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "Called").Exposure);
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Helper").Exposure);
    }

    [Fact]
    public void Parse_AncestorCaptureThroughNestedTransparentLayers_IsLocalOnly()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Helper(y) = y + 10
                Other(z) = z * 2
                DoubleGrouped = ((x, 1))
                GroupedArg = Helper((x, 1))
                Chained = Helper(Other(x))
                x
            }
            """);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "DoubleGrouped").Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "GroupedArg").Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "Chained").Exposure);
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Helper").Exposure);
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Other").Exposure);
    }

    [Fact]
    public void Parse_AncestorCaptureInDotCallArguments_IsLocalOnly()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Data = [1, 2, 3]
                Taken = Data.take(x)
                x
            }
            """);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "Taken").Exposure);
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Data").Exposure);
    }

    [Fact]
    public void Parse_OwnCallableParametersThroughTransparentLayers_RemainExported()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Own(a) = (a, 1)
                Forward(b) = Own(b)
                x
            }
            """);

        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Own").Exposure);
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Forward").Exposure);
    }

    [Fact]
    public void Parse_BraceBlockArgumentScopes_KeepOwnershipBoundaries()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Apply(f) = f(3)
                OwnedBrace = Apply({y + 1})
                CapturedBrace = Apply({x + y})
                x
            }
            """);

        // The brace block owns its free name `y`, so passing it as an argument
        // does not make the containing property depend on any ancestor parameter.
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "OwnedBrace").Exposure);
        // A brace block that closes over the ancestor parameter `x` still marks
        // the containing property local-only: the brace algorithm's scope
        // boundary owns `y` but not `x`.
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "CapturedBrace").Exposure);
    }

    /// <summary>
    /// Declarations inside a conditional branch body classify under the ONE self-containment
    /// rule, exactly like declarations in a parameterized body: self-contained members — of the
    /// opened inline block, of a branch-local library, of a block the branch hands out, of a
    /// nested clause family's branch — are Exported; a member capturing the block's own
    /// parameter or the branch's pattern binder is local-only for that reason. Reachability from
    /// outside the conditional is the family's structural rule, never a classification, so
    /// <c>LocalOnlyConditionalAlgorithm</c> is assigned to no property.
    /// </summary>
    [Fact]
    public void Parse_BranchDeclarations_ClassifyUnderTheOneSelfContainmentRule()
    {
        var source = """
            Apply(f) = f
            F(0) = {
                open {
                    public Helper = 5
                    public Capturing(y) = {
                        public Inner = y
                        Inner
                    }
                }
                public Declared = Helper
                Lib = {
                    public X = 1
                }
                Handed = Apply({
                    public Member = 1
                    Member
                })
                Declared, Handed
            }
            F(n) = {
                Bound = n + 1
                Lib = {
                    public X = 1
                    public Y = n
                }
                K(0) = {
                    public Z = 7
                    Z
                }
                K(m) = m
                Bound, Lib.X
            }
            F(0), F(3)
            """;
        var result = Parser.Parse(source);
        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));

        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(result.Root.Properties, p => p.Name == "F").Value);
        var literalBranch = Assert.IsType<Algorithm.User>(family.Branches[0].Body);
        var opened = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(literalBranch.Opens)).Algorithm;
        Assert.Equal(PropertyExposure.Exported, Assert.Single(opened.Properties, p => p.Name == "Helper").Exposure);
        var capturing = Assert.Single(opened.Properties, p => p.Name == "Capturing");
        Assert.Equal(PropertyExposure.Exported, capturing.Exposure);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, Assert.Single(capturing.Value.Properties).Exposure);
        Assert.Equal(PropertyExposure.Exported, Assert.Single(literalBranch.Properties, p => p.Name == "Declared").Exposure);
        var library = Assert.Single(literalBranch.Properties, p => p.Name == "Lib");
        Assert.Equal(PropertyExposure.Exported, library.Exposure);
        Assert.Equal(PropertyExposure.Exported, Assert.Single(library.Value.Properties).Exposure);
        var handed = Assert.Single(literalBranch.Properties, p => p.Name == "Handed");
        Assert.Equal(PropertyExposure.Exported, handed.Exposure);
        var handedBlock = Assert.IsType<Expr.AlgorithmExpr>(
            Assert.Single(Assert.IsType<Expr.Call>(Assert.Single(handed.Value.Output)).Args)).Algorithm;
        Assert.Equal(PropertyExposure.Exported, Assert.Single(handedBlock.Properties).Exposure);

        var binderBranch = Assert.IsType<Algorithm.User>(family.Branches[1].Body);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(binderBranch.Properties, p => p.Name == "Bound").Exposure);
        var binderLibrary = Assert.Single(binderBranch.Properties, p => p.Name == "Lib");
        Assert.Equal(PropertyExposure.Exported, binderLibrary.Exposure);
        Assert.Equal(PropertyExposure.Exported, Assert.Single(binderLibrary.Value.Properties, p => p.Name == "X").Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(binderLibrary.Value.Properties, p => p.Name == "Y").Exposure);
        var nestedFamily = Assert.Single(binderBranch.Properties, p => p.Name == "K");
        Assert.Equal(PropertyExposure.Exported, nestedFamily.Exposure);
        Assert.Equal(PropertyExposure.Exported, Assert.Single(nestedFamily.Value.Branches[0].Body.Properties).Exposure);

        Assert.Equal(
            "(5, 1)\n(4, 1)",
            Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n"));
    }

    // ───────── Bug-hunt K1-02: a local property referenced through a transparent layer ─────────
    //
    // Capture rows, call and dot-call argument bundles walk with empty local maps (they own no
    // names), and a nested block's completed summary knows nothing of the enclosing level, so a
    // reference to the ENCLOSING algorithm's own property escaped as a bare visible name. An
    // enclosing level without that name dropped it (a local-only member leaked through `open`);
    // an enclosing sibling of the same name was wrongly consulted (a self-contained member was
    // hidden). The summary now resolves those names ownership-first at the algorithm level.

    private static string OpenThroughTransparentLayerSource(string row) =>
        $$"""
        Outer(p) = {
          open Lib
          Lib = { public G = { Q = p + 1
          {{row}} } }
          Id(v) = v
          Zero = 0
          Add2(u, v) = u + v
          G
        }
        Outer(1)
        """;

    private const string SelfContainedThroughCaptureRowSource = """
        Outer(p) = {
          open Lib
          Lib = {
            public G = { Q = 7
            (Q) }
            Q = p + 1
          }
          G
        }
        Outer(1)
        """;

    [Theory]
    [InlineData("(Q)")]
    [InlineData("{ Q }")]
    [InlineData("Id(Q)")]
    [InlineData("Zero.Add2(Q)")]
    public void Parse_LocalPropertyReferencedThroughTransparentLayer_KeepsAncestorCaptureLocalOnly(string row)
    {
        var source = OpenThroughTransparentLayerSource(row);
        var root = SourceProvenance.ParseValid(source).Root;

        // `G` depends, through its own local `Q`, on `p` — owned by the enclosing `Outer` — so it
        // is local-only however the reference is written, and `open Lib` must not expose it.
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            NestedProperty(root, "Outer", "Lib", "G").Exposure);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UnknownName, error.Code);
        Assert.Contains("Unknown name: G", error.Message);
    }

    [Fact]
    public void Parse_LocalPropertyReferencedDirectly_IsTheControlForTheTransparentLayers()
    {
        // The bare `Q` row: the same program every transparent spelling above must agree with.
        var source = OpenThroughTransparentLayerSource("Q");
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            NestedProperty(SourceProvenance.ParseValid(source).Root, "Outer", "Lib", "G").Exposure);
        Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
    }

    [Fact]
    public void Parse_SelfContainedLocalReferencedThroughCaptureRow_StaysExportedBesideSameNamedEnclosingSibling()
    {
        var root = SourceProvenance.ParseValid(SelfContainedThroughCaptureRowSource).Root;

        // `G`'s `(Q)` names ITS OWN self-contained `Q = 7`, never Lib's `Q = p + 1`.
        Assert.Equal(PropertyExposure.Exported, NestedProperty(root, "Outer", "Lib", "G").Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            NestedProperty(root, "Outer", "Lib", "Q").Exposure);

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(SelfContainedThroughCaptureRowSource));
        Assert.Equal("7", success.ToDisplayString());
    }

    public static IEnumerable<object[]> ExposureAdversarialCases()
    {
        foreach (var row in new[] { "Q", "(Q)", "((Q))", "Id(Q)", "Id(Id(Q))", "Zero.Add2(Id(Q))", "{ Q }", "Id({ Q })", "[Q]:0", "Q*" })
        foreach (var captures in new[] { false, true })
        foreach (var declarations in new[] { "Q = VALUE", "Q = R\n R = VALUE", "R = VALUE\n Q = R", "Q = if(0, R, VALUE)\n R = (Q)" })
            yield return [row, declarations.Replace("VALUE", captures ? "p + 1" : "7", StringComparison.Ordinal), captures];
    }

    [Theory]
    [MemberData(nameof(ExposureAdversarialCases))]
    public async Task Exposure_TransitiveAndCyclicLocals_RespectOwnershipAcrossBundles(
        string row, string declarations, bool captures)
    {
        var source = $$"""
            Outer(p) = {
              open Lib, Other, Lib
              Lib = {
                public G = { {{declarations}}
                {{row}} }
                Q = p + 100
              }
              Other = { public Extra = 9 }
              Id(value) = value
              Zero = 0
              Add2(left, right) = left + right
              G
            }
            Outer(1)
            """;
        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(captures ? PropertyExposure.LocalOnlyCapturedAncestorParameters : PropertyExposure.Exported,
            NestedProperty(root, "Outer", "Lib", "G").Exposure);
        var sync = KatLangEngine.Run(source);
        var asyncResult = await KatLangEngine.RunAsync(source);
        Assert.Equal(sync.ToDisplayString(), asyncResult.ToDisplayString());
        if (captures)
        {
            var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(sync).Errors);
            Assert.Equal(KatLangErrorCode.UnknownName, error.Code);
            Assert.Contains("Unknown name: G", error.Message);
        }
        else
            Assert.Equal("7", Assert.IsType<RunResult.Success>(sync).ToDisplayString());
    }

    private static Property NestedProperty(Algorithm algorithm, params string[] path)
    {
        Property? current = null;
        var scope = algorithm;
        foreach (var name in path)
        {
            current = Assert.Single(scope.Properties, property => property.Name == name);
            scope = current.Value;
        }

        return current!;
    }

    private static Algorithm.User ParseSinglePropertyBody(string source)
    {
        var result = Parser.Parse(source);
        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));
        return Assert.IsType<Algorithm.User>(Assert.Single(result.Root.Properties).Value);
    }

    private static Algorithm.User BuildUserAlgorithmBeforeExposure(string propertyName, string source)
    {
        var syntaxResult = Parser.ParseSyntax(source);
        Assert.False(syntaxResult.HasErrors, string.Join(Environment.NewLine, syntaxResult.Diagnostics.Select(d => d.Message)));

        var (parameterizedRoot, parameterDiagnostics) = ParameterDetector.Detect(syntaxResult.Root);
        Assert.DoesNotContain(parameterDiagnostics, diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);

        var implicitResolvedRoot = ImplicitArgumentResolver.Resolve(parameterizedRoot);
        var property = Assert.Single(implicitResolvedRoot.Properties, candidate => candidate.Name == propertyName);
        return Assert.IsType<Algorithm.User>(property.Value);
    }

    private static int PropertyIndex(PropertyDependencySummaryGraph graph, string propertyName)
    {
        Assert.True(graph.TryGetPropertyIndex(propertyName, out var propertyIndex));
        return propertyIndex;
    }
}