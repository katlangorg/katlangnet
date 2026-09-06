namespace KatLang.Tests;

public class ConditionalBranchElaborationTests
{
    private static Algorithm.User Body(params Expr[] output)
        => new(null, [], [], [], output);

    [Theory]
    [InlineData("flat", false)]
    [InlineData("flat", true)]
    [InlineData("literal-flat", false)]
    [InlineData("literal-flat", true)]
    [InlineData("literal-group", false)]
    [InlineData("literal-group", true)]
    [InlineData("literal-empty-group", false)]
    [InlineData("literal-empty-group", true)]
    [InlineData("named-group", false)]
    [InlineData("named-group", true)]
    [InlineData("repeated", false)]
    [InlineData("repeated", true)]
    [InlineData("deep", false)]
    [InlineData("deep", true)]
    public void HostBranch_MixedBinderProjection_MatchesExplicitForwarding(string shape, bool strict)
    {
        var rest = new Pattern.Bind("rest") { ParameterKind = ParameterKind.Collecting };
        var items = new Pattern.Bind("items");
        var collectedItems = items with { ParameterKind = ParameterKind.Collecting };
        Pattern.SequenceValue Group(params Pattern[] patterns) => new(patterns);
        var (branchPattern, ordinaryPattern, argument) = shape switch
        {
            "flat" => ((Pattern)rest, (Pattern)rest, "(.sequenceSpread (.param \"rest\"))"),
            "literal-flat" => (Group(new Pattern.LitInt(0), rest), rest, "(.sequenceSpread (.param \"rest\"))"),
            "literal-group" => (Group(new Pattern.LitInt(0), Group(new Pattern.LitString("tag"), rest)),
                Group(Group(rest)), null),
            "literal-empty-group" => (Group(Group(new Pattern.LitInt(0)), rest), Group(Group(), rest), null),
            "named-group" => (Group(new Pattern.LitInt(0), Group(new Pattern.LitString("tag"), collectedItems)),
                Group(Group(collectedItems)), "(.sequenceSpread (.param \"items\"))"),
            "repeated" => (Group(new Pattern.LitInt(0), items, items), Group(items, items), ".param \"items\""),
            "deep" => (Group(new Pattern.LitInt(0), Group(Group(items))), Group(Group(Group(items))), ".param \"items\""),
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
        var body = Body(SourceProvenance.ParseSyntaxValidRoot(strict ? "Math.Abs(Target)" : "Target").Output.ToArray());
        var root = SourceProvenance.ParseSyntaxValidRoot("Target(*items) = items");
        root = root with
        {
            Properties =
            [
                .. root.Properties,
                new Property("Ordinary", Algorithm.ElaborateClauseGroup([new CondBranch(ordinaryPattern, body)])),
                new Property("Branch", new Algorithm.Conditional(null, [], [new CondBranch(branchPattern, body)])),
            ],
        };
        var (detected, detectorDiagnostics) = ParameterDetector.Detect(root);
        Assert.Empty(detectorDiagnostics);
        var diagnostics = new List<Diagnostic>();

        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics);

        var ordinary = resolved.Properties.Single(property => property.Name == "Ordinary").Value;
        var branch = Assert.Single(resolved.Properties.Single(property => property.Name == "Branch").Value.Branches).Body;
        Assert.Empty(branch.Params);
        Assert.Equal(LeanAstEncoder.EncodeExpr(Assert.Single(ordinary.Output)), LeanAstEncoder.EncodeExpr(Assert.Single(branch.Output)));
        var reference = strict
            ? Assert.Single(Assert.IsType<Expr.DotCall>(Assert.Single(branch.Output)).Args!)
            : Assert.Single(branch.Output);
        if (argument is null)
            Assert.IsType<Expr.Resolve>(reference);
        else
            Assert.Equal(argument, LeanAstEncoder.EncodeExpr(Assert.Single(Assert.IsType<Expr.Call>(reference).Args)));
        Assert.Equal(strict && argument is null ? 2 : 0, diagnostics.Count);
        Assert.All(diagnostics, diagnostic =>
        {
            Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
            Assert.Contains("'items'", diagnostic.Message, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void Source_InlineBranchOpen_RetainsCurrentLocalOnlyExposure()
    {
        var root = SourceProvenance.ParseValid("F(0) = { open { public Helper = q }\nHelper(5) }\nF(n) = n\nF(0)").Root;
        var family = root.Properties.Single(property => property.Name == "F").Value;
        var library = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(family.Branches[0].Body.Opens)).Algorithm;
        Assert.Equal(PropertyExposure.LocalOnlyConditionalAlgorithm, Assert.Single(library.Properties).Exposure);
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(root));
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        Assert.IsType<EvalError.UnknownName>(error);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void HostConditional_RootOrExpression_UsesBranchDetection(bool expressionPosition)
    {
        var conditional = new Algorithm.Conditional(null, [],
            [new CondBranch(new Pattern.Bind("n"), Body(new Expr.Resolve("n")))]);
        Algorithm root = expressionPosition
            ? Body(new Expr.AlgorithmExpr(conditional)) with
            {
                Properties = [new Property("n", Body(new Expr.Num(99)))],
            }
            : conditional;

        var (detected, diagnostics) = ParameterDetector.Detect(root);

        Assert.Empty(diagnostics);
        var family = expressionPosition
            ? Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(detected.Output)).Algorithm
            : detected;
        Assert.IsType<Expr.Param>(Assert.Single(Assert.Single(family.Branches).Body.Output));
    }

    [Fact]
    public void HostConditional_Expression_UsesClosedBranchResolution()
    {
        var root = SourceProvenance.ParseValid("A = n + 1").Root;
        var conditional = new Algorithm.Conditional(null, [],
            [new CondBranch(new Pattern.Bind("n"), Body(new Expr.Resolve("A")))]);
        root = root with { Output = new OutputBundle([new Expr.AlgorithmExpr(conditional)]) };

        var resolved = ImplicitArgumentResolver.Resolve(root);

        var family = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(resolved.Output)).Algorithm;
        var branch = Assert.Single(family.Branches).Body;
        Assert.Empty(branch.Params);
        var call = Assert.IsType<Expr.Call>(Assert.Single(branch.Output));
        Assert.Equal("n", Assert.IsType<Expr.Param>(Assert.Single(call.Args)).Name);
    }

    [Theory]
    [InlineData("Host(4)")]
    [InlineData("{ G(x) = Host(x)\nG(4) }")]
    [InlineData("(Host(4))")]
    [InlineData("[Host(4)]:0")]
    public void Source_ClosedBranch_ResolvesConfiguredHostOperations(string expression)
    {
        var calls = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Host", (arguments, _) =>
            {
                calls++;
                return arguments[0];
            }, "value")),
        };

        var result = KatLangEngine.Run($"F(0) = {expression}\nF(n) = n\nF(0)", options);

        Assert.Equal("4", Assert.IsType<RunResult.Success>(result).ToDisplayString());
        Assert.Equal(1, calls);
    }

    [Theory]
    [InlineData("n = 99\nF(0) = { G(0) = { H(0) = 0\nH(n) = n\nH(5) }\nG(k) = k\nG(0) }\nF(k) = k\nF(0)", "5")]
    [InlineData("n = 99\nF(0) = { 1, { G(0) = 0\nG(n) = n\nG(5) } }\nF(k) = k, k\nF(0)", "(1, 5)")]
    [InlineData("Outer(y) = { F(0) = { 1, { G(x) = x + y\nG(2) } }\nF(k) = k, k\nF(0) }\nOuter(3)", "(1, 5)")]
    [InlineData("Outer = { y, { F(0) = { G(x) = x + y\nG(2) }\nF(k) = k\nF(0) } }\nOuter(3)", "(3, 5)")]
    [InlineData("Outer(y) = { F(0) = y\nF(k) = k\nF(0) }\nOuter(5)", "5")]
    [InlineData("Lib = { public Inc(x) = x + 1 }\nF(0) = { open Lib\nG(0) = Inc(4)\nG(n) = n\nG(0) }\nF(n) = n\nF(0)", "5")]
    [InlineData("F(0) = Math.Abs(-5)\nF(n) = count([n])\nF(0), F(3)", "5\n1")]
    [InlineData("A = x + y\nF(0, ((x, y), x)) = Math.Abs(A)\nF(k, rest) = 0\nF(0, ((2, 3), 2))", "5")]
    [InlineData("A = x + 1\nF(0, ('tag', x)) = A\nF(k, rest) = 0\nF(0, ('tag', 4))", "5")]
    [InlineData("Apply(f) = f(4)\nF(0) = Apply({ x + 1 })\nF(n) = n\nF(0)", "5")]
    public void Source_NestedBodies_RespectScopeAndClosedInputs(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(expected, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n"));
    }

    [Theory]
    [InlineData("Apply(f) = f\nF(0) = Apply({ G(x) = missing\nG(1) })\nF(n) = n")]
    [InlineData("F(0) = (1, { G(x) = missing\nG(1) })\nF(n) = (n, n)")]
    [InlineData("F(0) = [{ G(x) = missing\nG(1) }]\nF(n) = [n]")]
    [InlineData("F(0) = { 1, { G(0) = missing\nG(n) = n\nG(1) } }\nF(n) = n, n")]
    public void Source_NestedClosedBody_DiagnosticSurvivesExpressionContainers(string source)
    {
        var parsed = Parser.Parse(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Contains("'missing'", diagnostic.Message, StringComparison.Ordinal);
        Assert.True(diagnostic.Span!.StartLineNumber > 0);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void Detector_SharedBlock_DiagnosesOnceAcrossParents(bool branchBody, bool reverse)
    {
        var block = SourceProvenance.ParseSyntaxValidRoot("Bad(x) = missing\nBad(1)");
        var shared = new Expr.AlgorithmExpr(block);
        Expr diamond = shared;
        for (var depth = 0; depth < 40; depth++)
            diamond = new Expr.Binary(BinaryOp.Add, diamond, diamond);
        Expr[] output =
        [
            new Expr.ListLiteral(new OutputBundle([shared])),
            new Expr.Capture(new OutputBundle([shared])),
            new Expr.Call(new Expr.Resolve("count"), new OutputBundle([shared])),
            new Expr.AlgorithmExpr(block),
            diamond,
        ];
        if (reverse)
            Array.Reverse(output);
        Algorithm root = Body(output);
        if (branchBody)
            root = Body() with
            {
                Properties = [new Property("Branch", new Algorithm.Conditional(null, [],
                    [new CondBranch(new Pattern.LitInt(0), root)]))],
            };
        var observations = new FrontEndTraversalObservations();

        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(root, observations: observations);

        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Contains("'missing'", diagnostic.Message, StringComparison.Ordinal);
        Assert.InRange(observations.DetectorRewriteExpansions, 40, 60);
        var rewritten = (branchBody
            ? Assert.Single(Assert.Single(detected.Properties).Value.Branches).Body.Output
            : detected.Output).ToArray();
        if (reverse)
            Array.Reverse(rewritten);
        var listBlock = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(Assert.IsType<Expr.ListLiteral>(rewritten[0]).Items));
        var captureBlock = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(Assert.IsType<Expr.Capture>(rewritten[1]).Body));
        var argumentBlock = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(Assert.IsType<Expr.Call>(rewritten[2]).Args));
        Assert.Same(listBlock, captureBlock);
        Assert.Same(listBlock, argumentBlock);
        Assert.Same(listBlock.Algorithm, Assert.IsType<Expr.AlgorithmExpr>(rewritten[3]).Algorithm);
        var current = rewritten[4];
        for (var depth = 0; depth < 40; depth++)
        {
            var binary = Assert.IsType<Expr.Binary>(current);
            Assert.Same(binary.Left, binary.Right);
            current = binary.Left;
        }
        Assert.Same(listBlock, current);
    }

    [Theory]
    [InlineData(false, false, false)]
    [InlineData(false, true, false)]
    [InlineData(true, false, false)]
    [InlineData(true, true, false)]
    [InlineData(false, false, true)]
    [InlineData(false, true, true)]
    [InlineData(true, false, true)]
    [InlineData(true, true, true)]
    public void Detector_SharedBlock_SeparatesBindingRegions(bool branches, bool reverse, bool bothInvalid)
    {
        var block = new Expr.AlgorithmExpr(SourceProvenance.ParseSyntaxValidRoot("Inner(x) = y\nInner(1)"));
        var firstPattern = new Pattern.Bind(bothInvalid ? "other" : "y");
        var secondPattern = new Pattern.Bind("z");
        Algorithm CreateRegion(Pattern pattern) => branches
            ? new Algorithm.Conditional(null, [], [new CondBranch(pattern, Body(block))])
            : Algorithm.ElaborateClauseGroup([new CondBranch(pattern, Body(block))]);
        Property[] properties =
        [
            new Property("First", CreateRegion(firstPattern)),
            new Property("Second", CreateRegion(secondPattern)),
        ];
        if (reverse)
            Array.Reverse(properties);

        var (detected, diagnostics) = ParameterDetector.Detect(Body() with { Properties = properties });

        Assert.Equal(bothInvalid ? 2 : 1, diagnostics.Count);
        Assert.All(diagnostics, diagnostic => Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code));
        Algorithm Nested(string name)
        {
            var region = detected.Properties.Single(property => property.Name == name).Value;
            if (branches)
                region = Assert.Single(region.Branches).Body;
            return Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(region.Output)).Algorithm;
        }
        var first = Nested("First");
        var second = Nested("Second");
        Assert.NotSame(first, second);
        var firstReference = Assert.Single(Assert.Single(first.Properties).Value.Output);
        if (bothInvalid)
            Assert.IsType<Expr.Resolve>(firstReference);
        else
            Assert.IsType<Expr.Param>(firstReference);
        Assert.IsType<Expr.Resolve>(Assert.Single(Assert.Single(second.Properties).Value.Output));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void HostBranch_EmptyGroup_PreservesExplicitListForwarding(bool strict)
    {
        var expression = strict ? "Math.Abs(Target)" : "Target";
        var root = SourceProvenance.ParseSyntaxValidRoot("Target(*items) = items");
        var pattern = new Pattern.SequenceValue(
        [
            new Pattern.SequenceValue([]),
            new Pattern.Bind("rest") { ParameterKind = ParameterKind.Collecting },
        ]);
        var body = Body(SourceProvenance.ParseSyntaxValidRoot(expression).Output.ToArray());
        var ordinary = Algorithm.ElaborateClauseGroup([new CondBranch(pattern, body)]);
        var conditional = new Algorithm.Conditional(null, [],
            [new CondBranch(pattern, body)]);
        root = root with
        {
            Properties = [.. root.Properties, new Property("Ordinary", ordinary), new Property("Branch", conditional)],
        };
        var (detected, detectorDiagnostics) = ParameterDetector.Detect(root);
        Assert.Empty(detectorDiagnostics);
        var diagnostics = new List<Diagnostic>();

        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics);

        var ordinaryOutput = resolved.Properties.Single(property => property.Name == "Ordinary").Value.Output;
        var branch = Assert.IsType<Algorithm.Conditional>(
            resolved.Properties.Single(property => property.Name == "Branch").Value).Branches[0].Body;
        Assert.Empty(branch.Parameters);
        Expr Reference(Expr output) => strict
            ? Assert.Single(Assert.IsType<Expr.DotCall>(output).Args!)
            : output;
        Assert.IsType<Expr.Resolve>(Reference(Assert.Single(ordinaryOutput)));
        Assert.IsType<Expr.Resolve>(Reference(Assert.Single(branch.Output)));
        Assert.Equal(strict ? 2 : 0, diagnostics.Count);
        Assert.All(diagnostics, diagnostic => Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code));
    }

    [Fact]
    public void HostConditional_OwnedOpen_IsDetected()
    {
        var library = Body() with
        {
            Properties =
            [
                new Property("Helper", Body(new Expr.Resolve("q"))) { IsPublic = true },
                new Property("Forward", Body(new Expr.Resolve("Helper"))) { IsPublic = true },
            ],
        };
        var conditional = new Algorithm.Conditional(null, [new Expr.AlgorithmExpr(library)],
            [new CondBranch(new Pattern.LitInt(0), Body(
                new Expr.Call(new Expr.Resolve("Forward"), new OutputBundle([new Expr.Num(5)]))))]);
        var root = Body() with { Properties = [new Property("Branch", conditional)] };

        var (detected, diagnostics) = ParameterDetector.Detect(root);

        Assert.Empty(diagnostics);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(detected.Properties).Value);
        var opened = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(family.Opens)).Algorithm;
        var helper = opened.Properties.Single(property => property.Name == "Helper").Value;
        Assert.Equal(["q"], helper.Params);
        Assert.IsType<Expr.Param>(Assert.Single(helper.Output));

        var resolved = ImplicitArgumentResolver.Resolve(detected);
        family = Assert.IsType<Algorithm.Conditional>(Assert.Single(resolved.Properties).Value);
        opened = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(family.Opens)).Algorithm;
        var forward = opened.Properties.Single(property => property.Name == "Forward").Value;
        Assert.Equal(["q"], forward.Params);
        Assert.IsType<Expr.Call>(Assert.Single(forward.Output));
        var call = new Expr.Call(new Expr.Resolve("Branch"), new OutputBundle([new Expr.Num(0)]));
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(resolved with { Output = new OutputBundle([call]) }));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([5m], result.Value);
    }
}