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

    // ── An inline open written in a branch body exposes its public members to that branch ──
    //
    // Exposure is a fact about a property's VALUE, never about where the declaration is
    // written (PropertyExposureResolver.ClassifyDeclaredProperty): an inline block in a branch
    // body's open list has no name, so only the branch's own lookup chain can reach it, and its
    // self-contained public members are Exported and visible to the branch exactly like the
    // members of an equivalent named open of an outer library. The branch pattern stays a
    // closed input specification throughout.

    [Fact]
    public void Source_InlineBranchOpen_ExposesMembersToTheOpeningBranch()
    {
        var root = SourceProvenance.ParseValid("F(0) = { open { public Helper = q }\nHelper(5) }\nF(n) = n\nF(0)").Root;
        var family = root.Properties.Single(property => property.Name == "F").Value;
        var library = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(family.Branches[0].Body.Opens)).Algorithm;
        Assert.Equal(PropertyExposure.Exported, Assert.Single(library.Properties).Exposure);
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(root));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([5m], result.Value);
    }

    [Theory]
    // Basic same-branch visibility.
    [InlineData("F(0) = {\n    open {\n        public Helper = 5\n    }\n\n    Helper\n}\n\nF(0)", "5")]
    // A parameterized helper: detection, implicit resolution, and exposure cooperate.
    [InlineData("F(0) = {\n    open {\n        public Helper(x) = x\n    }\n\n    Helper(5)\n}\nF(n) = n\n\nF(0)", "5")]
    // A branch binder reaches an opened helper the way the language already allows: as an
    // explicit argument. The block is isolated from the opener like every open target, so a
    // bare `x` inside it is the helper's own implicit parameter, never a capture of the branch.
    [InlineData("F(0) = 0\nF(n) = {\n    open {\n        public Helper(x) = x\n    }\n\n    Helper(n)\n}\n\nF(5)", "5")]
    [InlineData("F(0) = 0\nF(n) = {\n    open {\n        public Helper = x\n    }\n\n    Helper(n)\n}\n\nF(5)", "5")]
    // The helper's own binder and the branch's binder share a spelling without conflating.
    [InlineData("F(0) = 0\nF(n) = {\n    open {\n        public Helper(n) = n + 1\n    }\n\n    Helper(n * 2)\n}\n\nF(5)", "11")]
    // An inline open inside a nested brace block within the branch exposes to THAT block:
    // an output row, a call argument, a list element, a capture row, a property body.
    [InlineData("F(0) = {\n    { open { public H = 3 }\n      H }\n}\nF(n) = n\n\nF(0)", "3")]
    [InlineData("Apply(f) = f\nF(0) = Apply({ open { public H = 4 }\n  H })\nF(n) = n\n\nF(0)", "4")]
    [InlineData("F(0) = [{ open { public H = 6 }\n  H }]:0\nF(n) = n\n\nF(0)", "6")]
    [InlineData("F(0) = ({ open { public H = 8 }\n  H }, 1)\nF(n) = (n, n)\n\nF(0)", "(8, 1)")]
    [InlineData("F(0) = {\n    G = {\n        open { public H = 1 }\n        H\n    }\n    G\n}\nF(n) = n\n\nF(0)", "1")]
    // An inner clause family's branch opening its own inline block.
    [InlineData("F(0) = {\n  G(0) = {\n    open { public H = 1 }\n    H\n  }\n  G(k) = k\n  G(0)\n}\nF(n) = n\n\nF(0)", "1")]
    // An opened library is exported like an outer library's member, so the branch may hand it
    // out on the algorithm channel exactly as it could hand out an outer library's member.
    [InlineData("Apply(f) = f.Y\nF(0) = {\n    open {\n        public Lib = { public Y = 7 }\n    }\n\n    Apply(Lib)\n}\nF(n) = n\n\nF(0)", "7")]
    public void Source_InlineBranchOpen_ExposesMembersWithinTheOpeningBody(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(expected, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n"));
    }

    [Theory]
    // A sibling branch never acquires the first branch's opened names.
    [InlineData("F(0) = {\n    open {\n        public Helper = 5\n    }\n\n    Helper\n}\nF(1) = Helper\nF(n) = n\n\nF(1)", "Helper", "F")]
    // An inner branch's inline open reaches neither its sibling branch nor the outer branch
    // after the nested family.
    [InlineData("F(0) = {\n  G(0) = {\n    open { public H = 1 }\n    H\n  }\n  G(k) = H\n  G(0)\n}\nF(n) = n\n\nF(0)", "H", "G")]
    [InlineData("F(0) = {\n  G(0) = {\n    open { public H = 1 }\n    H\n  }\n  G(k) = k\n  G(0), H\n}\nF(n) = n, n\n\nF(0)", "H", "F")]
    // A private member of the opened block is not exposed merely because the block is opened.
    [InlineData("F(0) = {\n    open {\n        Secret = 5\n        public Helper = 6\n    }\n\n    Secret\n}\nF(n) = n\n\nF(0)", "Secret", "F")]
    // Visibility of the helper does not reopen the closed branch pattern: an input the pattern
    // does not bind is still diagnosed in the branch's own terms.
    [InlineData("F(0) = {\n    open {\n        public Helper(x) = x\n    }\n\n    Helper(n)\n}\nF(k) = k\n\nF(0)", "n", "F")]
    public void Source_InlineBranchOpen_DoesNotEscapeItsBranch(string source, string identifier, string branchName)
    {
        var parsed = Parser.Parse(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Contains($"Identifier '{identifier}' is used in conditional branch '{branchName}'", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Source_InlineBranchOpen_DoesNotEscapeToTheEnclosingAlgorithm(bool nested)
    {
        // Outside the branch the opened name resolves to nothing: the enclosing body (the root,
        // or a brace algorithm) treats it as its own implicit parameter, while the branch's own
        // reference stays an ordinary lexical resolve and the branch body acquires no parameter.
        var body = "F(0) = {\n    open {\n        public Helper = 5\n    }\n\n    Helper\n}\nF(n) = n\nF(0), Helper";
        var source = nested ? $"Outer = {{\n{body}\n}}\nOuter(7)" : body;
        var root = SourceProvenance.ParseValid(source).Root;
        var owner = nested ? root.Properties.Single(property => property.Name == "Outer").Value : root;
        Assert.Equal(["Helper"], owner.Params);
        var branch = owner.Properties.Single(property => property.Name == "F").Value.Branches[0].Body;
        Assert.Empty(branch.Params);
        Assert.Equal("Helper", Assert.IsType<Expr.Resolve>(Assert.Single(branch.Output)).Name);
        if (nested)
            Assert.Equal("(5, 7)", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Theory]
    [InlineData("public Helper = 5", "Helper", 5)]
    [InlineData("public Helper(x) = x", "Helper(5)", 5)]
    [InlineData("public Helper = x", "Helper(5)", 5)]
    [InlineData("public Helper = x", "Helper", null)]
    [InlineData("public Helper = x", "Math.Abs(Helper)", null)]
    public void Source_InlineBranchOpen_MatchesNamedOuterOpen(string member, string reference, int? expected)
    {
        // The inline block and an equivalent outer library make the SAME decisions inside the
        // branch: the same elaborated branch output (a bare opened helper is never implicitly
        // forwarded, in either form — even under a strict-value demand — so it stays bare) and
        // the same outcome, a value or the same structured zero-argument arity failure. Only the
        // provider's lifetime differs: the inline block exists for this branch alone.
        var named = $"Helpers = {{\n    {member}\n}}\nF(0) = {{\n    open Helpers\n    {reference}\n}}\nF(n) = n\n\nF(0)";
        var inline = $"F(0) = {{\n    open {{\n        {member}\n    }}\n\n    {reference}\n}}\nF(n) = n\n\nF(0)";
        var namedRoot = SourceProvenance.ParseValid(named).Root;
        var inlineRoot = SourceProvenance.ParseValid(inline).Root;
        static Expr BranchOutput(Algorithm root)
            => Assert.Single(root.Properties.Single(property => property.Name == "F").Value.Branches[0].Body.Output);
        Assert.Equal(LeanAstEncoder.EncodeExpr(BranchOutput(namedRoot)), LeanAstEncoder.EncodeExpr(BranchOutput(inlineRoot)));

        var namedResult = Evaluator.RunFlat(new Expr.AlgorithmExpr(namedRoot));
        var inlineResult = Evaluator.RunFlat(new Expr.AlgorithmExpr(inlineRoot));
        if (expected is { } value)
        {
            Assert.Equal([(decimal)value], namedResult.Value);
            Assert.Equal([(decimal)value], inlineResult.Value);
        }
        else
        {
            Assert.True(namedResult.IsError);
            Assert.True(inlineResult.IsError);
            Assert.IsType<EvalError.ArityMismatch>(EvaluatorTestSupport.Innermost(namedResult.Error));
            Assert.IsType<EvalError.ArityMismatch>(EvaluatorTestSupport.Innermost(inlineResult.Error));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void HostBranch_InlineOpen_ExposesMembersThroughTheCompletePipeline(bool familyOwned)
    {
        // Host-built: the branch-owned form a parser would produce, and the family-owned form
        // (Conditional.Opens) only host trees can build, both through the complete internal
        // pipeline INCLUDING exposure resolution — the pass HostConditional_OwnedOpen_IsDetected
        // deliberately stops short of, and the one that used to hide the members.
        var library = Body() with
        {
            Properties = [new Property("Helper", Body(new Expr.Num(5))) { IsPublic = true }],
        };
        var open = new Expr.AlgorithmExpr(library);
        var branchBody = Body(new Expr.Resolve("Helper"));
        var conditional = new Algorithm.Conditional(
            null,
            familyOwned ? [open] : [],
            [
                new CondBranch(new Pattern.LitInt(0), familyOwned ? branchBody : branchBody with { Opens = [open] }),
                new CondBranch(new Pattern.Bind("n"), Body(new Expr.Resolve("n"))),
            ]);
        var call = new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(0)]));
        var root = Body(call) with { Properties = [new Property("F", conditional)] };

        var (detected, diagnostics) = ParameterDetector.Detect(root);
        Assert.Empty(diagnostics);
        var exposed = PropertyExposureResolver.Resolve(ImplicitArgumentResolver.Resolve(detected));

        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(exposed.Properties).Value);
        var opens = familyOwned ? family.Opens : family.Branches[0].Body.Opens;
        var helper = Assert.Single(Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(opens)).Algorithm.Properties);
        Assert.Equal(PropertyExposure.Exported, helper.Exposure);
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(exposed));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([5m], result.Value);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void HostBranch_SharedInlineOpenBlock_ClassifiesOnceAndPreservesSharingInAnyOrder(bool reverse)
    {
        // ONE block node is the open target of two distinct branch regions, a call argument of a
        // third, and the leaf of a binary diamond in a fourth. Its self-contained member
        // classifies Exported at every reach — classification is a pure function of the value,
        // so no region, context, or traversal order can change it — every reach is usable
        // (opened, and handed out on the algorithm channel), and the diamond expands once per
        // distinct node with its sharing preserved.
        var root = SourceProvenance.ParseValid("Apply(f) = f.Helper").Root;
        var library = Body() with
        {
            Properties = [new Property("Helper", Body(new Expr.Num(5))) { IsPublic = true }],
        };
        var shared = new Expr.AlgorithmExpr(library);
        Expr diamond = shared;
        for (var depth = 0; depth < 40; depth++)
            diamond = new Expr.Binary(BinaryOp.Add, diamond, diamond);
        CondBranch[] branches =
        [
            new(new Pattern.LitInt(0), Body(new Expr.Resolve("Helper")) with { Opens = [shared] }),
            new(new Pattern.LitInt(1), Body(new Expr.Resolve("Helper")) with { Opens = [shared] }),
            new(new Pattern.LitInt(2), Body(new Expr.Call(new Expr.Resolve("Apply"), new OutputBundle([shared])))),
            new(new Pattern.LitInt(3), Body(diamond)),
        ];
        if (reverse)
            Array.Reverse(branches);
        root = root with
        {
            Properties = [.. root.Properties, new Property("F", new Algorithm.Conditional(null, [], branches))],
        };
        var observations = new FrontEndTraversalObservations();

        var exposed = PropertyExposureResolver.Resolve(root, observations);

        var family = Assert.IsType<Algorithm.Conditional>(exposed.Properties.Single(property => property.Name == "F").Value);
        Algorithm Branch(int literal) => family.Branches[reverse ? 3 - literal : literal].Body;
        foreach (var literal in new[] { 0, 1 })
        {
            var opened = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(Branch(literal).Opens)).Algorithm;
            Assert.Equal(PropertyExposure.Exported, Assert.Single(opened.Properties).Exposure);
        }
        var argument = Assert.IsType<Expr.AlgorithmExpr>(
            Assert.Single(Assert.IsType<Expr.Call>(Assert.Single(Branch(2).Output)).Args)).Algorithm;
        Assert.Equal(PropertyExposure.Exported, Assert.Single(argument.Properties).Exposure);
        var current = Assert.Single(Branch(3).Output);
        for (var depth = 0; depth < 40; depth++)
        {
            var binary = Assert.IsType<Expr.Binary>(current);
            Assert.Same(binary.Left, binary.Right);
            current = binary.Left;
        }
        var leaf = Assert.IsType<Expr.AlgorithmExpr>(current).Algorithm;
        Assert.Equal(PropertyExposure.Exported, Assert.Single(leaf.Properties).Exposure);
        Assert.InRange(observations.ExposureRewriteExpansions, 40, 60);

        Algorithm Program(int literal) => exposed with
        {
            Output = new OutputBundle([new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(literal)]))]),
        };
        Assert.Equal([5m], Evaluator.RunFlat(new Expr.AlgorithmExpr(Program(0))).Value);
        Assert.Equal([5m], Evaluator.RunFlat(new Expr.AlgorithmExpr(Program(1))).Value);
        Assert.Equal([5m], Evaluator.RunFlat(new Expr.AlgorithmExpr(Program(2))).Value);
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

    // ── Declarations inside a branch body classify under the ONE self-containment rule ──
    //
    // A conditional family exposes no structural members, so nothing DECLARED in a branch body
    // is reachable by name from outside the conditional (the family-level rule, unchanged).
    // Inside the branch a declaration behaves exactly like the same declaration in a
    // parameterized body: a self-contained branch-local library is Exported — openable,
    // dot-accessible, and hand-out-able by the branch and the bodies nested in it — while a
    // member that captures the branch's pattern binder is local-only for the same reason a
    // parameter-capturing member is.

    [Theory]
    // Same-branch nested open, and the parameterized-member form.
    [InlineData("F(0) = {\n    Lib = {\n        public X = 1\n    }\n    G = {\n        open Lib\n        X\n    }\n    G\n}\nF(n) = n\nF(0)", "1")]
    [InlineData("F(0) = {\n    Lib = {\n        public X(n) = n\n    }\n    G = {\n        open Lib\n        X(5)\n    }\n    G\n}\nF(n) = n\nF(0)", "5")]
    // The branch body opening its own declaration, and structural dot access inside the branch.
    [InlineData("F(0) = {\n    open Lib\n    Lib = { public X = 1 }\n    X\n}\nF(n) = n\nF(0)", "1")]
    [InlineData("F(0) = {\n    Lib = { public X = 1 }\n    Lib.X\n}\nF(n) = n\nF(0)", "1")]
    // Nested descendants: two brace levels, an inner clause family's branch, an output-position
    // block, and a call-argument block.
    [InlineData("F(0) = {\n    Lib = { public X = 1 }\n    G = {\n        H = {\n            open Lib\n            X\n        }\n        H\n    }\n    G\n}\nF(n) = n\nF(0)", "1")]
    [InlineData("F(0) = {\n    Lib = { public X = 1 }\n    G(0) = {\n        open Lib\n        X\n    }\n    G(k) = k\n    G(0)\n}\nF(n) = n\nF(0)", "1")]
    [InlineData("F(0) = {\n    Lib = { public X = 1 }\n    { open Lib\n      X }\n}\nF(n) = n\nF(0)", "1")]
    [InlineData("Apply(f) = f\nF(0) = {\n    Lib = { public X = 1 }\n    Apply({ open Lib\n      X })\n}\nF(n) = n\nF(0)", "1")]
    // Handing the library out on the algorithm channel is the branch's own act, exactly as it
    // is for a parameterized body or an inline-open library: a self-contained member stays
    // usable there.
    [InlineData("Apply(f) = f.X\nF(0) = {\n    Lib = { public X = 1 }\n    Apply(Lib)\n}\nF(n) = n\nF(0)", "1")]
    // Branch binders: a binder reaches a branch-local member as an explicit argument, and a
    // binder-capturing declaration is still usable BY NAME inside the branch (lexical capture
    // is ownership-first lookup, which never consults exposure).
    [InlineData("F(0) = 0\nF(n) = {\n    Lib = { public X(k) = k }\n    G = {\n        open Lib\n        X(n)\n    }\n    G\n}\nF(5)", "5")]
    [InlineData("F(0) = 0\nF(n) = {\n    Helper = n + 1\n    G = { Helper }\n    G\n}\nF(4)", "5")]
    public void Source_BranchLocalLibrary_IsUsableWithinTheBranch(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(expected, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n"));
    }

    [Theory]
    // A sibling branch never sees the first branch's library or its members.
    [InlineData("F(0) = {\n    Lib = { public X = 1 }\n    G = {\n        open Lib\n        X\n    }\n    G\n}\nF(1) = X\nF(n) = n\nF(1)", "X", "F")]
    // Declaring Lib does not implicitly open it: a bare member name stays unbound.
    [InlineData("F(0) = {\n    Lib = { public X = 1 }\n    X\n}\nF(n) = n\nF(0)", "X", "F")]
    // Opening a branch-local library does not reopen the closed branch pattern.
    [InlineData("F(0) = {\n    open Lib\n    Lib = { public X(k) = k }\n    X(n)\n}\nF(k) = k\nF(0)", "n", "F")]
    public void Source_BranchLocalLibrary_DoesNotEscapeItsBranch(string source, string identifier, string branchName)
    {
        var parsed = Parser.Parse(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Contains($"Identifier '{identifier}' is used in conditional branch '{branchName}'", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Source_BranchLocalLibrary_IsUnreachableByNameFromOutsideTheBranch()
    {
        // After the branch, neither the library nor its member is visible: the enclosing
        // algorithm treats the names as its own implicit parameters, and a structural or
        // dotted-open path through the family is refused AT THE FAMILY with the family-level
        // reason — the declaration's own (Exported) classification never enters into it.
        var body = "F(0) = {\n    Lib = { public X = 1 }\n    G = {\n        open Lib\n        X\n    }\n    G\n}\nF(n) = n\n";
        var root = SourceProvenance.ParseValid(body + "F(0), X, Lib").Root;
        Assert.Equal(["X", "Lib"], root.Params);
        var declared = root.Properties.Single(property => property.Name == "F").Value.Branches[0].Body
            .Properties.Single(property => property.Name == "Lib");
        Assert.Equal(PropertyExposure.Exported, declared.Exposure);
        Assert.Equal(PropertyExposure.Exported, Assert.Single(declared.Value.Properties).Exposure);

        var structural = Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(body + "F.Lib").Root));
        Assert.True(structural.IsError);
        var structuralError = Assert.IsType<EvalError.LocalOnlyProperty>(EvaluatorTestSupport.Innermost(structural.Error));
        Assert.Equal("Lib", structuralError.PropertyName);
        Assert.Equal(PropertyExposure.LocalOnlyConditionalAlgorithm, structuralError.Exposure);

        // A dotted open through the family provides nothing to the front end (X becomes the
        // opener's own implicit parameter), and the runtime refuses the open at the family.
        // Opens resolve lazily, on the first name lookup that consults them, so the runtime
        // side is pinned on the raw syntax tree, where X is still a bare resolve that forces
        // open resolution.
        const string dottedOpen = "G = {\n    open F.Lib\n    X\n}\nG";
        var opener = SourceProvenance.ParseValid(body + dottedOpen).Root.Properties.Single(property => property.Name == "G").Value;
        Assert.Equal(["X"], opener.Params);
        var dotted = Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseSyntaxValidRoot(body + dottedOpen)));
        Assert.True(dotted.IsError);
        var dottedError = Assert.IsType<EvalError.LocalOnlyProperty>(EvaluatorTestSupport.Innermost(dotted.Error));
        Assert.Equal("Lib", dottedError.PropertyName);
        Assert.Equal(PropertyExposure.LocalOnlyConditionalAlgorithm, dottedError.Exposure);
    }

    [Theory]
    // A member capturing the branch binder is local-only exactly like a parameter-capturing
    // member: hidden from `open` (Unknown name at runtime), refused by dot access and on the
    // algorithm channel with the captured-parameter reason.
    [InlineData("F(0) = 0\nF(n) = {\n    Lib = { public X = n }\n    G = {\n        open Lib\n        X\n    }\n    G\n}\nF(5)", typeof(EvalError.UnknownName))]
    [InlineData("F(0) = 0\nF(n) = {\n    Lib = { public X = n }\n    Lib.X\n}\nF(5)", typeof(EvalError.LocalOnlyProperty))]
    [InlineData("Apply(f) = f.X\nF(0) = 0\nF(n) = {\n    Lib = { public X = n }\n    Apply(Lib)\n}\nF(5)", typeof(EvalError.LocalOnlyProperty))]
    // A private member is not provided by `open` merely because the library is branch-local:
    // the nested body's X is unresolved, so it becomes that body's implicit parameter and the
    // bare `G` fails the ordinary zero-argument arity check.
    [InlineData("F(0) = {\n    Lib = { X = 1 }\n    G = {\n        open Lib\n        X\n    }\n    G\n}\nF(n) = n\nF(0)", typeof(EvalError.ArityMismatch))]
    // Opened callables are never implicitly forwarded, in a branch exactly as anywhere else.
    [InlineData("F(0) = 0\nF(n) = {\n    Lib = { public X = k }\n    G = {\n        open Lib\n        X\n    }\n    G\n}\nF(5)", typeof(EvalError.ArityMismatch))]
    // A nested brace body keeps its own open implicit-parameter list: an unbound `n` in a
    // nested consumer becomes THAT body's implicit parameter (the branch acquires none), so
    // the bare `G` fails the zero-argument arity check exactly as an unforwarded helper does.
    [InlineData("F(0) = {\n    Lib = { public X(k) = k }\n    G = {\n        open Lib\n        X(n)\n    }\n    G\n}\nF(k) = k\nF(0)", typeof(EvalError.ArityMismatch))]
    public void Source_BranchLocalLibrary_KeepsCaptureAndPrivacyRules(string source, Type innermostError)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(root));
        Assert.True(result.IsError);
        var error = EvaluatorTestSupport.Innermost(result.Error);
        Assert.IsType(innermostError, error);
        if (error is EvalError.LocalOnlyProperty localOnly)
            Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, localOnly.Exposure);
    }

    [Fact]
    public void HostBranch_DeclaredLibraryOpenedByNestedBody_IsExportedThroughTheCompletePipeline()
    {
        // Host-built branch body declaring a library and a nested body opening it — the shape a
        // parser would produce — through the complete internal pipeline including exposure.
        var library = Body() with
        {
            Properties = [new Property("X", Body(new Expr.Num(1))) { IsPublic = true }],
        };
        var nested = Body(new Expr.Resolve("X")) with { Opens = [new Expr.Resolve("Lib")] };
        var branchBody = Body(new Expr.Resolve("G")) with
        {
            Properties = [new Property("Lib", library), new Property("G", nested)],
        };
        var conditional = new Algorithm.Conditional(null, [],
        [
            new CondBranch(new Pattern.LitInt(0), branchBody),
            new CondBranch(new Pattern.Bind("n"), Body(new Expr.Resolve("n"))),
        ]);
        var call = new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(0)]));
        var root = Body(call) with { Properties = [new Property("F", conditional)] };

        var (detected, diagnostics) = ParameterDetector.Detect(root);
        Assert.Empty(diagnostics);
        var exposed = PropertyExposureResolver.Resolve(ImplicitArgumentResolver.Resolve(detected));

        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(exposed.Properties).Value);
        var declared = family.Branches[0].Body.Properties.Single(property => property.Name == "Lib");
        Assert.Equal(PropertyExposure.Exported, declared.Exposure);
        Assert.Equal(PropertyExposure.Exported, Assert.Single(declared.Value.Properties).Exposure);
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(exposed));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([1m], result.Value);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void HostBranch_SharedDeclaredLibrary_ClassifiesOnceAndIsUsableInEveryRegion(bool reverse)
    {
        // ONE library node is declared by two branches (each opening it from a shared nested
        // consumer) and by the root (which dot-accesses it). Classification is a pure function
        // of the value: every region sees the same Exported verdict in either order, nothing
        // crosses a region boundary (the branch bodies stay independent rewrites), and the
        // rewrite work stays bounded by distinct nodes.
        var library = Body() with
        {
            Properties = [new Property("X", Body(new Expr.Num(1))) { IsPublic = true }],
        };
        var consumer = Body(new Expr.Resolve("X")) with { Opens = [new Expr.Resolve("Lib")] };
        Algorithm.User BranchBody() => Body(new Expr.Resolve("G")) with
        {
            Properties = [new Property("Lib", library), new Property("G", consumer)],
        };
        CondBranch[] branches = [new(new Pattern.LitInt(0), BranchBody()), new(new Pattern.LitInt(1), BranchBody())];
        if (reverse)
            Array.Reverse(branches);
        Property[] properties =
        [
            new Property("Lib", library),
            new Property("F", new Algorithm.Conditional(null, [], branches)),
        ];
        if (reverse)
            Array.Reverse(properties);
        var root = Body(
            new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(0)])),
            new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(1)])),
            new Expr.DotCall(new Expr.Resolve("Lib"), "X")) with { Properties = properties };
        var observations = new FrontEndTraversalObservations();

        var exposed = PropertyExposureResolver.Resolve(root, observations);

        var family = Assert.IsType<Algorithm.Conditional>(exposed.Properties.Single(property => property.Name == "F").Value);
        foreach (var branch in family.Branches)
        {
            var declared = branch.Body.Properties.Single(property => property.Name == "Lib");
            Assert.Equal(PropertyExposure.Exported, declared.Exposure);
            Assert.Equal(PropertyExposure.Exported, Assert.Single(declared.Value.Properties).Exposure);
        }
        Assert.NotSame(family.Branches[0].Body, family.Branches[1].Body);
        var rootLibrary = exposed.Properties.Single(property => property.Name == "Lib");
        Assert.Equal(PropertyExposure.Exported, Assert.Single(rootLibrary.Value.Properties).Exposure);
        Assert.InRange(observations.ExposureRewriteExpansions, 1, 12);
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(exposed));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([1m, 1m, 1m], result.Value);
    }
}