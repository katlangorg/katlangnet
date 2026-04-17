namespace KatLang.Tests;

public class ParameterDetectorTests
{
    private static Algorithm ParseAndDetect(string source)
    {
        var result = Parser.ParseSyntax(source);
        var (detected, _) = ParameterDetector.Detect(result.Root);
        return detected;
    }

    [Fact]
    public void Detect_NoParameters_EmptyParamList()
    {
        var ast = ParseAndDetect("1 + 2");
        Assert.Empty(ast.Params);
    }

    [Fact]
    public void Detect_SingleLowercaseIdentifier_BecomesParam()
    {
        var ast = ParseAndDetect("x + 1");

        Assert.Single(ast.Params);
        Assert.Equal("x", ast.Params[0]);
        var binary = Assert.IsType<Expr.Binary>(ast.Output[0]);
        Assert.IsType<Expr.Param>(binary.Left);
    }

    [Fact]
    public void Detect_MultipleLowercaseIdentifiers_AllBecomeParams()
    {
        var ast = ParseAndDetect("x + y");

        Assert.Equal(2, ast.Params.Count);
        Assert.Contains("x", ast.Params);
        Assert.Contains("y", ast.Params);
    }

    [Fact]
    public void Detect_ParamsInOrderOfFirstAppearance()
    {
        var ast = ParseAndDetect("z + a + m");
        Assert.Equal(["z", "a", "m"], ast.Params);
    }

    [Fact]
    public void Detect_UppercaseIdentifier_BecomesParam()
    {
        var ast = ParseAndDetect("X + 1");

        Assert.Equal(["X"], ast.Params);
        var binary = Assert.IsType<Expr.Binary>(ast.Output[0]);
        Assert.IsType<Expr.Param>(binary.Left);
    }

    [Fact]
    public void Detect_LocalProperty_NotAParam()
    {
        var source = """
            x = 5
            x
            """;
        var ast = ParseAndDetect(source);

        Assert.Empty(ast.Params);
        var resolve = Assert.IsType<Expr.Resolve>(ast.Output[0]);
        Assert.Equal("x", resolve.Name);
    }

    [Fact]
    public void Detect_PropertyBody_HasOwnParams()
    {
        var ast = ParseAndDetect("Add = a + b");

        Assert.Empty(ast.Params);
        var propBody = ast.Properties[0].Value;
        Assert.Equal(2, propBody.Params.Count);
        Assert.Contains("a", propBody.Params);
        Assert.Contains("b", propBody.Params);
    }

    [Fact]
    public void Detect_PropertyBodySeesParentProperty()
    {
        var source = """
            X = 5
            Y = X + x
            """;
        var ast = ParseAndDetect(source);

        var propY = ast.Properties[1].Value;
        Assert.Single(propY.Params);
        Assert.Equal("x", propY.Params[0]);

        var binary = Assert.IsType<Expr.Binary>(propY.Output[0]);
        Assert.IsType<Expr.Resolve>(binary.Left);
        Assert.IsType<Expr.Param>(binary.Right);
    }

    [Fact]
    public void Detect_NestedBlock_HasOwnScope()
    {
        var ast = ParseAndDetect("{x + 1}");

        var block = Assert.IsType<Expr.Block>(ast.Output[0]);
        Assert.Single(block.Algorithm.Params);
        Assert.Equal("x", block.Algorithm.Params[0]);
    }

    [Fact]
    public void Detect_NestedBlock_CapturesOuterParamWithoutAddingLocalParam()
    {
        var source = """
            OccurrenceCount(values, target) = filter(values, {item == target}).count
            """;
        var ast = ParseAndDetect(source);

        var occurrenceCount = Assert.Single(ast.Properties).Value;
        Assert.Equal(["values", "target"], occurrenceCount.Params);

        var countCall = Assert.IsType<Expr.DotCall>(Assert.Single(occurrenceCount.Output));
        var filterCall = Assert.IsType<Expr.Call>(countCall.Target);
        Assert.Empty(filterCall.Args.Params);

        var valuesArg = Assert.IsType<Expr.Param>(filterCall.Args.Output[0]);
        Assert.Equal("values", valuesArg.Name);

        var predicateBlock = Assert.IsType<Expr.Block>(filterCall.Args.Output[1]);
        Assert.Single(predicateBlock.Algorithm.Params);
        Assert.Equal("item", predicateBlock.Algorithm.Params[0]);

        var predicate = Assert.IsType<Expr.Binary>(Assert.Single(predicateBlock.Algorithm.Output));
        var itemParam = Assert.IsType<Expr.Param>(predicate.Left);
        var targetParam = Assert.IsType<Expr.Param>(predicate.Right);
        Assert.Equal("item", itemParam.Name);
        Assert.Equal("target", targetParam.Name);
    }

    [Fact]
    public void Detect_ImplicitOuterOutputOwnership_BelongsToEnclosingAlgorithm()
    {
        var ast = ParseAndDetect(
            """
            Algo = {
                Prop = x + 1
                x
            }
            """);

        var algo = Assert.IsType<Algorithm.User>(Assert.Single(ast.Properties).Value);
        Assert.Equal(["x"], algo.Params);

        var prop = Assert.IsType<Algorithm.User>(Assert.Single(algo.Properties).Value);
        Assert.Empty(prop.Params);
        var binary = Assert.IsType<Expr.Binary>(Assert.Single(prop.Output));
        Assert.Equal("x", Assert.IsType<Expr.Param>(binary.Left).Name);
    }

    [Fact]
    public void Detect_ExplicitOuterOutputOwnership_MatchesImplicitOwnership()
    {
        var ast = ParseAndDetect(
            """
            Algo(x) = {
                Prop = x + 1
                x
            }
            """);

        var algo = Assert.IsType<Algorithm.User>(Assert.Single(ast.Properties).Value);
        Assert.Equal(["x"], algo.Params);

        var prop = Assert.IsType<Algorithm.User>(Assert.Single(algo.Properties).Value);
        Assert.Empty(prop.Params);
        var binary = Assert.IsType<Expr.Binary>(Assert.Single(prop.Output));
        Assert.Equal("x", Assert.IsType<Expr.Param>(binary.Left).Name);
    }

    [Fact]
    public void Detect_NestedPropertyOwnsIdentifier_WhenOuterOutputDoesNotUseIt()
    {
        var ast = ParseAndDetect(
            """
            Algo = {
                Prop = x + 1
                7
            }
            """);

        var algo = Assert.IsType<Algorithm.User>(Assert.Single(ast.Properties).Value);
        Assert.Empty(algo.Params);

        var prop = Assert.IsType<Algorithm.User>(Assert.Single(algo.Properties).Value);
        Assert.Equal(["x"], prop.Params);
    }

    [Fact]
    public void Detect_CallArgsInBraces_IsParametrized()
    {
        // F{x + 1} desugars to F({x + 1}).  The brace content is an Expr.Block
        // whose inner algorithm has params detected (x).
        var ast = ParseAndDetect("F{x + 1}");

        var call = Assert.IsType<Expr.Call>(ast.Output[0]);
        Assert.Empty(call.Args.Params); // outer wrapper is non-parametrized
        var block = Assert.IsType<Expr.Block>(call.Args.Output[0]);
        Assert.Single(block.Algorithm.Params);
        Assert.Equal("x", block.Algorithm.Params[0]);
    }

    [Fact]
    public void Detect_CallArgsInParens_NotParametrized()
    {
        var ast = ParseAndDetect("F(x + 1)");

        // Both F and x are unknown → become params of the enclosing algorithm
        // F appears first, x second. Parenthesized args are non-parametrized.
        Assert.Equal(["F", "x"], ast.Params);
        var call = Assert.IsType<Expr.Call>(ast.Output[0]);
        Assert.Empty(call.Args.Params);
        Assert.IsType<Expr.Param>(call.Function);
        var binary = Assert.IsType<Expr.Binary>(call.Args.Output[0]);
        Assert.IsType<Expr.Param>(binary.Left);
    }

    [Fact]
    public void Detect_SameParamUsedMultipleTimes_OnlyOnceInList()
    {
        var ast = ParseAndDetect("x + x + x");

        Assert.Single(ast.Params);
        Assert.Equal("x", ast.Params[0]);
    }

    [Fact]
    public void Detect_UnaryOperand_ParamDetected()
    {
        var ast = ParseAndDetect("-x");

        Assert.Single(ast.Params);
        var unary = Assert.IsType<Expr.Unary>(ast.Output[0]);
        Assert.IsType<Expr.Param>(unary.Operand);
    }

    [Fact]
    public void Detect_IndexTarget_ParamDetected()
    {
        var ast = ParseAndDetect("arr:i");

        Assert.Equal(2, ast.Params.Count);
        var index = Assert.IsType<Expr.Index>(ast.Output[0]);
        Assert.IsType<Expr.Param>(index.Target);
        Assert.IsType<Expr.Param>(index.Selector);
    }

    [Fact]
    public void Detect_DotCallTarget_ParamDetected()
    {
        var ast = ParseAndDetect("x.arity");

        Assert.Single(ast.Params);
        var dotCall = Assert.IsType<Expr.DotCall>(ast.Output[0]);
        Assert.IsType<Expr.Param>(dotCall.Target);
    }

    [Fact]
    public void Detect_CombineExpr_ParamsFromBothSides()
    {
        var ast = ParseAndDetect("a; b");

        Assert.Equal(2, ast.Params.Count);
        var combine = Assert.IsType<Expr.Combine>(ast.Output[0]);
        Assert.IsType<Expr.Param>(combine.Left);
        Assert.IsType<Expr.Param>(combine.Right);
    }

    [Fact]
    public void Detect_CallFunction_ParamDetected()
    {
        var ast = ParseAndDetect("f(1)");

        Assert.Single(ast.Params);
        var call = Assert.IsType<Expr.Call>(ast.Output[0]);
        Assert.IsType<Expr.Param>(call.Function);
    }

    [Fact]
    public void Detect_SelfIdentifier_IsAParam()
    {
        // "self" is now just an ordinary identifier, so it becomes a parameter.
        var ast = ParseAndDetect("self");
        Assert.Single(ast.Params);
        Assert.Equal("self", ast.Params[0]);
    }

    [Fact]
    public void Detect_NumberExpr_NotAParam()
    {
        var ast = ParseAndDetect("42");
        Assert.Empty(ast.Params);
    }

    [Fact]
    public void Detect_MathResolve_NotAParam()
    {
        var ast = ParseAndDetect("Math.Pi + x");
        Assert.Single(ast.Params);
        Assert.Equal("x", ast.Params[0]);
        var binary = Assert.IsType<Expr.Binary>(ast.Output[0]);
        var dotCall = Assert.IsType<Expr.DotCall>(binary.Left);
        Assert.IsType<Expr.Resolve>(dotCall.Target);
        Assert.Equal("Math", ((Expr.Resolve)dotCall.Target).Name);
        Assert.IsType<Expr.Param>(binary.Right);
    }

    [Fact]
    public void Detect_ComplexExample_CorrectParams()
    {
        var source = """
            Numbers = 3, 5, 9
            Add = a + 1, total + Numbers:a
            Add
            """;
        var ast = ParseAndDetect(source);

        Assert.Empty(ast.Params);

        var addProp = ast.Properties[1].Value;
        Assert.Equal(2, addProp.Params.Count);
        Assert.Contains("a", addProp.Params);
        Assert.Contains("total", addProp.Params);
    }

    // â”€â”€ Grace operator parameter reordering tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Detect_PrefixGrace_MovesParamLeft()
    {
        // Without grace: first-appearance order is [b, a]
        // With ~a: a has weight -1, moves left â†’ [a, b]
        var ast = ParseAndDetect("b + ~a");
        Assert.Equal(["a", "b"], ast.Params);
    }

    [Fact]
    public void Detect_PostfixGrace_MovesParamRight()
    {
        // Without grace: first-appearance order is [a, b]
        // With a~: a has weight +1, moves right â†’ [b, a]
        var ast = ParseAndDetect("a~ + b");
        Assert.Equal(["b", "a"], ast.Params);
    }

    [Fact]
    public void Detect_GraceAtBoundary_StaysInPlace()
    {
        // a is already first, ~a can't move further left
        var ast = ParseAndDetect("~a + b");
        Assert.Equal(["a", "b"], ast.Params);
    }

    [Fact]
    public void Detect_DoublePrefixGrace_MovesTwoPositions()
    {
        // First-appearance order: [c, b, a]
        // ~~a: weight -2, moves a two positions left â†’ [a, c, b]
        var ast = ParseAndDetect("c + b + ~~a");
        Assert.Equal(["a", "c", "b"], ast.Params);
    }

    [Fact]
    public void Detect_AccumulatedGraceWeights_SumAcrossReferences()
    {
        // First-appearance order: [a, b]
        // ~a appears once (weight -1), then a~ appears once (weight +1)
        // Total weight for a: -1 + 1 = 0 â†’ no movement
        var ast = ParseAndDetect("~a + b + a~");
        Assert.Equal(["a", "b"], ast.Params);
    }

    [Fact]
    public void Detect_GraceStrippedFromAST()
    {
        // After detection, Grace nodes should be stripped and replaced with Param
        var ast = ParseAndDetect("~x + 1");
        Assert.Single(ast.Params);
        Assert.Equal("x", ast.Params[0]);

        var binary = Assert.IsType<Expr.Binary>(ast.Output[0]);
        Assert.IsType<Expr.Param>(binary.Left);
    }

    [Fact]
    public void Detect_GraceInPropertyBody_ReordersPropertyParams()
    {
        var source = """
            F = b + ~a * 10
            F
            """;
        var ast = ParseAndDetect(source);

        var fProp = ast.Properties[0].Value;
        Assert.Equal(["a", "b"], fProp.Params);
    }

    [Fact]
    public void Detect_ThreeParams_PostfixMovesMiddleToEnd()
    {
        // First-appearance order: [a, b, c]
        // b~: weight +1, moves b right â†’ [a, c, b]
        var ast = ParseAndDetect("a + b~ + c");
        Assert.Equal(["a", "c", "b"], ast.Params);
    }

    [Fact]
    public void Detect_NoGrace_PreservesFirstAppearanceOrder()
    {
        var ast = ParseAndDetect("a + b + c");
        Assert.Equal(["a", "b", "c"], ast.Params);
    }

    // â”€â”€ Opens-aware parameter detection tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Detect_OpenPublicProperty_NotAParam()
    {
        var source = """
            Lib = (public inc = x + 1)
            open Lib
            inc
            """;
        var ast = ParseAndDetect(source);

        // "inc" is visible through opens (public property of Lib) â†’ not a param
        Assert.Empty(ast.Params);
        Assert.IsType<Expr.Resolve>(ast.Output[0]);
    }

    [Fact]
    public void Detect_OpenPrivateProperty_StillAParam()
    {
        var source = """
            Lib = (inc = x + 1)
            open Lib
            inc + 1
            """;
        var ast = ParseAndDetect(source);

        // "inc" is private in Lib â†’ not visible through opens â†’ becomes a param
        Assert.Single(ast.Params);
        Assert.Equal("inc", ast.Params[0]);
    }

    [Fact]
    public void Detect_OpenMultipleLibraries_CollectsFromAll()
    {
        var source = """
            A = (public foo = 1)
            B = (public bar = 2)
            open A, B
            foo + bar + z
            """;
        var ast = ParseAndDetect(source);

        // foo and bar visible through opens, only z is a param
        Assert.Single(ast.Params);
        Assert.Equal("z", ast.Params[0]);
    }

    [Fact]
    public void Detect_OpenCombine_CollectsFromBothSides()
    {
        var source = """
            A = (public foo = 1)
            B = (public bar = 2)
            open A; B
            foo + bar + z
            """;
        var ast = ParseAndDetect(source);

        // Combine(A, B) â†’ collects public props from both
        Assert.Single(ast.Params);
        Assert.Equal("z", ast.Params[0]);
    }

    [Fact]
    public void Detect_OpenPropertyBody_InheritsOpenNames()
    {
        // Child property body should see names from parent's opens
        var source = """
            Lib = (public val = 42)
            open Lib
            F = val + 1
            F
            """;
        var ast = ParseAndDetect(source);

        // F's body: "val" is visible (from parent's opens)
        // F should have no params
        var fProp = ast.Properties[1].Value; // Properties[0] = Lib, Properties[1] = F
        Assert.Empty(fProp.Params);
    }

    [Fact]
    public void Detect_OpenDotPath_ResolvesPublicIntermediate()
    {
        var source = """
            Outer = (public Inner = (public val = 42))
            open Outer.Inner
            val
            """;
        var ast = ParseAndDetect(source);

        // val is visible through open Outer.Inner -> not a param
        Assert.Empty(ast.Params);
        Assert.IsType<Expr.Resolve>(ast.Output[0]);
    }

    [Fact]
    public void Detect_OpenDotPath_PrivateIntermediate_StillAParam()
    {
        var source = """
            Outer = (Inner = (public val = 42))
            open Outer.Inner
            val + 1
            """;
        var ast = ParseAndDetect(source);

        // Inner is private â†’ Outer.Inner can't be resolved â†’ val not suppressed â†’ param
        Assert.Single(ast.Params);
        Assert.Equal("val", ast.Params[0]);
    }
    // ── Ordinary clause elaboration ────────────────────────────────────────

    [Fact]
    public void Detect_OrdinaryClause_DeclaredParamsPreserveIgnoredBinder()
    {
        var source = "K(a, b) = a";
        var ast = ParseAndDetect(source);

        var user = Assert.IsType<Algorithm.User>(ast.Properties[0].Value);
        Assert.Equal(["a", "b"], user.Params);

        var param = Assert.IsType<Expr.Param>(user.Output[0]);
        Assert.Equal("a", param.Name);
    }

    [Fact]
    public void Detect_OrdinaryClause_SingleBinderDeclaresParam()
    {
        var source = "Id(x) = x";
        var ast = ParseAndDetect(source);

        var user = Assert.IsType<Algorithm.User>(ast.Properties[0].Value);
        Assert.Equal(["x"], user.Params);

        var param = Assert.IsType<Expr.Param>(user.Output[0]);
        Assert.Equal("x", param.Name);
    }

    [Fact]
    public void Detect_OrdinaryClause_SingleHigherOrderBinderRemainsDeclaredParam()
    {
        var source = "Apply(f) = f(4)";
        var ast = ParseAndDetect(source);

        var user = Assert.IsType<Algorithm.User>(ast.Properties[0].Value);
        Assert.Equal(["f"], user.Params);

        var call = Assert.IsType<Expr.Call>(user.Output[0]);
        var function = Assert.IsType<Expr.Param>(call.Function);
        Assert.Equal("f", function.Name);
        Assert.IsType<Expr.Num>(call.Args.Output[0]);
    }

    [Fact]
    public void Detect_OrdinaryClause_HigherOrderBinderRemainsDeclaredParam()
    {
        var source = "Choose(x, predicate) = if(predicate(x), x, 0)";
        var ast = ParseAndDetect(source);

        var user = Assert.IsType<Algorithm.User>(ast.Properties[0].Value);
        Assert.Equal(["x", "predicate"], user.Params);

        var ifCall = Assert.IsType<Expr.Call>(user.Output[0]);
        Assert.IsType<Expr.Resolve>(ifCall.Function);

        var predicateCall = Assert.IsType<Expr.Call>(ifCall.Args.Output[0]);
        var predicateParam = Assert.IsType<Expr.Param>(predicateCall.Function);
        Assert.Equal("predicate", predicateParam.Name);
        Assert.IsType<Expr.Param>(predicateCall.Args.Output[0]);
        Assert.IsType<Expr.Param>(ifCall.Args.Output[1]);
        Assert.IsType<Expr.Num>(ifCall.Args.Output[2]);
    }

    // ── Conditional branch: full-input-specification rule ──────────────────

    [Fact]
    public void Detect_ConditionalBranch_BindersBecomeParm_NoExtraParams()
    {
        // Pattern binders (a, b) become Expr.Param.
        // The branch body's Algorithm.Params must be empty (no implicit params).
        var source = "K((a), b) = a + b";
        var ast = ParseAndDetect(source);

        var cond = Assert.IsType<Algorithm.Conditional>(ast.Properties[0].Value);
        var branch = cond.Branches[0];

        // Branch body has no implicit params
        Assert.Empty(branch.Body.Params);

        // Output contains Param nodes for pattern binders
        var binary = Assert.IsType<Expr.Binary>(branch.Body.Output[0]);
        Assert.IsType<Expr.Param>(binary.Left);
        Assert.IsType<Expr.Param>(binary.Right);
    }

    [Fact]
    public void Detect_ConditionalBranch_FreeIdNotBound_StaysResolve()
    {
        // Free identifier 'Rate' is a sibling property → stays as Expr.Resolve, not Expr.Param
        var source = """
            Rate = 2
            F((x)) = x * Rate
            """;
        var ast = ParseAndDetect(source);

        var cond = Assert.IsType<Algorithm.Conditional>(ast.Properties[1].Value);
        var branch = cond.Branches[0];

        // Branch body has no implicit params
        Assert.Empty(branch.Body.Params);

        var binary = Assert.IsType<Expr.Binary>(branch.Body.Output[0]);
        var left = Assert.IsType<Expr.Param>(binary.Left); // x is a binder
        Assert.Equal("x", left.Name);
        var right = Assert.IsType<Expr.Resolve>(binary.Right); // Rate is a sibling
        Assert.Equal("Rate", right.Name);
    }

    [Fact]
    public void Detect_ConditionalBranch_UnresolvedFreeId_StaysResolve()
    {
        // Free identifier 'b' not bound by pattern and not a sibling → stays as Expr.Resolve
        // (will fail at runtime, but ParameterDetector should NOT turn it into a param)
        var source = "F((a)) = a + b";
        var ast = ParseAndDetect(source);

        var cond = Assert.IsType<Algorithm.Conditional>(ast.Properties[0].Value);
        var branch = cond.Branches[0];

        // Branch body has no implicit params
        Assert.Empty(branch.Body.Params);

        var binary = Assert.IsType<Expr.Binary>(branch.Body.Output[0]);
        Assert.IsType<Expr.Param>(binary.Left); // a is a binder
        Assert.IsType<Expr.Resolve>(binary.Right); // b stays as Resolve (will fail at runtime)
    }

    // ── Conditional branch: free identifier diagnostics ───────────────────

    private static IReadOnlyList<Diagnostic> ParseAndDetectDiagnostics(string source)
    {
        var result = Parser.ParseSyntax(source);
        var (_, diagnostics) = ParameterDetector.Detect(result.Root);
        return diagnostics;
    }

    [Fact]
    public void Detect_ConditionalBranch_FreeIdentifier_ReportsDiagnostic()
    {
        var diags = ParseAndDetectDiagnostics("F((a)) = a + b");

        var error = Assert.Single(diags);
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        Assert.Contains("b", error.Message);
        Assert.Contains("F", error.Message);
    }

    [Fact]
    public void Detect_ConditionalBranch_ConstantPatternFreeIdentifier_MessageIncludesExample()
    {
        var diags = ParseAndDetectDiagnostics("A(2) = x");

        var error = Assert.Single(diags);
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        Assert.Contains("Identifier 'x' is used in conditional branch 'A'", error.Message);
        Assert.Contains("not declared in the branch pattern", error.Message);
        Assert.Contains("A(y) = y", error.Message);
    }

    [Fact]
    public void Detect_ConditionalBranch_MixedPatternFreeIdentifier_MessageIncludesIdentifierName()
    {
        var diags = ParseAndDetectDiagnostics("A(1, y) = x");

        var error = Assert.Single(diags);
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        Assert.Contains("Identifier 'x' is used in conditional branch 'A'", error.Message);
    }

    [Fact]
    public void Detect_ConditionalBranch_MultipleFreeIdentifiers_ReportsAll()
    {
        var diags = ParseAndDetectDiagnostics("F((x)) = a * x + b");

        Assert.Equal(2, diags.Count);
        Assert.All(diags, d => Assert.Equal(DiagnosticSeverity.Error, d.Severity));
        Assert.Contains(diags, d => d.Message.Contains("a"));
        Assert.Contains(diags, d => d.Message.Contains("b"));
    }

    [Fact]
    public void Detect_ConditionalBranch_AllBindersBound_NoDiagnostic()
    {
        var diags = ParseAndDetectDiagnostics("F((a), b) = a + b");

        Assert.Empty(diags);
    }

    [Fact]
    public void Detect_ConditionalBranch_SingleBinderBody_NoDiagnostic()
    {
        var diags = ParseAndDetectDiagnostics("A(y) = y");

        Assert.Empty(diags);
    }

    [Fact]
    public void Detect_ConditionalBranch_TwoBindersBody_NoDiagnostic()
    {
        var diags = ParseAndDetectDiagnostics("A(x, y) = x + y");

        Assert.Empty(diags);
    }

    [Fact]
    public void Detect_ConditionalBranch_SiblingPropertyVisible_NoDiagnostic()
    {
        var source = """
            Rate = 2
            F(x) = x * Rate
            """;
        var diags = ParseAndDetectDiagnostics(source);

        Assert.Empty(diags);
    }

    [Fact]
    public void Detect_ConditionalBranch_ErrorOnlyInOneBranch()
    {
        // Branch 1 has free identifier 'a', branch 2 is fine
        var source = """
            Expense(1, qty) = a * qty
            Expense(2, a, qty) = a * qty
            """;
        var diags = ParseAndDetectDiagnostics(source);

        var error = Assert.Single(diags);
        Assert.Contains("a", error.Message);
        Assert.Contains("Expense", error.Message);
    }
}
