using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Pins for the permanent OutputBundle architecture: <see cref="Expr.AlgorithmExpr"/>
/// carries algorithm identity/scope, <see cref="Expr.Capture"/> is the normalized
/// value/output boundary over an <see cref="OutputBundle"/>, and call/dot-call
/// argument lists are OutputBundles of the original written expressions.
///
/// <para>Every test here either pins the structural shape of the elaborated
/// AST or pins an observable behavior of the permanent model
/// (<c>(Obj).V</c> capture-receiver suppression, captured open targets being
/// rejected, higher-order argument channels).</para>
/// </summary>
public class OutputBundleSplitTests
{
    private static Algorithm ParseValidRoot(string source)
        => SourceProvenance.ParseValid(source).Root;

    private static Result Eval(string source)
    {
        var result = Evaluator.Run(new Expr.AlgorithmExpr(ParseValidRoot(source)));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        return result.Value;
    }

    private static EvalError EvalError(string source)
    {
        var result = Evaluator.Run(new Expr.AlgorithmExpr(ParseValidRoot(source)));
        Assert.True(result.IsError, "expected evaluation to fail");
        return result.Error;
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    // ── AST shape ────────────────────────────────────────────────────────────

    [Fact]
    public void BraceSource_ProducesAlgorithmExpr()
    {
        var root = ParseValidRoot("{1, 2}");
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(root.Output));
        Assert.Equal(2, block.Algorithm.Output.Count);
    }

    [Fact]
    public void SurvivingParens_ProduceCapture_WithoutAnyAlgorithm()
    {
        var root = ParseValidRoot("(1, 2)");
        var capture = Assert.IsType<Expr.Capture>(Assert.Single(root.Output));
        Assert.Equal(2, capture.Body.Count);
        Assert.IsType<Expr.Num>(capture.Body[0]);
        Assert.IsType<Expr.Num>(capture.Body[1]);
    }

    [Fact]
    public void RedundantParens_NormalizeExactlyAsBefore()
    {
        // (1) unwraps; () is the empty sequence; ({1}) / (({1})) normalize to
        // the brace algorithm; ((1, 2)) keeps its written capture boundary.
        Assert.IsType<Expr.Num>(Assert.Single(ParseValidRoot("(1)").Output));
        Assert.IsType<Expr.EmptySequence>(Assert.Single(ParseValidRoot("()").Output));
        Assert.IsType<Expr.EmptySequence>(Assert.Single(ParseValidRoot("(())").Output));
        Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(ParseValidRoot("({1})").Output));
        Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(ParseValidRoot("(({1}))").Output));

        var nested = Assert.IsType<Expr.Capture>(Assert.Single(ParseValidRoot("((1, 2))").Output));
        var inner = Assert.IsType<Expr.Capture>(Assert.Single(nested.Body));
        Assert.Equal(2, inner.Body.Count);
    }

    [Fact]
    public void CallArgs_AreOutputBundles()
    {
        // Parser-produced Call/DotCall argument lists are ordered
        // OutputBundles of the original written argument expressions — no
        // transparent Algorithm wrapper exists anywhere in the AST.
        var call = Assert.IsType<Expr.Call>(Assert.Single(ParseValidRoot("F(x) = x\nF(1)").Output));
        var args = Assert.IsType<OutputBundle>(call.Args);
        Assert.IsType<Expr.Num>(Assert.Single(args));

        var dot = Assert.IsType<Expr.DotCall>(Assert.Single(ParseValidRoot("A = 1, 2\nA.take(1)").Output));
        var dotArgs = Assert.IsType<OutputBundle>(dot.Args);
        Assert.IsType<Expr.Num>(Assert.Single(dotArgs));

        // No-argument-list dot access stays null — distinct from an explicit
        // empty argument list, which is an empty bundle (never an Algorithm).
        var propertyStyle = Assert.IsType<Expr.DotCall>(Assert.Single(ParseValidRoot("A = 1, 2\nA.count").Output));
        Assert.Null(propertyStyle.Args);
        var explicitEmpty = Assert.IsType<Expr.Call>(Assert.Single(ParseValidRoot("Z = f()\nZ()").Output));
        Assert.Empty(explicitEmpty.Args);
    }

    [Fact]
    public void TrailingBraceCall_LowersToOneAlgorithmExprSlot()
    {
        // Apply{a + 1}: the brace algorithm is the single bundle slot — no
        // outer transparent argument Algorithm surrounds it.
        var call = Assert.IsType<Expr.Call>(Assert.Single(ParseValidRoot("Apply = f(9)\nApply{a + 1}").Output));
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(call.Args));
        Assert.Equal(["a"], block.Algorithm.Params);
    }

    [Fact]
    public void ParenthesizedBraceCallArgument_NormalizesToTheSameAlgorithmExprSlot()
    {
        // Apply(({a + 1})): redundant parentheses around a scope-owning brace
        // argument normalize away, leaving the same single AlgorithmExpr slot
        // the trailing-brace form produces.
        var call = Assert.IsType<Expr.Call>(Assert.Single(ParseValidRoot("Apply = f(9)\nApply(({a + 1}))").Output));
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(call.Args));
        Assert.Equal(["a"], block.Algorithm.Params);
    }

    [Fact]
    public void NestedCaptureArgument_KeepsItsBoundaryInTheBundle()
    {
        // F((1, 2)): the inner group survives as ONE Capture slot — the outer
        // call owning the bundle directly never flattens a written boundary.
        var call = Assert.IsType<Expr.Call>(Assert.Single(ParseValidRoot("F(x) = x.count\nF((1, 2))").Output));
        var capture = Assert.IsType<Expr.Capture>(Assert.Single(call.Args));
        Assert.Equal(2, capture.Body.Count);
    }

    // Exactly-once argument forcing is pinned DETERMINISTICALLY by
    // CallArgumentSingleForcingTests (charged-step/materialization counts per
    // call family) and PatternedCallSingleEvaluationTests (prepared patterned
    // pass) — not by value equality over generated values.

    [Fact]
    public void ListLiteral_CarriesAnOutputBundle()
    {
        var root = ParseValidRoot("[1, 2]");
        var list = Assert.IsType<Expr.ListLiteral>(Assert.Single(root.Output));
        Assert.IsType<OutputBundle>(list.Items);
        Assert.Equal(2, list.Items.Count);
    }

    [Fact]
    public void AlgorithmOutput_IsAnOutputBundle()
    {
        Assert.IsType<OutputBundle>(ParseValidRoot("1, 2").Output);
        Assert.Same(OutputBundle.Empty, new Algorithm.Builtin(BuiltinId.@count).Output);
    }

    [Fact]
    public void OutputBundle_IsAReadOnlyExprList()
    {
        var leaf = new Expr.Num(1);
        OutputBundle bundle = [leaf, leaf];
        Assert.Equal(2, bundle.Count);
        Assert.Same(leaf, bundle[0]);
        Assert.Equal(2, bundle.Count());
        Assert.Empty(OutputBundle.Empty);

        // From() never copies an existing bundle.
        Assert.Same(bundle, OutputBundle.From(bundle));
    }

    // ── Scope ownership ──────────────────────────────────────────────────────

    [Fact]
    public void FreeNamesInsideCapture_BelongToTheNearestScopeOwner()
    {
        // The capture owns nothing: x bubbles to the root as an implicit
        // parameter, and the capture row is rewritten to reference it.
        var root = ParseValidRoot("map((x, 1), first)");
        Assert.Equal(["x"], root.Params);

        var call = Assert.IsType<Expr.Call>(Assert.Single(root.Output));
        var capture = Assert.IsType<Expr.Capture>(call.Args[0]);
        Assert.IsType<Expr.Param>(capture.Body[0]);
    }

    [Fact]
    public void FreeNamesInsideListLiteral_StayTransparent()
    {
        var root = ParseValidRoot("[x, 1]");
        Assert.Equal(["x"], root.Params);
    }

    [Fact]
    public void FreeNamesInsideBraceBlock_StayOwnedByTheBlock()
    {
        var root = ParseValidRoot("[1, 2, 3].map({x * 10})");
        Assert.Empty(root.Params);

        var dot = Assert.IsType<Expr.DotCall>(Assert.Single(root.Output));
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(dot.Args!));
        Assert.Equal(["x"], block.Algorithm.Params);
    }

    // ── Capture evaluation (shared output-row machinery) ────────────────────

    [Theory]
    [InlineData("(1, 2).count", 2)]
    [InlineData("((1, 2)).count", 2)]
    [InlineData("A = 1, 2, 3\n(A).count", 3)]
    [InlineData("A = 1, 2, 3\n((A)).count", 3)]
    [InlineData("A = 1, 2, 3\n(A*).count", 3)]
    [InlineData("A = 1, 2, 3\n((A*)).count", 3)]
    public void CaptureCardinality_MatchesPreSplitBehavior(string source, decimal expected)
    {
        var value = Eval(source);
        Assert.Equal(expected, Assert.IsType<Result.Atom>(value).Value);
    }

    [Fact]
    public void VisibleEmpty_SlotsStayVisibleInsideCapture()
    {
        var value = Assert.IsType<Result.SequenceValue>(Eval("((), ())"));
        Assert.Equal(2, value.Items.Count);
    }

    [Fact]
    public void SpreadCapture_SuppliesItemsThenCaptures()
    {
        var value = Assert.IsType<Result.SequenceValue>(Eval("A = 1, 2, 3\n(A*, 5)"));
        Assert.Equal(4, value.Items.Count);
    }

    [Fact]
    public void HostBuiltEmptyCapture_CapturesTheEmptySequence()
    {
        // Not parser-reachable (`()` parses to EmptySequence): an empty bundle
        // captures zero items, i.e. the empty sequence value.
        var result = Evaluator.RunCounted(new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [], [], [new Expr.Capture(OutputBundle.Empty)])));
        Assert.False(result.IsError);
        var value = Assert.IsType<Result.SequenceValue>(result.Value.Value);
        Assert.Empty(value.Items);
        Assert.Equal(1, result.Value.EmittedCount);
    }

    [Fact]
    public void HostBuiltCapture_EvaluatesLikeAnEquivalentZeroDeclarationBlock()
    {
        // For declaration-free content the two node kinds are observationally
        // equivalent in value position — the shared output-row loop is the
        // single implementation both reach.
        OutputBundle rows = [new Expr.Num(1), new Expr.Num(2)];
        var viaCapture = Evaluator.RunCounted(new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [], [], [new Expr.Capture(rows)])));
        var viaBlock = Evaluator.RunCounted(new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [], [], [new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], rows))])));

        Assert.False(viaCapture.IsError);
        Assert.False(viaBlock.IsError);
        Assert.Equal(viaBlock.Value.EmittedCount, viaCapture.Value.EmittedCount);
        Assert.True(Result.ValueComparer.Equals(viaBlock.Value.Value, viaCapture.Value.Value));
    }

    // ── Capture is not algorithm identity ────────────────────────────────────

    [Fact]
    public void GroupedNamedAlgorithm_StaysSuppressedOnTheValueChannel()
    {
        // (Increment) is a capture: evaluating it as the argument VALUE calls
        // the one-parameter property with zero arguments. Increment's callable
        // identity never crosses the capture boundary.
        var error = Innermost(EvalError("Apply = f(9)\nIncrement = x + 1\nApply((Increment))"));
        var arity = Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.Equal(1, arity.Expected);
        Assert.Equal(0, arity.Actual);
    }

    [Fact]
    public void GroupedZeroParameterAlgorithm_IsAValueNotACallable()
    {
        var error = Innermost(EvalError("Zero = 0\nCall0 = f()\nCall0((Zero))"));
        Assert.IsType<EvalError.NotAnAlgorithm>(error);
    }

    [Fact]
    public void ParenthesizedBraceArgument_KeepsAlgorithmIdentity()
    {
        // ({a + 1}) normalizes to the brace algorithm, so callable identity is
        // preserved — the capture/identity distinction is decided by node kind.
        var value = Eval("Apply = f(9)\nApply(({a + 1}))");
        Assert.Equal(10, Assert.IsType<Result.Atom>(value).Value);
    }

    [Fact]
    public void CaptureReceiver_FailsStructuralLookup_AndInjectsIntoLexicalFallback()
    {
        // (Obj).V: the capture exposes no members, so structural lookup fails
        // and the lexical fallback resolves V lexically. The edge is inside a
        // CLOSED explicit parameter list, so the unresolvable fallback stays a
        // lexical name (it is not promoted to an implicit parameter) and the
        // structured error is UnknownName("V") — the engine's dot-call context
        // renders it as "Property 'V' was not found on `(inline library)`...",
        // never as a member of Obj.
        var missing = Innermost(EvalError("Obj = {public V = 7}\nQ(z) = (Obj).V\nQ(0)"));
        var unknown = Assert.IsType<EvalError.UnknownName>(missing);
        Assert.Equal("V", unknown.Name);

        // With a lexical one-parameter V, the receiver is injected as the one
        // leading argument: V(receiverValue). Obj has properties but NO output,
        // so evaluating the capture receiver reports Obj's missing output —
        // proof the fallback call was taken (structural access Obj.V works).
        var fallback = EvalError("V(v) = v + 1\nObj = {public V = 7}\n(Obj).V");
        Assert.IsType<EvalError.MissingOutput>(Innermost(fallback));

        var structural = Eval("Obj = {public V = 7}\nObj.V");
        Assert.Equal(7, Assert.IsType<Result.Atom>(structural).Value);
    }

    [Fact]
    public void OpenCaptureTarget_IsRejectedAtParse()
    {
        // `open` consumes algorithm/namespace identity, and a capture is a
        // value boundary that never exposes the identity of what it encloses,
        // so a parenthesized open target is rejected at parse time with the
        // targeted captured-open diagnostic — exactly like a spread-marked
        // target. Direct and brace-normalized targets still open.
        var direct = Eval("M = {public C = 5}\nR = {open M\nC}\nR");
        Assert.Equal(5, Assert.IsType<Result.Atom>(direct).Value);

        var braceNormalized = Eval("R = {open ({public C = 6})\nC}\nR");
        Assert.Equal(6, Assert.IsType<Result.Atom>(braceNormalized).Value);

        foreach (var source in new[]
        {
            "M = {public C = 5}\nR = {open (M)\nC}\nR",
            "M = {public C = 5}\nR = {open ((M))\nC}\nR",
        })
        {
            var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
            var diagnostic = Assert.Single(
                parsed.Diagnostics,
                d => d.Message == Parser.CapturedOpenTargetDiagnostic);
            Assert.Equal(2, diagnostic.Span.StartLineNumber);
        }

        // Prebuilt-AST defense: a capture open target that bypasses the
        // parser fails open resolution with the structured BadOpenForm error,
        // mirroring the spread arm (and covering dotted heads like `(X).B`).
        // Open resolution is lazy, so the output must consult the opens: the
        // unresolved name C forces them.
        var host = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [new Expr.Capture([new Expr.Resolve("M")])],
            Properties: [new Property("M", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))],
            Output: [new Expr.Resolve("C")]);
        var hostResult = Evaluator.Run(new Expr.AlgorithmExpr(host));
        Assert.True(hostResult.IsError);
        Assert.IsType<EvalError.BadOpenForm>(Innermost(hostResult.Error));
    }

    // ── Recovery ─────────────────────────────────────────────────────────────

    [Fact]
    public void ParenthesizedDeclarations_RecoverAsScopeOwningAlgorithmExpr()
    {
        // The diagnostic tells the user to write braces; the recovery tree now
        // IS the brace shape: declarations retained on a scope-owning
        // AlgorithmExpr, and the body identifier resolves to the retained
        // property instead of leaking a phantom implicit parameter.
        var parsed = SourceProvenance.ParseAllowingDiagnostics("(X = 1\nX)");
        Assert.Contains(parsed.Diagnostics, d => d.Message.Contains("not allowed inside parentheses"));

        Assert.Empty(parsed.Root.Params);
        var recovered = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(parsed.Root.Output));
        Assert.Equal("X", Assert.Single(recovered.Algorithm.Properties).Name);
        Assert.IsType<Expr.Resolve>(Assert.Single(recovered.Algorithm.Output));
    }

    [Fact]
    public void ParenthesizedOpen_RecoveryRetainsTheOpenTarget()
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics("M = {public C = 5}\n(open M\n1)");
        Assert.Contains(parsed.Diagnostics, d => d.Message.Contains("'open' declaration is not allowed inside parentheses"));

        var recovered = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(parsed.Root.Output));
        Assert.Single(recovered.Algorithm.Opens);
    }

    [Fact]
    public void RecoveryTrees_SurviveTheFullFrontEndAndSemanticModel()
    {
        // Malformed parenthesized declarations must not crash any later phase:
        // the full front-end pipeline (ParseAllowingDiagnostics runs it), the
        // evaluator, and the EDITOR SEMANTIC MODEL — built through the same
        // SemanticModelBuilder.Build(ParseResult) contract real tooling uses.
        foreach (var source in new[] { "(X = 1\nX)", "M = {public C = 5}\n(open M\n1)", "W = (public Y = 1)\nW" })
        {
            var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
            Assert.NotEmpty(parsed.Diagnostics);
            _ = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));

            var model = SemanticModelBuilder.Build(parsed.Parsed);
            Assert.Same(parsed.Root, model.Root);
        }

        // The retained recovery declaration is a real semantic-model citizen:
        // for `(X = 1\nX)` the recovery AlgorithmExpr owns property X, so the
        // model reports X's declaration and resolves the body reference to it.
        var recovered = SourceProvenance.ParseAllowingDiagnostics("(X = 1\nX)");
        var recoveredModel = SemanticModelBuilder.Build(recovered.Parsed);

        var declaration = Assert.Single(recoveredModel.FindDeclarations("X"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, declaration.Kind);

        var reference = Assert.Single(
            recoveredModel.FindResolutions("X"),
            resolution => resolution.Occurrence.Kind == OccurrenceKind.ResolveReference);
        Assert.Equal(declaration, reference.ResolvedDeclaration);
    }
}
