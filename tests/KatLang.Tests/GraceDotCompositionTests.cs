namespace KatLang.Tests;

/// <summary>
/// Focused regression matrix for Grace composed with ordinary DotCall syntax.
///
/// The language law: `~` affects inferred parameter ORDERING ONLY. It never
/// changes the property body's executable semantics, so `recv~.t(args...)` and
/// `recv.~t(args...)` have the SAME executable body as the ordinary dot edge
/// `recv.t(args...)` — structural member first, stored lexical fallback
/// second. Inferred parameters follow semantic source-occurrence order, so
/// `K = a.t` corresponds to `K(a, t) = a.t`; the fallback's runtime call
/// assembly as `t(a)` is a separate concern. In `a~.t`, postfix Grace decorates
/// `a`; in `a.~t`, prefix Grace decorates the participating fallback occurrence
/// `t`. Both use the same weight arithmetic as standalone Grace.
///
/// The architectural rule: each written marker contributes ordinary ordering
/// <see cref="Expr.Grace"/> on its individual name occurrence at parse time,
/// which parameter detection consumes and strips. After elaboration, graced and
/// ungraced dot sources are the SAME <see cref="Expr.DotCall"/> body; the
/// evaluator, the optimizer, and Lean cannot observe that the marker was
/// written. There is no additional resolution mode and no lowering to a call.
///
/// The eligibility rule follows the decorated occurrence. Postfix Grace before
/// a dot requires the receiver itself to be one bare name, so compound forms
/// such as `(x + y)~.t` and a second `~.` edge reject. Prefix Grace after a dot
/// decorates the bare member/fallback name, so `(x + y).~t` is valid.
/// </summary>
public class GraceDotCompositionTests
{
    private const string GraceEligibilityFragment =
        "Grace `~` can only be applied to a parameter or name occurrence.";

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result List(params Result[] items) => new Result.ListValue(items);

    private static Result Seq(params Result[] items) => new Result.SequenceValue(items);

    /// <summary>
    /// STRICT-SOURCE: requires a clean front end, then evaluates through both
    /// the plain and the counted evaluator entry points and asserts they agree
    /// on the same value before returning it.
    /// </summary>
    private static Result Evaluate(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        var expr = new Expr.AlgorithmExpr(provenance.Root);

        var plain = Evaluator.Run(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");

        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");

        Assert.True(
            Result.ValueComparer.Equals(plain.Value, counted.Value.Value),
            $"Plain/counted divergence: {plain.Value} vs {counted.Value.Value}");
        return plain.Value;
    }

    private static void AssertResult(string source, Result expected)
    {
        var actual = Evaluate(source);
        Assert.True(
            Result.ValueComparer.Equals(expected, actual),
            $"Expected {expected} but got {actual}{Environment.NewLine}Source:{Environment.NewLine}{source}");
    }

    /// <summary>
    /// The central law assertion: two sources elaborate to the SAME executable
    /// body. Compared structurally, because source spans legitimately differ —
    /// the marker occupies source columns, and span provenance is the ONE
    /// thing a graced source is still allowed to carry.
    /// </summary>
    private static void AssertSameElaboratedBody(string left, string right, string propertyName = "K")
    {
        static string BodyShapeOf(string source, string propertyName)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            var property = Assert.Single(root.Properties, p => p.Name == propertyName);
            return Shape(Assert.Single(property.Value.Output));
        }

        Assert.Equal(BodyShapeOf(right, propertyName), BodyShapeOf(left, propertyName));
    }

    /// <summary>Span-free structural rendering of an elaborated expression.</summary>
    private static string Shape(Expr expr) => expr switch
    {
        Expr.Num(var value) => value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Expr.StringLiteral(var text) => $"'{text}'",
        Expr.Param(var name) => $"Param({name})",
        Expr.Resolve(var name) => $"Resolve({name})",
        Expr.Grace(var inner, var weight) => $"Grace({Shape(inner)},{weight})",
        Expr.Unary(var op, var operand) => $"Unary({op},{Shape(operand)})",
        Expr.Binary(var op, var left, var right) => $"Binary({op},{Shape(left)},{Shape(right)})",
        Expr.Index(var target, var selector) => $"Index({Shape(target)},{Shape(selector)})",
        Expr.SequenceSpread(var operand) => $"Spread({Shape(operand)})",
        Expr.EmptySequence => "()",
        Expr.ListLiteral(var items) => $"List([{string.Join(",", items.Select(Shape))}])",
        Expr.Capture(var body) => $"Capture([{string.Join(",", body.Select(Shape))}])",
        Expr.Call(var function, var args) => $"Call({Shape(function)},[{string.Join(",", args.Select(Shape))}])",
        Expr.DotCall dotCall =>
            $"DotCall({Shape(dotCall.Target)},{dotCall.Name},"
            + $"{(dotCall.Args is null ? "null" : "[" + string.Join(",", dotCall.Args.Select(Shape)) + "]")},"
            + $"fallback={Shape(dotCall.EffectiveLexicalFallback)})",
        Expr.AlgorithmExpr(var algorithm) =>
            $"Alg([{string.Join(",", algorithm.Params)}],[{string.Join(",", algorithm.Output.Select(Shape))}])",
        _ => expr.GetType().Name,
    };

    private static IReadOnlyList<string> ParamsOf(string source, string propertyName = "K")
    {
        var root = SourceProvenance.ParseValid(source).Root;
        return Assert.Single(root.Properties, p => p.Name == propertyName).Value.Params;
    }

    private static EvalError AssertBothEvaluatorsFail(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        var expr = new Expr.AlgorithmExpr(provenance.Root);

        var plain = Evaluator.Run(expr);
        Assert.True(plain.IsError, $"Expected plain evaluation error but got: {(plain.IsError ? null : plain.Value)}");

        var counted = Evaluator.RunCounted(expr);
        Assert.True(counted.IsError, $"Expected counted evaluation error but got: {(counted.IsError ? null : counted.Value.Value)}");

        var plainInner = Innermost(plain.Error);
        var countedInner = Innermost(counted.Error);
        Assert.Equal(plainInner.GetType(), countedInner.GetType());
        return plainInner;
    }

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext withContext ? Innermost(withContext.Inner) : error;

    private static void AssertParseFails(string source, string diagnosticFragment)
    {
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors, $"Expected a parse diagnostic but the source parsed cleanly:{Environment.NewLine}{source}");
        Assert.Contains(parse.Diagnostics, diagnostic => diagnostic.Message.Contains(diagnosticFragment, StringComparison.Ordinal));
    }

    /// <summary>
    /// F10: a marker on an occurrence whose binding is already fixed — an explicit
    /// parameter, a visible property, a builtin, a structurally resolved member —
    /// cannot reorder anything and is the ineffective-Grace error. The recovery tree
    /// is still the ordinary ungraced program (the marker is stripped), which the
    /// callers below use to keep the "same executable body" law observable.
    /// </summary>
    private static ParseResult AssertGraceIneffective(string source, string name, string reasonFragment)
    {
        var parse = Parser.Parse(source);
        var diagnostic = Assert.Single(parse.Diagnostics, d => d.Code == DiagnosticCode.InvalidGraceMarker);
        Assert.StartsWith($"Grace has no effect on '{name}' because {reasonFragment}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(parse.Root));
        return parse;
    }

    // ── A. THE CENTRAL LAW: source occurrence order, same executable body ──

    [Fact]
    public void Law_PrimaryCase_OrdinaryDotInfersSemanticSourceOrder()
    {
        // `K = a.t` has ordinary DotCall semantics: structural `t` on `a` if
        // present, otherwise the lexical call `t(a)`. Because `a` is an opaque
        // implicit parameter, that fallback MAY be selected, so the fallback
        // callable participates at the member's semantic source occurrence:
        // receiver `a`, member/fallback `t` => K(a, t).
        Assert.Equal(["a", "t"], ParamsOf("K = a.t\nK(7, {x+1})"));
        AssertResult("K = a.t\nK(7, {x+1})", Atom(8));
    }

    [Fact]
    public void Law_PrimaryTrace_RawOccurrenceAndElaboratedFallbackIdentityAgree()
    {
        var syntax = Parser.ParseSyntax("K = a.t");
        Assert.Empty(syntax.Diagnostics);
        var rawK = Assert.Single(syntax.Root.Properties).Value;
        Assert.Empty(rawK.Params);
        var rawEdge = Assert.IsType<Expr.DotCall>(Assert.Single(rawK.Output));
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(rawEdge.Target).Name);
        Assert.Equal("t", Assert.IsType<Expr.Resolve>(rawEdge.LexicalFallback).Name);

        var (detected, diagnostics) = ParameterDetector.Detect(syntax.Root);
        Assert.Empty(diagnostics);
        var detectedK = Assert.Single(detected.Properties).Value;
        Assert.Equal(["a", "t"], detectedK.Params);
        var detectedEdge = Assert.IsType<Expr.DotCall>(Assert.Single(detectedK.Output));
        Assert.Equal("a", Assert.IsType<Expr.Param>(detectedEdge.Target).Name);
        Assert.Equal("t", Assert.IsType<Expr.Param>(detectedEdge.LexicalFallback).Name);

        var elaboratedK = Assert.Single(SourceProvenance.ParseValid("K = a.t").Root.Properties).Value;
        Assert.Equal(detectedK.Params, elaboratedK.Params);
        Assert.Equal(Shape(detectedEdge), Shape(Assert.Single(elaboratedK.Output)));
    }

    [Fact]
    public void Law_RawGraceOwnership_ReusesOrdinaryPrefixAndPostfixRepresentation()
    {
        var postfixSyntax = Parser.ParseSyntax("K = a~.t");
        Assert.Empty(postfixSyntax.Diagnostics);
        var postfixEdge = Assert.IsType<Expr.DotCall>(
            Assert.Single(Assert.Single(postfixSyntax.Root.Properties).Value.Output));
        var receiverGrace = Assert.IsType<Expr.Grace>(postfixEdge.Target);
        Assert.Equal(+1, receiverGrace.Weight);
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(receiverGrace.Inner).Name);
        Assert.Equal("t", Assert.IsType<Expr.Resolve>(postfixEdge.LexicalFallback).Name);

        var prefixSyntax = Parser.ParseSyntax("K = a.~t");
        Assert.Empty(prefixSyntax.Diagnostics);
        var prefixEdge = Assert.IsType<Expr.DotCall>(
            Assert.Single(Assert.Single(prefixSyntax.Root.Properties).Value.Output));
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(prefixEdge.Target).Name);
        var memberGrace = Assert.IsType<Expr.Grace>(prefixEdge.LexicalFallback);
        Assert.Equal(-1, memberGrace.Weight);
        Assert.Equal("t", Assert.IsType<Expr.Resolve>(memberGrace.Inner).Name);

        var (postfixDetected, postfixDiagnostics) = ParameterDetector.Detect(postfixSyntax.Root);
        var (prefixDetected, prefixDiagnostics) = ParameterDetector.Detect(prefixSyntax.Root);
        Assert.Empty(postfixDiagnostics);
        Assert.Empty(prefixDiagnostics);
        Assert.Equal(["t", "a"], Assert.Single(postfixDetected.Properties).Value.Params);
        Assert.Equal(["t", "a"], Assert.Single(prefixDetected.Properties).Value.Params);
        Assert.Equal(
            Shape(Assert.Single(postfixDetected.Properties[0].Value.Output)),
            Shape(Assert.Single(prefixDetected.Properties[0].Value.Output)));
    }

    [Fact]
    public void Law_GraceCounterpart_UsesOrdinaryWeightOnTheSameBody()
    {
        // Base occurrence order is a,t. Postfix Grace moves `a` one place
        // later; prefix Grace moves `t` one place earlier. Both yield t,a.
        Assert.Equal(["t", "a"], ParamsOf("K = a~.t\nK({x+1}, 7)"));
        AssertResult("K = a~.t\nK({x+1}, 7)", Atom(8));

        Assert.Equal(["t", "a"], ParamsOf("K = a.~t\nK({x+1}, 7)"));
        AssertResult("K = a.~t\nK({x+1}, 7)", Atom(8));
    }

    [Fact]
    public void Law_EquivalenceMatrix_ImplicitAndExplicitAgree()
    {
        // Inference differs only by ordinary Grace; explicit declarations keep
        // their written parameter order — and because an explicit list FIXES the
        // order, a marker under one is the ineffective-Grace error (F10), never a
        // silent no-op. Every property body is the same edge.
        AssertResult("K1 = a.t\nK1(7, {x+1})", Atom(8));
        AssertResult("K2(a, t) = a.t\nK2(7, {x+1})", Atom(8));
        AssertResult("K3 = a~.t\nK3({x+1}, 7)", Atom(8));
        AssertResult("K4(t, a) = a.t\nK4({x+1}, 7)", Atom(8));
        AssertResult("K5 = a.~t\nK5({x+1}, 7)", Atom(8));
        AssertResult("K6(t, a) = a.t\nK6({x+1}, 7)", Atom(8));
        AssertGraceIneffective("K4(t, a) = a~.t\nK4({x+1}, 7)", "a", "it already resolves to an explicit parameter");
        AssertGraceIneffective("K6(t, a) = a.~t\nK6({x+1}, 7)", "t", "it already resolves to an explicit parameter");
    }

    [Fact]
    public void Law_BothSpellings_ElaborateToTheOrdinaryDotBody()
    {
        // The marker leaves NO trace: the graced spellings elaborate to the same
        // ordinary dot body as `K(t, a) = a.t` — the explicit spelling of the order
        // they infer — with the same param names bound, and none of them is a Call.
        AssertSameElaboratedBody("K = a~.t", "K(t, a) = a.t");
        AssertSameElaboratedBody("K = a.~t", "K(t, a) = a.t");

        var body = Assert.IsType<Expr.DotCall>(
            Assert.Single(SourceProvenance.ParseValid("K = a~.t\nK({a+1}, 7)")
                .Root.Properties[0].Value.Output));
        Assert.Equal("t", body.Name);
        Assert.Equal("a", Assert.IsType<Expr.Param>(body.Target).Name);
        Assert.Equal("t", Assert.IsType<Expr.Param>(body.EffectiveLexicalFallback).Name);
        Assert.Null(body.Args);
    }

    [Fact]
    public void Law_ExplicitParameterLists_FixTheOrder_SoGraceUnderThemIsAnError()
    {
        // Written parameter order IS the declared order; a marker on a declared
        // parameter could only contradict it, so it is rejected instead of ignored
        // (F10). The recovery tree keeps the declared order exactly.
        Assert.Equal(["a", "t"], ParamsOf("K(a, t) = a.t"));
        Assert.Equal(["t", "a"], ParamsOf("K(t, a) = a.t"));
        foreach (var (source, name) in new[]
        {
            ("K(a, t) = a~.t", "a"), ("K(t, a) = a~.t", "a"),
            ("K(a, t) = a.~t", "t"), ("K(t, a) = a.~t", "t"),
        })
        {
            var recovery = AssertGraceIneffective(source, name, "it already resolves to an explicit parameter");
            string[] declaredOrder = source.StartsWith("K(a, t)", StringComparison.Ordinal) ? ["a", "t"] : ["t", "a"];
            Assert.Equal(declaredOrder, Assert.Single(recovery.Root.Properties).Value.Params);
        }
    }

    [Fact]
    public void Law_DirectCallComparison_HasItsOwnSourceOrderAndDifferentBody()
    {
        // Direct-call traversal sees callee then argument; DotCall traversal
        // sees receiver then semantic member/fallback occurrence.
        Assert.Equal(["t", "a"], ParamsOf("K = t(a)\nK({x+1}, 7)"));
        Assert.Equal(["a", "t"], ParamsOf("K = a.t\nK(7, {x+1})"));

        // Their bodies are also NOT equivalent: only the dot edge consults
        // structural members first.
        AssertResult(StructuralSplit + "\nK(o) = o.V\nK(Obj)", Atom(42));
        AssertResult(StructuralSplit + "\nK(o) = V(o)\nK(Obj)", Atom(99));
    }

    [Fact]
    public void Law_GeneralExpressionTraversal_IsLeftToRightSemanticSourceOrder()
    {
        Assert.Equal(["a", "b"], ParamsOf("K = a + b"));
        Assert.Equal(["f", "a"], ParamsOf("K = f(a)"));
        Assert.Equal(["a", "b"], ParamsOf("K = a:b"));

        Assert.Equal(["z", "a", "t"], ParamsOf("K = z + a.t"));
        Assert.Equal(["z", "t", "a"], ParamsOf("K = z + a~.t"));
        Assert.Equal(["z", "t", "a"], ParamsOf("K = z + a.~t"));
        Assert.Equal(["a", "t", "z"], ParamsOf("K = a.t + z"));
        Assert.Equal(["f", "a", "t"], ParamsOf("K = f(a.t)"));
        Assert.Equal(["a", "t", "b"], ParamsOf("K = a.t(b)"));
        Assert.Equal(["q", "a", "t", "z"], ParamsOf("K = q(a.t, z)"));
    }

    [Fact]
    public void Law_BlockOwnsItsSourceOrderedParameters()
    {
        var k = Assert.Single(SourceProvenance.ParseValid("K = { a.t }").Root.Properties).Value;
        Assert.Equal(["a", "t"], k.Params);
        Assert.IsType<Expr.DotCall>(Assert.Single(k.Output));
    }

    [Fact]
    public void Law_MultipleDotsAndRepeatedNames_PreserveFirstOccurrenceOrder()
    {
        Assert.Equal(["a", "t", "b", "u"], ParamsOf("K = a.t + b.u"));
        Assert.Equal(["a", "t", "b"], ParamsOf("K = a.t + b.t"));
        Assert.Equal(["a", "t"], ParamsOf("K = a.t + a.t"));

        Assert.Equal(["t", "a", "b", "u"], ParamsOf("K = a~.t + b.u"));
        Assert.Equal(["a", "t", "u", "b"], ParamsOf("K = a.t + b~.u"));
        Assert.Equal(["t", "a", "b", "u"], ParamsOf("K = a.~t + b.u"));
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a.t + b.~t"));
    }

    [Fact]
    public void Law_MultiArgument_FollowsReceiverMemberArgumentsOrder()
    {
        // Runtime fallback still invokes `t(a, b, c)`, but signature order is
        // the DotCall's semantic source occurrence order.
        Assert.Equal(["a", "t", "b", "c"], ParamsOf("K = a.t(b, c)"));
        Assert.Equal(["t", "a", "b", "c"], ParamsOf("K = a~.t(b, c)"));
        Assert.Equal(["t", "a", "b", "c"], ParamsOf("K = a.~t(b, c)"));
        AssertSameElaboratedBody("K = a~.t(b, c)", "K(t, a, b, c) = a.t(b, c)");
        AssertSameElaboratedBody("K = a.~t(b, c)", "K(t, a, b, c) = a.t(b, c)");
        AssertResult("K = a.t(b, c)\nK(1, {a+b+c}, 10, 100)", Atom(111));
        AssertResult("K = a~.t(b, c)\nK({a+b+c}, 1, 10, 100)", Atom(111));
        AssertResult("K = a.~t(b, c)\nK({a+b+c}, 1, 10, 100)", Atom(111));
    }

    [Fact]
    public void Law_GraceAffectsSignatureOnly_OrdinaryGraceIdiomsUnchanged()
    {
        // Standalone Grace keeps the same sign and one-position arithmetic.
        Assert.Equal(["a", "t"], ParamsOf("K = t~(a)\nK(7, {a+1})"));
        AssertResult("K = t~(a)\nK(7, {a+1})", Atom(8));

        // Prefix grace on an ordinary argument still just reorders.
        Assert.Equal(["t", "b", "a"], ParamsOf("K = t(a~, b)\nK(1, 2, {x + y})"));

        // The same base name order a,t,b plus postfix Grace on `a` produces
        // the same one-position move with or without DotCall structure.
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a~ + t + b"));
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a~.t(b)"));
        // Likewise, prefix Grace on `t` is identical inside and outside dot.
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a.~t + b"));
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a + ~t + b"));
    }

    [Fact]
    public void Law_RepeatedPostfixGrace_UsesOrdinaryWeightArithmetic()
    {
        // `a~~.t` is two ordinary postfix markers (+2) on `a`. Only `t`
        // follows it, so the final order is still t,a.
        Assert.Equal(["t", "a"], ParamsOf("K = a~~.t\nK({x + 1}, 7)"));
        AssertResult("K = a~~.t\nK({x + 1}, 7)", Atom(8));
        AssertSameElaboratedBody("K = a~~.t", "K(t, a) = a.t");
    }

    [Fact]
    public void Law_RepeatedCallableName_OrdersByOrdinaryGraceBubbling()
    {
        // Postfix Grace moves a name ONE position per unit through the
        // ordinary bubble pass; with the callable also written directly, the
        // outcome is plain grace arithmetic, not a bespoke source-order rule.
        Assert.Equal(["a", "t", "b"], ParamsOf("K = a.t + t(b)\nK(1, {x + 1}, 2)"));
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a~.t + t(b)"));
        Assert.Equal(["t", "a", "b"], ParamsOf("K = a.t + b.~t"));
    }

    [Fact]
    public void Law_GracedDotsInsideArgumentSlots_ComposeSourceOrder()
    {
        // Each edge's receiver is its own bare name — nesting needs no
        // distribution, only the two one-name graces.
        // Base occurrence order is a,t,b,u. Each receiver moves one place
        // later, yielding t,a,u,b through the general bubble pass.
        Assert.Equal(["t", "a", "u", "b"], ParamsOf("K = a~.t(b~.u)"));
    }

    [Fact]
    public void Law_ReceiverEvaluatesExactlyOnce()
    {
        // The receiver is ONE expression in ONE dot edge, so a failing
        // receiver surfaces its one failure identically on both paths. (The
        // graced receiver is a free name bound to a failing block at the call;
        // Grace on a bound property receiver would be the ineffective-Grace error.)
        var error = AssertBothEvaluatorsFail("F(x) = x + 1\nK = bad~.F\nK({1/0})");
        Assert.IsType<EvalError.DivByZero>(error);
    }

    [Fact]
    public void Law_NestedLexicalScope_ResolvesLikeTheOrdinaryEdge()
    {
        // `t` is a visible sibling, so the member occurrence never joins the
        // signature: `K2 = a~.t` graces the FREE receiver (effective, inert at the
        // boundary), while `K3 = a.~t` would grace the bound member — that marker
        // is the ineffective-Grace error (F10), not a silent no-op.
        AssertResult(
            """
            Outer = {
                t(a) = a + 1
                K1 = a.t
                K2 = a~.t
                K1(41)
                K2(41)
            }
            Outer
            """,
            Seq(Atom(42), Atom(42)));
        AssertGraceIneffective(
            "Outer = {\n    t(a) = a + 1\n    K3 = a.~t\n    K3(41)\n}\nOuter",
            "t",
            "it already resolves to a property");
    }

    // ── B. Structural precedence: Grace NEVER changes member selection ─────

    private const string StructuralSplit =
        """
        V(x) = 99
        Obj = {
            public V = 42
            0
        }
        """;

    [Fact]
    public void Law_StructuralCollision_AllSpellingsSelectTheStructuralMember()
    {
        // The receiver HAS the member, so the edge uses it. `~` orders parameters;
        // it does not bypass structural lookup — and on THIS edge it can order
        // nothing: `Obj` is a bound property and `V` a member Obj is known to
        // declare, so both graced spellings are the ineffective-Grace error (F10)
        // whose recovery tree is exactly the ordinary edge.
        AssertResult(StructuralSplit + "\nObj.V", Atom(42));
        AssertGraceIneffective(StructuralSplit + "\nObj~.V", "Obj", "it already resolves to a property");
        AssertGraceIneffective(StructuralSplit + "\nObj.~V", "V", "the member 'V' always resolves structurally on its receiver");

        // With a FREE receiver the marker is effective and structural lookup still
        // wins at runtime (the spec case `grace-dot-keeps-structural-precedence`).
        AssertResult(StructuralSplit + "\nRead = o~.V\nRead(Obj)", Atom(42));
    }

    [Fact]
    public void Law_StructuralCollision_OnOpaqueReceiver_AllFormsAgree()
    {
        // With a runtime receiver the selection is decided at runtime, and the
        // spellings agree in BOTH directions — only the argument ORDER of the
        // enclosing signature differs. The graced forms infer their signatures
        // (`V` is then a free name, so the lexical `V` is omitted); under a closed
        // explicit list the markers are the ineffective-Grace error (F10).
        const string objOnly = "Obj = {\n    public V = 42\n    0\n}";
        AssertResult(StructuralSplit + "\nK(o, V) = o.V\nK(Obj, {x + 1})", Atom(42));
        AssertResult(objOnly + "\nK = o~.V\nK({x + 1}, Obj)", Atom(42));
        AssertResult(objOnly + "\nK = o.~V\nK({x + 1}, Obj)", Atom(42));
        AssertGraceIneffective(StructuralSplit + "\nK(o, V) = o~.V\nK(Obj, {x + 1})", "o", "it already resolves to an explicit parameter");
        AssertGraceIneffective(StructuralSplit + "\nK(o, V) = o.~V\nK(Obj, {x + 1})", "V", "it already resolves to an explicit parameter");
        // No structural member on the receiver → the lexical parameter is used.
        AssertResult("K(o, V) = o.V\nK(7, {x + 1})", Atom(8));
        AssertResult("K = o~.V\nK({x + 1}, 7)", Atom(8));
        AssertResult("K = o.~V\nK({x + 1}, 7)", Atom(8));
    }

    [Fact]
    public void Law_StructuralPrivateMember_IsReachedByBothSpellings()
    {
        // Structural dot access ignores `public`: a private member is still
        // reached, and Grace does not change that — the graced forms infer their
        // signatures (receiver and `V` free) and the private member still wins.
        const string privateMember = "Obj = {\n    V = 42\n    0\n}\n";
        AssertResult(privateMember + "K(o, V) = o.V\nK(Obj, {x + 100})", Atom(42));
        AssertResult(privateMember + "K = o~.V\nK({x + 100}, Obj)", Atom(42));
        AssertResult(privateMember + "K = o.~V\nK({x + 100}, Obj)", Atom(42));
    }

    [Fact]
    public void Law_NoStructuralMember_FallsBackInAllSpellings()
    {
        // `Obj` has no `Inc`, so the edge calls `Inc` lexically with the
        // receiver's own value (its output row `0`). A graced FREE receiver bound
        // to Obj at the call behaves identically; a marker on the bound `Obj`
        // itself, or on the visible `Inc`, is the ineffective-Grace error (F10).
        const string defs = "Inc(x) = x + 1\nObj = {\n    V = 42\n    0\n}\n";
        AssertResult(defs + "Obj.Inc", Atom(1));
        AssertResult(defs + "K = o~.Inc\nK(Obj)", Atom(1));
        AssertGraceIneffective(defs + "Obj~.Inc", "Obj", "it already resolves to a property");
        AssertGraceIneffective(defs + "Obj.~Inc", "Inc", "it already resolves to a property");
    }

    // ── C. Static fallback certainty drives inference ───────────────────────

    [Fact]
    public void Certainty_GuaranteedStructuralMember_InfersNoFallbackParameter()
    {
        // The receiver's statically known algorithm declares `t`, so the
        // fallback can NEVER be selected: no spurious `t` parameter — and a marker
        // on either name of that edge could reorder nothing (F10): the graced
        // spellings are rejected, their recovery trees keeping the empty signature.
        Assert.Empty(ParamsOf(
            """
            Obj = {
                public t = 42
                0
            }
            K = Obj.t
            K
            """));
        var gracedReceiver = AssertGraceIneffective("Obj = { public t = 42\n0 }\nK = Obj~.t", "Obj", "it already resolves to a property");
        Assert.Empty(Assert.Single(gracedReceiver.Root.Properties, p => p.Name == "K").Value.Params);
        var gracedMember = AssertGraceIneffective("Obj = { public t = 42\n0 }\nK = Obj.~t", "t", "the member 't' always resolves structurally on its receiver");
        Assert.Empty(Assert.Single(gracedMember.Root.Properties, p => p.Name == "K").Value.Params);
        AssertResult(
            """
            Obj = {
                public t = 42
                0
            }
            K = Obj.t
            K
            """,
            Atom(42));
    }

    [Fact]
    public void Certainty_KnownStructuralMiss_InfersTheFallbackParameter()
    {
        // The receiver is a statically known algorithm WITHOUT the member, so
        // the fallback is unconditionally selected and its callable
        // participates. (`S` itself is a visible sibling, not a free name — so
        // `S~.t` graces a bound name and is rejected (F10), while `S.~t` graces
        // the participating free member and is effective.)
        Assert.Equal(["t"], ParamsOf("S = 1, 2, 3\nK = S.t\nK({a:0 + 100})"));
        AssertGraceIneffective("S = 1, 2, 3\nK = S~.t", "S", "it already resolves to a property");
        Assert.Equal(["t"], ParamsOf("S = 1, 2, 3\nK = S.~t"));
        AssertResult("S = 1, 2, 3\nK = S.t\nK({a:0 + 100})", Atom(101));
        AssertResult("S = 1, 2, 3\nK = S.~t\nK({a:0 + 100})", Atom(101));
    }

    [Fact]
    public void Certainty_OpaqueReceiver_InfersTheFallbackParameter()
    {
        // An implicit-parameter receiver is runtime-valued: the fallback MAY
        // be selected, so it participates (the primary law case).
        Assert.Equal(["a", "t"], ParamsOf("K = a.t"));
    }

    [Fact]
    public void Certainty_VisibleLexicalMember_IsNotAFreeName()
    {
        // A member name that resolves lexically is not free, so it never
        // becomes a parameter regardless of fallback certainty — and a marker on
        // it is the ineffective-Grace error (F10); the graced receiver `a` is free.
        Assert.Equal(["a"], ParamsOf("t(x) = x + 1\nK = a.t\nK(7)"));
        Assert.Equal(["a"], ParamsOf("t(x) = x + 1\nK = a~.t\nK(7)"));
        AssertGraceIneffective("t(x) = x + 1\nK = a.~t\nK(7)", "t", "it already resolves to a property");
        AssertResult("t(x) = x + 1\nK = a.t\nK(7)", Atom(8));
        AssertResult("t(x) = x + 1\nK = a~.t\nK(7)", Atom(8));
    }

    [Fact]
    public void Certainty_StringIntrinsic_IsNeverAFallback()
    {
        // The dot-only `.string` intrinsic pre-empts both channels on every
        // receiver shape, so it contributes no fallback parameter — and prefix
        // Grace on it is the ineffective-Grace error (F10), while postfix Grace on
        // the free receiver stays effective.
        Assert.Equal(["v"], ParamsOf("K = v.string"));
        Assert.Equal(["v"], ParamsOf("K = v~.string"));
        AssertGraceIneffective("K = v.~string", "string", "'.string' is the dot-only intrinsic");
    }

    // ── D. May-selection (signature) vs must-selection (closed lists) ───────

    [Fact]
    public void MayVsMust_ClosedExplicitListDoesNotRequireTheFallbackName()
    {
        // Parameter inference asks "CAN the fallback be needed?" — the closed
        // explicit-parameter-list rule asks the DEFINITE question and takes no
        // fallback contribution, so the common structural-accessor idiom stays
        // legal without declaring every member name.
        var source =
            """
            Get(obj) = obj.size
            Obj = {
                public size = 11
                0
            }
            Get(Obj)
            """;
        Assert.Equal(["obj"], ParamsOf(source, "Get"));
        AssertResult(source, Atom(11));

        // The same body still reaches the lexical fallback at runtime.
        AssertResult("Get(obj) = obj.size\nsize(v) = 77\nGet(3)", Atom(77));

        // And an unresolvable member in a closed list is a RUNTIME miss, not a
        // parse-time undeclared-identifier error. (Under the closed list the
        // graced spelling `K(a) = a~.t` is the ineffective-Grace error instead —
        // F10 — while the free-name spelling stays a runtime miss.)
        Assert.IsType<EvalError.UnknownName>(AssertBothEvaluatorsFail("K(a) = a.t\nK(7)"));
        AssertGraceIneffective("K(a) = a~.t\nK(7)", "a", "it already resolves to an explicit parameter");
    }

    [Fact]
    public void MayVsMust_ConditionalBranchBodyDoesNotRequireTheFallbackName()
        // The full-input-specification rule is the same DEFINITE question: a
        // dot member is not reported as an undeclared branch identifier, and
        // the fallback arm still resolves lexically at runtime.
        => AssertResult(
            """
            size(v) = v * 2
            P(0) = 0
            P(x) = x.size
            P(21)
            """,
            Atom(42));

    // ── E. Special forms are shared, never Grace-sensitive ──────────────────

    [Fact]
    public void SpecialForm_StringIntrinsic_IsIdenticalInBothSpellings()
    {
        // The graced receiver is a FREE name bound at the call; `v = 5` then
        // `v~.string` would grace a bound property and `v.~string` the intrinsic
        // itself — both the ineffective-Grace error (F10), never a silent no-op.
        AssertResult("v = 5\nv.string", Str("5"));
        AssertResult("K = v~.string\nK(5)", Str("5"));
        AssertGraceIneffective("v = 5\nv~.string", "v", "it already resolves to a property");
        AssertGraceIneffective("v = 5\nv.~string", "string", "'.string' is the dot-only intrinsic");
        AssertSameElaboratedBody("K = v~.string", "K(v) = v.string");

        // The intrinsic pre-empts a same-named lexical callable in every
        // spelling — it is an ordinary-dot member rule, not a Grace rule.
        AssertResult("string(x) = x + 100\nv = 5\nv.string", Str("5"));
        AssertResult("string(x) = x + 100\nK = v~.string\nK(5)", Str("5"));
    }

    [Fact]
    public void SpecialForm_SequenceBuiltins_AreIdenticalInBothSpellings()
    {
        // Graced spellings use a FREE receiver bound at the call (`K = v~.count`,
        // `K(S)`); a marker on the bound property `S` or on the builtin member
        // (`S.~count`) is the ineffective-Grace error (F10).
        Assert.Equal(["v"], ParamsOf("K = v.count"));
        Assert.Equal(["v", "n"], ParamsOf("K = v.take(n)"));
        Assert.Equal(["v"], ParamsOf("K = v~.count"));
        AssertResult("S = 1, 2, 3\nS.count", Atom(3));
        AssertResult("S = 1, 2, 3\nK = v~.count\nK(S)", Atom(3));
        AssertGraceIneffective("S = 1, 2, 3\nS~.count", "S", "it already resolves to a property");
        AssertGraceIneffective("S = 1, 2, 3\nS.~count", "count", "it already resolves to the builtin 'count'");
        AssertResult("S = 1, 2, 3\nS.take(2)", List(Atom(1), Atom(2)));
        AssertResult("S = 1, 2, 3\nK = v~.take(2)\nK(S)", List(Atom(1), Atom(2)));
        AssertSameElaboratedBody("K = v~.take(2)", "K(v) = v.take(2)");

        // A user `count` shadows the builtin in BOTH spellings.
        AssertResult("count(x) = 99\nS = 1, 2, 3\nS.count", Atom(99));
        AssertResult("count(x) = 99\nS = 1, 2, 3\nK = v~.count\nK(S)", Atom(99));

        // Dot-call passes a value: the dotted receiver IS the direct call's
        // argument, and Grace changes nothing about that — a collecting callee
        // binds it by the collector supply-boundary law (a lone written
        // sequence opens one level) in every spelling.
        AssertResult("S = 1, 2, 3\nK = v~.count\nK(S)", Atom(3));
        AssertResult("S = 1, 2, 3\ncount(S)", Atom(3));
        AssertResult("Collect(*items) = items\nS = 1, 2, 3\nK = v~.Collect\nK(S)", List(Atom(1), Atom(2), Atom(3)));
        AssertResult("Collect(*items) = items\n(1, 2, 3).Collect", List(Atom(1), Atom(2), Atom(3)));
        AssertResult("Collect(*items) = items\n(1, 2, 3)*.Collect", List(Atom(1), Atom(2), Atom(3)));
        AssertResult("Collect(*items) = items\nS = 1, 2, 3\nK = v~.Collect(0)\nK(S)", List(Seq(Atom(1), Atom(2), Atom(3)), Atom(0)));
        AssertResult("Collect(*items) = items\nL = [1, 2, 3]\nK = v~.Collect\nK(L)", List(List(Atom(1), Atom(2), Atom(3))));
    }

    [Fact]
    public void SpecialForm_ReceiverValue_IsSharedByBothSpellings()
    {
        // The receiver is the ordinary leading argument (dot-call passes a
        // value), so Grace inherits that unchanged: a WRITTEN GROUP receiver
        // and a NAMED receiver are each ONE written slot, which a lone
        // collector opens one level (the collector supply-boundary law), and
        // the spread marker supplies the same items as final slots. A group is
        // not a Grace-eligible receiver, so only the named form has both
        // spellings — and they agree exactly.
        AssertResult("Mean(*Vector) = Vector.sum / Vector.count\n(1, 2, 2.718)*.Mean", Atom(1.906m));
        AssertResult("Mean(*Vector) = Vector.sum / Vector.count\n(1, 2, 2.718).Mean", Atom(1.906m));
        AssertResult("Collect(*items) = items\n(1, 2, 3).Collect", List(Atom(1), Atom(2), Atom(3)));
        AssertResult("Collect(*items) = items\nS = 1, 2, 3\nS.Collect", List(Atom(1), Atom(2), Atom(3)));
        AssertResult("Collect(*items) = items\nS = 1, 2, 3\nK = v~.Collect\nK(S)", List(Atom(1), Atom(2), Atom(3)));
        AssertGraceIneffective("Collect(*items) = items\nS = 1, 2, 3\nS~.Collect", "S", "it already resolves to a property");
        AssertSameElaboratedBody("Collect(*items) = items\nK = v~.Collect", "Collect(*items) = items\nK(v) = v.Collect");
        AssertParseFails("Collect(*items) = items\n(1, 2, 3)~.Collect", GraceEligibilityFragment);
    }

    [Fact]
    public void SpecialForm_ValueKindsWorkThroughFreeReceivers()
    {
        // Every value kind flows through the graced edge when the receiver is a
        // FREE name bound at the call; on the bound property itself the marker is
        // the ineffective-Grace error (F10).
        AssertResult("L = [1, 2, 3]\nK = v~.sum\nK(L)", Atom(6));
        AssertResult("E = ()\nK = v~.count\nK(E)", Atom(0));
        AssertResult("S = 1, 2, 3\nK = v~.first\nK(S)", Atom(1));
        AssertGraceIneffective("L = [1, 2, 3]\nL~.sum", "L", "it already resolves to a property");
    }

    [Fact]
    public void SpecialForm_MemberResolvesThroughOpen()
    {
        AssertResult(
            """
            Lib = {
                public V(x) = 99
            }
            R = {
                open Lib
                K = v~.V
                K(5)
            }
            R
            """,
            Atom(99));
        // A marker on the sibling property `v` (or on the opened `V`) is rejected.
        AssertGraceIneffective(
            "Lib = {\n    public V(x) = 99\n}\nR = {\n    open Lib\n    v = 5\n    v~.V\n}\nR",
            "v",
            "it already resolves to a property");
        AssertGraceIneffective(
            "Lib = {\n    public V(x) = 99\n}\nR = {\n    open Lib\n    K = v.~V\n    K(5)\n}\nR",
            "V",
            "it already resolves to an opened property");
    }

    [Fact]
    public void SpecialForm_GracedDotIsNotAnOpenTarget()
        // `open` consumes structural algorithm identity; there is no parameter
        // inference there, so a grace-marked target is not an open form. The
        // ordinary dotted path stays valid.
        => AssertParseFails(
            """
            M = {
                public C = 5
            }
            R = {
                open M~.C
                C
            }
            R
            """,
            "'grace' is not allowed in open declarations");

    [Fact]
    public void SpecialForm_InArgumentListAndCallbackSlots()
    {
        // The graced receiver is a FREE name in every slot kind (call argument,
        // list element, callback body, reduce initial); `v = 5` then `v~.Inc`
        // would grace a bound property — the ineffective-Grace error (F10).
        AssertResult("Inc(x) = x + 1\nF(a, b) = a * 10 + b\nK = F(v~.Inc, 2)\nK(5)", Atom(62));
        AssertResult("Inc(x) = x + 1\nK = [v~.Inc, 9]\nK(5)", List(Atom(6), Atom(9)));
        AssertResult("Inc(x) = x + 1\nmap((1, 2, 3), {a~.Inc})", List(Atom(2), Atom(3), Atom(4)));
        AssertResult("Id(x) = x\nK = reduce((1, 2, 3), {a + b}, v~.Id)\nK(5)", Atom(11));
        AssertGraceIneffective("Inc(x) = x + 1\nv = 5\n[v~.Inc, 9]", "v", "it already resolves to a property");
    }

    [Fact]
    public void SpecialForm_SequencePipelineEdge_IsSharedByBothSpellings()
    {
        AssertResult("K(xs) = xs.filter({a > 1}).count\nK((1, 2, 3))", Atom(2));
        AssertResult("K = xs~.filter({a > 1}).count\nK((1, 2, 3))", Atom(2));
        AssertSameElaboratedBody("K = xs~.filter({a > 1}).count", "K(xs) = xs.filter({a > 1}).count");
        AssertGraceIneffective("K(xs) = xs~.filter({a > 1}).count\nK((1, 2, 3))", "xs", "it already resolves to an explicit parameter");
    }

    // ── F. Argument-list forms ──────────────────────────────────────────────

    [Fact]
    public void ArgumentList_ExtraArgumentsFollowTheReceiver()
    {
        // The graced receiver is a FREE name bound at the call (`K(3)`).
        AssertResult("F(x, y, z) = x*100 + y*10 + z\nv = 3\nv.F(1, 2)", Atom(312));
        AssertResult("F(x, y, z) = x*100 + y*10 + z\nK = v~.F(1, 2)\nK(3)", Atom(312));
        AssertResult("F(x, y, z) = x*100 + y*10 + z\nF(3, 1, 2)", Atom(312));
    }

    [Fact]
    public void ArgumentList_ExplicitEmptyArgsKeepTheOrdinaryDotDistinction()
    {
        // `v~.F()` and `v~.F` keep the ordinary dot edge's property-style vs
        // explicit-argument-list distinction (Args null vs empty) — the marker
        // changes neither. (`v` is K's free receiver name, bound by `K(3)`.)
        static Expr.DotCall BodyOfK(string source)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            return Assert.IsType<Expr.DotCall>(Assert.Single(root.Properties, p => p.Name == "K").Value.Output[0]);
        }

        var withArgs = BodyOfK("F(x) = x + 1\nK = v~.F()\nK(3)");
        Assert.NotNull(withArgs.Args);
        Assert.Empty(withArgs.Args);

        var propertyStyle = BodyOfK("F(x) = x + 1\nK = v~.F\nK(3)");
        Assert.Null(propertyStyle.Args);

        AssertResult("F(x) = x + 1\nK = v~.F()\nK(3)", Atom(4));
        AssertResult("F(x) = x + 1\nK = v~.F\nK(3)", Atom(4));
    }

    [Fact]
    public void ArgumentList_MemberIdentifierKeepsItsSourceSpan()
    {
        static Expr.DotCall Body(string source)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            return Assert.IsType<Expr.DotCall>(root.Properties[0].Value.Output[0]);
        }

        // The member identifier keeps its exact source span in every spelling
        // (hover/navigation anchor), and the receiver keeps its own span: in
        // `K = a~.t` / `K = a.~t` the member is at column 8 and the receiver
        // name at column 5 (the marker occupies its own column).
        foreach (var source in new[] { "K = a~.t\nK({a+1}, 7)", "K = a.~t\nK({a+1}, 7)" })
        {
            var dotCall = Body(source);
            Assert.Equal(new SourceSpan(1, 8, 1, 9), dotCall.MemberSpan);
            Assert.Equal(new SourceSpan(1, 5, 1, 6), dotCall.Target.Span);
        }

        var ordinary = Body("K(a, t) = a.t\nK(7, {a+1})");
        Assert.Equal(new SourceSpan(1, 13, 1, 14), ordinary.MemberSpan);
    }

    // ── G. Chaining ─────────────────────────────────────────────────────────

    [Fact]
    public void Chain_GracedDotThenOrdinaryContinuation()
    {
        // The first edge is an ordinary dot edge; `.string` then applies to
        // its result exactly as after an ungraced edge. (The graced names are
        // free: under an explicit list the markers are the ineffective-Grace
        // error, F10.)
        AssertResult("K = a~.t.string\nK({a+1}, 7)", Str("8"));
        AssertResult("K = a.~t.string\nK({a+1}, 7)", Str("8"));
        AssertSameElaboratedBody("K = a~.t.string", "K(t, a) = a.t.string");
        AssertGraceIneffective("K(a, t) = a~.t.string\nK(7, {a+1})", "a", "it already resolves to an explicit parameter");
    }

    [Fact]
    public void Chain_SecondPostfixGraceEdge_IsRejected()
        // The second edge's receiver is the first edge's RESULT — a non-name
        // expression — so it cannot carry the single-name Grace ordering.
        => AssertParseFails(
            """
            Dub(x) = x * 2
            Inc(x) = x + 1
            v = 5
            v~.Inc~.Dub
            """,
            GraceEligibilityFragment);

    [Fact]
    public void Chain_StructuralEdgeThenPostfixGrace_IsRejected()
        => AssertParseFails(
            """
            Inc(x) = x + 1
            Obj = {
                public V = 42
                0
            }
            Obj.V~.Inc
            """,
            GraceEligibilityFragment);

    [Fact]
    public void Chain_OrdinaryDotChain_IsUnchanged()
    {
        AssertResult("Inc(x) = x + 1\n1.Inc.Inc.Inc", Atom(4));
        AssertResult("Inc(x) = x + 1\nInc(Inc(Inc(1)))", Atom(4));
    }

    // ── H. Name-occurrence eligibility (the narrow Grace law) ───────────────

    [Fact]
    public void Eligibility_CompoundReceiver_IsRejectedNotDistributed()
    {
        AssertParseFails("K = (x + y)~.t", GraceEligibilityFragment);
        // The ORDINARY complex-receiver edge stays valid.
        AssertResult("K(x, y) = (x + y).t\nt(v) = v * 2\nK(1, 2)", Atom(6));
        // Prefix Grace after the dot decorates the bare fallback name, not the
        // compound receiver, and therefore remains eligible — on a FREE member
        // name: base order (x, y, t) becomes (x, t, y). (On a declared `t` the
        // marker is the ineffective-Grace error, F10.)
        AssertResult("K = (x + y).~t\nK(1, {v * 2}, 2)", Atom(6));
        AssertGraceIneffective("K(x, y, t) = (x + y).~t\nK(1, 2, {v * 2})", "t", "it already resolves to an explicit parameter");
    }

    [Fact]
    public void Eligibility_RejectsEveryNonNameShape()
    {
        // The ONE eligibility law across receiver shapes: literals, groups,
        // calls, dot results, index results, lists, braces, strings, and
        // spreads all reject with the same diagnostic when postfix Grace is
        // applied to the receiver expression.
        AssertParseFails("t(a) = a + 1\n5~.t", GraceEligibilityFragment);
        AssertParseFails("K = f(x)~.t", GraceEligibilityFragment);
        AssertParseFails("K = [x, y]~.t", GraceEligibilityFragment);
        AssertParseFails("K = a.b~.t", GraceEligibilityFragment);
        AssertParseFails("S = 1, 2, 3\nK = (S:0)~.t", GraceEligibilityFragment);
        AssertParseFails("t(a) = a\n{1}~.t", GraceEligibilityFragment);
        AssertParseFails("t(a) = a\n'text'~.t", GraceEligibilityFragment);
        AssertParseFails("[1, 2, 3]~.sum", GraceEligibilityFragment);
        AssertParseFails("()~.count", GraceEligibilityFragment);
        AssertParseFails("(1, 2, 3)~.first", GraceEligibilityFragment);

        // The corresponding prefix-member forms are eligible because the
        // decorated occurrence is the bare member/fallback name — a FREE name
        // that joins the enclosing signature (on a declared `t` the marker is
        // the ineffective-Grace error, F10).
        AssertResult("K = 5.~t\nK({a + 1})", Atom(6));
        AssertResult("K = [1, 2].~t\nK({a})", List(Atom(1), Atom(2)));
        AssertGraceIneffective("t(a) = a + 1\n5.~t", "t", "it already resolves to a property");
    }

    [Fact]
    public void Eligibility_GroupedReceiver_IsRejected_GroupedAndCaptureReceiversUnchanged()
    {
        // A marker after a closing parenthesis is not attached to a bare name, so
        // parentheses never smuggle an expression into Grace (the attachment law).
        AssertParseFails(StructuralSplit + "\n(Obj)~.V", GraceEligibilityFragment);
        AssertParseFails(StructuralSplit + "\n(Obj*)~.V", GraceEligibilityFragment);
        // PARENTHESES GROUP SYNTAX: `(Obj).V` IS `Obj.V`, so the structural member wins
        // exactly as in the bare spelling ...
        AssertResult(StructuralSplit + "\n(Obj).V", Atom(42));
        AssertResult(StructuralSplit + "\nObj.V", Atom(42));
        // ... while a genuine capture receiver (a lone spread slot) has no structural
        // identity, so the lexical `V` wins there.
        AssertResult(StructuralSplit + "\n(Obj*).V", Atom(99));
    }

    [Fact]
    public void Eligibility_SpreadReceiver_IsRejected_FluentSupplyUnchanged()
    {
        AssertResult("Collect(*items) = items\n[1, 2]*.Collect", List(Atom(1), Atom(2)));
        AssertParseFails("Collect(*items) = items\n[1, 2]*~.Collect", GraceEligibilityFragment);
        // Prefix member Grace on the lowered lexical callee is effective on a FREE
        // callee name (bound by the call); on the declared `Collect` it is the
        // ineffective-Grace error (F10).
        AssertResult("K = [1, 2]*.~F\nK({a + b})", Atom(3));
        AssertGraceIneffective("Collect(*items) = items\n[1, 2]*.~Collect", "Collect", "it already resolves to a property");
        AssertParseFails("K = xs*~.F", GraceEligibilityFragment);
    }

    [Theory]
    [InlineData("~.F", 9)]
    [InlineData("~ .F", 9)]
    [InlineData("~~.F", 10)]
    [InlineData("~ ~.F", 11)]
    [InlineData("~\n.F", 9)]
    public void InvalidGraceBeforeDot_KeepsSpreadRecoveryIndependentOfLayout(string continuation, int markerEnd)
    {
        var syntax = Parser.ParseSyntax("K = xs*" + continuation);
        var error = Assert.Single(syntax.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, error.Code);
        Assert.Contains(GraceEligibilityFragment, error.Message);
        Assert.Equal(new SourceSpan(1, 8, 1, markerEnd), error.Span);

        // A Grace run followed by a dot cannot supply a multiplication RHS.
        // Recovery removes the invalid annotation and keeps the same fluent
        // call F(xs*) in every layout, never xs * 0.F.
        var call = Assert.IsType<Expr.Call>(Assert.Single(Assert.Single(syntax.Root.Properties).Value.Output));
        Assert.Equal("F", Assert.IsType<Expr.Resolve>(call.Function).Name);
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args));
        Assert.Equal("xs", Assert.IsType<Expr.Resolve>(spread.Operand).Name);
    }

    [Fact]
    public void Eligibility_InvalidReceiver_RecoversAsTheOrdinaryGracelessEdge()
    {
        const string source = "K = f(x)~.t";
        var syntax = Parser.ParseSyntax(source);

        Assert.Single(
            syntax.Diagnostics,
            diagnostic => diagnostic.Message.Contains(GraceEligibilityFragment, StringComparison.Ordinal));

        // Recovery is the ordinary dot edge (as if the marker were absent):
        // useful structure and spans for tooling, no ordering assigned.
        var rawK = Assert.IsType<Algorithm.User>(Assert.Single(syntax.Root.Properties).Value);
        var rawEdge = Assert.IsType<Expr.DotCall>(Assert.Single(rawK.Output));
        Assert.Equal("t", rawEdge.Name);
        Assert.IsType<Expr.Call>(rawEdge.Target);
        Assert.Equal(new SourceSpan(1, 11, 1, 12), rawEdge.MemberSpan);
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(syntax.Root));

        var elaborated = Parser.Parse(source);
        Assert.True(elaborated.HasErrors);
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(elaborated.Root));
        // No Grace ordering was assigned: the recovered signature is the
        // ordinary semantic occurrence order (the receiver call's names,
        // then the member/fallback occurrence).
        Assert.Equal(
            ["f", "x", "t"],
            Assert.Single(elaborated.Root.Properties).Value.Params);
    }

    // ── I. Adjacency and Grace preservation ─────────────────────────────────

    [Fact]
    public void Adjacency_AttachedTildeBeforeASpacedDot_KeepsGraceMeaning()
        // `a~ .t`: the postfix marker is attached to `a` (the marker attachment
        // law), and the space before the dot is ordinary whitespace before a
        // same-line postfix continuation, so this is postfix grace on `a` plus
        // the ordinary dot edge. Postfix grace (+1) moves `a` later than the
        // following member/fallback occurrence: `K` infers `(t, a)`.
        => AssertResult("K = a~ .t\nK({a+1}, 7)", Atom(8));

    [Fact]
    public void Adjacency_AttachedTildeBeforeASpacedDot_HasTheOrdinaryPostfixGraceOrder()
        => Assert.Equal(["t", "a"], ParamsOf("K = a~ .t"));

    [Theory]
    [InlineData("K = a ~ .t", 5, 8)]
    [InlineData("K = a ~.t", 5, 8)]
    public void Adjacency_DetachedTilde_IsRejectedByTheAttachmentLaw_AndRecoversToThePlainEdge(
        string source, int startColumn, int endColumn)
    {
        // `a ~ .t`: the postfix marker is NOT attached to `a`, so it decorates
        // nothing. The marker attachment law reports it (the diagnostic spans
        // the name through the marker), and the recovered tree is the plain
        // ordinary dot edge `a.t` with the ungraced occurrence order `(a, t)` —
        // a detached marker never silently keeps the `(t, a)` meaning of `a~.t`.
        var syntax = Parser.ParseSyntax(source);
        var error = Assert.Single(syntax.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, error.Code);
        Assert.Equal(
            "The Grace marker `~` must be directly attached to the name it decorates: write `~a` or `a~`.",
            error.Message);
        Assert.Equal(new SourceSpan(1, startColumn, 1, endColumn), error.Span);

        var elaborated = Parser.Parse(source);
        Assert.Equal(["a", "t"], Assert.Single(elaborated.Root.Properties).Value.Params);
        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(elaborated.Root.Properties).Value.Output[0]);
        Assert.IsType<Expr.Param>(dotCall.Target); // no Grace wrapper survives
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(elaborated.Root));
    }

    [Theory]
    [InlineData("K = a.~ t", 7, 10)]
    [InlineData("K = a.~ ~t", 7, 11)]
    [InlineData("K = a.~~ ~t", 7, 12)]
    public void MemberGrace_DetachedFromTheMemberName_IsRejectedByTheAttachmentLaw(
        string source, int startColumn, int endColumn)
    {
        // `a.~ t`: the member prefix marker begins at the dot (member Grace
        // syntax) but is not attached to `t`, so the attachment law rejects it
        // and the recovered edge is the plain `a.t` with the `(a, t)` order.
        var syntax = Parser.ParseSyntax(source);
        var error = Assert.Single(syntax.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, error.Code);
        Assert.Equal(
            "The Grace marker `~` must be directly attached to the name it decorates: write `~t` or `t~`.",
            error.Message);
        Assert.Equal(new SourceSpan(1, startColumn, 1, endColumn), error.Span);

        var elaborated = Parser.Parse(source);
        Assert.Equal(["a", "t"], Assert.Single(elaborated.Root.Properties).Value.Params);
        Assert.Null(DotCallElaborationInvariant.CheckElaborated(elaborated.Root));
    }

    [Fact]
    public void Adjacency_RepeatedPostfixGrace_ComposesWithDot()
        => AssertResult("K = a~~.t\nK({a+1}, 7)", Atom(8));

    [Fact]
    public void Adjacency_PostfixReceiverAndPrefixMemberGrace_BothCompose()
    {
        Assert.Equal(["t", "a"], ParamsOf("K = a~.~t"));
        AssertResult("K = a~.~t\nK({a+1}, 7)", Atom(8));
    }

    [Fact]
    public void Adjacency_PostfixGrace_DoesNotContinueFromANewPhysicalLine()
        => AssertParseFails(
            "K(a, t) = a\n~.t\nK(7, {a+1})",
            "Grace `~` can only be applied to a parameter or name occurrence");

    [Fact]
    public void Adjacency_LeadingDotContinuation_CanCarryPrefixMemberGrace()
    {
        // The graced member is a FREE name (K infers `(t, a)`); on a declared
        // `t` the marker would be the ineffective-Grace error (F10).
        var source = "K = a\n.~t\nK({a+1}, 7)";
        var root = SourceProvenance.ParseValid(source).Root;
        var k = Assert.Single(root.Properties, p => p.Name == "K").Value;
        Assert.Equal(["t", "a"], k.Params);
        var edge = Assert.IsType<Expr.DotCall>(k.Output[0]);
        Assert.Equal("t", edge.Name);
        AssertResult(source, Atom(8));
    }

    [Fact]
    public void Adjacency_PrefixMemberGrace_IsLineLocal_OrdinaryTrailingDotIsUnchanged()
    {
        // A trailing dot may precede a newline; an annotation may not reach
        // across it to acquire its name. B4's line-local law applies to the
        // member occurrence just as it does to a primary occurrence.
        var graced = Parser.ParseSyntax("a.~\nt\n7");
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, Assert.Single(graced.Diagnostics).Code);
        Assert.Equal("t", Assert.IsType<Expr.Resolve>(graced.Root.Output[1]).Name);
        AssertResult("Obj = {public V = 42}\nObj.\nV", Atom(42));
    }

    // ── J. The stored fallback decides — wrapper topology is irrelevant ─────

    [Fact]
    public void WrapperDivergence_IsGone_ChainedDotAgreesWithPlainForm()
    {
        // 0.8.159 residual defect: with a same-name visible property, the
        // chained `a.t.string` evaluated its inner dot edge under a synthetic
        // algorithm-position wrapper that hid the parameter's local ownership
        // from the runtime gate, so the dotted form resolved the property
        // while plain `t(a).string` resolved the parameter. The binding now
        // rides the expression itself, so wrapper topology cannot change it.
        AssertResult("t = 5\nK(a, t) = a.t.string\nK(7, {a+1})", Str("8"));
        AssertResult("t = 5\nK(a, t) = t(a).string\nK(7, {a+1})", Str("8"));
    }

    [Fact]
    public void HostBuiltDotCall_WithoutFallback_KeepsPlainLexicalSemantics()
    {
        // A host-built DotCall carries no elaborated fallback (null =>
        // Resolve(Name)): with no lexical `t` in sight the member fails as
        // unknown even though a dynamically visible `t` binding exists — the
        // stored identity, not the runtime environment, decides.
        var k = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [new CaptureParameterPattern("a"), new CaptureParameterPattern("t")],
            Opens: [],
            Properties: [],
            Output: [new Expr.DotCall(new Expr.Param("a"), "t")]);
        var increment = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [new CaptureParameterPattern("x")],
            Opens: [],
            Properties: [],
            Output: [new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1m))]);
        var root = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties: [new Property("K", k)],
            Output:
            [
                new Expr.Call(
                    new Expr.Resolve("K"),
                    [new Expr.Num(7m), new Expr.AlgorithmExpr(increment)]),
            ]);

        var plain = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.True(plain.IsError);
        Assert.IsType<EvalError.UnknownName>(Innermost(plain.Error));
    }

    [Fact]
    public void OptimizerOnOrOff_SeesTheSameEdgeInBothSpellings()
    {
        // Optimizer eligibility is decided on the elaborated body, which is
        // identical for both spellings, so neither the results nor the
        // optimizer's own view can depend on source grace provenance.
        static Result Run(string source, bool loops, bool pipelines)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            var evaluated = Evaluator.Run(
                new Expr.AlgorithmExpr(root),
                new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(),
                loops,
                loopDiagnostics: null,
                pipelines,
                sequenceDiagnostics: null);
            Assert.False(evaluated.IsError, $"Unexpected error: {(evaluated.IsError ? evaluated.Error : null)}");
            return evaluated.Value;
        }

        // Every graced spelling graces a FREE name (a marker on a bound receiver,
        // a builtin member, or a member the receiver declares is the
        // ineffective-Grace error, F10, and never reaches the evaluator).
        foreach (var (ordinary, graced) in new[]
        {
            ("K = a.t\nK(7, {x + 1})", "K = a~.t\nK({x + 1}, 7)"),
            ("K = a.t\nK(7, {x + 1})", "K = a.~t\nK({x + 1}, 7)"),
            ("K(xs) = xs.filter({a > 1}).count\nK((1, 2, 3))", "K = xs~.filter({a > 1}).count\nK((1, 2, 3))"),
            ("S = 1, 2, 3\nS.take(2)", "S = 1, 2, 3\nK = v~.take(2)\nK(S)"),
            ("V(x) = 99\nObj = {\n    public V = 42\n    0\n}\nObj.V", "V(x) = 99\nObj = {\n    public V = 42\n    0\n}\nRead = o~.V\nRead(Obj)"),
            ("Obj = {\n    public V = 42\n    0\n}\nObj.V", "Obj = {\n    public V = 42\n    0\n}\nRead = o.~V\nRead({x}, Obj)"),
        })
        {
            foreach (var (loops, pipelines) in new[] { (true, true), (false, false) })
            {
                Assert.True(
                    Result.ValueComparer.Equals(
                        Run(ordinary, loops, pipelines),
                        Run(graced, loops, pipelines)),
                    $"Spellings diverged with loops={loops}, pipelines={pipelines}:{Environment.NewLine}{ordinary}");
            }

            Assert.True(
                Result.ValueComparer.Equals(
                    Run(graced, true, true),
                    Run(graced, false, false)),
                $"Optimizer changed the result of:{Environment.NewLine}{graced}");
        }
    }

    [Fact]
    public void UnknownMember_RendersTheOrdinaryDotDiagnostic_AndTheGracedClosedListTwinIsRejected()
    {
        // The dot edge renders the dot diagnostic on a member miss — never
        // call-style wording. A member can only miss at runtime under a CLOSED
        // list (a free member name would join the signature instead), and under a
        // closed list the graced twin is the ineffective-Grace error (F10) — it
        // never reaches the evaluator at all.
        static string MessageOf(string source)
            => KatLangError.FromEvalError(
                Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root)).Error).Message;

        var ordinary = MessageOf("K(a) = a.Missing\nK(1)");
        Assert.Contains("Property 'Missing' was not found on", ordinary);
        AssertGraceIneffective("K(a) = a~.Missing\nK(1)", "a", "it already resolves to an explicit parameter");
    }
}
