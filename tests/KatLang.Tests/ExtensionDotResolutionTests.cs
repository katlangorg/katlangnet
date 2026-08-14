namespace KatLang.Tests;

/// <summary>
/// Focused regression matrix for the EXTENSION-DOT language rule and the
/// elaborated dot-edge model behind it.
///
/// The language rule: `.` performs structural member lookup first and uses
/// lexical extension fallback only when no structural member is available;
/// `~.` / `.~` explicitly selects extension-call resolution and therefore
/// bypasses structural member lookup, and in an extension dot the member is a
/// callable-name occurrence that participates in ordinary parameter/name
/// resolution (`K = a~.t` infers the same parameters as `K = t(a)`).
///
/// The architectural rule: the front-end decides the member's lexical-fallback
/// identity ONCE (`Expr.DotCall.LexicalFallback` = Resolve or Param) and every
/// runtime consumer CONSUMES that stored decision; no subsystem reconstructs
/// Param-vs-Resolve from runtime environments. Lean: `Expr.dotMember`,
/// CoreTests `extensionDot*` guards.
/// </summary>
public class ExtensionDotResolutionTests
{
    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result List(params Result[] items) => new Result.ListValue(items);

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

    // ── A. Explicit extension syntax: both spellings, one semantic form ─────

    [Fact]
    public void ExplicitExtension_TildeDot_ResolvesParameterMember()
        => AssertResult(
            """
            K(a, t) = a~.t
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void ExplicitExtension_DotTilde_ResolvesParameterMember()
        => AssertResult(
            """
            K(a, t) = a.~t
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void BothSpellings_NormalizeToOneSemanticNode()
    {
        static Expr.DotCall ParseEdge(string source)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            var body = Assert.IsType<Algorithm.User>(root.Properties[0].Value);
            return Assert.IsType<Expr.DotCall>(body.Output[0]);
        }

        var tildeDot = ParseEdge("K(a, t) = a~.t\nK(7, {a+1})");
        var dotTilde = ParseEdge("K(a, t) = a.~t\nK(7, {a+1})");

        foreach (var edge in new[] { tildeDot, dotTilde })
        {
            Assert.Equal(DotResolutionMode.ExtensionOnly, edge.ResolutionMode);
            Assert.NotNull(edge.ExtensionMarkerSpan);
            Assert.Equal("t", edge.Name);
            var fallback = Assert.IsType<Expr.Param>(edge.LexicalFallback);
            Assert.Equal("t", fallback.Name);
        }
    }

    [Fact]
    public void BothSpellings_PreserveExactMarkerAndMemberSpans()
    {
        static Expr.DotCall ParseEdge(string source)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            var body = Assert.IsType<Algorithm.User>(root.Properties[0].Value);
            return Assert.IsType<Expr.DotCall>(body.Output[0]);
        }

        var beforeDot = ParseEdge("K(a, t) = a~.t\nK(7, {a+1})");
        Assert.Equal(new SourceSpan(1, 12, 1, 12), beforeDot.ExtensionMarkerSpan);
        Assert.Equal(new SourceSpan(1, 14, 1, 14), beforeDot.MemberSpan);

        var afterDot = ParseEdge("K(a, t) = a.~t\nK(7, {a+1})");
        Assert.Equal(new SourceSpan(1, 13, 1, 13), afterDot.ExtensionMarkerSpan);
        Assert.Equal(new SourceSpan(1, 14, 1, 14), afterDot.MemberSpan);
    }

    [Fact]
    public void ExtensionDot_ExplicitEmptyArgsStayDistinctAndInvokeWithReceiver()
    {
        var root = SourceProvenance.ParseValid("F(x) = x + 1\n3~.F()").Root;
        var edge = Assert.IsType<Expr.DotCall>(root.Output[^1]);
        Assert.NotNull(edge.Args);
        Assert.Empty(edge.Args);
        AssertResult("F(x) = x + 1\n3~.F()", Atom(4));
    }

    [Fact]
    public void LeadingDotContinuation_CanCarryAfterDotExtensionMarker()
    {
        var source = "K(a, t) = a\n.~t\nK(7, {a+1})";
        var root = SourceProvenance.ParseValid(source).Root;
        var body = Assert.IsType<Algorithm.User>(root.Properties[0].Value);
        var edge = Assert.IsType<Expr.DotCall>(body.Output[0]);
        Assert.Equal(DotResolutionMode.ExtensionOnly, edge.ResolutionMode);
        Assert.Equal(new SourceSpan(2, 2, 2, 2), edge.ExtensionMarkerSpan);
        AssertResult(source, Atom(8));
    }

    [Fact]
    public void BeforeDotMarker_DoesNotContinueFromANewPhysicalLine()
        => AssertParseFails(
            "K(a, t) = a\n~.t\nK(7, {a+1})",
            "Expected identifier after '~'");

    // ── B. Implicit extension: the member is a callable-name occurrence ─────

    [Fact]
    public void ImplicitExtension_TildeDot_InfersMemberParameter()
        => AssertResult(
            """
            K = a~.t
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void ImplicitExtension_DotTilde_InfersMemberParameter()
        => AssertResult(
            """
            K = a.~t
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void ImplicitExtension_ParameterOrderIsSourceOrder()
        // target `a`, member `t`, argument `b` — first-appearance order.
        => AssertResult(
            """
            K = a~.t(b)
            K(1, {x + y * 10}, 2)
            """,
            Atom(21));

    [Fact]
    public void OrdinaryDot_MemberIsNeverAnImplicitParameter()
        // K stays arity 1; V resolves structurally on the runtime receiver.
        => AssertResult(
            """
            K(x) = x.V
            Obj = {public V = 42}
            K(Obj)
            """,
            Atom(42));

    [Fact]
    public void ExtensionMember_InClosedExplicitList_IsUndeclaredIdentifierError()
        => AssertParseFails(
            """
            K(a) = a~.t
            K(7)
            """,
            "not declared in the parameter list");

    // ── C. Structural precedence vs extension bypass ────────────────────────

    private const string SplitDefs =
        """
        V(x) = 99
        Obj = {
            public V = 42
            0
        }
        """;

    [Fact]
    public void OrdinaryDot_KeepsStructuralPrecedence()
        => AssertResult(SplitDefs + "\nObj.V", Atom(42));

    [Fact]
    public void ExtensionDot_BypassesStructuralMember()
        => AssertResult(SplitDefs + "\nObj~.V", Atom(99));

    [Fact]
    public void ExtensionDot_DotTildeSpelling_BypassesStructuralMember()
        => AssertResult(SplitDefs + "\nObj.~V", Atom(99));

    // ── D. Receiver/argument laws shared with ordinary lexical fallback ─────

    [Fact]
    public void ExtensionDot_ExtraArgumentsFollowInjectedReceiver()
    {
        AssertResult(
            """
            F(x, y, z) = x*100 + y*10 + z
            3~.F(1, 2)
            """,
            Atom(312));
        AssertResult(
            """
            F(x, y, z) = x*100 + y*10 + z
            F(3, 1, 2)
            """,
            Atom(312));
    }

    [Fact]
    public void ExtensionDot_CollectingReceiverSegmentLawMatchesOrdinary()
    {
        // The extension edge reuses the ordinary receiver-segment machinery: a
        // written group receiver supplies its row items to a flat top-level
        // collecting parameter in BOTH forms.
        AssertResult(
            """
            Mean(*Vector) = Vector.sum / Vector.count
            (1, 2, 2.718).Mean
            """,
            Atom(1.906m));
        AssertResult(
            """
            Mean(*Vector) = Vector.sum / Vector.count
            (1, 2, 2.718)~.Mean
            """,
            Atom(1.906m));
    }

    [Fact]
    public void ExtensionDot_SequenceBuiltinTakesPlainCallBoundary()
    {
        AssertResult("(1, 2, 3)~.count", Atom(3));
        AssertResult("((1, 2, 3))~.take(2)", List(Atom(1), Atom(2)));
    }

    [Fact]
    public void ExtensionDot_SpreadReceiverLowersToFluentSupplyCall()
    {
        // A spread receiver has no structural members, so the extension marker
        // selects exactly the fluent lowering `Collect(operand*)` that
        // `operand*.Collect` already uses — all three spellings agree.
        AssertResult("Collect(*items) = items\n[1, 2]*.Collect", List(Atom(1), Atom(2)));
        AssertResult("Collect(*items) = items\n[1, 2]*~.Collect", List(Atom(1), Atom(2)));
        AssertResult("Collect(*items) = items\n[1, 2]*.~Collect", List(Atom(1), Atom(2)));
    }

    [Fact]
    public void ExtensionDot_StringIsAnOrdinaryCallableNameOccurrence()
    {
        // The `.string` value intrinsic is an ordinary-dot member special case;
        // an extension edge treats `string` as a plain callable-name
        // occurrence, which at root becomes an unfillable implicit parameter —
        // exactly like the plain spelling `string(5)`.
        var error = AssertBothEvaluatorsFail("5~.string");
        Assert.IsType<EvalError.UnresolvedImplicitParams>(error);
    }

    // ── E. Chaining: the mode belongs to exactly one dot edge ───────────────

    [Fact]
    public void Chain_ExtensionEdgeThenOrdinaryString()
    {
        AssertResult(
            """
            K(a, t) = a~.t.string
            K(7, {a+1})
            """,
            Str("8"));
        AssertResult(
            """
            K(a, t) = a.~t.string
            K(7, {a+1})
            """,
            Str("8"));
    }

    [Fact]
    public void Chain_TwoExtensionEdges()
        => AssertResult(
            """
            Dub(x) = x * 2
            Inc(x) = x + 1
            5~.Inc~.Dub
            """,
            Atom(12));

    [Fact]
    public void Chain_StructuralEdgeThenExtensionEdge()
        => AssertResult(
            """
            Inc(x) = x + 1
            Obj = {
                public V = 42
                0
            }
            Obj.V~.Inc
            """,
            Atom(43));

    // ── F. Marker adjacency and grace preservation ──────────────────────────

    [Fact]
    public void DetachedTilde_KeepsGraceMeaning_OrdinaryDotEdge()
        // `a ~ .t`: the tilde is not attached to the dot, so it stays postfix
        // grace on `a` and the dot edge is ORDINARY — the member still reaches
        // the parameter through its stored fallback, exactly like `a.t`.
        => AssertResult(
            """
            K(a, t) = a ~ .t
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void MarkerRun_OnlyDotAdjacentTildeIsExtensionMarker()
        // `a~~.t`: the first tilde stays grace (+1), the dot-adjacent tilde is
        // the extension marker.
        => AssertResult(
            """
            K(a, t) = a~~.t
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void DoubleMarker_IsRejected()
        => AssertParseFails("K(a, t) = a~.~t\nK(7, {a+1})", "Expected property name after '.'");

    [Fact]
    public void GraceOnCallee_Unchanged()
        => AssertResult(
            """
            K(a, t) = t~(a)
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void PrefixGraceExpression_Unchanged()
    {
        // `~t` prefix grace on an identifier expression stays grace; the
        // detector consumes the weight and the reference still resolves.
        var root = SourceProvenance.ParseValid("K = t(a~, b)\nK(1, 2, {x + y})").Root;
        var k = Assert.IsType<Algorithm.User>(root.Properties[0].Value);
        // Grace pushed `a` rightward: detected order is (t, b, a).
        Assert.Equal(["t", "b", "a"], k.Params);
    }

    // ── G. Extension edges are not open targets ─────────────────────────────

    [Fact]
    public void OpenTarget_ExtensionEdge_IsRejectedAtParse()
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
            "'extension dotCall' is not allowed in open declarations");

    // ── H. The stored fallback decides — wrapper topology is irrelevant ─────

    [Fact]
    public void WrapperDivergence_IsGone_ChainedDotAgreesWithPlainForm()
    {
        // 0.8.159 residual defect: with a same-name visible property, the
        // chained `a.t.string` evaluated its inner dot edge under a synthetic
        // algorithm-position wrapper that hid the parameter's local ownership
        // from the runtime gate, so the dotted form resolved the property
        // while plain `t(a).string` resolved the parameter. The binding now
        // rides the expression itself, so wrapper topology cannot change it.
        AssertResult(
            """
            t = 5
            K(a, t) = a.t.string
            K(7, {a+1})
            """,
            Str("8"));
        AssertResult(
            """
            t = 5
            K(a, t) = t(a).string
            K(7, {a+1})
            """,
            Str("8"));
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
            Parameters: [new ParameterDeclaration("a"), new ParameterDeclaration("t")],
            Opens: [],
            Properties: [],
            Output: [new Expr.DotCall(new Expr.Param("a"), "t")]);
        var increment = new Algorithm.User(
            Parent: null,
            Parameters: [new ParameterDeclaration("x")],
            Opens: [],
            Properties: [],
            Output: [new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1m))]);
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
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

    // ── I. Cross-context law probes (promoted from the review sweep) ───────

    [Fact]
    public void ExtensionString_LexicalDeclarationWinsOverIntrinsic()
    {
        // An extension edge treats `string` as an ordinary callable-name
        // occurrence: a user `string` callable is invoked exactly like the
        // plain form, while the ordinary dot keeps the value intrinsic.
        AssertResult("string(x) = x + 100\n5~.string", Atom(105));
        AssertResult("string(x) = x + 100\n5.~string", Atom(105));
        AssertResult("string(x) = x + 100\n5.string", Str("5"));
    }

    [Fact]
    public void ExtensionSequencePipeline_Edges_DefeatFusion_ButKeepSemantics()
    {
        // Fusion only applies to the ordinary-dot sequence-builtin view; an
        // extension edge is the plain lexical call, so it never fuses — but
        // evaluates to the same result through the generic path.
        AssertResult("K(xs) = xs~.filter({a > 1}).count\nK((1, 2, 3))", Atom(2));
        AssertResult("K(xs) = xs.filter({a > 1})~.count\nK((1, 2, 3))", Atom(2));
        AssertResult("K(xs) = xs.filter({a > 1}).count\nK((1, 2, 3))", Atom(2));
    }

    [Fact]
    public void ExtensionBuiltinMember_LocalPropertyShadowsBuiltin()
    {
        // A user `count` wins over the builtin in BOTH channels: the ordinary
        // sequence-builtin view only applies when the name genuinely resolves
        // to the builtin, and the extension channel is the plain lexical call.
        AssertResult("count(x) = 99\n(1, 2, 3)~.count", Atom(99));
        AssertResult("count(x) = 99\n(1, 2, 3).count", Atom(99));
    }

    [Fact]
    public void ExtensionMember_ResolvesThroughOpen()
        => AssertResult(
            """
            Lib = {
                public V(x) = 99
            }
            R = {
                open Lib
                5~.V
            }
            R
            """,
            Atom(99));

    [Fact]
    public void ExtensionDot_BypassesPrivateStructuralMember()
    {
        // Extension resolution never consults structural members; the
        // receiver's own VALUE (Obj's output row `0`) feeds the injection.
        AssertResult("Inc(x) = x + 1\nObj = {\n    V = 42\n    0\n}\nObj~.Inc", Atom(1));
        // With no lexical `V` anywhere, the extension member becomes an
        // implicit parameter and `K` requires it: the receiver's PRIVATE
        // structural `V` never fills it — extension bypass is total.
        var error = AssertBothEvaluatorsFail("K = a~.V\nObj = {\n    V = 42\n    0\n}\nK(Obj)");
        Assert.IsType<EvalError.ArityMismatch>(error);
        // And supplying a lexical `V` algorithm resolves it lexically, still
        // ignoring the private structural member: V(Obj-value 0) = 100.
        AssertResult("K(a, V) = a~.V\nObj = {\n    V = 42\n    0\n}\nK(Obj, {x + 100})", Atom(100));
    }

    [Fact]
    public void ExtensionDot_CaptureReceiver_SuppressesStructuralIdentity()
    {
        // A capture receiver has no structural identity for EITHER mode: the
        // ordinary edge and the extension edge both resolve the lexical `V`.
        AssertResult(
            """
            V(x) = 99
            Obj = {
                public V = 42
                0
            }
            (Obj)~.V
            """,
            Atom(99));
        AssertResult(
            """
            V(x) = 99
            Obj = {
                public V = 42
                0
            }
            (Obj).V
            """,
            Atom(99));
    }

    [Fact]
    public void ExtensionDot_CollectingCallee_ExplicitEmptyArgs()
        => AssertResult("Collect(*items) = items\n(1, 2, 3)~.Collect()", List(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void ExtensionDot_InsideMapCallback()
        => AssertResult("Inc(x) = x + 1\nmap((1, 2, 3), {a~.Inc})", List(Atom(2), Atom(3), Atom(4)));

    [Fact]
    public void ExtensionDot_InCallArgumentAndListSlots()
    {
        AssertResult("Inc(x) = x + 1\nF(a, b) = a * 10 + b\nF(5~.Inc, 2)", Atom(62));
        AssertResult("Inc(x) = x + 1\n[5~.Inc, 9]", List(Atom(6), Atom(9)));
    }

    [Fact]
    public void ExtensionDot_ReduceInitialAccumulator_CountedContext()
        => AssertResult("Id(x) = x\nreduce((1, 2, 3), {a + b}, 5~.Id)", Atom(11));

    [Fact]
    public void ExtensionDot_ListAndEmptySequenceReceivers()
    {
        AssertResult("[1, 2, 3]~.sum", Atom(6));
        AssertResult("()~.count", Atom(0));
        AssertResult("(1, 2, 3)~.first", Atom(1));
    }

    [Fact]
    public void TwoImplicitExtensionMembers_ParameterOrderIsSourceOrder()
    {
        // target `a`, first member `t`, second member `u` — first-appearance
        // order across BOTH extension edges, exactly like two written callees.
        var root = SourceProvenance.ParseValid("K = a~.t~.u\nK(1, {x + 10}, {x * 2})").Root;
        var k = Assert.IsType<Algorithm.User>(root.Properties[0].Value);
        Assert.Equal(["a", "t", "u"], k.Params);
        AssertResult("K = a~.t~.u\nK(1, {x + 10}, {x * 2})", Atom(22));
    }

    [Fact]
    public void DotTildeMarker_MemberOnNextLine_MirrorsOrdinaryTrailingDot()
    {
        // The extension marker must be attached to the dot, but the member
        // name follows the ordinary dot's member rule: the '.'-led method-chain
        // layout carries the member on its own line for both spellings.
        var extension = Parser.Parse("K(a, t) = a.~\nt\nK(7, {a+1})");
        var ordinary = Parser.Parse("Obj = {public V = 42}\nObj.\nV");
        Assert.Equal(ordinary.HasErrors, extension.HasErrors);
        if (!extension.HasErrors)
            AssertResult("K(a, t) = a.~\nt\nK(7, {a+1})", Atom(8));
    }

    [Fact]
    public void ExtensionChain_MatchesOrdinaryChain()
    {
        // Shallow equivalence probe; the near-boundary envelope pin lives in
        // AstStructuralDepthTests (extension and ordinary chains share the
        // exact per-link frame cost and depth envelope there).
        AssertResult("Inc(x) = x + 1\n1~.Inc~.Inc~.Inc", Atom(4));
        AssertResult("Inc(x) = x + 1\n1.Inc.Inc.Inc", Atom(4));
    }

    // ── J. Extension error diagnostics are mode-honest ─────────────────────

    [Fact]
    public void ExtensionUnknownMember_MessageDoesNotClaimPropertyLookup()
    {
        // An extension edge never performed structural member lookup, so its
        // diagnostic must not claim a property lookup happened. Ordinary dot
        // keeps the structural-first wording; extension drops that clause.
        // (A host-built extension edge carries an explicit Resolve fallback
        // with no front-end parameter detection, so `B` is genuinely unknown
        // at runtime — and no structural lookup ran.)
        var extensionEdge = new Expr.DotCall(new Expr.Resolve("Lib"), "B")
        {
            LexicalFallback = new Expr.Resolve("B"),
            ResolutionMode = DotResolutionMode.ExtensionOnly,
        };
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties:
            [
                new Property("Lib", new Algorithm.User(
                    Parent: null, Parameters: [], Opens: [],
                    Properties: [new Property("A", new Algorithm.User(null, [], [], [], [new Expr.Num(1m)]))],
                    Output: [])),
            ],
            Output: [extensionEdge]);
        var extension = KatLangError.FromEvalError(
            Evaluator.Run(new Expr.AlgorithmExpr(root)).Error).Message;
        Assert.DoesNotContain("was not found on", extension);
        Assert.Contains("No visible algorithm or property named 'B'", extension);

        var ordinary = KatLangError.FromEvalError(Evaluator.Run(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid("K(a) = a.Missing\nK(1)").Root)).Error).Message;
        Assert.Contains("Property 'Missing' was not found on", ordinary);
    }

    [Fact]
    public void ExtensionStringMissingOutput_RendersFullReference_NotIntrinsicForm()
    {
        // An extension edge named `string` is an ordinary callable-name
        // occurrence, not the ordinary-dot `string` value intrinsic: a
        // missing-output diagnostic renders the full `receiver.string`
        // reference, not the intrinsic's receiver-only form.
        var source = "string = {}\n5~.string";
        var error = AssertBothEvaluatorsFail(source);
        Assert.IsType<EvalError.MissingOutput>(error);
        var message = KatLangError.FromEvalError(
            Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root)).Error).Message;
        Assert.Contains("`5.string`", message);
        Assert.DoesNotContain("value `5` has no defined output", message);
    }
}
