using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;
using KatLang.Rendering;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// LAW SYSTEM U — the combined dot-semantics decision (owner decision, October 5 2026: Q-17 S-C,
/// Q-18 C-B3, Q-75 F-A). One four-clause law decides every dot edge:
/// <list type="number">
/// <item><b>Route.</b> An ordinary non-spread edge <c>R.n(args?)</c> selects a DECLARED structural
/// member <c>n</c> first, whatever its spelling — a member named <c>string</c> included — with
/// accessibility checked after selection; a member declared only in clause branches is the
/// <c>LocalOnlyProperty</c> error; only on a structural MISS does the edge take its miss route: the
/// number-to-text intrinsic for <c>string</c>, the extension call <c>n(R, args)</c> otherwise. A
/// lexical <c>string</c> is never consulted by <c>.string</c>; the fluent <c>R*.n(args)</c> stays
/// <c>n(R*, args)</c>.</item>
/// <item><b>Identity.</b> A dot expression carries ONE callable identity in every algorithm-capable
/// position — supplied, forwarded, callback, loop step and callee alike: an argumentless structural
/// path is its member's own callable (aliases normalized); every other dot expression is a computed
/// VALUE with no callable identity. Parentheses never change identity: <c>(Box.G)(2)</c> is
/// <c>Box.G(2)</c> and <c>(Box.V)()</c> the fresh call <c>Box.V()</c>.</item>
/// <item><b>Syntax.</b> A call may follow a name, a graced name, an argumentless dot edge, or a
/// redundant grouping of those — never an already computed call result: <c>X.Mk(1)()</c> is
/// <c>UnseparatedSameLineItem</c> exactly like <c>Mk(1)()</c>.</item>
/// <item><b>Static obligation.</b> Under a closed explicit parameter list or in a clause-branch
/// body, a fallback name is checked exactly when the existing selection lattice says the fallback
/// MUST be selected (<c>LexicalFallbackSelection.Always</c>): undeclared, it is
/// <c>UndeclaredIdentifier</c> at the member token, worded as the call the edge is. A MAY-selected
/// fallback stays runtime-dependent; a NEVER-selected edge has no fallback name.</item>
/// </list>
/// Runtime cases run on the six established routes (sync and async engines, the engine's suspending
/// twin, the generic and optimized evaluators, the forced twin) and require the same value, errors
/// and host-call log on all of them and identical budget counters on the three evaluator routes
/// (Q-09). Lean: <c>CoreTests/DotIdentity.lean</c>, law <c>callee_projection_is_supplied_projection</c>.
/// </summary>
public class DotSemanticsDecisionTests
{
    // ── Shared fixtures ─────────────────────────────────────────────────────────────────────────

    private const string ObjStringValue = "Obj = {\n    public string = 5\n    7\n}\n";
    private const string ObjStringCallable = "Obj = {\n    public string(x) = x * 2\n    7\n}\n";
    private const string ObjWithoutString = "Obj = {\n    public V = 1\n    7\n}\n";
    private const string Box = "Box = {\n    public G(x) = x * 10\n    public H(f) = f(3)\n    public V = tick()\n}\n";
    private const string Apply = "Apply(f, v) = f(v)\n";
    private const string PlainBox = "Box = {\n    public G(x) = x * 10\n    public H(f) = f(3)\n}\n";

    // ── 1. Q-17 S-C: the `.string` route is member-first ───────────────────────────────────────

    /// <summary>name, source, expected (<c>ok VALUE</c> or <c>err CODE</c>), expected host log.</summary>
    public static TheoryData<string, string, string, string> StringRouteMatrix() => new()
    {
        // A declared member named `string` is selected like any member.
        { "zero-parameter member", ObjStringValue + "Obj.string", "ok 5", "" },
        { "zero-parameter member, explicit empty call", ObjStringValue + "Obj.string()", "ok 5", "" },
        { "receiver without output", "Obj = {\n    public string = 5\n}\nObj.string", "ok 5", "" },
        { "private member", "Obj = {\n    string = 5\n    7\n}\nObj.string", "ok 5", "" },
        { "parameterized member called", ObjStringCallable + "Obj.string(5)", "ok 10", "" },
        { "parameterized member, two parameters", "Obj = {\n    public string(a, b) = a * 10 + b\n    7\n}\nObj.string(1, 2)", "ok 12", "" },
        { "parameterized member read bare", ObjStringCallable + "Obj.string", "err ArityMismatch", "" },
        { "argument evaluated once", ObjStringCallable + "Obj.string(trace(5))", "ok 10", "trace(5)" },
        { "nested member", "Lib = {\n    public Sub = {\n        public string = 5\n        7\n    }\n}\nLib.Sub.string", "ok 5", "" },
        { "alias member", "Inc(x) = x + 1\nObj = {\n    public string = Inc\n    7\n}\nObj.string(4)", "ok 5", "" },
        { "member with its own members", "Obj = {\n    public string = {\n        public Q = 3\n        4\n    }\n    7\n}\nObj.string.Q, Obj.string", "ok S[3, 4]", "" },
        { "parameter receiver declaring it", "Use(o) = o.string\n" + ObjStringValue + "Use(Obj)", "ok 5", "" },
        { "opened member and dotted member agree", "open Obj\n" + ObjStringValue + "string, Obj.string", "ok S[5, 5]", "" },
        { "supplied callable", Apply + ObjStringCallable + "Apply(Obj.string, 5)", "ok 10", "" },
        { "callback", ObjStringCallable + "map([1, 2], Obj.string)", "ok L[2, 4]", "" },
        { "loop step", "Obj = {\n    public string(s) = s + 2\n    7\n}\nrepeat(Obj.string, 3, 1), Obj.string.repeat(3, 1)", "ok S[7, 7]", "" },
        { "grouped callee", ObjStringCallable + "(Obj.string)(5)", "ok 10", "" },
        { "callable alias of the member", ObjStringCallable + "A = Obj.string\nA(3)", "ok 6", "" },
        { "member without output", "Obj = {\n    public string = {\n        A = 1\n    }\n    7\n}\nObj.string", "err MissingOutput", "" },

        // Selection then accessibility: an inaccessible or branch-only member is an error, never the intrinsic.
        { "local-only member", "G(x) = {\n    public Sub = {\n        public string = x + 1\n        0\n    }\n    0\n}\nG.Sub.string", "err LocalOnlyProperty", "" },
        { "local-only member at the final edge", "G(x) = {\n    public string = x + 1\n    0\n}\nG.string", "err LocalOnlyProperty", "" },
        { "branch-only member", "F(0) = {\n    string = 1\n    0\n}\nF(n) = n\nUse(o) = o.string\nUse(F)", "err LocalOnlyProperty", "" },
        { "branch-only member, root", "F(0) = {\n    string = 1\n    0\n}\nF(n) = n\nF.string", "err LocalOnlyProperty", "" },

        // A structural miss is the intrinsic; a lexical `string` is never consulted.
        { "number", "7.string", "ok '7'", "" },
        { "negative number", "(-5).string", "ok '-5'", "" },
        { "receiver without the member", ObjWithoutString + "Obj.string", "ok '7'", "" },
        { "lexical string does not pre-empt the intrinsic", "string(x) = 99\n3.string, string(3)", "ok S['3', 99]", "" },
        { "spread receiver is the lexical call", "string(x) = 99\nA = 5\nA.string, A*.string, string(A)", "ok S['5', 99, 99]", "" },
        { "parameter receiver without the member", "Use(o) = o.string\nUse(12)", "ok '12'", "" },
        { "property receiver is read through the cache", "A = tick()\nA.string, A, A.string", "ok S['1', 1, '1']", "tick#1" },
        { "Boolean receiver", "true.string", "err TypeMismatch", "" },
        { "receiver without output", "Obj = {\n    A = 1\n}\nObj.string", "err MissingOutput", "" },
    };

    [Theory]
    [MemberData(nameof(StringRouteMatrix))]
    public async Task Q17_StringRoute_IsMemberFirst(string name, string source, string expected, string hostLog)
    {
        var (observation, _) = await AllRoutesAsync(source);
        AssertOutcome(name, observation, expected);
        Assert.Equal(hostLog, string.Join(",", observation.HostCalls));
    }

    [Fact]
    public async Task Q17_MissingOutputBlame_FollowsTheRoute()
    {
        // A declared member named `string` without output is the MEMBER's missing output — named like
        // every member's — while the intrinsic over a receiver without output blames the receiver.
        var (member, _) = await AllRoutesAsync("Obj = {\n    public string = {\n        A = 1\n    }\n    7\n}\nObj.string");
        Assert.StartsWith("MissingOutput: The value `Obj.string` has no defined output.", Assert.Single(member.Errors), StringComparison.Ordinal);
        var (intrinsic, _) = await AllRoutesAsync("Obj = {\n    A = 1\n}\nObj.string");
        Assert.StartsWith("MissingOutput: Property 'Obj' has no defined output.", Assert.Single(intrinsic.Errors), StringComparison.Ordinal);
        var (ordinary, _) = await AllRoutesAsync("Obj = {\n    public V = {\n        A = 1\n    }\n    7\n}\nObj.V");
        Assert.StartsWith("MissingOutput: The value `Obj.V` has no defined output.", Assert.Single(ordinary.Errors), StringComparison.Ordinal);
    }

    [Fact]
    public void Q17_BareForwardingOfAStringMember_IsBareForwardingLikeAnyMember()
    {
        // `K(z) = Obj.string` names a parameterized member: FWD-02 bare forwarding, exactly like `K(z) = Obj.T`.
        foreach (var member in new[] { "string", "T" })
        {
            var source = $"Obj = {{\n    public {member}(x) = x * 2\n    7\n}}\nK(z) = Obj.{member}\n7";
            var diagnostic = Assert.Single(Parser.Parse(source).Diagnostics, static d => d.Severity == DiagnosticSeverity.Error);
            Assert.Equal(DiagnosticCode.UnforwardableParameter, diagnostic.Code);
        }
    }

    [Fact]
    public void Q17_StaticViews_ClassifyAStringEdgeByItsReceiver()
    {
        // The detector's stamp records the structural-miss verdict; a `.string` edge projects it to a
        // never-selected lexical fallback in every case.
        static Expr.DotCall LastEdge(string source) => Assert.IsType<Expr.DotCall>(SourceProvenance.ParseValid(source).Root.Output[^1]);

        var member = LastEdge(ObjStringValue + "Obj.string");
        Assert.Equal(LexicalFallbackSelection.Never, member.ElaboratedMissSelection);
        Assert.False(member.LexicalFallbackMayBeSelected());
        Assert.Equal(DotEdgeKind.StructuralMember, FormulaLiftingRoles.EdgeKind(member, member.EffectiveMissSelection()));

        var miss = LastEdge(ObjWithoutString + "Obj.string");
        Assert.Equal(LexicalFallbackSelection.Always, miss.ElaboratedMissSelection);
        Assert.False(miss.LexicalFallbackMayBeSelected());
        Assert.Equal(DotEdgeKind.StringIntrinsic, FormulaLiftingRoles.EdgeKind(miss, miss.EffectiveMissSelection()));

        var value = LastEdge("7.string");
        Assert.Equal(LexicalFallbackSelection.Always, value.ElaboratedMissSelection);
        Assert.Equal(DotEdgeKind.StringIntrinsic, FormulaLiftingRoles.EdgeKind(value, value.EffectiveMissSelection()));

        var runtime = Assert.IsType<Expr.DotCall>(Assert.Single(
            SourceProvenance.ParseValid("Use(o) = o.string\nUse(1)").Root.Properties[0].Value.Output));
        Assert.Equal(LexicalFallbackSelection.Conditional, runtime.ElaboratedMissSelection);
        Assert.Equal(DotEdgeKind.Undecided, FormulaLiftingRoles.EdgeKind(runtime, runtime.EffectiveMissSelection()));

        // The compositional provider navigates a declared `string` member: `Obj.string.Q`'s receiver is
        // that member's algorithm, never the intrinsic's value.
        var chained = LastEdge("Obj = {\n    public string = {\n        public Q = 3\n        4\n    }\n    7\n}\nObj.string.Q");
        Assert.Equal(LexicalFallbackSelection.Never, chained.ElaboratedMissSelection);
        // A receiver without the member makes `Obj.string` the intrinsic's VALUE: an edge chained on it
        // certainly misses (MUST) — while on a parameter receiver it stays runtime-dependent (MAY).
        Assert.Equal(LexicalFallbackSelection.Always, LastEdge(ObjWithoutString + "Obj.string.Q").ElaboratedMissSelection);
        var parameterChain = Assert.IsType<Expr.DotCall>(Assert.Single(
            SourceProvenance.ParseValid("Use(p) = p.string.Q\n7").Root.Properties[0].Value.Output));
        Assert.Equal(LexicalFallbackSelection.Conditional, parameterChain.ElaboratedMissSelection);
    }

    [Fact]
    public async Task Q17_RootFormulaLifting_NavigatesADeclaredStringMember()
    {
        // `Obj.string` on a receiver that requires arguments: a declared `string` member is navigated
        // (the receiver is not demanded, so nothing lifts), the intrinsic demands the receiver's VALUE
        // (which lifts it into the formula's signature).
        var member = Parser.Parse("Obj(p) = {\n    public string = 5\n    p\n}\nK = Obj.string + 0\nK");
        Assert.False(member.HasErrors, string.Join("\n", member.Diagnostics));
        Assert.Empty(member.Root.Properties.Single(static p => p.Name == "K").Value.Params);
        var (memberRun, _) = await AllRoutesAsync("Obj(p) = {\n    public string = 5\n    p\n}\nK = Obj.string + 0\nK");
        AssertOutcome("navigated member", memberRun, "ok 5");

        var intrinsic = Parser.Parse("Obj(p) = {\n    public V = 5\n    p\n}\nK = Obj.string\nK(3)");
        Assert.False(intrinsic.HasErrors, string.Join("\n", intrinsic.Diagnostics));
        Assert.Equal(["p"], intrinsic.Root.Properties.Single(static p => p.Name == "K").Value.Params);
        var (intrinsicRun, _) = await AllRoutesAsync("Obj(p) = {\n    public V = 5\n    p\n}\nK = Obj.string\nK(3)");
        AssertOutcome("lifted intrinsic receiver", intrinsicRun, "ok '3'");
    }

    [Fact]
    public void Q17_Editor_ResolvesADeclaredStringMemberToItsDeclaration()
    {
        var source = ObjStringValue + "Obj.string";
        var model = SemanticModelBuilder.Build(Parser.Parse(source));
        var site = new SourcePosition(5, 6);
        var resolution = model.FindResolutionAt(site);
        Assert.NotNull(resolution);
        Assert.Equal(IdentifierClassification.PropertyReference, resolution!.Classification);
        Assert.Equal(new SourceSpan(new SourcePosition(2, 12), new SourcePosition(2, 18)), resolution.ResolvedDeclaration!.Span);

        foreach (var intrinsicSource in new[] { "7.string", ObjWithoutString + "Obj.string" })
        {
            var lines = intrinsicSource.Split('\n');
            var line = lines.Length;
            var column = lines[^1].IndexOf("string", StringComparison.Ordinal) + 2;
            var intrinsic = SemanticModelBuilder.Build(Parser.Parse(intrinsicSource)).FindResolutionAt(new SourcePosition(line, column));
            Assert.NotNull(intrinsic);
            Assert.Equal(IdentifierClassification.Builtin, intrinsic!.Classification);
            Assert.Null(intrinsic.ResolvedDeclaration);
        }
    }

    // ── 2. Q-18 C-B3: one callable identity in callee position ──────────────────────────────────

    /// <summary>name, source, expected (<c>ok VALUE</c> or <c>err CODE</c>).</summary>
    public static TheoryData<string, string, string> CalleeMatrix() => new()
    {
        { "grouped structural callee", Box + "(Box.G)(2), ((Box.G))(2), Box.G(2)", "ok S[20, 20, 20]" },
        { "grouped callee with a trailing block", Box + "(Box.H){ x * 10 }, Box.H{ x * 10 }", "ok S[30, 30]" },
        { "grouped member of a library", "Lib = {\n    public F(x) = x + 1\n}\n(Lib.F)(4)", "ok 5" },
        { "grouped clause-family member", "Lib = {\n    public F(0) = 0\n    public F(n) = n * 2\n}\n(Lib.F)(4), Lib.F(4)", "ok S[8, 8]" },
        { "front end and evaluator agree on a grouped family callee", "Inc(x) = x + 1\nLib = {\n    public F(0) = 0\n    public F(n) = n * 2\n}\nK = (Lib.F)(Inc)\nK(4)", "ok 10" },
        { "grouped alias member", "Inc(x) = x * 10\nObj = {\n    public M = Inc\n    7\n}\n(Obj.M)(5)", "ok 50" },
        { "grouped builtin alias member", "Lib = {\n    public C = count\n}\n(Lib.C)([1, 2, 3])", "ok 3" },
        { "members of members", "Lib = {\n    public M(x) = {\n        public Q = 7\n        x\n    }\n}\nF(p) = p.Q\n(Lib.M)(3), Lib.M.Q, F(Lib.M)", "ok S[3, 7, 7]" },
        { "parameter receiver", Box + "Call(o) = (o.G)(2)\nCall(Box), Call(Box) + 0", "ok S[20, 20]" },
        { "canonical Math member", "(Math.Abs)(-3), (Math.Pow)(2, 5)", "ok S[3, 32]" },
        { "user module named Math is ordinary", "Math = {\n    public Abs(x) = 100\n}\n(Math.Abs)(-3)", "ok 100" },
        { "missing Math member is a computed value", "(Math.abs)(-3)", "err NotAnAlgorithm" },
        { "inaccessible member", "G(p) = {\n    public Sub = {\n        public M(x) = x * p\n        0\n    }\n    0\n}\n(G.Sub.M)(5)", "err LocalOnlyProperty" },
        { "member's own arity", Box + "(Box.G)()", "err ArityMismatch" },
        { "computed extension value", "Inc(x) = x + 1\n(5.Inc)()", "err NotAnAlgorithm" },
        { "computed extension value with an argument", "Inc(x) = x + 1\n(5.Inc)(1)", "err NotAnAlgorithm" },
        { "computed intrinsic value", "(5.string)()", "err NotAnAlgorithm" },
        { "receiver without the member", "Other(o) = 7\n" + ObjWithoutString + "(Obj.Other)()", "err NotAnAlgorithm" },

        // The projection normalizes an alias member to its target's ONE identity (FWD-02), grouped or
        // not: a repeated parameter binds the alias member and its target as one callable — and two
        // distinct callables as two (the control).
        { "supplied alias member is its target's callable identity", "Only(*xs) = xs\nObj = {\n    public M = Only\n    7\n}\nP(f, f) = 1\nP(Obj.M, Only), P((Obj.M), Only)", "ok S[1, 1]" },
        { "a distinct callable is a distinct identity", "Only(*xs) = xs\nOther(*xs) = xs\nObj = {\n    public M = Other\n    7\n}\nP(f, f) = 1\nP(Obj.M, Only)", "err TypeMismatch" },
    };

    [Theory]
    [MemberData(nameof(CalleeMatrix))]
    public async Task Q18_Callee_CarriesTheProjectedIdentity(string name, string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        AssertOutcome(name, observation, expected);
    }

    [Fact]
    public async Task Q18_ComputedDotCallee_IsAComputedValue_NamedByItsCallFrame()
    {
        var (observation, _) = await AllRoutesAsync("Inc(x) = x + 1\n(5.Inc)()");
        Assert.StartsWith(
            "NotAnAlgorithm: `5.Inc` is a computed value, not a callable: a dot expression can be called only when it names a member that its receiver declares (such as `Lib.F`); otherwise it evaluates to a value. @ [2:1, ",
            Assert.Single(observation.Errors),
            StringComparison.Ordinal);

        var error = GenericError("Inc(x) = x + 1\n(5.Inc)()");
        Assert.Equal(["while evaluating call to 5.Inc"], Frames(error));
        var innermost = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(error));
        Assert.Equal(Evaluator.ComputedDotCalleeDescription, innermost.Description);
        // Positioned at the written callee — the group's full extent.
        Assert.Equal(new SourceSpan(new SourcePosition(2, 1), new SourcePosition(2, 8)), innermost.Span);
    }

    [Fact]
    public void Q18_GroupedStructuralCallee_FramesNameTheMember()
    {
        // A failure inside the member's call reports the member's own call frame — never a synthetic
        // wrapper's.
        var error = GenericError("Box = {\n    public G(x) = x / 0\n}\n(Box.G)(2)");
        Assert.Equal(["while evaluating call to Box.G"], Frames(error));
        Assert.IsType<EvalError.DivByZero>(Innermost(error));

        var arity = GenericError(Box + "(Box.G)()");
        Assert.Equal(["while evaluating call to Box.G"], Frames(arity));
        Assert.Contains("Callable `Box.G(x)` expects 1 argument", KatLangError.FromEvalError(arity).Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task Q18_GroupedZeroParameterMemberCall_IsTheFreshCall()
    {
        // Box.V reads the per-run property cache; Box.V() and (Box.V)() are the explicit fresh call —
        // the grouped spelling never reads, and never populates, the cache entry.
        var (read, _) = await AllRoutesAsync(Box + "Box.V, Box.V(), (Box.V)(), Box.V(), Box.V");
        Assert.Equal("ok S[1, 2, 3, 4, 1]", read.Semantic);
        Assert.Equal(["tick#1", "tick#2", "tick#3", "tick#4"], read.HostCalls);

        var (populate, _) = await AllRoutesAsync(Box + "(Box.V)(), Box.V, (Box.V)(), Box.V");
        Assert.Equal("ok S[1, 2, 3, 2]", populate.Semantic);
        Assert.Equal(["tick#1", "tick#2", "tick#3"], populate.HostCalls);

        // The dotted spellings behave exactly as the opened ones (`(V)()` is `V()`).
        var (opened, _) = await AllRoutesAsync("open Box\n" + Box + "V, V(), (V)(), V(), V");
        Assert.Equal("ok S[1, 2, 3, 4, 1]", opened.Semantic);
    }

    [Fact]
    public async Task Q18_GroupedZeroParameterMemberCall_DrawsLikeTheOpenedSpelling()
    {
        const string Rand = "Box = {\n    public V = Math.RandomInt(1, 1000)\n}\n";
        var (dotted, _) = await AllRoutesAsync(Rand + "Box.V, Box.V, (Box.V)(), Box.V(), Box.V", seed: 7);
        var (opened, _) = await AllRoutesAsync("open Box\n" + Rand + "V, V, (V)(), V(), V", seed: 7);
        Assert.Equal(opened.Semantic, dotted.Semantic);
        var items = dotted.Value!.TrimStart('S', '[').TrimEnd(']').Split(", ");
        Assert.Equal(5, items.Length);
        Assert.Equal(items[0], items[1]);
        Assert.Equal(items[0], items[4]);
        Assert.NotEqual(items[0], items[2]);
        Assert.NotEqual(items[2], items[3]);
    }

    [Fact]
    public async Task Q18_SuppliedPosition_IsUnchanged()
    {
        // Model C (NEED-06) settled the supplied position; C-B3 gives the callee the SAME identity.
        var (observation, _) = await AllRoutesAsync(
            Apply
            + "Lib = {\n    public F(x) = x + 5\n    public Inc(x) = x + 1\n    public Step(s) = s + 2\n    public X = 7\n    public Sub = {\n        public Q = 1\n    }\n}\n"
            + "P(f, f) = f\nG(p) = p.Q\n"
            + "Apply(Lib.F, 5), map([1, 2], Lib.Inc), repeat(Lib.Step, 3, 0), Lib.Step.repeat(2, 0), P(Lib.X, Lib.X), G(Lib.Sub)");
        Assert.Equal("ok S[10, L[2, 3], 6, 4, 7, 1]", observation.Semantic);

        var (calls, _) = await AllRoutesAsync(Box + "Call0(f) = f()\nCall0(Box.V), Call0(Box.V), Box.V");
        Assert.Equal("ok S[1, 2, 3]", calls.Semantic);

        foreach (var computed in new[] { "Sub(a, b) = a - b\nTwice(f) = f(f(1))\nTwice(10.Sub(1))", "Inc(x) = x + 1\n" + Apply + "Apply(5.Inc, 1)", "Call0(f) = f()\nCall0(5.string)" })
        {
            var (value, _) = await AllRoutesAsync(computed);
            AssertOutcome(computed, value, "err NotAnAlgorithm");
        }
    }

    [Fact]
    public void Q18_Parser_ACallMayFollowOnlyACallableReference()
    {
        // C-B3: a call written directly after an argument-bearing dot edge is the call-result error,
        // exactly like a call after any call result; grouping erases to the same tree.
        foreach (var (source, line, column) in new[]
        {
            ("X = {\n    public Mk(k) = k + 1\n}\nX.Mk(1)()", 4, 8),
            ("X = {\n    public Mk(k) = k + 1\n}\nX.Mk(1)(5)", 4, 8),
            ("X = {\n    public G(k) = k + 1\n}\nX.G(1){ 2 }", 4, 7),
            ("X = {\n    public Mk(k) = k + 1\n}\n(X.Mk(1))()", 4, 10),
            ("Mk(k) = k + 1\na = 1\na.Mk()()", 3, 7),
            ("Mk(k) = k + 1\nMk(1)()", 2, 6),
        })
        {
            var diagnostic = Assert.Single(Parser.Parse(source).Diagnostics, static d => d.Severity == DiagnosticSeverity.Error);
            Assert.Equal(DiagnosticCode.UnseparatedSameLineItem, diagnostic.Code);
            Assert.Equal(new SourcePosition(line, column), diagnostic.Span!.Value.Start);
        }

        // An argumentless dot edge — grouped or not — is a callable reference: the call parses.
        var grouped = SourceProvenance.ParseValid(PlainBox + "(Box.G)(2)").Root.Output[^1];
        var call = Assert.IsType<Expr.Call>(grouped);
        Assert.IsType<Expr.DotCall>(call.Function);
        Assert.Null(((Expr.DotCall)call.Function).Args);
        SourceProvenance.ParseValid(PlainBox + "(Box.H){ x * 10 }");
    }

    [Fact]
    public void Q18_Optimizer_RecognizesAGroupedStructuralCallee()
    {
        // Recognition reads the ONE callee law: the direct-range source probe resolves the source call's
        // callee, and a grouped alias member of the builtin `range` IS that builtin — so the
        // filter→count pipeline fuses its direct range exactly as the written builtin does, with the
        // generic strategy's result and budget (Q-09).
        const string Definitions = "Lib = {\n    public R = range\n}\nF(x) = x > 2\n";
        foreach (var row in new[] { "count(filter((Lib.R)(1, 5), F))", "(Lib.R)(1, 5).filter(F).count", "count(filter(range(1, 5), F))" })
        {
            var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(Definitions + row).Root);
            var diagnostics = new SequencePipelineDiagnostics();
            var (optimized, optimizedBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: true, sequenceDiagnostics: diagnostics);
            var (generic, genericBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
            Assert.True(optimized.IsOk, row);
            Assert.Equal("3", SixRouteAgreement.Neutral(optimized.Value.Value));
            Assert.Equal(SixRouteAgreement.Neutral(generic.Value.Value), SixRouteAgreement.Neutral(optimized.Value.Value));
            Assert.True(diagnostics.FilterCountFusionHits == 1, row);
            Assert.True(diagnostics.DirectRangeFusionHits == 1, row);
            Assert.Equal(genericBudget.ConsumedSteps, optimizedBudget.ConsumedSteps);
            Assert.Equal(genericBudget.ConsumedExpressionCheckpoints, optimizedBudget.ConsumedExpressionCheckpoints);
            Assert.Equal(genericBudget.PeakDepth, optimizedBudget.PeakDepth);
            Assert.Equal(genericBudget.MaterializedItems, optimizedBudget.MaterializedItems);
        }
    }

    // ── 3. Q-75 F-A: closed bodies check MUST-selected fallback names ──────────────────────────

    /// <summary>name, source, expected: <c>ok VALUE</c> (accepted and run), or
    /// <c>undeclared NAME @ line:column-column</c> (the front end's one diagnostic).</summary>
    public static TheoryData<string, string, string> StaticObligationMatrix() => new()
    {
        // MUST (Always): the edge IS the call F(R, args), so its name is checked like the written callee name.
        { "MUST: value receiver", "Get(obj) = 5.size\n7", "undeclared size @ 1:14-18" },
        { "MUST: known receiver without the member", "Obj = {\n    public V = 1\n}\nGet(o) = Obj.G\n7", "undeclared G @ 4:14-15" },
        { "MUST: list receiver", "Get(xs) = [1, 2].summ\n7", "undeclared summ @ 1:18-22" },
        { "MUST: capture receiver", "A = 1, 2\nGet(o) = (A*).G\n7", "undeclared G @ 2:15-16" },
        { "MUST: string literal receiver", "Get(o) = 'a'.summ\n7", "undeclared summ @ 1:14-18" },
        { "MUST: call result receiver", "Inc(x) = x + 1\nGet(o) = Inc(o).summ\n7", "undeclared summ @ 2:17-21" },
        { "MUST: argument-bearing edge result", "F(xs) = if(xs.count > 5, xs.map{ x * 2 }.summ, 0)\nF([1, 2, 3])", "undeclared summ @ 1:42-46" },
        { "MUST: Math receiver", "Get(x) = Math.Ceiling(x)\n7", "undeclared Ceiling @ 1:15-22" },
        { "MUST: clause branch", "F(0) = 0\nF(n) = (n + 1).G\nF(0)", "undeclared G @ 2:16-17" },
        { "MUST: first occurrence is the member token", "Get(obj) = 5.size + size(5)\n7", "undeclared size @ 1:14-18" },

        // MUST with a visible or parameter-bound fallback name: accepted.
        { "MUST: declared fallback", "size(v) = 3\nGet(obj) = 5.size\nGet(0)", "ok 3" },
        { "MUST: parameter-bound fallback", "Get(size) = [1, 2].size\nGet(count)", "ok 2" },
        { "MUST: known receiver, declared fallback", "G(o) = o + 1\nObj = {\n    public V = 1\n    5\n}\nGet(z) = Obj.G\nGet(0)", "ok 6" },

        // MAY (Conditional): the runtime receiver may declare the member.
        { "MAY: parameter receiver", "Get(obj) = obj.size\n7", "ok 7" },
        { "MAY: parameter receiver declaring the member", "Get(obj) = obj.size\nObj = {\n    public size = 11\n}\nGet(Obj)", "ok 11" },
        { "MAY: parameter receiver reaching the fallback", "Get(obj) = obj.size\nsize(v) = 77\nGet(3)", "ok 77" },
        { "MAY: parameter chain", "Get(obj) = obj.Sub.size\n7", "ok 7" },
        { "MAY: through a .string edge on a parameter", "Use(p) = p.string.Q\n7", "ok 7" },
        { "MAY: clause branch binder", "F(0) = 0\nF(n) = n.G\nF(0)", "ok 0" },

        // NEVER: a structural member is selected (accessibility is checked at run time), or `.string`.
        { "NEVER: declared member", "Obj = {\n    public size = 3\n}\nGet(o) = Obj.size\nGet(0)", "ok 3" },
        { "NEVER: inaccessible declared member", "G(x) = {\n    public Sub = {\n        public size = x + 1\n        0\n    }\n    0\n}\nGet(o) = G.Sub.size\n7", "ok 7" },
        { "NEVER: branch-only member", "F(0) = {\n    size = 1\n    0\n}\nF(n) = n\nGet(o) = F.size\n7", "ok 7" },
        { "NEVER: .string intrinsic", "Get(o) = 5.string\nGet(0)", "ok '5'" },
        { "NEVER: .string member", ObjStringValue + "Get(o) = Obj.string\nGet(0)", "ok 5" },

        // Inferring bodies are unchanged: a MAY or MUST fallback name is inferred.
        { "inferring body", "Get = 5.size\nGet(count)", "ok 1" },
    };

    [Theory]
    [MemberData(nameof(StaticObligationMatrix))]
    public async Task Q75_ClosedBodies_CheckExactlyTheMustSelectedFallbackNames(string name, string source, string expected)
    {
        if (expected.StartsWith("ok ", StringComparison.Ordinal))
        {
            var (accepted, _) = await AllRoutesAsync(source);
            AssertOutcome(name, accepted, expected);
            return;
        }

        var match = System.Text.RegularExpressions.Regex.Match(expected, @"^undeclared (\w+) @ (\d+):(\d+)-(\d+)$");
        Assert.True(match.Success, expected);
        var diagnostic = Assert.Single(Parser.Parse(source).Diagnostics, static d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        var line = int.Parse(match.Groups[2].Value, System.Globalization.CultureInfo.InvariantCulture);
        Assert.Equal(
            new SourceSpan(
                new SourcePosition(line, int.Parse(match.Groups[3].Value, System.Globalization.CultureInfo.InvariantCulture)),
                new SourcePosition(line, int.Parse(match.Groups[4].Value, System.Globalization.CultureInfo.InvariantCulture))),
            diagnostic.Span);
        Assert.Contains($"'{match.Groups[1].Value}'", diagnostic.Message, StringComparison.Ordinal);

        // Every route rejects the same source with the same front-end error.
        var (observation, _) = await AllRoutesAsync(source, expectParseFailure: true);
        Assert.Equal("parse", observation.Kind);
    }

    [Fact]
    public void Q75_Diagnostic_ExplainsTheEdgeAsItsCall()
    {
        var closed = Assert.Single(Parser.Parse("Get(obj) = 5.size\n7").Diagnostics);
        Assert.Equal(
            "Property 'size' was not found on `5`, so `5.size` is the call `size(5)`; 'size' is not declared in the explicit parameter list or otherwise visible here."
            + Environment.NewLine
            + "Explicit parameter lists are closed. Declare the parameter explicitly or define a visible property/opened name.",
            closed.Message);

        var branch = Assert.Single(Parser.Parse("F(0) = 0\nF(n) = (n + 1).G\nF(0)").Diagnostics);
        Assert.Equal(
            "Property 'G' was not found on `(n + 1)`, so `(n + 1).G` is the call `G(n + 1)`; 'G' is not declared in the pattern of conditional branch 'F' or otherwise visible here."
            + Environment.NewLine
            + "If you want to use a parameter, declare it in the pattern, for example: `A(y) = y`.",
            branch.Message);

        // A known receiver that declares members offers its near member (G-24's suggestion policy).
        var math = Assert.Single(Parser.Parse("Get(x) = Math.Ceiling(x)\n7").Diagnostics);
        Assert.Equal(
            "Property 'Ceiling' was not found on `Math`, so `Math.Ceiling(...)` is the call `Ceiling(Math, ...)`; 'Ceiling' is not declared in the explicit parameter list or otherwise visible here."
            + Environment.NewLine
            + "Explicit parameter lists are closed. Declare the parameter explicitly or define a visible property/opened name."
            + Environment.NewLine
            + "Did you mean 'Math.Ceil'?",
            math.Message);

        // A name first written as an ordinary callee keeps the ordinary wording at its own position.
        var written = Assert.Single(Parser.Parse("Get(obj) = size(5) + 5.size\n7").Diagnostics);
        Assert.Equal(new SourceSpan(new SourcePosition(1, 12), new SourcePosition(1, 16)), written.Span);
        Assert.StartsWith("Identifier 'size' is used in an explicitly parameterized algorithm", written.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Q75_EachClauseFamily_ReportsItsBranchBodyReceiverAware()
    {
        // Each family reports its own branch body's MUST fallback, worded with the family's name.
        var parsed = Parser.Parse("F(0) = 0\nF(n) = (n + 1).G\nH(0) = 0\nH(n) = (n + 1).G\n7");
        var reports = parsed.Diagnostics.Where(static d => d.Code == DiagnosticCode.UndeclaredIdentifier).ToArray();
        Assert.Equal(2, reports.Length);
        Assert.Contains("conditional branch 'F'", reports[0].Message, StringComparison.Ordinal);
        Assert.Contains("conditional branch 'H'", reports[1].Message, StringComparison.Ordinal);
        Assert.All(reports, static report => Assert.StartsWith("Property 'G' was not found on `(n + 1)`", report.Message, StringComparison.Ordinal));
    }

    [Fact]
    public void Q75_Editor_MarksTheMemberToken()
    {
        var parsed = Parser.Parse("Get(obj) = 5.size\n7");
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        var model = SemanticModelBuilder.Build(parsed);
        // The member token's resolution is unchanged: no binding exists for it.
        Assert.NotEqual(IdentifierClassification.PropertyReference, model.FindResolutionAt(new SourcePosition(1, 15))?.Classification);
    }

    private const string ModuleUrl = "https://katlang.org/q75/lib.kat";

    private static ValueTask<string> Download(string url, CancellationToken cancellationToken)
        => url == ModuleUrl
            ? ValueTask.FromResult("public F(x) = x + 1\npublic V = 7")
            : throw new InvalidOperationException($"404: {url}");

    [Fact]
    public async Task Q75_EagerModuleReceiver_IsAKnownReceiver()
    {
        var options = new RunOptions { DownloadCode = Download };
        var missing = await Parser.ParseAsync($"M = load('{ModuleUrl}')\nK(z) = M.G(z)\n7", options);
        var diagnostic = Assert.Single(missing.Diagnostics, static d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Equal(new SourceSpan(new SourcePosition(2, 10), new SourcePosition(2, 11)), diagnostic.Span);

        var declared = await KatLangEngine.RunAsync($"M = load('{ModuleUrl}')\nK(z) = M.F(z)\nK(1)", options);
        Assert.Equal("2", Assert.IsType<RunResult.Success>(declared).ToDisplayString());

        // A MAY receiver stays runtime-dependent inside a module-using program as well.
        var may = await KatLangEngine.RunAsync($"M = load('{ModuleUrl}')\nK(z) = z.G\n7", options);
        Assert.IsType<RunResult.Success>(may);
    }

    [Fact]
    public async Task Q75_DeferredBranchUnit_IsCheckedWhenSelected()
    {
        // A load-bearing clause branch is ONE deferred compilation unit (MOD-10): its rules — F-A
        // included — run when the branch is selected, before its body runs; an unselected branch never fails.
        var options = new RunOptions { DownloadCode = Download };
        const string Unit = "K(0) = 0\nK(n) = {\n    M = load('" + ModuleUrl + "')\n    W(z) = M.G(z)\n    n\n}\n";
        var unselected = await KatLangEngine.RunAsync(Unit + "K(0)", options);
        Assert.Equal("0", Assert.IsType<RunResult.Success>(unselected).ToDisplayString());

        var selected = await KatLangEngine.RunAsync(Unit + "K(0), K(5)", options);
        var failure = Assert.IsType<RunResult.EvalFailure>(selected);
        Assert.Contains(failure.Errors, static error => error.Message.Contains("Property 'G' was not found on `M`", StringComparison.Ordinal));

        const string Declared = "K(0) = 0\nK(n) = {\n    M = load('" + ModuleUrl + "')\n    W(z) = M.F(z)\n    W(n)\n}\n";
        var ok = await KatLangEngine.RunAsync(Declared + "K(0), K(5)", options);
        Assert.Equal($"0{Environment.NewLine}6", Assert.IsType<RunResult.Success>(ok).ToDisplayString());
    }

    // ── 4. Metamorphic relations ───────────────────────────────────────────────────────────────

    /// <summary>Structural member shapes on a statically known receiver (MR1/MR3/MR6 grid).</summary>
    private static readonly (string Name, string Definitions, string Member)[] StructuralMembers =
    [
        ("user algorithm", "R = {\n    public M(x) = x * 3\n}\n", "R.M"),
        ("clause family", "R = {\n    public M(0) = 100\n    public M(n) = n * 3\n}\n", "R.M"),
        ("alias of a user algorithm", "T(x) = x * 3\nR = {\n    public M = T\n}\n", "R.M"),
        ("alias of a builtin", "R = {\n    public M = abs\n}\n", "R.M"),
        ("Math member", "", "Math.Abs"),
        ("nested member", "R = {\n    public Sub = {\n        public M(x) = x * 3\n    }\n}\n", "R.Sub.M"),
        ("member named string", "R = {\n    public string(x) = x * 3\n    0\n}\n", "R.string"),
        ("parameterized container", "R(k) = {\n    public M(x) = x * 3\n    k\n}\n", "R.M"),
    ];

    [Fact]
    public async Task MR1_DirectStructuralMemberCall_EqualsTheGroupedCall()
    {
        foreach (var (name, definitions, member) in StructuralMembers)
        {
            var (direct, _) = await AllRoutesAsync(definitions + $"{member}(5)");
            var (grouped, _) = await AllRoutesAsync(definitions + $"({member})(5)");
            var (twice, _) = await AllRoutesAsync(definitions + $"(({member}))(5)");
            Assert.True(direct.Semantic == grouped.Semantic, $"{name}: {direct.Semantic} vs {grouped.Semantic}");
            Assert.True(direct.Semantic == twice.Semantic, $"{name}: {direct.Semantic} vs {twice.Semantic}");
            Assert.Equal("ok", direct.Kind);
        }
    }

    [Fact]
    public async Task MR3_GroupedEmptyCall_EqualsTheExplicitEmptyCall()
    {
        foreach (var (name, definitions, member) in StructuralMembers.Append(("zero-parameter member", "R = {\n    public M = tick()\n}\n", "R.M")))
        {
            var (direct, _) = await AllRoutesAsync(definitions + $"{member}(), {member}()");
            var (grouped, _) = await AllRoutesAsync(definitions + $"({member})(), ({member})()");
            Assert.True(direct.Semantic == grouped.Semantic, $"{name}: {direct.Semantic} vs {grouped.Semantic}");
        }
    }

    [Fact]
    public async Task MR6_SuppliedProjection_EqualsTheCalleeProjection()
    {
        // One projection: the identity a dot expression carries supplied is the identity it carries
        // as a callee — structural members call the member, computed values are not callable.
        var receivers = StructuralMembers
            .Select(static member => (member.Name, member.Definitions, member.Member, Structural: true))
            .Append(("extension fallback", "M(r, x) = x * 3\nR = {\n    public V = 1\n}\n", "R.M", false))
            .Append(("intrinsic", "", "5.string", false))
            .Append(("value receiver", "M(r, x) = x * 3\n", "5.M", false));
        foreach (var (name, definitions, member, structural) in receivers)
        {
            var (supplied, _) = await AllRoutesAsync(Apply + definitions + $"Apply({member}, 5)");
            var (callee, _) = await AllRoutesAsync(Apply + definitions + $"({member})(5)");
            if (structural)
            {
                Assert.True(supplied.Semantic == callee.Semantic, $"{name}: {supplied.Semantic} vs {callee.Semantic}");
                Assert.Equal("ok", callee.Kind);
            }
            else
            {
                Assert.Equal("err", supplied.Kind);
                Assert.Equal("err", callee.Kind);
                Assert.StartsWith("NotAnAlgorithm", Assert.Single(callee.Errors), StringComparison.Ordinal);
                Assert.StartsWith("NotAnAlgorithm", Assert.Single(supplied.Errors), StringComparison.Ordinal);
            }
        }
    }

    [Fact]
    public void MR_StaticObligation_OfAMustFallback_IsTheDirectCall()
    {
        // A MUST-selected `R.F(args)` has the static name obligation of `F(R, args)` in every closed
        // context: rejected together when F is undeclared, accepted together when it is declared.
        string[] receivers = ["5", "[1, 2]", "(1 + 2)", "'a'", "Obj", "Inc(o)"];
        const string Context = "Obj = {\n    public V = 1\n}\nInc(x) = x + 1\n";
        foreach (var receiver in receivers)
        {
            foreach (var declared in new[] { false, true })
            {
                var prefix = Context + (declared ? "F(r, k) = 1\n" : "");
                var dotted = Parser.Parse(prefix + $"Get(o) = {receiver}.F(o)\n7");
                var direct = Parser.Parse(prefix + $"Get(o) = F({receiver}, o)\n7");
                Assert.Equal(direct.HasErrors, dotted.HasErrors);
                Assert.Equal(!declared, dotted.HasErrors);
                Assert.Equal(
                    direct.Diagnostics.Select(static d => d.Code),
                    dotted.Diagnostics.Select(static d => d.Code));

                var branchDotted = Parser.Parse(prefix + $"B(0) = 0\nB(o) = {receiver}.F(o)\n7");
                var branchDirect = Parser.Parse(prefix + $"B(0) = 0\nB(o) = F({receiver}, o)\n7");
                Assert.Equal(branchDirect.HasErrors, branchDotted.HasErrors);
            }
        }
    }

    // ── 5. Model C is unchanged by the callee projection ───────────────────────────────────────

    /// <summary>name, grouped spelling, direct spelling (written after <see cref="Lazy"/>).</summary>
    public static TheoryData<string, string, string> ArgumentDemandPairs() => new()
    {
        { "unused argument is never demanded", "(Lazy.K)(trace(1))", "Lazy.K(trace(1))" },
        { "a used argument is demanded once", "(Lazy.D)(trace(2))", "Lazy.D(trace(2))" },
        { "demand order follows the member's body", "(Lazy.Second)(trace(1), trace(2))", "Lazy.Second(trace(1), trace(2))" },
    };

    private const string Lazy = "Lazy = {\n    public K(x) = 7\n    public D(x) = x + x\n    public Second(a, b) = b + a\n}\n";

    [Theory]
    [MemberData(nameof(ArgumentDemandPairs))]
    public async Task ModelC_GroupedCallee_DemandsArgumentsExactlyAsTheMemberCall(string name, string grouped, string direct)
    {
        // NEED-01..03: the callee's projection decides WHICH callable runs; argument cells stay suspended
        // and are demanded by that callable's body exactly as the direct member call demands them.
        var (viaGroup, _) = await AllRoutesAsync(Lazy + grouped);
        var (viaMember, _) = await AllRoutesAsync(Lazy + direct);
        Assert.True(viaGroup.Equals(viaMember), $"{name}: {viaGroup} vs {viaMember}");
    }

    [Fact]
    public async Task ModelC_CalleeProjection_DemandsNoValue()
    {
        // The projection is identity-only navigation (NEED-06): a structural callee never evaluates its
        // container's output, and a computed dot callee is rejected without evaluating its receiver.
        var (structural, _) = await AllRoutesAsync("Lib = {\n    public F(x) = x + 1\n    trace(9)\n}\n(Lib.F)(1)");
        Assert.Equal("ok 2", structural.Semantic);
        Assert.Empty(structural.HostCalls);

        var (computed, _) = await AllRoutesAsync("Inc(x) = x + 1\n(trace(5).Inc)()");
        Assert.Equal("err [NotAnAlgorithm]", computed.Semantic);
        Assert.Empty(computed.HostCalls);
    }

    [Theory]
    [InlineData("(Box.G)(cancel(2))")]
    [InlineData("Box.G(cancel(2))")]
    [InlineData("(Lib.F)(cancel(2))")]
    public async Task ModelC_Cancellation_IsUnchangedThroughAGroupedCallee(string row)
    {
        // Cancellation observes the run's token at every chokepoint and throws with that token, never
        // an EvalError — through a grouped member callee exactly as through the member call.
        var source = PlainBox + "Lib = {\n    public F(x) = x + 1\n}\n" + row;
        foreach (var engineAsync in new[] { false, true })
        {
            using var cts = new CancellationTokenSource();
            var calls = new List<string>();
            var options = new RunOptions
            {
                HostOperations = HostOperations.Create(HostOperation.Create("cancel", (args, _) =>
                {
                    calls.Add("cancel");
                    cts.Cancel();
                    return args[0];
                }, "x")),
                EvaluationCancellationToken = cts.Token,
            };
            var thrown = engineAsync
                ? await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await KatLangEngine.RunAsync(source, options))
                : Assert.ThrowsAny<OperationCanceledException>(() => KatLangEngine.Run(source, options));
            Assert.Equal(cts.Token, thrown.CancellationToken);
            Assert.Equal(["cancel"], calls);
        }
    }

    // ── Harness ─────────────────────────────────────────────────────────────────────────────────

    private sealed record Budget(long Steps, long Checkpoints, int PeakDepth, long Items, long StringChars);

    internal sealed record Observation(string Kind, string? Value, IReadOnlyList<string> Errors, IReadOnlyList<string> HostCalls)
    {
        public bool Equals(Observation? other)
            => other is not null && Kind == other.Kind && Value == other.Value
                && Errors.SequenceEqual(other.Errors) && HostCalls.SequenceEqual(other.HostCalls);

        public override int GetHashCode() => HashCode.Combine(Kind, Value);

        /// <summary>The value, or each error's code, and the host log — the layer two different spellings are compared at.</summary>
        public string Semantic
            => Kind == "ok" ? $"ok {Value}" : $"{Kind} [{string.Join(", ", Errors.Select(static e => e[..e.IndexOf(':')]))}]";

        public override string ToString()
            => $"{Kind} {Value} errors=[{string.Join(" | ", Errors)}] host=[{string.Join(",", HostCalls)}]";
    }

    private sealed class HostLog
    {
        private int _ticks;
        public List<string> Calls { get; } = [];

        public Result Tick()
        {
            var tick = Interlocked.Increment(ref _ticks);
            lock (Calls)
                Calls.Add($"tick#{tick}");
            return new Result.Atom(tick);
        }

        public Result Trace(Result value)
        {
            lock (Calls)
                Calls.Add($"trace({SixRouteAgreement.Neutral(value)})");
            return value;
        }
    }

    private static HostOperations Operations(HostLog log, bool suspending)
        => suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return log.Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x"))
            : HostOperations.Create(
                HostOperation.Create("tick", (_, _) => log.Tick()),
                HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x"));

    private static async Task<(Observation Observation, Budget? Budget)> ObserveAsync(
        SixRouteAgreement.Route route, string source, long? seed)
    {
        var log = new HostLog();
        var operations = Operations(log, route is SixRouteAgreement.Route.EngineAsyncTwin or SixRouteAgreement.Route.ForcedTwin);
        var options = new RunOptions { HostOperations = operations, RandomSeed = seed };
        switch (route)
        {
            case SixRouteAgreement.Route.EngineSync:
                return (FromRunResult(KatLangEngine.Run(source, options), log), null);
            case SixRouteAgreement.Route.EngineAsync:
            case SixRouteAgreement.Route.EngineAsyncTwin:
                return (FromRunResult(await KatLangEngine.RunAsync(source, options), log), null);
        }

        var parsed = Parser.Parse(source, options);
        if (parsed.HasErrors)
        {
            return (new Observation(
                "parse",
                null,
                [.. parsed.Diagnostics.Where(static d => d.Severity == DiagnosticSeverity.Error).Select(static d => Describe(KatLangError.FromDiagnostic(d)))],
                [.. log.Calls]), null);
        }

        var program = new Expr.AlgorithmExpr(parsed.Root);
        var (result, budget) = route switch
        {
            SixRouteAgreement.Route.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false,
                hostOperations: operations, randomSeed: seed),
            SixRouteAgreement.Route.Optimized => Evaluator.RunCountedObserved(program, enableOptimizations: true,
                hostOperations: operations, randomSeed: seed),
            SixRouteAgreement.Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: operations, randomSeed: seed),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };
        var counters = new Budget(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
            budget.MaterializedItems, budget.MaterializedStringChars);
        return result.IsError
            ? (new Observation("err", null, [Describe(KatLangError.FromEvalError(result.Error))], [.. log.Calls]), counters)
            : (new Observation("ok", SixRouteAgreement.Neutral(result.Value.Value), [], [.. log.Calls]), counters);
    }

    /// <summary>
    /// Runs <paramref name="source"/> on every route; requires every route to agree with the synchronous
    /// engine and the three evaluator routes to report identical budget counters (Q-09).
    /// </summary>
    private static async Task<(Observation Observation, Budget Budget)> AllRoutesAsync(string source, long? seed = null, bool expectParseFailure = false)
    {
        var (oracle, _) = await ObserveAsync(SixRouteAgreement.Route.EngineSync, source, seed);
        Assert.True(expectParseFailure == (oracle.Kind == "parse"), $"unexpected front-end outcome: {oracle}\nsource:\n{source}");
        Budget? counters = null;
        foreach (var route in SixRouteAgreement.Routes.Skip(1))
        {
            var (observation, budget) = await ObserveAsync(route, source, seed);
            Assert.True(oracle.Equals(observation), $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
            if (budget is null)
                continue;
            if (counters is null)
                counters = budget;
            else
                Assert.True(counters == budget, $"{route}: budget {budget} differs from {counters}\nsource:\n{source}");
        }

        return (oracle, counters ?? new Budget(0, 0, 0, 0, 0));
    }

    private static void AssertOutcome(string name, Observation observation, string expected)
    {
        if (expected.StartsWith("ok ", StringComparison.Ordinal))
        {
            Assert.True(observation.Kind == "ok", $"{name}: {observation}");
            Assert.Equal(expected[3..], observation.Value);
            return;
        }

        Assert.True(expected.StartsWith("err ", StringComparison.Ordinal), expected);
        Assert.True(observation.Kind == "err", $"{name}: {observation}");
        Assert.StartsWith(expected[4..] + ":", Assert.Single(observation.Errors), StringComparison.Ordinal);
    }

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", SixRouteAgreement.Neutral(success.Value), [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.ParseFailure failure => new("parse", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", null, [none.Diagnostic.Code.ToString()], [.. log.Calls]),
    };

    private static string Describe(KatLangError error) => $"{error.Code}: {error.Message} @ {error.Span}";

    private static EvalError GenericError(string source)
    {
        var log = new HostLog();
        var operations = Operations(log, suspending: false);
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: false, hostOperations: operations);
        Assert.True(result.IsError, source);
        return result.Error;
    }

    private static string[] Frames(EvalError error)
    {
        var frames = new List<string>();
        while (error is EvalError.WithContext context)
        {
            frames.Add(context.ErrorContext.ToString() ?? "");
            error = context.Inner;
        }

        return [.. frames];
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }
}
