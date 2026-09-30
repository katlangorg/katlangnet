using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// THE UNIFIED FORMULA-LIFTING LAW (decided September 30 2026; constitution Q-11, Q-12 and Q-13 for
/// formulas, and X-02). A formula that USES a callable without arguments lifts it — the formula gains
/// the callable's inputs as parameters and the reference becomes the call that forwards them by
/// binding name — exactly when two independent facts hold:
/// <list type="bullet">
///   <item><b>role</b>: the reference's IMMEDIATE consumer demands its VALUE (an operand, a list or
///   capture element, an index part, a spread operand, a row, a builtin value slot, an argument of a
///   Math member, a host operation or a clause family, the <c>.string</c> receiver, a fallback dot
///   receiver of such a callee). A callee, a callback, a loop step, a whole argument of a user callable
///   or of a callee known only at run time, and a navigated receiver keep the callable. The role is
///   recursive — a nested expression takes its own consumer's role — and blind to laziness: an
///   <c>if</c> branch is a value position whether or not a run selects it;</item>
///   <item><b>signature</b>: the callable the reference RESOLVES to — whatever route reached it: the
///   owner walk, the prelude (builtins, Math members and their aliases, host operations), an
///   <c>open</c>, or a structural dot path — has a lifting signature that requires supplied
///   arguments (Q-03). A clause family's signature is one whole-value slot per position, named by the
///   plain binders of its clauses; a family whose clauses do not name every position distinctly has
///   none, and lifting it is the front-end error <see cref="DiagnosticCode.UnliftableClauseFamily"/>.</item>
/// </list>
/// Everything else is unchanged: forwarding reuses existing parameter bindings by name (Q-04),
/// closed lists and branch patterns receive nothing new (PAR-04), a lone bare row is an exact alias or
/// bare forwarding (FWD-02, whose eligibility is untouched), a bare ROOT row is its callable's own
/// zero-argument demand whatever the category, and an inferred signature must be one a programmer could
/// write (X-02, <see cref="InferredSignatureValidityTests"/>). Every outcome here is observed on six
/// execution routes with the exact host-call log.
/// </summary>
public class UnifiedFormulaLiftingTests
{
    private const string Inc = "Inc(x) = x + 1\n";

    private static async Task<string> Outcome(string source, long? seed = null)
        => RepeatedNameConstraintTests.Rendered(await RepeatedNameConstraintTests.OnEveryRouteAsync(source, seed));

    private static Algorithm.User Owner(Algorithm.User root, string name)
        => Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == name).Value);

    private static string Signature(Algorithm.User algorithm)
        => string.Join(", ", algorithm.ParameterPatterns.Select(static pattern => pattern.DisplayName));

    /// <summary>The host operations the six-route runner provides (<c>tick()</c>, <c>trace(x)</c>), for elaboration alone.</summary>
    private static readonly RunOptions HostVocabulary = new()
    {
        HostOperations = HostOperations.Create(
            HostOperation.Create("tick", static (_, _) => new Result.Atom(0)),
            HostOperation.Create("trace", static (args, _) => args[0], "x")),
    };

    private static Algorithm.User Elaborated(string source)
    {
        var parsed = Parser.Parse(source, HostVocabulary);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics) + Environment.NewLine + source);
        return parsed.Root;
    }

    private static string SignatureOf(string source, string owner = "G")
        => Signature(Owner(Elaborated(source), owner));

    // ── 1. The role of a position decides whether a reference lifts ─────────────────────

    /// <summary>(id, formula, G's inferred signature, call, outcome on every route): every VALUE position lifts.</summary>
    public static TheoryData<string, string, string, string, string> ValuePositions => new()
    {
        { "operand", Inc + "G = Inc + 1", "x", "G(4)", "ok 6" },
        { "comparison", Inc + "G = Inc > 4", "x", "G(4)", "ok true" },
        { "unary", Inc + "G = -Inc", "x", "G(4)", "ok -5" },
        { "logical", "Pos(x) = x > 0\nG = not Pos", "x", "G(3)", "ok false" },
        { "index-target", "Pair(x) = [x, x + 1]\nG = Pair:1", "x", "G(4)", "ok 5" },
        { "index-part", Inc + "G = [10, 20, 30]:Inc", "x", "G(1)", "ok 30" },
        { "spread-operand", "Two(x) = x, x\nG = count((Two*))", "x", "G(4)", "ok 2" },
        { "list-element", Inc + "G = [Inc]", "x", "G(4)", "ok L[5]" },
        { "capture-element", Inc + "G = (Inc, 0)", "x", "G(4)", "ok S[5, 0]" },
        { "nested-in-user-argument", Inc + "Id(v) = v\nG = Id(Inc + 0)", "x", "G(4)", "ok 5" },
        { "builtin-value-slot", Inc + "G = take([1, 2, 3], Inc)", "x", "G(1)", "ok L[1, 2]" },
        { "if-condition", "Pos(x) = x > 0\nG = if(Pos, 1, 2)", "x", "G(-3)", "ok 2" },
        { "if-branch", Inc + "G = if(true, Inc, 0)", "x", "G(4)", "ok 5" },
        { "math-argument", Inc + "G = abs(Inc)", "x", "G(-9)", "ok 8" },
        { "host-argument", Inc + "G = trace(Inc)", "x", "G(4)", "ok 5 [trace(5)]" },
        { "family-argument", Inc + "E(0) = 100\nE(n) = n\nG = E(Inc)", "x", "G(-1), G(4)", "ok S[100, 5]" },
        { "string-receiver", Inc + "G = Inc.string", "x", "G(4)", "ok '5'" },
        { "fallback-receiver", Inc + "G = Inc.count", "x", "G(4)", "ok 1" },
        { "fallback-argument", Inc + "G = 5.take(Inc)", "x", "G(0)", "ok L[5]" },
        { "deconstruction-source", "Two(x) = x, x + 1\nG = {\n    a, b = Two\n    a * b\n}", "x", "G(3)", "ok 12" },
    };

    [Theory]
    [MemberData(nameof(ValuePositions))]
    public async Task EveryValuePosition_LiftsTheReference(string id, string formula, string signature, string call, string outcome)
    {
        _ = id;
        var source = formula + "\n" + call;
        Assert.Equal(signature, SignatureOf(source));
        Assert.Equal(outcome, await Outcome(source));
    }

    /// <summary>(id, formula, G's signature, call, outcome): every CALLABLE position keeps the reference.</summary>
    public static TheoryData<string, string, string, string, string> CallablePositions => new()
    {
        { "callee", Inc + "G = Inc(3)", "", "G", "ok 4" },
        { "user-argument", Inc + "Apply(f) = f(1)\nG = Apply(Inc)", "", "G", "ok 2" },
        { "grouped-user-argument", Inc + "Apply(f) = f(1)\nG = Apply((Inc))", "", "G", "ok 2" },
        { "callback", Inc + "G = map([1, 2], Inc)", "", "G", "ok L[2, 3]" },
        { "loop-step", Inc + "G = repeat(Inc, 2, 0)", "", "G", "ok 2" },
        { "reducer", "Add(e, a) = e + a\nG = reduce([1, 2], Add, 0)", "", "G", "ok 3" },
        { "dynamic-callee-argument", Inc + "Apply(g) = g(1)\nG = f(Inc)", "f", "G(Apply)", "ok 2" },
        { "navigated-receiver", "Obj(x) = {\n    public V = 7\n    x\n}\nG = Obj.V + 0", "", "G", "ok 7" },
    };

    [Theory]
    [MemberData(nameof(CallablePositions))]
    public async Task EveryCallablePosition_KeepsTheReference(string id, string formula, string signature, string call, string outcome)
    {
        _ = id;
        var source = formula + "\n" + call;
        Assert.Equal(signature, SignatureOf(source));
        Assert.Equal(outcome, await Outcome(source));
    }

    // ── 2. One identity-keyed lifting signature for every category and route ───────────

    /// <summary>
    /// (id, definitions, formula, G's signature, call, outcome): the same law for every kind of
    /// callable, whatever route reaches it. Formerly only document properties and the two Math
    /// spellings lifted.
    /// </summary>
    public static TheoryData<string, string, string, string, string, string> Categories => new()
    {
        { "user-property", Inc, "G = Inc + 0", "x", "G(4)", "ok 5" },
        { "math-alias", "", "G = abs + 0", "x", "G(-4)", "ok 4" },
        { "math-qualified", "", "G = Math.Abs + 0", "x", "G(-4)", "ok 4" },
        { "math-opened", "", "G = {\n    open Math\n    Abs + 0\n}", "x", "G(-4)", "ok 4" },
        { "math-declared-names", "", "G = round + 0", "value, digits", "G(2.345, 2)", "ok 2.35" },
        { "collection-builtin", "", "G = count + 0", "collection", "G((1, 2, 3))", "ok 3" },
        { "conditional-builtin", "", "G = if + 0", "condition, whenTrue, whenFalse", "G(false, 1, 2)", "ok 2" },
        { "loop-builtin", "Step(s) = s + 1\n", "G = repeat + 0", "step, count, *init", "G(Step, 2, 0)", "ok 2" },
        { "host-operation", "", "G = trace + 0", "x", "G(4)", "ok 4 [trace(4)]" },
        { "opened-member", "Lib = {\n    public Inc(x) = x + 1\n}\n", "G = {\n    open Lib\n    Inc + 0\n}", "x", "G(4)", "ok 5" },
        { "dotted-member", "Lib = {\n    public Inc(x) = x + 1\n}\n", "G = Lib.Inc + 0", "x", "G(4)", "ok 5" },
        { "clause-family", "E(0) = 100\nE(n) = n\n", "G = E + 0", "n", "G(0), G(7)", "ok S[100, 7]" },
        { "alias-of-user", Inc + "A = Inc\n", "G = A + 0", "x", "G(4)", "ok 5" },
        { "alias-of-math", "S = abs\n", "G = S + 0", "x", "G(-4)", "ok 4" },
    };

    [Theory]
    [MemberData(nameof(Categories))]
    public async Task EveryCallableCategory_LiftsThroughTheSameLaw(
        string id, string definitions, string formula, string signature, string call, string outcome)
    {
        _ = id;
        var source = definitions + formula + "\n" + call;
        Assert.Equal(signature, SignatureOf(source));
        Assert.Equal(outcome, await Outcome(source));
    }

    [Fact]
    public void TheLiftedReference_KeepsItsResolvedCallable_ForEditorTooling()
    {
        // The forwarded call's callee is the written reference, so hover and go-to-definition
        // still land on the callable the name resolves to, whatever its category.
        var parsed = SourceProvenance.ParseValid("Lib = {\n    public Inc(x) = x + 1\n}\nG = Lib.Inc + 0\nG(4)").Parsed;
        var model = SemanticModelBuilder.Build(parsed);
        var member = model.FindResolutionAt(new SourcePosition(4, 9));
        Assert.NotNull(member);
        Assert.Equal("Inc", member.ResolvedProperty?.Name);
        Assert.Equal(new SourceSpan(2, 12, 2, 15), member.ResolvedDeclaration!.Span);
    }

    // ── 3. A clause family is named by its clauses, or not lifted at all ──────────────────

    public static TheoryData<string, string, string, string, string> NameableFamilies => new()
    {
        // A literal base case names nothing; the general clause names the slot.
        { "literal-base", "Fact(0) = 1\nFact(n) = n * Fact(n - 1)\n", "Fact", "n", "ok 120" },
        // Each position is named by the clauses that bind it.
        { "two-positions", "P(0, y) = y\nP(x, y) = x + y\n", "P", "x, y", "ok 7" },
        // A structural clause pattern names nothing; a plain binder beside it does.
        { "structural-clause", "L([x]) = x\nL(n) = n\n", "L", "n", "ok 5" },
    };

    [Theory]
    [MemberData(nameof(NameableFamilies))]
    public async Task NameableFamily_LiftsOneWholeValueSlotPerPosition(
        string id, string definitions, string family, string signature, string outcome)
    {
        var call = id switch
        {
            "literal-base" => "G(5)",
            "two-positions" => "G(2, 5)",
            _ => "G([5])",
        };
        var source = definitions + $"G = {family} + 0\n{call}";
        Assert.Equal(signature, SignatureOf(source));
        Assert.Equal(outcome, await Outcome(source));

        // The lifted call hands the family the caller's arguments whole: it is the explicit call.
        var explicitCall = definitions + $"G({signature}) = {family}({signature}) + 0\n{call}";
        Assert.Equal(await Outcome(explicitCall), await Outcome(source));
    }

    /// <summary>(id, family, the clause-derived reason): no name is ever invented.</summary>
    public static TheoryData<string, string, string> UnnameableFamilies => new()
    {
        { "no-plain-binder", "S(1) = 1\nS(-1) = -1\n", "no clause binds argument position 1 with a plain parameter" },
        { "conflicting-names", "S(a, 0) = a\nS(b, 1) = b\n", "its clauses name argument position 1 differently ('a' and 'b')" },
        { "one-name-for-two-positions", "S(a, 0) = a\nS(0, a) = a\n", "argument positions 1 and 2 would both be named 'a'" },
    };

    [Theory]
    [MemberData(nameof(UnnameableFamilies))]
    public void UnnameableFamily_InAnInferringFormula_IsTheTargetedFrontEndError(string id, string family, string reason)
    {
        _ = id;
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(family + "G = S + 0\n0"));
        Assert.Equal(DiagnosticCode.UnliftableClauseFamily, diagnostic.Code);
        Assert.Equal(new SourcePosition(3, 5), Assert.NotNull(diagnostic.Span).Start);
        Assert.Contains("'S' is used as a value here, but clause family 'S' has no formula-lifting signature", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(reason, diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(KatLangErrorCode.UnliftableClauseFamily,
            Assert.Single(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(family + "G = S + 0\n0")).Errors).Code);
    }

    [Fact]
    public void SharedFamilyDiagnostics_NameTheCurrentBinding_IndependentlyOfVisitOrder()
    {
        var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var family = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(1), body)]);
        foreach (var names in new[] { new[] { "First", "Second" }, new[] { "Second", "First" } })
        {
            var root = new Algorithm.User(null, [], [],
                [new Property("First", family), new Property("Second", family)],
                names.Select(name => (Expr)new Expr.Binary(BinaryOp.Add, new Expr.Resolve(name), new Expr.Num(0))).ToArray());
            var diagnostics = new DiagnosticBag();
            _ = ImplicitArgumentResolver.ResolvePrevalidated(root, diagnostics: diagnostics);
            var errors = diagnostics.Where(diagnostic => diagnostic.Code == DiagnosticCode.UnliftableClauseFamily).ToArray();
            Assert.Equal(names.Length, errors.Length);
            for (var index = 0; index < names.Length; index++)
                Assert.StartsWith($"'{names[index]}' is used as a value here, but clause family '{names[index]}'", errors[index].Message, StringComparison.Ordinal);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SharedFamilyDiagnostic_IsReportedOnce_WhenStrictOrLazyObservationRevisitsTheNode(bool lazy)
    {
        var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var family = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(1), body)]);
        var shared = new Expr.Binary(BinaryOp.Add, new Expr.Resolve("Family"), new Expr.Num(0));
        Expr consumer = lazy
            ? new Expr.Call(new Expr.Resolve("if"), [new Expr.BoolLiteral(false), shared, new Expr.Num(0)])
            : new Expr.Call(new Expr.Resolve("abs"), [shared]);
        foreach (var rows in new[] { new Expr[] { shared, consumer }, new Expr[] { consumer, shared } })
        {
            var root = new Algorithm.User(null, [], [], [new Property("Family", family)], rows);
            var diagnostics = new DiagnosticBag();
            _ = ImplicitArgumentResolver.ResolvePrevalidated(root, diagnostics: diagnostics);
            Assert.Single(diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.UnliftableClauseFamily);
        }
    }

    [Fact]
    public async Task UnnameableFamily_StaysExplicitlyCallable_AndClosedListsKeepTheirRuntimeCheck()
    {
        const string Sign = "S(1) = 1\nS(-1) = -1\n";
        Assert.Equal("ok -1", await Outcome(Sign + "G(v) = S(v) + 0\nG(-1)"));
        // A closed list forwards only same-named bindings and the family names nothing, so the
        // reference stays its own zero-argument demand, exactly like any blocked reference.
        Assert.StartsWith("err NoMatchingBranch", await Outcome(Sign + "P(u) = S + 0\nP(0)"), StringComparison.Ordinal);
        // A family is still never an alias target (FWD-02 eligibility is unchanged).
        Assert.StartsWith("err ArityMismatch", await Outcome("E(0) = 1\nE(n) = n\nAliasE = E\nAliasE(3)"), StringComparison.Ordinal);
    }

    // ── 4. Laziness does not change a role, and lifting does not change laziness ───────────

    [Fact]
    public async Task IfBranches_AreValuePositions_WhileEvaluationStaysLazy()
    {
        const string Formula = "Bad(x) = trace(x) / 0\nG = if(c, 1, Bad)\n";
        Assert.Equal("c, x", SignatureOf(Formula + "G(true, 5)"));
        // The unselected branch is never evaluated: no trace, no failure.
        Assert.Equal("ok 1", await Outcome(Formula + "G(true, 5)"));
        var selected = await Outcome(Formula + "G(false, 5)");
        Assert.StartsWith("err DivisionByZero", selected, StringComparison.Ordinal);
        Assert.EndsWith("[trace(5)]", selected, StringComparison.Ordinal);
    }

    // ── 5. Implicit lifting is the explicit call, and extraction is inlining ───────────────

    public static TheoryData<string> Positions => new()
    {
        "{0} + 1",
        "-{0}",
        "[{0}, {0}]",
        "({0}, 1)",
        "if(true, {0}, 0)",
        "if(false, 0, {0})",
        "count(({0}, {0}))",
        "abs({0} - 100)",
        "({0}).string",
        "Id({0} + 0)",
        "[5, 6]:({0} mod 2)",
        "trace({0})",
        "{0}.take(2)",
    };

    [Theory]
    [MemberData(nameof(Positions))]
    public async Task ImplicitLifting_IsTheExplicitCallThatForwardsTheSameBinding(string position)
    {
        const string Definitions = "F(x) = x * 10 + 1\nId(v) = v\n";
        var implicitForm = Definitions + "G = " + string.Format(position, "F") + "\n";
        var explicitForm = Definitions + "G(x) = " + string.Format(position, "F(x)") + "\n";
        Assert.Equal("x", SignatureOf(implicitForm + "G(1)"));
        foreach (var argument in new[] { "1", "7" })
            Assert.Equal(await Outcome(explicitForm + $"G({argument})"), await Outcome(implicitForm + $"G({argument})"));
    }

    [Fact]
    public async Task ExtractingAHelperFormula_AgreesWithInliningIt()
    {
        const string Definitions = "F(x) = x * 10 + 1\n";
        var extracted = Definitions + "H = F + 1\nG = H * 2\n";
        var inlined = Definitions + "G = (F + 1) * 2\n";
        Assert.Equal(SignatureOf(inlined + "G(3)"), SignatureOf(extracted + "G(3)"));
        Assert.Equal(await Outcome(inlined + "G(3)"), await Outcome(extracted + "G(3)"));

        // The same through a builtin value slot and a Math argument.
        Assert.Equal(
            await Outcome(Definitions + "G = count((abs(F), F))\nG(3)"),
            await Outcome(Definitions + "H = abs(F)\nG = count((H, F))\nG(3)"));
    }

    // ── 6. Effects, caching, and random draws are the explicit call's ──────────────────────

    [Fact]
    public async Task LiftedCalls_EvaluateLikeTheExplicitCalls_OnceEach()
    {
        const string Roll = "Roll(x) = tick() + x\n";
        Assert.Equal(
            await Outcome(Roll + "G(x) = Roll(x) + Roll(x)\nG(0)"),
            await Outcome(Roll + "G = Roll + Roll\nG(0)"));
        Assert.Equal("ok 3 [tick#1,tick#2]", await Outcome(Roll + "G = Roll + Roll\nG(0)"));

        // A callable that works with no arguments is still read from the cache, never lifted (Q-03).
        Assert.Equal("ok 2 [tick#1]", await Outcome("Once = tick()\nG = Once + Once\nG"));
    }

    [Fact]
    public async Task LiftedRandom_DrawsExactlyTheExplicitCallsStream()
    {
        Assert.Equal("start, end", SignatureOf("G = random + 0\nG(1, 1000)"));
        Assert.Equal(
            await Outcome("G(start, end) = random(start, end) + 0\nG(1, 1000), G(1, 1000)", seed: 42),
            await Outcome("G = random + 0\nG(1, 1000), G(1, 1000)", seed: 42));
    }

    // ── 7. Inferred signatures stay valid across categories (X-02) ─────────────────────────

    [Fact]
    public void DistinctCollectors_FromAnyCategory_AreTheDefinitionsFrontEndError()
    {
        var diagnostic = Assert.Single(
            SourceProvenance.ExpectFrontEndError("C1(a, *p) = a\nK = C1 + while\n0"),
            static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.InvalidCollectingBinding, diagnostic.Code);

        // One collecting NAME shared by two callees is one binding, so the loops compose.
        Assert.Equal("step, *init, count", SignatureOf("K = while + repeat\n0", "K"));
    }

    // ── 8. What the law does not touch ────────────────────────────────────────────────────

    [Theory]
    [InlineData("abs", "err ArityMismatch")]
    [InlineData("count", "err ArityMismatch")]
    [InlineData("trace", "err ArityMismatch")]
    [InlineData("Lib = {\n    public Inc(x) = x + 1\n}\nLib.Inc", "err ArityMismatch")]
    [InlineData("E(0) = 1\nE(n) = n\nE", "err NoMatchingBranch")]
    public async Task ABareRootRow_IsItsCallablesOwnZeroArgumentDemand_WhateverTheCategory(string source, string outcome)
        => Assert.StartsWith(outcome, await Outcome(source), StringComparison.Ordinal);

    [Fact]
    public async Task ClosedLists_ForwardOnlySameNamedBindings()
    {
        Assert.Equal("ok 6", await Outcome(Inc + "G(x) = Inc + 1\nG(4)"));
        Assert.StartsWith("err ArityMismatch", await Outcome(Inc + "G(y) = Inc + 1\nG(4)"), StringComparison.Ordinal);
        // A builtin forwards by its own parameter name exactly like a user callable.
        Assert.Equal("ok 3", await Outcome("G(collection) = count + 0\nG((1, 2, 3))"));
    }

    // ── 9. Processing order: every read sees the signature its turn gives ───────────────────

    /// <summary>Runs <paramref name="work"/> on a thread with a 1 MiB stack: a host stack overflow would end the test run.</summary>
    private static T OnOneMebibyteStack<T>(Func<T> work)
    {
        T result = default!;
        Exception? failure = null;
        var thread = new Thread(() =>
        {
            try
            {
                result = work();
            }
            catch (Exception exception)
            {
                failure = exception;
            }
        }, maxStackSize: 1024 * 1024);
        thread.Start();
        thread.Join();
        if (failure is not null)
            throw new InvalidOperationException("The work failed on the 1 MiB thread.", failure);
        return result;
    }

    /// <summary>
    /// Siblings declared in the reverse of their dependency order, each reading the next through a
    /// nested-body <c>open</c> or as the argument of a local clause family — reads the order channel
    /// cannot classify exactly. They are ordered by soft preferences, so no signature is read before
    /// its property's turn and no chain of on-demand processing forms; the programs elaborate and
    /// run exactly as before the unified law (where these reads were no lifting positions).
    /// </summary>
    [Fact]
    public void ReverseDeclaredChainsThroughOpensAndLocalFamilies_AreOrderedWithoutOnDemandProcessing()
    {
        // Longer than on-demand processing may stack within the structural depth budget, so without
        // the ordering these chains would be refused (AstDepthLimitExceeded).
        const int Length = 40;
        var opens = new System.Text.StringBuilder();
        var families = new System.Text.StringBuilder();
        for (var i = 1; i <= Length; i++)
        {
            opens.Append(i < Length
                ? $"P{i} = {{\n    open P{i + 1}\n    public A{i} = A{i + 1} + 1\n    0\n}}\n"
                : $"P{i} = {{\n    public A{i} = 5\n    0\n}}\n");
            families.Append(i < Length
                ? $"B{i} = {{\n    F(0) = 0\n    F(n) = n + 1\n    F(B{i + 1})\n}}\n"
                : $"B{i} = 5\n");
        }

        var openChain = opens + "R = {\n    open P1\n    A1\n}\nR";
        var familyChain = families + "B1";
        foreach (var (source, expected) in new[] { (openChain, 5 + Length - 1), (familyChain, 5 + Length - 1) })
        {
            var parsed = OnOneMebibyteStack(() => Parser.Parse(source));
            Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
            Assert.Equal(
                expected.ToString(System.Globalization.CultureInfo.InvariantCulture),
                Assert.IsType<RunResult.Success>(OnOneMebibyteStack(() => KatLangEngine.Run(source))).ToDisplayString());
        }
    }

    /// <summary>
    /// A READ THAT REACHES A SIBLING IN PROGRESS NEVER CHANGES WHAT ITS DEPENDENTS SEE (hostile review,
    /// September 30 2026). <c>Y</c> reads <c>X</c>'s member <c>Q</c> through its own <c>open X</c>, while
    /// <c>X</c>'s member <c>Z</c> reads <c>Y</c>: the two form a sibling cycle. Processing <c>X</c> in
    /// the middle of <c>Y</c> to answer that read — as the first implementation of the law did — gave
    /// <c>Z</c> the unprocessed signature of <c>Y</c> and dropped <c>Y</c>'s lifted <c>x</c> from
    /// <c>Z</c> and <c>W</c>, so <c>X.W(7)</c> became an ArityMismatch; HEAD gave 16. A cycle keeps its
    /// processing-order fallback instead — the read of <c>Q</c> sees <c>X</c> unprocessed (it needs
    /// nothing), and <c>X</c> is processed in its turn — so the program means the same in either
    /// declaration order and with or without the unrelated read.
    /// </summary>
    [Fact]
    public async Task AReadThatReachesASiblingInProgress_NeverChangesWhatItsDependentsSee()
    {
        const string Y = "Y = {\n    open X\n    A = Q + 1\n    Inc + 0\n}\n";
        const string YWithoutTheRead = "Y = {\n    A = 1\n    Inc + 0\n}\n";
        const string X = "X = {\n    public Q = 5\n    Z = Y + 0\n    public W = Z * 2\n    0\n}\n";
        foreach (var source in new[] { Inc + Y + X, Inc + X + Y, Inc + YWithoutTheRead + X })
            Assert.Equal("ok 16", await Outcome(source + "X.W(7)"));

        // The same cycle closed by a dotted member read: Z2 lifts Z1's x in every order.
        const string P1 = "P1 = {\n    open P2\n    public A1 = A2 + 1\n    public Z1 = Inc + 0\n    0\n}\n";
        const string P1WithoutTheRead = "P1 = {\n    public Z1 = Inc + 0\n    0\n}\n";
        const string P2 = "P2 = {\n    public A2 = 5\n    public Z2 = P1.Z1 + 0\n    0\n}\n";
        foreach (var source in new[] { Inc + P1 + P2, Inc + P2 + P1, Inc + P1WithoutTheRead + P2 })
            Assert.Equal("ok 8", await Outcome(source + "R = P2.Z2 + 0\nR(7)"));

        // A provider that needs a parameter is no open target (IllegalInOpen, as in HEAD) — the stale
        // read had hidden the parameter P2 lifts from P1.
        const string P1Lifting = "P1 = {\n    open P2\n    public A1 = A2 + 1\n    Inc + 0\n}\n";
        const string P2Reading = "P2 = {\n    public A2 = 5\n    Z2 = P1 + 0\n    Z2\n}\n";
        foreach (var source in new[] { Inc + P1Lifting + P2Reading, Inc + P2Reading + P1Lifting })
            Assert.Contains(Parser.Parse(source + "R = P2 + 0\nR(7)").Diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.IllegalInOpen);
    }

    /// <summary>
    /// A chain whose soft preferences its hard edges override — each <c>P(i)</c> opens <c>P(i+1)</c>
    /// while <c>P(i+1)</c> reads <c>P(i)</c>'s member — and a ring of siblings opening each other are
    /// sibling cycles too: no property of one is processed ahead of its turn, so neither stacks one
    /// processing inside the next (at any length, on a 1 MiB stack), and each elaborates like the
    /// program without the unified law's new reads.
    /// </summary>
    [Fact]
    public void LongSiblingCycles_ProcessNoPropertyAheadOfItsTurn()
    {
        static string Chain(int length)
        {
            var source = new System.Text.StringBuilder();
            for (var i = 1; i <= length; i++)
            {
                source.Append($"P{i} = {{\n");
                if (i < length)
                    source.Append($"    open P{i + 1}\n");
                source.Append(i < length ? $"    public A{i} = A{i + 1} + 1\n" : $"    public A{i} = 5\n");
                source.Append(i > 1 ? $"    public Z{i} = P{i - 1}.Z{i - 1} + 0\n" : "    public Z1 = 0\n");
                source.Append("    0\n}\n");
            }

            return source + "R = {\n    open P1\n    A1\n}\nR";
        }

        static string Ring(int length)
        {
            var source = new System.Text.StringBuilder();
            for (var i = 1; i <= length; i++)
            {
                source.Append($"P{i} = {{\n    open P{(i < length ? i + 1 : 1)}\n");
                source.Append(i < length ? $"    public A{i} = A{i + 1} + 1\n" : $"    public A{i} = 5\n");
                source.Append("    0\n}\n");
            }

            return source + "R = {\n    open P1\n    A1\n}\nR";
        }

        foreach (var length in new[] { 4, 40, 300 })
        {
            foreach (var source in new[] { Chain(length), Ring(length) })
            {
                var parsed = OnOneMebibyteStack(() => Parser.Parse(source));
                Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));

                // Evaluating a 300-deep chain of reads is the evaluator's own depth question.
                if (length <= 40)
                {
                    Assert.Equal(
                        (5 + length - 1).ToString(System.Globalization.CultureInfo.InvariantCulture),
                        Assert.IsType<RunResult.Success>(OnOneMebibyteStack(() => KatLangEngine.Run(source))).ToDisplayString());
                }
            }
        }
    }

    [Fact]
    public async Task LoneBareRows_KeepTheirAliasAndForwardingEligibility()
    {
        // FWD-02's targets are unchanged: a non-Math builtin, a host operation and a dotted member
        // are no alias targets, so these stay zero-parameter properties.
        Assert.StartsWith("err ArityMismatch", await Outcome("C = count\nC((1, 2))"), StringComparison.Ordinal);
        Assert.StartsWith("err ArityMismatch", await Outcome("T = trace\nT(1)"), StringComparison.Ordinal);
        Assert.StartsWith("err ArityMismatch", await Outcome("Lib = {\n    public Inc(x) = x + 1\n}\nB = Lib.Inc\nB(1)"), StringComparison.Ordinal);
        // ... while a formula over the same callables lifts them.
        Assert.Equal("ok 2", await Outcome("C = count + 0\nC((1, 2))"));
        Assert.Equal("ok 2", await Outcome("Lib = {\n    public Inc(x) = x + 1\n}\nB = Lib.Inc + 0\nB(1)"));
    }
}
