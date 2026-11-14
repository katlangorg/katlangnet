using KatLang.Evaluation.Caching;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// DECLARATION-LEVEL OUTPUT SPREADING, the static form (November 2026). A declaration written with a postfix
/// <c>*</c> after its name or parameter list (<c>A* = x, y</c>, <c>A(x, y)* = x, y</c>) changes no algorithm;
/// the front end spreads every eligible call that statically resolves to it, exactly where a written <c>*</c>
/// would stand. The oracle: a marked program elaborates to the SAME tree as its explicit counterpart — the
/// markers removed and <c>*</c> written after each eligible call — compared through the Lean encoding (which
/// ignores spans and the marker metadata); where the counterpart needs different source (lifted and forwarded
/// calls), value, rows, errors, <c>tick()</c> effects and step counts agree on the generic, optimized and async
/// routes instead. Behavioral cases run on every route (<see cref="SixRouteAgreement"/>).
/// </summary>
public class DeclarationOutputSpreadingTests
{
    private const string Shared = "A(x, y)* = x, y\nAdd(x, y) = x + y\nFib(a, b)* = b, a + b\n";

    /// <summary>The program with the shared declarations, placed after a leading <c>open</c> (the body's preamble).</summary>
    private static string WithShared(string program)
        => program.StartsWith("open ", StringComparison.Ordinal)
            ? program[..(program.IndexOf('\n') + 1)] + Shared + program[(program.IndexOf('\n') + 1)..]
            : Shared + program;

    private static string Summarize(SixRouteAgreement.Observation outcome)
        => outcome.Kind == "ok"
            ? $"ok {outcome.Value}"
            : $"{outcome.Kind} {string.Join(" | ", outcome.Errors.Select(static error => error[..error.IndexOf(':')]))}";

    private static async Task<string> SummaryOnEveryRoute(string source)
        => Summarize(await SixRouteAgreement.OnEveryRouteAsync(source));

    // ── The specified results (the task's table, every row) ──

    public static TheoryData<string, string> SpecifiedRows => new()
    {
        { "A(1, 2)\nA(3, 4)", "ok S[1, 2, 3, 4]" },
        { "B = A\nB(3, 4)", "ok S[3, 4]" },
        { "Add(A(1, 2))", "ok 3" },
        { "[A(1, 2), A(3, 4)]", "ok L[1, 2, 3, 4]" },
        { "(A(1, 2), 5)", "ok S[1, 2, 5]" },
        { "count([A(1, 2)])", "ok 2" },
        { "count(A(1, 2))", "err ArityMismatch" },
        { "if(true, A(1, 2), 0)", "err ArityMismatch" },
        { "A(1, 2)[0]", "ok 1" },
        { "first(A(1, 2))", "err ArityMismatch" },
        { "A(1, 2).first", "err ArityMismatch" },
        { "count((A(1, 2)))", "err ArityMismatch" },
        { "count({ A(1, 2) })", "ok 2" },
        { "Apply(f) = Add(f(1, 2))\nApply(A)", "err ArityMismatch" },
        { "W(x, y) = A(x, y)\nAdd(W(1, 2))", "err ArityMismatch" },
        { "V = A(1, 2)\nAdd(V)", "err ArityMismatch" },
        { "V = A(1, 2)\nAdd(V*)", "ok 3" },
        { "S = [A]\nS(1, 2)", "ok L[1, 2]" },
        { "C = count(A)\nC(1, 2)", "err ArityMismatch" },
        { "Fib(0, 1)\nFib(0, 1).repeat(10)", "err ArityMismatch" },
        { "F(a, b) = Fib(a, b)\nF(0, 1).repeat(10)", "ok S[55, 89]" },
        { "Step(a, b) = Fib(a, b)\nStep(0, 1).repeat(3)", "ok S[2, 3]" },
        { "{ Fib(0, 1) }.repeat(10)", "err NotAnAlgorithm" },
        { "Pair(x, y)* = [x, y]\nCall12(f) = f(1, 2)\nCall12(Pair)", "ok L[1, 2]" },
        { "open Lib\nLib = {\npublic Pair(x, y)* = x, y\n}\ncount(Pair(1, 2))", "err ArityMismatch" },
        { "D(x, y)* = x / y, y\nFirstOf(a, *rest) = a\nFirstOf(5, D(1, 0))", "err DivisionByZero" },
        { "G* = [[1, 2], [3]]\n[G()]\n(G(), 9)", "ok S[L[L[1, 2], L[3]], S[L[1, 2], L[3], 9]]" },
        { "Z(x)* = ()\n[Z(1), 7]", "ok L[7]" },
        { "R(a, b)* = range(a, b)\nR(1, 3)", "ok S[1, 2, 3]" },
    };

    [Theory]
    [MemberData(nameof(SpecifiedRows))]
    public async Task SpecifiedRow_HasItsResult_OnEveryRoute(string program, string expected)
        => Assert.Equal(expected, await SummaryOnEveryRoute(WithShared(program)));

    /// <summary>The same rows without any marker keep today's results: only the marker changes them.</summary>
    public static TheoryData<string, string> UnmarkedControls => new()
    {
        { "A(x, y) = x, y\nS = [A]\nS(1, 2)", "ok L[S[1, 2]]" },
        { "A(x, y) = x, y\nC = count(A)\nC(1, 2)", "ok 2" },
        { "Fib(a, b) = b, a + b\nStep(a, b) = Fib(a, b)\nStep(0, 1).repeat(3)", "err ArityMismatch" },
        { "open Lib\nLib = {\npublic Pair(x, y) = x, y\n}\ncount(Pair(1, 2))", "ok 2" },
        { "D(x, y) = x / y, y\nFirstOf(a, *rest) = a\nFirstOf(5, D(1, 0))", "ok 5" },
        { "A(x, y) = x, y\ncount(A(1, 2))", "ok 2" },
    };

    [Theory]
    [MemberData(nameof(UnmarkedControls))]
    public async Task UnmarkedControl_KeepsTodaysResult(string program, string expected)
        => Assert.Equal(expected, await SummaryOnEveryRoute(program));

    // ── The oracle: the explicit counterpart elaborates to the same tree ──

    public static TheoryData<string, string> ExplicitCounterparts => new()
    {
        // Whole output rows, an alias's call, argument slots of a user callee and a builtin, `if` included.
        { "A(x, y)* = x, y\nA(1, 2)\nA(3, 4)", "A(x, y) = x, y\nA(1, 2)*\nA(3, 4)*" },
        { "A(x, y)* = x, y\nB = A\nB(3, 4)", "A(x, y) = x, y\nB = A\nB(3, 4)*" },
        { "A(x, y)* = x, y\nB = A\nC = B\n[C(1, 2)]", "A(x, y) = x, y\nB = A\nC = B\n[C(1, 2)*]" },
        { "A(x, y)* = x, y\nAdd(x, y) = x + y\nAdd(A(1, 2))", "A(x, y) = x, y\nAdd(x, y) = x + y\nAdd(A(1, 2)*)" },
        { "A(x, y)* = x, y\ncount(A(1, 2))", "A(x, y) = x, y\ncount(A(1, 2)*)" },
        { "A(x, y)* = x, y\nif(true, A(1, 2), 0)", "A(x, y) = x, y\nif(true, A(1, 2)*, 0)" },
        // List and group elements, a block row, a selector slot, a deconstruction right-hand side.
        { "A(x, y)* = x, y\n[A(1, 2), A(3, 4)]", "A(x, y) = x, y\n[A(1, 2)*, A(3, 4)*]" },
        { "A(x, y)* = x, y\n(A(1, 2), 5)", "A(x, y) = x, y\n(A(1, 2)*, 5)" },
        { "A(x, y)* = x, y\ncount({ A(1, 2) })", "A(x, y) = x, y\ncount({ A(1, 2)* })" },
        { "A(x, y)* = x, y\nL = [10, 20, 30]\nL[A(0, 1)]", "A(x, y) = x, y\nL = [10, 20, 30]\nL[A(0, 1)*]" },
        { "A(x, y)* = x, y\na, b = A(1, 2)\na + b", "A(x, y) = x, y\na, b = A(1, 2)*\na + b" },
        // The operand of a written `*` (chained spread), and positions that stay one value.
        { "A(x, y)* = x, y\n[A(1, 2)*]", "A(x, y) = x, y\n[A(1, 2)**]" },
        { "A(x, y)* = x, y\nA(1, 2)[0]", "A(x, y) = x, y\nA(1, 2)[0]" },
        { "A(x, y)* = x, y\nA(1, 2) == A(1, 2)", "A(x, y) = x, y\nA(1, 2) == A(1, 2)" },
        { "A(x, y)* = x, y\nA(1, 2).string", "A(x, y) = x, y\nA(1, 2).string" },
        // The receiver of an extension-call edge is lowered as the parser lowers a written `R*.F(args)`.
        { "A(x, y)* = x, y\nA(1, 2).first", "A(x, y) = x, y\nA(1, 2)*.first" },
        { "A(x, y)* = x, y\nF(a, b, c) = a + b + c\nA(1, 2).F(3)", "A(x, y) = x, y\nF(a, b, c) = a + b + c\nA(1, 2)*.F(3)" },
        { "A(x, y)* = x, y\nAdd(x, y) = x + y\n5.Add(A(1, 2))", "A(x, y) = x, y\nAdd(x, y) = x + y\n5.Add(A(1, 2)*)" },
        // An extension call to a marked declaration is itself a call to it.
        { "Dup(x)* = x, x\n[3.Dup]", "Dup(x) = x, x\n[3.Dup*]" },
        // Member paths, opened members, families, zero-parameter declarations, carriers.
        { "Box = {\npublic P(x, y)* = x, y\n}\n[Box.P(1, 2), (Box.P)(3, 4)]", "Box = {\npublic P(x, y) = x, y\n}\n[Box.P(1, 2)*, (Box.P)(3, 4)*]" },
        { "open Lib\nLib = {\npublic P(x, y)* = x, y\n}\n[P(1, 2)]", "open Lib\nLib = {\npublic P(x, y) = x, y\n}\n[P(1, 2)*]" },
        { "F(0)* = 0, 0\nF(n)* = n, n * 10\n[F(0), F(2)]", "F(0) = 0, 0\nF(n) = n, n * 10\n[F(0)*, F(2)*]" },
        { "P* = 1, 2\n[P, P()]", "P = 1, 2\n[P, P()*]" },
        { "A(x, y)* = x, y\nB* = { A }\n[B(1, 2)]", "A(x, y) = x, y\nB = { A }\n[B(1, 2)*]" },
        { "A(x, y)* = x, y\nB = { A }\n[B(1, 2)]", "A(x, y) = x, y\nB = { A }\n[B(1, 2)]" },
        // Routes the front end cannot see never spread.
        { "A(x, y)* = x, y\nApply(f) = [f(1, 2)]\nApply(A)", "A(x, y) = x, y\nApply(f) = [f(1, 2)]\nApply(A)" },
        { "A(x, y)* = x, y\nUse(f) = {\nG = f\n[G(1, 2)]\n}\nUse(A)", "A(x, y) = x, y\nUse(f) = {\nG = f\n[G(1, 2)]\n}\nUse(A)" },
        // A marked call written inside an unmarked wrapper spreads where it stands; calls to the wrapper do not.
        { "A(x, y)* = x, y\nW(x, y) = A(x, y)\n[W(1, 2)]", "A(x, y) = x, y\nW(x, y) = A(x, y)*\n[W(1, 2)]" },
        // Nested and public declarations.
        { "Outer = {\npublic In(x)* = x, x\n[In(1)]\n}\nOuter", "Outer = {\npublic In(x) = x, x\n[In(1)*]\n}\nOuter" },
        // A spread slot makes the positions after it unknown to the argument roles, inserted or written alike: `Inc` in
        // `reduce`'s initial slot stays a callable after a spread collection (Codex review round 1), under a closed list, in
        // an inferring body (whose signature selection reads the same roles) and through a lowered receiver.
        {
            "P* = [[1]]\nAdd(a, b) = a + b\nInc(x) = x + 1\nH(x) = reduce(P(), Add, Inc)\nH(5)",
            "P = [[1]]\nAdd(a, b) = a + b\nInc(x) = x + 1\nH(x) = reduce(P()*, Add, Inc)\nH(5)"
        },
        {
            "P* = [[1]]\nAdd(a, b) = a + b\nInc(x) = x + 1\nH = reduce(P(), Add, Inc)\n[H]",
            "P = [[1]]\nAdd(a, b) = a + b\nInc(x) = x + 1\nH = reduce(P()*, Add, Inc)\n[H]"
        },
        {
            "P* = [[1]]\nAdd(a, b) = a + b\nInc(x) = x + 1\nH = P().reduce(Add, Inc)\n[H]",
            "P = [[1]]\nAdd(a, b) = a + b\nInc(x) = x + 1\nH = P()*.reduce(Add, Inc)\n[H]"
        },
    };

    [Theory]
    [MemberData(nameof(ExplicitCounterparts))]
    public async Task MarkedProgram_IsItsExplicitCounterpart(string marked, string explicitSpreads)
    {
        var markedRoot = SourceProvenance.ParseValid(marked).Root;
        var explicitRoot = SourceProvenance.ParseValid(explicitSpreads).Root;
        Assert.Equal(LeanAstEncoder.EncodeProgram(explicitRoot), LeanAstEncoder.EncodeProgram(markedRoot));

        // The same tree runs the same way on every route; only an error's wording may gain the marker's note.
        var markedOutcome = await SixRouteAgreement.OnEveryRouteAsync(marked);
        var explicitOutcome = await SixRouteAgreement.OnEveryRouteAsync(explicitSpreads);
        Assert.Equal(explicitOutcome.Kind, markedOutcome.Kind);
        Assert.Equal(explicitOutcome.Value, markedOutcome.Value);
        Assert.Equal(explicitOutcome.Errors.Select(WithoutNotes), markedOutcome.Errors.Select(WithoutNotes));
    }

    /// <summary>
    /// A rendered error (<c>Code: message @ span</c>) without the marker's note and without the span's END, which
    /// the written star of the explicit counterpart moves one column: the code, the message and the start remain.
    /// </summary>
    private static string WithoutNotes(string rendered)
    {
        var at = rendered.LastIndexOf(" @ ", StringComparison.Ordinal);
        var message = rendered[..at];
        var note = message.IndexOf("\nNote: `", StringComparison.Ordinal);
        if (note >= 0)
            message = message[..note];
        var span = rendered[(at + 3)..];
        var comma = span.IndexOf(',');
        return message + " @ " + (comma < 0 ? span : span[..comma]);
    }

    // ── Lifted and forwarded calls: the counterpart needs different source ──

    public static TheoryData<string, string> SynthesizedCounterparts => new()
    {
        // Formula lifting: a lifted call spreads like a written one.
        { "A(x, y)* = x, y\nS = [A]\nS(1, 2), S(3, 4)", "A(x, y) = x, y\nS(x, y) = [A(x, y)*]\nS(1, 2), S(3, 4)" },
        { "A(x, y)* = x, y\nC = count(A)\nC(1, 2)", "A(x, y) = x, y\nC(x, y) = count(A(x, y)*)\nC(1, 2)" },
        { "T(x)* = x, tick()\nU = [T, T]\nU(5), U(6)", "T(x) = x, tick()\nU(x) = [T(x)*, T(x)*]\nU(5), U(6)" },
        // Bare forwarding: the forwarded call is the body's row.
        { "A(x, y)* = x, y\nG(x, y) = A\nG(1, 2), [G(3, 4)]", "A(x, y) = x, y\nG(x, y) = A(x, y)*\nG(1, 2), [G(3, 4)]" },
        // An operand position stays one value whether the call is written or lifted.
        { "A(x, y)* = x, y\nH = [A][0]\nH(1, 2)", "A(x, y) = x, y\nH(x, y) = [A(x, y)*][0]\nH(1, 2)" },
    };

    [Theory]
    [MemberData(nameof(SynthesizedCounterparts))]
    public async Task SynthesizedCall_SpreadsLikeItsWrittenCounterpart(string marked, string explicitSpreads)
    {
        Assert.Equal(await SummaryOnEveryRoute(explicitSpreads), await SummaryOnEveryRoute(marked));
        foreach (var route in new[] { 0, 1, 2 })
        {
            var markedRun = await ObserveRoute(marked, route);
            var explicitRun = await ObserveRoute(explicitSpreads, route);
            Assert.Equal(explicitRun, markedRun);
        }
    }

    /// <summary>Value or error code, <c>tick()</c> count and consumed steps on the generic (0), optimized (1) or async (2) evaluator.</summary>
    private static async Task<string> ObserveRoute(string source, int route)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var (result, budget) = route switch
        {
            0 => Evaluator.RunCountedObserved(program, enableOptimizations: false),
            1 => Evaluator.RunCountedObserved(program, enableOptimizations: true),
            _ => await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache()),
        };
        var outcome = result.IsError ? $"err {result.Error.Code}" : $"ok {SixRouteAgreement.Neutral(result.Value.Value)}";
        return $"{outcome} ticks={budget.TickCount} steps={budget.ConsumedSteps}";
    }

    // ── The oracle for calls formula lifting creates (owner decision D2) ──
    // The counterpart of a lifted call writes `*` after the bare reference: `reduce(P*, Add, Inc)`.

    private const string Reducers = "Add(a, b) = a + b\nInc(x) = x + 1\nPos(x) = x > 0\n";

    private static string Encoding(string source) => LeanAstEncoder.EncodeProgram(SourceProvenance.ParseValid(source).Root);

    /// <summary>A rendered error without the marker's note and without its span (a counterpart's source shifts columns).</summary>
    private static string CodeAndMessage(string rendered)
    {
        var message = rendered[..rendered.LastIndexOf(" @ ", StringComparison.Ordinal)];
        var note = message.IndexOf("\nNote: `", StringComparison.Ordinal);
        return note < 0 ? message : message[..note];
    }

    /// <summary>The two programs elaborate to one tree (Lean encodings) and run alike on every route.</summary>
    private static async Task AssertOneProgram(string expected, string actual)
    {
        Assert.Equal(Encoding(expected), Encoding(actual));
        var expectedOutcome = await SixRouteAgreement.OnEveryRouteAsync(expected);
        var actualOutcome = await SixRouteAgreement.OnEveryRouteAsync(actual);
        Assert.Equal(expectedOutcome.Kind, actualOutcome.Kind);
        Assert.Equal(expectedOutcome.Value, actualOutcome.Value);
        Assert.Equal(expectedOutcome.Errors.Select(CodeAndMessage), actualOutcome.Errors.Select(CodeAndMessage));
    }

    /// <summary>
    /// The marked declaration, the formula with a BARE reference to it, and the outcome all three spellings share: the
    /// marked lifted form, the marked explicit call, and the unmarked explicit <c>*</c>. Every builtin whose slot roles
    /// depend on the position (a value slot of a builtin that also has a callable slot: <c>reduce</c>'s initial value, a
    /// surplus slot of <c>map</c> and <c>filter</c>, and loop control/surplus slots), <c>if</c> as the control, and the receiver spelling.
    /// </summary>
    public static TheoryData<string, string, string, string> LiftedCallFamily => new()
    {
        // `reduce`: after the spread collection, `Inc` in the initial slot is no value any more, so it is not lifted.
        { "P(x)* = [x]", "H = reduce(P, Add, Inc)\nH(1)", "P", "err ArityMismatch" },
        { "P(x)* = [x]", "H = P.reduce(Add, Inc)\nH(1)", "P", "err ArityMismatch" },
        // A literal initial value has no role to change: the reduction runs over the spread items.
        { "P(x)* = [x]", "H = reduce(P, Add, 10)\nH(1)", "P", "ok 11" },
        // A surplus slot after a callback is a value at a known position only.
        { "P(x)* = [x]", "H = map(P, Inc, Inc)\nH(1)", "P", "err ArityMismatch" },
        { "P(x)* = [x]", "H = filter(P, Pos, Inc)\nH(1)", "P", "err ArityMismatch" },
        // META steps stay callable; a spreading control/surplus slot still ends the known positions after it.
        { "P(x)* = [x]", "H = repeat(Inc(0), P, Inc)\nH(1)", "P", "err ArityMismatch" },
        { "P(x)* = [x]", "H = while(Inc(0), P, Inc)\nH(1)", "P", "err ArityMismatch" },
        // The control: every slot of `if` is a value at every position, so `Inc` is lifted either way.
        { "P(x)* = [x]", "H = if(P, Inc, Inc)\nH(1)", "P", "err TypeMismatch" },
        // The declaration's own INFERRED names require the argument too.
        { "P* = [x]", "H = reduce(P, Add, Inc)\nH(1)", "P", "err ArityMismatch" },
        // A transparent alias of a marked declaration, and a chain of them.
        { "P(x)* = [x]\nQ = P", "H = reduce(Q, Add, Inc)\nH(1)", "Q", "err ArityMismatch" },
        { "P(x)* = [x]\nQ = P\nR = Q", "H = R.reduce(Add, Inc)\nH(1)", "R", "err ArityMismatch" },
        // A member path: the dotted reference lifts like a name.
        { "Lib = {\npublic P(x)* = [x]\n}", "H = reduce(Lib.P, Add, Inc)\nH(1)", "Lib.P", "err ArityMismatch" },
        // Positions that stay one value, and rows, lists and selectors, lifted or written.
        { "P(x)* = [x]", "H = [P, P]\nH(1)", "P", "ok L[1, 1]" },
        { "P(x)* = [x]", "H = count(P)\nH(1)", "P", "ok 1" },
        { "P(x)* = x, x", "H = count(P)\nH(1)", "P", "err ArityMismatch" },
    };

    [Theory]
    [MemberData(nameof(LiftedCallFamily))]
    public async Task LiftedMarkedCall_IsItsExplicitCall_AndTheUnmarkedExplicitSpread(string declaration, string formula, string reference, string expected)
    {
        // Every bare occurrence of the reference in the formula's own row (never the trailing call of `H`).
        var row = formula[..formula.IndexOf('\n')];
        var bare = new System.Text.RegularExpressions.Regex(@"(?<![\w.])" + System.Text.RegularExpressions.Regex.Escape(reference) + @"(?![\w(])");
        string Rewritten(string replacement) => bare.Replace(row, replacement) + formula[row.Length..];

        var markedLifted = declaration + "\n" + Reducers + formula;
        var markedExplicitCall = declaration + "\n" + Reducers + Rewritten(reference + "(x)");
        var unmarkedExplicitSpread = declaration.Replace(")* =", ") =").Replace("P* =", "P =") + "\n" + Reducers + Rewritten(reference + "*");

        Assert.Equal(expected, await SummaryOnEveryRoute(markedLifted));
        // Lifting equals the explicit call for a marked callee (the formula-lifting law) ...
        await AssertOneProgram(markedExplicitCall, markedLifted);
        // ... and the marked program is its explicit-`*` counterpart (the oracle).
        await AssertOneProgram(unmarkedExplicitSpread, markedLifted);
    }

    /// <summary>
    /// A bare reference that static facts show is a READ is no call (R3): no spread, and the slots after it keep their
    /// known positions — the marker changes nothing, so the marked program is the unmarked one.
    /// </summary>
    public static TheoryData<string, string, string> ReadsThatChangeNoRole => new()
    {
        // A collecting-only declaration accepts zero supplied arguments: it is read.
        { "Only(*xs)* = [xs*]", "H = reduce(Only, Add, Inc)\nH(1)", "ok 2" },
        // A zero-parameter declaration with nothing to lift.
        { "G* = [1, 2]", "H = reduce(G, Add, Inc)\nH(1)", "ok 5" },
        { "G* = [1, 2]", "H = G.reduce(Add, Inc)\nH(1)", "ok 5" },
        // A zero-parameter declaration whose body only CALLS: nothing in it can be lifted.
        { "Two(a, b) = [a, b]\nG* = Two(1, 2)", "H = reduce(G, Add, Inc)\nH(1)", "ok 5" },
        // A reference to a closed zero-supply callable cannot lift either: the marked declaration stays a read.
        { "Values(*xs) = [1, 2]\nG* = [Values*]", "H = reduce(G, Add, Inc)\nH(1)", "ok 5" },
        { "Values(*xs) = [1, 2]\nAlias = Values\nG* = [Alias*]", "H = reduce(G, Add, Inc)\nH(1)", "ok 5" },
        { "Box = {\npublic Values(*xs) = [1, 2]\n}\nG* = [Box.Values*]", "H = reduce(G, Add, Inc)\nH(1)", "ok 5" },
        // Callbacks and neutral user arguments never lift their supplied references.
        { "G* = map([1, 2], Inc)", "H = reduce(G, Add, Inc)\nH(1)", "ok 7" },
        { "Use(f) = [f(1)]\nG* = Use(Inc)", "H = reduce(G, Add, Inc)\nH(1)", "ok 4" },
        // A slot that keeps the callable: the argument of a user algorithm, a callback slot.
        { "P(x)* = [x]", "Use(f, g) = f(1)\nH = Use(P, Inc)\nH", "ok L[1]" },
        { "P(x)* = x, x", "H = map([1, 2], P)\nH", "ok L[S[1, 1], S[2, 2]]" },
    };

    [Theory]
    [MemberData(nameof(ReadsThatChangeNoRole))]
    public async Task BareReferenceThatIsRead_NeverSpreads_AndChangesNoRole(string declaration, string formula, string expected)
    {
        var marked = declaration + "\n" + Reducers + formula;
        var unmarked = declaration.Replace(")* =", ") =").Replace("G* =", "G =") + "\n" + Reducers + formula;
        Assert.Equal(expected, await SummaryOnEveryRoute(marked));
        await AssertOneProgram(unmarked, marked);
    }

    [Theory]
    // A closed list that cannot supply the callee's parameter blocks the lift (PAR-04): the reference stays a read —
    // its run-time zero-argument demand — so it is no spread and changes no role, and the prediction says so.
    [InlineData("P(x)* = [x]\n" + Reducers + "H(y) = reduce(P, Add, Inc)\nH(1)", "err ArityMismatch")]
    [InlineData("P(x)* = [x]\n" + Reducers + "G(0) = 0\nG(n) = reduce(P, Add, 10)\nG(3)", "err ArityMismatch")]
    // A closed list, an enclosing parameter binding (Q-04) and a clause branch that supply it: lifted, and spread.
    [InlineData("P(x)* = [x]\n" + Reducers + "H(x) = reduce(P, Add, 10)\nH(1)", "ok 11")]
    [InlineData("P(x)* = [x]\n" + Reducers + "Outer(x) = {\nH = reduce(P, Add, 10)\nH\n}\nOuter(4)", "ok 14")]
    [InlineData("P(x)* = [x]\n" + Reducers + "G(0) = 0\nG(x) = reduce(P, Add, 10)\nG(3)", "ok 13")]
    // A marked carrier is read through to what it invokes: its lifted call spreads because the carrier is marked.
    [InlineData("A(x) = [x]\nB* = { A }\n" + Reducers + "H = reduce(B, Add, 10)\nH(1)", "ok 11")]
    // A marked family formula lifting cannot name is never lifted: the family's own report, no spread.
    [InlineData("F(0, a)* = [a]\nF(a, 0)* = [a]\n" + Reducers + "H = reduce(F, Add, Inc)\nH(1, 2)", "parse UnliftableClauseFamily")]
    public async Task LiftPrediction_FollowsTheClosedListAndTheCalleesSignature(string source, string expected)
        => Assert.Equal(expected, await SummaryOnEveryRoute(source));

    // ── A reference whose lift only selection decides (D2): the error, exactly where the elaboration depends on it ──

    private const string SelectionDependent = "Q(x) = [[x]]\nP* = Q[0]\n" + Reducers;

    [Theory]
    [InlineData("Mk(t) = t\nLink = Mk.Algorithm\nG* = [Link]\n")]
    [InlineData("Mk(t) = t\nBox = {\npublic Link = Mk.Algorithm\n}\nG* = [Box.Link]\n")]
    public void NoLiftCertificate_KeepsRuntimeProjectionDeclarationsConservative(string declarations)
    {
        // Q3's receiver reading has a runtime endpoint for a link, but the declaration's signature may still gain
        // Mk's parameter during selection. Treating that endpoint as absence incorrectly certifies G as a read.
        var source = declarations + Reducers + "H = reduce(G, Add, Inc)\n1";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.OutputSpreadReferenceNeedsCall, diagnostic.Code);
        Assert.Contains("whether `G` is called here", diagnostic.Message);
    }

    [Theory]
    // `reduce`'s initial slot holds a reference the value role lifts and the callable role keeps.
    [InlineData("H = reduce(P, Add, Inc)\nH(1)", 6, 12, "P")]
    [InlineData("H = P.reduce(Add, Inc)\nH(1)", 6, 5, "P")]
    // Under a closed list the rule is the same: the reference decides the roles there too.
    [InlineData("H(x) = reduce(P, Add, Inc)\nH(1)", 6, 15, "P")]
    // A surplus slot after a callback.
    [InlineData("H = map(P, Inc, Inc)\nH(1)", 6, 9, "P")]
    // Loop value and surplus positions follow the same rule as collection builtins.
    [InlineData("H = repeat(Inc(0), P, Inc)\nH(1)", 6, 20, "P")]
    [InlineData("H = while(Inc(0), P, Inc)\nH(1)", 6, 19, "P")]
    // Through a transparent alias the report names both.
    [InlineData("R = P\nH = reduce(R, Add, Inc)\nH(1)", 7, 12, "R")]
    public void SelectionDependentReference_IsReported_WhereALaterSlotDependsOnIt(string program, int line, int column, string reference)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(SelectionDependent + program);
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.OutputSpreadReferenceNeedsCall, diagnostic.Code);
        // Five header lines precede the program; the report spans exactly the bare reference.
        Assert.Equal(new SourcePosition(line, column), diagnostic.Span!.Value.Start);
        Assert.Equal(new SourcePosition(line, column + reference.Length), diagnostic.Span!.Value.End);
        Assert.Contains("only parameter inference decides whether `" + reference + "` is called here", diagnostic.Message);
        Assert.Contains("Write the call: `" + reference + "(…)`.", diagnostic.Message);
        Assert.Contains(reference == "P" ? "`P` is declared with `*`" : "`R` is `P`, which is declared with `*`", diagnostic.Message);

        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(SelectionDependent + program));
        Assert.Equal(KatLangErrorCode.OutputSpreadReferenceNeedsCall, Assert.Single(failure.Errors).Code);
    }

    [Theory]
    // Nothing role-dependent later: a literal initial value, no later slot, a callback only.
    [InlineData("H = reduce(P, Add, 0)\nH(1)", "ok 1")]
    [InlineData("H = count(P)\nH(1)", "ok 1")]
    [InlineData("H = map(P, Inc)\nH(1)", "ok L[2]")]
    [InlineData("H = repeat(Inc(0), P)\nH(1)", "ok 1")]
    [InlineData("H = while(Inc(0), P)\nH(1)", "err ArityMismatch")]
    // `if`: every slot is a value at every position.
    [InlineData("H = if(count(P) == 1, Inc, Inc)\nH(1)", "ok 2")]
    // A user callable keeps its arguments as callables: `P` is not lifted there at all.
    [InlineData("Use(f, g, h) = h(1)\nH = Use(P, Add, Inc)\nH", "ok 2")]
    // The later slot holds a reference neither role lifts.
    [InlineData("Zero = 0\nH = reduce(P, Add, Zero)\nH(1)", "ok 1")]
    // The explicit call is what the message asks for.
    [InlineData("H = reduce(P(x), Add, 10)\nH(1)", "ok 11")]
    // A written spread already ended the known positions before the reference.
    [InlineData("Xs = [[5]]\nH = reduce(Xs*, P, Inc)\nH(1)", "err ArityMismatch")]
    public async Task SelectionDependentReference_IsNoError_WhereNothingDependsOnIt(string program, string expected)
        => Assert.Equal(expected, await SummaryOnEveryRoute(SelectionDependent + program));

    [Theory]
    // A final signature decides the lift: a closed list, a clause family.
    [InlineData("P(x)* = [x]\n" + Reducers + "H = reduce(P, Add, Inc)\nH(1)")]
    [InlineData("P(0)* = [0]\nP(n)* = [n]\n" + Reducers + "H = reduce(P, Add, Inc)\nH(1)")]
    // The declaration's own inferred name requires the argument.
    [InlineData("Q(y) = [y]\nP* = Q + [x]\n" + Reducers + "H = reduce(P, Add, Inc)\nH(1, 2)")]
    // A declaration that lifts nothing is read.
    [InlineData("P* = [1]\n" + Reducers + "H = reduce(P, Add, Inc)\nH(1)")]
    // An unmarked declaration is no subject of the rule, whatever selection decides.
    [InlineData("Q(x) = [x]\nP = Q + 0\n" + Reducers + "H = reduce(P, Add, Inc)\nH(1)")]
    public void StaticallySettledReference_IsNeverReported(string source)
        => Assert.DoesNotContain(SourceProvenance.ParseAllowingDiagnostics(source).Diagnostics, d => d.Code == DiagnosticCode.OutputSpreadReferenceNeedsCall);

    // ── A marked extension edge is the lowered call from parameter detection on (owner decision D1) ──

    public static TheoryData<string, string, string, string> LoweredReceiverFamily => new()
    {
        // An INFERRED member: the call's order, callee first (the reviewer's program).
        { "H = A(x, y).F(3)\nH(Add3, 1, 2)", "H = A(x, y)*.F(3)\nH(Add3, 1, 2)", "H(F, x, y)", "ok 6" },
        { "H = A(x, y).F(3)\nH(1, 2, Add3)", "H = A(x, y)*.F(3)\nH(1, 2, Add3)", "H(F, x, y)", "err NotAnAlgorithm" },
        // A RESOLVED member: nothing to order, the same call.
        { "H = A(x, y).Add3(3)\nH(1, 2)", "H = A(x, y)*.Add3(3)\nH(1, 2)", "H(x, y)", "ok 6" },
        // A receiver reached through a transparent alias, and through a member path.
        { "B = A\nH = B(x, y).F(3)\nH(Add3, 1, 2)", "B = A\nH = B(x, y)*.F(3)\nH(Add3, 1, 2)", "H(F, x, y)", "ok 6" },
        {
            "Lib = {\npublic P(x, y)* = x, y\n}\nH = Lib.P(x, y).F(3)\nH(Add3, 1, 2)",
            "Lib = {\npublic P(x, y) = x, y\n}\nH = Lib.P(x, y)*.F(3)\nH(Add3, 1, 2)",
            "H(F, x, y)", "ok 6"
        },
        // A receiver that is a call to a marked clause family, and to an opened member.
        {
            "Pair(0, b)* = 0, b\nPair(a, b)* = a, b\nH = Pair(x, y).F(3)\nH(Add3, 1, 2)",
            "Pair(0, b) = 0, b\nPair(a, b) = a, b\nH = Pair(x, y)*.F(3)\nH(Add3, 1, 2)",
            "H(F, x, y)", "ok 6"
        },
        // Both edges of a chain are marked calls: each is lowered, the outermost callee first.
        {
            "Swap(a, b, c)* = c, a + b\nH = A(x, y).Swap(3).G\nH(Add, 1, 2)",
            "Swap(a, b, c) = c, a + b\nH = A(x, y)*.Swap(3)*.G\nH(Add, 1, 2)",
            "H(G, x, y)", "ok 6"
        },
        // A chain: the inner edge is the call, the outer edge keeps its own receiver-first order.
        { "H = A(x, y).F(3).G(4)\nH(Add3, 1, 2, Add)", "H = A(x, y)*.F(3).G(4)\nH(Add3, 1, 2, Add)", "H(F, x, y, G)", "ok 10" },
        // A parenthesized receiver is the receiver.
        { "H = (A(x, y)).F(3)\nH(Add3, 1, 2)", "H = (A(x, y))*.F(3)\nH(Add3, 1, 2)", "H(F, x, y)", "ok 6" },
        // Grace: on the member (the callee occurrence's own) and on a name inside the receiver.
        { "H = A(x, y).~F(3)\nH(Add3, 1, 2)", "H = A(x, y)*.~F(3)\nH(Add3, 1, 2)", "H(F, x, y)", "ok 6" },
        { "H = A(x~, y).F(3)\nH(Add3, 2, 1)", "H = A(x~, y)*.F(3)\nH(Add3, 2, 1)", "H(F, y, x)", "ok 6" },
        // An argumentless edge, and an extension call that is itself the receiver.
        { "H = A(x, y).F\nH(Add, 1, 2)", "H = A(x, y)*.F\nH(Add, 1, 2)", "H(F, x, y)", "ok 3" },
        { "Dup(v)* = v, v\nH = 4.Dup.F\nH(Add)", "Dup(v) = v, v\nH = 4.Dup*.F\nH(Add)", "H(F)", "ok 8" },
        // Under a closed list nothing is inferred; the tree is the call's all the same.
        { "H(F, x, y) = A(x, y).F(3)\nH(Add3, 1, 2)", "H(F, x, y) = A(x, y)*.F(3)\nH(Add3, 1, 2)", "H(F, x, y)", "ok 6" },
    };

    [Theory]
    [MemberData(nameof(LoweredReceiverFamily))]
    public async Task MarkedExtensionEdge_IsTheLoweredCall_FromParameterDetectionOn(string marked, string explicitSpread, string signature, string expected)
    {
        const string helpers = "Add(a, b) = a + b\nAdd3(a, b, c) = a + b + c\n";
        var markedSource = "A(x, y)* = x, y\n" + helpers + marked;
        var explicitSource = "A(x, y) = x, y\n" + helpers + explicitSpread;

        Assert.Equal(expected, await SummaryOnEveryRoute(markedSource));
        Assert.Equal(signature, Assert.Single(SemanticModelBuilder.Build(SourceProvenance.ParseValid(markedSource).Parsed).FindProperties("H")).DisplaySignature);
        Assert.Equal(signature, Assert.Single(SemanticModelBuilder.Build(SourceProvenance.ParseValid(explicitSource).Parsed).FindProperties("H")).DisplaySignature);
        await AssertOneProgram(explicitSource, markedSource);
    }

    [Theory]
    // An edge that is no marked extension edge keeps the receiver-first order of every dot edge.
    [InlineData("A(x, y) = x, y\nH = A(x, y).F(3)", "H(x, y, F)")]
    [InlineData("A(x, y)* = x, y\nH = a.F(A(x, y))", "H(a, F, x, y)")]
    [InlineData("A(x, y)* = x, y\nH = A(x, y)[0].F(3)", "H(x, y, F)")]
    [InlineData("A(x, y)* = x, y\nW(x, y) = A(x, y)\nH = W(x, y).F(3)", "H(x, y, F)")]
    [InlineData("A(x, y)* = x, y\nB = { A }\nH = B(x, y).F(3)", "H(x, y, F)")]
    // An intrinsic edge is no extension edge: its receiver is one value.
    [InlineData("A(x, y)* = x, y\nH = A(x, y).string + t", "H(x, y, t)")]
    public void EveryOtherDotEdge_KeepsReceiverFirstOrder(string source, string signature)
        => Assert.Equal(signature, Assert.Single(SemanticModelBuilder.Build(SourceProvenance.ParseValid(source + "\n1").Parsed).FindProperties("H")).DisplaySignature);

    [Fact]
    public void LoweredReceiver_KeepsTheMemberTokensSite_AndCreatesNoneForTheSpread()
    {
        // The lowered call's callee is the edge's member token: the same site the written `A(1, 2)*.F(3)` has. Up to
        // the receiver's closing parenthesis the two sources share their columns.
        const string helpers = "A(x, y)* = x, y\nF(a, b, c) = a + b + c\n";
        var marked = SemanticModelBuilder.Build(SourceProvenance.ParseValid(helpers + "A(1, 2).F(3)").Parsed);
        var written = SemanticModelBuilder.Build(SourceProvenance.ParseValid(helpers.Replace(")* =", ") = ") + "A(1, 2)*.F(3)").Parsed);
        Assert.Equal(
            written.IdentifierOccurrences.Where(static occurrence => occurrence.Span.Start.Line == 3).Select(static occurrence => (occurrence.Name, occurrence.Kind)),
            marked.IdentifierOccurrences.Where(static occurrence => occurrence.Span.Start.Line == 3).Select(static occurrence => (occurrence.Name, occurrence.Kind)));
        var member = Assert.Single(marked.IdentifierOccurrences, static occurrence => occurrence.Name == "F" && occurrence.Span.Start.Line == 3);
        Assert.Equal(new SourceSpan(3, 9, 3, 10), member.Span);
        Assert.Equal("F(a, b, c)", marked.FindResolutionAt(new SourcePosition(3, 9))!.ResolvedProperty!.DisplaySignature);
        Assert.Equal("A(x, y)*", marked.FindResolutionAt(new SourcePosition(3, 1))!.ResolvedProperty!.DisplaySignature);

        // The elaborated tree is the call, with the front end's spread around the receiver (no marker span).
        var call = Assert.IsType<Expr.Call>(Assert.Single(SourceProvenance.ParseValid(helpers + "A(1, 2).F(3)").Root.Output));
        var spread = Assert.IsType<Expr.SequenceSpread>(call.Args[0]);
        Assert.Equal("A", spread.InsertedFor!.DeclarationName);
        Assert.Null(spread.SpreadMarkerSpan);
        Assert.Equal(new SourceSpan(3, 1, 3, 8), spread.Span);
        Assert.Equal(new SourceSpan(3, 1, 3, 13), call.Span);
    }

    // ── The review's nine programs (the two findings of the 2026-11-14 review, with their controls) ──

    private const string ReducePrograms = "Add(a, b) = a + b\nInc(x) = x + 1\n";
    private const string ReceiverPrograms = "Add3(a, b, c) = a + b + c\n";

    public static TheoryData<string, string, string> ReviewPrograms => new()
    {
        // Finding 1 (D2): a lifted marked call is a spread for the later slots, like the explicit call and the written `*`.
        { "P(x)* = [x]\n" + ReducePrograms + "H = reduce(P, Add, Inc)\nH(1)", "H(x)", "err ArityMismatch" },
        { "P(x)* = [x]\n" + ReducePrograms + "H = reduce(P(x), Add, Inc)\nH(1)", "H(x)", "err ArityMismatch" },
        { "P(x) = [x]\n" + ReducePrograms + "H = reduce(P, Add, Inc)\nH(1)", "H(x)", "ok 3" },
        { "P(x) = [x]\n" + ReducePrograms + "H = reduce(P(x), Add, Inc)\nH(1)", "H(x)", "ok 3" },
        { "P(x) = [x]\n" + ReducePrograms + "H = reduce(P(x)*, Add, Inc)\nH(1)", "H(x)", "err ArityMismatch" },
        // Finding 2 (D1): a marked extension edge orders its names as the lowered call does.
        { "A(x, y)* = x, y\n" + ReceiverPrograms + "H = A(x, y).F(3)\nH(1, 2, Add3)", "H(F, x, y)", "err NotAnAlgorithm" },
        { "A(x, y) = x, y\n" + ReceiverPrograms + "H = A(x, y)*.F(3)\nH(1, 2, Add3)", "H(F, x, y)", "err NotAnAlgorithm" },
        { "A(x, y)* = x, y\n" + ReceiverPrograms + "H = F(A(x, y), 3)\nH(Add3, 1, 2)", "H(F, x, y)", "ok 6" },
        { "A(x, y) = x, y\n" + ReceiverPrograms + "H = A(x, y).F(3)\nH(1, 2, Add3)", "H(x, y, F)", "err ArityMismatch" },
    };

    [Theory]
    [MemberData(nameof(ReviewPrograms))]
    public async Task ReviewProgram_HasItsSignatureAndResult_OnEveryRoute(string source, string signature, string expected)
    {
        Assert.Equal(signature, Assert.Single(SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed).FindProperties("H")).DisplaySignature);
        Assert.Equal(expected, await SummaryOnEveryRoute(source));
    }

    // ── Loaded modules and deferred units: the same two decisions where a unit is elaborated later ──

    [Theory]
    // D1: a marked module member as the receiver, in the importer and inside the module itself.
    [InlineData("open '@'\nAdd3(a, b, c) = a + b + c\nH = P(x, y).F(3)\nH(Add3, 1, 2)", "ok 6")]
    [InlineData("open '@'\nAdd3(a, b, c) = a + b + c\nHM(Add3, 1, 2)", "ok 6")]
    // D2: a lifted call to a marked module member ends the known positions.
    [InlineData("open '@'\nAdd(a, b) = a + b\nInc(x) = x + 1\nH = reduce(P1, Add, Inc)\nH(1)", "err ArityMismatch")]
    [InlineData("open '@'\nAdd(a, b) = a + b\nH = reduce(P1, Add, 10)\nH(1)", "ok 11")]
    // A deferred unit (a clause branch that loads the module) decides both when it materializes, for the module's
    // markers and for the eager program's.
    [InlineData("Add3(a, b, c) = a + b + c\nG(0) = 0\nG(n) = {\n    open '@'\n    H = P(x, y).F(3)\n    H(Add3, 1, 2)\n}\nG(1)", "ok 6")]
    [InlineData("A(x, y)* = x, y\nAdd3(a, b, c) = a + b + c\nG(0) = 0\nG(n) = {\n    open '@'\n    H = A(x, y).F(3)\n    H(Add3, 1, 2)\n}\nG(1)", "ok 6")]
    [InlineData("Add(a, b) = a + b\nInc(x) = x + 1\nG(0) = 0\nG(n) = {\n    open '@'\n    H = reduce(P1, Add, Inc)\n    H(1)\n}\nG(1)", "err ArityMismatch")]
    [InlineData("Add(a, b) = a + b\nG(0) = 0\nG(n) = {\n    open '@'\n    H = reduce(P1, Add, 10)\n    H(1)\n}\nG(1)", "ok 11")]
    public async Task ModulesAndDeferredUnits_LowerMarkedReceivers_AndSpreadLiftedCalls(string program, string expected)
    {
        const string url = "https://katlang.org/spread.kat";
        var options = new RunOptions
        {
            DownloadCode = (requested, _) => requested == url
                ? ValueTask.FromResult("public P(x, y)* = x, y\npublic P1(x)* = [x]\npublic HM = P(x, y).F(3)")
                : throw new InvalidOperationException($"404: {requested}"),
        };

        var result = await KatLangEngine.RunAsync(program.Replace("@", url), options);
        var outcome = result switch
        {
            RunResult.Success success => "ok " + SixRouteAgreement.Neutral(success.Value),
            RunResult.EvalFailure failure => "err " + string.Join(" | ", failure.Errors.Select(static error => error.Code)),
            RunResult.ParseFailure failure => "parse " + string.Join(" | ", failure.Errors.Select(static error => error.Code)),
            _ => result.GetType().Name,
        };
        Assert.Equal(expected, outcome);
    }

    // ── Timing (R6): a marked argument runs once, during supply formation, whether or not it is used ──

    [Fact]
    public async Task MarkedArgument_RunsOnceDuringFormation_EvenWhenUnused()
    {
        // The marked argument's ticks precede the call's body; an unmarked argument nothing demands never runs.
        Assert.Equal("ok S[7, 2]", await SummaryOnEveryRoute("T(x)* = x, tick()\nIgnore(*rest) = 7\nIgnore(T(0)), tick()"));
        Assert.Equal("ok S[7, 1]", await SummaryOnEveryRoute("T(x) = x, tick()\nIgnore(*rest) = 7\nIgnore(T(0)), tick()"));
        // Caching is unchanged: `P` is the cached read and never spreads, `P()` a fresh call that does.
        Assert.Equal("ok S[L[S[1, 2], 1, 3], 3]", await SummaryOnEveryRoute("P* = 1, tick() + 1\n[P, P()], tick()"));
    }

    // ── Families, zero-parameter declarations, aliases, carriers ──

    public static TheoryData<string, string> DeclarationKinds => new()
    {
        // A family marked on every clause spreads every call; an unmarked family none.
        { "F(0)* = 0, 0\nF(n)* = n, n * 10\n[F(0), F(2)]", "ok L[0, 0, 2, 20]" },
        { "F(0) = 0, 0\nF(n) = n, n * 10\n[F(0), F(2)]", "ok L[S[0, 0], S[2, 20]]" },
        // A zero-parameter declaration spreads only on an explicit call.
        { "P* = 1, 2\ncount(P)", "ok 2" },
        { "P* = 1, 2\n[P()]", "ok L[1, 2]" },
        { "P* = 1, 2\ncount(P())", "err ArityMismatch" },
        // A collector-only declaration is read bare and spread when called.
        { "Only(*xs)* = xs*\n[Only, Only(1, 2)]", "ok L[S[], 1, 2]" },
        // Aliases inherit the marker through a chain; a transparent alias of a zero-parameter declaration too.
        { "A(x, y)* = x, y\nB = A\nC = B\n[C(1, 2)]", "ok L[1, 2]" },
        { "P* = 1, 2\nQ = P\n[Q, Q()]", "ok L[S[1, 2], 1, 2]" },
        // A structural forwarding carrier is a declaration of its own: marked or not.
        { "A(x, y)* = x, y\nB = { A }\ncount(B(1, 2))", "ok 2" },
        { "A(x, y) = x, y\nB* = { A }\ncount(B(1, 2))", "err ArityMismatch" },
        // Explicit wrappers and bare-forwarding bodies are their own declarations.
        { "A(x, y)* = x, y\nW(x, y) = A(x, y)\ncount(W(1, 2))", "ok 2" },
        { "A(x, y)* = x, y\nG(x, y) = A\ncount(G(1, 2))", "ok 2" },
        // A nested public marked declaration, called through its member path and through `open`.
        { "Lib = {\npublic P(x, y)* = x, y\n}\n[Lib.P(1, 2)]", "ok L[1, 2]" },
        // A marked extension call: `3.Dup` is `Dup(3)`.
        { "Dup(x)* = x, x\n[3.Dup, 4.Dup()]", "ok L[3, 3, 4, 4]" },
    };

    [Theory]
    [MemberData(nameof(DeclarationKinds))]
    public async Task DeclarationKind_SpreadsAsSpecified(string program, string expected)
        => Assert.Equal(expected, await SummaryOnEveryRoute(program));

    // ── Routes that never spread (R3) ──

    public static TheoryData<string, string> NonSpreadingRoutes => new()
    {
        // A call through a parameter.
        { "A(x, y)* = x, y\nApply(f) = count(f(1, 2))\nApply(A)", "ok 2" },
        // A runtime-target alias (an enclosing parameter row).
        { "A(x, y)* = x, y\nUse(f) = {\nG = f\ncount(G(1, 2))\n}\nUse(A)", "ok 2" },
        // `.Algorithm` and `Invoke()` on a captured call.
        { "A(x, y)* = x, y\nBox(meta op) = count(op.Algorithm(1, 2))\nVia(f) = Box(f(0, 0))\nVia(A)", "ok 2" },
        { "A(x, y)* = x, y\nBox(meta op) = count(op.Invoke())\nVia(f) = Box(f(1, 2))\nVia(A)", "ok 2" },
        // A builtin's callback invocation.
        { "Dup(x)* = x, x\nmap([1, 2], Dup)", "ok L[S[1, 1], S[2, 2]]" },
        // A loop's step invocation: the documented workaround is an unmarked wrapper.
        { "Fib(a, b)* = b, a + b\nF(a, b) = Fib(a, b)\nF(0, 1).repeat(10)", "ok S[55, 89]" },
        { "Fib(a, b)* = b, a + b\nF(a, b) = Fib(a, b)\nF(0, 1).while", "err TypeMismatch" },
        // A read is not a call.
        { "P* = 1, 2\nX = P\ncount(X)", "ok 2" },
    };

    [Theory]
    [MemberData(nameof(NonSpreadingRoutes))]
    public async Task NonSpreadingRoute_PassesOneValue(string program, string expected)
        => Assert.Equal(expected, await SummaryOnEveryRoute(program));

    // ── Syntax: heads, attachment, line rules and recovery (R5) ──

    [Theory]
    [InlineData("A* = 1, 2\nA()", "A")]
    [InlineData("A(x, y)* = x, y\nA(1, 2)", "A")]
    [InlineData("public A* = 1\nA()", "A")]
    [InlineData("public A(x)* = x, x\nA(1)", "A")]
    [InlineData("F(0)* = 1\nF(n)* = n\nF(2)", "F")]
    [InlineData("public F(0)* = 1\npublic F(n)* = n\nF(2)", "F")]
    [InlineData("A(x, y)*=x, y\nA(1, 2)", "A")]
    [InlineData("A(x, y)* =\n  x, y\nA(1, 2)", "A")]
    public void MarkedHead_ParsesCleanly_AndMarksItsDeclaration(string source, string name)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var declaration = Assert.Single(root.Properties, property => property.Name == name);
        var marker = Assert.IsType<OutputSpreadMarker>(declaration.Value.OutputSpread);
        Assert.Equal(name, marker.DeclarationName);
        Assert.NotNull(marker.Span);
    }

    [Fact]
    public void NestedMarkedDeclaration_IsMarkedInItsOwnBody()
    {
        var root = SourceProvenance.ParseValid("Lib = {\npublic P(x)* = x, x\nQ = 1\n}\nLib.P(1)").Root;
        var lib = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == "Lib").Value);
        Assert.NotNull(Assert.Single(lib.Properties, property => property.Name == "P").Value.OutputSpread);
        Assert.Null(Assert.Single(lib.Properties, property => property.Name == "Q").Value.OutputSpread);
    }

    [Theory]
    // A detached marker: reported at the star; the declaration is kept, marked.
    [InlineData("A * = 1, 2\nA()", DiagnosticCode.DetachedOutputSpreadMarker, 1, 3, "A")]
    [InlineData("F(x) * = x, x\nF(1)", DiagnosticCode.DetachedOutputSpreadMarker, 1, 6, "F")]
    // A repeated marker: one report over the run; one marker kept.
    [InlineData("A** = 1, 2\nA()", DiagnosticCode.RepeatedOutputSpreadMarker, 1, 2, "A")]
    [InlineData("F(x)** = x, x\nF(1)", DiagnosticCode.RepeatedOutputSpreadMarker, 1, 5, "F")]
    // Some clauses marked: reported at the first clause that differs; the family recovers marked.
    [InlineData("F(0)* = 1, 2\nF(n) = n, n\nF(0)", DiagnosticCode.MixedOutputSpreadMarkers, 2, 1, "F")]
    [InlineData("F(0) = 1, 2\nF(n)* = n, n\nF(0)", DiagnosticCode.MixedOutputSpreadMarkers, 2, 1, "F")]
    public void MalformedMarker_IsReported_AndTheDeclarationIsKept(string source, DiagnosticCode code, int line, int column, string name)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(code, diagnostic.Code);
        Assert.Equal(new SourcePosition(line, column), diagnostic.Span!.Value.Start);
        Assert.NotNull(Assert.Single(parsed.Root.Properties, property => property.Name == name).Value.OutputSpread);
    }

    [Theory]
    [InlineData("a*, b = 1, 2\na", 1, 2)]
    [InlineData("x, y* = 1, 2\nx", 1, 5)]
    [InlineData("*xs* = 1, 2\nxs", 1, 4)]
    public void MarkerOnADeconstructionTarget_IsReported_AndDropped(string source, int line, int column)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.OutputSpreadMarkerOnDeconstructionTarget, diagnostic.Code);
        Assert.Equal(new SourcePosition(line, column), diagnostic.Span!.Value.Start);
        Assert.All(parsed.Root.Properties, property => Assert.Null(property.Value.OutputSpread));
    }

    [Theory]
    // Heads are line-local: the marker and the `=` share the name's (or the `)`'s) line.
    [InlineData("A = 1, 2\nA*\n= 3")]
    [InlineData("F(x) = x, x\nF(1)*\n= 3")]
    public void SplitHead_IsNoDeclaration(string source)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken);
        Assert.All(parsed.Root.Properties, property => Assert.Null(property.Value.OutputSpread));
    }

    [Fact]
    public void DeclarationHead_IsNeverTheOperandOfADanglingStar()
    {
        // `X = 2 *` ends in a detached star — an incomplete multiplication — and the next line's marked head is a
        // declaration, never its operand (#9): one missing-operand report, and `A` keeps its scope and its marker.
        var parsed = SourceProvenance.ParseAllowingDiagnostics("X = 2 *\nA* = 3\nX");
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal(new SourcePosition(1, 7), diagnostic.Span!.Value.Start);
        Assert.NotNull(Assert.Single(parsed.Root.Properties, property => property.Name == "A").Value.OutputSpread);
    }

    [Fact]
    public void AttachedLineFinalSpread_BeforeAMarkedHead_CompletesItsRow()
    {
        // `A*` at the end of its line is a spread row; the next line's head is a marked declaration.
        var root = SourceProvenance.ParseValid("A = 1, 2\nB = A*\nC* = 3\nB, C()").Root;
        Assert.NotNull(Assert.Single(root.Properties, property => property.Name == "C").Value.OutputSpread);
        Assert.Null(Assert.Single(root.Properties, property => property.Name == "B").Value.OutputSpread);
    }

    // ── Declarations the marker is not allowed on (R4) ──

    [Theory]
    [InlineData("A(x, y)* = x, y\nB* = A\nB(1, 2)", 2, 2, "B(x, y)* = A(x, y)")]
    [InlineData("P* = 1\nQ* = P\nQ()", 2, 2, "Q* = P()")]
    [InlineData("A(x, *ys)* = x, ys*\nB* = A\nB(1)", 2, 2, "B(x, *ys)* = A(x, ys*)")]
    public void MarkerOnATransparentAlias_IsReported_WithAMarkedWrapperSuggestion(string source, int line, int column, string suggestion)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.OutputSpreadMarkerOnAlias, diagnostic.Code);
        Assert.Equal(new SourcePosition(line, column), diagnostic.Span!.Value.Start);
        Assert.Contains($"`{suggestion}`", diagnostic.Message);
    }

    [Theory]
    [InlineData("F(f) = {\nG* = f\nG(1)\n}\nF({ x + 1 })")]
    [InlineData("Mk(meta op) = op\nR = Mk(Inc(1))\nInc(x) = x + 1\nH* = R.Algorithm\nH(2)")]
    public void MarkerOnARuntimeTargetAlias_IsReported(string source)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.OutputSpreadMarkerOnAlias, diagnostic.Code);
        Assert.Contains("runtime-target alias", diagnostic.Message);
    }

    [Fact]
    public void MarkerOnACalculationLink_IsReported()
    {
        // `A* = Mk.Algorithm` with `Mk(meta op)` lifts to the calculation `A(op)`: a call through a link is never spread.
        var parsed = SourceProvenance.ParseAllowingDiagnostics("Mk(meta op) = op\nA* = Mk.Algorithm\n1");
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(DiagnosticCode.OutputSpreadMarkerOnAlias, diagnostic.Code);
        Assert.Contains("`.Algorithm` link", diagnostic.Message);
        Assert.Equal(new SourcePosition(2, 2), diagnostic.Span!.Value.Start);
    }

    [Theory]
    // A failed binding-pattern scan's memo also covers the postfix stars it tolerates, so a long same-line list of
    // spread-marked items costs linear lookahead (Codex review round 1).
    [InlineData("open ", "A*, ")]
    [InlineData("", "A*, ")]
    [InlineData("", "a* b, ")]
    public void PostfixStarRuns_KeepHeadLookaheadLinear(string prefix, string unit)
    {
        long previousSteps = 0;
        foreach (var length in new[] { 5_000, 10_000 })
        {
            var source = prefix + string.Concat(Enumerable.Repeat(unit, length)) + "Z\nGood=41\nGood";
            var observations = new ParserTraversalObservations();
            var parsed = Parser.ParseSyntaxObserved(source, observations);
            Assert.Single(parsed.Root.Properties, property => property.Name == "Good");
            Assert.True(observations.TokenSteps > 0);
            if (previousSteps > 0)
                Assert.True(observations.TokenSteps <= 2.5 * previousSteps, $"{unit}: {previousSteps} -> {observations.TokenSteps}");
            previousSteps = observations.TokenSteps;
        }
    }

    [Fact]
    public void MarkerOnAModuleHolder_IsReported()
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics("M* = load('https://katlang.org/lib.kat')\nM");
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.OutputSpreadMarkerOnAlias);
        Assert.Equal(new SourcePosition(1, 2), diagnostic.Span!.Value.Start);
    }

    [Fact]
    public void MarkerOnACarrier_IsAllowed()
        => _ = SourceProvenance.ParseValid("A(x, y) = x, y\nB* = { A }\nB(1, 2)");

    // ── Diagnostics: the note on the call's own failure ──

    [Theory]
    [InlineData("A(x, y)* = x, y\ncount(A(1, 2))", "Note: `A(1, 2)` supplies 2 arguments here because `A` is declared with `*` (line 1).")]
    [InlineData("A(x, y)* = x, y\nAdd(x, y) = x + y\n5.Add(A(1, 2))", "Note: `A(1, 2)` supplies 2 arguments here because `A` is declared with `*` (line 1).")]
    [InlineData("\nFib(a, b)* = b, a + b\nFib(0, 1).repeat(10)", "Note: `Fib(0, 1)` supplies 2 arguments here because `Fib` is declared with `*` (line 2).")]
    [InlineData("P* = 1, 2\nB = { P }\nQ = P\ncount(Q())", "Note: `Q()` supplies 2 arguments here because `P` is declared with `*` (line 1).")]
    [InlineData("A(x, y)* = x, y\nCap(meta op, x) = 1\nCap(A(1, 2))", "Note: `A(1, 2)` is spread into separate arguments here because `A` is declared with `*` (line 1).")]
    [InlineData("A(x, y)* = x, y\nB(x)* = x, x\nAdd(x, y) = x + y\nAdd(A(1, 2), B(3))", "Note: `B(3)` is spread into separate arguments here because `B` is declared with `*` (line 2).")]
    public async Task OwnFailure_NamesTheMarkedDeclaration(string source, string note)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", outcome.Kind);
        Assert.Contains(note + " To pass its output as one value, write `{ ", Assert.Single(outcome.Errors));
    }

    [Fact]
    public void OwnFailure_KeepsItsKindPayloadAndSpan()
    {
        var marked = SourceProvenance.ParseValid("A(x, y)* = x, y\ncount(A(1, 2))").Evaluate();
        var written = SourceProvenance.ParseValid("A(x, y) = x, y\ncount(A(1, 2)*)").Evaluate();
        Assert.True(marked.IsError && written.IsError);
        // Record equality ignores the note: the failure is the explicit counterpart's, kind and payload included,
        // under the same call frame, starting where the call starts (the written star only lengthens the call).
        Assert.Equal(Innermost(written.Error), Innermost(marked.Error));
        var markedFrame = Assert.IsType<EvalError.WithContext>(marked.Error);
        var writtenFrame = Assert.IsType<EvalError.WithContext>(written.Error);
        Assert.Equal(writtenFrame.Context, markedFrame.Context);
        Assert.Equal(writtenFrame.Span!.Value.Start, markedFrame.Span!.Value.Start);
        Assert.Null(Innermost(written.Error).OutputSpreadNotes);
        Assert.Single(Innermost(marked.Error).OutputSpreadNotes!);
        Assert.Equal(KatLangError.FromEvalError(written.Error).Code, KatLangError.FromEvalError(marked.Error).Code);
    }

    [Fact]
    public async Task CapturedCallFailure_NamesTheMarkedDeclaration_OnThePlannedRoute()
    {
        // The captured `count(P())` runs through its invocation plan (Codex review round 1).
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("P* = 1, 2\nRun(meta op) = op.Invoke()\nRun(count(P()))");
        Assert.Equal("err", outcome.Kind);
        Assert.Contains("Note: `P()` supplies 2 arguments here because `P` is declared with `*` (line 1).", Assert.Single(outcome.Errors));
    }

    [Theory]
    // A failure from inside the callee is not the call's own: no note.
    [InlineData("A(x, y)* = x, y\nInner(x) = count(x, x)\nOuter(a, b) = Inner(a)\nOuter(A(1, 2))")]
    // No inserted spread: no note.
    [InlineData("A(x, y) = x, y\ncount(A(1, 2)*)")]
    // A META refusal of a WRITTEN argument is not the inserted spread's doing (Codex review round 1).
    [InlineData("P* = 7\nC(meta op, x) = 0\nC(5, P())")]
    public async Task OtherFailures_CarryNoNote(string source)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", outcome.Kind);
        Assert.DoesNotContain("Note: `", Assert.Single(outcome.Errors));
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    // ── Elaboration: the inserted node, its span, and sharing ──

    [Fact]
    public void InsertedSpread_TakesTheCallsSpan_AndNamesTheDeclaration()
    {
        var root = SourceProvenance.ParseValid("A(x, y)* = x, y\ncount([A(1, 2)])").Root;
        var call = Assert.IsType<Expr.Call>(Assert.Single(root.Output));
        var list = Assert.IsType<Expr.ListLiteral>(Assert.Single(call.Args));
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(list.Items));
        Assert.Equal("A", spread.InsertedFor!.DeclarationName);
        Assert.Null(spread.SpreadMarkerSpan);
        Assert.Equal(spread.Operand.Span, spread.Span);
        Assert.Equal(new SourceSpan(2, 8, 2, 15), spread.Span);
    }

    [Fact]
    public void LiftedCalls_KeepSharingTheirOneImplicitArgumentBundle()
    {
        // FE-2: every lifted reference to one callee in one rewrite region shares ONE synthesized argument bundle;
        // spreading wraps the call node that holds it, never the bundle.
        var root = SourceProvenance.ParseValid("A(x, y)* = x, y\nS = [A, A]\nS(1, 2)").Root;
        var s = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == "S").Value);
        var list = Assert.IsType<Expr.ListLiteral>(Assert.Single(s.Output));
        var calls = list.Items.Select(item => Assert.IsType<Expr.Call>(Assert.IsType<Expr.SequenceSpread>(item).Operand)).ToList();
        Assert.Equal(2, calls.Count);
        Assert.Same(calls[0].Args, calls[1].Args);
    }

    [Fact]
    public void ProgramWithoutMarkers_ElaboratesExactlyAsBefore()
    {
        // No admission met a marker, so no call is examined: the unmarked counterpart of a marked program keeps its
        // unspread calls.
        var root = SourceProvenance.ParseValid("A(x, y) = x, y\ncount(A(1, 2))").Root;
        var call = Assert.IsType<Expr.Call>(Assert.Single(root.Output));
        Assert.IsType<Expr.Call>(Assert.Single(call.Args));
    }

    // ── Loaded modules: a module's marked declaration spreads its importers' calls ──

    [Fact]
    public async Task ModuleMember_SpreadsTheImportersCalls_WithALocationlessNote()
    {
        const string url = "https://katlang.org/spread.kat";
        var options = new RunOptions
        {
            DownloadCode = (requested, _) => requested == url
                ? ValueTask.FromResult("public P(x, y)* = x, y\npublic Q(x) = [P(x, x)]")
                : throw new InvalidOperationException($"404: {requested}"),
        };

        var success = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync($"open '{url}'\n[P(1, 2)], Q(3)", options));
        Assert.Equal("S[L[1, 2], L[3, 3]]", SixRouteAgreement.Neutral(success.Value));

        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync($"open '{url}'\ncount(P(1, 2))", options));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        Assert.Contains("Note: `P(1, 2)` supplies 2 arguments here because `P` is declared with `*`. ", error.Message);

        // A deferred unit — a clause branch that loads the module — spreads its calls too: its operation inherits the
        // eager admission's marker fact and adds the loaded unit's own (Codex review round 1).
        var deferred = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(
            $"Add(x, y) = x + y\nF(0) = 0\nF(n) = {{\n    open '{url}'\n    Add(P(1, 2))\n}}\nF(1)", options));
        Assert.Equal("3", SixRouteAgreement.Neutral(deferred.Value));
        var inherited = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(
            $"A(x, y)* = x, y\nAdd(x, y) = x + y\nF(0) = 0\nF(n) = {{\n    open '{url}'\n    Add(A(1, 2))\n}}\nF(1)", options));
        Assert.Equal("3", SixRouteAgreement.Neutral(inherited.Value));
    }

    // ── The editor: the marker in signatures, no site for an inserted node ──

    [Fact]
    public void Signature_ShowsTheMarker_OnTheDeclarationAndItsAliases()
    {
        var parsed = SourceProvenance.ParseValid("A(x, y)* = x, y\nB = A\nP* = 1\nC = { A }\nW(x) = x\nW(A(1, 2))");
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        Assert.Equal("A(x, y)*", Assert.Single(model.FindProperties("A")).DisplaySignature);
        Assert.True(Assert.Single(model.FindProperties("A")).SpreadsOutput);
        Assert.Equal("B(x, y)*", Assert.Single(model.FindProperties("B")).DisplaySignature);
        Assert.Equal("P*", Assert.Single(model.FindProperties("P")).DisplaySignature);
        // A carrier is a declaration of its own, and this one is unmarked.
        Assert.False(Assert.Single(model.FindProperties("C")).SpreadsOutput);
        Assert.Equal("W(x)", Assert.Single(model.FindProperties("W")).DisplaySignature);
    }

    [Fact]
    public void InsertedSpreads_CreateNoSemanticSites()
    {
        var marked = SemanticModelBuilder.Build(SourceProvenance.ParseValid("A(x, y)* = x, y\n[A(1, 2), count({ A(3, 4) })]").Parsed);
        // The same columns, so occurrence spans compare directly.
        var plain = SemanticModelBuilder.Build(SourceProvenance.ParseValid("A(x, y) =  x, y\n[A(1, 2), count({ A(3, 4) })]").Parsed);
        Assert.Equal(
            plain.IdentifierOccurrences.Select(static occurrence => (occurrence.Name, occurrence.Span)),
            marked.IdentifierOccurrences.Select(static occurrence => (occurrence.Name, occurrence.Span)));
        Assert.Equal(
            plain.IdentifierResolutions.Select(static resolution => (resolution.Occurrence.Name, resolution.Occurrence.Span)),
            marked.IdentifierResolutions.Select(static resolution => (resolution.Occurrence.Name, resolution.Occurrence.Span)));
        var hover = marked.FindResolutionAt(new SourcePosition(2, 2));
        Assert.Equal("A(x, y)*", hover!.ResolvedProperty!.DisplaySignature);
    }
}
