using KatLang.Evaluation;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// META-S3-1: the META-S3 research corpus (R1 cycles <c>C*</c>, asynchronous resolution <c>AS*</c>,
/// deferred source admission <c>DM*</c>, non-observing optimizer recognition <c>OP*</c>, VALUE/CALLABLE
/// independence <c>VC*</c>, loops <c>LP*</c>; R2 VALUE→CALLABLE→VALUE re-entry <c>Q1*</c>, callback/loop
/// re-entry <c>Q5*</c>, runtime failure versus static absence <c>E*</c>; runtime aliases <c>RA*</c>, since META-S3-2 positive)
/// promoted to permanent source-level tests over the public <c>R.Algorithm</c>. Each case runs in its own
/// bounded task on the synchronous generic evaluator, the synchronous optimized evaluator and the
/// asynchronous engine (with genuinely asynchronous host operations), and every mode must give the
/// recorded outcome, the recorded host effects, identical diagnostics and spans, and the same semantic step
/// count — except that where host-stack headroom decides (Q-09a), a mode may instead stop at the host-stack
/// backstop after a prefix of the recorded effects; the optimized mode must also
/// show the recorded loop and fusion counters. The expectations were verified against the R2 prototype's
/// recorded outcomes; the deliberate differences are the runtime aliases (<c>RA*</c>, <c>AS3</c>–
/// <c>AS6</c>, <c>AS13</c>: ordinary property semantics until META-S3-2, now runtime-target callable aliases,
/// FWD-02 — their call is the projected identity's fresh call), diagnostic enrichment that may not start a
/// runtime projection (<c>AS11</c>, <c>AS12</c>) and headroom (<c>C3b</c>, <c>C8b</c>: they record the
/// outcome a run reaches when the host stack does not stop it first). Parser probes are
/// kept separately (<see cref="FrontEndProbes_AreParseErrors"/>), and bounded <c>MaxSteps</c> scans compare
/// the three modes at every limit (<see cref="StepLimitScans_AgreeAcrossModes"/>).
/// </summary>
public class CallReferenceS3CorpusTests
{
    private const string Lib = """
        Square(x) = trace(x) * x
        Inc(x) = x + 1
        Dec(x) = x - 1
        Capture(meta operation) = operation
        Hold(g) = Capture(g(0))
        Apply(f, x) = f(x)
        Forward(f, x) = Apply(f, x)

        """;

    private const string ModuleUrl = "https://modules.example/m.kat";
    private const string ModuleText = "public Inc2(x) = x + 2";
    private const string Q = "Take(x) = x\n";
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    public sealed record Case(string Id, string Source, string Expected, string Traces, string Loops, string Fusion,
        bool AsyncOnly = false, bool HeadroomSensitive = false, EvaluationLimits? Limits = null, string? Module = null,
        bool WithCancel = false, int ExpectedAdmissions = 1);

    // R0 = Capture(Square(5)), Rk = Hold(R(k-1).Algorithm): a noncyclic chain of k links.
    private static string Chain(int length)
    {
        var builder = new System.Text.StringBuilder("R0 = Capture(Square(5))\n");
        for (var k = 1; k <= length; k++) builder.Append($"R{k} = Hold(R{k - 1}.Algorithm)\n");
        return builder.ToString();
    }

    private static readonly Case[] Cases =
    [
        new("C1a", "R = Hold(R.Algorithm)\nR.Algorithm(1)", "err DemandCycle", "", "0/0", "0/0"),
        new("C1b", "R = Hold(R.Algorithm)\nR.Algorithm", "err DemandCycle", "", "0/0", "0/0"),
        new("C1c", "R = Hold(R.Algorithm)\nApply(R.Algorithm, 1)", "err DemandCycle", "", "0/0", "0/0"),
        new("C1d", "R = Hold(R.Algorithm)\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),
        new("C1e", "R = Hold(R.Algorithm)\ncount((R, 1))", "ok 2", "", "0/0", "0/0"),
        new("C1f", "R = Hold(R.Algorithm)\nR.Arguments.count", "ok 1", "", "0/0", "0/0"),
        new("C1g", "R = Hold(R.Algorithm)\n(R.Algorithm)(1)", "err DemandCycle", "", "0/0", "0/0"),
        new("C2a", "R1 = Hold(R2.Algorithm)\nR2 = Hold(R1.Algorithm)\nR1.Algorithm(1)", "err DemandCycle", "", "0/0", "0/0"),
        new("C2b", "R1 = Hold(R2.Algorithm)\nR2 = Hold(R3.Algorithm)\nR3 = Hold(R1.Algorithm)\nApply(R1.Algorithm, 1)", "err DemandCycle", "", "0/0", "0/0"),
        new("C2c", "R1 = Hold(R2.Algorithm)\nR2 = Hold(R1.Algorithm)\nR1.Invoke()", "err DemandCycle", "", "0/0", "0/0"),
        new("C2d", "Box = { G(x) = x * 10 }\nMk(p) = Hold(p.G)\nR = Mk(R.Algorithm)\nR.Algorithm(1)", "err DemandCycle", "", "0/0", "0/0"),
        new("C3a", "Keep(meta op) = op\nHold2(g) = if(g > 0, Capture(Inc(0)), Capture(Dec(0)))\nR = Keep(Inc(Apply(Hold2(R.Arguments*).Algorithm, 5)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),
        new("C3b", "X = Apply(X.Algorithm, 1)\nX", "err EvaluationDepthExceeded", "", "0/0", "0/0", HeadroomSensitive: true),
        new("C4a", "R = Hold(R.Algorithm)\ncount((R, 1)), R.Algorithm(1)", "err DemandCycle", "", "0/0", "0/0"),
        new("C4b", "R = Hold(R.Algorithm)\nR.Arguments.count, Apply(R.Algorithm, 1)", "err DemandCycle", "", "0/0", "0/0"),
        new("C6a", "R = if(aflag(), Hold(R.Algorithm), 0)\nR.Algorithm(1)", "err DemandCycle", "", "0/0", "0/0"),
        new("C6b", "R = if(aflag(), Hold(R.Algorithm), 0)\nApply(R.Algorithm, 1)", "err DemandCycle", "", "0/0", "0/0"),
        new("C6c", "R1 = if(aflag(), Hold(R2.Algorithm), 0)\nR2 = Hold(R1.Algorithm)\nR1.Algorithm(1)", "err DemandCycle", "", "0/0", "0/0"),
        new("C6d", "R = if(aflag(), Hold(R.Algorithm), 0)\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),
        new("C7a", "R = Capture(Square(5))\nBoth(f, g) = f(2) + g(3)\nBoth(R.Algorithm, R.Algorithm)", "ok 13", "2,3", "0/0", "0/0"),
        new("C7b", "Mk(g) = Capture(g(5))\nR = Mk(Square)\nQ = Mk(R.Algorithm)\nPair(a, b) = a(1) + b(2)\nPair(Q.Algorithm, R.Algorithm), Q.Algorithm(3)", "ok (5, 9)", "1,2,3", "0/0", "0/0"),
        new("C7c", "R0 = Capture(Square(5))\nR1 = Hold(R0.Algorithm)\nR2 = Hold(R1.Algorithm)\nR2.Algorithm(4), R1.Algorithm(5), Apply(R2.Algorithm, 6)", "ok (16, 25, 36)", "4,5,6", "0/0", "0/0"),
        new("C7d", "K(*xs) = count(xs)\nSel(t) = if(trace(t) > 0, Capture(K(t)), Capture(K(t)))\nBoth(f) = (f, f(7, 8))\nBoth(Sel(trace(1)).Algorithm)", "ok (0, 2)", "1,1", "0/0", "0/0"),
        new("C7e", "Fact(n) = if(n <= 1, 1, n * Fact(n - 1))\nR = Capture(Fact(1))\nR.Algorithm(5), Apply(R.Algorithm, 4)", "ok (120, 24)", "", "0/0", "0/0"),
        new("C7f", "Box = { G(x) = x * 10 }\nMk(p) = Hold(p.G)\nR = Mk(Box)\nR.Algorithm(3), Apply(R.Algorithm, 4)", "ok (30, 40)", "", "0/0", "0/0"),
        new("C7g", "Mk(g) = Capture(g(5))\nR = Mk(Square)\nQ = Mk(R.Algorithm)\nS = Mk(Q.Algorithm)\nS.Algorithm(2), Q.Algorithm(3), Apply(S.Algorithm, 4)", "ok (4, 9, 16)", "2,3,4", "0/0", "0/0"),
        new("C8a", Chain(40) + "R40.Algorithm(3)", "ok 9", "3", "0/0", "0/0"),
        new("C8b", Chain(3000) + "R3000.Algorithm(3)", "ok 9", "3", "0/0", "0/0", HeadroomSensitive: true),
        new("AS1", "R = if(aflag(), Capture(Square(5)), Capture(Inc(5)))\nUse(f) = 9.f\nUse(R.Algorithm)", "ok 81", "9", "0/0", "0/0"),
        new("AS1b", "R = if(aflag(), Capture(Square(5)), Capture(Inc(5)))\nUse(f) = 9.f\ncount((R, 0)), Use(R.Algorithm)", "ok (2, 81)", "9", "0/0", "0/0"),
        new("AS2", "MkBox(k) = {\n  G(x) = x * 10\n  k\n}\nR = if(aflag(), Capture(MkBox(1)), 0)\nUse(b) = b.G(3)\nUse(R.Algorithm)", "ok 30", "", "0/0", "0/0"),
        new("AS3", "R = if(aflag(), Capture(Square(5)), 0)\nBox = { A = R.Algorithm }\nUse(f) = f(4)\nUse(Box.A)", "ok 16", "4", "0/0", "0/0"),
        new("AS4", "R = if(aflag(), Capture(Square(5)), 0)\nBox = { A = R.Algorithm }\nUse(b) = Apply(b.A, 4)\nUse(Box)", "ok 16", "4", "0/0", "0/0"),
        new("AS5", "R = if(aflag(), Capture(Square(5)), 0)\nBox = { A = R.Algorithm }\n[1, 2].map(Box.A)", "ok [1, 4]", "1,2", "0/0", "0/0"),
        new("AS6", "Step(x) = x + 1, x < 3\nR = if(aflag(), Capture(Step(0)), 0)\nBox = { A = R.Algorithm }\nBA = Box.A\nBA(0).while", "ok 3", "", "1/0", "0/0"),
        new("AS7", "R = if(aflag(), 1 / 0, 0)\nUse(f) = 9.f\nUse(R.Algorithm)", "err DivisionByZero", "", "0/0", "0/0"),
        new("AS8", "R = if(aflag(), 5, 0)\nUse(f) = 9.f\nUse(R.Algorithm)", "err TypeMismatch", "", "0/0", "0/0"),
        new("AS9", "R = if(stop(), Capture(Square(5)), 0)\nUse(f) = 9.f\nUse(R.Algorithm), trace(1)", "cancelled", "", "0/0", "0/0", WithCancel: true),
        new("AS10", "R = if(aflag(), Hold(R.Algorithm), 0)\nsum(R.Algorithm)", "err DemandCycle", "", "0/0", "0/0"),
        new("AS11", "R = if(aflag(), Capture(Square(5)), 0)\nsum(R.Algorithm)", "err ArityMismatch", "", "0/0", "0/0"),
        new("AS12", "Add(a, b) = a + b\nR = if(aflag(), Capture(Add(0, 0)), 0)\n[1, 2].reduce(Add, R.Algorithm)", "err ArityMismatch", "", "0/0", "0/0"),
        new("AS13", "R = if(aflag(), Capture(Square(5)), 0)\nUse(f) = {\n  A = f\n  A(3)\n}\nUse(R.Algorithm)", "ok 9", "3", "0/0", "0/0"),
        new("AS14", "K(*xs) = count(xs)\nSame(f, f) = f(3)\nR = if(aflag(), Capture(K(1)), 0)\nSame(R.Algorithm, R.Algorithm)", "ok 1", "", "0/0", "0/0"),
        new("AS15", "R = if(aflag(), Capture(Square(5)), 0)\nUse(r) = Apply(r.Algorithm, 6)\nUse(R)", "ok 36", "6", "0/0", "0/0"),
        new("AS16", "R = if(aflag(), Capture(Square(5)), 0)\nUse(r) = r.Algorithm\nUse(R)", "err ArityMismatch", "", "0/0", "0/0"),
        new("AS17", "MkBox(k) = {\n  G(x) = x * 10\n  k\n}\nR = if(aflag(), Capture(MkBox(1)), 0)\nMk(p) = Apply(p.G, 4)\nMk(R.Algorithm)", "ok 40", "", "0/0", "0/0"),
        new("AS19", "R = if(aflag(), Capture(Square(5)), 0)\nUse(f) = f.Algorithm\nUse(R)", "err ArityMismatch", "", "0/0", "0/0"),
        new("AS20", "MkBox(k) = {\n  G = 5\n  k\n}\nR = if(aflag(), Capture(MkBox(1)), 0)\nUse(b) = b.G.string\nUse(R.Algorithm)", "ok '5'", "", "0/0", "0/0"),
        new("AS-family", "F(0) = 100\nF(n) = n * 2\nR = if(aflag(), Capture(F(0)), 0)\n[0, 1, 2].map(R.Algorithm)", "ok [100, 2, 4]", "", "0/0", "0/0"),
        new("RA16b", "Box = { Sq = Square }\nBox.Sq(9), (Box.Sq)(9), Apply(Box.Sq, 9)", "ok (81, 81, 81)", "9,9,9", "0/0", "0/0"),
        new("DM1", $"F(0) = Capture(Inc(0))\nF(n) = {{ open '{ModuleUrl}'\n Capture(Inc2(n)) }}\nR = F(1)\nApply(R.Algorithm, 5), trace(99)", "ok (7, 99)", "99", "", "", AsyncOnly: true, Module: ModuleText),
        new("DM2", $"F(0) = 42\nF(n) = {{ open '{ModuleUrl}'\n Inc2(n) }}\nR = Capture(F(0))\nApply(R.Algorithm, 0), trace(1), Apply(R.Algorithm, 3)", "ok (42, 1, 5)", "1", "", "", AsyncOnly: true, Module: ModuleText),
        new("DM3", $"F(0) = Capture(Inc(0))\nF(n) = {{ open '{ModuleUrl}'\n Capture(Inc2(n)) }}\nR = F(1)\nApply(R.Algorithm, 5), trace(99)", "err LoadFetchFailed", "", "", "", AsyncOnly: true, Module: "<fail>"),
        new("DM4", $"F(0) = Capture(Inc(0))\nF(n) = {{ open '{ModuleUrl}'\n Capture(Inc2(n)) }}\nR = F(1)\nApply(R.Algorithm, 5), trace(99)", "cancelled", "", "", "", AsyncOnly: true, Module: "<cancel>", WithCancel: true),
        new("DM5", $"F(0) = 42\nF(n) = {{ open '{ModuleUrl}'\n Inc2(n) }}\nR = Capture(F(0))\nUse(f) = 9.f\nUse(R.Algorithm), trace(1)", "ok (11, 1)", "1", "", "", AsyncOnly: true, Module: ModuleText),
        new("DM-unused", $"F(0) = 42\nF(n) = {{ open '{ModuleUrl}'\n Inc2(n) }}\nR = Capture(F(0))\nApply(R.Algorithm, 0)", "ok 42", "", "", "", AsyncOnly: true, Module: ModuleText, ExpectedAdmissions: 0),
        new("OP1", "Deep(n) = if(n <= 0, Capture(range(0, 0)), Deep(n - 1))\nIsBig(x) = x > 5\nUse(f) = count(filter(f(1, 10), IsBig))\nUse(Deep(4).Algorithm)", "ok 5", "", "0/0", "0/0"),
        new("OP2", "Deep(n) = if(trace(n) <= 0, Capture(range(0, 0)), Deep(n - 1))\nIsBig(x) = x > 5\nUse(f) = count(filter(f(1, 10), IsBig))\nUse(Deep(4).Algorithm)", "ok 5", "4,3,2,1,0", "0/0", "0/0"),
        new("OP3", "R = Capture(range(0, 0))\nIsBig(x) = x > 5\nUse(f) = (f(1, 1), count(filter(f(1, 10), IsBig)))\nUse(R.Algorithm)", "ok ([1], 5)", "", "0/0", "1/1"),
        new("OP4", "R = Capture(range(0, 0))\nIsBig(x) = x > 5\nUse(f) = count(filter(f(1, 10), IsBig))\nUse(R.Algorithm)", "ok 5", "", "0/0", "0/0"),
        new("OP5", "IsBig(x) = x > 5\nE = Capture(IsBig(0))\nUse(p) = count(filter(range(1, 10), p))\nUse(E.Algorithm)", "ok 5", "", "0/0", "1/1"),
        new("OP6", "IsBig(x) = x > 5\nUse(g) = count(filter(g(1, 10), IsBig))\nUse(range)", "ok 5", "", "0/0", "1/1"),
        new("OP7", "Mk(t) = if(trace(t) > 0, Capture(range(0, 0)), 0)\nIsBig(x) = x > 5\nUse(f) = count(filter(f(1, 10), IsBig))\nUse(Mk(7).Algorithm)", "ok 5", "7", "0/0", "0/0"),
        new("OP8", "R = Capture(range(0, 0))\nIsBig(x) = x > 5\nUse(xs) = xs.filter(IsBig).count\nUse(R.Algorithm(1, 10))", "ok 5", "", "0/0", "1/0"),
        new("RA1", "R = Capture(Square(5))\nA = R.Algorithm\nA(9)", "ok 81", "9", "0/0", "0/0"),
        new("RA2", "R = Capture(Square(5))\nA = R.Algorithm\n9.A", "ok 81", "9", "0/0", "0/0"),
        new("RA3", "R = Capture(Square(5))\nBox = { A = R.Algorithm }\nBox.A(9)", "ok 81", "9", "0/0", "0/0"),
        new("RA4", "R = Capture(Square(5))\nBox = { A = R.Algorithm }\n(Box.A)(9)", "ok 81", "9", "0/0", "0/0"),
        new("RA5", "R = Capture(Square(5))\nA = R.Algorithm\nApply(A, 9)", "ok 81", "9", "0/0", "0/0"),
        new("RA6", "Step(x) = x + 1, x < 3\nR = Capture(Step(0))\nA = R.Algorithm\nA(0).while", "ok 3", "", "1/0", "0/0"),
        new("RA7", "R = Capture(Square(5))\nA = R.Algorithm\n[1, 2].map(A)", "ok [1, 4]", "1,2", "0/0", "0/0"),
        new("RA8", "R = Capture(Square(5))\nA = R.Algorithm\nB = A\nB(9)", "ok 81", "9", "0/0", "0/0"),
        new("RA10", "Use(f) = {\n  A = f\n  9.A\n}\nUse(Square)", "ok 81", "9", "0/0", "0/0"),
        new("RA11", "Use(f) = {\n  A = f\n  A(9)\n}\nUse(Square)", "ok 81", "9", "0/0", "0/0"),
        // M4★ OD-B: `A = b.G` is a parameter-rooted MEMBER alias (formerly A inferred the fallback name G
        // as its parameter, and A(3) read the member G as a value: ArityMismatch).
        new("RA12", "Box = { G(x) = x * 10 }\nUse(b) = {\n  A = b.G\n  A(3), 3.A\n}\nUse(Box)", "ok (30, 30)", "", "0/0", "0/0"),
        new("RA13", "R = Capture(Square(5))\nA = R.Algorithm\nBox = { B = A }\nBox.B(9)", "ok 81", "9", "0/0", "0/0"),
        new("RA14", "Only(*xs) = tick()\nUse(f) = {\n  A = f\n  A, A(), A()\n}\nUse(Only)", "ok (1, 2, 3)", "", "0/0", "0/0"),
        new("RA15", "Sq = Square\n9.Sq, Apply(Sq, 9), Sq(9)", "ok (81, 81, 81)", "9,9,9", "0/0", "0/0"),
        new("RA17", "R = Capture(Square(5))\nA = R.Algorithm\nR2 = Capture(A(4))\nR2.Invoke(), R2.Algorithm(5)", "ok (16, 25)", "4,5", "0/0", "0/0"),
        new("RA18", "Use(f) = {\n  A = f\n  W(x) = A\n  W(4)\n}\nUse(Square)", "err ArityMismatch", "", "0/0", "0/0"),
        new("VC1", "Z = tick()\nR = Capture(Z())\nR.Algorithm", "ok 1", "", "0/0", "0/0"),
        new("VC2", "Z = tick()\nR = Capture(Z())\nIgnore(f) = 7\nIgnore(R.Algorithm), tick()", "ok (7, 1)", "", "0/0", "0/0"),
        new("VC3", "Z = tick()\nMk(t) = if(trace(t) > 0, Capture(Z()), 0)\nTwice(f) = (f(), f())\nTwice(Mk(1).Algorithm), tick()", "ok ((1, 2), 3)", "1", "0/0", "0/0"),
        new("VC4", "T(x) = x * 10\nR = Capture(T(trace(5)))\nR.Algorithm(2)", "ok 20", "", "0/0", "0/0"),
        new("VC5", "Mk(x) = {\n  Pick(t) = if(t > 0, Capture(Square(999)), Capture(Inc(999)))\n  Hold2(g) = Capture(g(x))\n  Hold2(Pick(x).Algorithm)\n}\nR = Mk(trace(5))\nR.Algorithm(8)", "ok 64", "5,8", "0/0", "0/0"),
        new("VC6", "T(x) = x * 10\nR = Capture(T(trace(5)))\nR.Algorithm(2), R.Invoke(), R.Invoke()", "ok (20, 50, 50)", "5", "0/0", "0/0"),
        new("VC7", "Z = tick()\nR = Capture(Z())\nR.Algorithm, Z, R.Algorithm", "ok (1, 1, 1)", "", "0/0", "0/0"),
        new("VC8", "Square2(x) = x * x\nR = Capture(Square2(5))\nR.Algorithm", "err ArityMismatch", "", "0/0", "0/0"),
        new("VC9a", "K(*xs) = count(xs)\nSel(t) = if(atrace(t) > 0, Capture(K(t)), 0)\nBoth(f) = (f, f(7, 8))\nBoth(Sel(1).Algorithm)", "ok (0, 2)", "a1", "0/0", "0/0"),
        new("VC9b", "K(*xs) = count(xs)\nSel(t) = if(atrace(t) > 0, Capture(K(t)), 0)\nBoth(f) = (f(7, 8), f)\nBoth(Sel(1).Algorithm)", "ok (2, 0)", "a1", "0/0", "0/0"),
        new("VC10", "T(x) = x * x\nProject(meta op) = op.Algorithm(8)\nAfter(x) = if(x > 0, (Project(x), x), 0)\nAfter(T(atrace(5)))", "ok (64, 25)", "a5", "0/0", "0/0"),
        new("LP1", "Step(x) = x + 1, x < 3\nR = Capture(Step(0))\nRA = R.Algorithm\nRA(R.Arguments*).while", "ok 3", "", "1/0", "0/0"),
        new("LP2", "Fib(a, b, n) = b, a + b, n - 1, n > 1\nR = Capture(Fib(0, 1, 10))\nRA = R.Algorithm\nRA(R.Arguments*).while, Fib(0, 1, 10).while", "ok ((34, 55, 1), (34, 55, 1))", "", "2/0", "0/0"),
        new("LP3", "Step(x) = x + 1, x < 3\nLoop(meta operation) = {\n  S = operation.Algorithm\n  S(operation.Arguments*).while\n}\nLoop(Step(0)), Step(0).Loop", "ok (3, 3)", "", "2/0", "0/0"),
        new("LP4", "Step(x) = x + 1, x < 3\nR = if(aflag(), Capture(Step(0)), Capture(Step(1)))\nRA = R.Algorithm\nRA(R.Arguments*).while", "ok 3", "", "1/0", "0/0"),
        new("LP5", "G(x) = x + 1 + 0 * (1 / (3 - x)), x < 3\nR = Capture(G(0))\nRA = R.Algorithm\nRA(R.Arguments*).while, G(0).while", "ok (3.000000000000000000000000000000000, 3.000000000000000000000000000000000)", "", "2/0", "0/0"),
        new("LP6", "Step(x) = x + 1, x < 3\nR = Capture(Step(5))\nRA = R.Algorithm\nRA(R.Arguments*).while, Step(5).while", "ok (5, 5)", "", "2/0", "0/0"),
        new("LP7", "Increment(x) = x + 1\nTimes(meta operation, n) = {\n  S = operation.Algorithm\n  S(operation.Arguments*).repeat(n)\n}\nIncrement(0).Times(5)", "ok 5", "", "1/0", "0/0"),
        new("Q1", Q + "Use(x) = Apply(x.Algorithm, 0)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // Codex, verbatim
        new("Q1b", Q + "Use(x) = x.Algorithm(0)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // fresh invocation
        new("Q1c", Q + "Use(x) = (x.Algorithm)(0)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // callee position
        new("Q1d", Q + "Use(x) = [0].map(x.Algorithm)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // map callback
        new("Q1e", Q + "Use(x) = [0].filter(x.Algorithm)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // filter callback
        new("Q1f", Q + "Use(x) = [1, 2].reduce(x.Algorithm, 0)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // reduce callback
        new("Q1g", Q + "Use(x) = {\n  A = x.Algorithm\n  A(0).while\n}\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // loop step
        new("Q1h", Q + "Use(x) = x.Algorithm\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // bare VALUE
        new("Q1i", Q + "Same(f, f) = f(0)\nUse(x) = Same(x.Algorithm, x.Algorithm)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // repeated name
        new("Q1j", Q + "Use(x) = Forward(x.Algorithm, 0)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // forwarded twice
        new("Q1l", Q + "Use(f) = 9.f\nW(x) = Use(x.Algorithm)\nR = Capture(Take(W(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // lexical fallback route
        new("Q1m", Q + "Use(x) = Apply(x.Algorithm, 0)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke(), trace(1)", "err DemandCycle", "", "0/0", "0/0"),  // nothing after the cycle runs
        new("Q1n", Q + "Use(x) = Apply(x.Algorithm, 0)\nR = if(aflag(), Capture(Take(Use(R.Arguments*))), 0)\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // async receiver
        new("Q1o", Q + "Use(x) = if(x.Algorithm(0) > 0, 1, 2)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),  // conditional builtin
        new("Q2", "Hold3(g) = if(Apply(g, 1) > 0, Capture(Inc(0)), Capture(Dec(0)))\nKeep(meta op) = op\nR = Keep(Hold3(R.Arguments*))\nR.Invoke()", "err DemandCycle", "", "0/0", "0/0"),
        new("Q2b", "Wrap(meta op) = op\nP(g) = Apply(g, 1)\nR = Wrap(P(R.Algorithm))\nR.Invoke()", "err NotAnAlgorithm", "", "0/0", "0/0"),
        new("Q3", Q + "Use(x) = Apply(x.Algorithm, 0)\nInner = Capture(Square(3))\nR = Capture(Take(Use(Inner)))\nR.Invoke()", "ok 0", "0", "0/0", "0/0"),
        new("Q3b", Q + "Use(x, y) = Apply(x.Algorithm, 4) + Apply(y.Algorithm, 5)\nInner = if(aflag(), Capture(Square(3)), 0)\nUse(Inner, Inner)", "ok 41", "4,5", "0/0", "0/0"),
        new("Q4", "Use(f) = Apply(f, 0)\nUse(5)", "err NotAnAlgorithm", "", "0/0", "0/0"),
        new("Q4b", "Use(f) = Apply(f, 0)\nUse(Inc(1))", "err NotAnAlgorithm", "", "0/0", "0/0"),
        new("E1", "Use(p) = Apply(p.G, 0)\nUse(5)", "err NotAnAlgorithm", "", "0/0", "0/0"),  // static: value receiver
        new("E1b", "Box = { G(x) = x * 10 }\nUse(p) = Apply(p.G, 0)\nUse(Box)", "ok 0", "", "0/0", "0/0"),  // static success
        new("E1c", "Use(p) = Apply(p.G, 0)\nUse(Inc(1))", "err NotAnAlgorithm", "", "0/0", "0/0"),  // static: computed receiver
        new("E2", "Bad = 5\nUse(p) = Apply(p.G, 0)\nUse(Bad.Algorithm)", "err TypeMismatch", "", "0/0", "0/0"),  // runtime TypeMismatch
        new("E2b", "Bad = 5\nUse(f) = Apply(f, 0)\nUse(Bad.Algorithm)", "err TypeMismatch", "", "0/0", "0/0"),  // control: direct parameter
        new("E3", "Bad = min([])\nUse(p) = Apply(p.G, 0)\nUse(Bad.Algorithm)", "err IllegalInEval", "", "0/0", "0/0"),  // runtime IllegalInEval
        new("E3b", "Bad = min([])\nUse(f) = Apply(f, 0)\nUse(Bad.Algorithm)", "err IllegalInEval", "", "0/0", "0/0"),  // control: direct parameter
        new("E3c", "Bad = min([])\nUse(p) = p.G(0)\nUse(Bad.Algorithm)", "err IllegalInEval", "", "0/0", "0/0"),  // member call route
        new("E3d", "Bad = min([])\nUse(p) = (p.G)(0)\nUse(Bad.Algorithm)", "err IllegalInEval", "", "0/0", "0/0"),  // grouped member callee
        new("E3e", "Bad = min([])\nUse(p) = p.G\nUse(Bad.Algorithm)", "err IllegalInEval", "", "0/0", "0/0"),  // bare VALUE
        new("E3f", "Bad = min([])\nUse(p) = Apply(p.Algorithm, 0)\nUse(Bad.Algorithm)", "err IllegalInEval", "", "0/0", "0/0"),  // `.Algorithm` of a parameter
        new("E4", "Q5(f) = f(1)\nBad = Q5(5)\nUse(p) = Apply(p.G, 0)\nUse(Bad.Algorithm)", "err NotAnAlgorithm", "", "0/0", "0/0"),  // runtime NotAnAlgorithm (wrapped)
        new("E4b", "Q5(f) = f(1)\nBad = Q5(5)\nUse(f) = Apply(f, 0)\nUse(Bad.Algorithm)", "err NotAnAlgorithm", "", "0/0", "0/0"),  // control
        new("E5", "Mk(k) = Capture(k(1))\nR0 = Mk(Bad.Algorithm)\nBad = min([])\nUse(p) = Apply(p.G, 0)\nUse(R0.Algorithm)", "err IllegalInEval", "", "0/0", "0/0"),  // transitive callee route
        new("E6", "Bad = min([])\nUse(p) = [1].map(p.G)\nUse(Bad.Algorithm)", "err IllegalInEval", "", "0/0", "0/0"),  // callback
        // loop step: M4★ normalizes the runtime-reference step to its target before planning, so the failing
        // projection precedes any plan build (formerly the planner refused the alias's own body: 0/1, OPT-FB-1).
        new("E7", "Bad = min([])\nUse(p) = {\n  A = p.G\n  A(0).while\n}\nUse(Bad.Algorithm)", "err IllegalInEval", "", "0/0", "0/0"),
        new("E8", "Bad = if(aflag(), min([]), 0)\nUse(p) = Apply(p.G, 0)\nUse(Bad.Algorithm)", "err IllegalInEval", "", "0/0", "0/0"),  // async receiver
        new("E9", "Bad = if(stop(), Capture(Square(5)), 0)\nUse(p) = Apply(p.G, 0)\nUse(Bad.Algorithm), trace(1)", "cancelled", "", "0/0", "0/0", WithCancel: true),
        new("E10", $"F(0) = Capture(Inc(0))\nF(n) = {{ open '{ModuleUrl}'\n Capture(Inc2(n)) }}\nR = F(1)\nUse(p) = Apply(p.G, 5)\nUse(R.Algorithm), trace(99)", "err LoadFetchFailed", "", "", "", AsyncOnly: true, Module: "<fail>"),
        new("E11s", "Deep(n) = if(n <= 0, Capture(Square(2)), Deep(n - 1))\nUse(p) = Apply(p.G, 0)\nUse(Deep(30).Algorithm)", "err NotAnAlgorithm", "", "0/0", "0/0", Limits: new EvaluationLimits { MaxSteps = 40 }),  // completes: static absence (Square declares no G)
        new("E11", "Deep(n) = if(n <= 0, Capture(Square(2)), Deep(n - 1))\nUse(p) = Apply(p.G, 0)\nUse(Deep(30).Algorithm), trace(1)", "err EvaluationStepLimitExceeded", "", "0/0", "0/0", Limits: new EvaluationLimits { MaxSteps = 10 }),  // receiver reaches the step limit
        new("E11b", "Deep(n) = if(n <= 0, Capture(Square(2)), Deep(n - 1))\nUse(f) = Apply(f, 0)\nUse(Deep(30).Algorithm), trace(1)", "err EvaluationStepLimitExceeded", "", "0/0", "0/0", Limits: new EvaluationLimits { MaxSteps = 10 }),
        new("Q5", "F(f) = f\nR = Capture(F(Q.Algorithm))\nQ = if(count([0].map(R.Arguments*)) > 0, Capture(Inc(0)), 0)\nApply(R.Arguments*, 1)", "err DemandCycle", "", "0/0", "0/0"),
        new("Q5b", "F(f) = f\nR = Capture(F(Q.Algorithm))\nQ = if(count([0].filter(R.Arguments*)) > 0, Capture(Inc(0)), 0)\nApply(R.Arguments*, 1)", "err DemandCycle", "", "0/0", "0/0"),
        new("Q5c", "F(f) = f\nR = Capture(F(Q.Algorithm))\nQ = if([1].reduce(R.Arguments*, 0) > 0, Capture(Inc(0)), 0)\nApply(R.Arguments*, 1)", "err DemandCycle", "", "0/0", "0/0"),
        new("Q5d", "F(f) = f\nW(s) = s(0).while\nR = Capture(F(Q.Algorithm))\nQ = if(W(R.Arguments*) > 0, Capture(Inc(0)), 0)\nApply(R.Arguments*, 1)", "err DemandCycle", "", "0/0", "0/0"),
        new("Q5e", "F(f) = f\nM(g) = [0].map(g)\nR = Capture(F(Q.Algorithm))\nQ = if(count(M(R.Arguments*)) > 0, Capture(Inc(0)), 0)\nApply(R.Arguments*, 1)", "err DemandCycle", "", "0/0", "0/0"),
        new("Q5f", "F(f) = f\nR = Capture(F(Q.Algorithm))\nQ = if(count([0].map(R.Arguments*)) > 0, Capture(Inc(0)), 0)\n[5].map(R.Arguments*)", "err DemandCycle", "", "0/0", "0/0"),
        new("Q5h", "F(f) = f\nW(s) = while(s(0))\nR = Capture(F(Q.Algorithm))\nQ = if(W(R.Arguments*) > 0, Capture(Inc(0)), 0)\nApply(R.Arguments*, 1)", "err DemandCycle", "", "0/0", "0/0"),  // call-form loop step
        new("Q5i", "F(f) = f\nW(s) = repeat(s(0), 2)\nR = Capture(F(Q.Algorithm))\nQ = if(W(R.Arguments*) > 0, Capture(Inc(0)), 0)\nApply(R.Arguments*, 1)", "err DemandCycle", "", "0/0", "0/0"),
        new("Q5g", "F(f) = f\nR = Capture(F(Q.Algorithm))\nQ = if(aflag(), if(count([0].map(R.Arguments*)) > 0, Capture(Inc(0)), 0), 0)\nApply(R.Arguments*, 1)", "err DemandCycle", "", "0/0", "0/0"),
        new("E12", "Bad = min([])\nUse(p) = Apply(p.G.H, 0)\nUse(Bad.Algorithm)", "err IllegalInEval", "", "0/0", "0/0"),  // deeper path
        new("E14", "Bad = min([])\nUse(p) = Apply(p.G, 0)\nUse(Bad.Algorithm), trace(1)", "err IllegalInEval", "", "0/0", "0/0"),
    ];

    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var c in Cases) data.Add(c.Id);
        return data;
    }

    private sealed record Observation(string Outcome, string Traces, long Steps, string Loops, string Fusion,
        string Diagnostic = "", int Admissions = 0, bool CompilationFailure = false);

    /// <summary>Host traces and asynchronous gates; execution counts use the native <c>tick()</c>.</summary>
    private sealed class Probe(Case c)
    {
        public readonly List<string> Traces = [];
        public readonly CancellationTokenSource? Cancel = c.WithCancel ? new CancellationTokenSource() : null;
        public int Admissions;

        public HostOperations Operations(bool asynchronous) => HostOperations.Create(
            HostOperation.Create("trace", (args, _) => { lock (Traces) Traces.Add(Format(args[0])); return args[0]; }, "x"),
            asynchronous
                ? HostOperation.CreateAsync("aflag", async (_, _) => { await Task.Yield(); return new Result.Bool(true); })
                : HostOperation.Create("aflag", (_, _) => new Result.Bool(true)),
            asynchronous
                ? HostOperation.CreateAsync("atrace", async (args, _) => { await Task.Yield(); lock (Traces) Traces.Add("a" + Format(args[0])); return args[0]; }, "x")
                : HostOperation.Create("atrace", (args, _) => { lock (Traces) Traces.Add("a" + Format(args[0])); return args[0]; }, "x"),
            asynchronous
                ? HostOperation.CreateAsync("stop", async (_, _) => { await Task.Yield(); Cancel?.Cancel(); return new Result.Bool(true); })
                : HostOperation.Create("stop", (_, _) => { Cancel?.Cancel(); return new Result.Bool(true); }));

        public RunOptions Options(HostOperations operations) => c.Module is null
            ? new RunOptions { HostOperations = operations }
            : new RunOptions
            {
                HostOperations = operations,
                AllowedHosts = ["modules.example"],
                DownloadCode = async (_, token) =>
                {
                    Interlocked.Increment(ref Admissions);
                    await Task.Yield();
                    token.ThrowIfCancellationRequested();
                    if (c.Module == "<fail>") throw new InvalidOperationException("download refused by the test loader");
                    if (c.Module == "<cancel>") { Cancel?.Cancel(); token.ThrowIfCancellationRequested(); }
                    if (c.Module == "<syntax>") return "public Inc2(x) = x +";
                    return c.Module;
                },
            };

        public string TraceText => string.Join(",", Traces);
    }

    private static string Format(Result value) => value switch
    {
        Result.Atom a => a.Value.ToString(),
        Result.Str s => "'" + s.Value + "'",
        Result.Bool b => b.Value ? "true" : "false",
        Result.SequenceValue q => "(" + string.Join(", ", q.Items.Select(Format)) + ")",
        Result.ListValue l => "[" + string.Join(", ", l.Items.Select(Format)) + "]",
        _ => value.ToString(),
    };

    private static string Outcome(EvalResult<Evaluator.CountedResult> result)
        => result.IsOk ? "ok " + Format(result.Value.Value) : "err " + result.Error.Code;

    private static string Diagnostic(EvalResult<Evaluator.CountedResult> result)
        => result.IsOk ? "" : $"{KatLangError.FromEvalError(result.Error).Message} @{result.Error.Span}";

    private static bool IsCompilationFailure(EvalResult<Evaluator.CountedResult> result)
    {
        if (result.IsOk) return false;
        var error = result.Error;
        while (error is EvalError.WithContext context) error = context.Inner;
        return error is EvalError.ModuleRegionMaterializationFailed;
    }

    private static Observation Sync(Case c, bool optimized, EvaluationLimits? limits)
    {
        var probe = new Probe(c);
        var operations = probe.Operations(asynchronous: false);
        var parsed = Parser.Parse(Lib + c.Source, probe.Options(operations));
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
        var loops = new LoopOptimizationDiagnostics();
        var sequences = new SequencePipelineDiagnostics();
        try
        {
            var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), limits,
                enableOptimizations: optimized, loopDiagnostics: loops, sequenceDiagnostics: sequences,
                hostOperations: operations, cancellationToken: probe.Cancel?.Token ?? default);
            return new(Outcome(result), probe.TraceText, budget.ConsumedSteps,
                $"{loops.OptimizedLoopHits}/{loops.OptimizedLoopFallbacks}",
                $"{sequences.FilterCountFusionHits}/{sequences.DirectRangeFusionHits}", Diagnostic(result), probe.Admissions,
                IsCompilationFailure(result));
        }
        catch (OperationCanceledException cancelled) when (probe.Cancel is { } source)
        {
            Assert.Equal(source.Token, cancelled.CancellationToken);
            return new("cancelled", probe.TraceText, 0, "", "", Admissions: probe.Admissions);
        }
    }

    private static async Task<Observation> Async(Case c, EvaluationLimits? limits)
    {
        var probe = new Probe(c);
        var operations = probe.Operations(asynchronous: true);
        try
        {
            var options = probe.Options(operations);
            var parsed = c.Module is null ? Parser.Parse(Lib + c.Source, options) : await Parser.ParseAsync(Lib + c.Source, options);
            Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
            var (result, budget) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), limits,
                hostOperations: operations, cancellationToken: probe.Cancel?.Token ?? default);
            return new(Outcome(result), probe.TraceText, budget.ConsumedSteps, "", "", Diagnostic(result), probe.Admissions,
                IsCompilationFailure(result));
        }
        catch (OperationCanceledException cancelled) when (probe.Cancel is { } source)
        {
            Assert.Equal(source.Token, cancelled.CancellationToken);
            return new("cancelled", probe.TraceText, 0, "", "", Admissions: probe.Admissions);
        }
    }

    private static Task<Observation> Bounded(Func<Task<Observation>> run) => Task.Run(run).WaitAsync(WaitLimit);

    private const string HostStackBackstop = "err EvaluationStackExhausted";

    private static void Check(Case c, string mode, Observation observed)
    {
        // Q-09a: where host-stack headroom decides, the backstop may end a run before its recorded
        // outcome — before the depth limit of an unbounded recursion (C3b), or before a long chain that
        // holds no evaluation depth completes (C8b: a 1.5 MiB Windows thread-pool stack stops it, while
        // the 8 MiB Linux default, or a larger stack glibc reuses, lets it finish). It is the only other
        // permitted outcome — never a hang, a host fault or another error — and nothing runs after it,
        // so the effects before it are a prefix of the recorded ones.
        if (c.HeadroomSensitive && observed.Outcome == HostStackBackstop)
        {
            Assert.True(IsTracePrefix(observed.Traces, c.Traces),
                $"{c.Id} {mode}: traces [{observed.Traces}] before the host-stack backstop, recorded [{c.Traces}]");
            return;
        }

        Assert.True(c.Expected == observed.Outcome, $"{c.Id} {mode}: {observed.Outcome}, expected {c.Expected}"
            + (c.HeadroomSensitive ? " or " + HostStackBackstop : ""));
        Assert.True(c.Traces == observed.Traces, $"{c.Id} {mode}: traces [{observed.Traces}], expected [{c.Traces}]");
        Assert.Equal(c.Module is null ? 0 : c.ExpectedAdmissions, observed.Admissions);
    }

    private static bool IsTracePrefix(string traces, string recorded)
    {
        if (traces.Length == 0) return true;
        var items = traces.Split(',');
        var all = recorded.Split(',');
        return items.Length <= all.Length && items.SequenceEqual(all.Take(items.Length));
    }

    [Theory]
    [MemberData(nameof(CaseIds))]
    public async Task Corpus_AgreesOnEveryEngine(string id)
    {
        var c = Cases.Single(x => x.Id == id);
        var asynchronous = await Bounded(() => Async(c, c.Limits));
        Check(c, "async", asynchronous);
        if (c.AsyncOnly)
            return;

        var generic = await Bounded(() => Task.FromResult(Sync(c, optimized: false, c.Limits)));
        var optimized = await Bounded(() => Task.FromResult(Sync(c, optimized: true, c.Limits)));
        Check(c, "generic", generic);
        Check(c, "optimized", optimized);
        if (c.HeadroomSensitive || c.Expected == "cancelled")
            return;
        Assert.True(c.Loops == optimized.Loops, $"{c.Id}: optimized loops {optimized.Loops}, expected {c.Loops}");
        Assert.True(c.Fusion == optimized.Fusion, $"{c.Id}: optimized fusion {optimized.Fusion}, expected {c.Fusion}");
        Assert.True(generic.Steps == optimized.Steps, $"{c.Id}: optimized {optimized.Steps} steps, generic {generic.Steps}");
        Assert.True(generic.Steps == asynchronous.Steps, $"{c.Id}: async {asynchronous.Steps} steps, generic {generic.Steps}");
        Assert.True(generic.Diagnostic == optimized.Diagnostic,
            $"{c.Id}: optimized {optimized.Diagnostic} vs generic {generic.Diagnostic}");
        Assert.True(generic.Diagnostic == asynchronous.Diagnostic,
            $"{c.Id}: async {asynchronous.Diagnostic} vs generic {generic.Diagnostic}");
    }

    /// <summary>
    /// Bounded MaxSteps scans (R2 §I): at every limit from 1 to 25 the three modes reach the same outcome
    /// after the same number of steps with the same effects — no optimizer moves a runtime projection
    /// into speculative recognition, and no async resolution charges, repeats or skips a step.
    /// </summary>
    [Theory]
    [InlineData("Q1")]
    [InlineData("Q3b")]
    [InlineData("Q5")]
    [InlineData("E3")]
    [InlineData("E4")]
    [InlineData("E11b")]
    [InlineData("AS2")]
    [InlineData("LP4")]
    [InlineData("C7c")]
    [InlineData("VC5")]
    [InlineData("LP3")]
    public async Task StepLimitScans_AgreeAcrossModes(string id)
    {
        var c = Cases.Single(x => x.Id == id);
        for (var limit = 1; limit <= 25; limit++)
        {
            var limits = new EvaluationLimits { MaxSteps = limit };
            var generic = await Bounded(() => Task.FromResult(Sync(c, optimized: false, limits)));
            var optimized = await Bounded(() => Task.FromResult(Sync(c, optimized: true, limits)));
            var asynchronous = await Bounded(() => Async(c, limits));
            foreach (var (mode, observed) in new[] { ("optimized", optimized), ("async", asynchronous) })
            {
                Assert.True(generic.Outcome == observed.Outcome, $"{id} MaxSteps={limit} {mode}: {observed.Outcome} vs generic {generic.Outcome}");
                Assert.True(generic.Steps == observed.Steps, $"{id} MaxSteps={limit} {mode}: {observed.Steps} vs generic {generic.Steps} steps");
                Assert.True(generic.Traces == observed.Traces, $"{id} MaxSteps={limit} {mode}: [{observed.Traces}] vs generic [{generic.Traces}]");
                Assert.True(generic.Diagnostic == observed.Diagnostic,
                    $"{id} MaxSteps={limit} {mode}: {observed.Diagnostic} vs generic {generic.Diagnostic}");
            }
        }
    }

    private const string DeferredSource =
        "F(0) = Capture(Inc(0))\nF(n) = { open '" + ModuleUrl + "'\n Capture(Inc2(n)) }\nR = F(1)\nApply(R.Algorithm, 5), trace(99)";

    /// <summary>
    /// Deferred source admission on the callee route (Q-71): a required module that fails to COMPILE ends the
    /// run with its compilation failure before anything after it runs, exactly as a failed acquisition does.
    /// </summary>
    [Fact]
    public async Task ARequiredModuleThatFailsToCompile_EndsTheRun()
    {
        var observed = await Bounded(() => Async(new Case("DM-syntax", DeferredSource, "", "", "", "", AsyncOnly: true, Module: "<syntax>"), null));
        Assert.True(observed.CompilationFailure, observed.Diagnostic);
        Assert.Equal(1, observed.Admissions);
        Assert.Equal("", observed.Traces);
    }

    /// <summary>A failed acquisition belongs to its run: a fresh run with a working loader admits the module.</summary>
    [Fact]
    public async Task AFailedAcquisition_IsNotStickyAcrossFreshRuns()
    {
        var failed = await Bounded(() => Async(new Case("DM-fail", DeferredSource, "", "", "", "", AsyncOnly: true, Module: "<fail>"), null));
        Assert.Equal("err LoadFetchFailed", failed.Outcome);
        Assert.Equal(1, failed.Admissions);
        var fresh = await Bounded(() => Async(new Case("DM-fresh", DeferredSource, "", "", "", "", AsyncOnly: true, Module: ModuleText), null));
        Assert.Equal("ok (7, 99)", fresh.Outcome);
        Assert.Equal("99", fresh.Traces);
        Assert.Equal(1, fresh.Admissions);
    }

    /// <summary>The research fixtures that are deliberately invalid syntax stay parse errors, not runtime cases.</summary>
    [Theory]
    [InlineData(Q + "Use(x) = 9.(x.Algorithm)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()")]
    [InlineData("Bad = min([])\nUse(p) = 3.p.G\nUse(Bad.Algorithm)")]
    [InlineData("R = if(aflag(), Capture(Square(5)), 0)\nBox = { A = R.Algorithm }\n9.(Box.A)")]
    [InlineData("R = Capture(Square(5))\nA() = R.Algorithm\nA(9)")]
    public void FrontEndProbes_AreParseErrors(string source)
    {
        var probe = new Probe(new Case("probe", source, "", "", "", ""));
        Assert.True(Parser.Parse(Lib + source, probe.Options(probe.Operations(asynchronous: false))).HasErrors);
    }
}
