using System.Diagnostics;
using KatLang.Evaluation;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// META-S3-2: RUNTIME-TARGET CALLABLE ALIASES (FWD-02; owner decisions D1 = yes, D2 = Option A with Q-75
/// unchanged, D3 = fresh invocation). The META-S3-2-R research corpus — its 120 original cases
/// (<c>Q*</c> Q-75 situations, <c>A*</c> direct parameter aliases, <c>B*</c> <c>.Algorithm</c> aliases,
/// <c>C*</c> parameter-rooted member aliases, <c>D*</c> chains, <c>E*</c> callable consumers, <c>F*</c>
/// compatibility, <c>G*</c> runtime control) and its 29 independent-review cases (<c>V*</c>) — plus the
/// implementation stage's own scenarios (<c>X*</c>: receiver sharing in both channel orders, inline
/// aliases, a structure whose row is a parameter staying a namespace, forward ten-link and structural
/// chains, distinct declaring activations, loops, callbacks, families, capture, cancellation, async
/// receivers, failures, terminal properties and optimizer recognition), promoted to permanent source-level
/// regressions. Common cases run on the synchronous generic evaluator, the synchronous optimized evaluator
/// and the asynchronous engine (the two module cases run on the async engine; <c>aflag</c>, <c>atrace</c> and <c>stop</c> are genuinely
/// asynchronous); each mode must give the recorded outcome, rendered diagnostic (message and span), host
/// effects and source admissions, all modes the same semantic step count, and the optimized mode the
/// recorded loop and fusion counters. Research expectations were checked against the Option A predictions;
/// the X10 regressions pin the owner-approved ordinary-property preservation contract, including the
/// incorrect receiver repetition. <see cref="Case.Was"/> records the
/// pre-S3-2 (accepted S3-1) outcome wherever it changed — the D1/D2/D3 compatibility changes
/// (<c>A04</c>/<c>C08</c>/<c>F08</c>/<c>V10</c> freshness, <c>F07</c>/<c>F07r</c>/<c>V24</c> navigation
/// through a passed alias), the newly demanded runtime outcomes (<c>B08</c>, <c>G02</c>–<c>G06</c>,
/// <c>V09</c>, <c>V20</c>) and every previously failing program that now succeeds — while every other case
/// is a preserved CURRENT oracle (the Q-75 F01–F06 inference programs among them).
/// </summary>
public class RuntimeCallableAliasCorpusTests
{
    /// <summary>The research harness's prelude (META-S3-2-R §N).</summary>
    private const string Lib = """
        Square(x) = trace(x) * x
        Inc(x) = x + 1
        Capture(meta operation) = operation
        Apply(f, x) = f(x)

        """;

    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    public sealed record Case(string Id, string Source, string Expected, string Traces,
        int Ticks = 0, string Diagnostic = "", string Loops = "0/0", string Fusion = "0/0",
        string? Module = null, int Downloads = 0, bool WithCancel = false, int? MaxSteps = null, string? Was = null, long? Steps = null, int? Emitted = null);

    private static readonly Case[] Cases =
    [
        new("Q01-known-member", "Box = { G(x) = x * 10 }\nA = Box.G\nA(3)", "ok 30", ""),
        new("Q01b-known-miss-lexical", "G(o) = 7\nBox = { K = 1 }\nA = Box.G\nA, A(3)", "err ArityMismatch", "", Diagnostic: "Callable `A` expects 0 arguments, but was called with 1 argument. @[8:4, 8:8)"),
        new("Q01c-known-miss-unresolved", "Thousand(v) = v * 1000\nBox = { K = 1\n 5 }\nA = Box.G\nA(Thousand)", "ok 5000", ""),
        new("Q02-param-miss-unresolved", "Thousand(v) = v * 1000\nUse(b) = {\n  A = b.G\n  A(Thousand)\n}\nUse(5)", "ok 5000", ""),
        new("Q03-param-hit-unresolved", "Box = { G(x) = x * 10 }\nUse(b) = {\n  A = b.G\n  A(3)\n}\nUse(Box)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: while evaluating call to A: Property 'G' on `b` expects 1 parameter, but was called with 0 arguments. @[7:7, 7:10)"),
        new("Q03b-param-hit-value-member", "Box = { G = 42 }\nUse(b) = {\n  A = b.G\n  A(3)\n}\nUse(Box)", "ok 42", ""),
        new("Q04-runtime-selected", "G(o) = o + 100\nBox = { G(x) = x * 10 }\nUse(b) = {\n  A = b.G\n  A\n}\nUse(Box), Use(5)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Property 'G' on `b` expects 1 parameter, but was called with 0 arguments. @[8:7, 8:10)"),
        new("Q05-param-miss-lexical", "G(o) = o + 100\nUse(b) = {\n  A = b.G\n  A, A(3)\n}\nUse(5)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Callable `A` expects 0 arguments, but was called with 1 argument. @[8:6, 8:10)"),
        new("Q05b-param-hit-lexical", "G(o) = o + 100\nBox = { G(x) = x * 10 }\nUse(b) = {\n  A = b.G\n  A(3)\n}\nUse(Box)", "ok 30", "", Was: "err ArityMismatch"),
        new("Q07-enclosing-explicit-G", "Use(b, G) = {\n  A = b.G\n  A\n}\nUse(5, Inc)", "ok 6", ""),
        new("Q07b-enclosing-inferred-G", "Mk(b) = {\n  Outer = {\n    A = b.G\n    A, G(0)\n  }\n  Outer(Inc)\n}\nMk(5)", "ok (6, 1)", ""),
        new("Q08-closed-may-unresolved-miss", "Use(b) = b.G\nUse(5)", "err UnknownName", "", Diagnostic: "while evaluating call to Use: Property 'G' was not found on `b`, and no visible algorithm or property named 'G' can be used with `b` as the first argument. @[5:10, 5:13)"),
        new("Q08b-closed-may-unresolved-hit", "Box = { G(x) = x * 10 }\nUse(b) = b.G(4)\nUse(Box)", "ok 40", ""),
        new("Q08c-closed-nested-alias-shape", "Thousand(v) = v * 1000\nUse(b) = {\n  A(p) = b.G\n  A(1)\n}\nUse(5)", "err UnknownName", "", Diagnostic: "while evaluating call to Use: while evaluating call to A: Property 'G' was not found on `b`, and no visible algorithm or property named 'G' can be used with `b` as the first argument. @[7:10, 7:13)"),
        new("Q09-multi-row", "Thousand(v) = v * 1000\nUse(b) = {\n  A = b.G, 1\n  A(Thousand)\n}\nUse(5)", "ok (5000, 1)", ""),
        new("Q10-two-edges-unresolved", "Thousand(v) = v * 1000\nUse(b) = {\n  A = b.H.G\n  A(Thousand, Thousand)\n}\nUse(5)", "ok 5000000", ""),
        new("Q10b-two-edges-hit", "Outer = { H = { G(x) = x * 10 } }\nUse(b) = {\n  A = b.H.G\n  A(3)\n}\nUse(Outer)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Callable `A(H, G)` expects 2 arguments, but was called with 1 argument. @[8:3, 8:7)"),
        new("Q10c-two-edges-lexical", "G(o) = 1\nH(o) = 2\nOuter = { H = { G(x) = x * 10 } }\nUse(b) = {\n  A = b.H.G\n  A, A(3)\n}\nUse(Outer)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Property 'G' on `b.H` expects 1 parameter, but was called with 0 arguments. @[9:7, 9:12)"),
        new("Q11-root-open-must", "Get = 5.size\nGet(count)", "ok 1", ""),
        new("A01-callable", "Use(f) = {\n  A = f\n  A(9)\n}\nUse(Square)", "ok 81", "9", Was: "err ArityMismatch"),
        new("A02-value-only", "Use(f) = {\n  A = f\n  A, A(9)\n}\nUse(5)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Callable `A` expects 0 arguments, but was called with 1 argument. @[7:6, 7:10)"),
        new("A02b-value-only-bare", "Use(f) = {\n  A = f\n  A + 1\n}\nUse(5)", "ok 6", ""),
        new("A03-zero-param-property", "Z = tick()\nUse(f) = {\n  A = f\n  A, A, Z\n}\nUse(Z)", "ok (1, 1, 1)", "", Ticks: 1),
        new("A03b-zero-param-property-call", "Z = tick()\nUse(f) = {\n  A = f\n  A(9)\n}\nUse(Z)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Callable `A` expects 0 arguments, but was called with 1 argument. @[8:3, 8:7)"),
        new("A04-collecting-F10", "Only(*xs) = tick()\nUse(f) = {\n  A = f\n  A, A(), A()\n}\nUse(Only)", "ok (1, 2, 3)", "", Ticks: 3, Was: "ok (1, 1, 1) ticks 1"),
        new("A04b-collecting-static-oracle", "Only(*xs) = tick()\nA = Only\nA, A(), A()", "ok (1, 2, 3)", "", Ticks: 3),
        new("A05-family", "Describe(0) = 'zero'\nDescribe(n) = 'other'\nUse(f) = {\n  A = f\n  A(0), A(5)\n}\nUse(Describe)", "ok ('zero', 'other')", "", Was: "err ArityMismatch"),
        new("A06-bare-callable", "Use(f) = {\n  A = f\n  A\n}\nUse(Square)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Property 'Square' expects 1 parameter, but was called with 0 arguments. @[9:5, 9:11)"),
        new("A07-inferred-not-alias", "Use = {\n  A = f\n  A(9)\n}\nUse", "ok 9", ""),
        new("A08-static-oracle", "Use(f) = f(9)\nA = Square\nUse(Square), A(9)", "ok (81, 81)", "9,9"),
        new("B01-call", "R = Capture(Square(5))\nA = R.Algorithm\nA(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("B02-bare", "R = Capture(Square(5))\nA = R.Algorithm\nA", "err ArityMismatch", "", Diagnostic: "while evaluating dotCall .Algorithm of R: Property 'Square' expects 1 parameter, but was called with 0 arguments. @[5:13, 5:19)"),
        new("B03-direct-control", "R = Capture(Square(5))\nR.Algorithm(9), R.Invoke()", "ok (81, 25)", "9,5"),
        new("B04-callback", "R = Capture(Square(5))\nA = R.Algorithm\n[1, 2].map(A)", "ok [1, 4]", "1,2", Was: "err ArityMismatch"),
        new("B05-family", "Describe(0) = 'zero'\nDescribe(n) = 'other'\nR = Capture(Describe(0))\nA = R.Algorithm\nA(5)", "ok 'other'", "", Was: "err ArityMismatch"),
        new("B05b-family-direct", "Describe(0) = 'zero'\nDescribe(n) = 'other'\nR = Capture(Describe(0))\n[0, 1].map(R.Algorithm), R.Algorithm(5)", "ok (['zero', 'other'], 'other')", ""),
        new("B06-invocation-independence", "R = Capture(Square(5))\nA = R.Algorithm\nR.Invoke(), A, R.Invoke()", "err ArityMismatch", "5", Diagnostic: "while evaluating dotCall .Algorithm of R: Property 'Square' expects 1 parameter, but was called with 0 arguments. @[5:13, 5:19)"),
        new("B07-absent-callee", "Mk(g) = Capture(g(1))\nR = Mk(5)\nA = R.Algorithm\nA(9)", "err ArityMismatch", "", Diagnostic: "Callable `A` expects 0 arguments, but was called with 1 argument. @[8:1, 8:5)"),
        new("B07b-absent-callee-direct", "Mk(g) = Capture(g(1))\nR = Mk(5)\nR.Algorithm(9)", "err NotAnAlgorithm", "", Diagnostic: "while evaluating dotCall .Algorithm of R: Not an algorithm: captured callee @[7:1, 7:15)"),
        new("B08-non-reference", "R = 5\nA = R.Algorithm\nA(9)", "err TypeMismatch", "", Diagnostic: "while evaluating call to A: Type mismatch: `Algorithm` requires a call reference, got numeric value 5 @[7:1, 7:2)", Was: "err ArityMismatch"),
        new("B08b-non-reference-bare", "R = 5\nA = R.Algorithm\nA", "err TypeMismatch", "", Diagnostic: "while evaluating dotCall .Algorithm of R: Type mismatch: `Algorithm` requires a call reference, got numeric value 5 @[6:5, 6:16)"),
        new("B10-computed-receiver", "Only(*xs) = tick()\nMk(n) = if(trace(n) > 0, Capture(Only(n)), 0)\nA = Mk(5).Algorithm\nA, A", "ok (1, 1)", "5", Ticks: 1),
        new("B10b-computed-receiver-supplied", "Only(*xs) = tick()\nMk(n) = if(trace(n) > 0, Capture(Only(n)), 0)\nUse(f) = f, f(), Apply(f, 1)\nUse(Mk(5).Algorithm)", "ok (1, 2, 3)", "5", Ticks: 3),
        new("B09-param-rooted-algorithm", "Use(r) = {\n  A = r.Algorithm\n  A(9)\n}\nUse(Capture(Square(5)))", "ok 81", "9", Was: "err ArityMismatch"),
        new("C01-declared-member-lexical", "G(o) = o + 100\nBox = { G(x) = x * 10 }\nUse(b) = {\n  A = b.G\n  A, A(3)\n}\nUse(Box)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Property 'G' on `b` expects 1 parameter, but was called with 0 arguments. @[8:7, 8:10)"),
        new("C02-runtime-selected-lexical", "G(o) = o + 100\nBox = { G(x) = x * 10 }\nUse(b) = {\n  A = b.G\n  A(3)\n}\nUse(Box), Use(5)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Callable `A` expects 0 arguments, but was called with 1 argument. @[9:3, 9:7)"),
        new("C03-fallback-lexical", "G(o) = o + 100\nUse(b) = {\n  A = b.G\n  A, A(3)\n}\nUse(5)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Callable `A` expects 0 arguments, but was called with 1 argument. @[8:6, 8:10)"),
        new("C04-unresolved-may", "Thousand(v) = v * 1000\nBox = { G(x) = x * 10 }\nUse(b) = {\n  A = b.G\n  A(Thousand)\n}\nUse(5), Use(Box)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: while evaluating call to A: Property 'G' on `b` expects 1 parameter, but was called with 0 arguments. @[8:7, 8:10)"),
        new("C05-existing-implicit-G", "Box = { G(x) = x * 10 }\nUse(b, G) = {\n  A = b.G\n  A, A(3)\n}\nUse(Box, Inc), Use(5, Inc)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Property 'G' on `b` expects 1 parameter, but was called with 0 arguments. @[7:7, 7:10)"),
        new("C06-shadowed-G", "G(o) = o + 100\nUse(b) = {\n  G(o) = o + 200\n  A = b.G\n  A\n}\nUse(5)", "ok 205", ""),
        new("C06b-shadow-at-consumer", "G(o) = o + 100\nUse(b) = {\n  A = b.G\n  Box2 = { G(o) = o + 300\n  K = A }\n  Box2.K\n}\nUse(5)", "ok 105", ""),
        new("C07-missing-runtime-member", "G(o) = 7\nNoG = { K = 1\n 5 }\nUse(b) = {\n  A = b.G\n  A, A(3)\n}\nUse(NoG)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Callable `A` expects 0 arguments, but was called with 1 argument. @[10:6, 10:10)"),
        new("C08-value-vs-callable", "G(o) = o\nBox = { G(*xs) = tick() }\nUse(b) = {\n  A = b.G\n  A, A(), A()\n}\nUse(Box)", "ok (1, 2, 3)", "", Ticks: 3, Was: "ok (1, 1, 1) ticks 1"),
        new("C08b-static-oracle", "Box = { G(*xs) = tick() }\nA = Box.G\nA, A(), A()", "ok (1, 2, 3)", "", Ticks: 3),
        new("C09-effects", "G(o) = o\nBox = { G(x) = trace(x) * 10 }\nUse(b) = {\n  A = b.G\n  A(3), A(4)\n}\nUse(Box)", "ok (30, 40)", "3,4", Was: "err ArityMismatch"),
        new("C09b-receiver-failure", "G(o) = o + 1\nUse(b) = {\n  A = b.G\n  A, A(3)\n}\nUse(1 / 0)", "err DivisionByZero", "", Diagnostic: "while evaluating call to Use: while evaluating dotCall .G of b: Division by zero @[10:5, 10:10)"),
        new("C10-supplied-path-control", "Box = { G(x) = x * 10 }\nUse(b) = Apply(b.G, 3)\nUse(Box)", "ok 30", ""),
        new("C10b-callee-path-control", "Box = { G(x) = x * 10 }\nUse(b) = b.G(3), (b.G)(3)\nUse(Box)", "ok (30, 30)", ""),
        new("C11-supplied-miss", "G(o) = o + 100\nUse(b) = Apply(b.G, 3)\nUse(5)", "err NotAnAlgorithm", "", Diagnostic: "while evaluating call to Use: while evaluating call to Apply: while evaluating call to f: Parameter 'f' is not callable here: it is bound to a value, not to an algorithm. Pass an algorithm for 'f', or read it as a value. @[4:15, 4:16)"),
        new("C11b-callee-miss", "G(o) = o + 100\nUse(b) = (b.G)(3)\nUse(5)", "err NotAnAlgorithm", "", Diagnostic: "while evaluating call to Use: `b.G` is a computed value, not a callable: a dot expression can be called only when it names a member that its receiver declares (such as `Lib.F`); otherwise it evaluates to a value. @[6:10, 6:15)"),
        new("C11c-call-miss", "G(o, k) = o + k\nUse(b) = b.G(3)\nUse(5)", "ok 8", ""),
        new("C12-static-must-oracle", "G(o, k) = o + k\nBox = { K = 1\n 5 }\nA = Box.G\nBox.G(3), (Box.G)(3)", "err NotAnAlgorithm", "", Diagnostic: "`Box.G` is a computed value, not a callable: a dot expression can be called only when it names a member that its receiver declares (such as `Lib.F`); otherwise it evaluates to a value. @[9:11, 9:18)"),
        new("C12b-static-must-alias-call", "G(o, k) = o + k\nBox = { K = 1\n 5 }\nA = Box.G\nA(3)", "err ArityMismatch", "", Diagnostic: "Callable `A` expects 0 arguments, but was called with 1 argument. @[9:1, 9:5)"),
        new("C13-member-is-static-alias", "G(o) = o\nBox = { G = Square }\nUse(b) = {\n  A = b.G\n  A(3)\n}\nUse(Box)", "ok 9", "3", Was: "err ArityMismatch"),
        new("C14-family-zero-call", "Fam(0) = 1\nFam(n) = 2\nUse(f) = {\n  A = f\n  A()\n}\nUse(Fam)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Property 'A' expects 1 parameter, but was called with 0 arguments. @[9:3, 9:6)", Was: "err NoMatchingBranch"),
        new("C14s-family-zero-call-static", "Fam(0) = 1\nFam(n) = 2\nA = Fam\nA()", "err ArityMismatch", "", Diagnostic: "Property 'A' expects 1 parameter, but was called with 0 arguments. @[8:1, 8:4)"),
        new("C15-fixed-zero-call", "Use(f) = {\n  A = f\n  A()\n}\nUse(Square)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Callable `A(x)` expects 1 argument, but was called with 0 arguments. @[7:3, 7:6)"),
        new("C15s-fixed-zero-call-static", "A = Square\nA()", "err ArityMismatch", "", Diagnostic: "Callable `A(x)` expects 1 argument, but was called with 0 arguments. @[6:1, 6:4)"),
        new("D01-runtime-chain-3", "R = Capture(Square(5))\nA = R.Algorithm\nB = A\nC = B\nC(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("D02-static-chain-10", "S1 = Square\nS2 = S1\nS3 = S2\nS4 = S3\nS5 = S4\nS6 = S5\nS7 = S6\nS8 = S7\nS9 = S8\nS10 = S9\nS10(9), S2(9)", "ok (81, 81)", "9,9"),
        new("D03-runtime-chain-10", "R = Capture(Square(5))\nS1 = R.Algorithm\nS2 = S1\nS3 = S2\nS4 = S3\nS5 = S4\nS6 = S5\nS7 = S6\nS8 = S7\nS9 = S8\nS10 = S9\nS10(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("D04-in-structure", "R = Capture(Square(5))\nBox = { A = R.Algorithm }\nBox.A(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("D05-member-of-member", "R = Capture(Square(5))\nA = R.Algorithm\nBox = { B = A }\nBox.B(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("D06-different-owners", "Use(f) = {\n  A = f\n  Box = { B = A }\n  Box.B(9)\n}\nUse(Square)", "ok 81", "9", Was: "err ArityMismatch"),
        new("D07-static-in-structure-oracle", "Box = { Sq = Square }\nBox.Sq(9), (Box.Sq)(9), Apply(Box.Sq, 9)", "ok (81, 81, 81)", "9,9,9"),
        new("E01-direct", "R = Capture(Square(5))\nA = R.Algorithm\nA(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("E02-grouped", "R = Capture(Square(5))\nA = R.Algorithm\n(A)(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("E03-structural", "R = Capture(Square(5))\nBox = { A = R.Algorithm }\nBox.A(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("E04-grouped-structural", "R = Capture(Square(5))\nBox = { A = R.Algorithm }\n(Box.A)(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("E05-lexical-dot", "R = Capture(Square(5))\nA = R.Algorithm\n9.A", "ok 81", "9", Was: "err ArityMismatch"),
        new("E05b-lexical-dot-param", "Use(f) = {\n  A = f\n  9.A\n}\nUse(Square)", "ok 81", "9", Was: "err ArityMismatch"),
        new("E06-higher-order", "R = Capture(Square(5))\nA = R.Algorithm\nApply(A, 9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("E06b-forward-twice", "Fwd(f, x) = Apply(f, x)\nUse(f) = {\n  A = f\n  Fwd(A, 9)\n}\nUse(Square)", "ok 81", "9", Was: "err ArityMismatch"),
        new("E07-map-filter-reduce", "IsBig(x) = x > 1\nAdd(a, b) = a + b\nRm = Capture(Square(5))\nRf = Capture(IsBig(5))\nRr = Capture(Add(1, 2))\nM = Rm.Algorithm\nF = Rf.Algorithm\nD = Rr.Algorithm\n[1, 2].map(M), [1, 2, 3].filter(F), [1, 2, 3].reduce(D, 0)", "ok ([1, 4], [2, 3], 6)", "1,2", Was: "err ArityMismatch"),
        new("E07s-static-oracle", "IsBig(x) = x > 1\nAdd(a, b) = a + b\nM = Square\nF = IsBig\nD = Add\n[1, 2].map(M), [1, 2, 3].filter(F), [1, 2, 3].reduce(D, 0)", "ok ([1, 4], [2, 3], 6)", "1,2"),
        new("E08-family-redispatch", "Describe(0) = 'zero'\nDescribe(n) = 'other'\nUse(f) = {\n  A = f\n  [0, 1].map(A)\n}\nUse(Describe)", "ok ['zero', 'other']", "", Was: "err ArityMismatch"),
        new("E09-while", "Step(x) = x + 1, x < 3\nR = Capture(Step(0))\nA = R.Algorithm\nA(0).while", "ok 3", "", Loops: "1/0", Was: "err ArityMismatch"),
        new("E09b-repeat", "Step(x) = x + 1\nR = Capture(Step(0))\nA = R.Algorithm\nA(0).repeat(4)", "ok 4", "", Loops: "1/0", Was: "err ArityMismatch"),
        new("E09s-static-oracle", "Step(x) = x + 1, x < 3\nA = Step\nA(0).while", "ok 3", "", Loops: "1/0"),
        new("E10-capture-alias-call", "R = Capture(Square(5))\nA = R.Algorithm\nR2 = Capture(A(4))\nR2.Invoke(), R2.Algorithm(5)", "ok (16, 25)", "4,5", Was: "err ArityMismatch"),
        new("E10s-static-oracle", "A = Square\nR2 = Capture(A(4))\nR2.Invoke(), R2.Algorithm(5)", "ok (16, 25)", "4,5"),
        new("E11-bare-forwarding", "Use(f) = {\n  A = f\n  W(x) = A\n  W(4)\n}\nUse(Square)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: while evaluating call to W: Property 'Square' expects 1 parameter, but was called with 0 arguments. @[10:5, 10:11)"),
        new("E12-formula", "R = Capture(Square(5))\nA = R.Algorithm\nB = A + 1\nB", "err ArityMismatch", "", Diagnostic: "while evaluating dotCall .Algorithm of R: Property 'Square' expects 1 parameter, but was called with 0 arguments. @[5:13, 5:19)"),
        new("F01-extension-param", "Thousand(v) = v * 1000\nUse(b) = {\n  A = b.G\n  A(Thousand)\n}\nUse(5)", "ok 5000", ""),
        new("F02-hit-ignores-arg", "Box = { G = 42 }\nUse(b) = {\n  A = b.G\n  A(Inc)\n}\nUse(Box)", "ok 42", ""),
        new("F03-mixed-activations", "Thousand(v) = v * 1000\nBox = { G = 42 }\nUse(b) = {\n  A = b.G\n  A(Thousand)\n}\nUse(5), Use(Box)", "ok (5000, 42)", ""),
        new("F04-closed-callers-named-size", "Use(obj) = {\n  Get = obj.size\n  Get(count)\n}\nUse([1, 2, 3])", "ok 3", ""),
        new("F05-root-must-inferred", "Get = 5.size\nGet(count)", "ok 1", ""),
        new("F07-navigate-through-A", "Lib(*xs) = {\n  public K = 99\n  0\n}\nK(v) = 7\nNavigate(f) = f.K\nUse(f) = {\n  A = f\n  Navigate(A)\n}\nUse(Lib)", "ok 99", "", Was: "ok 7"),
        new("F07d-navigate-direct-param", "Lib(*xs) = {\n  public K = 99\n  0\n}\nK(v) = 7\nNavigate(f) = f.K\nUse(f) = Navigate(f)\nUse(Lib)", "ok 99", ""),
        new("F07s-navigate-static-oracle", "Lib(*xs) = {\n  public K = 99\n  0\n}\nK(v) = 7\nNavigate(f) = f.K\nA = Lib\nNavigate(A)", "ok 99", ""),
        new("F07r-navigate-runtime-ref", "Lib(*xs) = {\n  public K = 99\n  0\n}\nK(v) = 7\nNavigate(f) = f.K\nR = Capture(Lib(1))\nA = R.Algorithm\nNavigate(A), Navigate(R.Algorithm)", "ok (99, 99)", "", Was: "ok (7, 99)"),
        new("F08-twice-zero-call", "Only(*xs) = tick()\nTwice(f) = f(), f()\nUse(f) = {\n  A = f\n  Twice(A)\n}\nUse(Only)", "ok (1, 2)", "", Ticks: 2, Was: "ok (1, 1) ticks 1"),
        new("F08s-twice-static-oracle", "Only(*xs) = tick()\nTwice(f) = f(), f()\nA = Only\nTwice(A)", "ok (1, 2)", "", Ticks: 2),
        new("F06-two-edges", "Thousand(v) = v * 1000\nUse(b) = {\n  A = b.H.G\n  A(Thousand, Thousand)\n}\nUse(5)", "ok 5000000", ""),
        new("G01-absent-callable", "Use(f) = {\n  A = f\n  A(9)\n}\nUse(5)", "err ArityMismatch", "", Diagnostic: "while evaluating call to Use: Callable `A` expects 0 arguments, but was called with 1 argument. @[7:3, 7:7)"),
        new("G02-projection-failure", "Bad = min([])\nUse(f) = {\n  A = f\n  A(9)\n}\nUse(Bad.Algorithm)", "err IllegalInEval", "", Diagnostic: "while evaluating call to Use: while evaluating call to A: while evaluating call to min: Illegal in eval: min requires a non-empty collection @[5:7, 5:14)", Was: "err ArityMismatch"),
        new("G02b-projection-failure-direct", "Bad = min([])\nUse(f) = f(9)\nUse(Bad.Algorithm)", "err IllegalInEval", "", Diagnostic: "while evaluating call to Use: while evaluating call to f: while evaluating call to min: Illegal in eval: min requires a non-empty collection @[5:7, 5:14)"),
        new("G03-not-an-algorithm", "Q5(f) = f(1)\nBad = Q5(5)\nUse(f) = {\n  A = f\n  A(9)\n}\nUse(Bad.Algorithm)", "err NotAnAlgorithm", "", Diagnostic: "while evaluating call to Use: while evaluating call to A: while evaluating call to Q5: while evaluating call to f: Parameter 'f' is not callable here: it is bound to a value, not to an algorithm. Pass an algorithm for 'f', or read it as a value. @[5:9, 5:10)", Was: "err ArityMismatch"),
        new("G03b-not-an-algorithm-direct", "Q5(f) = f(1)\nBad = Q5(5)\nUse(f) = f(9)\nUse(Bad.Algorithm)", "err NotAnAlgorithm", "", Diagnostic: "while evaluating call to Use: while evaluating call to f: while evaluating call to Q5: while evaluating call to f: Parameter 'f' is not callable here: it is bound to a value, not to an algorithm. Pass an algorithm for 'f', or read it as a value. @[5:9, 5:10)"),
        new("G04-cycle", "A = R.Algorithm\nR = Capture(A(1))\nA(2)", "err DemandCycle", "", Diagnostic: "while evaluating call to A: Demand cycle: the argument depends on its own value while it is being evaluated. @[5:5, 5:16)", Was: "err ArityMismatch"),
        new("G04b-cycle-direct", "R = Capture(R.Algorithm(1))\nR.Algorithm(2)", "err DemandCycle", "", Diagnostic: "while evaluating dotCall .Algorithm of R: Demand cycle: the argument depends on its own value while it is being evaluated. @[5:13, 5:27)", Was: "err NotAnAlgorithm (the pre-META-S3-4 CR-2 refusal of a dot callee)"),
        new("G05-unresolved-member-fallback", "Use(b) = {\n  A = b.G\n  A(3)\n}\nUse(5)", "err NotAnAlgorithm", "", Diagnostic: "while evaluating call to Use: while evaluating call to A: while evaluating dotCall .G of b: Parameter 'G' is not callable here: it is bound to a value, not to an algorithm. Pass an algorithm for 'G', or read it as a value. @[6:9, 6:10)"),
        new("G06-cancel", "R = if(stop(), Capture(Square(5)), 0)\nA = R.Algorithm\nA(9), trace(1)", "cancelled", "", WithCancel: true, Was: "err ArityMismatch"),
        new("G07-async-receiver", "R = if(aflag(), Capture(Square(5)), 0)\nA = R.Algorithm\nA(9), Apply(R.Algorithm, 9)", "ok (81, 81)", "9,9", Was: "err ArityMismatch"),
        new("G08-deferred-source", "F(0) = Capture(Inc(0))\nF(n) = { open 'https://modules.example/m.kat'\n Capture(Inc2(n)) }\nR = F(1)\nA = R.Algorithm\nA(5), Apply(R.Algorithm, 5)", "ok (7, 7)", "", Module: "public Inc2(x) = x + 2", Downloads: 1, Was: "err ArityMismatch"),
        new("G09-steps-runtime", "R = Capture(Square(5))\nA = R.Algorithm\nA", "err ArityMismatch", "", Diagnostic: "while evaluating dotCall .Algorithm of R: Property 'Square' expects 1 parameter, but was called with 0 arguments. @[5:13, 5:19)", MaxSteps: 3),
        new("G09b-steps-static", "A = Square\nA(9)", "ok 81", "9", MaxSteps: 3),
        new("G10-optimizer", "Step(x) = x + 1, x < 3\nUse(f) = {\n  A = f\n  A(0).while\n}\nUse(Step)", "ok 3", "", Loops: "1/0", Was: "err ArityMismatch"),
        new("V01-C01-static-exact", "G(o) = o + 100\nBox = { G(x) = x * 10 }\nA = Box.G\nA, A(3)", "err ArityMismatch", "", Diagnostic: "Property 'A' expects 1 parameter, but was called with 0 arguments. @[8:1, 8:2)"),
        new("V02-C04-hit-static-exact", "Thousand(v) = v * 1000\nBox = { G(x) = x * 10 }\nA = Box.G\nA(Thousand)", "err ArityMismatch", "", Diagnostic: "while evaluating call to A: Property 'Thousand' expects 1 parameter, but was called with 0 arguments. @[8:3, 8:11)"),
        new("V03-B05-direct-exact", "Describe(0) = 'zero'\nDescribe(n) = 'other'\nR = Capture(Describe(0))\nR.Algorithm(5)", "ok 'other'", ""),
        new("V04-G08-direct-exact", "F(0) = Capture(Inc(0))\nF(n) = { open 'https://modules.example/m.kat'\n Capture(Inc2(n)) }\nR = F(1)\nR.Algorithm(5), Apply(R.Algorithm, 5)", "ok (7, 7)", "", Module: "public Inc2(x) = x + 2", Downloads: 1),
        new("V05-forward-static-chain", "B = A\nA = Square\nB(9)", "ok 81", "9"),
        new("V06-forward-runtime-chain", "B = A\nA = R.Algorithm\nR = Capture(Square(5))\nB(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("V07-two-runtime-links", "R = Capture(Square(5))\nA = R.Algorithm\nB = A\nB(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("V08-value-only-direct-alias", "Use(f) = {\n A = f\n A, A(), A()\n}\nUse(5)", "ok (5, 5, 5)", ""),
        new("V09-runtime-cycle-two-links", "A = R.Algorithm\nB = A\nR = Capture(B(1))\nB(2)", "err DemandCycle", "", Diagnostic: "while evaluating call to B: Demand cycle: the argument depends on its own value while it is being evaluated. @[5:5, 5:16)", Was: "err ArityMismatch"),
        new("V10-chain-known-signature-cache", "Only(*xs) = tick()\nUse(f) = {\n A = f\n B = A\n A, B, B()\n}\nUse(Only)", "ok (1, 1, 2)", "", Ticks: 2, Was: "ok (1, 1, 1) ticks 1"),
        new("V11-structural-supply-async", "R = if(aflag(), Capture(Square(5)), 0)\nBox = { A = R.Algorithm }\nApply(Box.A, 9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("V12-param-structural-supply-async", "R = if(aflag(), Capture(Square(5)), 0)\nBox = { A = R.Algorithm }\nUse(b) = Apply(b.A, 9)\nUse(Box)", "ok 81", "9", Was: "err ArityMismatch"),
        new("V13-structural-map-async", "R = if(aflag(), Capture(Square(5)), 0)\nBox = { A = R.Algorithm }\n[1, 2].map(Box.A)", "ok [1, 4]", "1,2", Was: "err ArityMismatch"),
        new("V14-structural-while-async", "Step(x) = x + 1, x < 3\nR = if(aflag(), Capture(Step(0)), 0)\nBox = { A = R.Algorithm }\nBA = Box.A\nBA(0).while", "ok 3", "", Loops: "1/0", Was: "err ArityMismatch"),
        new("V15-param-algorithm-alias-async", "Use(r) = {\n A = r.Algorithm\n A(9)\n}\nUse(if(aflag(), Capture(Square(5)), 0))", "ok 81", "9", Was: "err ArityMismatch"),
        new("V16-identity-through-runtime-alias-name", "Lib(*xs) = { public K(x) = x + 100\n 0 }\nUse(f) = {\n A = f\n B = A.K\n B(3)\n}\nUse(Lib)", "err NotAnAlgorithm", "", Diagnostic: "while evaluating call to Use: while evaluating call to B: while evaluating dotCall .K of A: Parameter 'K' is not callable here: it is bound to a value, not to an algorithm. Pass an algorithm for 'K', or read it as a value. @[9:8, 9:9)"),
        new("V17-identity-through-runtime-alias-param", "Lib(*xs) = { public K(x) = x + 100\n 0 }\nUse(f) = {\n A = f\n C(b) = {\n  K(o) = 7\n  B = b.K\n  B(3)\n }\n C(A)\n}\nUse(Lib)", "ok 103", "", Was: "err ArityMismatch"),
        new("V18-own-member", "Lib(*xs) = { public K = 99\n 0 }\nUse(f) = {\n A = { public K = 5\n f }\n A.K\n}\nUse(Lib)", "ok 5", ""),
        new("V19-zero-target-chain", "Z = tick()\nUse(f) = {\n A = f\n B = A\n A, B, B(), A()\n}\nUse(Z)", "ok (1, 1, 1, 1)", "", Ticks: 1),
        new("V20-named-link-failure", "Bad = min([])\nA = Bad.Algorithm\nUse(f) = {\n B = f\n B(9)\n}\nUse(A)", "err IllegalInEval", "", Diagnostic: "while evaluating call to Use: while evaluating call to B: while evaluating call to min: Illegal in eval: min requires a non-empty collection @[5:7, 5:14)", Was: "err ArityMismatch"),
        new("V21-static-own-forward-namespace", "A = { public K = 5\n Square }\nA.K, Apply(A, 3)", "ok (5, 9)", "3"),
        new("V22-alias-own-fallback", "Lib(*xs) = { public K(x) = x + 100\n 0 }\nUse(f) = {\n A = f\n B = A.K\n B(Inc)\n}\nUse(Lib)", "ok 1", ""),
        new("V23-two-captured-invocations-independent", "F(x) = trace(x)\nR = Capture(F(5))\nR.Algorithm(9), R.Invoke(), R.Invoke()", "ok (9, 5, 5)", "9,5,5"),
        new("V24-member-navigation-compat", "Box = { G(*xs) = { public K = 99\n 0 } }\nG(o) = o\nK(v) = 7\nNavigate(f) = f.K\nUse(b) = {\n A = b.G\n Navigate(A)\n}\nUse(Box)", "ok 99", "", Was: "ok 7"),
        new("V25-member-navigation-direct", "Box = { G(*xs) = { public K = 99\n 0 } }\nG(o) = o\nK(v) = 7\nNavigate(f) = f.K\nUse(b) = Navigate(b.G)\nUse(Box)", "ok 99", ""),
        new("V26-alias-own-target-scope", "R = 5\nA = {\n R = Capture(Square(5))\n R.Algorithm\n}\nA(9)", "ok 81", "9", Was: "err ArityMismatch"),
        new("V27-valid-current-cycle", "Hold(g) = Capture(g(0))\nR = Hold(R.Algorithm)\nR.Algorithm(1)", "err DemandCycle", "", Diagnostic: "while evaluating dotCall .Algorithm of R: Demand cycle: the argument depends on its own value while it is being evaluated. @[6:10, 6:21)"),
        new("V28-direct-cancellation", "R = if(stop(), Capture(Square(5)), 0)\nR.Algorithm(9), trace(1)", "cancelled", "", WithCancel: true),
        new("V29-forced-twin-alias-error", "if(aflag(), {\n R = Capture(Square(5))\n A = R.Algorithm\n A(9)\n}, 0)", "ok 81", "9", Was: "err ArityMismatch"),
        new("X01-share-value-then-call", "Only(*xs) = tick()\nMk(n) = if(trace(n) > 0, Capture(Only(n)), 0)\nA = Mk(5).Algorithm\nA, A()", "ok (1, 2)", "5", Ticks: 2, Was: "ok (1, 1) [5,5] ticks 1"),
        new("X01b-share-call-then-value", "Only(*xs) = tick()\nMk(n) = if(trace(n) > 0, Capture(Only(n)), 0)\nA = Mk(5).Algorithm\nA(), A", "ok (1, 2)", "5", Ticks: 2, Was: "ok (1, 1) [5,5] ticks 1"),
        new("X01c-share-forwarded", "Only(*xs) = tick()\nMk(n) = if(trace(n) > 0, Capture(Only(n)), 0)\nA = Mk(5).Algorithm\nTwice(f) = f(), f()\nA, Twice(A), A", "ok (1, (2, 3), 1)", "5", Ticks: 3, Was: "ok (1, (1, 1), 1) [5,5,5] ticks 1"),
        new("X02-inline-param-callable", "Use(f) = Apply({ f }, 9)\nUse(Square)", "ok 81", "9", Was: "err ArityMismatch"),
        new("X02b-inline-param-value", "Use(f) = { f } + 1\nUse(5)", "ok 6", ""),
        new("X02c-inline-link-callee", "R = Capture(Square(5))\nApply({ R.Algorithm }, 9), [1, 2].map({ R.Algorithm })", "ok (81, [1, 4])", "9,1,2", Was: "err ArityMismatch"),
        new("X02d-inline-two-activations", "Use(f) = Apply({ f }, 3)\nUse(Square), Use(Inc)", "ok (9, 4)", "3", Was: "err ArityMismatch"),
        new("X03-open-runtime-alias-namespace", "Outer(n) = {\n  Lib = { public X = 10\n  n }\n  P = { open Lib\n  X }\n  P, Lib, Lib.X\n}\nOuter(1)", "ok (10, 1, 10)", ""),
        new("X03b-member-with-runtime-row", "Outer(n) = {\n  Lib = { public X = 10\n  n }\n  Lib(4)\n}\nOuter(Inc)", "ok 5", "", Was: "err ArityMismatch"),
        new("X04-forward-chain-10", "S1 = S2\nS2 = S3\nS3 = S4\nS4 = S5\nS5 = S6\nS6 = S7\nS7 = S8\nS8 = S9\nS9 = S10\nS10 = R.Algorithm\nR = Capture(Square(5))\nS1(9), S5(3)", "ok (81, 9)", "9,3", Was: "err ArityMismatch"),
        new("X04b-structural-chain", "R = Capture(Square(5))\nA = R.Algorithm\nBox = { Inner = { B = A } }\nC = Box.Inner.B\nC(9), Box.Inner.B(3), Apply(C, 2)", "ok (81, 9, 4)", "9,3,2", Was: "err ArityMismatch"),
        new("X05-two-activations", "Mk(g) = {\n  A = g\n  A(3)\n}\nMk(Square), Mk(Inc)", "ok (9, 4)", "3", Was: "err ArityMismatch"),
        new("X05b-recursive-activations", "Walk(n, f) = {\n  A = f\n  if(n <= 0, A(0), A(n) + Walk(n - 1, f))\n}\nWalk(3, Inc)", "ok 10", "", Was: "err ArityMismatch"),
        new("X06-repeat", "Use(f) = {\n  A = f\n  A(0).repeat(3)\n}\nUse(Inc)", "ok 3", "", Loops: "1/0", Was: "err ArityMismatch"),
        new("X06b-filter", "IsBig(x) = x > 1\nUse(p) = {\n  A = p\n  [1, 2, 3].filter(A)\n}\nUse(IsBig)", "ok [2, 3]", "", Was: "err ArityMismatch"),
        new("X06c-reduce", "Add(a, b) = a + b\nUse(p) = {\n  A = p\n  [1, 2, 3].reduce(A, 0)\n}\nUse(Add)", "ok 6", "", Was: "err ArityMismatch"),
        new("X06d-family-member-path", "F(o) = o\nBox = {\n  F(0) = 'z'\n  F(n) = 'o'\n}\nUse(b) = {\n  A = b.F\n  A(0), A(1)\n}\nUse(Box)", "ok ('z', 'o')", "", Was: "err ArityMismatch"),
        new("X06e-capture-param-alias", "Use(f) = {\n  A = f\n  R2 = Capture(A(4))\n  R2.Invoke(), R2.Algorithm(5)\n}\nUse(Square)", "ok (16, 25)", "4,5", Was: "err ArityMismatch"),
        new("X07-cancel-param-alias", "Use(f) = {\n  A = f\n  A(9)\n}\nR = if(stop(), Capture(Square(5)), 0)\nUse(R.Algorithm), trace(1)", "cancelled", "", WithCancel: true, Was: "err ArityMismatch"),
        new("X07b-async-param-alias", "Use(f) = {\n  A = f\n  A(9), A(2)\n}\nUse(if(aflag(), Capture(Square(5)), 0).Algorithm)", "ok (81, 4)", "9,2", Was: "err ArityMismatch"),
        new("X07c-failure-param-alias", "Use(f) = {\n  A = f\n  A(9)\n}\nUse(5.Algorithm)", "err TypeMismatch", "", Diagnostic: "while evaluating call to Use: while evaluating call to A: Type mismatch: `Algorithm` requires a call reference, got numeric value 5 @[7:3, 7:4)", Was: "err ArityMismatch"),
        new("X08-zero-param-callee", "Z = tick()\nR = Capture(Z())\nA = R.Algorithm\nA, A(), A", "ok (1, 1, 1)", "", Ticks: 1),
        new("X08b-value-member-terminal", "Box = { G = 42 }\nG(o) = o\nUse(b) = {\n  A = b.G\n  A, A()\n}\nUse(Box)", "ok (42, 42)", ""),
        new("X09-fused-count-filter", "IsBig(x) = x > 5\nUse(p) = {\n  A = p\n  count(filter(range(1, 10), A))\n}\nUse(IsBig)", "ok 5", "", Fusion: "1/1", Was: "err ArityMismatch"),
        new("X09b-dot-fallback-builtin", "Use(f) = {\n  A = f\n  [1, 2, 3].A\n}\nUse(count)", "ok 3", "", Was: "err ArityMismatch"),
        // A genuinely zero-parameter target remains an ordinary property (brief §3): deciding its
        // runtime eligibility must not execute the computed receiver twice for ONE call. The S3-1
        // oracle runs Mk once; D4's ordinary-property preservation requires that same result here.
        new("X10-terminal-call-receiver-once", "Z = tick()\nMk(n) = if(trace(n) == n, Capture(Z()), 0)\nA = Mk(5).Algorithm\nA()", "ok 1", "5", Ticks: 1),
        // Repeating the receiver can also change the calculation, not just its trace and charges.
        new("X10b-terminal-call-keeps-selected-value", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nA()", "ok 10", "", Ticks: 1, Steps: 5),
        new("RF1-D4-single", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nA()", "ok 10", "", Ticks: 1, Emitted: 1),
        new("RF1-D4-twice", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nA(), A()", "ok (10, 20)", "", Ticks: 2, Emitted: 2),
        new("RF1-D4-bare-call", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nA, A()", "ok (10, 20)", "", Ticks: 2, Emitted: 2),
        new("RF1-D4-call-bare", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nA(), A", "ok (10, 10)", "", Ticks: 1, Emitted: 2),
        new("RF1-D4-bare-bare", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nA, A", "ok (10, 10)", "", Ticks: 1, Emitted: 2),
        new("RF1-D4-alternating", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nA(), A, A(), A, A()", "ok (10, 10, 20, 10, 20)", "", Ticks: 3, Emitted: 5),
        new("RF1-D4-chain-2", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nS1 = A\nS2 = S1\nS2(), A, S2()", "ok (10, 20, 20)", "", Ticks: 3),
        new("RF1-D4-chain-10", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nS1 = A\nS2 = S1\nS3 = S2\nS4 = S3\nS5 = S4\nS6 = S5\nS7 = S6\nS8 = S7\nS9 = S8\nS10 = S9\nS10(), A, S10()", "ok (10, 20, 20)", "", Ticks: 3),
        new("RF1-D4-inline", "Call0(f) = f()\nTen = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nCall0({ Mk(5).Algorithm })", "ok 10", "", Ticks: 1),
        new("RF1-D4-forward", "Call0(f) = f()\nTen = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nCall0(A), Call0(A), A", "ok (10, 20, 10)", "", Ticks: 2),
        new("RF1-D4-nested", "Z = 7\nUse(n) = {\n Mk(t) = if(trace(t) == t, Capture(Z()), 0)\n A = Mk(n).Algorithm\n A(), A, A(), A\n}\nUse(3), Use(4)", "ok ((7, 7, 7, 7), (7, 7, 7, 7))", "3,3,4,4"),
        new("RF1-D4-value-only", "G(o) = trace(o)\nUse(b) = {\n A = b.G\n A(), A, A(), A\n}\nUse(5)", "ok (5, 5, 5, 5)", "5,5"),
        new("RF1-D4-zero-member", "G(o) = o\nBox = { G = tick() }\nUse(b) = {\n A = b.G\n A(), A, A(), A\n}\nUse(Box)", "ok (1, 1, 1, 1)", "", Ticks: 1),
        new("RF1-D4-async", "Z = 7\nMk(n) = if(atrace(n) == n, Capture(Z()), 0)\nA = Mk(5).Algorithm\nA(), A, A(), A", "ok (7, 7, 7, 7)", "a5,a5"),
        new("RF1-D3-zero-accepting", "Only(*xs) = tick()\nMk(n) = if(trace(n) == n, Capture(Only()), 0)\nA = Mk(5).Algorithm\nA(), A, A(), A", "ok (1, 2, 3, 2)", "5", Ticks: 3),
        new("RF1-open-chain-1", "Outer(n) = {\n A = n\n B1 = { public K = 11\n A }\n P = { open B1\n K }\n P\n}\nOuter(1)", "ok 11", ""),
        new("RF1-open-chain-2", "Outer(n) = {\n A = n\n B1 = { public K = 11\n A }\n B2 = { public K = 12\n B1 }\n P = { open B2\n K }\n P\n}\nOuter(1)", "ok 12", ""),
        new("RF1-open-chain-10", "Outer(n) = {\n A = n\n B1 = { public K = 11\n A }\n B2 = { public K = 12\n B1 }\n B3 = { public K = 13\n B2 }\n B4 = { public K = 14\n B3 }\n B5 = { public K = 15\n B4 }\n B6 = { public K = 16\n B5 }\n B7 = { public K = 17\n B6 }\n B8 = { public K = 18\n B7 }\n B9 = { public K = 19\n B8 }\n B10 = { public K = 20\n B9 }\n P = { open B10\n K }\n P\n}\nOuter(1)", "ok 20", ""),
        new("RF1-open-original", "Outer(n) = {\n A = n\n B = { public K = 10\n A }\n P = { open B\n K }\n P\n}\nOuter(1)", "ok 10", ""),
        new("RF1-open-forward", "Outer(n) = {\n B = { public K = 10\n A }\n A = n\n P = { open B\n K }\n P\n}\nOuter(1)", "ok 10", ""),
        new("RF1-open-own-not-target", "Target(x) = { public K = 99\n x }\nOuter(n) = {\n A = n\n B = { public K = 10\n A }\n P = { open B\n K }\n P, B.K\n}\nOuter(Target)", "ok (10, 10)", ""),
        new("RF1-open-nested", "Outer(n) = {\n A = n\n Box = { public B = { public K = 10\n A } }\n P = { open Box.B\n K }\n P\n}\nOuter(1)", "ok 10", ""),
        new("RF1-open-shadow", "Outer(n) = {\n A = n\n B = { public K = 10\n A }\n P = { open B\n K = 12\n K }\n P\n}\nOuter(1)", "ok 12", ""),
        new("RF1-open-through-opens", "Outer(n) = {\n A = n\n Lib = { public Ref = A }\n B = { open Lib, Lib\n public K = 10\n Ref }\n P = { open B\n K }\n P\n}\nOuter(1)", "ok 10", ""),
        new("RF1-D4-cancel-terminal", "Z = stop()\nMk(n) = if(trace(n) == n, Capture(Z()), 0)\nA = Mk(5).Algorithm\nA(), trace(99)", "cancelled", "5", WithCancel: true),
        new("RF1-D4-structure-empty", "Z = ()\nMk(n) = if(trace(n) == n, Capture(Z()), 0)\nA = Mk(5).Algorithm\n[A(), A, A()]", "ok [(), (), ()]", "5,5", Emitted: 1),
        new("RF1-D4-structure-sequence", "Z = (1, 2)\nMk(n) = if(trace(n) == n, Capture(Z()), 0)\nA = Mk(5).Algorithm\n[A(), A, A()]", "ok [(1, 2), (1, 2), (1, 2)]", "5,5", Emitted: 1),
        // D4 (final review, 2026-10-19): a CALLABLE-only observation (`Navigate(A)` reads the alias's own
        // member K) performs the eligibility projection and so the receiver work; the FIRST ordinary
        // observation afterwards — a bare read or a terminal call — consumes it, exactly as the S3-1
        // ordinary-property oracle evaluates these programs. RF1 refused to lend that work ((7, 20) with
        // two ticks), which made eligibility checking duplicate the receiver evaluation.
        new("RF1-prior-projection-call", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = { public K = 7\n Mk(5).Algorithm }\nNavigate(f) = f.K\nNavigate(A), A()", "ok (7, 10)", "", Ticks: 1),
        new("RF1-prior-projection-bare", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = { public K = 7\n Mk(5).Algorithm }\nNavigate(f) = f.K\nNavigate(A), A", "ok (7, 10)", "", Ticks: 1),
        new("RF1-prior-projection-mixed", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = { public K = 7\n Mk(5).Algorithm }\nNavigate(f) = f.K\nNavigate(A), A(), A", "ok (7, 10, 10)", "", Ticks: 1),
        new("RF1-prior-projection-planned-value", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = { public K = 7\n Mk(5).Algorithm }\nNavigate(f) = f.K\nId(x) = x\nNavigate(A), Id(A()), A", "ok (7, 10, 10)", "", Ticks: 1),
        new("RF1-prior-projection-planned-invoke", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = { public K = 7\n Mk(5).Algorithm }\nNavigate(f) = f.K\nP = Capture(A())\nNavigate(A), P.Invoke(), P.Invoke(), A", "ok (7, 10, 20, 10)", "", Ticks: 2),
        new("RF1-prior-projection-async", "Ten = 10\nTwenty = 20\nMk(n) = if(atrace(tick()) == 1, Capture(Ten()), Capture(Twenty()))\nA = { public K = 7\n Mk(5).Algorithm }\nNavigate(f) = f.K\nNavigate(A), A(), A", "ok (7, 10, 10)", "a1", Ticks: 1),
        // The distinguishing pair of the final review: the same program with the parameter read directly
        // or through one nested call. Under RF1's invocation tokens the nested read fell outside the
        // token that performed the projection, so the bare read re-evaluated the receiver ((20, 20), two
        // ticks) while the direct read shared it ((10, 10), one tick); a bare read's value cannot depend
        // on incidental call nesting. The S3-1 ordinary-property oracle gives (10, 10) with one tick.
        new("FR-nav-direct-read", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nK(x) = x\nNavigate(f) = f.K\nNavigate(A), A", "ok (10, 10)", "", Ticks: 1),
        new("FR-nav-nested-call-read", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nId(y) = y\nK(x) = Id(x)\nNavigate(f) = f.K\nNavigate(A), A", "ok (10, 10)", "", Ticks: 1),
        new("FR-nav-nested-call-then-call", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nId(y) = y\nK(x) = Id(x)\nNavigate(f) = f.K\nNavigate(A), A()", "ok (10, 20)", "", Ticks: 2),
        new("FR-nav-twice-bare", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = { public K = 7\n Mk(5).Algorithm }\nNavigate(f) = f.K\nNavigate(A), Navigate(A), A", "ok (7, 7, 10)", "", Ticks: 1),
        new("FR-call-then-nav-then-bare", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = { public K = 7\n Mk(5).Algorithm }\nNavigate(f) = f.K\nA(), Navigate(A), A", "ok (10, 7, 10)", "", Ticks: 1),
        new("FR-chain-nested-nav", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nB = A\nId(y) = y\nKK(x) = Id(x)\nNav2(f) = f.KK\nNav2(B), A, B(), A", "ok (10, 10, 20, 10)", "", Ticks: 2),
        new("FR-activation-nav-call-bare", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nUse(n) = {\n A = { public K = 7\n  Mk(n).Algorithm }\n Navigate(f) = f.K\n Navigate(A), A(), A\n}\nUse(5)", "ok (7, 10, 10)", "", Ticks: 1),
        new("FR-string-then-call-then-bare", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nS1 = A\nS2 = S1\nS2.string, S2(), A", "ok ('10', 20, 10)", "", Ticks: 2),
        new("RF1-prior-peek-empty-filter", "Ten = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\ncount(filter([], A)), A()", "ok (0, 10)", "", Ticks: 1),
        new("RF1-D4-first-planned-invoke", "Run(meta p) = p.Invoke()\nTen = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nRun(A())", "ok 10", "", Ticks: 1),
        new("RF1-D4-first-planned-value", "Force(x) = x\nTen = 10\nTwenty = 20\nMk(n) = if(tick() == 1, Capture(Ten()), Capture(Twenty()))\nA = Mk(5).Algorithm\nForce(A())", "ok 10", "", Ticks: 1),
        new("RF1-D4-local-cache-alias", "Ten = 10\nTwenty = 20\nUse(n) = {\n A = {\n R = if(tick() + n == n + 1, Capture(Ten()), Capture(Twenty()))\n R.Algorithm\n }\n A(), A, A(), A\n}\nUse(5)", "ok (10, 10, 20, 10)", "", Ticks: 2),
        // CACHE-PUB-1 D4 extension (owner decision 2026-10-22): both terminal alias and ordinary
        // control establish A's empty entry on the first owning A(); later calls stay fresh.
        new("RF1-D4-local-cache-ordinary-control", "Ten = 10\nTwenty = 20\nUse(n) = {\n A = {\n R = if(tick() + n == n + 1, Capture(Ten()), Capture(Twenty()))\n R.Algorithm + 0\n }\n A(), A, A(), A\n}\nUse(5)", "ok (10, 10, 20, 10)", "", Ticks: 2),
    ];

    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public async Task RF1_SourceProjectionFailure_IsNotCallableAbsence(bool premark, bool suspended)
    {
        var source = "Id(x) = x\nIgnore(x) = 1\nR = Capture(Id(1))\nBad = "
            + (suspended ? "if(aflag(), R.Invoke, 0)" : "R.Invoke")
            + "\nUse(p) = Apply(p.G, 0)\nOuter(r) = {\n A = r.Algorithm\n B = A\n Box = { C = B }\n Use(Box.C)\n}\n"
            + (premark ? "Ignore(5.Algorithm)\n" : "") + "Outer(Bad)";
        var c = new Case("RF1-C1-H", source, "err IllegalInEval", "");
        var generic = Sync(c, false);
        var optimized = Sync(c, true);
        var asynchronous = await Async(c);
        Assert.Equal("err IllegalInEval", generic.Outcome);
        Assert.Equal(generic.Outcome, optimized.Outcome);
        Assert.Equal(generic.Outcome, asynchronous.Outcome);
        Assert.Equal(generic.Diagnostic, optimized.Diagnostic);
        Assert.Equal(generic.Diagnostic, asynchronous.Diagnostic);
        Assert.Equal(generic.Steps, optimized.Steps);
        Assert.Equal(generic.Steps, asynchronous.Steps);
        Assert.Equal("", generic.Traces);
    }

    [Theory]
    [InlineData("F(x) = x\nA = F\nP = { open A\n 1 }\nP", "callable alias")]
    [InlineData("F(x) = x + 1\nP = { open F\n 1 }\nP", "requires arguments")]
    [InlineData("Outer(n) = {\n A = n\n B = { private K = 10\n A }\n P = { open B\n K }\n P\n}\nOuter(1)", "forwarded by name")]
    [InlineData("Box = { Algorithm(x) = x }\nA = Box.Algorithm\nP = { open A\n 1 }\nP", "callable alias")]
    public void RF1_NamespaceRestrictions_RemainStatic(string source, string reason)
    {
        var parsed = Parser.Parse(source);
        Assert.True(parsed.HasErrors);
        Assert.Contains(parsed.Diagnostics, d => d.Message.Contains(reason, StringComparison.Ordinal));
    }

    [Theory]
    // META-S3-3: a bare alias is no supplied call computation, so `while`'s meta step refuses it
    // before the alias (or its terminal `Mk(5)` body) is ever demanded.
    [InlineData("Z = false\nMk(n) = if(trace(n) == n, Capture(Z()), 0)\nA = Mk(5).Algorithm\nA.while()", "err NotAnAlgorithm", "")]
    [InlineData("Z = 1 / 0\nMk(n) = if(trace(n) == n, Capture(Z()), 0)\nA = Mk(5).Algorithm\nA()", "err DivisionByZero", "5")]
    [InlineData("G(o) = trace(o) / 0\nUse(b) = { A = b.G\n A() }\nUse(5)", "err DivisionByZero", "5")]
    public async Task RF1_TerminalBodyConsumers_PreserveEffectsAndDiagnostics(string source, string expected, string traces)
    {
        var c = new Case("RF1-terminal-consumer", source, expected, traces);
        var generic = Sync(c, false);
        var optimized = Sync(c, true);
        var asynchronous = await Async(c);
        Assert.Equal(expected, generic.Outcome);
        Assert.Equal(traces, generic.Traces);
        Assert.Equal(generic.Outcome, optimized.Outcome);
        Assert.Equal(generic.Outcome, asynchronous.Outcome);
        Assert.Equal(generic.Diagnostic, optimized.Diagnostic);
        Assert.Equal(generic.Diagnostic, asynchronous.Diagnostic);
        Assert.Equal(generic.Traces, optimized.Traces);
        Assert.Equal(generic.Traces, asynchronous.Traces);
        Assert.Equal(generic.Steps, optimized.Steps);
        Assert.Equal(generic.Steps, asynchronous.Steps);
    }

    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var c in Cases) data.Add(c.Id);
        return data;
    }

    private sealed record Observation(string Outcome, string Diagnostic, string Traces, int Ticks, long Steps,
        string Loops, string Fusion, int Downloads, int? Emitted);

    /// <summary>The harness host: <c>trace</c>, <c>tick</c>; <c>aflag</c>/<c>atrace</c>/<c>stop</c> genuinely asynchronous on the async engine.</summary>
    private sealed class Probe(Case c)
    {
        private readonly List<string> _traces = [];
        private int _ticks;
        private int _downloads;
        public readonly CancellationTokenSource? Cancel = c.WithCancel ? new CancellationTokenSource() : null;

        public HostOperations Operations(bool asynchronous) => HostOperations.Create(
            HostOperation.Create("trace", (args, _) => { lock (_traces) _traces.Add(Format(args[0])); return args[0]; }, "x"),
            HostOperation.Create("tick", (_, _) => new Result.Atom(Interlocked.Increment(ref _ticks))),
            asynchronous
                ? HostOperation.CreateAsync("aflag", async (_, _) => { await Task.Yield(); return new Result.Bool(true); })
                : HostOperation.Create("aflag", (_, _) => new Result.Bool(true)),
            asynchronous
                ? HostOperation.CreateAsync("atrace", async (args, _) => { await Task.Yield(); lock (_traces) _traces.Add("a" + Format(args[0])); return args[0]; }, "x")
                : HostOperation.Create("atrace", (args, _) => { lock (_traces) _traces.Add("a" + Format(args[0])); return args[0]; }, "x"),
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
                    Interlocked.Increment(ref _downloads);
                    await Task.Yield();
                    token.ThrowIfCancellationRequested();
                    return c.Module;
                },
            };

        public Observation Observe(string outcome, string diagnostic, long steps, string loops, string fusion, int? emitted = null)
            => new(outcome, diagnostic, string.Join(",", _traces), _ticks, steps, loops, fusion, _downloads, emitted);
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

    private static EvaluationLimits? LimitsOf(Case c, int? maxSteps = null)
        => (maxSteps ?? c.MaxSteps) is { } steps ? new EvaluationLimits { MaxSteps = steps } : null;

    private static Observation Sync(Case c, bool optimized, int? maxSteps = null)
    {
        var probe = new Probe(c);
        var operations = probe.Operations(asynchronous: false);
        var parsed = Parser.Parse(Lib + c.Source, probe.Options(operations));
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
        var loops = new LoopOptimizationDiagnostics();
        var sequences = new SequencePipelineDiagnostics();
        try
        {
            var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), LimitsOf(c, maxSteps),
                enableOptimizations: optimized, loopDiagnostics: loops, sequenceDiagnostics: sequences,
                hostOperations: operations, cancellationToken: probe.Cancel?.Token ?? default);
            return probe.Observe(Outcome(result), Diagnostic(result), budget.ConsumedSteps,
                $"{loops.OptimizedLoopHits}/{loops.OptimizedLoopFallbacks}",
                $"{sequences.FilterCountFusionHits}/{sequences.DirectRangeFusionHits}", result.IsOk ? result.Value.EmittedCount : null);
        }
        catch (OperationCanceledException cancelled) when (probe.Cancel is { } source)
        {
            Assert.Equal(source.Token, cancelled.CancellationToken);
            return probe.Observe("cancelled", "", 0, "", "");
        }
    }

    private static async Task<Observation> Async(Case c, int? maxSteps = null)
    {
        var probe = new Probe(c);
        var operations = probe.Operations(asynchronous: true);
        try
        {
            var options = probe.Options(operations);
            var parsed = c.Module is null ? Parser.Parse(Lib + c.Source, options) : await Parser.ParseAsync(Lib + c.Source, options);
            Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
            var (result, budget) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), LimitsOf(c, maxSteps),
                hostOperations: operations, cancellationToken: probe.Cancel?.Token ?? default);
            return probe.Observe(Outcome(result), Diagnostic(result), budget.ConsumedSteps, "", "", result.IsOk ? result.Value.EmittedCount : null);
        }
        catch (OperationCanceledException cancelled) when (probe.Cancel is { } source)
        {
            Assert.Equal(source.Token, cancelled.CancellationToken);
            return probe.Observe("cancelled", "", 0, "", "");
        }
    }

    private static Task<Observation> Bounded(Func<Task<Observation>> run) => Task.Run(run).WaitAsync(WaitLimit);

    private static void Check(Case c, string mode, Observation observed)
    {
        if (c.Steps is { } steps) Assert.Equal(steps, observed.Steps);
        if (c.Emitted is { } emitted) Assert.Equal(emitted, observed.Emitted);
        Assert.True(c.Expected == observed.Outcome, $"{c.Id} {mode}: {observed.Outcome}, expected {c.Expected}");
        Assert.True(c.Diagnostic == observed.Diagnostic, $"{c.Id} {mode}: diagnostic {observed.Diagnostic}, expected {c.Diagnostic}");
        Assert.True(c.Traces == observed.Traces, $"{c.Id} {mode}: traces [{observed.Traces}], expected [{c.Traces}]");
        Assert.True(c.Ticks == observed.Ticks, $"{c.Id} {mode}: ticks {observed.Ticks}, expected {c.Ticks}");
        Assert.True(c.Downloads == observed.Downloads, $"{c.Id} {mode}: downloads {observed.Downloads}, expected {c.Downloads}");
    }

    [Theory]
    [MemberData(nameof(CaseIds))]
    public async Task Corpus_AgreesOnEveryEngine(string id)
    {
        if (Cases.Single(x => x.Id == id).Expected == "err DemandCycle")
        {
            await RunCycleChild(id, scan: false);
            return;
        }
        await CheckCorpus(id);
    }

    private static async Task CheckCorpus(string id)
    {
        var c = Cases.Single(x => x.Id == id);
        var asynchronous = await Bounded(() => Async(c));
        if (c.Module is not null)
        {
            Check(c, "async", asynchronous);
            return;
        }

        var generic = await Bounded(() => Task.FromResult(Sync(c, optimized: false)));
        var optimized = await Bounded(() => Task.FromResult(Sync(c, optimized: true)));
        var failures = new List<string>();
        foreach (var (mode, observed) in new[] { ("generic", generic), ("optimized", optimized), ("async", asynchronous) })
        {
            try { Check(c, mode, observed); }
            catch (Exception error)
            {
                failures.Add($"{error.Message} [ticks={observed.Ticks}; steps={observed.Steps}; emitted={observed.Emitted}; traces={observed.Traces}]");
            }
        }
        Assert.True(failures.Count == 0, string.Join(Environment.NewLine, failures));
        if (c.Expected == "cancelled")
            return;
        Assert.True(c.Loops == optimized.Loops, $"{c.Id}: optimized loops {optimized.Loops}, expected {c.Loops}");
        Assert.True(c.Fusion == optimized.Fusion, $"{c.Id}: optimized fusion {optimized.Fusion}, expected {c.Fusion}");
        Assert.Equal(generic.Emitted, optimized.Emitted);
        Assert.Equal(generic.Emitted, asynchronous.Emitted);
        Assert.True(generic.Steps == optimized.Steps, $"{c.Id}: optimized {optimized.Steps} steps, generic {generic.Steps}");
        Assert.True(generic.Steps == asynchronous.Steps, $"{c.Id}: async {asynchronous.Steps} steps, generic {generic.Steps}");
    }

    /// <summary>
    /// Bounded MaxSteps scans over the newly exposed routes (brief §13: <c>B01</c>, <c>E09</c>, <c>G04</c>,
    /// plus a chain, the freshness rows and the shared receiver): at every limit from 1 to 25 the three modes
    /// reach the same outcome after the same number of steps with the same effects — no optimizer and no
    /// asynchronous resolution moves, repeats or skips a runtime alias's projection or its receiver demand.
    /// </summary>
    [Theory]
    [InlineData("B01-call")]
    [InlineData("E09-while")]
    [InlineData("G04-cycle")]
    [InlineData("D03-runtime-chain-10")]
    [InlineData("A04-collecting-F10")]
    [InlineData("C08-value-vs-callable")]
    [InlineData("V10-chain-known-signature-cache")]
    [InlineData("X01-share-value-then-call")]
    [InlineData("C09-effects")]
    [InlineData("X10b-terminal-call-keeps-selected-value")]
    [InlineData("RF1-D4-alternating")]
    [InlineData("RF1-D4-value-only")]
    [InlineData("RF1-D4-async")]
    [InlineData("FR-nav-nested-call-read")]
    [InlineData("RF1-prior-projection-mixed")]
    public async Task StepLimitScans_AgreeAcrossModes(string id)
    {
        if (Cases.Single(x => x.Id == id).Expected == "err DemandCycle")
        {
            await RunCycleChild(id, scan: true);
            return;
        }
        await CheckStepLimits(id);
    }

    private static async Task CheckStepLimits(string id)
    {
        var c = Cases.Single(x => x.Id == id);
        for (var limit = 1; limit <= 25; limit++)
        {
            var generic = await Bounded(() => Task.FromResult(Sync(c, optimized: false, limit)));
            var optimized = await Bounded(() => Task.FromResult(Sync(c, optimized: true, limit)));
            var asynchronous = await Bounded(() => Async(c, limit));
            foreach (var (mode, observed) in new[] { ("optimized", optimized), ("async", asynchronous) })
            {
                Assert.True(generic.Outcome == observed.Outcome, $"{id} MaxSteps={limit} {mode}: {observed.Outcome} vs generic {generic.Outcome}");
                Assert.True(generic.Steps == observed.Steps, $"{id} MaxSteps={limit} {mode}: {observed.Steps} vs generic {generic.Steps} steps");
                Assert.True(generic.Traces == observed.Traces, $"{id} MaxSteps={limit} {mode}: [{observed.Traces}] vs generic [{generic.Traces}]");
                Assert.True(generic.Ticks == observed.Ticks, $"{id} MaxSteps={limit} {mode}: ticks {observed.Ticks} vs generic {generic.Ticks}");
                Assert.True(generic.Diagnostic == observed.Diagnostic,
                    $"{id} MaxSteps={limit} {mode}: {observed.Diagnostic} vs generic {generic.Diagnostic}");
            }
        }
    }

    private const string CycleCaseVariable = "KATLANG_RUNTIME_ALIAS_CYCLE_CASE";
    private const string CycleScanVariable = "KATLANG_RUNTIME_ALIAS_CYCLE_SCAN";
    private const string CycleMarkerVariable = "KATLANG_RUNTIME_ALIAS_CYCLE_MARKER";

    // A regression to alias-to-self dispatch can overflow the process stack. A task timeout cannot
    // protect the test host from that failure; each dangerous case runs in its own bounded process.
    private static async Task RunCycleChild(string id, bool scan)
    {
        var marker = Path.Combine(Path.GetTempPath(), $"katlang-runtime-alias-cycle-{Guid.NewGuid():N}.txt");
        var start = new ProcessStartInfo("dotnet")
        {
            UseShellExecute = false, CreateNoWindow = true,
            RedirectStandardOutput = true, RedirectStandardError = true,
        };
        start.ArgumentList.Add("vstest");
        start.ArgumentList.Add(typeof(RuntimeCallableAliasCorpusTests).Assembly.Location);
        start.ArgumentList.Add("--Tests:" + typeof(RuntimeCallableAliasCorpusTests).FullName + ".IsolatedCycleChild");
        start.Environment[CycleCaseVariable] = id;
        start.Environment[CycleScanVariable] = scan ? "1" : "0";
        start.Environment[CycleMarkerVariable] = marker;
        try
        {
            using var process = Process.Start(start)!;
            var output = process.StandardOutput.ReadToEndAsync();
            var error = process.StandardError.ReadToEndAsync();
            using var deadline = new CancellationTokenSource(TimeSpan.FromSeconds(90));
            try { await process.WaitForExitAsync(deadline.Token); }
            catch (OperationCanceledException)
            {
                process.Kill(entireProcessTree: true);
                await process.WaitForExitAsync();
                Assert.Fail($"Runtime alias cycle {id} timed out");
            }
            var text = await output + await error;
            Assert.True(process.ExitCode == 0, text);
            Assert.DoesNotContain("Stack overflow", text, StringComparison.OrdinalIgnoreCase);
            Assert.True(File.Exists(marker), text);
            Assert.Equal(id, await File.ReadAllTextAsync(marker));
        }
        finally { File.Delete(marker); }
    }

    [Fact]
    public async Task IsolatedCycleChild()
    {
        if (Environment.GetEnvironmentVariable(CycleCaseVariable) is not { } id)
            return;
        Assert.Equal("err DemandCycle", Cases.Single(x => x.Id == id).Expected);
        if (Environment.GetEnvironmentVariable(CycleScanVariable) == "1")
            await CheckStepLimits(id);
        else
            await CheckCorpus(id);
        await File.WriteAllTextAsync(Environment.GetEnvironmentVariable(CycleMarkerVariable)!, id);
    }

    /// <summary>The research's deliberately invalid shapes stay parse errors: <c>A() = R.Algorithm</c> (RA9/G11).</summary>
    [Fact]
    public void AnEmptyParameterListOverTheProjection_StaysAParseError()
        => Assert.True(Parser.Parse(Lib + "R = Capture(Square(5))\nA() = R.Algorithm\nA(9)").HasErrors);
}
