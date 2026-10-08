using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Q-16 G-O — owner-local Grace (decided 2026-10-07). The one law:
/// <para><b>Grace belongs to the owner whose written rows contain the marked occurrence</b> — the
/// innermost algorithm-level scope (the root, a property body, a brace block in any position, a
/// clause-branch body) whose output rows or deconstruction right-hand sides contain it, through
/// every transparent construct (<c>AstHelpers.WrittenRows</c>). <b>A marker is valid exactly when
/// that occurrence becomes one of the owner's OWN inferred parameters</b>; its weight is applied as
/// far as the ordering allows, and <b>saturation is never an error</b> (Q-16(1) E: eligibility, not
/// movement). A fixed binding has no inferred parameter for the weight to attach to and is
/// <see cref="DiagnosticCode.InvalidGraceMarker"/>, as is every marker on a closed level (a written
/// parameter list, a clause branch's own level). A clause branch is closed at its OWN level only:
/// an algorithm nested in it is an ordinary owner (Q-16(2) O) — in every spelling — whose inferred
/// parameters are supplied by its caller and never added to the branch.</para>
/// <para>Organized by law, not by ticket. Accepted programs are checked on the six established
/// routes (<see cref="SixRouteAgreement"/>; module programs on <see cref="ModuleRouteAgreement"/>),
/// signatures through the elaborated tree, rejections by code, reason and exact span. The
/// historical boundaries live beside this suite: <see cref="GraceEffectivenessTests"/> (F10),
/// <see cref="ConditionalBranchDeconstructionGraceTests"/> (PV-49), <see cref="GraceDotCompositionTests"/>.</para>
/// </summary>
public class GraceOwnershipSemanticsTests
{
    private const string Apply2 = "Apply(f) = f(1, 10)\n";
    private const string Apply1 = "Apply(f) = f(1)\n";

    // ── helpers ──────────────────────────────────────────────────────────────

    private static Algorithm.User Root(string source) => SourceProvenance.ParseValid(source).Root;

    private static Algorithm PropertyValue(Algorithm owner, string name)
        => Assert.Single(owner.Properties, p => p.Name == name).Value;

    private static IReadOnlyList<string> Params(string source, string property)
        => PropertyValue(Root(source), property).Params;

    private static Algorithm.User Branch(Algorithm family, int index)
        => Assert.IsType<Algorithm.User>(Assert.IsType<Algorithm.Conditional>(family).Branches[index].Body);

    /// <summary>The brace blocks written directly in an owner's rows (output and hoisted right-hand sides), depth first.</summary>
    private static List<Algorithm> InlineBlocks(Algorithm owner)
    {
        var blocks = new List<Algorithm>();
        foreach (var row in AstHelpers.WrittenRows(owner))
            Collect(row);
        return blocks;

        void Collect(Expr expr)
        {
            switch (expr)
            {
                case Expr.AlgorithmExpr(var algorithm):
                    blocks.Add(algorithm);
                    break;
                case Expr.Binary(_, var left, var right):
                    Collect(left);
                    Collect(right);
                    break;
                case Expr.Comparison(var first, var links):
                    Collect(first);
                    foreach (var link in links)
                        Collect(link.Operand);
                    break;
                case Expr.Unary(_, var operand):
                    Collect(operand);
                    break;
                case Expr.Index(var target, var selector):
                    Collect(target);
                    Collect(selector);
                    break;
                case Expr.SequenceSpread(var operand):
                    Collect(operand);
                    break;
                case Expr.ListLiteral(var items):
                    foreach (var item in items)
                        Collect(item);
                    break;
                case Expr.Capture(var body):
                    foreach (var item in body)
                        Collect(item);
                    break;
                case Expr.Call(var function, var args):
                    Collect(function);
                    foreach (var arg in args)
                        Collect(arg);
                    break;
                case Expr.DotCall dot:
                    Collect(dot.Target);
                    if (dot.Args is { } dotArgs)
                        foreach (var arg in dotArgs)
                            Collect(arg);
                    break;
            }
        }
    }

    private static async Task<string> ValueOnEveryRoute(string source)
    {
        SourceProvenance.ParseValid(source);
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "ok", $"expected success, got {observation}\nsource:\n{source}");
        return observation.Value!;
    }

    /// <summary>
    /// The one front-end report of a rejected marker: exactly one diagnostic in all, an
    /// <see cref="DiagnosticCode.InvalidGraceMarker"/> naming the marked name and the reason that
    /// fixed its binding — and the same structured failure, at the same span, on every route.
    /// </summary>
    private static async Task<Diagnostic> SingleGraceReport(string source, string name, string reason, SourceSpan? span = null)
    {
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.StartsWith($"Grace cannot reorder '{name}' because {reason}", diagnostic.Message, StringComparison.Ordinal);
        Assert.EndsWith("; remove the marker.", diagnostic.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("has no effect", diagnostic.Message, StringComparison.Ordinal);
        if (span is { } expected)
            Assert.Equal(expected, diagnostic.Span);

        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("parse", observation.Kind);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith($"{KatLangErrorCode.InvalidGraceMarker}: ", error, StringComparison.Ordinal);
        Assert.EndsWith($" @ {diagnostic.Span}", error, StringComparison.Ordinal);
        return diagnostic;
    }

    private const string ExplicitParameter = "it already resolves to an explicit parameter";
    private const string EnclosingParameter = "it already resolves to a parameter of an enclosing algorithm";
    private const string Property = "it already resolves to a property";
    private const string ClauseBinder = "it is a binder of this clause's head, which is the complete input specification of the branch";
    private const string BranchOwnLevel = "it stands on a clause branch's own level, where nothing is inferred";
    private const string ClosedList = "this algorithm's explicit parameter list fixes its parameters, so nothing is inferred at this level";

    // ── 1. Eligibility, not movement (Q-16(1) E): saturation is valid ───────────

    public static TheoryData<string, string, string[]> SaturatedMarkers() => new()
    {
        // singleton own parameter
        { "singleton-prefix", "F = ~x + 1", ["x"] },
        { "singleton-postfix", "F = x~ + 1", ["x"] },
        { "singleton-excess", "F = ~~x + 1", ["x"] },
        // already at the boundary the marker points to
        { "already-first-prefix", "F = ~x + y * 10", ["x", "y"] },
        { "already-last-postfix", "F = x + y~ * 10", ["x", "y"] },
        // excess weight on a name that is already first
        { "excess", "F = ~~x + y * 10", ["x", "y"] },
        // ties: an equal weight on the neighbour blocks the move
        { "tie-prefix", "F = ~x + ~y * 10", ["x", "y"] },
        { "tie-postfix", "F = x~ * 10 + y~", ["x", "y"] },
        // cancelled weight: one occurrence, and two occurrences of one name
        { "cancelled-one-occurrence", "F = ~x~ + y * 10", ["x", "y"] },
        { "cancelled-two-occurrences", "F = ~x + y * 10 + 0 * x~", ["x", "y"] },
        // the own/lifted boundary: lifted names always follow the owner's own names (PAR-05)
        { "lifted-tail", "A = p - q\nF = A - z~", ["z", "p", "q"] },
    };

    [Theory]
    [MemberData(nameof(SaturatedMarkers))]
    public void SaturatedMarker_IsValid_AndTheSignatureEqualsTheUngracedOne(string label, string definition, string[] expected)
    {
        _ = label;
        Assert.Equal(expected, Params(definition, "F"));
        Assert.Equal(expected, Params(definition.Replace("~", ""), "F"));
    }

    [Theory]
    [InlineData("F = ~x + 1\nF(3)", "4")]
    [InlineData("F = ~x + y * 10\nF(1, 2)", "21")]
    [InlineData("F = x + y~ * 10\nF(1, 2)", "21")]
    [InlineData("F = ~~x + y * 10\nF(1, 2)", "21")]
    [InlineData("F = ~x + ~y * 10\nF(1, 2)", "21")]
    [InlineData("F = ~x~ + y * 10\nF(1, 2)", "21")]
    [InlineData("A = p - q\nF = A - z~\nF(1, 2, 3)", "-2")]
    public async Task SaturatedMarker_EvaluatesLikeTheUngracedProgram(string source, string expected)
    {
        Assert.Equal(expected, await ValueOnEveryRoute(source));
        Assert.Equal(expected, await ValueOnEveryRoute(source.Replace("~", "")));
    }

    [Theory]
    // the same rule, applied where it can move the name
    [InlineData("F = y - ~x", new[] { "x", "y" })]
    [InlineData("F = y~ - x", new[] { "x", "y" })]
    [InlineData("F = a + 10 * b + 100 * ~~c", new[] { "c", "a", "b" })]
    [InlineData("F = a + 10 * b + 100 * ~c + ~c", new[] { "c", "a", "b" })]
    [InlineData("F = y * 10 + ~~x", new[] { "x", "y" })]
    [InlineData("F = x~~~ * 10 + y", new[] { "y", "x" })]
    public void MovingMarker_ReordersTheOwnSignature(string definition, string[] expected)
        => Assert.Equal(expected, Params(definition, "F"));

    [Fact]
    public void LiftedTail_IsNeverCrossed_InEitherDirection()
    {
        // Grace orders the owner's OWN names only; forwarded names are appended afterwards and are
        // never weighted, so neither a postfix marker on an own name nor a marker on another own
        // name can move anything into or out of the lifted tail.
        Assert.Equal(["z", "p", "q"], Params("A = p - q\nF = A - z~~~", "F"));
        Assert.Equal(["w", "z", "p", "q"], Params("A = p - q\nF = z * A + ~w", "F"));
        Assert.Equal(["z", "w", "p", "q"], Params("A = p - q\nF = z * A + w", "F"));
    }

    [Fact]
    public void AddingAnUnrelatedOwnParameter_NeverChangesWhetherAMarkerIsLegal()
    {
        // Under eligibility the verdict is a function of the marked occurrence alone: `~x` is legal
        // with or without a neighbour it could move past.
        SourceProvenance.ParseValid("F = ~x + 1");
        SourceProvenance.ParseValid("F = ~x + y");
        SourceProvenance.ParseValid("F = y + ~x");
        SourceProvenance.ParseValid("A = p - q\nF = ~x + A");
    }

    [Fact]
    public void X49Witness_FollowsFrontFirstMovement()
    {
        // X-49 (decided 2026-10-08): postfix movers take their turns first, from the last-occurring;
        // then prefix movers, from the first-occurring (PAR-06; GraceMovementLawTests pins the law).
        // b passes c, and c — displaced, but still owed its own turn — passes a: (c, a, b), as
        // without `b~`. Q-16's eligibility is unaffected; the other four orders were already these.
        Assert.Equal(["c", "a", "b"], Params("F = a * 100 + b~ * 10 + ~~c", "F"));
        Assert.Equal(["c", "a", "b"], Params("F = a * 100 + b * 10 + ~~c", "F"));
        Assert.Equal(["b", "c", "a"], Params("F = a~ * 100 + b * 10 + ~c", "F"));
        Assert.Equal(["b", "a", "c"], Params("F = a~ + b + c~", "F"));
        Assert.Equal(["c", "b", "a"], Params("F = a~~ + ~b + ~~c", "F"));
    }

    // ── 2. Fixed bindings stay invalid (F10) ─────────────────────────────────────

    public static TheoryData<string, string, string, string, int, int> FixedBindings() => new()
    {
        { "explicit-parameter", "F(a) = ~a + 1\nF(1)", "a", ExplicitParameter, 1, 8 },
        { "explicit-parameter-cancelled", "F(a) = ~a~ + 1\nF(1)", "a", ExplicitParameter, 1, 8 },
        { "enclosing-parameter", "Outer(a) = {\n    Inner = ~a + x\n    Inner(1)\n}\nOuter(2)", "a", EnclosingParameter, 2, 13 },
        { "visible-property", "Rate = 3\nF = ~Rate + x\nF(1)", "Rate", Property, 2, 5 },
        { "builtin", "F = ~count((1, 2)) + x\nF(1)", "count", "it already resolves to the builtin 'count'", 1, 5 },
        { "math-alias-builtin", "F = ~pi * r\nF(2)", "pi", "it already resolves to the builtin 'pi'", 1, 5 },
        { "opened-property", "Lib = { public V = 1 }\nK = {\n    open Lib\n    ~V + x\n}\nK(1)", "V", "it already resolves to an opened property", 4, 5 },
        { "structural-member", "Obj = {\n    public V = 42\n    0\n}\nObj.~V", "V", "the member 'V' always resolves structurally on its receiver", 5, 5 },
        { "dot-string-intrinsic", "v = 5\nK = v.~string\nK", "string", "'.string' is the dot-only intrinsic on this receiver", 2, 7 },
    };

    [Theory]
    [MemberData(nameof(FixedBindings))]
    public async Task FixedBinding_IsInvalid_WithTheReasonThatFixedIt(
        string label, string source, string name, string reason, int line, int column)
    {
        _ = label;
        var diagnostic = await SingleGraceReport(source, name, reason);
        Assert.Equal(line, diagnostic.Span!.Value.Start.Line);
        Assert.Equal(column, diagnostic.Span!.Value.Start.Column);
    }

    [Fact]
    public void ClosedExplicitList_FreeName_ReportsTheUndeclaredNameAndTheClosedLevel()
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError("K(b) = b + ~a\nK(1)");
        Assert.Equal([DiagnosticCode.UndeclaredIdentifier, DiagnosticCode.InvalidGraceMarker], diagnostics.Select(d => d.Code).ToArray());
        Assert.StartsWith($"Grace cannot reorder 'a' because {ClosedList}", diagnostics[1].Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(1, 12, 1, 14), diagnostics[1].Span);
    }

    [Fact]
    public async Task OpenedName_IsFixed_WhileAnUnprovidedName_IsTheOwnersOwn()
    {
        // Ownership-first resolution decides first: an opened member is a fixed binding, while a
        // name the opened provider does NOT declare is this owner's free inferred name.
        await SingleGraceReport(
            "Lib = { public V = 1 }\nK = {\n    open Lib\n    x - ~V\n}\nK(1)", "V", "it already resolves to an opened property");
        const string free = "Lib = { public W = 1 }\nK = {\n    open Lib\n    x - ~V\n}\nK(1, 10)";
        Assert.Equal(["V", "x"], Params(free, "K"));
        Assert.Equal("9", await ValueOnEveryRoute(free));
    }

    // ── 3. A clause branch is closed at its OWN level (PAT-04) ──────────────────

    [Theory]
    [InlineData("own-output-row", "F(0) = 0\nF(n) = ~n + 1\nF(1)", "n", ClauseBinder, 2, 8, 2, 10)]
    [InlineData("own-postfix-row", "F(0) = 0\nF(n) = n~ + 1\nF(1)", "n", ClauseBinder, 2, 8, 2, 10)]
    [InlineData("own-deconstruction-rhs", "F(0) = 0\nF(n) = {\n    a, b = (~n, 1)\n    a + b\n}\nF(5)", "n", ClauseBinder, 3, 13, 3, 15)]
    [InlineData("own-row-visible-property", "Rate = 3\nF(0) = 0\nF(n) = ~Rate + n\nF(1)", "Rate", Property, 3, 8, 3, 13)]
    [InlineData("own-row-dot-receiver", "F(0) = 0\nF(n) = n~.count\nF(1)", "n", ClauseBinder, 2, 8, 2, 10)]
    [InlineData("single-literal-clause", "F(0) = ~q0 + 1\nF(0)", "q0", BranchOwnLevel, 1, 8, 1, 11)]
    public async Task BranchOwnLevel_IsClosed(
        string label, string source, string name, string reason, int line, int column, int endLine, int endColumn)
    {
        _ = label;
        if (reason == BranchOwnLevel)
        {
            // A free name on the branch's own level is undeclared too (the full-input rule).
            var diagnostics = SourceProvenance.ExpectFrontEndError(source);
            Assert.Equal([DiagnosticCode.UndeclaredIdentifier, DiagnosticCode.InvalidGraceMarker], diagnostics.Select(d => d.Code).ToArray());
            Assert.StartsWith($"Grace cannot reorder '{name}' because {reason}", diagnostics[1].Message, StringComparison.Ordinal);
            Assert.Contains("An algorithm nested inside the branch may use Grace", diagnostics[1].Message, StringComparison.Ordinal);
            Assert.Equal(new SourceSpan(line, column, endLine, endColumn), diagnostics[1].Span);
            return;
        }

        await SingleGraceReport(source, name, reason, new SourceSpan(line, column, endLine, endColumn));
    }

    [Fact]
    public void BranchHead_GraceIsAPatternGrammarError()
    {
        // The head is a pattern, never an expression: the parser keeps that rule.
        var diagnostic = Assert.Single(Parser.ParseSyntax("F(0) = 0\nF(~n) = n\nF(1)").Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Contains("Grace is not allowed in clause-head patterns", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    // `{ … }` (and its redundant group `({ … })`) written as the WHOLE definition body IS the
    // branch body: its rows are the branch's own rows, closed. Only a block written inside the
    // body is a nested owner.
    [InlineData("G(0) = 0\nG(k) = { y - ~x }\nG(1)")]
    [InlineData("G(0) = 0\nG(k) = ({ y - ~x })\nG(1)")]
    public void BodyMerge_TheBracedBodyIsTheBranchsOwnLevel(string source)
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError(source);
        Assert.Equal(
            [DiagnosticCode.UndeclaredIdentifier, DiagnosticCode.UndeclaredIdentifier, DiagnosticCode.InvalidGraceMarker],
            diagnostics.Select(d => d.Code).ToArray());
        Assert.StartsWith($"Grace cannot reorder 'x' because {BranchOwnLevel}", diagnostics[2].Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Branch_NeverGainsAParameter_FromAnOwnerNestedInIt()
    {
        var root = Root(Apply2 + "F(0) = Apply({ y - ~x })");
        var branch = Branch(PropertyValue(root, "F"), 0);
        Assert.Empty(branch.Params);
        Assert.Equal(["x", "y"], Assert.Single(InlineBlocks(branch)).Params);

        var named = Root(Apply2 + "F(0) = {\n    B = y - ~x\n    Apply(B)\n}");
        var namedBranch = Branch(PropertyValue(named, "F"), 0);
        Assert.Empty(namedBranch.Params);
        Assert.Equal(["x", "y"], PropertyValue(namedBranch, "B").Params);
    }

    [Fact]
    public async Task ValuePositionBlock_InABranch_IsFrontEndValid_AndFailsAtRunTimeLikeItsUngracedTwin()
    {
        // G-O injects nothing: the inner block owns `(x, y)`, and demanding its value with no
        // arguments is the ordinary run-time failure, exactly as without the marker.
        foreach (var source in new[] { "G(k) = { { y - ~x } }\nG(1)", "G(0) = 0\nG(k) = { { y - ~x } }\nG(1)" })
        {
            var graced = await SixRouteAgreement.OnEveryRouteAsync(source);
            var ungraced = await SixRouteAgreement.OnEveryRouteAsync(source.Replace("~", ""));
            Assert.Equal("err", graced.Kind);
            Assert.Equal("err", ungraced.Kind);
            Assert.StartsWith($"{KatLangErrorCode.UnresolvedImplicitParams}: ", Assert.Single(graced.Errors), StringComparison.Ordinal);
            Assert.StartsWith($"{KatLangErrorCode.UnresolvedImplicitParams}: ", Assert.Single(ungraced.Errors), StringComparison.Ordinal);
        }
    }

    // ── 4. Nested owners are ordinary (Q-16(2) O), in every spelling ────────────

    public static TheoryData<string, string, string, string> NestedOwnerSpellings() => new()
    {
        { "call-argument", Apply2 + "G(0) = 0\nG(k) = Apply({ y - ~x }) + k\nG(1)", "10", "-8" },
        { "grouped-call-argument", Apply2 + "G(0) = 0\nG(k) = Apply(({ y - ~x })) + k\nG(1)", "10", "-8" },
        { "trailing-brace-callback", Apply2 + "G(0) = 0\nG(k) = Apply{ y - ~x } + k\nG(1)", "10", "-8" },
        { "dot-receiver", Apply2 + "G(0) = 0\nG(k) = { y - ~x }.Apply + k\nG(1)", "10", "-8" },
        { "grouped-dot-receiver", Apply2 + "G(0) = 0\nG(k) = ({ y - ~x }).Apply + k\nG(1)", "10", "-8" },
        { "dot-argument", "Apply2(a, f) = f(a, 10)\nG(0) = 0\nG(k) = 1.Apply2({ y - ~x }) + k\nG(1)", "10", "-8" },
        { "reduce-callback", "G(0) = 0\nG(k) = reduce([1, 2, 3], { b * 10 + ~a }, 0) + k\nG(1)", "124", "61" },
        // A one-parameter callback: the marker is valid saturation.
        { "map-callback-saturated", "G(0) = 0\nG(k) = map([1, 2], { ~x * 10 })\nG(1)", "L[10, 20]", "L[10, 20]" },
        { "if-slot", Apply2 + "G(0) = 0\nG(k) = if(k > 0, Apply({ y - ~x }), 0)\nG(1)", "9", "-9" },
        { "branch-deconstruction-rhs", Apply2 + "G(0) = 0\nG(k) = {\n    a, b = (Apply({ y - ~x }), k)\n    a + b\n}\nG(1)", "10", "-8" },
        { "block-own-deconstruction", Apply2 + "G(0) = 0\nG(k) = Apply({ a, b = (y, ~x)\n    a - b }) + k\nG(1)", "10", "-8" },
        { "block-local-property", Apply2 + "G(0) = 0\nG(k) = Apply({ B = y - ~x\n    B }) + k\nG(1)", "10", "-8" },
        { "block-in-block", Apply2 + "G(0) = 0\nG(k) = { Apply({ y - ~x }) } + k\nG(1)", "10", "-8" },
        { "named-property", Apply2 + "G(0) = 0\nG(k) = {\n    B = y - ~x\n    Apply(B) + k\n}\nG(1)", "10", "-8" },
        { "property-returning-block", Apply2 + "G(0) = 0\nG(k) = {\n    P = { y - ~x }\n    Apply(P) + k\n}\nG(1)", "10", "-8" },
        { "property-output-call", Apply2 + "G(0) = 0\nG(k) = {\n    P = Apply({ y - ~x })\n    P + k\n}\nG(1)", "10", "-8" },
        { "passed-through-another-algorithm", Apply2 + "Pass(f) = Apply(f)\nG(0) = 0\nG(k) = Pass({ y - ~x }) + k\nG(1)", "10", "-8" },
        { "nested-family-branch-inline", Apply2 + "G(0) = 0\nG(k) = {\n    H(0) = Apply({ y - ~x })\n    H(m) = m\n    H(k - 1) + k\n}\nG(1)", "10", "-8" },
        { "nested-family-branch-named", Apply2 + "G(0) = 0\nG(k) = {\n    H(0) = {\n        B = y - ~x\n        Apply(B)\n    }\n    H(m) = m\n    H(k - 1) + k\n}\nG(1)", "10", "-8" },
        { "depth-3", Apply2 + "G(0) = 0\nG(k) = {\n    H(0) = {\n        P = {\n            Q = y - ~x\n            Apply(Q)\n        }\n        P\n    }\n    H(m) = m\n    H(k - 1) + k\n}\nG(1)", "10", "-8" },
    };

    [Theory]
    [MemberData(nameof(NestedOwnerSpellings))]
    public async Task NestedInferredOwner_InABranch_OwnsItsGrace(string label, string source, string expected, string ungraced)
    {
        _ = label;
        Assert.Equal(expected, await ValueOnEveryRoute(source));
        // Without the marker the same owner binds in first-occurrence order.
        Assert.Equal(ungraced, await ValueOnEveryRoute(source.Replace("~", "")));
    }

    [Theory]
    // Value positions: the block is front-end valid (its Grace is its own) and demanding its value
    // with no arguments fails at run time with the same structured error as the ungraced block.
    [InlineData(Apply2 + "G(0) = 0\nG(k) = Apply({ y - ~x }*)\nG(1)")]
    [InlineData("G(0) = 0\nG(k) = [{ y - ~x }]\nG(1)")]
    [InlineData("G(0) = 0\nG(k) = {\n    { y - ~x }\n}\nG(1)")]
    public async Task NestedOwner_InAValuePosition_IsValid_AndFailsLikeItsUngracedTwin(string source)
    {
        SourceProvenance.ParseValid(source);
        var graced = await SixRouteAgreement.OnEveryRouteAsync(source);
        var ungraced = await SixRouteAgreement.OnEveryRouteAsync(source.Replace("~", ""));
        Assert.Equal("err", graced.Kind);
        Assert.Equal("err", ungraced.Kind);
        Assert.Equal(
            Assert.Single(ungraced.Errors).Split(':')[0],
            Assert.Single(graced.Errors).Split(':')[0]);
    }

    [Fact]
    public async Task InlineAndNamed_SpellingsOfOneOwner_Agree()
    {
        // Ten spellings of ONE nested owner in a family branch: one verdict, one owner signature,
        // one value (formerly the inline spellings were rejected and the named ones accepted, X-08).
        string[] spellings =
        [
            "G(k) = Apply({ y - ~x }) + k",
            "G(k) = Apply(({ y - ~x })) + k",
            "G(k) = Apply{ y - ~x } + k",
            "G(k) = { y - ~x }.Apply + k",
            "G(k) = {\n    B = y - ~x\n    Apply(B) + k\n}",
            "G(k) = {\n    P = { y - ~x }\n    Apply(P) + k\n}",
            "G(k) = {\n    P = Apply({ y - ~x })\n    P + k\n}",
            "G(k) = Apply({ B = y - ~x\n    B }) + k",
            "G(k) = Apply({ a, b = (y, ~x)\n    a - b }) + k",
            "G(k) = { Apply({ y - ~x }) } + k",
        ];
        foreach (var spelling in spellings)
            Assert.Equal("10", await ValueOnEveryRoute(Apply2 + "G(0) = 0\n" + spelling + "\nG(1)"));
    }

    [Fact]
    public async Task SingleClause_AndFamily_AgreeOnTheNestedOwner()
    {
        // Adding a sibling clause turns G into a family; it must not change the nested owner.
        const string single = Apply2 + "G(k) = Apply({ y - ~x }) + k\nG(1)";
        const string family = Apply2 + "G(0) = 0\nG(k) = Apply({ y - ~x }) + k\nG(1)";
        Assert.Equal(await ValueOnEveryRoute(single), await ValueOnEveryRoute(family));
        var singleBlock = Assert.Single(InlineBlocks(PropertyValue(Root(single), "G")));
        var familyBlock = Assert.Single(InlineBlocks(Branch(PropertyValue(Root(family), "G"), 1)));
        Assert.Equal(singleBlock.Params, familyBlock.Params);
        Assert.Equal(["x", "y"], familyBlock.Params);

        // ... and the same holds for a rejected nested marker: one identical report either way.
        var singleReport = await SingleGraceReport(Apply1 + "G(k) = Apply({ x - ~k })\nG(1)", "k", EnclosingParameter);
        var familyReport = await SingleGraceReport(Apply1 + "G(0) = 0\nG(k) = Apply({ x - ~k })\nG(1)", "k", EnclosingParameter);
        Assert.Equal(singleReport.Message, familyReport.Message);
        Assert.Equal(singleReport.Span!.Value.Start.Column, familyReport.Span!.Value.Start.Column);
    }

    [Fact]
    public async Task NestedOwner_UnderAClosedExplicitList_OwnsItsGrace()
    {
        // X-39's witness: closedness is per level.
        Assert.Equal("-4", await ValueOnEveryRoute("F(y) = {\n    G = w - ~z\n    G(5, 1)\n}\nF(0)"));
        Assert.Equal("10", await ValueOnEveryRoute("Outer(a) = {\n    Inner = y - ~x\n    Inner(1, 10) + a\n}\nOuter(1)"));
        Assert.Equal("10", await ValueOnEveryRoute(Apply2 + "Outer(a) = Apply({ y - ~x }) + a\nOuter(1)"));
    }

    [Fact]
    public async Task NestedFamily_EveryBranchOwnLevelIsClosed_AtEveryDepth()
    {
        await SingleGraceReport(
            "G(0) = 0\nG(k) = {\n    H(0) = 0\n    H(m) = ~m + 1\n    H(k)\n}\nG(1)", "m", ClauseBinder, new SourceSpan(4, 12, 4, 14));
        await SingleGraceReport(
            "Outer = {\n    H(0) = 0\n    H(m) = ~m\n    H(1)\n}\nOuter", "m", ClauseBinder, new SourceSpan(3, 12, 3, 14));
        // A family nested in a family nested in a branch: still closed at its own level.
        await SingleGraceReport(
            "G(0) = 0\nG(k) = {\n    H(0) = 0\n    H(m) = {\n        J(0) = 0\n        J(r) = r~\n        J(m)\n    }\n    H(k)\n}\nG(1)",
            "r", ClauseBinder, new SourceSpan(6, 16, 6, 18));
    }

    // ── 5. A nested owner never re-categorizes a capture or a fixed binding ─────

    [Theory]
    [InlineData("inline", "F(0) = 0\nF(n) = Apply({ x - ~n })\nF(1)", 2, 20)]
    [InlineData("named", "F(0) = 0\nF(n) = {\n    B = x - ~n\n    Apply(B)\n}\nF(1)", 3, 13)]
    [InlineData("block-deconstruction", "F(0) = 0\nF(n) = Apply({\n    c, d = (~n, x)\n    c + d\n})\nF(1)", 3, 13)]
    [InlineData("nested-family", "F(0) = 0\nF(n) = {\n    H(0) = Apply({ x - ~n })\n    H(m) = m\n    H(n - 1)\n}\nF(1)", 3, 24)]
    public async Task CapturedBranchBinder_InANestedOwner_IsOneEnclosingParameterReport(string label, string body, int line, int column)
    {
        _ = label;
        var diagnostic = await SingleGraceReport(Apply1 + body, "n", EnclosingParameter);
        Assert.Equal(line + 1, diagnostic.Span!.Value.Start.Line);
        Assert.Equal(column, diagnostic.Span!.Value.Start.Column);
        // It stays the branch's binder for the editor too: never the block's own parameter.
        var model = SemanticModelBuilder.Build(Parser.Parse(Apply1 + body));
        Assert.Equal(
            IdentifierClassification.ConditionalBinderReference,
            model.FindResolutionAt(new SourcePosition(line + 1, column + 1))!.Classification);
    }

    [Theory]
    [InlineData("inline", "Rate = 3\nF(0) = 0\nF(n) = Apply({ x + ~Rate }) + n\nF(1)")]
    [InlineData("named", "Rate = 3\nF(0) = 0\nF(n) = {\n    B = x + ~Rate\n    Apply(B) + n\n}\nF(1)")]
    public async Task VisibleProperty_InANestedOwner_IsOnePropertyReport_InEitherSpelling(string label, string body)
    {
        _ = label;
        await SingleGraceReport(Apply1 + body, "Rate", Property);
    }

    [Theory]
    [InlineData("inline", "F = x * 100 + Apply({ y - ~x })\nF(5)", 1, 27)]
    [InlineData("inline-postfix", "F = x * 100 + Apply({ x~ - y })\nF(5)", 1, 23)]
    [InlineData("enclosing-use-after-the-block", "F = Apply({ y - ~x }) + x * 100\nF(5)", 1, 17)]
    [InlineData("named", "F = {\n    P = y - ~x\n    x * 100 + Apply(P)\n}\nF(5)", 2, 13)]
    [InlineData("in-a-branch", "G(0) = 0\nG(k) = {\n    B = x * 100 + Apply({ y - ~x })\n    B(5) + k\n}\nG(1)", 3, 31)]
    public async Task InferredParameterOfAnEnclosingOwner_IsACaptureInANestedOwner_NeverItsOwn(
        string label, string body, int line, int column)
    {
        // A free name belongs to the OUTERMOST inferring owner whose own rows use it (PAR-03). Once the
        // enclosing owner uses `x` itself, `x` inside the nested owner is that owner's CAPTURE — a fixed
        // binding exactly like a written enclosing parameter — so the marker has no OWN inferred
        // parameter to weight, wherever the enclosing use stands and in either nested spelling.
        _ = label;
        var diagnostic = await SingleGraceReport(Apply2 + body, "x", EnclosingParameter);
        Assert.Equal(line + 1, diagnostic.Span!.Value.Start.Line);
        Assert.Equal(column, diagnostic.Span!.Value.Start.Column);
    }

    [Theory]
    [InlineData("builtin", Apply1 + "G(0) = 0\nG(k) = Apply({ ~count((1, 2)) + x }) + k\nG(1)",
        "count", "it already resolves to the builtin 'count'", 3, 16)]
    [InlineData("dot-string", Apply1 + "v = 5\nG(0) = 0\nG(k) = Apply({ v.~string + x }) + k\nG(1)",
        "string", "'.string' is the dot-only intrinsic on this receiver", 4, 18)]
    [InlineData("structural-member", "Obj = { public V = 42 }\n" + Apply1 + "G(0) = 0\nG(k) = Apply({ Obj.~V + x }) + k\nG(1)",
        "V", "the member 'V' always resolves structurally on its receiver", 4, 20)]
    [InlineData("opened-name", "Lib = { public V = 1 }\n" + Apply1 + "G(0) = 0\nG(k) = Apply({\n    open Lib\n    ~V + x\n}) + k\nG(1)",
        "V", "it already resolves to an opened property", 6, 5)]
    public async Task FixedBinding_InANestedOwnerOfABranch_StaysFixed(
        string label, string source, string name, string reason, int line, int column)
    {
        // Being written inside an inferring block nested in a branch never makes a resolved binding
        // eligible: the block infers only the names nothing binds (`x`), and the marker on the fixed
        // name is the one report, at the written marker.
        _ = label;
        var diagnostic = await SingleGraceReport(source, name, reason);
        Assert.Equal(line, diagnostic.Span!.Value.Start.Line);
        Assert.Equal(column, diagnostic.Span!.Value.Start.Column);
    }

    [Fact]
    public async Task WithoutTheEnclosingUse_TheSameNameIsTheNestedOwnersOwn()
    {
        // The control for the captures above: when only the block's rows use `x`, it is the BLOCK's own
        // inferred parameter, the marker is valid, and the enclosing owner gains nothing.
        const string source = Apply2 + "F = Apply({ y - ~x })\nF";
        var f = PropertyValue(Root(source), "F");
        Assert.Empty(f.Params);
        Assert.Equal(["x", "y"], Assert.Single(InlineBlocks(f)).Params);
        Assert.Equal("9", await ValueOnEveryRoute(source));
        Assert.Equal("10", await ValueOnEveryRoute(Apply2 + "G(0) = 0\nG(k) = {\n    B = Apply({ y - ~x })\n    B + k\n}\nG(1)"));
    }

    [Fact]
    public async Task NestedExplicitListAlgorithm_IsAClosedOwnerOfItsOwn()
    {
        await SingleGraceReport(
            Apply2 + "G(0) = 0\nG(k) = {\n    B(x, y) = y - ~x\n    Apply(B) + k\n}\nG(1)", "x", ExplicitParameter, new SourceSpan(4, 19, 4, 21));
    }

    [Fact]
    public async Task NestedOwner_LiftingFromACallee_KeepsTheOwnLiftedBoundary()
    {
        const string source = "A = p - q\nG(0) = 0\nG(k) = {\n    B = A * 10 + z~\n    B(1, 2, 3) + k\n}\nG(1)";
        Assert.Equal(["z", "p", "q"], PropertyValue(Branch(PropertyValue(Root(source), "G"), 1), "B").Params);
        Assert.Equal("-8", await ValueOnEveryRoute(source));
    }

    // ── 6. Hoisting never decides ownership (PV-49 preserved) ────────────────────

    [Fact]
    public async Task DeconstructionRightHandSide_BelongsToTheBodyThatWritesIt()
    {
        // The branch's OWN right-hand side: closed (PV-49) — exactly like the branch's own row.
        var ownRow = await SingleGraceReport("F(0) = 0\nF(n) = {\n    (~n, 1)\n}\nF(5)", "n", ClauseBinder);
        var ownRhs = await SingleGraceReport("F(0) = 0\nF(n) = {\n    a, b = (~n, 1)\n    a + b\n}\nF(5)", "n", ClauseBinder);
        Assert.Equal(ownRow.Message, ownRhs.Message);

        // A NESTED block's right-hand side: the block's own row — its own inferred name is valid,
        // and agrees with the same marker in the block's output.
        const string blockOutput = Apply2 + "F(0) = 0\nF(n) = Apply({ y - ~x }) + n\nF(1)";
        const string blockRhs = Apply2 + "F(0) = 0\nF(n) = Apply({\n    a, b = (y, ~x)\n    a - b\n}) + n\nF(1)";
        Assert.Equal(await ValueOnEveryRoute(blockOutput), await ValueOnEveryRoute(blockRhs));
        Assert.Equal(
            Assert.Single(InlineBlocks(Branch(PropertyValue(Root(blockOutput), "F"), 1))).Params,
            Assert.Single(InlineBlocks(Branch(PropertyValue(Root(blockRhs), "F"), 1))).Params);
    }

    // ── 7. Grace orders parameters only: dot, groups, resolution ────────────────

    [Fact]
    public async Task Dot_GraceNeverChangesSelection_InANestedOwnerToo()
    {
        // `o` is the block's only own parameter: saturated, valid; Obj's structural V is read.
        const string receiver = "V(x) = 99\nObj = { public V = 42 }\nApplyObj(f) = f(Obj)\nG(0) = 0\nG(k) = ApplyObj({ o~.V }) + k\nG(1)";
        Assert.Equal("43", await ValueOnEveryRoute(receiver));
        // Both dot forms infer (t, a) inside a nested owner exactly as at top level.
        const string applyCallable = "Apply(f) = f({ x + 1 }, 7)\nG(0) = 0\n";
        Assert.Equal("9", await ValueOnEveryRoute(applyCallable + "G(k) = Apply({ a~.t }) + k\nG(1)"));
        Assert.Equal("9", await ValueOnEveryRoute(applyCallable + "G(k) = Apply({ a.~t }) + k\nG(1)"));
        // A member the receiver is known to declare is fixed in a nested owner as well.
        await SingleGraceReport(
            "Obj = { public V = 42 }\nApply(f) = f(1)\nG(0) = 0\nG(k) = Apply({ Obj.~V + x }) + k\nG(1)",
            "V", "the member 'V' always resolves structurally on its receiver");
    }

    [Fact]
    public async Task RedundantGroups_AreTransparentToGrace()
    {
        Assert.Equal(Params("V(x) = x * 2\nF = b + ~a.V", "F"), Params("V(x) = x * 2\nF = b + (~a).V", "F"));
        Assert.Equal(["y", "x"], Params("F = y, (~x~)", "F"));
        Assert.Equal(await ValueOnEveryRoute(Apply2 + "G(0) = 0\nG(k) = Apply({ y - ~x }) + k\nG(1)"),
            await ValueOnEveryRoute(Apply2 + "G(0) = 0\nG(k) = Apply(({ y - ~x })) + k\nG(1)"));
        await SingleGraceReport("F(0) = 0\nF(n) = (~n) + 1\nF(1)", "n", ClauseBinder, new SourceSpan(2, 9, 2, 11));
    }

    [Fact]
    public void Grace_NeverChangesResolution()
    {
        // A graced name resolves exactly like the plain one: a property stays the property (and
        // the marker is rejected), a free name stays the owner's parameter.
        var graced = SourceProvenance.ParseAllowingDiagnostics("X = 1\nK = ~X + y\nK");
        Assert.Equal(["y"], PropertyValue(graced.Root, "K").Params);
        Assert.Equal(["y"], Params("X = 1\nK = X + y", "K"));
    }

    // ── 8. Exact spans, one report per marker ────────────────────────────────────

    [Theory]
    [InlineData("F(a) = ~a + 1", 1, 8, 1, 10)]
    [InlineData("F(a) = a~ + 1", 1, 8, 1, 10)]
    [InlineData("F(a) = ~~a + 1", 1, 8, 1, 11)]
    [InlineData("F(a) = a~~ + 1", 1, 8, 1, 11)]
    [InlineData("F(a) = (~a) + 1", 1, 9, 1, 11)]
    [InlineData("F(0) = 0\nF(a) = ~~a + 1", 2, 8, 2, 11)]
    [InlineData("F(0) = 0\nF(a) = (a~) + 1", 2, 9, 2, 11)]
    [InlineData("Obj = { public V = 1 }\nF(0) = 0\nF(a) = Obj.~V + a", 3, 12, 3, 14)]
    [InlineData("F(0) = 0\nF(a) = {\n    p, q = (1, ~~a)\n    p + q\n}", 3, 16, 3, 19)]
    [InlineData("Apply(f) = f(1)\nF(0) = 0\nF(a) = Apply({\n    p, q = (x, a~)\n    p + q\n})", 4, 16, 4, 18)]
    public void Report_IsAtTheWrittenMarker(string source, int line, int column, int endLine, int endColumn)
    {
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal(new SourceSpan(line, column, endLine, endColumn), diagnostic.Span);
    }

    [Fact]
    public void EveryRejectedMarker_IsReportedOnce_AtItsOwnSpan()
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError("F(0) = 0\nF(n) = ~n + n~\nF(1)");
        Assert.Equal(2, diagnostics.Count);
        Assert.All(diagnostics, d => Assert.Equal(DiagnosticCode.InvalidGraceMarker, d.Code));
        Assert.Equal(new SourceSpan(2, 8, 2, 10), diagnostics[0].Span);
        Assert.Equal(new SourceSpan(2, 13, 2, 15), diagnostics[1].Span);
    }

    // ── 9. Front-end timing: eager units, deferred units ─────────────────────────

    [Fact]
    public async Task OrdinaryBranch_IsValidatedBeforeEvaluation_EvenWhenNotSelected()
    {
        // An eagerly elaborated branch is front-end validated whether or not evaluation selects it.
        var observation = await SixRouteAgreement.OnEveryRouteAsync("G(0) = 0\nG(k) = ~k + 1\nG(0)");
        Assert.Equal("parse", observation.Kind);
        Assert.StartsWith($"{KatLangErrorCode.InvalidGraceMarker}: ", Assert.Single(observation.Errors), StringComparison.Ordinal);
    }

    [Fact]
    public async Task ValidNestedMarker_InAnUnselectedBranch_ExecutesNothing()
    {
        const string body = Apply2 + "G(0) = 0\nG(k) = Apply({ trace(y) - ~x }) + k\n";
        var unselected = await SixRouteAgreement.OnEveryRouteAsync(body + "G(0)");
        Assert.Equal(("ok", "0"), (unselected.Kind, unselected.Value));
        Assert.Empty(unselected.HostCalls);
        var selected = await SixRouteAgreement.OnEveryRouteAsync(body + "G(1)");
        Assert.Equal(("ok", "10"), (selected.Kind, selected.Value));
        Assert.Equal(["trace(10)"], selected.HostCalls);
    }

    private const string ModuleUrl = "https://mods.test/g0.kat";

    private static ModuleRouteAgreement.Modules ModuleServer() => new((ModuleUrl, "public G = y - x"));

    [Fact]
    public async Task LoadBearingBranch_OwnLevelMarker_IsReportedWhenTheDeferredUnitIsSelected()
    {
        // MOD-10 / Q-61: a load-bearing branch is ONE deferred compilation unit, elaborated and
        // validated when selected — its own-level Grace verdict included, like its other errors.
        const string body = "G(0) = 0\nG(k) = {\n    M = load('" + ModuleUrl + "')\n    ~k + M.G(1, 2)\n}\n";

        var unselectedServer = ModuleServer();
        var unselected = await ModuleRouteAgreement.OnEveryRouteAsync(
            body + "G(0)", () => unselectedServer, ModuleRouteAgreement.AsyncRoutes);
        Assert.Equal(("ok", "0"), (unselected.Kind, unselected.Value));
        // Never materialized merely to report the marker.
        Assert.Empty(unselectedServer.Fetches);

        var selected = await ModuleRouteAgreement.OnEveryRouteAsync(body + "G(1)", ModuleServer, ModuleRouteAgreement.AsyncRoutes);
        Assert.Equal("err", selected.Kind);
        var error = Assert.Single(selected.Errors);
        Assert.StartsWith($"{KatLangErrorCode.InvalidGraceMarker}: ", error, StringComparison.Ordinal);
        Assert.Contains($"Grace cannot reorder 'k' because {ClauseBinder}", error, StringComparison.Ordinal);
        Assert.EndsWith($" @ {new SourceSpan(4, 5, 4, 7)}", error, StringComparison.Ordinal);
    }

    [Fact]
    public async Task LoadBearingBranch_NestedOwner_OwnsItsGrace_WhenSelected()
    {
        var selected = await ModuleRouteAgreement.OnEveryRouteAsync(
            Apply2 + "G(0) = 0\nG(k) = {\n    M = load('" + ModuleUrl + "')\n    Apply({ y - ~x }) + M.G(1, 2)\n}\nG(1)",
            ModuleServer,
            ModuleRouteAgreement.AsyncRoutes);
        Assert.Equal(("ok", "8"), (selected.Kind, selected.Value));
    }

    // ── 10. Loaded and inlined owners follow their own ownership ─────────────────

    [Fact]
    public async Task ModuleMember_AndInlinedMember_OwnTheirGraceAlike()
    {
        const string url = "https://mods.test/g1.kat";
        ModuleRouteAgreement.Modules Server() => new((url, "public G = y - ~x"));
        var loaded = await ModuleRouteAgreement.OnEveryRouteAsync("M = load('" + url + "')\nM.G(1, 10)", Server);
        Assert.Equal(("ok", "9"), (loaded.Kind, loaded.Value));
        Assert.Equal("9", await ValueOnEveryRoute("M = { public G = y - ~x }\nM.G(1, 10)"));

        // Inside a family branch too (the branch loading the module is a deferred unit).
        var inBranch = await ModuleRouteAgreement.OnEveryRouteAsync(
            "G(0) = 0\nG(k) = {\n    M = load('" + url + "')\n    M.G(1, 10) + k\n}\nG(1)", Server, ModuleRouteAgreement.AsyncRoutes);
        Assert.Equal(("ok", "10"), (inBranch.Kind, inBranch.Value));
        Assert.Equal("10", await ValueOnEveryRoute("G(0) = 0\nG(k) = {\n    M = { public G = y - ~x }\n    M.G(1, 10) + k\n}\nG(1)"));
    }

    [Fact]
    public async Task ModuleProvidedName_IsAFixedBinding_InsideTheModule()
    {
        // A module's own property is a binding of the module's member, so its marker is rejected
        // there — reported at the import site (one coordinate space per result).
        const string url = "https://mods.test/g4.kat";
        var parsed = await Parser.ParseAsync(
            "M = load('" + url + "')\nM.G(1)",
            new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("Rate = 3\npublic G = x + ~Rate"), AllowedHosts = ["mods.test"] });
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.StartsWith($"Grace cannot reorder 'Rate' because {Property}", diagnostic.Message, StringComparison.Ordinal);
    }

    // ── 11. The editor agrees with the detector ──────────────────────────────────

    [Theory]
    [InlineData("F(0) = 0\nF(n) = ~n + 1", 2, 9, IdentifierClassification.ConditionalBinderReference)]
    [InlineData("Apply(f) = f(1)\nF(0) = 0\nF(n) = Apply({ x - ~n })", 3, 21, IdentifierClassification.ConditionalBinderReference)]
    [InlineData("Rate = 3\nApply(f) = f(1)\nF(0) = 0\nF(n) = Apply({ x + ~Rate }) + n", 4, 21, IdentifierClassification.PropertyReference)]
    [InlineData("F(a) = ~a + 1", 1, 9, IdentifierClassification.ExplicitParameterReference)]
    public void RejectedMarker_ClassifiesInTheEditorAsTheBindingItsReasonNames(
        string source, int line, int column, IdentifierClassification classification)
    {
        var parsed = Parser.Parse(source);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, Assert.Single(parsed.Diagnostics).Code);
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Equal(classification, model.FindResolutionAt(new SourcePosition(line, column))!.Classification);
    }

    [Fact]
    public void ValidNestedMarker_IsTheNestedOwnersImplicitParameter_ForTheEditor()
    {
        const string source = "Apply(f) = f(1, 10)\nF(0) = 0\nF(n) = {\n    B = y - ~x\n    Apply(B) + n\n}";
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, model.FindResolutionAt(new SourcePosition(4, 14))!.Classification);
        Assert.Equal(["x", "y"], Assert.Single(model.FindProperties("B")).Parameters.Select(p => p.Name).ToArray());

        var inline = SemanticModelBuilder.Build(SourceProvenance.ParseValid(Apply2 + "F(0) = Apply({ y - ~x })").Parsed);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, inline.FindResolutionAt(new SourcePosition(2, 21))!.Classification);
    }
}
