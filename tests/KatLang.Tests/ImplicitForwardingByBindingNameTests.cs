using System.Collections;
using System.Numerics;
using System.Reflection;
using KatLang.Semantics;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// FORMULA LIFTING IS BY BINDING NAME, regardless of how many times that name occurs in a callee's
/// parameter patterns (decided September 29 2026, replacing the same day's Q-72 refusal; narrowed to
/// formulas by the alias and bare-forwarding rules, FWD-02).
///
/// <para>A caller owns ONE binding for a given parameter name. When a formula USES another formula
/// without arguments inside an expression (a lifting position: an operand, a list element, an index
/// target, a strict Math argument, a callback body, several dependencies at once), the inputs are
/// forwarded by name: the caller receives one parameter per binding NAME the callees need (PAR-05's
/// first-occurrence order, skipping names already bound), and each synthesized call supplies that one
/// binding to every occurrence of the name in the callee's patterns. The same rule governs a name
/// shared ACROSS callees (<c>F(x)</c>, <c>G(x)</c>, <c>H = F + G</c> is <c>H(x) = F(x) + G(x)</c>) and
/// a name repeated WITHIN one callee (<c>P(x, x) = x</c>, <c>D = [P]:0</c> is
/// <c>D(x) = [P(x, x)]:0</c>): the language does not distinguish them. There is no repeated-name
/// exception anywhere in formula lifting.</para>
///
/// <para>A body whose ONE row is the bare callee is NOT a formula: <c>A = P</c> is an exact alias
/// (<c>A(x, x)</c>, P's own contract) and <c>Q(x) = P</c> is bare forwarding, which reuses Q's one
/// binding named x by name — <c>P(x, x)</c> — and never adds or renames a parameter
/// (<see cref="AliasAndBareForwardingTests"/>).</para>
///
/// <para>Q-05 is unchanged: a repeated name stays a compatibility constraint over INDEPENDENTLY
/// supplied arguments, so the direct <c>P(7, 8)</c> still fails. Forwarding supplies the SAME
/// existing caller binding to each occurrence — exactly the written <c>Same(x) = P(x, x)</c> — so no
/// binding is spliced or manufactured: each occurrence is an ordinary argument slot reading the
/// caller's one binding, a callable-only or failed binding is that argument's own failure, and no
/// value is ever paired with another argument's callable (<see cref="RepeatedNameConstraintTests"/>).</para>
///
/// <para>Evidence: the elaborated tree (one forwarded parameter per name, the synthesized call's
/// arguments), six execution routes with host-call logs, the metamorphic law that implicit
/// forwarding is observationally the explicit call that writes the same caller binding into every
/// matching callee slot, the rename-apart law, and an invariant — checked over every program here
/// and the whole executable specification — that no inferred signature repeats a name, an exact
/// alias's inherited signature (its callee's own) excepted.</para>
/// </summary>
public class ImplicitForwardingByBindingNameTests
{
    private const string P = "P(x, x) = x\n";

    private const string Vocabulary = "Bad = trace(1) / 0\nInc(y) = y + 1\n";

    private static Algorithm.User Property(Algorithm.User root, string name)
        => Assert.IsType<Algorithm.User>(root.Properties.Single(property => property.Name == name).Value);

    /// <summary>A signature's parameter patterns as a programmer would write them (<c>x, (a)</c>).</summary>
    private static string Signature(Algorithm.User algorithm)
        => string.Join(", ", algorithm.ParameterPatterns.Select(static pattern => pattern.DisplayName));

    /// <summary>An argument list as written, spans ignored (<c>x, [x, a]</c>, <c>x, rest*, x</c>).</summary>
    private static string Arguments(IEnumerable<Expr> arguments)
        => string.Join(", ", arguments.Select(ArgumentShape));

    private static string ArgumentShape(Expr expr) => expr switch
    {
        Expr.Param param => param.Name,
        Expr.Resolve resolve => resolve.Name,
        Expr.SequenceSpread spread => ArgumentShape(spread.Operand) + "*",
        // A forwarded structural group is rebuilt as the SAME kind (FWD-02): a sequence group as
        // a sequence (a capture), a list group as a list literal.
        Expr.Capture capture => "(" + Arguments(capture.Body) + ")",
        Expr.ListLiteral list => "[" + Arguments(list.Items) + "]",
        Expr.EmptySequence => "()",
        _ => expr.GetType().Name,
    };

    /// <summary>The one call to <c>P</c> an owner's rows contain, wherever it stands.</summary>
    private static Expr.Call CallTo(Algorithm.User owner, string callee = "P")
        => Assert.Single(AllCallsTo(owner, callee));

    /// <summary>Every call to <paramref name="callee"/> anywhere under <paramref name="owner"/>: its rows, properties, and blocks.</summary>
    private static List<Expr.Call> AllCallsTo(Algorithm.User owner, string callee = "P")
        => AllUserAlgorithms(owner)
            .SelectMany(AllExpressions)
            .OfType<Expr.Call>()
            .Where(call => call.Function is Expr.Resolve resolve && resolve.Name == callee)
            .ToList();

    private static async Task<string> Outcome(string source, long? seed = null)
        => RepeatedNameConstraintTests.Rendered(await RepeatedNameConstraintTests.OnEveryRouteAsync(source, seed));

    // ── 1. The motivating formula ───────────────────────────────────────────────────

    /// <summary>A formula that uses P without arguments: a list element selected back out, so its
    /// value is P's own whatever P returns.</summary>
    private const string Formula = "Some = [P]:0\n";

    [Fact]
    public async Task FormulaOfARepeatedNameCallee_ForwardsOneBindingToEveryOccurrence()
    {
        var root = SourceProvenance.ParseValid(P + Formula + "Some(7)").Root;
        var some = Property(root, "Some");

        // One binding name, one caller parameter — a forwarded one (nothing was written) — and the
        // synthesized call supplies it to both of P's occurrences: `Some(x) = [P(x, x)]:0`.
        Assert.Equal(["x"], some.Params);
        Assert.Equal(0, some.ForwardingParameterStart);
        Assert.Equal("x, x", Arguments(CallTo(some).Args));
        AssertNoInferredSignatureRepeatsAName(root, "formula");

        Assert.Equal("ok 7", await Outcome(P + Formula + "Some(7)"));
        // Some takes the ONE argument its one binding needs, never one per occurrence.
        Assert.Equal(
            "err ArityMismatch: Callable `Some(x)` expects 1 argument, but was called with 2 arguments.",
            await Outcome(P + Formula + "Some(7, 7)"));

        // The bare row is not a formula: an exact alias keeps P's two independent arguments.
        Assert.Equal("ok 7", await Outcome(P + "Some = P\nSome(7, 7)"));
    }

    [Fact]
    public void ForwardedReference_StillResolvesToTheCalleeForEditorTooling()
    {
        var parsed = SourceProvenance.ParseValid(P + Formula + "Some(7)").Parsed;
        var model = SemanticModelBuilder.Build(parsed);

        var reference = model.FindResolutionAt(new SourcePosition(2, 9));
        Assert.NotNull(reference);
        Assert.Equal("P", reference.ResolvedProperty?.Name);
        Assert.Equal(new SourceSpan(1, 1, 1, 2), reference.ResolvedDeclaration!.Span);
    }

    /// <summary>The editor shows the formula's forwarded signature: one parameter per binding name.</summary>
    [Theory]
    [InlineData("P(x, x) = x", "Some(x)")]
    [InlineData("P(x, x, x) = x", "Some(x)")]
    [InlineData("P((x, a), x) = a", "Some((x, a))")]
    // A sequence group left with one binding IS that binding: there is no one-item sequence.
    [InlineData("P(x, (x, a)) = a", "Some(x, a)")]
    [InlineData("P((x, x)) = x", "Some(x)")]
    // A list group keeps its brackets at every cardinality.
    [InlineData("P(x, [x, a]) = a", "Some(x, [a])")]
    [InlineData("P([x, x]) = x", "Some([x])")]
    [InlineData("P(x, *rest, x) = rest", "Some(x, *rest)")]
    public void EditorSignature_OfAForwardingFormula_HasOneParameterPerBindingName(string declaration, string signature)
    {
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(declaration + "\n" + Formula + "0").Parsed);
        Assert.Equal(signature, Assert.Single(model.FindProperties("Some")).DisplaySignature);
    }

    // ── 2. One binding name, one caller parameter — at any depth ────────────────────

    /// <summary>
    /// A generated repeated-name callee: its parameters and body, the signature a formula lifts
    /// from it (one capture per binding name, in first-occurrence order, group shapes kept for the
    /// names that are new there — a sequence group left with ONE binding is that binding, a list
    /// group keeps its brackets), the arguments the synthesized call passes (the callee's own
    /// patterns rebuilt from the caller's bindings, each group as its own kind), a satisfying call
    /// of the formula with its outcome, and the callee with every repeated occurrence renamed apart.
    /// </summary>
    public sealed record RepeatedShape(
        string Parameters,
        string Body,
        string Lifted,
        string ForwardedArguments,
        string AliasArguments,
        string Expected,
        string Distinct);

    private static readonly RepeatedShape[] Shapes =
    [
        new("x, x", "x", "x", "x, x", "7", "ok 7", "x, x2"),
        new("x, x, x", "x", "x", "x, x, x", "7", "ok 7", "x, x2, x3"),
        new("x, y, x", "[x, y]", "x, y", "x, y, x", "7, 1", "ok L[7, 1]", "x, y, x2"),
        new("x, x, y", "[x, y]", "x, y", "x, x, y", "7, 1", "ok L[7, 1]", "x, x2, y"),
        new("y, x, x", "[x, y]", "y, x", "y, x, x", "1, 7", "ok L[7, 1]", "y, x, x2"),
        new("x, y, y, x", "[x, y]", "x, y", "x, y, y, x", "7, 1", "ok L[7, 1]", "x, y, y2, x2"),
        // A forwarded group is rebuilt as its own kind (FWD-02): a sequence group as a sequence,
        // a list group as a list. A lifted sequence group left with ONE binding is that binding.
        new("(x, a), x", "a", "(x, a)", "(x, a), x", "(7, 1)", "ok 1", "(x, a), x2"),
        new("x, (x, a)", "a", "x, a", "x, (x, a)", "7, 1", "ok 1", "x, (x2, a)"),
        new("(x, y), (z, x)", "[y, z]", "(x, y), z", "(x, y), (z, x)", "(7, 1), 2", "ok L[1, 2]", "(x, y), (z, x2)"),
        new("(x, *rest), x", "rest", "(x, *rest)", "(x, rest*), x", "(7, 1, 2)", "ok L[1, 2]", "(x, *rest), x2"),
        new("x, *rest, x", "rest", "x, *rest", "x, rest*, x", "7, 1, 2", "ok L[1, 2]", "x, *rest, x2"),
        new("(x, x)", "x", "x", "(x, x)", "7", "ok 7", "(x, x2)"),
        new("(x, y), x, y", "[x, y]", "(x, y)", "(x, y), x, y", "(7, 1)", "ok L[7, 1]", "(x, y), x2, y2"),
        new("a, (b, c), (c, a)", "[a, b, c]", "a, (b, c)", "a, (b, c), (c, a)", "1, (2, 3)", "ok L[1, 2, 3]", "a, (b, c), (c2, a2)"),
        new("((x, y), x)", "[x, y]", "(x, y)", "((x, y), x)", "(7, 1)", "ok L[7, 1]", "((x, y), x2)"),
        // List groups keep their brackets at every cardinality, the one-element list included.
        new("[x, x]", "x", "[x]", "[x, x]", "[7]", "ok 7", "[x, x2]"),
        new("x, [x, a]", "a", "x, [a]", "x, [x, a]", "7, [1]", "ok 1", "x, [x2, a]"),
        new("[x, a], x", "a", "[x, a]", "[x, a], x", "[7, 1]", "ok 1", "[x, a], x2"),
        new("([x, y], x)", "[x, y]", "[x, y]", "([x, y], x)", "[7, 1]", "ok L[7, 1]", "([x, y], x2)"),
        new("[(x, y), x]", "[x, y]", "[(x, y)]", "[(x, y), x]", "[(7, 1)]", "ok L[7, 1]", "[(x, y), x2]"),
    ];

    public static TheoryData<int> ShapeIndexes()
    {
        var data = new TheoryData<int>();
        for (var shape = 0; shape < Shapes.Length; shape++)
            data.Add(shape);
        return data;
    }

    private static string Declaration(RepeatedShape shape) => $"P({shape.Parameters}) = {shape.Body}\n";

    /// <summary>
    /// THE NAME DEDUPLICATION LAW: whatever the number of occurrences of a name in the callee's
    /// patterns — at the top level, inside one group, across groups, beside a collector — formula
    /// lifting introduces ONE caller binding for it, in first-occurrence order; the synthesized call
    /// feeds that binding to every occurrence; and the formula evaluates on every route. (The exact
    /// alias of the same callee inherits its signature verbatim instead.)
    /// </summary>
    [Theory]
    [MemberData(nameof(ShapeIndexes))]
    public async Task EveryShape_LiftsOneCallerBindingPerName(int shapeIndex)
    {
        var shape = Shapes[shapeIndex];
        var source = Declaration(shape) + $"Lifted = [P]:0\nAlias = P\nLifted({shape.AliasArguments})";
        var root = SourceProvenance.ParseValid(source).Root;
        var lifted = Property(root, "Lifted");
        var callee = Property(root, "P");

        Assert.Equal(shape.Lifted, Signature(lifted));
        Assert.Equal(callee.Params.Distinct(StringComparer.Ordinal), lifted.Params);
        Assert.Equal(0, lifted.ForwardingParameterStart);
        Assert.Equal(shape.ForwardedArguments, Arguments(CallTo(lifted).Args));
        Assert.Equal(shape.Parameters, Signature(Property(root, "Alias")));
        AssertNoInferredSignatureRepeatsAName(root, shape.Parameters);

        Assert.Equal(shape.Expected, await Outcome(source));
    }

    /// <summary>
    /// THE EXPLICIT-FORWARDING EQUIVALENCE LAW: <c>Lifted = [P]:0</c> is observationally the formula
    /// that writes the caller's binding into every matching callee slot — <c>Lifted(x) = [P(x, x)]:0</c>,
    /// subject to the ordinary surrounding pattern shapes — on satisfying arguments and on a traced, a
    /// failing, and a callable-only argument alike: same signature, same synthesized arguments, same
    /// outcome and host-call log on every route.
    /// </summary>
    [Theory]
    [MemberData(nameof(ShapeIndexes))]
    public async Task EveryShape_ImplicitForwardingIsTheExplicitSameBindingCall(int shapeIndex)
    {
        var shape = Shapes[shapeIndex];
        var implicitAlias = Vocabulary + Declaration(shape) + "Alias = [P]:0\n";
        var explicitAlias = Vocabulary + Declaration(shape) + $"Alias({shape.Lifted}) = [P({shape.ForwardedArguments})]:0\n";

        var implicitOwner = Property(SourceProvenance.ParseValid(implicitAlias + "0").Root, "Alias");
        var explicitOwner = Property(SourceProvenance.ParseValid(explicitAlias + "0").Root, "Alias");
        Assert.Equal(Signature(explicitOwner), Signature(implicitOwner));
        Assert.Equal(Arguments(CallTo(explicitOwner).Args), Arguments(CallTo(implicitOwner).Args));

        var firstSeven = shape.AliasArguments.IndexOf('7', StringComparison.Ordinal);
        string WithFirstSeven(string replacement) => firstSeven < 0
            ? shape.AliasArguments
            : shape.AliasArguments[..firstSeven] + replacement + shape.AliasArguments[(firstSeven + 1)..];

        foreach (var arguments in new[] { shape.AliasArguments, WithFirstSeven("trace(7)"), WithFirstSeven("Bad"), WithFirstSeven("Inc") })
        {
            var expected = await Outcome(explicitAlias + $"Alias({arguments})");
            var actual = await Outcome(implicitAlias + $"Alias({arguments})");
            Assert.True(expected == actual, $"P({shape.Parameters}) with Alias({arguments})\nexplicit: {expected}\nimplicit: {actual}");
        }
    }

    /// <summary>
    /// THE RENAME-APART LAW: renaming the repeated occurrences apart gives each fresh name its own
    /// caller parameter by ordinary inference — the formula then lifts the callee's whole signature as
    /// written. No repeated-name transition is involved: the rule reads binding names only.
    /// </summary>
    [Theory]
    [MemberData(nameof(ShapeIndexes))]
    public void EveryShape_RenamedApart_LiftsEveryFreshName(int shapeIndex)
    {
        var shape = Shapes[shapeIndex];
        var root = SourceProvenance.ParseValid($"P({shape.Distinct}) = {shape.Body}\nAlias = [P]:0\n0").Root;
        var alias = Property(root, "Alias");
        Assert.Equal(shape.Distinct, Signature(alias));
        Assert.Equal(Property(root, "P").Params, alias.Params);
        AssertNoInferredSignatureRepeatsAName(root, shape.Distinct);
    }

    // ── 3. The same rule within and across callees ──────────────────────────────────

    /// <summary>
    /// A name repeated within one callee and a name shared across callees are the same case:
    /// one binding name, one caller parameter, supplied to every occurrence. (source, owner,
    /// owner signature, outcome)
    /// </summary>
    [Theory]
    [InlineData("F(x) = x + 1\nG(x) = x * 2\nH = F + G\nH(3)", "x", "ok 10")]
    [InlineData(P + "F(x) = x + 1\nH = P + F\nH(3)", "x", "ok 7")]
    [InlineData(P + "F(x) = x + 1\nH = F + P\nH(3)", "x", "ok 7")]
    [InlineData(P + "H = P + P\nH(3)", "x", "ok 6")]
    [InlineData(P + "P2((x, x)) = x * 10\nH = P + P2\nH(3)", "x", "ok 33")]
    [InlineData(P + "G(y, x) = y - x\nH = P + G\nH(3, 1)", "x, y", "ok 1")]
    [InlineData(P + "G(y, x) = y - x\nH = G + P\nH(1, 3)", "y, x", "ok 1")]
    public async Task WithinAndAcrossCallees_OneBindingNameIsOneCallerParameter(string source, string signature, string expected)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(signature, Signature(Property(root, "H")));
        AssertNoInferredSignatureRepeatsAName(root, source);
        Assert.Equal(expected, await Outcome(source));
    }

    [Fact]
    public async Task CrossCalleeComposition_IsUnchanged()
    {
        const string Source = "F(x) = x + 1\nG(x) = x * 2\nH = F + G\nH(3)";
        var h = Property(SourceProvenance.ParseValid(Source).Root, "H");
        Assert.Equal(["x"], h.Params);
        var sum = Assert.IsType<Expr.Binary>(Assert.Single(h.Output));
        Assert.Equal("x", Arguments(Assert.IsType<Expr.Call>(sum.Left).Args));
        Assert.Equal("x", Arguments(Assert.IsType<Expr.Call>(sum.Right).Args));
        Assert.Equal("ok 10", await Outcome(Source));
    }

    // ── 4. Existing bindings and closed parameter lists ─────────────────────────────

    /// <summary>
    /// A closed list that declares the name supplies its OWN binding to every occurrence of a
    /// formula's callee: <c>Q(x) = P + 0</c> is <c>Q(x) = P(x, x) + 0</c>. The lone row
    /// <c>Q(x) = P</c> is bare forwarding, which is by name too: <c>P(x, x)</c> — the one binding
    /// named x reaches every occurrence, and nothing is added or renamed.
    /// </summary>
    [Fact]
    public async Task ClosedListDeclaringTheName_ForwardsItsBindingToEveryOccurrence()
    {
        foreach (var body in new[] { "P + 0", "P" })
        {
            var root = SourceProvenance.ParseValid(P + $"Q(x) = {body}\nQ(7)").Root;
            var q = Property(root, "Q");
            Assert.True(q.HasExplicitParameterList);
            Assert.Equal(["x"], q.Params);
            Assert.Null(q.ForwardingParameterStart);
            Assert.Equal("x, x", Arguments(CallTo(q).Args));
            Assert.Equal("ok 7", await Outcome(P + $"Q(x) = {body}\nQ(7)"));
        }

        Assert.Equal("ok 1", await Outcome("P((x, a), x) = a\nQ(x, a) = P + 0\nQ(7, 1)"));
    }

    /// <summary>
    /// A closed list that does NOT declare the name follows the ordinary closed-list rule, with no
    /// repeated-name special case: exactly what the same position does for a callee whose names are
    /// distinct. In a neutral-valued position the reference stays the callable's own zero-argument
    /// demand; in a strict Math position the front end names the missing parameter once.
    /// </summary>
    [Theory]
    [InlineData("Q(y) = [@]:0\nQ(7)")]
    [InlineData("Q(y) = @ + y\nQ(7)")]
    [InlineData("F(0) = 0\nF(y) = @ + y\nF(7)")]
    public async Task ClosedListLackingTheName_FollowsTheOrdinaryClosedListRule(string template)
    {
        var repeated = P + template.Replace("@", "P", StringComparison.Ordinal);
        var distinct = "P(x, z) = x\n" + template.Replace("@", "P", StringComparison.Ordinal);
        SourceProvenance.ParseValid(repeated);
        SourceProvenance.ParseValid(distinct);
        var expected = await Outcome(distinct);
        Assert.Contains("Property 'P' expects 2 parameters, but was called with 0 arguments.", expected, StringComparison.Ordinal);
        Assert.Equal(expected, await Outcome(repeated));
    }

    [Theory]
    [InlineData("Q(y) = sin(@)\nQ(0)")]
    [InlineData("F(0) = 0\nF(y) = sin(@) + y\nF(1)")]
    public void StrictValueUnderAClosedList_NamesTheMissingParameterOnce(string template)
    {
        var repeated = Parser.Parse(P + template.Replace("@", "P", StringComparison.Ordinal));
        var distinct = Parser.Parse("P(x) = x\n" + template.Replace("@", "P", StringComparison.Ordinal));

        var diagnostic = Assert.Single(repeated.Diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Contains("needs the implicit parameter 'x',", diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(Assert.Single(distinct.Diagnostics).Message, diagnostic.Message);
    }

    /// <summary>
    /// An existing parameter binding of the name — the owner's written or inferred parameter, a
    /// captured parameter of an enclosing owner (Q-04), a clause-branch binder — is the one binding
    /// every occurrence receives; nothing is added beside it. (source, owner, owner params, outcome)
    /// </summary>
    [Theory]
    [InlineData(P + "Q = x + P\nQ(7)", "Q", new[] { "x" }, "ok 14")]
    [InlineData(P + "Outer(x) = {\n  Inner = [P]:0\n  Inner\n}\nOuter(7)", "Outer", new[] { "x" }, "ok 7")]
    [InlineData(P + "F(0) = 0\nF(x) = P + x\nF(7)", "F", new string[0], "ok 14")]
    [InlineData(P + "Outer(x) = {\n  Inner = P + 1\n  Inner\n}\nOuter(7)", "Outer", new[] { "x" }, "ok 8")]
    public async Task ExistingBinding_IsTheOneBindingEveryOccurrenceReceives(string source, string owner, string[] parameters, string expected)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var algorithm = root.Properties.Single(property => property.Name == owner).Value;
        Assert.Equal(parameters, algorithm.Params);
        if (algorithm is Algorithm.User user)
            Assert.Null(user.ForwardingParameterStart);
        AssertNoInferredSignatureRepeatsAName(root, source);
        Assert.Equal(expected, await Outcome(source));
    }

    [Fact]
    public void CapturedEnclosingBinding_MakesTheHelperAnOrdinaryProperty()
    {
        var outer = Property(SourceProvenance.ParseValid(P + "Outer(x) = {\n  Inner = [P]:0\n  Inner\n}\nOuter(7)").Root, "Outer");
        var inner = Property(outer, "Inner");
        Assert.Empty(inner.Params);
        Assert.Equal("x, x", Arguments(CallTo(inner).Args));

        // A bare local alias is not a formula: it keeps P's own signature, whatever Outer binds.
        var alias = Property(Property(SourceProvenance.ParseValid(P + "Outer(x) = {\n  Inner = P\n  Inner(x, x)\n}\nOuter(7)").Root, "Outer"), "Inner");
        Assert.Equal("x, x", Signature(alias));
    }

    // ── 5. Every lifting position: implicit forwarding is the explicit call ─────────

    /// <summary>
    /// (template, a satisfying argument). <c>@</c> marks the callee reference, <c>#</c> the argument
    /// of the call that runs it. Every position where formula lifting applies: operator, comparison
    /// and unary operands, list elements, index targets and selectors, row spreads, strict Math
    /// arguments and a Math dot-fallback receiver, a deconstruction right-hand side, a block body
    /// and a nested property that use the callee, a closed list and a branch pattern that bind the
    /// name, sibling formulas, a loop step and a callback. (A LONE bare row — an alias row, a lone
    /// block or helper row, bare forwarding — is not a lifting position: AliasAndBareForwardingTests.)
    /// </summary>
    public static TheoryData<string, string> LiftingPositions => new()
    {
        { "D = @ + 1\nD(#)", "7" },
        { "D = 1 + @\nD(#)", "7" },
        { "D = @ == 7\nD(#)", "7" },
        { "D = 1 < @ <= 9\nD(#)", "7" },
        { "D = -@\nD(#)", "7" },
        { "D = not @\nD(#)", "true" },
        { "D = [@, 1]\nD(#)", "7" },
        { "D = @:0\nD(#)", "(7, 8)" },
        { "D = [10, 20]:@\nD(#)", "1" },
        { "D = @*, 1\nD(#)", "(7, 8)" },
        { "D = sin(@)\nD(#)", "0" },
        { "D = Math.Pow(@, 2)\nD(#)", "3" },
        { "D = @.sin\nD(#)", "0" },
        { "D = {\n  u, v = @\n  u\n}\nD(#)", "(7, 8)" },
        { "D = { @ + 0 }\nD(#)", "7" },
        { "D = {\n  Inner = [@]:0\n  Inner\n}\nD(#)", "7" },
        { "Apply(f) = f(#)\nApply({ [@]:0 })", "7" },
        { "D = @ + @\nD(#)", "7" },
        { "Q(x) = [@]:0\nQ(#)", "7" },
        { "F(0) = 0\nF(x) = @ + x\nF(#)", "7" },
        { "Outer(x) = {\n  Inner = [@]:0\n  Inner\n}\nOuter(#)", "7" },
        { "A = [@]:0\nB = A + 1\nC = [B, A]\nC(#)", "7" },
        { "Step = @ + 1\nrepeat(Step, 2, #)", "0" },
        { "Some = [@]:0\nmap([#, 2], Some)", "7" },
    };

    /// <summary>
    /// For every lifting position, the bare reference <c>P</c> and the explicit call <c>P(x, x)</c>
    /// written in its place elaborate to owners with the same parameters, and they agree on every
    /// route — outcome and host-call log — for a satisfying argument and for a traced, a failing, a
    /// callable-only, a ticking and a seeded random argument: one argument evaluation, read by both
    /// occurrences, whatever it produces.
    /// </summary>
    [Theory]
    [MemberData(nameof(LiftingPositions))]
    public async Task EveryLiftingPosition_ForwardsLikeTheExplicitCall(string template, string satisfying)
    {
        // The explicit call is grouped so it is ONE operand in every position (a selector included);
        // a redundant group is the expression itself.
        var implicitProgram = Vocabulary + P + template.Replace("@", "P", StringComparison.Ordinal);
        var explicitProgram = Vocabulary + P + template.Replace("@", "(P(x, x))", StringComparison.Ordinal);

        var implicitRoot = SourceProvenance.ParseValid(implicitProgram.Replace("#", satisfying, StringComparison.Ordinal)).Root;
        var explicitRoot = SourceProvenance.ParseValid(explicitProgram.Replace("#", satisfying, StringComparison.Ordinal)).Root;
        AssertNoInferredSignatureRepeatsAName(implicitRoot, template);
        foreach (var property in explicitRoot.Properties)
        {
            Assert.Equal(
                property.Value.Params,
                implicitRoot.Properties.Single(candidate => candidate.Name == property.Name).Value.Params);
        }

        var satisfied = await Outcome(implicitProgram.Replace("#", satisfying, StringComparison.Ordinal));
        Assert.StartsWith("ok ", satisfied, StringComparison.Ordinal);

        foreach (var argument in new[] { satisfying, $"trace({satisfying})", "Bad", "Inc", "tick()", "randomInt(0, 9)" })
        {
            var expected = await Outcome(explicitProgram.Replace("#", argument, StringComparison.Ordinal), seed: 4);
            var actual = await Outcome(implicitProgram.Replace("#", argument, StringComparison.Ordinal), seed: 4);
            Assert.True(expected == actual, $"{template} with {argument}\nexplicit: {expected}\nimplicit: {actual}");
        }
    }

    /// <summary>
    /// The generated shapes in every open lifting position and under a closed list that declares
    /// their names with the callee's binding kinds (a collector as a collector, so FWD-02 re-spreads
    /// it): each elaborates cleanly, the owner receives one parameter per distinct name, every
    /// synthesized call feeds that one binding to every occurrence, and no inferred signature
    /// repeats a name.
    /// </summary>
    [Theory]
    [MemberData(nameof(ShapeByPosition))]
    public void EveryShapeInEveryPosition_LiftsEachNameOnce(int shapeIndex, int positionIndex)
    {
        var shape = Shapes[shapeIndex];
        var callee = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid(Declaration(shape) + "0").Root.Properties.Single().Value);
        var captures = callee.ParameterPatterns
            .SelectMany(static pattern => pattern.Captures)
            .DistinctBy(static capture => capture.Name, StringComparer.Ordinal)
            .ToList();
        var names = captures.Select(static capture => capture.Name).ToList();
        var declared = string.Join(", ", captures.Select(static capture => capture.DisplayName));
        var template = ShapePositions[positionIndex].Replace("@@", declared, StringComparison.Ordinal);
        var root = SourceProvenance.ParseValid(Declaration(shape) + template.Replace("@", "P", StringComparison.Ordinal)).Root;

        AssertNoInferredSignatureRepeatsAName(root, $"{shape.Parameters} / {template}");
        var owner = Property(root, "D");
        Assert.Equal(names, owner.Params);
        var calls = AllCallsTo(owner);
        Assert.NotEmpty(calls);
        Assert.All(calls, call => Assert.Equal(shape.ForwardedArguments, Arguments(call.Args)));
    }

    private static readonly string[] ShapePositions =
    [
        "D = [@]:0\n0",
        "D = @ + 0\n0",
        "D = [@]\n0",
        "D = @:0\n0",
        "D = sin(@)\n0",
        "D = { @ + 0 }\n0",
        "D = {\n  Inner = [@]:0\n  Inner\n}\n0",
        "D = {\n  u, v = @\n  u\n}\n0",
        "D(@@) = [@]:0\n0",
        "D(@@) = [@, @]\n0",
    ];

    public static TheoryData<int, int> ShapeByPosition()
    {
        var data = new TheoryData<int, int>();
        for (var shape = 0; shape < Shapes.Length; shape++)
        {
            for (var position = 0; position < ShapePositions.Length; position++)
                data.Add(shape, position);
        }

        return data;
    }

    // ── 6. Q-05 holds through forwarding: one binding, never a splice ───────────────

    /// <summary>
    /// The forwarded binding is ONE complete binding — the value AND the callable the caller's one
    /// argument supplied — handed to every occurrence. So a callable-only or failed argument is its
    /// own failure (evaluated once, never repaired by another occurrence), a callable accompanies its
    /// own argument's value, and no value is paired with another argument's callable. The direct call
    /// still supplies independent arguments and still fails on unequal values.
    /// </summary>
    public static TheoryData<string, string, string> ForwardedOutcomes => new()
    {
        { "direct-unequal", P + "P(7, 8)", "err ArityMismatch: while evaluating call to P: Bad arity" },
        { "direct-equal", P + "P(7, 7)", "ok 7" },
        { "forwarded", P + "Some = [P]:0\nSome(7)", "ok 7" },
        { "forwarded-once", P + "Some = [P]:0\nSome(trace(7))", "ok 7 [trace(7)]" },
        { "forwarded-tick-once", P + "Some = [P]:0\nSome(tick())", "ok 1 [tick#1]" },
        { "forwarded-failed", "Bad = trace(1) / 0\n" + P + "Some = [P]:0\nSome(Bad)",
            "err DivisionByZero: while evaluating call to Some: while evaluating call to P: Division by zero [trace(1)]" },
        { "forwarded-callable-only", "Inc(y) = y + 1\nPC(x, x) = x, x(5)\nSome = [PC]:0\nSome(Inc)",
            "err ArityMismatch: while evaluating call to Some: while evaluating call to PC: Property 'Inc' expects 1 parameter, but was called with 0 arguments." },
        { "forwarded-accompanying-callable", "A = 5\nPF(f, f) = f, f()\nSome = [PF]:0\nSome(A)", "ok S[5, 5]" },
        { "forwarded-distinct-values-impossible", P + "Some = [P]:0\nSome(7), Some(8)", "ok S[7, 8]" },
        { "explicit-same", P + "Same(x) = P(x, x)\nSame(7)", "ok 7" },
        { "explicit-two", P + "Both(a, b) = P(a, b)\nBoth(7, 8)", "err ArityMismatch: while evaluating call to Both: while evaluating call to P: Bad arity" },
        { "nested-group-forwarded", "N(x, (x, y)) = y\nSome = [N]:0\nSome(7, 8)", "ok 8" },
        { "collector-forwarded", "C(x, *r, x) = x, r\nSome = [C]:0\nSome(7, 9)", "ok S[7, L[9]]" },
        // The exact alias is not a formula: it keeps P's two independent arguments (Q-05).
        { "alias-equal", P + "Some = P\nSome(7, 7)", "ok 7" },
        { "alias-unequal", P + "Some = P\nSome(7, 8)", "err ArityMismatch: while evaluating call to Some: Bad arity" },
    };

    [Theory]
    [MemberData(nameof(ForwardedOutcomes))]
    public async Task RepeatedNameConstraint_HoldsThroughForwarding(string id, string source, string expected)
    {
        var actual = await Outcome(source);
        Assert.True(expected == actual, $"{id}\nexpected: {expected}\nactual:   {actual}");
    }

    /// <summary>
    /// <c>Some = [P]:0</c> and the written <c>Some(x) = [P(x, x)]:0</c> are the same program: same
    /// signature, same synthesized call, and the same outcome for every argument kind, on every route.
    /// </summary>
    [Theory]
    [InlineData("7")]
    [InlineData("trace(7)")]
    [InlineData("Bad")]
    [InlineData("Inc")]
    [InlineData("A")]
    [InlineData("[1, 2]")]
    [InlineData("(1, 2)")]
    [InlineData("{ 5 }")]
    [InlineData("tick()")]
    public async Task SomeEqualsSame_ForEveryArgumentKind(string argument)
    {
        const string Prelude = "Bad = trace(1) / 0\nInc(y) = y + 1\nA = 5\nP(x, x) = x, x.string\n";
        var implicitOutcome = await Outcome(Prelude + $"Some = [P]:0\nSome({argument})");
        var explicitOutcome = await Outcome(Prelude + $"Some(x) = [P(x, x)]:0\nSome({argument})");
        Assert.Equal(explicitOutcome, implicitOutcome);
    }

    // ── 7. Positions that never forward are unchanged ───────────────────────────────

    /// <summary>
    /// Removing the refusal widens nothing: neutral positions still pass the callable itself,
    /// callees and dot fallbacks still receive written arguments, a bare root row is still the
    /// callable's own zero-argument demand, and a clause family is still never aliased (PV-14).
    /// </summary>
    [Theory]
    [InlineData(P + "Apply(f) = f(4, 4)\nApply(P)", "ok 4")]
    [InlineData(P + "P(7, 7)", "ok 7")]
    [InlineData(P + "(7, 7)*.P", "ok 7")]
    [InlineData(P + "D = y.P(y)\nD(3)", "ok 3")]
    [InlineData(P + "Twice(f, v) = f(v, v)\nTwice(P, 5)", "ok 5")]
    [InlineData(P + "P", "err ArityMismatch: Property 'P' expects 2 parameters, but was called with 0 arguments.")]
    [InlineData(P + "7.P", "err ArityMismatch: Callable `P(x, x)` expects 2 arguments, but was called with 1 argument.")]
    [InlineData(P + "map([1, 2], P)", "err ArityMismatch: while evaluating call to map: while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact): Expected 2 parameters, but was called with 1 argument.")]
    [InlineData("Same(x, x) = true\nSame(x, y) = false\nAlias = Same\nAlias(1, 1)", "err ArityMismatch: Callable `Alias` expects 0 arguments, but was called with 2 arguments.")]
    public async Task PositionsThatNeverForward_AreUnchanged(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(expected, await Outcome(source));
    }

    /// <summary>
    /// THE UNIFIED FORMULA-LIFTING LAW: the lifting signature is keyed by the resolved callable,
    /// never by the route that reached it, so an opened member and a structural dotted member lift
    /// by binding name exactly like a lexical property — one binding per name (<c>D(x)</c> is
    /// <c>P(x, x) + 1</c>) — and the bare root row naming the formula is its own zero-argument
    /// demand. Formerly opened and structural names were never implicitly forwarded.
    /// </summary>
    [Theory]
    [InlineData("M = {\n  public P(x, x) = x\n}\nD = {\n  open M\n  P + 1\n}\nD(3)", "ok 4")]
    [InlineData("M = {\n  public P(x, x) = x\n}\nD = M.P + 1\nD(3)", "ok 4")]
    [InlineData("M = {\n  public P(x, x) = x\n}\nD = {\n  open M\n  P + 1\n}\nD", "err ArityMismatch: Property 'D' expects 1 parameter, but was called with 0 arguments.")]
    [InlineData("M = {\n  public P(x, x) = x\n}\nD = M.P + 1\nD", "err ArityMismatch: Property 'D' expects 1 parameter, but was called with 0 arguments.")]
    public async Task OpenedAndDottedMembers_LiftByBindingName_LikeEveryCallable(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(expected, await Outcome(source));
    }

    /// <summary>
    /// In a formula a callable that accepts zero supplied arguments is read, never lifted (Q-03),
    /// and a reused binding's KIND decides a re-spread — a repeated name never introduces one. A
    /// collector beside a repeated name is forwarded by spread exactly because it is a collector,
    /// while the repeated fixed name is forwarded as one argument at every occurrence.
    /// </summary>
    [Theory]
    [InlineData("Cnt(*xs) = xs.count\nD = Cnt + 0\nD", "ok 0")]
    [InlineData("Cnt(*xs) = xs.count\nD = Cnt == Cnt\nD", "ok true")]
    [InlineData("Cnt(*xs) = xs.count\nAlias(*xs) = Cnt(xs*)\nAlias(1, 2, 3)", "ok 3")]
    [InlineData("Cnt(*xs) = xs.count\nUse(t, *items) = Cnt + 0\nUse(0, 1, 2)", "ok 0")]
    [InlineData("Coll(*xs) = xs\nFwd(*ys) = Coll(ys*)\nFwd((1, 2), 3)", "ok L[S[1, 2], 3]")]
    [InlineData("Head(x, *rest) = x\nD = [Head]:0\nD(5, 6, 7)", "ok 5")]
    [InlineData("H((*xs)) = xs.count\nD = [H]:0\nD((1, 2))", "ok 2")]
    [InlineData("P(x, *rest, x) = rest.count\nD = [P]:0\nD((1, 2), (3, 4), 5)", "ok 2")]
    [InlineData("P((x, *rest), x) = rest\nD = [P]:0\nD(((1, 2), 3))", "ok L[3]")]
    public async Task CollectingForwarding_InAFormula(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(expected, await Outcome(source));
    }

    [Fact]
    public void RepeatedNameBesideACollector_ForwardsTheCollectorBySpreadAndTheNameOnce()
    {
        var formula = Property(SourceProvenance.ParseValid("P(x, *rest, x) = rest\nD = [P]:0\n0").Root, "D");
        Assert.Equal("x, *rest", Signature(formula));
        Assert.Equal("x, rest*, x", Arguments(CallTo(formula).Args));
    }

    // ── 8. Module text ──────────────────────────────────────────────────────────────

    /// <summary>
    /// Module text is elaborated by the same resolver: a formula over a repeated-name callee inside
    /// a loaded module forwards by binding name exactly like one in the document, and the module's
    /// explicit same-binding formula agrees.
    /// </summary>
    [Fact]
    public async Task LoadedModuleText_ForwardsByBindingNameToo()
    {
        static RunOptions Serving(string module) => new() { DownloadCode = (_, _) => ValueTask.FromResult(module) };
        const string Document = "M = load('https://katlang.org/forwarding/module.kat')\nM.Both(7), M.Both(8)";

        var lifted = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync(Document, Serving("public P(x, x) = x\npublic Both = [P]:0")));
        var written = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync(Document, Serving("public P(x, x) = x\npublic Both(x) = [P(x, x)]:0")));
        Assert.Equal([7m, 8m], lifted.Atoms);
        Assert.Equal(written.Atoms, lifted.Atoms);
    }

    // ── 9. The invariant: no inferred signature repeats a name ──────────────────────

    [Theory]
    [InlineData(4)]
    [InlineData(17)]
    [InlineData(64)]
    public async Task MultiplicityAndFormulaDepth_DoNotCreateBindingsOrRepeatEffects(int occurrences)
    {
        var parameters = string.Join(", ", Enumerable.Repeat("x", occurrences));
        var chain = "A0 = [P]:0\n" + string.Concat(Enumerable.Range(1, 16).Select(i => $"A{i} = [A{i - 1}]:0\n"));
        var source = $"P({parameters}) = x\n" + chain;
        var root = SourceProvenance.ParseValid(source + "A15(7)").Root;
        for (var i = 0; i < 16; i++)
            Assert.Equal(["x"], Property(root, $"A{i}").Params);
        Assert.Equal(occurrences, CallTo(Property(root, "A0")).Args.Count);
        Assert.Equal("ok 7 [trace(7)]", await Outcome(source + "A15(trace(7))"));

        // Renaming only the last occurrence introduces one binding, in the usual order.
        var apart = $"P({string.Join(", ", Enumerable.Repeat("x", occurrences - 1))}, y) = y\n" + chain;
        var renamed = SourceProvenance.ParseValid(apart + "A15(7, 8)").Root;
        Assert.Equal(["x", "y"], Property(renamed, "A15").Params);
        Assert.Equal("ok 8", await Outcome(apart + "A15(7, 8)"));
    }

    [Theory]
    [InlineData(1)]
    [InlineData(4)]
    [InlineData(16)]
    public async Task DeepMixedGroups_KeepFirstNameOrderAndEverySurvivingBoundary(int depth)
    {
        var pattern = "x";
        var lifted = "x";
        var argument = "7";
        for (var i = 0; i < depth; i++)
        {
            pattern = $"({pattern}, a{i}, x)";
            lifted = $"({lifted}, a{i})";
            argument = $"({argument}, {i})";
        }
        var source = $"P({pattern}) = x\nSome = [P]:0\nSome({argument})";
        var some = Property(SourceProvenance.ParseValid(source).Root, "Some");
        Assert.Equal(lifted, Signature(some));
        Assert.Equal(new[] { "x" }.Concat(Enumerable.Range(0, depth).Select(i => $"a{i}")), some.Params);
        Assert.Equal("ok 7", await Outcome(source));
    }

    /// <summary>
    /// A repeated name inside ONE sequence group leaves that group with one binding, and a
    /// sequence group with one binding IS the binding (there is no one-item sequence value): the
    /// formula takes the whole value, and its call rebuilds the callee's pair from it —
    /// <c>Some(x) = [P((x, x))]:0</c>, never the invalid <c>Some((x))</c>.
    /// </summary>
    [Theory]
    [InlineData("7", "ok 7")]
    [InlineData("[7]", "ok L[7]")]
    [InlineData("[(7, 8)]", "ok L[S[7, 8]]")]
    [InlineData("(7, 8)", "ok S[7, 8]")]
    [InlineData("[]", "ok L[]")]
    public async Task RepeatedNameInsideOneSequenceGroup_LiftsTheBareBinding(string argument, string expected)
    {
        const string declaration = "P((x, x)) = x\n";
        var implicitResult = await Outcome(declaration + $"Some = [P]:0\nSome({argument})");
        var explicitResult = await Outcome(declaration + $"Some(x) = [P((x, x))]:0\nSome({argument})");
        Assert.Equal(explicitResult, implicitResult);
        Assert.Equal(expected, implicitResult);
        Assert.Equal("x", Signature(Property(SourceProvenance.ParseValid(declaration + "Some = [P]:0\n0").Root, "Some")));
    }

    /// <summary>
    /// A repeated name inside ONE list group keeps the list: <c>Some([x]) = [P([x, x])]:0</c> takes
    /// exactly a one-element list, whose element is the binding.
    /// </summary>
    [Theory]
    [InlineData("[7]", "ok 7")]
    [InlineData("[(7, 8)]", "ok S[7, 8]")]
    [InlineData("[[7]]", "ok L[7]")]
    [InlineData("7", "err TypeMismatch:")]
    [InlineData("(7, 8)", "err TypeMismatch:")]
    [InlineData("[7, 8]", "err ArityMismatch:")]
    [InlineData("[]", "err ArityMismatch:")]
    public async Task RepeatedNameInsideOneListGroup_KeepsTheOneElementList(string argument, string expected)
    {
        const string declaration = "P([x, x]) = x\n";
        var implicitResult = await Outcome(declaration + $"Some = [P]:0\nSome({argument})");
        var explicitResult = await Outcome(declaration + $"Some([x]) = [P([x, x])]:0\nSome({argument})");
        Assert.Equal(explicitResult, implicitResult);
        Assert.StartsWith(expected, implicitResult, StringComparison.Ordinal);
        Assert.Equal("[x]", Signature(Property(SourceProvenance.ParseValid(declaration + "Some = [P]:0\n0").Root, "Some")));
    }

    /// <summary>
    /// A chain of formulas forwards each surviving group as its own kind at every step: Next
    /// rebuilds Some's list group as a list and its sequence group as a sequence, so each
    /// structural pattern opens its argument exactly once, like the direct call.
    /// </summary>
    [Fact]
    public async Task AnotherFormulaOverASurvivingGroup_RebuildsItAsTheSameKind()
    {
        const string list = "P([x, x]) = x\nSome = [P]:0\nNext = [Some]:0\n";
        Assert.Equal("ok S[7, 8]", await Outcome(list + "Some([(7, 8)])"));
        Assert.Equal("ok S[7, 8]", await Outcome(list + "Next([(7, 8)])"));
        Assert.Equal(await Outcome(list + "Some([[7]])"), await Outcome(list + "Next([[7]])"));
        Assert.StartsWith("err TypeMismatch:", await Outcome(list + "Next(7)"), StringComparison.Ordinal);
        Assert.Equal("[x]", Arguments(CallTo(Property(SourceProvenance.ParseValid(list + "0").Root, "Next"), "Some").Args));

        const string sequence = "P((x, x, y)) = [x, y]\nSome = [P]:0\nNext = [Some]:0\n";
        Assert.Equal("ok L[7, 8]", await Outcome(sequence + "Next((7, 8))"));
        Assert.StartsWith("err TypeMismatch:", await Outcome(sequence + "Next([7, 8])"), StringComparison.Ordinal);
        Assert.Equal("(x, y)", Arguments(CallTo(Property(SourceProvenance.ParseValid(sequence + "0").Root, "Next"), "Some").Args));
    }

    [Fact]
    public void SharedNameNode_KeepsOccurrenceSupplyAndNeutralCalleeContext()
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(P + "Some = P\nSome(7)");
        var shared = new Expr.Resolve("P");
        var some = Property(root, "Some") with
        {
            Output = new OutputBundle([new Expr.ListLiteral(new OutputBundle(
                [shared, shared, new Expr.Call(shared, new OutputBundle([new Expr.Num(7), new Expr.Num(7)]))]))]),
        };
        root = root with { Properties = root.Properties.Select(p => p.Name == "Some" ? p with { Value = some } : p).ToArray() };
        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(root);
        Assert.Empty(diagnostics);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected);
        var alias = Property(Assert.IsType<Algorithm.User>(resolved), "Some");
        Assert.Equal(["x"], alias.Params);
        var list = Assert.IsType<Expr.ListLiteral>(Assert.Single(alias.Output));
        Assert.Same(list.Items[0], list.Items[1]);
        Assert.Equal("x, x", Arguments(Assert.IsType<Expr.Call>(list.Items[0]).Args));
        Assert.IsType<Expr.Resolve>(Assert.IsType<Expr.Call>(list.Items[2]).Function);
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(PropertyExposureResolver.Resolve(resolved)));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([(Decimal128)7m, (Decimal128)7m, (Decimal128)7m], result.Value);
    }

    [Theory]
    [InlineData(64)]
    [InlineData(512)]
    public void NestedNameMerge_VisitsEachCaptureOnlyOnce(int width)
    {
        var items = new CountedPatterns(Enumerable.Range(0, width)
            .SelectMany(i => new ParameterPattern[] { new CaptureParameterPattern($"a{i}"), new CaptureParameterPattern("x") })
            .ToArray());
        IReadOnlyList<IReadOnlyList<ParameterPattern>> dependencies = [[new SequenceValueParameterPattern(items)]];
        var merge = typeof(ImplicitArgumentResolver).GetMethod("MergeLiftedTail", BindingFlags.NonPublic | BindingFlags.Static)!;
        var result = Assert.IsAssignableFrom<IReadOnlyList<ParameterPattern>>(merge.Invoke(null, [dependencies]));
        Assert.InRange(items.Reads, items.Count, 2 * items.Count);
        Assert.Equal(new[] { "a0", "x" }.Concat(Enumerable.Range(1, width - 1).Select(i => $"a{i}")),
            ParameterPattern.FlattenCaptures(result).Select(p => p.Name));
        Assert.IsType<SequenceValueParameterPattern>(Assert.Single(result));
    }

    private sealed class CountedPatterns(IReadOnlyList<ParameterPattern> items) : IReadOnlyList<ParameterPattern>
    {
        public int Reads { get; private set; }
        public int Count => items.Count;
        public ParameterPattern this[int index] { get { Reads++; return items[index]; } }
        public IEnumerator<ParameterPattern> GetEnumerator()
        {
            for (var i = 0; i < Count; i++) yield return this[i];
        }
        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }

    /// <summary>
    /// Across the whole executable specification, every algorithm whose signature is INFERRED (no
    /// written parameter list) binds each parameter name once — forwarding never turns a callee's
    /// repeated occurrences into repeated caller parameters. An exact alias is exempt: its signature
    /// is not inferred but INHERITED, verbatim, from its callee.
    /// </summary>
    [Fact]
    public void NoInferredSignatureRepeatsAName_AcrossTheLanguageSpecCorpus()
    {
        var checkedPrograms = 0;
        foreach (var spec in LanguageSpecCorpus.AllCases())
        {
            var parsed = Parser.Parse(spec.Source);
            if (parsed.HasErrors)
                continue;
            AssertNoInferredSignatureRepeatsAName(parsed.Root, spec.Id);
            checkedPrograms++;
        }

        Assert.True(checkedPrograms > 100, $"only {checkedPrograms} corpus programs elaborated cleanly");
    }

    private static void AssertNoInferredSignatureRepeatsAName(Algorithm.User root, string context)
    {
        foreach (var algorithm in AllUserAlgorithms(root))
        {
            if (algorithm.HasExplicitParameterList || IsExactAlias(algorithm))
                continue;
            var names = algorithm.Params;
            Assert.True(
                names.Distinct(StringComparer.Ordinal).Count() == names.Count,
                $"{context}: an inferred signature repeats a name: ({string.Join(", ", names)})");
        }
    }

    /// <summary>
    /// An exact alias: every parameter inherited (forwarded, none written or inferred), and one row
    /// that calls the callee with exactly those parameters rebuilt.
    /// </summary>
    private static bool IsExactAlias(Algorithm.User algorithm)
    {
        if (algorithm.ForwardingParameterStart != 0 || algorithm.Output.Count != 1)
            return false;
        var arguments = algorithm.Output[0] switch
        {
            Expr.Call call => call.Args,
            Expr.DotCall { Args: { } args } => args,
            _ => null,
        };
        var rebuilt = System.Text.RegularExpressions.Regex.Replace(
            Signature(algorithm), @"\*([A-Za-z_][A-Za-z_0-9]*)", "$1*");
        return arguments is not null && Arguments(arguments) == rebuilt;
    }

    private static IEnumerable<Algorithm.User> AllUserAlgorithms(Algorithm root)
    {
        var pending = new Stack<Algorithm>();
        pending.Push(root);
        while (pending.Count > 0)
        {
            switch (pending.Pop())
            {
                case Algorithm.User user:
                    yield return user;
                    foreach (var property in user.Properties)
                        pending.Push(property.Value);
                    foreach (var expr in AllExpressions(user))
                    {
                        if (expr is Expr.AlgorithmExpr block)
                            pending.Push(block.Algorithm);
                    }

                    break;
                case Algorithm.Conditional conditional:
                    foreach (var branch in conditional.Branches)
                        pending.Push(branch.Body);
                    break;
            }
        }
    }

    /// <summary>Every expression of an algorithm's own rows (not of its properties or nested blocks).</summary>
    private static IEnumerable<Expr> AllExpressions(Algorithm.User algorithm)
    {
        var pending = new Stack<Expr>(algorithm.Output);
        while (pending.Count > 0)
        {
            var expr = pending.Pop();
            yield return expr;
            IEnumerable<Expr> children = expr switch
            {
                Expr.Call call => [call.Function, .. call.Args],
                Expr.DotCall dotCall => [dotCall.Target, .. (IEnumerable<Expr>?)dotCall.Args ?? []],
                Expr.Binary binary => [binary.Left, binary.Right],
                Expr.Comparison comparison => [comparison.First, .. comparison.Links.Select(static link => link.Operand)],
                Expr.Unary unary => [unary.Operand],
                Expr.Index index => [index.Target, index.Selector],
                Expr.SequenceSpread spread => [spread.Operand],
                Expr.SequenceConstruct construct => [construct.Left, construct.Right],
                Expr.ListLiteral list => list.Items,
                Expr.Capture capture => capture.Body,
                Expr.Grace grace => [grace.Inner],
                _ => [],
            };
            foreach (var child in children)
                pending.Push(child);
        }
    }
}
