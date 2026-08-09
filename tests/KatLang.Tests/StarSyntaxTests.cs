using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Acceptance battery for the star syntax redesign.
///
/// Prefix <c>*</c> is the collect marker in binding patterns: a collecting
/// binding <c>*name</c> collects its matched supply segment into an exact
/// immutable list. Postfix <c>*</c> is the spread marker: a spread expression
/// <c>value*</c> contributes the items of <c>value</c> to the surrounding
/// item supply. Infix <c>*</c> multiplies two values.
///
/// Disambiguation: when the star has a valid same-line expression-start
/// token after it, it is multiplication REGARDLESS of spacing (`a*b`,
/// `a* b`, `a *b`, `a * b`). Otherwise a star directly attached to the
/// completed expression is a spread marker, and an unattached star is
/// multiplication whose right operand continues on the next line. Spreading
/// before another same-line supplied item therefore requires a comma
/// (`a*, b`), because `a* b` is multiplication.
/// </summary>
public class StarSyntaxTests
{
    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString().Replace("\r\n", "\n");
    }

    private static IReadOnlyList<KatLangError> FailureErrors(string source)
    {
        var result = KatLangEngine.Run(source);
        return result switch
        {
            RunResult.ParseFailure parseFailure => parseFailure.Errors,
            RunResult.EvalFailure evalFailure => evalFailure.Errors,
            _ => throw Xunit.Sdk.FailException.ForFailure($"Expected failure but got: {result.ToDisplayString()}"),
        };
    }

    private static Diagnostic SingleError(string source)
    {
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors, $"expected a parse error for: {source}");
        var error = Assert.Single(parse.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        return error;
    }

    private static void AssertCleanParse(string source)
    {
        var parse = Parser.Parse(source);
        Assert.Empty(parse.Diagnostics);
    }

    // ── Multiplication disambiguation ───────────────────────────────────────

    [Theory]
    [InlineData("a = 6\nb = 7\na*b")]
    [InlineData("a = 6\nb = 7\na* b")]
    [InlineData("a = 6\nb = 7\na *b")]
    [InlineData("a = 6\nb = 7\na * b")]
    public void SameLineRightOperand_IsMultiplication_RegardlessOfSpacing(string source)
    {
        Assert.Equal("42", Display(source));

        var parse = Parser.Parse(source);
        Assert.Empty(parse.Diagnostics);
        var binary = Assert.IsType<Expr.Binary>(Assert.Single(parse.Root.Output));
        Assert.Equal(BinaryOp.Mul, binary.Op);
    }

    [Theory]
    [InlineData("F(a, b) = a, b\nF(6*7)", "42")]
    [InlineData("F(a, b) = a, b\nF(6* 7)", "42")]
    [InlineData("F(a, b) = a, b\nF(6 *7)", "42")]
    public void CallArgument_StarWithRightOperand_IsOneMultiplicationSlot(string source, string _)
    {
        // `F(a* b)` means `F(a * b)` — one argument — so the two-parameter
        // callable reports an arity error, proving one slot was supplied.
        var errors = FailureErrors(source);
        Assert.Contains(errors, static error => error.Message.Contains("argument"));
    }

    [Fact]
    public void CallArgument_SpreadThenComma_SuppliesSeparateSlots()
    {
        // `F(A*, b)` spreads A and then supplies b — three argument slots
        // (the call's multi-output body is observed as one sequence value).
        Assert.Equal(
            "(1, 2, 9)",
            Display("F(x, y, z) = x, y, z\nA = (1, 2)\nF(A*, 9)"));
    }

    [Fact]
    public void MultiplicationAndSpreadSlots_AgreeWithArityExpectations()
    {
        // a*b is one slot (multiplication); A*, b is spread-plus-slot.
        Assert.Equal("42", Display("F(v) = v\nF(6*7)"));
        Assert.Equal("[6, 7, 9]", Display("F(*items) = items\nA = (6, 7)\nF(A*, 9)"));
    }

    [Fact]
    public void LineEndingAttachedStar_IsSpread_NextLineIsANewRow()
    {
        // `a*` at end of line spreads a; `b` begins a new output row.
        Assert.Equal(
            "1\n2\n5",
            Display("a = (1, 2)\nb = 5\na*\nb"));
    }

    [Fact]
    public void LineEndingUnattachedStar_IsMultiplication_AcrossTheNewline()
    {
        // `a *` keeps the multiplication open; its right operand is on the
        // next physical line under ordinary operator continuation.
        Assert.Equal(
            "35",
            Display("a = 5\nb = 7\na *\nb"));
    }

    [Fact]
    public void FourWayDistinction_MultiplicationVersusSpread()
    {
        // a*b / a* b / a * b multiply; a* newline b spreads then continues.
        Assert.Equal("35", Display("a = 5\nb = 7\na*b"));
        Assert.Equal("35", Display("a = 5\nb = 7\na* b"));
        Assert.Equal("35", Display("a = 5\nb = 7\na * b"));
        Assert.Equal("5\n7", Display("a = 5\nb = 7\na*\nb"));
    }

    [Theory]
    [InlineData("a = 2\na* -3", "-6")]
    [InlineData("a = 2\na* (3)", "6")]
    [InlineData("a = 2\na*(3)", "6")]
    // Every remaining token that can begin a same-line right operand must also
    // keep the star infix: identifier, number, `{` block, `~` grace, and the
    // `not` unary. If any of these were missing from the expression-start test
    // the star would silently become a spread marker instead.
    [InlineData("a = 2\nb = 3\na* b", "6")]
    [InlineData("a = 2\na* 3", "6")]
    [InlineData("a = 2\na* {3}", "6")]
    [InlineData("a = 2\nb = 3\na* ~b", "6")]
    [InlineData("a = 2\nb = 0\na* not b", "2")]
    public void OperandLikeTokensAfterStar_AreMultiplication(string source, string expected)
    {
        Assert.Equal(expected, Display(source));
    }

    [Fact]
    public void OpenKeywordAfterAttachedStar_IsADeclarationStarter_NotAMultiplicationOperand()
    {
        // `open` is handled by the algorithm/declaration parser and is never a
        // valid right operand. The attached star must therefore complete `A*`
        // before the parser reports that the following open is out of order.
        var parse = Parser.ParseSyntax("A*open Scope");

        Assert.True(parse.HasErrors);
        Assert.Contains(
            parse.Diagnostics,
            diagnostic => diagnostic.Message.Contains(
                "'open' declaration must appear before", StringComparison.Ordinal));
        Assert.DoesNotContain(
            parse.Diagnostics,
            diagnostic => diagnostic.Message.Contains(
                "cannot be used in expression position", StringComparison.Ordinal));

        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(parse.Root.Output));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(spread.Operand).Name);
        Assert.Equal("Scope", Assert.IsType<Expr.Resolve>(Assert.Single(parse.Root.Opens)).Name);
    }

    [Fact]
    public void StringLiteralAfterStar_IsMultiplicationOperand_AndFailsAtRuntime()
    {
        // A string literal begins an expression too, so `a* 'x'` is
        // multiplication by a string — a runtime type error, never a spread of
        // `a` followed by an adjacent string item.
        Assert.NotEmpty(FailureErrors("a = 2\na* 'x'"));
    }

    [Fact]
    public void ListLiteralAfterStar_IsMultiplicationOperand_AndFailsAtRuntime()
    {
        // `[` can begin an expression, so `a* [1]` is multiplication by a
        // list — a runtime type error, never spread-plus-adjacency.
        Assert.NotEmpty(FailureErrors("a = 2\na* [1]"));
    }

    [Fact]
    public void SpreadInsideListsAndGroups_FollowsTheCommaRule()
    {
        Assert.Equal("[1, 2]", Display("a = (1, 2)\n[a*]"));
        Assert.Equal("[1, 2, 9]", Display("a = (1, 2)\n[a*, 9]"));
        Assert.Equal("[14]", Display("a = 2\n[a*7]"));
        Assert.Equal("(1, 2)", Display("a = (1, 2)\n(a*)"));
        Assert.Equal("14", Display("a = 2\n(a*7)"));
    }

    [Fact]
    public void MissingRightOperand_ReportsOrdinaryMultiplicationError()
    {
        // `values *` at end of input is multiplication with a missing right
        // operand — never reinterpreted as an attached spread.
        var parse = Parser.Parse("values = (1, 2)\nvalues *");
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static d => d.Message.Contains("Unexpected token"));
    }

    // ── Collect marker (prefix *) ───────────────────────────────────────────

    [Fact]
    public void CollectingParameter_CollectsExactList()
    {
        const string declarations = "Collect(*items) = items\n";
        Assert.Equal("[]", Display(declarations + "Collect()"));
        Assert.Equal("[1]", Display(declarations + "Collect(1)"));
        Assert.Equal("[1, 2, 3]", Display(declarations + "Collect(1, 2, 3)"));
    }

    [Fact]
    public void MiddleCollectingParameter_CollectsTheMatchedSegment()
    {
        const string declarations = "Middle(first, *middle, last) = middle\n";
        Assert.Equal("[]", Display(declarations + "Middle(1, 2)"));
        Assert.Equal("[2]", Display(declarations + "Middle(1, 2, 3)"));
        Assert.Equal("[2, 3, 4]", Display(declarations + "Middle(1, 2, 3, 4, 5)"));
    }

    [Fact]
    public void LeadingAndTrailingCollectingParameters_Work()
    {
        Assert.Equal("[1, 2]", Display("Pre(*prefix, last) = prefix\nPre(1, 2, 3)"));
        Assert.Equal("[2, 3]", Display("Suffix(first, *suffix) = suffix\nSuffix(1, 2, 3)"));
    }

    [Fact]
    public void CollectingDeconstruction_AllPositions()
    {
        Assert.Equal("[1, 2, 3]", Display("*items = 1, 2, 3\nitems"));
        Assert.Equal("[2, 3]", Display("first, *middle, last = 1, 2, 3, 4\nmiddle"));
        Assert.Equal("[1, 2]", Display("*init, last = 1, 2, 3\ninit"));
        Assert.Equal("[2, 3]", Display("first, *rest = 1, 2, 3\nrest"));
        Assert.Equal("[]", Display("first, *rest = 1\nrest"));
    }

    [Fact]
    public void NestedSequenceValuePattern_SupportsCollectingBinding()
    {
        Assert.Equal(
            "[2, 3]",
            Display("F((x, *y, z)) = y\nF((1, 2, 3, 4))"));
    }

    [Fact]
    public void PublicCollectingParameter_IsSupported()
    {
        Assert.Equal("[1, 2]", Display("public Collect(*items) = items\nCollect(1, 2)"));
    }

    [Fact]
    public void CollectMarkerSpan_IsExact_AndPrefix()
    {
        var parse = Parser.Parse("Collect(*items) = items\nCollect(1)");
        Assert.Empty(parse.Diagnostics);

        var collect = Assert.Single(parse.Root.Properties, static p => p.Name == "Collect");
        var parameter = Assert.Single(collect.Value.ExplicitParameters);
        Assert.Equal("items", parameter.Name);
        Assert.Equal(ParameterKind.Collecting, parameter.Kind);
        // `*` sits at line 1, column 9; the name at columns 10..14.
        Assert.Equal(new SourceSpan(1, 9, 1, 9), parameter.CollectMarkerSpan);
        Assert.Equal(new SourceSpan(1, 10, 1, 14), parameter.Span);
        Assert.Equal("*items", parameter.DisplayName);
    }

    [Fact]
    public void DeconstructionCollectMarkerSpan_IsExact()
    {
        var parse = Parser.Parse("first, *middle, last = 1, 2, 3\nmiddle");
        Assert.Empty(parse.Diagnostics);

        // The deconstruction elaborates into helper properties whose shared
        // binding pattern carries the source-backed collect-marker span.
        var collector = new CollectMarkerSpanCollector();
        collector.VisitAlgorithm(parse.Root);
        var markerSpan = Assert.Single(collector.MarkerSpans.Distinct());
        Assert.Equal(new SourceSpan(1, 8, 1, 8), markerSpan);
    }

    private sealed class CollectMarkerSpanCollector : AstWalker
    {
        public List<SourceSpan> MarkerSpans { get; } = [];

        protected override void VisitCollectMarker(SourceSpan span)
            => MarkerSpans.Add(span);
    }

    // ── Malformed collect-marker forms ──────────────────────────────────────

    [Fact]
    public void DetachedCollectMarker_InParameterList_ReportsAttachmentError_NoCollectingBinding()
    {
        var error = SingleError("F(* items) = items\nF(1, 2)");
        Assert.Contains("directly attached", error.Message);
        Assert.Contains("*items", error.Message);

        // Recovery binds `items` as an ordinary fixed parameter.
        var parse = Parser.Parse("F(* items) = items\nF(1, 2)");
        var f = Assert.Single(parse.Root.Properties, static p => p.Name == "F");
        var parameter = Assert.Single(f.Value.ExplicitParameters);
        Assert.Equal(ParameterKind.Normal, parameter.Kind);
        Assert.Null(parameter.CollectMarkerSpan);
    }

    [Fact]
    public void RepeatedCollectMarker_InParameterList_ReportsError_NoCollectingBinding()
    {
        var error = SingleError("F(**items) = items\nF(1)");
        Assert.Contains("exactly one collect marker", error.Message);

        var parse = Parser.Parse("F(**items) = items\nF(1)");
        var f = Assert.Single(parse.Root.Properties, static p => p.Name == "F");
        var parameter = Assert.Single(f.Value.ExplicitParameters);
        Assert.Equal(ParameterKind.Normal, parameter.Kind);
    }

    [Fact]
    public void TwoCollectingParameters_AtOneLevel_ReportError()
    {
        var error = SingleError("F(first, *middle, *suffix) = middle\nF(1, 2, 3)");
        Assert.Contains("Only one collecting binding", error.Message);
    }

    [Fact]
    public void RepeatedCollectMarker_InDeconstruction_ReportsError_NoCollectingBinding()
    {
        var parse = Parser.Parse("first, **middle, last = 1, 2, 3\nfirst");
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static d => d.Message.Contains("exactly one collect marker"));
    }

    [Fact]
    public void DetachedCollectMarker_InDeconstruction_ReportsAttachmentError()
    {
        var parse = Parser.Parse("a, * b, c = 1, 2, 3\na");
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static d => d.Message.Contains("directly attached"));
    }

    [Fact]
    public void PrefixStarInExpressionPosition_ReportsTargetedError_AndRecovers()
    {
        var error = SingleError("values = 1, 2\nx = *values\nx");
        Assert.Contains("collect marker", error.Message);
        Assert.Contains("binding patterns", error.Message);
    }

    [Fact]
    public void PrefixStarRecovery_NeverConsumesOpenAsItsOperand()
    {
        // The prefix-star recovery resumes on the operand the star was
        // attached to, and it decides "is there an operand?" with the SAME
        // classifier the postfix spread/multiplication split uses
        // (CanStartMultiplicationOperand). `open` is the one token that
        // begins an expression for adjacency purposes but is never a star
        // operand, so recovery must stop before it and leave the declaration
        // to the algorithm parser — mirroring the postfix side pinned by
        // OpenKeywordAfterAttachedStar_IsADeclarationStarter_NotAMultiplicationOperand.
        var parse = Parser.ParseSyntax("open Scope\nx = *open Scope");

        Assert.Contains(
            parse.Diagnostics,
            diagnostic => diagnostic.Message.Contains("collect marker", StringComparison.Ordinal));
        Assert.DoesNotContain(
            parse.Diagnostics,
            diagnostic => diagnostic.Message.Contains(
                "'open' is a declaration and cannot be used in expression position",
                StringComparison.Ordinal));
    }

    [Fact]
    public void PrefixStarInCallArgument_ReportsTargetedError()
    {
        var parse = Parser.Parse("F(x) = x\nA = (1, 2)\nF(*A)");
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static d => d.Message.Contains("collect marker"));
    }

    [Fact]
    public void MalformedCollectMarker_LaterDeclarationsStillParse()
    {
        var parse = Parser.Parse("F(* items) = items\nG = 5\nG");
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Root.Properties, static p => p.Name == "G");
    }

    [Fact]
    public void PostfixStarInBindingPattern_ReportsSpreadMarkerError_NoCollectingBinding()
    {
        var error = SingleError("F(items*) = items\nF(1)");
        Assert.Contains("spread marker", error.Message);
        Assert.Contains("*items", error.Message);

        var parse = Parser.Parse("F(items*) = items\nF(1)");
        var f = Assert.Single(parse.Root.Properties, static p => p.Name == "F");
        var parameter = Assert.Single(f.Value.ExplicitParameters);
        Assert.Equal(ParameterKind.Normal, parameter.Kind);
    }

    // ── Spread marker (postfix *) ───────────────────────────────────────────

    [Fact]
    public void SpreadMarker_LowersToTheOneSpreadNode_WithExactSpans()
    {
        var parse = Parser.Parse("A = (1, 2)\nA*");
        Assert.Empty(parse.Diagnostics);

        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(parse.Root.Output));
        Assert.IsType<Expr.Resolve>(spread.Operand);
        Assert.Equal(new SourceSpan(2, 1, 2, 2), spread.Span);
        Assert.Equal(new SourceSpan(2, 2, 2, 2), spread.SpreadMarkerSpan);
        Assert.Equal(new SourceSpan(2, 1, 2, 1), spread.Operand.Span);
    }

    [Theory]
    [InlineData("items* ", "1\n2", "items = (1, 2)\n")]
    [InlineData("Calculate(5)*", "5\n6", "Calculate(x) = x, x + 1\n")]
    [InlineData("(2 + 3)*", "5", "")]
    [InlineData("[1, 2]*", "1\n2", "")]
    [InlineData("()*", "", "")]
    [InlineData("[]*", "", "")]
    [InlineData("'text'*", "text", "")]
    [InlineData("7*", "7", "")]
    public void SpreadExpressions_ContributeItemsToRootOutput(string expression, string expected, string declarations)
    {
        Assert.Equal(expected, Display(declarations + expression));
    }

    [Fact]
    public void CollectBoundaries_SpreadVersusUnspreadArguments()
    {
        const string declarations = "Collect(*items) = items\n";
        Assert.Equal("[[1, 2]]", Display(declarations + "Collect([1, 2])"));
        Assert.Equal("[1, 2]", Display(declarations + "Collect([1, 2]*)"));
        Assert.Equal("[(1, 2)]", Display(declarations + "Collect((1, 2))"));
        Assert.Equal("[1, 2]", Display(declarations + "Collect((1, 2)*)"));
        Assert.Equal("[()]", Display(declarations + "Collect(())"));
        Assert.Equal("[]", Display(declarations + "Collect(()*)"));
        Assert.Equal("[[]]", Display(declarations + "Collect([])"));
        Assert.Equal("[]", Display(declarations + "Collect([]*)"));
        // One-boundary spread only: nested structures are not flattened.
        Assert.Equal("[[1, 2]]", Display(declarations + "Collect([[1, 2]]*)"));
    }

    [Fact]
    public void Forwarding_SpreadOfCollectedList_ResuppliesExactItems()
    {
        const string declarations =
            "Target(*items) = items\n" +
            "Forward(*items) = Target(items*)\n";
        Assert.Equal("[]", Display(declarations + "Forward()"));
        Assert.Equal("[1]", Display(declarations + "Forward(1)"));
        Assert.Equal("[1, 2, 3]", Display(declarations + "Forward(1, 2, 3)"));
        Assert.Equal("[[1, 2]]", Display(declarations + "Forward([1, 2])"));
        Assert.Equal("[1, 2]", Display(declarations + "Forward([1, 2]*)"));
        Assert.Equal("[(1, 2)]", Display(declarations + "Forward((1, 2))"));
        Assert.Equal("[1, 2]", Display(declarations + "Forward((1, 2)*)"));
        Assert.Equal("[()]", Display(declarations + "Forward(())"));
        Assert.Equal("[]", Display(declarations + "Forward(()*)"));
        Assert.Equal("[[]]", Display(declarations + "Forward([])"));
        Assert.Equal("[]", Display(declarations + "Forward([]*)"));
    }

    [Fact]
    public void FluentForwarding_IsEquivalentToTheNonFluentForm()
    {
        const string fluent =
            "Target(*items) = items\n" +
            "Forward(*items) = items*.Target\n";
        const string plain =
            "Target(*items) = items\n" +
            "Forward(*items) = Target(items*)\n";

        foreach (var call in new[] { "Forward()", "Forward(1)", "Forward(1, 2, 3)", "Forward([1, 2]*)", "Forward((1, 2))" })
        {
            Assert.Equal(Display(plain + call), Display(fluent + call));
        }
    }

    // ── Fluent dot-chain (supply transition) ────────────────────────────────

    [Fact]
    public void FluentChain_LowersToLexicalCall_WithSpreadAsLeadingArgument()
    {
        var parse = Parser.Parse("Target(a, b) = a + b\nx = (1, 2)\nx*.Target");
        Assert.Empty(parse.Diagnostics);

        var call = Assert.IsType<Expr.Call>(Assert.Single(parse.Root.Output));
        var callee = Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("Target", callee.Name);
        var argument = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args));
        Assert.IsType<Expr.Resolve>(argument.Operand);
    }

    [Fact]
    public void FluentChain_EqualsTheExplicitCallAst()
    {
        static Expr ParseSingleOutput(string source)
        {
            var parse = Parser.Parse(source);
            Assert.Empty(parse.Diagnostics);
            return Assert.Single(parse.Root.Output);
        }

        var fluent = ParseSingleOutput("Target(a, b) = a + b\nx = (1, 2)\nx*.Target");
        var explicitCall = ParseSingleOutput("Target(a, b) = a + b\nx = (1, 2)\nTarget(x*)");

        // Identical AST up to source spans: same call shape, same callee, same
        // spread argument.
        var fluentCall = Assert.IsType<Expr.Call>(fluent);
        var plainCall = Assert.IsType<Expr.Call>(explicitCall);
        Assert.Equal(
            Assert.IsType<Expr.Resolve>(fluentCall.Function).Name,
            Assert.IsType<Expr.Resolve>(plainCall.Function).Name);
        Assert.Equal(
            Assert.IsType<Expr.Resolve>(Assert.IsType<Expr.SequenceSpread>(Assert.Single(fluentCall.Args)).Operand).Name,
            Assert.IsType<Expr.Resolve>(Assert.IsType<Expr.SequenceSpread>(Assert.Single(plainCall.Args)).Operand).Name);
    }

    [Fact]
    public void FluentChain_ImplicitCallableParameterParity_IsIntentional()
    {
        const string preamble = "A = (1, 2)\n";

        static (Algorithm Algorithm, Expr.Call Call, CallableSignature Signature) ParseUse(string source)
        {
            var parse = Parser.Parse(source);
            Assert.Empty(parse.Diagnostics);
            var use = Assert.Single(parse.Root.Properties, static property => property.Name == "Use").Value;
            return (
                use,
                Assert.IsType<Expr.Call>(Assert.Single(use.Output)),
                CallableSignature.FromAlgorithm("Use", use));
        }

        var explicitForm = ParseUse(preamble + "Use = Target(A*)");
        var fluentForm = ParseUse(preamble + "Use = A*.Target");

        Assert.Equal(["Target"], explicitForm.Algorithm.Params);
        Assert.Equal(explicitForm.Algorithm.Params, fluentForm.Algorithm.Params);
        Assert.Equal(explicitForm.Signature.DisplayText, fluentForm.Signature.DisplayText);
        Assert.Equal("Target", Assert.IsType<Expr.Param>(explicitForm.Call.Function).Name);
        Assert.Equal("Target", Assert.IsType<Expr.Param>(fluentForm.Call.Function).Name);

        const string compatible = "Add(x, y) = x + y\n";
        Assert.Equal(
            Display(preamble + compatible + "Use = Target(A*)\nUse(Add)"),
            Display(preamble + compatible + "Use = A*.Target\nUse(Add)"));

        const string incompatible = "One(x) = x\n";
        var explicitErrors = FailureErrors(
            preamble + incompatible + "Use = Target(A*)\nUse(One)").Select(static error => error.Message);
        var fluentErrors = FailureErrors(
            preamble + incompatible + "Use = A*.Target\nUse(One)").Select(static error => error.Message);
        Assert.Equal(explicitErrors, fluentErrors);

        // A typo-shaped name follows the SAME accepted rule. This deliberately
        // pins uniform implicit inference; it is not accidental typo tolerance
        // attached to the fluent spelling.
        Assert.Equal(
            "3",
            Display(preamble + compatible + "Use = Targe(A*)\nUse(Add)"));
        Assert.Equal(
            "3",
            Display(preamble + compatible + "Use = A*.Targe\nUse(Add)"));
    }

    [Fact]
    public void FluentChain_RunsTheSupplyThroughTheTarget()
    {
        Assert.Equal("3", Display("Target(a, b) = a + b\nx = (1, 2)\nx*.Target"));
        Assert.Equal("3", Display("Target(a, b) = a + b\nx = (1, 2)\nTarget(x*)"));
    }

    [Fact]
    public void FluentChain_WithDotCallOperand()
    {
        const string declarations =
            "Calculate(v) = v, v + 1\n" +
            "Target(a, b) = a * 10 + b\n" +
            "x = 4\n";
        Assert.Equal("45", Display(declarations + "x.Calculate*.Target"));
        Assert.Equal("45", Display(declarations + "Target(x.Calculate*)"));
    }

    [Fact]
    public void FluentChain_ContinuesThroughOrdinaryPostfixSyntax()
    {
        const string declarations =
            "Calculate(v) = v, v + 1\n" +
            "Target(a, b) = (a, b)\n" +
            "Other(pair) = pair.count\n" +
            "x = 4\n";
        Assert.Equal("2", Display(declarations + "x.Calculate*.Target.Other"));
    }

    [Fact]
    public void FluentChain_GroupedOperandIsEquivalent()
    {
        const string declarations =
            "Calculate(v) = v, v + 1\n" +
            "Target(a, b) = a * 10 + b\n" +
            "x = 4\n";
        Assert.Equal(
            Display(declarations + "x.Calculate*.Target"),
            Display(declarations + "(x.Calculate)*.Target"));
    }

    [Fact]
    public void SpreadInsideAGroup_IsACaptureReceiver_NotAFluentSupply()
    {
        // `A*.F` and `(A*).F` are two DIFFERENT receivers, and the difference
        // follows from the central model rather than from the star rule:
        //
        //   A*.F   — the spread stays a SUPPLY. The fluent dot lowers to the
        //            lexical call `F(A*)`, so the items become argument SLOTS.
        //   (A*).F — the parentheses are a CAPTURE receiver
        //            (`capture : Supply -> Value`). The items materialize as
        //            ONE sequence value first, and `.F` is then an ordinary
        //            dot-call on that value.
        //
        // They coincide on a collecting callable, which re-collects either
        // shape into the same list...
        const string collecting = "F(*v) = v\nA = (1, 2)\n";
        Assert.Equal("[1, 2]", Display(collecting + "A*.F"));
        Assert.Equal("[1, 2]", Display(collecting + "(A*).F"));

        // ...but they are decisively different at a FIXED-arity builtin,
        // which is the observation that pins the distinction: three argument
        // slots do not fit `count(collection)`, while the captured sequence
        // value is exactly one collection argument.
        const string counted = "A = (1, 2, 3)\n";
        Assert.Equal("3", Display(counted + "(A*).count"));
        var fluentError = Assert.Single(FailureErrors(counted + "A*.count"));
        var groupedOperandError = Assert.Single(FailureErrors(counted + "(A)*.count"));
        Assert.Equal(fluentError.Message, groupedOperandError.Message);
    }

    [Fact]
    public void SpreadReceiverRoutes_BuildTheirOwnDistinctAstShapes()
    {
        // The two routes are distinguishable in the AST, not just at runtime:
        // the ungrouped form is a Call with the spread as leading argument,
        // the grouped form is a DotCall whose target is the captured group.
        var ungrouped = Assert.IsType<Expr.Call>(
            Assert.Single(SourceProvenance.ParseValid("F(*v) = v\nA = (1, 2)\nA*.F").Root.Output));
        Assert.IsType<Expr.SequenceSpread>(Assert.Single(ungrouped.Args));

        var grouped = Assert.IsType<Expr.DotCall>(
            Assert.Single(SourceProvenance.ParseValid("F(*v) = v\nA = (1, 2)\n(A*).F").Root.Output));
        Assert.Equal("F", grouped.Name);
        var capture = Assert.IsType<Expr.Capture>(grouped.Target);
        Assert.IsType<Expr.SequenceSpread>(Assert.Single(capture.Body));
    }

    [Fact]
    public void FluentChain_WithExplicitExtraArguments()
    {
        const string declarations = "Target(a, b, c) = a * 10 + b + c\nx = (4, 3)\n";
        Assert.Equal("45", Display(declarations + "x*.Target(2)"));
        Assert.Equal(
            Display(declarations + "Target(x*, 2)"),
            Display(declarations + "x*.Target(2)"));
    }

    [Fact]
    public void FluentChain_ClauseSelectionAndArityErrorsMatchExplicitCall()
    {
        const string clauses =
            "F(0, 0) = 100\n" +
            "F(x, y) = x + y\n" +
            "A = (0, 0)\n";
        Assert.Equal("100", Display(clauses + "F(A*)"));
        Assert.Equal(Display(clauses + "F(A*)"), Display(clauses + "A*.F"));

        const string fixedArity = "One(x) = x\nA = (1, 2)\n";
        var explicitErrors = FailureErrors(fixedArity + "One(A*)").Select(static error => error.Message);
        var fluentErrors = FailureErrors(fixedArity + "A*.One").Select(static error => error.Message);
        Assert.Equal(explicitErrors, fluentErrors);
    }

    [Fact]
    public void FluentChain_TargetsResolveLexically_NotStructurally()
    {
        // The spread receiver is a supply, not a value: `.Target` never does
        // structural lookup inside the operand value's members. The lexical
        // `Target` receives the spread item (the property's value) as its
        // argument.
        const string source =
            "Target(v) = 100\n" +
            "A = (5)\n" +
            "A*.Target";
        Assert.Equal("100", Display(source));
    }

    // ── Repeated spread ─────────────────────────────────────────────────────

    [Fact]
    public void RepeatedSpread_BuildsDirectlyNestedSpreadNodes_WithDistinctMarkerSpans()
    {
        var parse = Parser.Parse("value = [[7]]\nvalue**");
        Assert.Empty(parse.Diagnostics);

        var outer = Assert.IsType<Expr.SequenceSpread>(Assert.Single(parse.Root.Output));
        var inner = Assert.IsType<Expr.SequenceSpread>(outer.Operand);
        Assert.IsType<Expr.Resolve>(inner.Operand);
        Assert.Equal(new SourceSpan(2, 7, 2, 7), outer.SpreadMarkerSpan);
        Assert.Equal(new SourceSpan(2, 6, 2, 6), inner.SpreadMarkerSpan);
    }

    [Fact]
    public void RepeatedSpread_PreservesCompositionalSemantics()
    {
        Assert.Equal("7", Display("[[7]]**"));
        Assert.Equal("1\n2", Display("((1, 2))**"));
        Assert.Equal("", Display("[()]**"));
        Assert.Equal("", Display("[[]]**"));
    }

    [Fact]
    public void RepeatedSpread_FollowedByCommaOrDot_Works()
    {
        Assert.Equal("7\n9", Display("value = [[7]]\nvalue**, 9"));
        Assert.Equal("8", Display("Target(v) = v + 1\nvalue = [[7]]\nvalue**.Target"));
    }

    [Theory]
    [InlineData("value = [[7]]\nvalue**next\nnext = 2")]
    [InlineData("value = [[7]]\nvalue** next\nnext = 2")]
    public void RepeatedSpread_WithSameLineRightOperand_IsRejectedAsSpreadTimesOperand(string source)
    {
        // The second star has a same-line right operand, so it parses as
        // multiplication whose left operand is a spread — the documented
        // deterministic rejection (never exponentiation, never adjacency).
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static d => d.Message.Contains("scalar operand"));
    }

    // Repeated spread is ordinary composition, not recursive flattening:
    // `value**` means `(value*)*`. The first star produces an item supply,
    // the ordinary expression boundary captures that supply back into one
    // value, and the second star spreads the captured value. A second star
    // therefore changes the observable supply only when the first spread
    // contributes exactly one structured value that exposes another item
    // boundary. Observed through a collecting callable so the exact supplied
    // items are pinned as an exact list.

    private const string CollectDeclaration = "Collect(*items) = items\n";

    [Theory]
    [InlineData("[]")]
    [InlineData("[7]")]
    [InlineData("[[7]]")]
    [InlineData("[(1, 2)]")]
    [InlineData("[[1, 2], [3, 4]]")]
    [InlineData("[[1, 2], 3]")]
    [InlineData("(1, 2)")]
    [InlineData("5")]
    public void RepeatedSpread_AgreesWithTheExplicitlyGroupedForm(string operand)
    {
        // The compositional law itself: `A**` and `(A*)*` are observationally
        // equivalent for every operand cardinality and item shape.
        var stacked = Display($"{CollectDeclaration}A = {operand}\nCollect(A**)");
        var grouped = Display($"{CollectDeclaration}A = {operand}\nCollect((A*)*)");
        Assert.Equal(grouped, stacked);
    }

    [Fact]
    public void RepeatedSpread_ZeroItemFirstSpread_StaysZero()
    {
        // `[]*` supplies zero items; the intermediate capture is `()`, whose
        // item view is also empty, so `[]**` supplies zero items too.
        Assert.Equal("[]", Display(CollectDeclaration + "Collect([]*)"));
        Assert.Equal("[]", Display(CollectDeclaration + "Collect([]**)"));
    }

    [Fact]
    public void RepeatedSpread_SingletonStructuredFirstSpread_OpensTheInnerBoundary()
    {
        // The first spread contributes exactly one item, `[7]`; singleton
        // capture collapses to that item, so the second star can spread its
        // inner list boundary.
        Assert.Equal("[[7]]", Display(CollectDeclaration + "Collect([[7]]*)"));
        Assert.Equal("[7]", Display(CollectDeclaration + "Collect([[7]]**)"));
    }

    [Fact]
    public void RepeatedSpread_SingletonScalarFirstSpread_IsNeutral()
    {
        // The captured singleton atom has a one-item view (spread is total),
        // so the second star changes nothing.
        Assert.Equal("[7]", Display(CollectDeclaration + "Collect([7]*)"));
        Assert.Equal("[7]", Display(CollectDeclaration + "Collect([7]**)"));
    }

    [Fact]
    public void RepeatedSpread_MultiItemFirstSpread_IsAFixedPoint_NotRecursiveFlattening()
    {
        // THE anti-flattening regression: after the first spread contributes
        // two items, capture creates a sequence containing those two items and
        // the second spread restores the SAME two-item supply. A refactor that
        // replaced capture-law composition with a concatMap-style lift (spread
        // every item one more level) would produce [1, 2, 3, 4] here.
        const string value = "A = [[1, 2], [3, 4]]\n";
        var once = Display(CollectDeclaration + value + "Collect(A*)");
        var twice = Display(CollectDeclaration + value + "Collect(A**)");
        Assert.Equal("[[1, 2], [3, 4]]", once);
        Assert.Equal(once, twice);
        Assert.NotEqual("[1, 2, 3, 4]", twice);

        // The same fixed point at root output rows.
        Assert.Equal(Display(value + "A*"), Display(value + "A**"));
        Assert.Equal("[1, 2]\n[3, 4]", Display(value + "A**"));
    }

    [Fact]
    public void RepeatedSpread_MixedMultiItemFirstSpread_KeepsEveryItemUnopened()
    {
        // A multi-item supply is a fixed point even when SOME of its items are
        // structured: the second star re-spreads the captured pair, it does
        // not selectively open the structured member.
        const string value = "A = [[1, 2], 3]\n";
        var once = Display(CollectDeclaration + value + "Collect(A*)");
        var twice = Display(CollectDeclaration + value + "Collect(A**)");
        Assert.Equal("[[1, 2], 3]", once);
        Assert.Equal(once, twice);
    }

    [Fact]
    public void RepeatedSpread_EvaluatesTheOperandExactlyOnce_StepAccounting()
    {
        // Same pinning approach as the single-spread test: the minimal
        // evaluation-step budget for `value**` matches a baseline that
        // evaluates the operand once — peeling the layers must not re-evaluate
        // the innermost operand per written star.
        const long budgetCap = 100_000;

        static bool Succeeds(string source, long maxSteps)
            => KatLangEngine.Run(
                source,
                new RunOptions { EvaluationLimits = new EvaluationLimits { MaxSteps = maxSteps } })
                is RunResult.Success;

        static long MinimalSteps(string source)
        {
            long low = 1, high = budgetCap;
            Assert.True(Succeeds(source, budgetCap), $"expected success under {budgetCap} steps: {source}");
            while (low < high)
            {
                var mid = low + ((high - low) / 2);
                if (Succeeds(source, mid))
                    high = mid;
                else
                    low = mid + 1;
            }

            return low;
        }

        const string preamble =
            "Inner(seed) = seed, seed + 1\n" +
            "Make(seed) = Inner(seed)\n";
        var baseline = MinimalSteps(preamble + "count(Make(1))");
        var stackedForm = MinimalSteps(preamble + "count((Make(1)**))");

        Assert.Equal(2, baseline);
        Assert.Equal(baseline, stackedForm);
    }

    [Fact]
    public void RepeatedSpread_BoundedLongChain_IsStackSafeAndStaysAFixedPoint()
    {
        // A postfix-star chain at the parser's expression-chain budget peels
        // iteratively and evaluates without deep recursion. Extra layers on a
        // scalar and on a multi-item sequence are fixed points.
        var stars = new string('*', Parser.MaxExpressionChainDepth);
        Assert.Equal("7", Display("value = 7\nvalue" + stars));
        Assert.Equal("1\n2", Display("value = (1, 2)\nvalue" + stars));
    }

    // ── Value/Supply interactions around selection and fluent calls ────────

    [Fact]
    public void SelectThenSpread_VersusSpreadCaptureThenSelect_AreDifferentOperations()
    {
        const string value = "A = [[1, 2], [3, 4]]\n";

        // `A:0*` — the star attaches to the completed index, so this SELECTS
        // the stored list `[1, 2]` first and then spreads the selected value.
        Assert.Equal("1\n2", Display(value + "A:0*"));
        Assert.Equal(Display(value + "(A:0)*"), Display(value + "A:0*"));

        // `(A*):0` — the parentheses CAPTURE the two-item spread supply as
        // one sequence value first, and selection projects from that value.
        Assert.Equal("[1, 2]", Display(value + "(A*):0"));

        // The two forms are not interchangeable.
        Assert.NotEqual(Display(value + "(A:0)*"), Display(value + "(A*):0"));
    }

    [Fact]
    public void SpreadAfterFluentCallResult_SpreadsTheCallResult()
    {
        // `A*.F*` is the call `F(A*)` with one more attached star spreading
        // the RESULT of `F` — the final star operates on the call's one
        // returned value, not on the receiver supply.
        const string source = CollectDeclaration + "A = (1, 2)\nA*.Collect*";
        Assert.Equal("1\n2", Display(source));

        var parse = Parser.Parse(source);
        Assert.Empty(parse.Diagnostics);
        var root = Assert.IsType<Expr.SequenceSpread>(Assert.Single(parse.Root.Output));
        Assert.IsType<Expr.Call>(root.Operand);
    }

    [Fact]
    public void RepeatedSpreadReceiver_FeedsTheFluentCallLikeTheExplicitSpelling()
    {
        // `A**.F` lowers to `F(A**)`: the capture-law repeated spread supplies
        // the argument slots of the lexical call.
        Assert.Equal("[7]", Display(CollectDeclaration + "A = [[7]]\nA**.Collect"));
        Assert.Equal(
            Display(CollectDeclaration + "A = [[1, 2], [3, 4]]\nCollect(A**)"),
            Display(CollectDeclaration + "A = [[1, 2], [3, 4]]\nA**.Collect"));
    }

    // ── Scalar spread through a collecting call ─────────────────────────────

    [Fact]
    public void CollectingCall_ScalarSpread_IsObservationallyNeutral()
    {
        // The item view is total: an atom contributes itself as a one-item
        // supply, so spreading an atom is neutral in this collecting context.
        Assert.Equal("[5]", Display(CollectDeclaration + "Collect(5)"));
        Assert.Equal("[5]", Display(CollectDeclaration + "Collect(5*)"));
    }

    // ── Minimum arity of mixed collecting parameter lists ───────────────────

    [Fact]
    public void MixedCollectingParameterList_RequiresTheFixedItemMinimum()
    {
        // `F(first, *middle, last)` has two fixed bindings, so a call must
        // supply at least two items; the movable collecting parameter collects
        // the (possibly empty) middle as an exact list.
        const string declaration = "F(first, *middle, last) = middle\n";
        Assert.Equal("[]", Display(declaration + "F(1, 2)"));
        Assert.Equal("[2]", Display(declaration + "F(1, 2, 3)"));

        var errors = FailureErrors(declaration + "F(1)");
        Assert.Contains(errors, static error => error.Message.Contains(
            "Callable `F(first, *middle, last)` expects at least 2 items, but received 1 item.",
            StringComparison.Ordinal));
    }

    // ── Invalid scalar embeddings ───────────────────────────────────────────

    [Theory]
    [InlineData("values = (1, 2)\n1 + values*")]
    [InlineData("values = (1, 2)\n-values*")]
    [InlineData("values = (1, 2)\nvalues* * 2")]
    [InlineData("values = (1, 2)\n2 * values*")]
    public void SpreadInScalarPosition_ReportsTargetedError(string source)
    {
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static d =>
            d.Message.Contains("spread expression") && d.Message.Contains("scalar operand"));
    }

    [Fact]
    public void SelectionOnSpread_ReportsValueSupplyDiagnostic_WithExactMessageSpanAndRecovery()
    {
        // `A*:0` — indexing a spread expression. The diagnostic must
        // distinguish the two valid intentions instead of offering them as
        // interchangeable fixes: `(A:0)*` selects first and then spreads the
        // selected value; `(A*):0` captures the spread supply and then
        // selects.
        var parse = Parser.Parse("values = (1, 2)\nvalues*:0\nAfter = 5\nAfter");
        Assert.True(parse.HasErrors);

        var error = Assert.Single(parse.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        Assert.Equal(
            "Selection cannot be applied directly to a spread expression — a spread supplies items to the surrounding item supply, not one selectable value. Write `(A:0)*` to select first and then spread the selected value, or `(A*):0` to capture the spread items as one sequence value and then select; the two forms have different meanings.",
            error.Message);
        Assert.Equal(new SourceSpan(2, 1, 2, 7), error.Span); // covers `values*`

        // Recovery unwraps the spread (no embedded SequenceSpread survives):
        // the recovered row is the ordinary index `values:0`, and following
        // declarations continue to parse.
        var recoveredRow = Assert.IsType<Expr.Index>(parse.Root.Output[0]);
        Assert.IsType<Expr.Resolve>(recoveredRow.Target);
        var selector = Assert.IsType<Expr.Num>(recoveredRow.Selector);
        Assert.Equal(0m, selector.Value);
        Assert.Contains(parse.Root.Properties, static p => p.Name == "After");
        Assert.Equal(2, parse.Root.Output.Count);

        var detector = new SpreadNodeDetector();
        foreach (var expr in parse.Root.Output)
            detector.VisitExpr(expr);
        Assert.False(detector.FoundEmbeddedSpread);
    }

    [Fact]
    public void SelectionOnRepeatedSpread_ReportsOneDiagnosticAndUnwrapsAllLayers()
    {
        var parse = Parser.Parse("values = (1, 2)\nvalues**:0");
        Assert.True(parse.HasErrors);
        var error = Assert.Single(parse.Diagnostics);
        Assert.Contains("Selection cannot be applied directly to a spread expression", error.Message);

        var recoveredRow = Assert.IsType<Expr.Index>(Assert.Single(parse.Root.Output));
        Assert.IsType<Expr.Resolve>(recoveredRow.Target);
    }

    [Fact]
    public void SpreadPlacementRecovery_NoEmbeddedSpreadSurvives()
    {
        var parse = Parser.Parse("values = (1, 2)\n1 + values*");
        Assert.True(parse.HasErrors);

        var detector = new SpreadNodeDetector();
        foreach (var expr in parse.Root.Output)
            detector.VisitExpr(expr);
        Assert.False(detector.FoundEmbeddedSpread);
    }

    private sealed class SpreadNodeDetector : AstWalker
    {
        public bool FoundEmbeddedSpread { get; private set; }

        public override void VisitExpr(Expr expr)
        {
            switch (expr)
            {
                case Expr.Binary(_, var left, var right):
                    FoundEmbeddedSpread |= left is Expr.SequenceSpread || right is Expr.SequenceSpread;
                    break;
                case Expr.Unary(_, var operand):
                    FoundEmbeddedSpread |= operand is Expr.SequenceSpread;
                    break;
                case Expr.Index(var target, var selector):
                    FoundEmbeddedSpread |= target is Expr.SequenceSpread || selector is Expr.SequenceSpread;
                    break;
            }

            base.VisitExpr(expr);
        }
    }

    // ── Evaluation once ─────────────────────────────────────────────────────

    /// <summary>
    /// The spread operand is evaluated exactly once: the minimal
    /// evaluation-step budget for the postfix-star form matches a baseline
    /// that evaluates the operand once without spreading — a second operand
    /// evaluation would strictly raise the minimal budget.
    /// </summary>
    [Fact]
    public void SpreadMarker_EvaluatesTheOperandExactlyOnce_StepAccounting()
    {
        const long budgetCap = 100_000;

        static long MinimalSteps(string source)
        {
            long low = 1, high = budgetCap;
            Assert.True(Succeeds(source, budgetCap), $"expected success under {budgetCap} steps: {source}");
            while (low < high)
            {
                var mid = low + ((high - low) / 2);
                if (Succeeds(source, mid))
                    high = mid;
                else
                    low = mid + 1;
            }

            return low;
        }

        static bool Succeeds(string source, long maxSteps)
            => KatLangEngine.Run(
                source,
                new RunOptions { EvaluationLimits = new EvaluationLimits { MaxSteps = maxSteps } })
                is RunResult.Success;

        const string preamble =
            "Inner(seed) = seed, seed + 1\n" +
            "Make(seed) = Inner(seed)\n";
        var baseline = MinimalSteps(preamble + "count(Make(1))");
        var starForm = MinimalSteps(preamble + "count((Make(1)*))");

        // The baseline's two nested user calls pin a real boundary: budget 2
        // succeeds and budget 1 fails. Spreading the result has EXACTLY the
        // same minimum. A second Make/Inner evaluation would require two more
        // charged invocations and make this equality fail deterministically.
        Assert.Equal(2, baseline);
        Assert.Equal(baseline, starForm);
    }

    // ── The name `spread` is an ordinary identifier now ─────────────────────

    [Fact]
    public void SpreadName_IsAnOrdinaryIdentifier()
    {
        Assert.Equal("5", Display("spread = 5\nspread"));
        Assert.Equal("8", Display("spread(x) = x + 1\nspread(7)"));
        Assert.Equal("3", Display("A = { spread = 3 }\nA.spread"));
    }

    [Fact]
    public void OldNamedSpreadSpelling_IsNotASpreadExpression()
    {
        // `spread(items)` is an ordinary call to whatever `spread` resolves
        // to — no SequenceSpread node is created for it.
        var parse = Parser.Parse("spread(x) = x + 1\nitems = 4\nspread(items)");
        Assert.Empty(parse.Diagnostics);
        Assert.IsType<Expr.Call>(Assert.Single(parse.Root.Output));
    }

    // Both ellipsis orientations are covered by
    // CollectingBindingSyntaxTests.OldEllipsisSpellings_FailThroughOrdinaryParsing,
    // which asserts the same inputs plus the nested pattern form, checks the
    // WHOLE recovered tree through an AstWalker (not just top-level explicit
    // parameters), and pins that no ellipsis-specific diagnostic survives.

    // ── Resource accounting parity ──────────────────────────────────────────

    [Fact]
    public void SpreadMarker_DoesNotAddACallBoundaryOrMultiplicationCharge()
    {
        // The postfix star lowers straight to the one SequenceSpread node
        // without an ordinary call or property boundary, so a spread of a
        // stored value stays a cheap operation: it must succeed under a
        // budget that a genuine multiplication + call pipeline would not fit.
        var result = KatLangEngine.Run(
            "x = (1, 2, 3)\ncount((x*))",
            new RunOptions { EvaluationLimits = new EvaluationLimits { MaxSteps = 200 } });
        Assert.True(result is RunResult.Success, result.ToDisplayString());
        Assert.Equal("3", result.ToDisplayString());
    }
}
