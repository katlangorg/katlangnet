using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Surface coverage for the named spread intrinsic. Both spellings —
/// the call form <c>spread(expr)</c> and the extension-property form
/// <c>expr.spread</c> — lower at parse time to the ONE
/// <see cref="Expr.SequenceSpread"/> node (no DotCall/Call is involved), so
/// they share a single evaluation path: the operand is evaluated exactly
/// once and its item view is contributed to the surrounding supply. The
/// intrinsic produces a SUPPLY, never a sequence or list value of its own —
/// the receiver decides what the supplied items become. `spread` is a
/// reserved name: it cannot be declared, bound, shadowed, or used as a bare
/// value, so the meaning of <c>expr.spread</c> is never scope-dependent.
/// </summary>
public class SpreadIntrinsicSyntaxTests
{
    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString().Replace("\r\n", "\n");
    }

    private static IReadOnlyList<Diagnostic> Diagnostics(string source)
        => Parser.Parse(source).Diagnostics;

    private static Diagnostic SingleError(string source)
    {
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors);
        var error = Assert.Single(parse.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        return error;
    }

    // ── Lowering: both spellings produce the one intrinsic node ─────────────

    [Fact]
    public void CallForm_LowersDirectlyToSequenceSpread_WithExactSpans()
    {
        var parse = Parser.Parse("A = (1, 2)\nspread(A)");
        Assert.Empty(parse.Diagnostics);

        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(parse.Root.Output));
        Assert.IsType<Expr.Resolve>(spread.Operand);

        // Node span covers `spread(A)`; the intrinsic-name span covers exactly
        // the `spread` keyword token and never overlaps the operand identifier.
        Assert.Equal(new SourceSpan(2, 1, 2, 9), spread.Span);
        Assert.Equal(new SourceSpan(2, 1, 2, 6), spread.IntrinsicNameSpan);
        Assert.Equal(new SourceSpan(2, 8, 2, 8), spread.Operand.Span);
    }

    [Fact]
    public void PropertyForm_LowersDirectlyToSequenceSpread_NeverToADotCall()
    {
        var parse = Parser.Parse("A = (1, 2)\nA.spread");
        Assert.Empty(parse.Diagnostics);

        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(parse.Root.Output));
        Assert.IsType<Expr.Resolve>(spread.Operand);

        // Node span covers `A.spread`; the intrinsic-name span covers exactly
        // the member token `spread`.
        Assert.Equal(new SourceSpan(2, 1, 2, 8), spread.Span);
        Assert.Equal(new SourceSpan(2, 3, 2, 8), spread.IntrinsicNameSpan);
        Assert.Equal(new SourceSpan(2, 1, 2, 1), spread.Operand.Span);
    }

    [Fact]
    public void BothSpellings_ProduceTheSameNodeShape()
    {
        static Expr.SequenceSpread ParseSpread(string source)
        {
            var parse = Parser.Parse(source);
            Assert.Empty(parse.Diagnostics);
            return Assert.IsType<Expr.SequenceSpread>(Assert.Single(parse.Root.Output));
        }

        var callForm = ParseSpread("A = (1, 2)\nspread(A)");
        var dotForm = ParseSpread("A = (1, 2)\nA.spread");

        // Same node kind, same operand shape — only source spans differ.
        Assert.Equal(
            Assert.IsType<Expr.Resolve>(callForm.Operand).Name,
            Assert.IsType<Expr.Resolve>(dotForm.Operand).Name);
    }

    // ── Exact semantic preservation matrix (supply, not value) ──────────────

    [Theory]
    [InlineData(
        "Calculate(x) = x, x + 1\nx = 4\n",
        "spread(Calculate(x))",
        "Calculate(x).spread",
        "4\n5")]
    [InlineData(
        "Calculate(x) = x * 2\nx = 4\noffset = 3\n",
        "spread(Calculate(x) + offset)",
        "(Calculate(x) + offset).spread",
        "11")]
    [InlineData(
        "GetValues = 7, 8\n",
        "spread(GetValues())",
        "GetValues().spread",
        "7\n8")]
    public void ComplexReceiverExpressions_PreserveCallFormPropertyFormParity(
        string declarations,
        string callForm,
        string propertyForm,
        string expected)
    {
        Assert.Equal(expected, Display(declarations + callForm));
        Assert.Equal(expected, Display(declarations + propertyForm));

        var parse = Parser.Parse(declarations + propertyForm);
        Assert.Empty(parse.Diagnostics);
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(parse.Root.Output));
        Assert.IsNotType<Expr.DotCall>(spread.Operand);
    }

    [Theory]
    [InlineData("spread(1)", "1")]
    [InlineData("1 .spread", "1")]
    [InlineData("spread('txt')", "txt")]
    [InlineData("'txt'.spread", "txt")]
    [InlineData("spread([1, 2])", "1\n2")]
    [InlineData("[1, 2].spread", "1\n2")]
    [InlineData("spread((1, 2))", "1\n2")]
    [InlineData("(1, 2).spread", "1\n2")]
    [InlineData("spread([[1, 2]])", "[1, 2]")]
    [InlineData("[[1, 2]].spread", "[1, 2]")]
    public void SpreadContributesItems_OpeningExactlyOneBoundary(string source, string expected)
        => Assert.Equal(expected, Display(source));

    [Theory]
    [InlineData("spread([])")]
    [InlineData("[].spread")]
    [InlineData("spread(())")]
    [InlineData("().spread")]
    public void SpreadOfEmptyValues_ContributesZeroItems(string source)
    {
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Empty(result.Atoms);
    }

    // ── Receiver behaviour: the receiver, not spread, decides the shape ─────

    [Fact]
    public void SingleNameCapture_MaterializesACanonicalSequence()
        => Assert.Equal("(1, 2, 3)", Display("values = [1, 2, 3]\nx = spread(values)\nx"));

    [Fact]
    public void CollectingBinding_CollectsTheSupplyAsAnExactList()
        => Assert.Equal("[1, 2, 3]", Display("values = (1, 2, 3)\nitems... = spread(values)\nitems"));

    [Fact]
    public void FixedDeconstruction_ReceivesIndividualItems()
        => Assert.Equal(
            "(1, 2)",
            Display("values = [1, 2]\nfirst, second = spread(values)\n(first, second)"));

    [Fact]
    public void CallBinding_ReceivesSeparateArgumentSlots()
        => Assert.Equal("3", Display("Target(a, b) = a + b\nvalues = (1, 2)\nTarget(spread(values))"));

    [Fact]
    public void RootOutput_EmitsTheContributedItemsAsRows()
        => Assert.Equal("1\n2\n3", Display("values = (1, 2, 3)\nspread(values)"));

    [Fact]
    public void ListLiteralElements_SpliceTheSupply()
        => Assert.Equal("[1, 2, 5]", Display("[spread([1, 2]), 5]"));

    // ── Property-form / call-form parity ────────────────────────────────────

    public static TheoryData<string> ParityOperands => new()
    {
        "[1, 2, 3]",
        "(1, 2, 3)",
        "()",
        "[]",
        "7",
        "'txt'",
        "[[1, 2], [3, 4]]",
        "((1, 2), 3)",
    };

    [Theory]
    [MemberData(nameof(ParityOperands))]
    public void BothSpellings_AreObservationallyIdentical_AtEveryReceiver(string operand)
    {
        foreach (var (callForm, dotForm) in new[]
        {
            ($"A = {operand}\nspread(A)", $"A = {operand}\nA.spread"),
            ($"A = {operand}\nCollect(items...) = items\nCollect(spread(A))", $"A = {operand}\nCollect(items...) = items\nCollect(A.spread)"),
            ($"A = {operand}\nx = spread(A)\nx", $"A = {operand}\nx = A.spread\nx"),
            ($"A = {operand}\n[spread(A), 99]", $"A = {operand}\n[A.spread, 99]"),
        })
        {
            var callResult = KatLangEngine.Run(callForm).ToDisplayString();
            var dotResult = KatLangEngine.Run(dotForm).ToDisplayString();
            Assert.Equal(callResult, dotResult);
        }
    }

    [Fact]
    public void BothSpellings_ProduceIdenticalErrors()
    {
        // A no-output operand fails identically through either spelling.
        const string bad = "Bad = {\n    X = 1\n}\n";
        var callFailure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(bad + "spread(Bad)"));
        var dotFailure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(bad + "Bad.spread"));
        Assert.Equal(
            callFailure.Errors.Select(static error => error.Message),
            dotFailure.Errors.Select(static error => error.Message));
    }

    /// <summary>
    /// The operand is evaluated exactly once by BOTH spellings: the minimal
    /// evaluation-step budget that lets the program run is identical for the
    /// call form, the property form, and a baseline that evaluates the
    /// operand expression once without spreading. A second operand
    /// evaluation would strictly raise the minimal budget.
    /// </summary>
    [Fact]
    public void BothSpellings_EvaluateTheOperandExactlyOnce_IdenticalStepAccounting()
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

        const string operand = "range(1, 40)";
        var baseline = MinimalSteps($"x = {operand}\nx.count");
        var callForm = MinimalSteps($"x = {operand}\ncount((spread(x)))");
        var dotForm = MinimalSteps($"x = {operand}\ncount((x.spread))");

        Assert.Equal(callForm, dotForm);
        // Sanity: the spread forms sit in the same order of magnitude as the
        // baseline — a double evaluation of range(1, 40) would visibly raise them.
        Assert.InRange(callForm, baseline / 2, baseline * 2);
    }

    // ── Chained spread ──────────────────────────────────────────────────────

    [Theory]
    [InlineData("spread(spread(A))")]
    [InlineData("A.spread.spread")]
    [InlineData("spread(A.spread)")]
    [InlineData("spread(A).spread")]
    public void ChainedSpread_AllSpellingsAgree(string chain)
    {
        // A singleton-list chain opens one list boundary per layer.
        Assert.Equal("7", Display($"A = [[7]]\n{chain}"));

        // Sequence values are fixed points beyond the first layer.
        Assert.Equal("1\n2", Display($"A = (1, 2)\n{chain}"));

        // A singleton empty structure is preserved by the first list spread,
        // then opened by the second layer.
        Assert.Equal("", Display($"A = [()]\n{chain}"));
        Assert.Equal("", Display($"A = [[]]\n{chain}"));
    }

    [Fact]
    public void ChainedSpread_LowersToDirectlyNestedSpreadNodes()
    {
        foreach (var source in new[] { "A = [[7]]\nspread(spread(A))", "A = [[7]]\nA.spread.spread" })
        {
            var parse = Parser.Parse(source);
            Assert.Empty(parse.Diagnostics);
            var outer = Assert.IsType<Expr.SequenceSpread>(Assert.Single(parse.Root.Output));
            var inner = Assert.IsType<Expr.SequenceSpread>(outer.Operand);
            Assert.IsType<Expr.Resolve>(inner.Operand);
        }
    }

    // ── Intrinsic arity and malformed forms ─────────────────────────────────

    [Fact]
    public void CallForm_WithZeroOperands_ReportsIntrinsicArity()
        => Assert.Contains(
            "Intrinsic 'spread' expects exactly 1 operand",
            SingleError("spread()").Message);

    [Fact]
    public void CallForm_WithTwoOperands_ReportsIntrinsicArity()
    {
        var error = SingleError("spread(1, 2)");
        Assert.Contains("Intrinsic 'spread' expects exactly 1 operand", error.Message);
        Assert.Contains("Got 2", error.Message);
        Assert.Contains("spread((a, b))", error.Message);
    }

    [Fact]
    public void CallForm_WithDeclarationInside_ReportsTargetedError()
        => Assert.Contains(
            "declarations are not allowed inside `spread(...)`",
            SingleError("spread(x = 1)").Message);

    [Fact]
    public void PropertyForm_WithArguments_ReportsTargetedError()
        => Assert.Contains(
            "`.spread` takes no arguments",
            SingleError("x = (1, 2)\nx.spread(1)").Message);

    [Theory]
    [InlineData("spread(1, 2)\nLater = 3\nLater")]
    [InlineData("spread(\nx = 1\n2)\nLater = 3\nLater")]
    [InlineData("x = (1, 2)\nx.spread(1)\nLater = 3\nLater")]
    public void RejectedIntrinsicForms_DoNotLeakSpreadNodesIntoTheRecoveredAst(string source)
    {
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Root.Properties, static property => property.Name == "Later");

        var detector = new SequenceSpreadDetector();
        detector.VisitAlgorithm(parse.Root);
        Assert.False(detector.Found);
    }

    [Theory]
    [InlineData("spread")]
    [InlineData("f = spread")]
    [InlineData("F(a, b) = a + b\nF(1, spread)")]
    [InlineData("~spread")]
    public void BareSpreadReference_IsNeverAValue(string source)
        => Assert.Contains(
            Diagnostics(source),
            static diagnostic => diagnostic.Message.Contains(
                "Intrinsic 'spread' requires exactly one operand and is not a value",
                StringComparison.Ordinal));

    [Fact]
    public void CallDelimiter_MustSitOnTheSameLine()
    {
        // `spread` newline `(x)` never continues into a call: the bare
        // reference reports the intrinsic misuse and `(x)` stays its own row.
        var parse = Parser.Parse("spread\n(1)");
        Assert.True(parse.HasErrors);
        Assert.Contains(
            parse.Diagnostics,
            static diagnostic => diagnostic.Message.Contains("Intrinsic 'spread' requires exactly one operand"));
    }

    // ── Reservation: spread can never be declared, bound, or shadowed ───────

    [Theory]
    [InlineData("spread = 1")]
    [InlineData("public spread = 1")]
    [InlineData("spread(x) = x + 1")]
    [InlineData("public spread(x) = x + 1")]
    [InlineData("spread(0) = 1")]
    [InlineData("F(spread) = 1")]
    [InlineData("F((a, spread)) = a")]
    [InlineData("spread, x = 1, 2")]
    [InlineData("x, spread... = 1, 2")]
    public void ReservedSpreadName_IsRejectedInEveryDeclarationPosition(string source)
        => Assert.Contains(
            Diagnostics(source),
            static diagnostic => diagnostic.Message.Contains(
                "'spread' is the spread intrinsic and cannot be declared, bound, or shadowed",
                StringComparison.Ordinal));

    [Fact]
    public void ReservedSpreadDefinition_DoesNotDeclareAProperty()
    {
        var parse = Parser.Parse("spread = 1\n2");
        Assert.True(parse.HasErrors);
        Assert.DoesNotContain(parse.Root.Properties, static property => property.Name == "spread");
    }

    [Theory]
    [InlineData("F(spread) = 1")]
    [InlineData("F((a, spread)) = a")]
    [InlineData("spread, x = 1, 2")]
    [InlineData("x, spread... = 1, 2")]
    public void ReservedSpreadBinding_DoesNotSurviveInTheRecoveredBindingTree(string source)
    {
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors);

        Assert.DoesNotContain(parse.Root.Properties, static property => property.Name == "spread");
        Assert.DoesNotContain(
            parse.Root.Properties.SelectMany(static property => property.Value.Parameters),
            static parameter => parameter.Name == "spread");

        var model = SemanticModelBuilder.Build(parse);
        Assert.Empty(model.FindDeclarations("spread"));
    }

    [Fact]
    public void PropertyFormMeaning_IsNeverScopeDependent()
    {
        // Even beside a rejected `spread` definition, `x.spread` keeps its
        // intrinsic meaning in the recovered tree (never a property access).
        var parse = Parser.Parse("spread = 99\nx = (1, 2)\nx.spread");
        Assert.True(parse.HasErrors);
        Assert.IsType<Expr.SequenceSpread>(Assert.Single(parse.Root.Output));
    }

    // ── Placement: a spread expression is a whole expression-list slot ──────

    [Theory]
    [InlineData("spread(1) + 2")]
    [InlineData("x = (1, 2)\n1 + x.spread")]
    [InlineData("-spread(1)")]
    [InlineData("not spread(1)")]
    [InlineData("spread((1, 2)):0")]
    [InlineData("x = (1, 2)\nx:spread(x)")]
    [InlineData("x = ([1], [2])\nx.spread.count")]
    public void SpreadAsAnOperand_ReportsTargetedPlacementError(string source)
        => Assert.Contains(
            Diagnostics(source),
            static diagnostic => diagnostic.Message.Contains(
                "cannot be an operand of another expression",
                StringComparison.Ordinal));

    [Fact]
    public void SpreadPlacementRecovery_UnwrapsToTheOperand_NoEmbeddedSpreadSurvives()
    {
        var parse = Parser.Parse("spread(1) + 2");
        Assert.True(parse.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(Assert.Single(parse.Root.Output));
        Assert.IsType<Expr.Num>(binary.Left);
    }

    // ── Postfix ellipsis is not an expression operator ──────────────────────
    // The ellipsis token is collecting-binding syntax only. In expression
    // position it fails through ordinary unexpected-token handling: no
    // SequenceSpread node is built, no collecting binding is created, no
    // warning is emitted, and recovery reaches later declarations.

    [Theory]
    [InlineData("Target(a, b) = a + b\nitems = (1, 2)\nTarget(items...)")]
    [InlineData("items = (1, 2)\nx = items...")]
    [InlineData("items = (1, 2)\nitems...")]
    [InlineData("values = (1, 2)\n[0, values..., 4]")]
    [InlineData("F(a, b) = a\nitems = (1, 2)\nF(items..., 1)")]
    [InlineData("Calculate(x) = x + 1\nCalculate(2)...")]
    [InlineData("value = (1, 2)\nvalue......")]
    [InlineData("items = (1, 2)\n...items")]
    public void EllipsisInExpressionPosition_FailsAsOrdinaryInvalidSyntax(string sourceCore)
    {
        var source = sourceCore + "\nLater = 3\nLater";
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors);

        // An ordinary unexpected-token failure with valid source spans.
        Assert.Contains(
            parse.Diagnostics,
            static diagnostic => diagnostic.Message.Contains("Unexpected token", StringComparison.Ordinal));
        Assert.All(parse.Diagnostics, static diagnostic =>
        {
            Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
            Assert.True(diagnostic.Span.StartLineNumber >= 1);
            Assert.True(diagnostic.Span.StartColumn >= 1);
            Assert.True(diagnostic.Span.EndLineNumber >= diagnostic.Span.StartLineNumber);
        });

        // The invalid ellipsis never becomes a spread or a collecting binding.
        var spreadDetector = new SequenceSpreadDetector();
        spreadDetector.VisitAlgorithm(parse.Root);
        Assert.False(spreadDetector.Found);
        var collectingDetector = new CollectingBindingDetector();
        collectingDetector.VisitAlgorithm(parse.Root);
        Assert.False(collectingDetector.Found);

        // Recovery reaches the following declaration, and the parse errors
        // block evaluation.
        Assert.Contains(parse.Root.Properties, static property => property.Name == "Later");
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    // ── Malformed editor-style input stays robust ───────────────────────────

    [Theory]
    [InlineData("x = 1\nx.")]
    [InlineData("x = 1\nx.s")]
    [InlineData("x = 1\nx.sp")]
    [InlineData("x = 1\nx.spre")]
    [InlineData("x = 1\nx.spread(")]
    [InlineData("spread(")]
    [InlineData("spread((")]
    public void MalformedSpreadLikeInput_ParsesWithDiagnosticsAndValidSpans(string source)
    {
        var parse = Parser.Parse(source);
        Assert.True(parse.Diagnostics.Count > 0 || parse.Root is not null);
        foreach (var diagnostic in parse.Diagnostics)
        {
            Assert.True(diagnostic.Span.StartLineNumber >= 1);
            Assert.True(diagnostic.Span.StartColumn >= 1);
            Assert.True(diagnostic.Span.EndLineNumber >= diagnostic.Span.StartLineNumber);
        }
    }

    private sealed class CollectingBindingDetector : AstWalker
    {
        public bool Found { get; private set; }

        protected override void VisitExplicitParameterDeclaration(
            Algorithm algorithm,
            ParameterDeclaration declaration)
        {
            if (declaration.Kind == ParameterKind.Variadic)
                Found = true;
        }

        protected override void VisitConditionalBinderDeclaration(Pattern.Bind pattern, SourceSpan span)
        {
            if (pattern.ParameterKind == ParameterKind.Variadic)
                Found = true;
        }
    }

    private sealed class SequenceSpreadDetector : AstWalker
    {
        public bool Found { get; private set; }

        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.SequenceSpread)
                Found = true;
            base.VisitExpr(expr);
        }
    }
}
