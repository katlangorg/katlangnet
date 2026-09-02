using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorSpreadTests
{
    private static void AssertSpreadMissingOutput(
        string source,
        int expectedStartLine,
        int expectedStartColumn,
        int expectedEndLine,
        int expectedEndColumn)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            $"Cannot spread because the spread operand has no defined output.\nUse `()*` if you intended to spread zero items.",
            formatted);

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;

        var spreadError = Assert.IsType<EvalError.SpreadMissingOutput>(error);
        var span = spreadError.Span;
        Assert.NotNull(span);
        Assert.Equal(expectedStartLine, span!.StartLineNumber);
        Assert.Equal(expectedStartColumn, span.StartColumn);
        Assert.Equal(expectedEndLine, span.EndLineNumber);
        Assert.Equal(expectedEndColumn, span.EndColumn);
    }

    // ── Postfix spread marker ──────────────────────────────────────

    // A. Existing property detection still works

    [Fact]
    public void Eval_PropertyDetection_TwoPrivateProperties()
    {
        AssertEval("A = 5\nB = 10\nA + B", 15);
    }

    [Fact]
    public void Eval_PropertyDetection_PublicAndPrivateProperties()
    {
        AssertEval("public A = 5\nB = 10\nA + B", 15);
    }

    // B. Comma-only outputs still work

    [Fact]
    public void Eval_CommaOnly_MultipleOutputs()
    {
        AssertEval("1 + 2, 2 + 3", 3, 5);
    }

    [Fact]
    public void Eval_SequenceValue_ParensEmitOneSequenceValue()
    {
        AssertEval("(1, 2)", 1, 2);
    }

    [Fact]
    public void Eval_ReportStyleNewlineBodyContributionsAreOutputRows()
    {
        var implicitSource = """
            SalaryExpenses(gross, tax, pension) = gross, tax, pension
            SalaryExpenses(3800, 1, 0)
            ''
            SalaryExpenses(50, 0, 0)
            """;
        var explicitCommaSource = """
            SalaryExpenses(gross, tax, pension) = gross, tax, pension
            SalaryExpenses(3800, 1, 0), '', SalaryExpenses(50, 0, 0)
            """;

        var implicitResult = EvalFull(implicitSource);
        if (implicitResult.IsError)
            Assert.Fail($"Expected implicit newline join success but got error: {implicitResult.Error}");

        var explicitResult = EvalFull(explicitCommaSource);
        if (explicitResult.IsError)
            Assert.Fail($"Expected explicit comma output success but got error: {explicitResult.Error}");

        Assert.True(Result.ValueComparer.Equals(explicitResult.Value, implicitResult.Value));

        var output = Assert.IsType<Result.SequenceValue>(implicitResult.Value);
        Assert.Equal(3, output.Items.Count);
        AssertSequenceValueAtoms(output.Items[0], 3800m, 1m, 0m);
        Assert.Equal("", Assert.IsType<Result.Str>(output.Items[1]).Value);
        AssertSequenceValueAtoms(output.Items[2], 50m, 0m, 0m);
    }

    [Theory]
    [InlineData("1\n2\n3", "1, 2, 3")]
    [InlineData("{\n1\n2\n3\n}", "{\n1, 2, 3\n}")]
    [InlineData("{\n1, 2\n3\n}", "{\n1, 2, 3\n}")]
    public void Eval_NewlineBodyContextsMatchExplicitComma(
        string implicitSource,
        string explicitSource)
    {
        var implicitResult = EvalFull(implicitSource);
        if (implicitResult.IsError)
            Assert.Fail($"Expected implicit newline join success but got error: {implicitResult.Error}");

        var explicitResult = EvalFull(explicitSource);
        if (explicitResult.IsError)
            Assert.Fail($"Expected explicit comma join success but got error: {explicitResult.Error}");

        Assert.True(Result.ValueComparer.Equals(explicitResult.Value, implicitResult.Value));
    }

    [Fact]
    public void Eval_SequenceConstruct_CommaConstructionDiffersByEmittedSlotCount()
    {
        var expected = Result.FromItems([SequenceValue(Atom(1), Atom(2)), Atom(3)]);

        AssertEvalCounted(
            """
            Pair = 1, 2
            (Pair, 3)
            """,
            expectedEmittedCount: 1,
            expected);

        AssertEvalCounted(
            """
            Pair = 1, 2
            Pair, 3
            """,
            expectedEmittedCount: 2,
            expected);
    }

    [Fact]
    public void Eval_SequenceSpreadAfterSequenceConstruct_AppliesToImmediateExpression()
    {
        // The inner `*` binds to `b` only, so both forms supply the ONE
        // sequence-valued argument (1, 2) and the collecting parameter collects [(1, 2)].
        // (Had the spread applied to the whole group — `X((a, b)*)` — the
        // call would supply two arguments and collect [1, 2] instead.)
        var concise = EvalFull(
            """
            X(*values) = values
            a = 1
            b = 2
            X((a, b*))
            """);
        if (concise.IsError)
            Assert.Fail($"Expected concise success but got error: {concise.Error}");

        var sequenceValueResult = EvalFull(
            """
            X(*values) = values
            a = 1
            b = 2
            X((a, (b*)))
            """);
        if (sequenceValueResult.IsError)
            Assert.Fail($"Expected sequence-value success but got error: {sequenceValueResult.Error}");

        Assert.True(Result.ValueComparer.Equals(sequenceValueResult.Value, concise.Value));
        Assert.True(
            Result.ValueComparer.Equals(
                ListValue(SequenceValue(Atom(1), Atom(2))),
                concise.Value),
            $"Expected [(1, 2)] but got {concise.Value}");
    }

    // C. Spread emits immediate results

    [Fact]
    public void Eval_SequenceSpread_TwoFragments()
    {
        AssertEval("1 + 2, (2 + 3)*, 3 + 4", 3, 5, 7);
    }

    [Fact]
    public void Eval_SequenceSpread_MultipleFragments()
    {
        AssertEval("1 + 2, (2 + 3)*, (3 + 4)*, 4 + 5, 5 + 6, 6 + 7", 3, 5, 7, 9, 11, 13);
    }

    [Fact]
    public void Eval_SequenceSpread_LongChain_IsStackSafeForFlatAndCountedEvaluation()
    {
        const int itemCount = 8192;

        // A spread AST over a deep internal sequence-construction chain
        // stays stack-safe and spreads all 8192 items.
        var deepJoin = LongOneJoin(itemCount);
        var spreadJoin = new Expr.SequenceSpread(deepJoin);

        var flatR = Evaluator.RunFlat(spreadJoin);
        if (flatR.IsError)
            Assert.Fail($"Expected success but got error: {flatR.Error}");
        Assert.Equal(Enumerable.Repeat(Decimal128.One, itemCount), flatR.Value);

        var countedRoot = new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Values", new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [deepJoin]))],
            Output:
            [
                BuiltinCall("sum", new Expr.Resolve("Values")),
                BuiltinCall("count", new Expr.Resolve("Values"))
            ]));

        var countedR = Evaluator.RunFlat(countedRoot);
        if (countedR.IsError)
            Assert.Fail($"Expected success but got error: {countedR.Error}");
        Assert.Equal([(decimal)itemCount, (decimal)itemCount], countedR.Value);

        // A deeply nested spread chain stays
        // stack-safe; every level spreads the single item of the innermost
        // operand, so the flat result is the one spread value.
        Expr nested = new Expr.Num(1);
        for (var i = 0; i < itemCount; i++)
            nested = new Expr.SequenceSpread(nested);

        var nestedR = Evaluator.RunFlat(nested);
        if (nestedR.IsError)
            Assert.Fail($"Expected success but got error: {nestedR.Error}");
        Assert.Equal([1m], nestedR.Value);

        static Expr LongOneJoin(int count)
        {
            Expr expr = new Expr.Num(1);
            for (var i = 1; i < count; i++)
                expr = new Expr.SequenceConstruct(expr, new Expr.Num(1));
            return expr;
        }

        static Expr BuiltinCall(string name, Expr arg) =>
            new Expr.Call(new Expr.Resolve(name), [arg]);
    }

    [Fact]
    public void Eval_SequenceSpread_SourceDrivenPostfixChainAtParserLimit_IsStackSafe()
    {
        // Source-driven coverage (not raw AST construction): `1` followed by attached `*`
        // spread markers parses to a deeply-nested unary spread chain
        // `SequenceSpread(SequenceSpread(...(1)))`. Parsing, elaborating, and evaluating it
        // from source stays stack-safe; every level spreads the single item 1, so the flat
        // result is [1].
        //
        // The depth is DERIVED from the parser's own supported ceiling rather than picked:
        // a base primary contributes no expression-chain level and each attached `*`
        // spread marker contributes exactly one, so `Parser.MaxExpressionChainDepth` spreads
        // is the deepest chain the parser accepts. Both sides of that boundary are pinned by
        // ParserExpressionChainDepthTests.SpreadChain_BoundaryIsExactlyMaxExpressionChainDepth.
        //
        // Evaluator stack safety BEYOND the parser ceiling is a separate guarantee and is
        // already covered by Eval_SequenceSpread_LongChain_IsStackSafeForFlatAndCountedEvaluation
        // above, which builds the same nested spread chain directly as an AST at depth 8192.
        const int spreadCount = Parser.MaxExpressionChainDepth;
        var source = "1" + new string('*', spreadCount);

        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors);
        Assert.Empty(parsed.Diagnostics);   // in particular, no "chain is too deep" diagnostic

        // The source really produced the chain under test, one spread level per written `*`.
        var output = Assert.Single(parsed.Root.Output);
        var nesting = 0;
        var operand = output;
        while (operand is Expr.SequenceSpread(var inner))
        {
            nesting++;
            operand = inner;
        }

        Assert.Equal(spreadCount, nesting);
        Assert.IsType<Expr.Num>(operand);

        AssertEval(source, 1m);
    }

    [Fact]
    public void Eval_SequenceSpread_CommaSimilarityForSimpleConstants()
    {
        var source = """
            A = 1, 2
            B = 1*, 2
            A.count
            B.count
            """;

        AssertEval(source, 2, 2);
    }

    [Fact]
    public void Eval_SequenceSpread_GroupsSpreadOneLevel()
    {
        AssertEval("(1, 2)*, 3", 1, 2, 3);
        AssertEval("1*, (2, 3)", 1, 2, 3);
        AssertEval("(1, 2)*, (3, 4)", 1, 2, 3, 4);
    }

    [Fact]
    public void Eval_SequenceSpread_NestedSequenceValuesArePreserved()
    {
        var nestedLeft = EvalFull("((1, 2))*, 3");
        if (nestedLeft.IsError)
            Assert.Fail($"Expected success but got error: {nestedLeft.Error}");

        AssertSequenceValueAtoms(nestedLeft.Value, 1, 2, 3);

        var nestedMiddle = EvalFull("(1, (2, 3))*, 4");
        if (nestedMiddle.IsError)
            Assert.Fail($"Expected success but got error: {nestedMiddle.Error}");

        var middleGroup = Assert.IsType<Result.SequenceValue>(nestedMiddle.Value);
        Assert.Equal(3, middleGroup.Items.Count);
        AssertAtomValue(middleGroup.Items[0], 1);
        AssertSequenceValueAtoms(middleGroup.Items[1], 2, 3);
        AssertAtomValue(middleGroup.Items[2], 4);
    }

    [Fact]
    public void Eval_SequenceSpread_InlineDotCallCountMatchesComma()
    {
        AssertEval("(1*, 2).count", 2);
        AssertEval("(1, 2).count", 2);
    }

    [Fact]
    public void Eval_SequenceConstruct_ErrorOrder_StopsAtEarlierContribution()
    {
        // Sequence-value evaluation evaluates contributions left to right and surfaces the
        // first failure: the unknown-name error from `Math.Nope` is reported
        // before the later `1 / 0` divide-by-zero is ever evaluated. (This is an
        // evaluation ordering test — the source contains no spread expression.)
        var error = GetEvalError(ClosedMemberProbe("", "(1, Math.Nope, 1 / 0)"));
        Assert.NotNull(error);

        var inner = error!;
        while (inner is EvalError.WithContext context)
            inner = context.Inner;

        var unknown = Assert.IsType<EvalError.UnknownName>(inner);
        Assert.Equal("Nope", unknown.Name);
    }

    // D. Spread by reference

    [Fact]
    public void Eval_SequenceSpread_ByReference()
    {
        var source = """
            Property1 = 1
            Property2 = 2, 3
            Property1*, Property2
            """;
        AssertEval(source, 1, 2, 3);
    }

    // E. Sequence-spreading call outputs with additional expressions

    [Fact]
    public void Eval_SequenceSpread_Extension()
    {
        // Simplified version of the motivating pattern:
        // Spread calls with additional expressions.
        var source = """
            Next = if(a > 5, (a - 1, b + 1), (b - 1, a + 1))
            Result = Next(10, 0)*, 10 > 5
            Result
            """;
        AssertEval(source, 9, 1, 1);
    }

    // F. Nested algorithm with spread

    [Fact]
    public void Eval_SequenceSpread_InParenAlgorithm()
    {
        // ((1 + 2)*, 3 + 4) is a parameterless nested algorithm with spread.
        AssertEval("((1 + 2)*, 3 + 4)", 3, 7);
    }

    // G. Capturing algorithm with spread

    [Fact]
    public void Eval_SequenceSpread_InBraceAlgorithm()
    {
        var source = "{ X = 10\n(X + 1)*, X + 2 }";
        AssertEval(source, 11, 12);
    }

    // H. Ordinary parenthesized arithmetic expression unchanged

    [Fact]
    public void Eval_ParenGrouping_ArithmeticUnchanged()
    {
        AssertEval("1 + (2 * 3)", 7);
    }

    // I. Multiline formatting with explicit commas remains irrelevant

    [Fact]
    public void Eval_SequenceSpread_MultilineWithExplicitCommasEquivalentToOneline()
    {
        var multiline = """
            1 + 2, (2 + 3)*,
            (3 + 4)*,
            4 + 5, 5 + 6
            """;
        var oneline = "1 + 2, (2 + 3)*, (3 + 4)*, 4 + 5, 5 + 6";
        var r1 = Eval(multiline);
        var r2 = Eval(oneline);
        Assert.Equal(r1.Value, r2.Value);
    }

    [Fact]
    public void Eval_SequenceSpread_DotCallReceiverBoundaryCanBeSpread()
    {
        var commaSource = """
            A = 1, 2
            F = a, 3
            A.F
            """;

        var commaResult = EvalFull(commaSource);
        if (commaResult.IsError)
            Assert.Fail($"Expected success but got error: {commaResult.Error}");

        var commaGroup = Assert.IsType<Result.SequenceValue>(commaResult.Value);
        Assert.Equal(2, commaGroup.Items.Count);
        AssertSequenceValueAtoms(commaGroup.Items[0], 1, 2);
        AssertAtomValue(commaGroup.Items[1], 3);

        var sequenceSpreadSource = """
            A = 1, 2
            F = a*, 3
            A.F
            """;

        AssertEval(sequenceSpreadSource, 1, 2, 3);
    }

    [Fact]
    public void Eval_SequenceSpread_DoesNotPreserveOrMergeProperties()
    {
        var valueSource = """
            A = {
                X = 1
                10
            }

            B = {
                Y = 2
                20
            }

            C = A*, B
            C
            """;
        AssertEval(valueSource, 10, 20);

        var xSource = """
            A = {
                X = 1
                10
            }

            B = {
                Y = 2
                20
            }

            C = A*, B
            C.X
            """;
        AssertEvalFails(xSource);

        var ySource = """
            A = {
                X = 1
                10
            }

            B = {
                Y = 2
                20
            }

            C = A*, B
            C.Y
            """;
        AssertEvalFails(ySource);
    }

    [Fact]
    public void Eval_SequenceSpread_NoOutputOperandFails()
    {
        // Postfix `Bad*` spreads its (only) operand; a no-output operand
        // fails with the spread missing-output diagnostic, whose span
        // points at the offending operand `Bad` (line 5, columns 1-3), not at the
        // whole spread or some synthetic location.
        var operandSource = """
            Bad = {
                X = 1
            }

            Bad*
            """;
        AssertSpreadMissingOutput(operandSource, 5, 1, 5, 3);

        // A no-output expression in the slot after the spread is an ordinary
        // missing-output failure, not part of the spread: `3*, Bad` is the two
        // expression-list slots `3*` and `Bad`.
        var joinedSource = """
            Bad = {
                X = 1
            }

            3*, Bad
            """;
        AssertEvalFails(joinedSource);
    }

    [Fact]
    public void Eval_SequenceSpread_DirectBlockOperandWithoutOutput_IsSpreadMissingOutput()
    {
        // The spread operand is SYNTACTICALLY a written block (`Expr.AlgorithmExpr`),
        // so evaluation takes the direct block arm of the spread-operand
        // evaluator rather than the generic expression arm. A no-output block
        // operand must report the SAME spread-specific structured error as a
        // resolved-name operand — never raw MissingOutput (T4-2; the Lean
        // `.algorithmExpr` arm translates identically). Root row: span is the block
        // `{A = 1}` (line 1, columns 1-7).
        AssertSpreadMissingOutput("{A = 1}*", 1, 1, 1, 7);

        // The same rule inside a list literal element slot.
        AssertSpreadMissingOutput("[{A = 1}*]", 1, 2, 1, 8);

        // And inside a call-argument slot: the structured kind stays
        // SpreadMissingOutput under the call's context wrapper.
        var callResult = EvalFull("F(a) = a\nF({A = 1}*)");
        Assert.True(callResult.IsError);
        var callError = callResult.Error;
        while (callError is EvalError.WithContext context)
            callError = context.Inner;

        var callSpread = Assert.IsType<EvalError.SpreadMissingOutput>(callError);
        Assert.NotNull(callSpread.Span);
        Assert.Equal(2, callSpread.Span!.StartLineNumber);
        Assert.Equal(3, callSpread.Span.StartColumn);
        Assert.Equal(2, callSpread.Span.EndLineNumber);
        Assert.Equal(9, callSpread.Span.EndColumn);

        // Resolved-name control: reaching the same no-output block through a
        // property keeps the identical structured error, so the direct and
        // resolved spellings agree.
        AssertSpreadMissingOutput("X = {A = 1}\nX*", 2, 1, 2, 1);
    }

    [Fact]
    public void Eval_SequenceSpreadThenMissingAdjacentExpression_FailsOutsideSpread()
    {
        // `3*, Bad` is the two expression-list slots `3*` and `Bad`. The
        // `3*` spread succeeds; `Bad` is a SEPARATE expression-list slot that
        // fails on its own because it has no output. A spread expression has no
        // right operand, so `Bad` never enters the spread and the failure is the
        // ordinary missing-output error, NOT SpreadMissingOutput.
        var source = """
            Bad = {
                X = 1
            }

            3*, Bad
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);

        var inner = error!;
        while (inner is EvalError.WithContext context)
            inner = context.Inner;

        Assert.IsNotType<EvalError.SpreadMissingOutput>(inner);
        Assert.IsType<EvalError.MissingOutput>(inner);
    }

    [Fact]
    public void Eval_Call_SpreadCommaAndNewlineBothSupplySeparateArguments()
    {
        // A spread expression has no right operand:
        // `F(X*, 2)` is TWO argument slots — `X*` spreads X's items (just 1),
        // then `2` — so it binds the two-parameter F to 1 + 2 = 3.
        AssertEval(
            """
            X = 1
            F(a, b) = a + b
            F(X*, 2)
            """,
            3m);

        // A newline inside the open call delimiter also separates slots, so a
        // line-ending spread followed by `2` on the next line is the same TWO
        // argument slots. (`F(X* 2)` would instead be the multiplication X * 2.)
        AssertEval(
            """
            X = 1
            F(a, b) = a + b
            F(X*
            2)
            """,
            3m);
    }

    [Fact]
    public void Eval_SequenceSpread_OfEmptySequenceContributesNoItems()
    {
        AssertEval("1, ()*, 2", 1, 2);
        AssertEval("1, (())*, 2", 1, 2);
        AssertEval("()*, 1", 1);
        AssertEval("1, ()*", 1);
        AssertEvalEmptyOutput("()*");
    }

    // Additional: simple spread of two literals

    [Theory]
    [InlineData("A*, B")]
    [InlineData("A*\nB")]
    public void Eval_SpreadThenJoin_CreatesExpressionListSlots(string tail)
    {
        // A spread expression never consumes a right operand: a comma (or a
        // row-separating newline) after `A*` starts the next expression-list
        // slot, so B stays one separate sequence-valued slot. (An adjacent
        // same-line expression after the star — `A* B` — would instead be the
        // multiplication A * B.)
        var program = "A = 1, 2\nB = 3, 4\n" + tail;
        AssertEvalCounted(program, 3, Result.FromItems([Atom(1), Atom(2), SequenceValue(Atom(3), Atom(4))]));
    }

    [Fact]
    public void Eval_SequenceSpread_SimpleLiterals()
    {
        AssertEval("1*, 2", 1, 2);
        AssertEval("1*, 2*, 3", 1, 2, 3);
    }

    [Fact]
    public void Eval_SequenceSpread_PropertyBody()
    {
        AssertEval("A = 1*, 2\nA", 1, 2);
    }

    [Fact]
    public void Eval_SequenceValue_ParensCreateOneSequenceValue()
    {
        AssertEvalCounted(
            "(1, 2, 3)",
            expectedEmittedCount: 1,
            SequenceValue(Atom(1), Atom(2), Atom(3)));
    }

    [Fact]
    public void Eval_SequenceConstruct_CommaCreatesSiblingOutputSlots()
    {
        AssertEvalCounted(
            "1, 2, 3",
            expectedEmittedCount: 3,
            SequenceValue(Atom(1), Atom(2), Atom(3)));
    }

    [Theory]
    [InlineData("Sum((1, 2, 3))")]
    [InlineData("Seq = (1, 2, 3)\nSum(Seq)")]
    [InlineData("Seq = 1, 2, 3\nSum(Seq)")]
    public void Eval_SingleVariadic_GroupedArgumentIsOneCollectedItem(string call)
        // Each call supplies ONE sequence-valued argument, and the collecting binding
        // collects the supplied slots as the one-element list [(1, 2, 3)] — the
        // old grouped/opened display coincidence is intentionally gone.
        => AssertEval(
            $$"""
            Sum(*values) = values.count
            {{call}}
            """,
            1m);

    [Theory]
    [InlineData("Sum(1, 2, 3)")]
    [InlineData("Sum(1 2 3)")]
    public void Eval_SingleVariadic_InlineCommaOrAdjacencyBindsItemSupply(string call)
        // Inline comma and adjacency both supply three argument slots, bound by the
        // item-supply matcher as one sequence value of count 3 — the same as the
        // grouped form `Sum((1, 2, 3))`.
        => AssertEval(
            $$"""
            Sum(*values) = values.count
            {{call}}
            """,
            3m);

    [Theory]
    [InlineData("Pair = (1, 2)\nAdd(Pair)")]
    [InlineData("Pair = 1, 2\nAdd(Pair)")]
    public void Eval_FixedCalls_DoNotDestructureSequenceArgumentWithoutSpread(string call)
        => AssertEvalFailsWithArityMismatch(
            $$"""
            Add(a, b) = a + b
            {{call}}
            """,
            expected: 2,
            actual: 1);

    [Theory]
    [InlineData("Pair = (1, 2)\nAdd(Pair*)")]
    [InlineData("Pair = 1, 2\nAdd(Pair*)")]
    public void Eval_FixedCalls_ExplicitSpreadDestructuresSequenceArgument(string call)
        => AssertEval(
            $$"""
            Add(a, b) = a + b
            {{call}}
            """,
            3m);

    [Theory]
    [InlineData("F((1, 2, 3), 99)")]
    public void Eval_VariadicWithSuffix_SequenceArgumentStaysOneCollectedItem(string call)
        // F((1, 2, 3), 99) supplies one sequence-valued argument plus the suffix:
        // the collecting parameter collects [(1, 2, 3)] (count 1) and last binds 99. Ordinary
        // calls never implicitly open sequence arguments.
        => AssertEval(
            $$"""
            F(*values, last) = values.count, last
            {{call}}
            """,
            1m,
            99m);

    [Theory]
    [InlineData("F(1, 2, 3, 99)")]
    [InlineData("Seq = (1, 2, 3)\nF(Seq*, 99)")]
    public void Eval_VariadicWithSuffix_DeconstructsInlineCommaOrSpreadSlots(string call)
        // F(*values, last) is a comma deconstruction parameter list: the inline
        // comma slots and the spread both supply four items, so the collecting
        // parameter captures [1, 2, 3] (count 3) and last binds 99.
        => AssertEval(
            $$"""
            F(*values, last) = values.count, last
            {{call}}
            """,
            3m,
            99m);

    [Fact]
    public void Eval_SequenceSpread_OpensOneBoundaryAtOutput()
    {
        AssertEval(
            """
            Seq1 = (1, 2, 3)
            Seq2 = (1, 2, 3)
            Seq1*
            Seq2*
            """,
            1m,
            2m,
            3m,
            1m,
            2m,
            3m);

        AssertEvalResultLoopModes(
            """
            Nested = ((1, 2), 3)
            Nested*
            """,
            Result.FromItems([SequenceValue(Atom(1), Atom(2)), Atom(3)]));
    }

    [Theory]
    [InlineData("Add(Pair)", false)]
    [InlineData("Add(Pair*)", true)]
    public void Eval_SequenceValue_FixedCallSlotSpreadRequiresSpreadMarker(string call, bool succeeds)
    {
        var source = $$"""
            Pair = (1, 2)
            Add(a, b) = a + b
            {{call}}
            """;

        if (succeeds)
            AssertEval(source, 3m);
        else
            AssertEvalFailsWithArityMismatch(source, expected: 2, actual: 1);
    }

    [Theory]
    [InlineData("1\n2\n3")]
    [InlineData("1 2 3")]
    public void Eval_Adjacency_IsImplicitExpressionList(string source)
    {
        AssertEvalCounted(
            source,
            expectedEmittedCount: 3,
            ResultFromAtoms(1, 2, 3));
    }
}
