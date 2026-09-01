namespace KatLang.Tests;

public class ParserTests
{
    private const string UnsupportedSemicolonExpressionMessage =
        "Semicolon is not supported as an expression separator";

    private static void AssertUnsupportedSemicolonDiagnostic(SyntaxParseResult result)
    {
        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            diagnostic => diagnostic.Message.Contains(UnsupportedSemicolonExpressionMessage, StringComparison.Ordinal));
    }

    [Fact]
    public void Parse_EmptySource_ReturnsEmptyAlgorithm()
    {
        var result = Parser.ParseSyntax("");

        Assert.False(result.HasErrors);
        Assert.Empty(result.Root.Properties);
        Assert.Empty(result.Root.Output);
    }

    [Fact]
    public void Parse_WhitespaceOnly_ReturnsEmptyAlgorithm()
    {
        var result = Parser.ParseSyntax("   \n\t  ");

        Assert.False(result.HasErrors);
        Assert.Empty(result.Root.Properties);
        Assert.Empty(result.Root.Output);
    }

    [Fact]
    public void Parse_SingleNumber_ReturnsNumExpr()
    {
        var result = Parser.ParseSyntax("42");

        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Output);
        Assert.IsType<Expr.Num>(result.Root.Output[0]);
        Assert.Equal(42, ((Expr.Num)result.Root.Output[0]).Value);
    }

    [Fact]
    public void Parse_NegativeNumber_ReturnsUnaryExpr()
    {
        var result = Parser.ParseSyntax("-5");

        Assert.False(result.HasErrors);
        var unary = Assert.IsType<Expr.Unary>(result.Root.Output[0]);
        Assert.Equal(UnaryOp.Minus, unary.Op);
        Assert.Equal(5, ((Expr.Num)unary.Operand).Value);
    }

    [Fact]
    public void Parse_DoubleNegative_ReturnsNestedUnary()
    {
        var result = Parser.ParseSyntax("--5");

        Assert.False(result.HasErrors);
        var outer = Assert.IsType<Expr.Unary>(result.Root.Output[0]);
        var inner = Assert.IsType<Expr.Unary>(outer.Operand);
        Assert.Equal(5, ((Expr.Num)inner.Operand).Value);
    }

    [Fact]
    public void Parse_Identifier_ReturnsResolveExpr()
    {
        var result = Parser.ParseSyntax("foo");

        Assert.False(result.HasErrors);
        var resolve = Assert.IsType<Expr.Resolve>(result.Root.Output[0]);
        Assert.Equal("foo", resolve.Name);
    }

    [Fact]
    public void Parse_EmptyParens_ParseAsEmptySequenceValue()
    {
        var result = Parser.ParseSyntax("()");

        Assert.False(result.HasErrors);
        var empty = Assert.IsType<Expr.EmptySequence>(Assert.Single(result.Root.Output));
        Assert.Equal(0, empty.Depth);
    }

    [Fact]
    public void Parse_NestedEmptyParens_CanonicalizeToEmptySequence()
    {
        var nested = Parser.ParseSyntax("(())");
        Assert.False(nested.HasErrors);
        var nestedEmpty = Assert.IsType<Expr.EmptySequence>(Assert.Single(nested.Root.Output));
        Assert.Equal(0, nestedEmpty.Depth);

        var deeper = Parser.ParseSyntax("((()))");
        Assert.False(deeper.HasErrors);
        var deeperEmpty = Assert.IsType<Expr.EmptySequence>(Assert.Single(deeper.Root.Output));
        Assert.Equal(0, deeperEmpty.Depth);
    }

    [Fact]
    public void Parse_EmptyBrace_ParsesAsEmptyNoOutputBody()
    {
        var brace = Parser.ParseSyntax("{}");
        Assert.False(brace.HasErrors);
        var braceBlock = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(brace.Root.Output));
        Assert.Empty(braceBlock.Algorithm.Output);
    }

    [Fact]
    public void Parse_Empty_IsOrdinaryIdentifier()
    {
        var resolve = Parser.ParseSyntax("empty");
        Assert.False(resolve.HasErrors);
        Assert.Equal("empty", Assert.IsType<Expr.Resolve>(Assert.Single(resolve.Root.Output)).Name);

        // `empty` is no longer reserved: it can be defined as an ordinary property.
        var property = Parser.ParseSyntax("empty = 1\nempty");
        Assert.False(property.HasErrors);
        Assert.Equal("empty", Assert.Single(property.Root.Properties).Name);

        // `empty` can be used as an ordinary parameter/binder.
        var binder = Parser.ParseSyntax("F(empty) = empty\nF(0)");
        Assert.False(binder.HasErrors);
    }

    [Fact]
    public void Parse_Self_NowParsesAsResolve()
    {
        var result = Parser.ParseSyntax("self");

        Assert.False(result.HasErrors);
        var resolve = Assert.IsType<Expr.Resolve>(result.Root.Output[0]);
        Assert.Equal("self", resolve.Name);
    }

    [Fact]
    public void Parse_Addition_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("1 + 2");

        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Add, binary.Op);
        Assert.Equal(1, ((Expr.Num)binary.Left).Value);
        Assert.Equal(2, ((Expr.Num)binary.Right).Value);
    }

    [Fact]
    public void Parse_Subtraction_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("5 - 3");

        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Sub, binary.Op);
    }

    [Fact]
    public void Parse_Multiplication_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("4 * 3");

        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Mul, binary.Op);
    }

    [Fact]
    public void Parse_LessThan_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("1 < 2");

        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Lt, binary.Op);
    }

    [Fact]
    public void Parse_GreaterThan_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("2 > 1");

        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Gt, binary.Op);
    }

    [Fact]
    public void Parse_OperatorPrecedence_MultiplicationBeforeAddition()
    {
        var result = Parser.ParseSyntax("1 + 2 * 3");

        Assert.False(result.HasErrors);
        var add = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Add, add.Op);
        Assert.Equal(1, ((Expr.Num)add.Left).Value);
        var mul = Assert.IsType<Expr.Binary>(add.Right);
        Assert.Equal(BinaryOp.Mul, mul.Op);
    }

    [Fact]
    public void Parse_OperatorPrecedence_ComparisonAfterArithmetic()
    {
        var result = Parser.ParseSyntax("1 + 2 < 4");

        Assert.False(result.HasErrors);
        var cmp = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Lt, cmp.Op);
        var add = Assert.IsType<Expr.Binary>(cmp.Left);
        Assert.Equal(BinaryOp.Add, add.Op);
    }

    [Fact]
    public void Parse_LeftAssociativity_Addition()
    {
        var result = Parser.ParseSyntax("1 - 2 - 3");

        Assert.False(result.HasErrors);
        var outer = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Sub, outer.Op);
        Assert.Equal(3, ((Expr.Num)outer.Right).Value);
        var inner = Assert.IsType<Expr.Binary>(outer.Left);
        Assert.Equal(BinaryOp.Sub, inner.Op);
    }

    [Fact]
    public void Parse_Parentheses_OverridePrecedence()
    {
        var result = Parser.ParseSyntax("(1 + 2) * 3");

        Assert.False(result.HasErrors);
        var mul = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Mul, mul.Op);
        var add = Assert.IsType<Expr.Binary>(mul.Left);
        Assert.Equal(BinaryOp.Add, add.Op);
    }

    [Fact]
    public void Parse_CommaList_ReturnsMultipleOutputs()
    {
        var result = Parser.ParseSyntax("1, 2, 3");

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
    }

    [Fact]
    public void Parse_Property_ReturnsSingleProperty()
    {
        var result = Parser.ParseSyntax("X = 5");

        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        Assert.Equal("X", result.Root.Properties[0].Name);
        Assert.Single(result.Root.Properties[0].Value.Output);
        Assert.Empty(result.Root.Output);
    }

    [Fact]
    public void Parse_PropertyWithOutput_BothPresent()
    {
        var source = """
            X = 5
            X
            """;
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        Assert.Single(result.Root.Output);
        var resolve = Assert.IsType<Expr.Resolve>(result.Root.Output[0]);
        Assert.Equal("X", resolve.Name);
    }

    [Fact]
    public void Parse_UnaryOutputAfterBraceProperty_StaysAtRootLevel()
    {
        var source = """
            A = {
                X = 1
            }
            -A
            """;

        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("A", property.Name);
        Assert.Empty(property.Value.Output);

        var unary = Assert.IsType<Expr.Unary>(Assert.Single(result.Root.Output));
        Assert.Equal(UnaryOp.Minus, unary.Op);
        var operand = Assert.IsType<Expr.Resolve>(unary.Operand);
        Assert.Equal("A", operand.Name);
    }

    [Fact]
    public void Parse_MultipleProperties_AllParsed()
    {
        var source = """
            A = 1
            B = 2
            C = 3
            """;
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Properties.Count);
        Assert.Equal("A", result.Root.Properties[0].Name);
        Assert.Equal("B", result.Root.Properties[1].Name);
        Assert.Equal("C", result.Root.Properties[2].Name);
        Assert.Empty(result.Root.Output);
    }

    [Fact]
    public void Parse_Index_ReturnsIndexExpr()
    {
        var result = Parser.ParseSyntax("X:0");

        Assert.False(result.HasErrors);
        var index = Assert.IsType<Expr.Index>(result.Root.Output[0]);
        var target = Assert.IsType<Expr.Resolve>(index.Target);
        Assert.Equal("X", target.Name);
        Assert.Equal(0, ((Expr.Num)index.Selector).Value);
    }

    [Fact]
    public void Parse_Index_ListLiteralTarget_ReturnsIndexExpr()
    {
        var result = Parser.ParseSyntax("[1, 2, 3]:1");

        Assert.False(result.HasErrors);
        var index = Assert.IsType<Expr.Index>(Assert.Single(result.Root.Output));
        var target = Assert.IsType<Expr.ListLiteral>(index.Target);
        Assert.Equal(3, target.Items.Count);
        Assert.Equal(1, ((Expr.Num)index.Selector).Value);
    }

    [Fact]
    public void Parse_Index_NestedListLiteralTarget_ChainsLeftAssociatively()
    {
        var result = Parser.ParseSyntax("[[1, 2], [3, 4]]:1:0");

        Assert.False(result.HasErrors);
        var outer = Assert.IsType<Expr.Index>(Assert.Single(result.Root.Output));
        Assert.Equal(0, ((Expr.Num)outer.Selector).Value);
        var inner = Assert.IsType<Expr.Index>(outer.Target);
        Assert.Equal(1, ((Expr.Num)inner.Selector).Value);
        var list = Assert.IsType<Expr.ListLiteral>(inner.Target);
        Assert.Equal(2, list.Items.Count);
        Assert.All(list.Items, static item => Assert.IsType<Expr.ListLiteral>(item));
    }

    [Fact]
    public void Parse_Index_CallTarget_ReturnsIndexOverCall()
    {
        var result = Parser.ParseSyntax("take([1, 2, 3], 2):1");

        Assert.False(result.HasErrors);
        var index = Assert.IsType<Expr.Index>(Assert.Single(result.Root.Output));
        Assert.Equal(1, ((Expr.Num)index.Selector).Value);
        var call = Assert.IsType<Expr.Call>(index.Target);
        var callee = Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("take", callee.Name);
    }

    [Fact]
    public void Parse_Index_DottedBuiltinTarget_ReturnsIndexOverDotCall()
    {
        var result = Parser.ParseSyntax("[3, 1, 2].order:0");

        Assert.False(result.HasErrors);
        var index = Assert.IsType<Expr.Index>(Assert.Single(result.Root.Output));
        Assert.Equal(0, ((Expr.Num)index.Selector).Value);
        var dotCall = Assert.IsType<Expr.DotCall>(index.Target);
        Assert.Equal("order", dotCall.Name);
        var receiver = Assert.IsType<Expr.ListLiteral>(dotCall.Target);
        Assert.Equal(3, receiver.Items.Count);
    }

    [Fact]
    public void Parse_DotAccess_ReturnsDotCallExpr()
    {
        var result = Parser.ParseSyntax("X.count");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("count", dotCall.Name);
        var target = Assert.IsType<Expr.Resolve>(dotCall.Target);
        Assert.Equal("X", target.Name);
    }

    [Fact]
    public void Parse_Call_ReturnsCallExpr()
    {
        var result = Parser.ParseSyntax("F(1, 2)");

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        var func = Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("F", func.Name);
        Assert.Equal(2, call.Args.Count);
    }

    [Fact]
    public void Parse_CallWithBraces_WrapsInBlock()
    {
        // F{x + 1} desugars to F({x + 1}) — the brace content becomes an
        // Expr.AlgorithmExpr argument row in the call's args bundle.
        var result = Parser.ParseSyntax("F{x + 1}");

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.IsType<Expr.AlgorithmExpr>(call.Args[0]);
    }

    [Fact]
    public void Parse_CallWithParens_ProducesArgsBundle()
    {
        var result = Parser.ParseSyntax("F(1)");

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Single(call.Args);
    }

    [Fact]
    public void Parse_DotCall_WithArgs_ReturnsDotCallWithArgs()
    {
        var result = Parser.ParseSyntax("X.Method(1)");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("Method", dotCall.Name);
        Assert.IsType<Expr.Resolve>(dotCall.Target);
        Assert.NotNull(dotCall.Args);
    }

    [Fact]
    public void Parse_DotCall_TrailingBlockWithSpace_AttachesAsDotCallArgs()
    {
        var result = Parser.ParseSyntax("range(0, 5).filter { n > 2 }.count");

        Assert.False(result.HasErrors);
        var countCall = Assert.IsType<Expr.DotCall>(Assert.Single(result.Root.Output));
        Assert.Equal("count", countCall.Name);

        var filterCall = Assert.IsType<Expr.DotCall>(countCall.Target);
        Assert.Equal("filter", filterCall.Name);
        Assert.NotNull(filterCall.Args);
        Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(filterCall.Args!));
    }

    [Fact]
    public void Parse_DotCall_ReceiverIsLeftSide()
    {
        // Lean: A.B = dotCall(resolve("A"), "B", none) — receiver is left of dot
        var result = Parser.ParseSyntax("A.B");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("B", dotCall.Name);
        var target = Assert.IsType<Expr.Resolve>(dotCall.Target);
        Assert.Equal("A", target.Name);
        Assert.Null(dotCall.Args);
    }

    [Fact]
    public void Parse_DotCall_WithArgs_ReceiverIsLeftSide()
    {
        // Lean: A.B(args) = dotCall(resolve("A"), "B", some args)
        var result = Parser.ParseSyntax("A.B(1, 2)");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("B", dotCall.Name);
        var target = Assert.IsType<Expr.Resolve>(dotCall.Target);
        Assert.Equal("A", target.Name);
        Assert.NotNull(dotCall.Args);
        Assert.Equal(2, dotCall.Args!.Count);
    }

    [Fact]
    public void Parse_DotCall_NumericLiteralReceiver()
    {
        // 5.Square → DotCall(Num(5), "Square", null)
        // Lexer: 5 is integer token (dot not consumed as decimal since 'S' is not a digit)
        var result = Parser.ParseSyntax("5.Square");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("Square", dotCall.Name);
        var target = Assert.IsType<Expr.Num>(dotCall.Target);
        Assert.Equal(5, target.Value);
        Assert.Null(dotCall.Args);
    }

    [Fact]
    public void Parse_DotCall_NumericLiteralReceiver_WithArgs()
    {
        // 5.Add(3) → DotCall(Num(5), "Add", args([Num(3)]))
        var result = Parser.ParseSyntax("5.Add(3)");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("Add", dotCall.Name);
        Assert.IsType<Expr.Num>(dotCall.Target);
        Assert.NotNull(dotCall.Args);
        Assert.Single(dotCall.Args!);
    }

    [Fact]
    public void Parse_DotCall_ParenExprReceiver()
    {
        // (2 + 3).Square → DotCall(Binary(Add, Num(2), Num(3)), "Square", null)
        var result = Parser.ParseSyntax("(2 + 3).Square");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("Square", dotCall.Name);
        Assert.IsType<Expr.Binary>(dotCall.Target);
        Assert.Null(dotCall.Args);
    }

    [Fact]
    public void Parse_DotCall_DecimalLiteralReceiver()
    {
        // 5.0.Square → DotCall(Num(5.0), "Square", null)
        // Lexer: 5.0 is decimal token, then dot, then identifier
        var result = Parser.ParseSyntax("5.0.Square");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("Square", dotCall.Name);
        var target = Assert.IsType<Expr.Num>(dotCall.Target);
        Assert.Equal(5.0m, target.Value);
        Assert.Null(dotCall.Args);
    }

    [Fact]
    public void Parse_Block_ReturnsBlockExpr()
    {
        var result = Parser.ParseSyntax("{1}");

        Assert.False(result.HasErrors);
        var block = Assert.IsType<Expr.AlgorithmExpr>(result.Root.Output[0]);
        Assert.IsType<Algorithm.User>(block.Algorithm);
    }

    [Fact]
    public void Parse_GroupingParens_UnwrapsExpression()
    {
        var result = Parser.ParseSyntax("(1)");

        Assert.False(result.HasErrors);
        var num = Assert.IsType<Expr.Num>(result.Root.Output[0]);
        Assert.Equal(1, num.Value);
    }

    [Fact]
    public void Parse_ParenthesizedReference_PreservesBlockLayer()
    {
        var result = Parser.ParseSyntax("(Inner)");

        Assert.False(result.HasErrors);
        var capture = Assert.IsType<Expr.Capture>(result.Root.Output[0]);
        var inner = Assert.IsType<Expr.Resolve>(Assert.Single(capture.Body));
        Assert.Equal("Inner", inner.Name);
    }

    [Fact]
    public void Parse_DoubleParenthesizedReference_PreservesNestedBlockLayer()
    {
        var result = Parser.ParseSyntax("((Inner))");

        Assert.False(result.HasErrors);
        var outer = Assert.IsType<Expr.Capture>(result.Root.Output[0]);
        var inner = Assert.IsType<Expr.Capture>(Assert.Single(outer.Body));
        var reference = Assert.IsType<Expr.Resolve>(Assert.Single(inner.Body));
        Assert.Equal("Inner", reference.Name);
    }

    [Theory]
    [InlineData("A*, B")]
    [InlineData("A*,B")]
    [InlineData("A*\nB")]
    public void Parse_SpreadFollowedByExpression_IsSpreadThenExpressionListSlot(string source)
    {
        // A spread expression never consumes a right operand. A comma (tight
        // or spaced) or a following line starts a new expression-list slot,
        // so every spelling parses as the two slots A*, B. (Same-line
        // adjacency after a star is multiplication, so spreading before
        // another same-line item requires the comma.)
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Theory]
    [InlineData("A*, empty")]
    [InlineData("A*\nempty")]
    public void Parse_SpreadFollowedByEmpty_IsSpreadThenEmptyExpressionListSlot(string source)
    {
        // `A*, empty` is not a binary spread with `empty` as a right operand:
        // a spread expression takes no right operand, so source `empty` is an
        // ordinary expression-list slot and every spelling is A*, empty.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("empty", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Fact]
    public void Parse_PostfixSpreadMarker_IsUnarySpreadWithNoRightOperand()
    {
        var result = Parser.ParseSyntax("A*");

        Assert.False(result.HasErrors);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Fact]
    public void Parse_LineEndingSpreadMarker_SeparatesExpressionListSlots()
    {
        var result = Parser.ParseSyntax(
            """
            A = range(1, 3)

            A*
            A
            """);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Fact]
    public void Parse_LineEndingSpreadMarkerWithExplicitComma_KeepsNextLineSeparate()
    {
        var result = Parser.ParseSyntax(
            """
            A = range(1, 3)

            A*,
            A
            """);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);

        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Fact]
    public void Parse_OrdinaryCompleteExpressionsAcrossNewlines_CreateExpressionListSlots()
    {
        var result = Parser.ParseSyntax(
            """
            A = range(1, 3)

            A
            A
            """);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.All(result.Root.Output, expr => Assert.Equal("A", Assert.IsType<Expr.Resolve>(expr).Name));
    }

    [Fact]
    public void Parse_LegacyPostfixEllipsisRemnant_IsParseError()
    {
        // `...` is not a token: it lexes as three dots, so the legacy postfix
        // ellipsis spelling fails through the ordinary dotted-continuation
        // diagnostics instead of parsing as a spread or collecting binding.
        var result = Parser.ParseSyntax(
            """
            A = range(1, 3)

            A
            A...
            """);

        Assert.True(result.HasErrors);
    }

    [Fact]
    public void Parse_LineEndingSpreadMarkerWithTrailingComment_SeparatesExpressionListSlots()
    {
        var result = Parser.ParseSyntax(
            """
            A = range(1, 3)

            A* # a newline never continues a closed expression
            A
            """);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Theory]
    [InlineData("A = range(1, 3)\n\nA*, A\nA")]
    public void Parse_NewlineAfterSequenceSpread_CreatesExpressionListSlots(string source)
    {
        // At root output a newline separates expression-list slots, and a
        // spread takes no right operand, so comma-separated and newline
        // followers become ordinary slots.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[2]).Name);
    }

    [Fact]
    public void Parse_CallEndingAfterInnerSpreadMarker_DoesNotContinueSequenceSpread()
    {
        var result = Parser.ParseSyntax(
            """
            F(x*)
            y
            """);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args));
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("y", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Fact]
    public void Parse_CallEndingAfterInnerSpreadMarkerWithTrailingComment_DoesNotContinueSequenceSpread()
    {
        var result = Parser.ParseSyntax(
            """
            F(x*) # the physical line ends with ')' before the comment
            y
            """);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args));
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("y", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Fact]
    public void Parse_ParenthesizedSpreadMarker_DoesNotContinueSequenceSpread()
    {
        var result = Parser.ParseSyntax(
            """
            (x*)
            y
            """);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var capture = Assert.IsType<Expr.Capture>(result.Root.Output[0]);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(capture.Body));
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("y", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Fact]
    public void Parse_ParenthesizedSpreadMarkerWithTrailingComment_DoesNotContinueSequenceSpread()
    {
        var result = Parser.ParseSyntax(
            """
            (x*) # the physical line ends with ')' before the comment
            y
            """);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var capture = Assert.IsType<Expr.Capture>(result.Root.Output[0]);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(capture.Body));
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("y", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Fact]
    public void Parse_UnparenthesizedSequenceSpread_RemainsBareSequenceSpread()
    {
        var result = Parser.ParseSyntax("A*");

        Assert.False(result.HasErrors);
        Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
    }

    [Fact]
    public void Parse_ParenthesizedSequenceSpread_ReturnsBlockExpr()
    {
        var result = Parser.ParseSyntax("(A*)");

        Assert.False(result.HasErrors);
        var capture = Assert.IsType<Expr.Capture>(result.Root.Output[0]);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(capture.Body));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Fact]
    public void Parse_DoubleParenthesizedSequenceSpread_PreservesOuterBlockLayer()
    {
        var result = Parser.ParseSyntax("((A*))");

        Assert.False(result.HasErrors);
        var outer = Assert.IsType<Expr.Capture>(result.Root.Output[0]);
        var inner = Assert.IsType<Expr.Capture>(Assert.Single(outer.Body));
        Assert.IsType<Expr.SequenceSpread>(Assert.Single(inner.Body));
    }

    [Fact]
    public void Parse_ScalarParentheses_RemainTransparent()
    {
        var scalar = Parser.ParseSyntax("(3)");
        Assert.False(scalar.HasErrors);
        var num = Assert.IsType<Expr.Num>(scalar.Root.Output[0]);
        Assert.Equal(3, num.Value);

        var arithmetic = Parser.ParseSyntax("((1 + 2))");
        Assert.False(arithmetic.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(arithmetic.Root.Output[0]);
        Assert.Equal(BinaryOp.Add, binary.Op);
    }

    [Fact]
    public void Parse_CommaGroup_BehaviorUnchanged()
    {
        var result = Parser.ParseSyntax("(1, 2)");

        Assert.False(result.HasErrors);
        var capture = Assert.IsType<Expr.Capture>(result.Root.Output[0]);
        Assert.Equal(2, capture.Body.Count);
    }

    [Fact]
    public void Parse_NestedCommaGroup_BehaviorUnchanged()
    {
        var result = Parser.ParseSyntax("((1, 2))");

        Assert.False(result.HasErrors);
        var outer = Assert.IsType<Expr.Capture>(result.Root.Output[0]);
        var inner = Assert.IsType<Expr.Capture>(Assert.Single(outer.Body));
        Assert.Equal(2, inner.Body.Count);
    }

    [Fact]
    public void Parse_SpreadOfBinaryOperands_ChainedSlots()
    {
        // (1 + 2)*, (3 + 4)*, 5 + 6: each spread wraps a whole parenthesized
        // binary operand and the following expression is another
        // expression-list slot.
        var result = Parser.ParseSyntax("(1 + 2)*, (3 + 4)*, 5 + 6");
        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        var first = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.IsType<Expr.Binary>(first.Operand);
        var second = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[1]);
        Assert.IsType<Expr.Binary>(second.Operand);
        Assert.IsType<Expr.Binary>(result.Root.Output[2]); // 5 + 6
    }

    [Fact]
    public void Parse_CommaAndSpreadMarker_CorrectStructure()
    {
        // `2*, 3` is a spread slot followed by another expression-list slot.
        var result = Parser.ParseSyntax("1, 2*, 3");
        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.Equal(1m, Assert.IsType<Expr.Num>(result.Root.Output[0]).Value);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[1]);
        Assert.Equal(2m, Assert.IsType<Expr.Num>(sequenceSpread.Operand).Value);
        Assert.Equal(3m, Assert.IsType<Expr.Num>(result.Root.Output[2]).Value);
    }

    [Fact]
    public void Parse_PropertyDetectionWithSpreadMarker()
    {
        // A = 1*, 2 B = 3 -> two properties; A's body is the expression list (1*, 2).
        var result = Parser.ParseSyntax("A = 1*, 2 B = 3");
        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Properties.Count);
    }

    [Fact]
    public void Parse_Semicolon_ReportsUnsupportedExpressionSeparator()
    {
        var result = Parser.ParseSyntax("1; 2");

        AssertUnsupportedSemicolonDiagnostic(result);
        Assert.Equal(2, result.Root.Output.Count);
    }

    [Fact]
    public void Parse_SemicolonAcrossNewline_ReportsUnsupportedExpressionSeparator()
    {
        var result = Parser.ParseSyntax(
            """
            A ;
            B
            """);

        AssertUnsupportedSemicolonDiagnostic(result);
        Assert.Equal(2, result.Root.Output.Count);
    }

    [Fact]
    public void Parse_CommaWithSequenceValue_PreservesExpressionListStructure()
    {
        var result = Parser.ParseSyntax("1, (2, 3)");

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal(1m, Assert.IsType<Expr.Num>(result.Root.Output[0]).Value);
        var group = Assert.IsType<Expr.Capture>(result.Root.Output[1]);
        Assert.Equal([2m, 3m], group.Body.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Fact]
    public void Parse_NewlineCommaContribution_MaterializesCommaRow()
    {
        var result = Parser.ParseSyntax(
            """
            1, 2
            3
            """);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.Equal([1m, 2m, 3m], result.Root.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Fact]
    public void Parse_NewlineBodyContributions_ReturnExpressionListSlots()
    {
        var result = Parser.ParseSyntax(
            """
            1
            2
            3
            """);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.Equal([1m, 2m, 3m], result.Root.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Fact]
    public void Parse_BraceBodyNewlineContributions_ReturnExpressionListSlots()
    {
        var result = Parser.ParseSyntax(
            """
            {
                1
                2
                3
            }
            """);

        Assert.False(result.HasErrors);
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(result.Root.Output));
        Assert.Equal(3, block.Algorithm.Output.Count);
        Assert.Equal([1m, 2m, 3m], block.Algorithm.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Fact]
    public void Parse_BraceBodyCommaThenNewline_CreatesFlatExpressionList()
    {
        var result = Parser.ParseSyntax(
            """
            {
                1, 2
                3
            }
            """);

        Assert.False(result.HasErrors);
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(result.Root.Output));
        Assert.Equal(3, block.Algorithm.Output.Count);
        Assert.Equal([1m, 2m, 3m], block.Algorithm.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Fact]
    public void Parse_BraceBodyExplicitSemicolonAcrossNewline_ReportsUnsupportedExpressionSeparator()
    {
        var result = Parser.ParseSyntax(
            """
            {
                1 ;
                2
            }
            """);

        AssertUnsupportedSemicolonDiagnostic(result);
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(result.Root.Output));
        Assert.Equal(2, block.Algorithm.Output.Count);
        Assert.Equal([1m, 2m], block.Algorithm.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Fact]
    public void Parse_ArithmeticCommaNewline_CreatesFlatExpressionList()
    {
        var result = Parser.ParseSyntax(
            """
            1 + 2, 2 + 3
            3 + 4
            """);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.All(result.Root.Output, static expr => Assert.IsType<Expr.Binary>(expr));
    }

    [Theory]
    [InlineData("1 2")]
    public void Parse_SameLineAdjacentExpressions_ParseAsExpressionList(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal([1m, 2m], result.Root.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Theory]
    [InlineData("(1, 2)")]
    public void Parse_ParenthesizedComma_ParseAsSequenceValue(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var capture = Assert.IsType<Expr.Capture>(Assert.Single(result.Root.Output));
        Assert.Equal([1m, 2m], capture.Body.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Theory]
    [InlineData("{ 1 2 }")]
    [InlineData("{\n1 2\n}")]
    public void Parse_BraceBodySameLineAdjacency_ParsesAsExpressionList(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(result.Root.Output));
        Assert.Equal(2, block.Algorithm.Output.Count);
        Assert.Equal([1m, 2m], block.Algorithm.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Fact]
    public void Parse_BraceBodySequenceValueComma_ParsesAsSequenceValue()
    {
        var result = Parser.ParseSyntax("{ (1, 2) }");

        Assert.False(result.HasErrors);
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(result.Root.Output));
        var group = Assert.IsType<Expr.Capture>(Assert.Single(block.Algorithm.Output));
        Assert.Equal([1m, 2m], group.Body.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Theory]
    [InlineData("1 2 3")]
    [InlineData("1\n2\n3")]
    public void Parse_AdjacencyNewline_CreateExpressionList(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.Equal([1m, 2m, 3m], result.Root.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Fact]
    public void Parse_ParenthesizedCommaChain_CreatesSequenceValue()
    {
        var result = Parser.ParseSyntax("(1, 2, 3)");

        Assert.False(result.HasErrors);
        var capture = Assert.IsType<Expr.Capture>(Assert.Single(result.Root.Output));
        Assert.Equal([1m, 2m, 3m], capture.Body.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Theory]
    [InlineData("1, 2 3")]
    [InlineData("1, (2, 3)")]
    public void Parse_AdjacencyAfterComma_PreservesExpressionListStructure(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        if (source.Contains("(2, 3)", StringComparison.Ordinal))
        {
            Assert.Equal(2, result.Root.Output.Count);
            Assert.Equal(1m, Assert.IsType<Expr.Num>(result.Root.Output[0]).Value);
            var group = Assert.IsType<Expr.Capture>(result.Root.Output[1]);
            Assert.Equal([2m, 3m], group.Body.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
        }
        else
        {
            Assert.Equal(3, result.Root.Output.Count);
            Assert.Equal([1m, 2m, 3m], result.Root.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
        }
    }

    [Theory]
    [InlineData("A B*")]
    [InlineData("A\nB*")]
    public void Parse_AdjacencyBeforePostfixSequenceSpread_CreatesExpressionListSlots(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[1]);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Theory]
    [InlineData("A B C*")]
    [InlineData("A\nB\nC*")]
    public void Parse_MultipleAdjacencyBeforePostfixSequenceSpread_SpreadsImmediateExpression(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[2]);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Theory]
    [InlineData("A, (B*)")]
    [InlineData("A\n(B*)")]
    public void Parse_ExplicitlySequenceValuePostfixSequenceSpread_AppliesOnlyToSequenceValueOperand(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        var sequenceValueCapture = Assert.IsType<Expr.Capture>(result.Root.Output[1]);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(sequenceValueCapture.Body));
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Theory]
    [InlineData("A, B C*")]
    [InlineData("A, B\nC*")]
    public void Parse_CommaContributionBeforeJoinedPostfixSequenceSpread_PreservesCommaStructure(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[2]);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Theory]
    [InlineData("A B, C*")]
    [InlineData("A\nB, C*")]
    public void Parse_JoinContributionBeforeCommaSlotPostfixSequenceSpread_PreservesCommaStructure(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[2]);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Fact]
    public void Parse_DefinitionSeparatedPostfixSequenceSpreadContribution_PreservesPriorCommaSlot()
    {
        var result = Parser.ParseSyntax("A, B\nP = 1\nC*");

        Assert.False(result.HasErrors);
        Assert.Equal("P", Assert.Single(result.Root.Properties).Name);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[2]);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Fact]
    public void Parse_DefinitionSeparatedCommaSlotSpreadContribution_PreservesPriorSequenceSlot()
    {
        var result = Parser.ParseSyntax("A\nP = 1\nB, C*");

        Assert.False(result.HasErrors);
        Assert.Equal("P", Assert.Single(result.Root.Properties).Name);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[2]);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Fact]
    public void Parse_CommaSlotPostfixSequenceSpreadWithoutJoin_KeepsCommaStructure()
    {
        // Comma slots stay structural and the spread stays local to its own
        // slot — no adjacency pulls `B*` into `A`'s slot.
        var result = Parser.ParseSyntax("A, B*");

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[1]);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Theory]
    [InlineData("A B*, C")]
    [InlineData("A\nB*\nC")]
    public void Parse_MiddlePostfixSequenceSpread_AppliesToImmediateExpressionAndLaterOutputContinues(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[1]);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(result.Root.Output[2]).Name);
    }

    [Theory]
    [InlineData("(A B*)")]
    [InlineData("(A\nB*)")]
    public void Parse_ParenthesizedAdjacencyBeforePostfixSequenceSpread_IsOneSequenceValue(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var capture = Assert.IsType<Expr.Capture>(Assert.Single(result.Root.Output));
        Assert.Equal(2, capture.Body.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(capture.Body[0]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(capture.Body[1]);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Theory]
    [InlineData("F(A B*)")]
    [InlineData("F(A\nB*)")]
    public void Parse_CallArgumentAdjacencyBeforePostfixSequenceSpread_IsExpressionListArguments(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        Assert.Equal(2, call.Args.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(call.Args[0]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(call.Args[1]);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Fact]
    public void Parse_CallArgumentCommaBeforePostfixSequenceSpread_RemainsTwoArguments()
    {
        var result = Parser.ParseSyntax("F(A, B*)");

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        Assert.Equal(2, call.Args.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(call.Args[0]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(call.Args[1]);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Fact]
    public void Parse_CallArgument_SpreadCommaAndStarAdjacency_AreDistinct()
    {
        // A spread slot before another same-line argument requires the comma:
        // `F(X*, Y)` is TWO argument slots — the spread `X*` and `Y`.
        var twoArgs = Parser.ParseSyntax("F(X*, Y)");
        Assert.False(twoArgs.HasErrors);
        var call2 = Assert.IsType<Expr.Call>(Assert.Single(twoArgs.Root.Output));
        Assert.Equal(2, call2.Args.Count);
        Assert.Equal("X", Assert.IsType<Expr.Resolve>(
            Assert.IsType<Expr.SequenceSpread>(call2.Args[0]).Operand).Name);
        Assert.Equal("Y", Assert.IsType<Expr.Resolve>(call2.Args[1]).Name);

        // Without the comma the star is followed by a same-line
        // expression-start token, so it is infix multiplication:
        // `F(X* Y)` is ONE argument `X * Y`, regardless of spacing.
        var oneArg = Parser.ParseSyntax("F(X* Y)");
        Assert.False(oneArg.HasErrors);
        var call1 = Assert.IsType<Expr.Call>(Assert.Single(oneArg.Root.Output));
        var product = Assert.IsType<Expr.Binary>(Assert.Single(call1.Args));
        Assert.Equal(BinaryOp.Mul, product.Op);
        Assert.Equal("X", Assert.IsType<Expr.Resolve>(product.Left).Name);
        Assert.Equal("Y", Assert.IsType<Expr.Resolve>(product.Right).Name);
    }

    [Theory]
    [InlineData("(1 2)")]
    [InlineData("(1\n2)")]
    public void Parse_ParenthesizedAdjacency_IsOneSequenceValue(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var capture = Assert.IsType<Expr.Capture>(Assert.Single(result.Root.Output));
        Assert.Equal(2, capture.Body.Count);
        Assert.Equal([1m, 2m], capture.Body.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Theory]
    [InlineData("F(1 2)")]
    [InlineData("F (1 2)")]
    [InlineData("F((1, 2))")]
    [InlineData("F ((1, 2))")]
    public void Parse_CallArgumentAdjacency_IsExpressionListArguments(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        if (source.Contains("((1, 2))", StringComparison.Ordinal))
        {
            var group = Assert.IsType<Expr.Capture>(Assert.Single(call.Args));
            Assert.Equal([1m, 2m], group.Body.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
        }
        else
        {
            Assert.Equal(2, call.Args.Count);
            Assert.Equal([1m, 2m], call.Args.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
        }
    }

    [Theory]
    [InlineData("F(1, 2)")]
    [InlineData("F (1, 2)")]
    public void Parse_DirectCallWhitespaceBeforeParen_IsCallContinuation(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        Assert.Equal("F", Assert.IsType<Expr.Resolve>(call.Function).Name);
        Assert.Equal(2, call.Args.Count);
    }

    [Theory]
    [InlineData("F{1}")]
    [InlineData("F {1}")]
    public void Parse_DirectCallWhitespaceBeforeBrace_IsCallContinuation(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        Assert.Equal("F", Assert.IsType<Expr.Resolve>(call.Function).Name);
        var argument = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(call.Args));
        Assert.Equal(1, Assert.IsType<Expr.Num>(Assert.Single(argument.Algorithm.Output)).Value);
    }

    [Theory]
    [InlineData("A.B(1)")]
    [InlineData("A.B (1)")]
    public void Parse_DotCallWhitespaceBeforeParen_IsCallContinuation(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(result.Root.Output));
        Assert.Equal("B", dotCall.Name);
        Assert.NotNull(dotCall.Args);
        Assert.Equal(1, Assert.IsType<Expr.Num>(Assert.Single(dotCall.Args!)).Value);
    }

    [Theory]
    [InlineData("A.B{1}")]
    [InlineData("A.B {1}")]
    public void Parse_DotCallWhitespaceBeforeBrace_IsCallContinuation(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(result.Root.Output));
        Assert.Equal("B", dotCall.Name);
        Assert.NotNull(dotCall.Args);
        var argument = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(dotCall.Args!));
        Assert.Equal(1, Assert.IsType<Expr.Num>(Assert.Single(argument.Algorithm.Output)).Value);
    }

    [Fact]
    public void Parse_ExplicitSemicolonBeforeParen_ReportsUnsupportedExpressionSeparator()
    {
        var result = Parser.ParseSyntax("F ; (1)");

        AssertUnsupportedSemicolonDiagnostic(result);
        Assert.Equal(2, result.Root.Output.Count);
    }

    [Fact]
    public void Parse_CommaBeforeParen_RemainsCommaStructureNotCall()
    {
        var result = Parser.ParseSyntax("F, (1)");

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal("F", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        Assert.Equal(1, Assert.IsType<Expr.Num>(result.Root.Output[1]).Value);
    }

    [Fact]
    public void Parse_NewlineBeforeCallDelimiter_IsExpressionListNotCall()
    {
        // A physical newline never continues a closed expression into a
        // call: `Add` newline `(1, 2)` is two expression-list slots.
        // Multiline calls must open the delimiter before the newline.
        var result = Parser.ParseSyntax("Add\n(1, 2)");

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal("Add", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        var group = Assert.IsType<Expr.Capture>(result.Root.Output[1]);
        Assert.Equal(2, group.Body.Count);
    }

    [Fact]
    public void Parse_NewlineBeforeDotCallDelimiter_IsExpressionListNotCall()
    {
        // Same newline boundary for dot calls: `A.B` newline `(1)` is the
        // expression list `A.B, (1)` (the bare dot call then a separate `(1)`
        // slot), never the dot call `A.B(1)`.
        var result = Parser.ParseSyntax("A.B\n(1)");

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("B", dotCall.Name);
        Assert.Null(dotCall.Args);
        Assert.Equal(1, Assert.IsType<Expr.Num>(result.Root.Output[1]).Value);
    }

    [Theory]
    [InlineData("Pair = 1, 2\nP = Pair:0")]
    [InlineData("Pair = 1, 2\nP = Pair :0")]
    [InlineData("Pair = 1, 2\nP = Pair : 0")]
    public void Parse_SameLineIndexing_RemainsPostfixIndex(string source)
    {
        // Same-line whitespace around ':' is insignificant; the index stays
        // a postfix continuation of the expression before it.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = result.Root.Properties[1];
        Assert.Equal("P", property.Name);
        var body = Assert.IsType<Algorithm.User>(property.Value);
        var index = Assert.IsType<Expr.Index>(Assert.Single(body.Output));
        Assert.Equal("Pair", Assert.IsType<Expr.Resolve>(index.Target).Name);
    }

    [Fact]
    public void Parse_ColonLedLineAfterDefinitionBody_IsRejectedNotBodyContinuation()
    {
        // A physical newline never continues a closed expression into
        // postfix indexing, mirroring the call-delimiter rule: `P = Pair`
        // newline `:0` must not silently define `P = Pair:0`. P's body stays
        // the bare resolve and the ':'-led line is rejected with a targeted
        // diagnostic.
        var result = Parser.ParseSyntax("Pair = 1, 2\nP = Pair\n:0\nP");

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            static diagnostic => diagnostic.Message.Contains(
                "Indexing is postfix and must follow the indexed expression on the same physical line",
                StringComparison.Ordinal));
        var property = result.Root.Properties[1];
        Assert.Equal("P", property.Name);
        var body = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal("Pair", Assert.IsType<Expr.Resolve>(Assert.Single(body.Output)).Name);
    }

    [Theory]
    [InlineData("Pair = 1, 2\nPair\n:0")]
    [InlineData("Pair = 1, 2\nPair # comment\n:0")]
    public void Parse_ColonLedLineAfterOutputRow_IsRejectedNotPostfixContinuation(string source)
    {
        // Same boundary in root output: `Pair` newline `:0` is not the index
        // `Pair:0`; the ':'-led row reports the targeted diagnostic. A
        // trailing comment is invisible and must not change that.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            static diagnostic => diagnostic.Message.Contains(
                "Indexing is postfix and must follow the indexed expression on the same physical line",
                StringComparison.Ordinal));
        Assert.DoesNotContain(
            result.Root.Output,
            static expr => expr is Expr.Index);
    }

    [Theory]
    [InlineData("A B")]
    [InlineData("A\nB")]
    public void Parse_AdjacencySpellings_ProduceExpressionListSlots(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Fact]
    public void Parse_ExplicitSemicolon_ReportsUnsupportedExpressionSeparator()
    {
        var result = Parser.ParseSyntax("A ; B");

        AssertUnsupportedSemicolonDiagnostic(result);
        Assert.Equal(2, result.Root.Output.Count);
    }

    [Theory]
    [InlineData("A\n-1")]
    [InlineData("A # comment\n-1")]
    public void Parse_MinusLedLineAfterOutputRow_IsAdjacencyRowNotSubtraction(string source)
    {
        // A binary operator never continues a closed expression across a
        // physical newline, and a trailing comment must not change that:
        // both forms are the expression list `A, -1`, never `A - 1`.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        Assert.IsType<Expr.Unary>(result.Root.Output[1]);
        Assert.DoesNotContain(result.Root.Output, static expr => expr is Expr.Binary);
    }

    [Theory]
    [InlineData("P = A\n-1")]
    [InlineData("P = A # comment\n-1")]
    public void Parse_MinusLedLineAfterDefinitionBody_IsOutputRowNotBodySubtraction(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        var body = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(body.Output)).Name);
        Assert.IsType<Expr.Unary>(Assert.Single(result.Root.Output));
    }

    [Theory]
    [InlineData("F(A\n-1)")]
    [InlineData("F(A # comment\n-1)")]
    public void Parse_MinusLedLineInCallArguments_JoinsAsOneArgument(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        Assert.Equal(2, call.Args.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(call.Args[0]).Name);
        Assert.IsType<Expr.Unary>(call.Args[1]);
    }

    [Theory]
    [InlineData("F\n(1)")]
    [InlineData("F # comment\n(1)")]
    public void Parse_CommentBeforeParenLedLine_DoesNotEnableCallContinuation(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal("F", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        Assert.Equal(1, Assert.IsType<Expr.Num>(result.Root.Output[1]).Value);
    }

    [Fact]
    public void Parse_SameLinePostfixGrace_BindsToPrecedingIdentifier()
    {
        // Same-line '~' after an identifier is postfix grace on that
        // identifier; the adjacent expression joins after it.
        var result = Parser.ParseSyntax("A~B");

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var grace = Assert.IsType<Expr.Grace>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(grace.Inner).Name);
        Assert.Equal(1, grace.Weight);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Theory]
    [InlineData("A\n~B")]
    [InlineData("A # comment\n~B")]
    public void Parse_TildeLedLine_IsPrefixGraceRowNotPostfixContinuation(string source)
    {
        // A physical newline never continues a closed expression into
        // postfix grace: the '~'-led line is its own prefix-grace row, and a
        // trailing comment must not change that.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        var grace = Assert.IsType<Expr.Grace>(result.Root.Output[1]);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(grace.Inner).Name);
        Assert.Equal(-1, grace.Weight);
    }

    [Theory]
    [InlineData("A*, B\nC")]
    [InlineData("A*, B\nP = 9\nC")]
    public void Parse_PostfixSpreadThenLaterOutput_SequencesAfterSpread(string source)
    {
        // A spread takes no right operand, so later output never lands "inside" a
        // spread. A newline at root and a definition-separated contribution
        // keep the spread value and later output as expression-list slots.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        var spread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(spread.Operand).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(result.Root.Output[2]).Name);
    }

    [Theory]
    [InlineData("A*\nC")]
    [InlineData("A*\nP = 9\nC")]
    public void Parse_PostfixSpreadLaterOutput_ContinuesAfterSpread(string source)
    {
        // Postfix `A*` lets later output continue after the spread in every
        // spelling: a newline at root and definition-separated rows both
        // produce expression-list slots after the spread.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var spread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(spread.Operand).Name);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Theory]
    [InlineData("A*, empty\nC")]
    [InlineData("A*, empty\nP = 9\nC")]
    public void Parse_PostfixSpreadThenEmptyThenLaterOutput_SequencesAfterSpread(string source)
    {
        // A spread takes no right operand, so a comma-separated `empty` is an
        // ordinary expression-list contribution.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        var spread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(spread.Operand).Name);
        Assert.Equal("empty", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(result.Root.Output[2]).Name);
    }

    [Theory]
    [InlineData("P\n= 1\nP")]
    [InlineData("P # comment\n= 1\nP")]
    public void Parse_CommentBeforeEqualsLine_StillParsesPropertyDefinition(string source)
    {
        // Declaration lookahead skips comments: a trailing comment before
        // the '='-led line must not turn the definition into an output row.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        Assert.Equal("P", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Output)).Name);
    }

    [Theory]
    [InlineData("public P\n= 1\nP")]
    [InlineData("public P # comment\n= 1\nP")]
    public void Parse_CommentInPublicPropertyHeader_StillParsesPublicDefinition(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        Assert.True(property.IsPublic);
    }

    [Theory]
    [InlineData("Output\n= 1")]
    [InlineData("Output # comment\n= 1")]
    public void Parse_CommentInOutputNamedPropertyHeader_StillParsesPropertyDefinition(string source)
    {
        // `Output` is an ordinary identifier, so the cross-line definition
        // header parses exactly like any other property named `Output`.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("Output", property.Name);
        Assert.Empty(result.Root.Output);
    }

    [Theory]
    [InlineData("F(x) = x\nF(4)")]
    [InlineData("F # comment\n(x) # comment\n= x\nF(4)")]
    public void Parse_CommentedClauseHeader_ParsesIdentically(string source)
    {
        // Clause-header lookahead scans through the shared significant-token
        // API, so comments between the header tokens never change what
        // parses as a clause definition.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("F", property.Name);
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        Assert.Equal("F", Assert.IsType<Expr.Resolve>(call.Function).Name);
    }

    [Theory]
    [InlineData("public F(x) = x\nF(4)")]
    [InlineData("public F # comment\n(x) # comment\n= x\nF(4)")]
    public void Parse_CommentedPublicClauseHeader_ParsesIdentically(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("F", property.Name);
        Assert.True(property.IsPublic);
    }

    [Theory]
    [InlineData("A = { public X = 1 }\npublic open A")]
    [InlineData("A = { public X = 1 }\npublic # comment\nopen A")]
    public void Parse_CommentedPublicOpen_ReportsSameDiagnostic(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("'public' cannot be applied to open declarations"));
    }

    [Fact]
    public void Parse_Spread_SpanCoversExactlyTheSpreadExpression()
    {
        // `A*, B` parses as the two expression-list slots `A*` and `B`. The
        // SequenceSpread node must span exactly `A*` (operand start through
        // the star, columns 1-2) — NOT `A*, B`. The comma-separated `B` is a
        // separate expression-list slot, not part of the spread. This
        // behavioral span check replaces the old source-text regex that
        // counted construction sites (the unary node has no parser-local
        // metadata to protect; the real invariant is the exact source span).
        var result = Parser.ParseSyntax("A*, B");

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        var spread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal(new SourceSpan(1, 1, 1, 2), spread.Span);
        Assert.Equal(new SourceSpan(1, 2, 1, 2), spread.SpreadMarkerSpan);

        // The following `B` is the next expression-list slot, positioned after `A*, `.
        var b = Assert.IsType<Expr.Resolve>(result.Root.Output[1]);
        Assert.Equal("B", b.Name);
        Assert.Equal(5, b.Span!.StartColumn);

        // Chained spread nests one node per written star; each layer's span
        // grows to its own star and each spread-marker span is exactly that star.
        var chained = Parser.ParseSyntax("A**");

        Assert.False(chained.HasErrors);
        var outer = Assert.IsType<Expr.SequenceSpread>(Assert.Single(chained.Root.Output));
        Assert.Equal(new SourceSpan(1, 1, 1, 3), outer.Span);
        Assert.Equal(new SourceSpan(1, 3, 1, 3), outer.SpreadMarkerSpan);
        var inner = Assert.IsType<Expr.SequenceSpread>(outer.Operand);
        Assert.Equal(new SourceSpan(1, 1, 1, 2), inner.Span);
        Assert.Equal(new SourceSpan(1, 2, 1, 2), inner.SpreadMarkerSpan);
    }

    [Fact]
    public void ParserSource_OpenTargetListParsing_DoesNotUseOutputPrecedenceParsing()
    {
        // Architecture regression: `open` has a dedicated comma-list parser.
        // The open-target parsing region must never invoke the generic
        // expression-LIST machinery (implicit adjacency separators, semicolon
        // recovery, spread slots) — open atoms are single plain expressions
        // parsed by ParseExpression, with spread-marked targets rejected by
        // open-form validation. ParseExpressionListOperand is that machinery's
        // one entry point (the historical ParseOutputLineExprs wrapper over it
        // is gone), so its name appearing in the open region would mean the
        // dedicated comma-list model regressed into output-precedence parsing.
        var source = ReadParserSource();
        var start = source.IndexOf("private List<Expr> ParseOpenTargetList", StringComparison.Ordinal);
        var end = source.IndexOf("private static Expr CreateLoadOpenTarget", StringComparison.Ordinal);
        Assert.True(
            start >= 0 && end > start,
            "Expected the ParseOpenTargetList .. CreateLoadOpenTarget region in Parser.cs.");

        var openRegion = source[start..end];
        Assert.Contains("return ParseExpression();", openRegion, StringComparison.Ordinal);
        Assert.DoesNotContain("ParseExpressionListOperand", openRegion, StringComparison.Ordinal);
        Assert.DoesNotContain("StartsImplicitExpressionListSeparator", openRegion, StringComparison.Ordinal);
    }

    private static string ReadParserSource()
    {
        string? parserPath = null;
        for (var current = new System.IO.DirectoryInfo(System.AppContext.BaseDirectory);
            current is not null;
            current = current.Parent)
        {
            var candidate = System.IO.Path.Combine(current.FullName, "src", "KatLang", "Parser.cs");
            if (System.IO.File.Exists(candidate))
            {
                parserPath = candidate;
                break;
            }
        }

        Assert.NotNull(parserPath);
        return System.IO.File.ReadAllText(parserPath!);
    }

    [Theory]
    [InlineData("~P\n= 1\nP")]
    [InlineData("~P # comment\n= 1\nP")]
    public void Parse_CommentInGracePrefixedDefinition_ReportsSameGraceDiagnostic(string source)
    {
        // The invalid-grace property diagnostic fires identically with or
        // without a comment in the declaration header.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Grace operator cannot be applied to property names"));
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
    }

    [Theory]
    [InlineData("(A\n-1)")]
    [InlineData("(A # comment\n-1)")]
    public void Parse_MinusLedLineInGroup_JoinsAsSequenceValueRows(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var group = Assert.IsType<Expr.Capture>(Assert.Single(result.Root.Output));
        Assert.Equal(2, group.Body.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(group.Body[0]).Name);
        Assert.IsType<Expr.Unary>(group.Body[1]);
    }

    [Theory]
    [InlineData("A\n...")]
    [InlineData("A # comment\n...")]
    public void Parse_LegacyEllipsisLedLine_IsRejectedIdentically(string source)
    {
        // `...` is not a token: it lexes as three dots, and a leading '.' is
        // the whitelisted cross-line continuation, so a '...'-led line fails
        // through the ordinary dotted-continuation diagnostics — with or
        // without a trailing comment above it.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Expected property name after '.'."));
    }

    [Theory]
    [InlineData("A\n*")]
    [InlineData("A # comment\n*")]
    public void Parse_StarLedLine_IsCollectMarkerInExpressionError(string source)
    {
        // A star never crosses lines: the previous row is complete, so a
        // '*'-led line is a prefix collect marker in expression position —
        // rejected with the targeted diagnostic, with or without a trailing
        // comment above it.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains(
                "Prefix `*` is the collect marker and is valid only in binding patterns"));
    }

    [Theory]
    [InlineData("A B C*")]
    [InlineData("A\nB\nC*")]
    public void Parse_TrailingPostfixSpreadAfterJoinChain_SpreadsImmediateExpression(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
        var spread = Assert.IsType<Expr.SequenceSpread>(result.Root.Output[2]);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(spread.Operand).Name);
    }

    [Theory]
    [InlineData("F\n{1}")]
    [InlineData("A.B\n{1}")]
    public void Parse_NewlineBeforeBraceDelimiter_IsExpressionListNotBraceCall(string source)
    {
        // The newline boundary applies to brace delimiters too: a '{'-led
        // line is its own block row, never callback arguments for the
        // callable expression on the previous line.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.True(result.Root.Output[0] is Expr.Resolve or Expr.DotCall);
        if (result.Root.Output[0] is Expr.DotCall dotCall)
            Assert.Null(dotCall.Args);
        var block = Assert.IsType<Expr.AlgorithmExpr>(result.Root.Output[1]);
        Assert.Equal(1, Assert.IsType<Expr.Num>(Assert.Single(block.Algorithm.Output)).Value);
    }

    [Theory]
    [InlineData("Add ; (1, 2)")]
    [InlineData("Add ;\n(1, 2)")]
    public void Parse_ExplicitSemicolonBeforeCallDelimiter_ReportsUnsupportedExpressionSeparator(string source)
    {
        var result = Parser.ParseSyntax(source);

        AssertUnsupportedSemicolonDiagnostic(result);
        Assert.Equal(2, result.Root.Output.Count);
    }

    [Fact]
    public void Parse_ParenLedLineAfterDefinitionBody_IsOutputRowNotBodyCall()
    {
        // The newline call boundary applies inside definition bodies too: a
        // '('-led line after a body that ends in a callable expression is a
        // following output row, never call arguments appended to that body.
        var result = Parser.ParseSyntax("P = F\n(1, 2)");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        var body = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal("F", Assert.IsType<Expr.Resolve>(Assert.Single(body.Output)).Name);
        var row = Assert.IsType<Expr.Capture>(Assert.Single(result.Root.Output));
        Assert.Equal(2, row.Body.Count);
    }

    [Fact]
    public void Parse_ParenLedLineAfterDefinitionBody_DoesNotCreateSelfRecursiveCall()
    {
        // Regression: `A = Identity` newline `(A)` once parsed as
        // `A = Identity(A)`, making A recursively depend on itself and
        // blowing up property evaluation. The newline ends the body, so A's
        // body stays the bare resolve `Identity` and `(A)` is a report row.
        var result = Parser.ParseSyntax("Identity = x\n\nA = Identity\n(A)\n\nA");

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Properties.Count);
        var property = result.Root.Properties[1];
        Assert.Equal("A", property.Name);
        var body = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal("Identity", Assert.IsType<Expr.Resolve>(Assert.Single(body.Output)).Name);
        Assert.Equal(2, result.Root.Output.Count);
        var row = Assert.IsType<Expr.Capture>(result.Root.Output[0]);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(row.Body)).Name);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Fact]
    public void Parse_SameLineCallDelimiterInDefinitionBody_RemainsCall()
    {
        // Control: with the delimiter on the same physical line, the body is
        // the call. Newline is the only boundary; same-line whitespace
        // continues the call.
        var result = Parser.ParseSyntax("Identity = x\nA = Identity (A)");

        Assert.False(result.HasErrors);
        var property = result.Root.Properties[1];
        Assert.Equal("A", property.Name);
        var body = Assert.IsType<Algorithm.User>(property.Value);
        var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
        Assert.Equal("Identity", Assert.IsType<Expr.Resolve>(call.Function).Name);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(call.Args)).Name);
    }

    [Theory]
    [InlineData("Identity = x\nA = Identity(A)")]
    [InlineData("Identity = x\nA = Identity(\n  A\n)")]
    public void Parse_OpenedCallDelimiterSpansLines_RemainsCall(string source)
    {
        // An already-open argument list spans physical lines normally: only
        // the delimiter itself must be opened before the newline.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = result.Root.Properties[1];
        Assert.Equal("A", property.Name);
        var body = Assert.IsType<Algorithm.User>(property.Value);
        var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
        Assert.Equal("Identity", Assert.IsType<Expr.Resolve>(call.Function).Name);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(call.Args)).Name);
    }

    [Theory]
    [InlineData("1\n2, 3")]
    [InlineData("(1, 2), 3")]
    public void Parse_NewlineAdjacencyAndSequenceValueComma_ProduceExpectedExpressionListShape(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        if (source.StartsWith('('))
        {
            Assert.Equal(2, result.Root.Output.Count);
            var group = Assert.IsType<Expr.Capture>(result.Root.Output[0]);
            Assert.Equal([1m, 2m], group.Body.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
            Assert.Equal(3m, Assert.IsType<Expr.Num>(result.Root.Output[1]).Value);
        }
        else
        {
            Assert.Equal(3, result.Root.Output.Count);
            Assert.Equal([1m, 2m, 3m], result.Root.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
        }
    }

    [Fact]
    public void Parse_CallArgumentAdjacency_BecomesTwoArguments()
    {
        var adjacency = Parser.ParseSyntax("F(1 2)");
        var commaSeparated = Parser.ParseSyntax("F(1, 2)");

        Assert.False(adjacency.HasErrors);
        Assert.False(commaSeparated.HasErrors);
        var adjacencyCall = Assert.IsType<Expr.Call>(Assert.Single(adjacency.Root.Output));
        Assert.Equal(2, adjacencyCall.Args.Count);
        var commaCall = Assert.IsType<Expr.Call>(Assert.Single(commaSeparated.Root.Output));
        Assert.Equal(2, commaCall.Args.Count);
        Assert.DoesNotContain(commaCall.Args, static expr => expr is Expr.SequenceConstruct);
    }

    [Theory]
    [InlineData("F(1, 2 3)")]
    [InlineData("F(1, (2, 3))")]
    public void Parse_CallArgumentMixedCommaAndAdjacency_UsesExpressionListStructure(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        if (source.Contains("(2, 3)", StringComparison.Ordinal))
        {
            Assert.Equal(2, call.Args.Count);
            Assert.Equal(1m, Assert.IsType<Expr.Num>(call.Args[0]).Value);
            var group = Assert.IsType<Expr.Capture>(call.Args[1]);
            Assert.Equal([2m, 3m], group.Body.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
        }
        else
        {
            Assert.Equal(3, call.Args.Count);
            Assert.Equal([1m, 2m, 3m], call.Args.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
        }
    }

    [Fact]
    public void Parse_IfArityUsesSyntacticArguments_AdjacencySatisfiesArity()
    {
        var threeArguments = Parser.ParseSyntax("if(1, 2, 3)");
        Assert.False(threeArguments.HasErrors);

        var adjacencyArguments = Parser.ParseSyntax("if(1, 2 3)");
        Assert.False(adjacencyArguments.HasErrors);
    }

    [Theory]
    [InlineData("P = 1 2", "P")]
    [InlineData("P = (1, 2)", "P")]
    public void Parse_PropertyBodySameLineAdjacency_UsesExpressionListOrSequenceValue(string source, string propertyName)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal(propertyName, property.Name);
        var body = Assert.IsType<Algorithm.User>(property.Value);
        if (source.Contains('('))
        {
            var group = Assert.IsType<Expr.Capture>(Assert.Single(body.Output));
            Assert.Equal([1m, 2m], group.Body.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
        }
        else
        {
            Assert.Equal(2, body.Output.Count);
            Assert.Equal([1m, 2m], body.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
        }
    }

    [Fact]
    public void Parse_ClauseBodySameLineAdjacency_JoinsIntoBody()
    {
        var result = Parser.ParseSyntax("F(x) = x y");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("F", property.Name);
        var body = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal(2, body.Output.Count);
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(body.Output[0]).Name);
        Assert.Equal("y", Assert.IsType<Expr.Resolve>(body.Output[1]).Name);
    }

    [Fact]
    public void Parse_AdjacencyDoesNotConsumePropertyDefinitionOnSameLine()
    {
        var result = Parser.ParseSyntax("1 P = 3");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        var output = Assert.Single(result.Root.Output);
        Assert.Equal(1, Assert.IsType<Expr.Num>(output).Value);
    }

    [Fact]
    public void Parse_PublicPropertyDefinitionAfterOutputLine_KeepsDeclarationBoundary()
    {
        var result = Parser.ParseSyntax("1\npublic P = 2");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        Assert.True(property.IsPublic);
        var output = Assert.Single(result.Root.Output);
        Assert.Equal(1, Assert.IsType<Expr.Num>(output).Value);
    }

    [Fact]
    public void Parse_OutputNamedPropertyAfterPropertyBody_KeepsDeclarationBoundary()
    {
        // A definition header named `Output` on a later line is an ordinary
        // property definition, never a continuation of the previous body.
        var result = Parser.ParseSyntax("P = 1\nOutput = 2");

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Properties.Count);
        Assert.Equal("P", result.Root.Properties[0].Name);
        Assert.Equal("Output", result.Root.Properties[1].Name);
        Assert.Empty(result.Root.Output);
    }

    [Fact]
    public void Parse_ClauseDefinitionAfterOutputLine_KeepsDeclarationBoundary()
    {
        var result = Parser.ParseSyntax("1\nF(x) = x + 1");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("F", property.Name);
        var output = Assert.Single(result.Root.Output);
        Assert.Equal(1, Assert.IsType<Expr.Num>(output).Value);
    }

    [Fact]
    public void Parse_OpenAfterOutputLine_KeepsDeclarationBoundaryAndPlacementDiagnostic()
    {
        // 'open' on a later line is still an open declaration, never an
        // adjacent expression; its placement rule still applies.
        var result = Parser.ParseSyntax("1\nopen A");

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("'open' declaration must appear before"));
        Assert.Single(result.Root.Opens);
    }

    [Theory]
    [InlineData("(F) (1)")]
    [InlineData("(F)\n(1)")]
    [InlineData("(1 + 2)(3)")]
    [InlineData("(1 + 2) (3)")]
    [InlineData("(1 + 2)\n(3)")]
    public void Parse_SequenceValueArbitraryExpressionBeforeParen_IsAdjacencyNotCall(string source)
    {
        // Sequence values and arithmetic results are not callable targets, so
        // a following '(' joins as adjacency and never becomes a call.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.DoesNotContain(result.Root.Output, static expr => expr is Expr.Call);
    }

    [Fact]
    public void Parse_LeadingSemicolonOnNextLineAfterDefinitionBody_ReportsUnsupportedExpressionSeparator()
    {
        var result = Parser.ParseSyntax("P = F\n; (1)");

        AssertUnsupportedSemicolonDiagnostic(result);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        var body = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal(2, body.Output.Count);
        Assert.Equal("F", Assert.IsType<Expr.Resolve>(body.Output[0]).Name);
        Assert.Equal(1m, Assert.IsType<Expr.Num>(body.Output[1]).Value);
    }

    [Theory]
    [InlineData("2(3)")]
    [InlineData("2 (3)")]
    [InlineData("2\n(3)")]
    public void Parse_NumberBeforeParenthesizedExpression_IsAdjacencyNotMultiplicationOrCall(string source)
    {
        // Numbers are not callable targets, so the relaxed call-whitespace
        // rule does not apply; the parenthesized expression joins as
        // adjacency and never becomes multiplication or a call.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal(2, Assert.IsType<Expr.Num>(result.Root.Output[0]).Value);
        Assert.Equal(3, Assert.IsType<Expr.Num>(result.Root.Output[1]).Value);
    }

    [Fact]
    public void Parse_AdjacencyDoesNotSplitIdentifiersOrNumbers()
    {
        var identifier = Parser.ParseSyntax("ab");
        var resolve = Assert.IsType<Expr.Resolve>(Assert.Single(identifier.Root.Output));
        Assert.Equal("ab", resolve.Name);

        var number = Parser.ParseSyntax("12");
        Assert.False(number.HasErrors);
        var num = Assert.IsType<Expr.Num>(Assert.Single(number.Root.Output));
        Assert.Equal(12, num.Value);
    }

    [Fact]
    public void Parse_BinaryOperatorContinuation_IsNotAdjacency()
    {
        var result = Parser.ParseSyntax("1 - 2");

        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(Assert.Single(result.Root.Output));
        Assert.Equal(BinaryOp.Sub, binary.Op);
    }

    [Fact]
    public void Parse_SequenceSpreadAfterSemicolon_ReportsUnsupportedExpressionSeparator()
    {
        var result = Parser.ParseSyntax("X(a ; b*)");

        AssertUnsupportedSemicolonDiagnostic(result);
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        Assert.Equal(2, call.Args.Count);
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(call.Args[0]).Name);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(call.Args[1]);
        Assert.Equal("b", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
    }

    [Theory]
    [InlineData("A* ; B")]
    [InlineData("X(a* ; b)")]
    public void Parse_SemicolonAfterPostfixSpread_ReportsUnsupportedSemicolon(string source)
    {
        // `;` is invalid expression syntax even immediately after a spread
        // expression (`;` is not an expression-start token, so the attached
        // star stays a spread). The diagnostic fires and recovery keeps the
        // spread value as a postfix Expr.SequenceSpread slot; this is never a
        // binary/right-operand spread or a valid sequence expression.
        var result = Parser.ParseSyntax(source);

        AssertUnsupportedSemicolonDiagnostic(result);

        IReadOnlyList<Expr> slots = source.StartsWith("X", StringComparison.Ordinal)
            ? Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output)).Args
            : result.Root.Output;
        Assert.Equal(2, slots.Count);
        Assert.IsType<Expr.SequenceSpread>(slots[0]);
    }

    [Fact]
    public void Parse_SequenceSpreadWithCommaInCall_KeepsCommaStructural()
    {
        var result = Parser.ParseSyntax("X(a*, b)");

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        Assert.Equal(2, call.Args.Count);
        var sequenceSpread = Assert.IsType<Expr.SequenceSpread>(call.Args[0]);
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(sequenceSpread.Operand).Name);
        Assert.Equal("b", Assert.IsType<Expr.Resolve>(call.Args[1]).Name);
    }

    [Fact]
    public void Parse_NewlineInsideExplicitSequenceValue_CreatesExpressionList()
    {
        var result = Parser.ParseSyntax(
            """
            (A
            B)
            """);

        Assert.False(result.HasErrors);
        var capture = Assert.IsType<Expr.Capture>(Assert.Single(result.Root.Output));
        Assert.Equal(2, capture.Body.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(capture.Body[0]).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(capture.Body[1]).Name);
    }

    [Fact]
    public void Parse_NewlineInsideCallArgs_CreatesArgumentSlots()
    {
        var result = Parser.ParseSyntax(
            """
            F(
                A
                B
            )
            """);

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        Assert.Equal(2, call.Args.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(call.Args[0]).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(call.Args[1]).Name);
    }

    [Fact]
    public void Parse_ArithmeticGroupingUnchanged()
    {
        // 1 + (2 * 3) → Binary with parentheses
        var result = Parser.ParseSyntax("1 + (2 * 3)");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Add, binary.Op);
    }

    [Fact]
    public void Parse_ChainedIndex_LeftAssociative()
    {
        var result = Parser.ParseSyntax("X:0:1");

        Assert.False(result.HasErrors);
        var outer = Assert.IsType<Expr.Index>(result.Root.Output[0]);
        var inner = Assert.IsType<Expr.Index>(outer.Target);
        Assert.IsType<Expr.Resolve>(inner.Target);
    }

    [Fact]
    public void Parse_ChainedDotCall_LeftAssociative()
    {
        var result = Parser.ParseSyntax("X.A.B");

        Assert.False(result.HasErrors);
        var outer = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("B", outer.Name);
        var inner = Assert.IsType<Expr.DotCall>(outer.Target);
        Assert.Equal("A", inner.Name);
    }

    [Fact]
    public void Parse_BinaryMinusWithNegative_ParsesCorrectly()
    {
        var result = Parser.ParseSyntax("5 - -3");

        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Sub, binary.Op);
        var unary = Assert.IsType<Expr.Unary>(binary.Right);
        Assert.Equal(UnaryOp.Minus, unary.Op);
    }

    [Fact]
    public void Parse_Comment_IsIgnored()
    {
        // Comments are semantically invisible: a same-line comment changes
        // nothing, and a trailing operator continues its expression onto the
        // next line with or without a comment in between.
        foreach (var source in new[] { "1 + 2 # comment", "1 +\n2", "1 + # comment\n2" })
        {
            var result = Parser.ParseSyntax(source);

            Assert.False(result.HasErrors);
            var binary = Assert.IsType<Expr.Binary>(Assert.Single(result.Root.Output));
            Assert.Equal(BinaryOp.Add, binary.Op);
        }
    }

    [Theory]
    [InlineData("1\n+ 2")]
    [InlineData("1 # comment\n+ 2")]
    public void Parse_CommentDoesNotEnableBinaryContinuationAcrossNewline(string source)
    {
        // A binary operator never continues a closed expression across a
        // physical newline, and a skipped comment must not relax that
        // boundary: both spellings reject the '+'-led line identically.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Unexpected token"));
    }

    [Fact]
    public void Parse_DotCall_InlineParenMultiOutputReceiver_IsBlock()
    {
        var result = Parser.ParseSyntax("(1, 2, 3).order");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        var target = Assert.IsType<Expr.Capture>(dotCall.Target);
        Assert.Equal(3, target.Body.Count);
        Assert.Null(dotCall.Args);
    }

    [Fact]
    public void Parse_DotCall_DoubleParenSequenceValueReceiver_PreservesOuterBlockLayer()
    {
        var result = Parser.ParseSyntax("((1, 2, 3)).count");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        var outer = Assert.IsType<Expr.Capture>(dotCall.Target);
        Assert.Single(outer.Body);

        var inner = Assert.IsType<Expr.Capture>(outer.Body[0]);
        Assert.Equal(3, inner.Body.Count);
        Assert.Null(dotCall.Args);
    }

    [Fact]
    public void Parse_DotCall_ParenWrappedBraceReceiver_RemainsScopingOnly()
    {
        var result = Parser.ParseSyntax("({1, 2, 3}).order");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        var target = Assert.IsType<Expr.AlgorithmExpr>(dotCall.Target);
        Assert.Equal(3, target.Algorithm.Output.Count);
        Assert.Null(dotCall.Args);
    }

    [Fact]
    public void Parse_DotCall_InlineBraceReceiver_IsBlock()
    {
        var result = Parser.ParseSyntax("{1, 2, 3}.order");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        var target = Assert.IsType<Expr.AlgorithmExpr>(dotCall.Target);
        Assert.Equal(3, target.Algorithm.Output.Count);
        Assert.Null(dotCall.Args);
    }

    [Fact]
    public void Parse_PropertyBody_SequenceValueTuple_PreservedAsSingleValue()
    {
        var result = Parser.ParseSyntax("Pair = (1, 2)");

        Assert.False(result.HasErrors);
        var pair = result.Root.Properties[0].Value;
        Assert.Single(pair.Output);
        var capture = Assert.IsType<Expr.Capture>(pair.Output[0]);
        Assert.Equal(2, capture.Body.Count);
    }

    [Fact]
    public void Parse_UnexpectedToken_ReportsError()
    {
        var result = Parser.ParseSyntax("1 + + 2");
        Assert.True(result.HasErrors);
    }

    [Fact]
    public void Parse_MissingCloseParen_ReportsError()
    {
        var result = Parser.ParseSyntax("(1 + 2");
        Assert.True(result.HasErrors);
    }

    // â"€â"€ New operators â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

    [Fact]
    public void Parse_Division_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("10 / 3");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Div, binary.Op);
    }

    [Fact]
    public void Parse_IntegerDivision_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("10 div 3");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.IDiv, binary.Op);
    }

    [Fact]
    public void Parse_Modulo_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("10 mod 3");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Mod, binary.Op);
    }

    [Fact]
    public void Parse_Power_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("2 ^ 3");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Pow, binary.Op);
    }

    [Fact]
    public void Parse_Power_RightAssociative()
    {
        var result = Parser.ParseSyntax("2 ^ 3 ^ 4");
        Assert.False(result.HasErrors);
        var outer = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Pow, outer.Op);
        Assert.Equal(2, ((Expr.Num)outer.Left).Value);
        var inner = Assert.IsType<Expr.Binary>(outer.Right);
        Assert.Equal(BinaryOp.Pow, inner.Op);
        Assert.Equal(3, ((Expr.Num)inner.Left).Value);
        Assert.Equal(4, ((Expr.Num)inner.Right).Value);
    }

    // ── Power vs prefix-unary precedence ────────────────────────────────────
    // `^` binds tighter than the prefix unary operators on the LEFT (the
    // base), while the exponent re-enters the unary level: `-2 ^ 2` is
    // `-(2 ^ 2)`, `2 ^ -2` stays valid, and `^` stays right-associative.

    private static Expr ParseSingleOutput(string source)
    {
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));
        return Assert.Single(result.Root.Output);
    }

    private static Expr.Binary AssertPow(Expr expr)
    {
        var binary = Assert.IsType<Expr.Binary>(expr);
        Assert.Equal(BinaryOp.Pow, binary.Op);
        return binary;
    }

    private static Expr AssertUnary(Expr expr, UnaryOp op)
    {
        var unary = Assert.IsType<Expr.Unary>(expr);
        Assert.Equal(op, unary.Op);
        return unary.Operand;
    }

    private static void AssertNum(Expr expr, decimal expected)
        => Assert.Equal(expected, Assert.IsType<Expr.Num>(expr).Value);

    [Fact]
    public void Parse_PowerWithUnaryMinusBase_NegatesTheWholePower()
    {
        // -2 ^ 2 = Unary(Minus, Binary(Pow, 2, 2))
        var pow = AssertPow(AssertUnary(ParseSingleOutput("-2 ^ 2"), UnaryOp.Minus));
        AssertNum(pow.Left, 2);
        AssertNum(pow.Right, 2);
    }

    [Fact]
    public void Parse_PowerWithParenthesizedNegativeBase_KeepsUnaryBase()
    {
        // (-2) ^ 2 = Binary(Pow, Unary(Minus, 2), 2) — a lone parenthesized
        // expression unwraps at parse time, so the unary lands in base position.
        var pow = AssertPow(ParseSingleOutput("(-2) ^ 2"));
        AssertNum(AssertUnary(pow.Left, UnaryOp.Minus), 2);
        AssertNum(pow.Right, 2);
    }

    [Fact]
    public void Parse_PowerWithUnaryMinusExponent_StaysValid()
    {
        // 2 ^ -2 = Binary(Pow, 2, Unary(Minus, 2))
        var pow = AssertPow(ParseSingleOutput("2 ^ -2"));
        AssertNum(pow.Left, 2);
        AssertNum(AssertUnary(pow.Right, UnaryOp.Minus), 2);
    }

    [Fact]
    public void Parse_PowerWithUnaryBaseAndUnaryExponent_NegatesThePowerOverTheUnaryExponent()
    {
        // -2 ^ -2 = Unary(Minus, Binary(Pow, 2, Unary(Minus, 2)))
        var pow = AssertPow(AssertUnary(ParseSingleOutput("-2 ^ -2"), UnaryOp.Minus));
        AssertNum(pow.Left, 2);
        AssertNum(AssertUnary(pow.Right, UnaryOp.Minus), 2);
    }

    [Fact]
    public void Parse_PowerChain_RemainsRightAssociative()
    {
        // 2 ^ 3 ^ 2 = Binary(Pow, 2, Binary(Pow, 3, 2))
        var outer = AssertPow(ParseSingleOutput("2 ^ 3 ^ 2"));
        AssertNum(outer.Left, 2);
        var inner = AssertPow(outer.Right);
        AssertNum(inner.Left, 3);
        AssertNum(inner.Right, 2);
    }

    [Fact]
    public void Parse_UnaryMinusOverPowerChain_NegatesTheWholeRightAssociativeChain()
    {
        // -2 ^ 3 ^ 2 = Unary(Minus, Binary(Pow, 2, Binary(Pow, 3, 2)))
        var outer = AssertPow(AssertUnary(ParseSingleOutput("-2 ^ 3 ^ 2"), UnaryOp.Minus));
        AssertNum(outer.Left, 2);
        var inner = AssertPow(outer.Right);
        AssertNum(inner.Left, 3);
        AssertNum(inner.Right, 2);
    }

    [Fact]
    public void Parse_UnaryMinusExponent_AppliesToTheWholeRightAssociativeTail()
    {
        // 2 ^ -2 ^ 2 = Binary(Pow, 2, Unary(Minus, Binary(Pow, 2, 2)))
        var outer = AssertPow(ParseSingleOutput("2 ^ -2 ^ 2"));
        AssertNum(outer.Left, 2);
        var inner = AssertPow(AssertUnary(outer.Right, UnaryOp.Minus));
        AssertNum(inner.Left, 2);
        AssertNum(inner.Right, 2);
    }

    [Fact]
    public void Parse_NotOverPower_NegatesTheWholePower()
    {
        // not 0 ^ 0 = Unary(Not, Binary(Pow, 0, 0))
        var pow = AssertPow(AssertUnary(ParseSingleOutput("not 0 ^ 0"), UnaryOp.Not));
        AssertNum(pow.Left, 0);
        AssertNum(pow.Right, 0);
    }

    [Fact]
    public void Parse_NotExponent_StaysValid()
    {
        // 2 ^ not 0 = Binary(Pow, 2, Unary(Not, 0))
        var pow = AssertPow(ParseSingleOutput("2 ^ not 0"));
        AssertNum(pow.Left, 2);
        AssertNum(AssertUnary(pow.Right, UnaryOp.Not), 0);
    }

    [Fact]
    public void Parse_NotVersusComparisonAndLogical_Unchanged()
    {
        // The unary tier's relationship with comparisons and logical operators
        // is NOT changed by the power-precedence rule: `not 1 == 2` stays
        // `(not 1) == 2`, and `not a and b` stays `(not a) and b`.
        var eq = Assert.IsType<Expr.Binary>(ParseSingleOutput("not 1 == 2"));
        Assert.Equal(BinaryOp.Eq, eq.Op);
        AssertNum(AssertUnary(eq.Left, UnaryOp.Not), 1);
        AssertNum(eq.Right, 2);

        var and = Assert.IsType<Expr.Binary>(ParseSingleOutput("not 1 and 0"));
        Assert.Equal(BinaryOp.And, and.Op);
        AssertNum(AssertUnary(and.Left, UnaryOp.Not), 1);
        AssertNum(and.Right, 0);
    }

    [Fact]
    public void Parse_UnaryPowerInsideAdditiveAndMultiplicative_KeepsUnaryAboveThoseTiers()
    {
        // 1 + -2 ^ 2 = Binary(Add, 1, Unary(Minus, Binary(Pow, 2, 2)))
        var add = Assert.IsType<Expr.Binary>(ParseSingleOutput("1 + -2 ^ 2"));
        Assert.Equal(BinaryOp.Add, add.Op);
        AssertNum(add.Left, 1);
        var addPow = AssertPow(AssertUnary(add.Right, UnaryOp.Minus));
        AssertNum(addPow.Left, 2);
        AssertNum(addPow.Right, 2);

        // 2 * -3 ^ 2 = Binary(Mul, 2, Unary(Minus, Binary(Pow, 3, 2)))
        var mul = Assert.IsType<Expr.Binary>(ParseSingleOutput("2 * -3 ^ 2"));
        Assert.Equal(BinaryOp.Mul, mul.Op);
        AssertNum(mul.Left, 2);
        var mulPow = AssertPow(AssertUnary(mul.Right, UnaryOp.Minus));
        AssertNum(mulPow.Left, 3);
        AssertNum(mulPow.Right, 2);
    }

    [Fact]
    public void Parse_PowerBaseIsPostfixLevel_CallsIndexingAndGroupsBindFirst()
    {
        // Postfix forms complete before `^` takes the base: `A:0 ^ 2` is
        // `(A:0) ^ 2`, and a parenthesized group is the base it wraps.
        var indexed = AssertPow(ParseSingleOutput("A = 4, 9\nA:0 ^ 2"));
        Assert.IsType<Expr.Index>(indexed.Left);
        AssertNum(indexed.Right, 2);

        var grouped = AssertPow(ParseSingleOutput("(1 + 2) ^ 2"));
        var sum = Assert.IsType<Expr.Binary>(grouped.Left);
        Assert.Equal(BinaryOp.Add, sum.Op);
        AssertNum(grouped.Right, 2);
    }

    [Fact]
    public void Parse_ScientificNotationExponentSign_IsLexerLevelAndUnaffected()
    {
        // `1e-2` is one numeric literal — the sign inside scientific notation
        // never involves the unary/power grammar.
        AssertNum(ParseSingleOutput("1e-2"), 0.01m);

        // And a literal in power position composes normally: 1e-2 ^ 2 is
        // Binary(Pow, 0.01, 2), with no unary node anywhere.
        var pow = AssertPow(ParseSingleOutput("1e-2 ^ 2"));
        AssertNum(pow.Left, 0.01m);
        AssertNum(pow.Right, 2);
    }

    [Fact]
    public void Parse_TrailingCaret_ContinuesAcrossNewline_LeadingCaretDoesNot()
    {
        // A trailing `^` continues to its right operand on the following line.
        var pow = AssertPow(ParseSingleOutput("2 ^\n3"));
        AssertNum(pow.Left, 2);
        AssertNum(pow.Right, 3);

        // A trailing `^` with a unary right operand on the next line.
        var unaryPow = AssertPow(ParseSingleOutput("2 ^\n-3"));
        AssertNum(AssertUnary(unaryPow.Right, UnaryOp.Minus), 3);

        // A `^`-led line never continues the closed expression on the
        // previous line — the first row stays `2` and the dangling `^` row
        // is a parse error.
        var broken = Parser.ParseSyntax("2\n^ 3");
        Assert.True(broken.HasErrors);
    }

    [Fact]
    public void Parse_LessEqual_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("1 <= 2");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Le, binary.Op);
    }

    [Fact]
    public void Parse_GreaterEqual_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("2 >= 1");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Ge, binary.Op);
    }

    [Fact]
    public void Parse_EqualEqual_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("1 == 1");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Eq, binary.Op);
    }

    [Fact]
    public void Parse_NotEqual_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("1 != 2");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Ne, binary.Op);
    }

    [Fact]
    public void Parse_And_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("1 and 0");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.And, binary.Op);
    }

    [Fact]
    public void Parse_Or_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("1 or 0");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Or, binary.Op);
    }

    [Fact]
    public void Parse_Xor_ReturnsBinaryExpr()
    {
        var result = Parser.ParseSyntax("1 xor 0");
        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Xor, binary.Op);
    }

    [Fact]
    public void Parse_Not_ReturnsUnaryExpr()
    {
        var result = Parser.ParseSyntax("not 1");
        Assert.False(result.HasErrors);
        var unary = Assert.IsType<Expr.Unary>(result.Root.Output[0]);
        Assert.Equal(UnaryOp.Not, unary.Op);
    }

    [Fact]
    public void Parse_Precedence_PowerBeforeMultiplication()
    {
        // 2 * 3 ^ 4 = 2 * (3 ^ 4)
        var result = Parser.ParseSyntax("2 * 3 ^ 4");
        Assert.False(result.HasErrors);
        var mul = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Mul, mul.Op);
        var pow = Assert.IsType<Expr.Binary>(mul.Right);
        Assert.Equal(BinaryOp.Pow, pow.Op);
    }

    [Fact]
    public void Parse_Precedence_DivModSameAsMul()
    {
        // 12 / 3 mod 2 = (12 / 3) mod 2
        var result = Parser.ParseSyntax("12 / 3 mod 2");
        Assert.False(result.HasErrors);
        var mod = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Mod, mod.Op);
        var div = Assert.IsType<Expr.Binary>(mod.Left);
        Assert.Equal(BinaryOp.Div, div.Op);
    }

    [Fact]
    public void Parse_Precedence_ComparisonBeforeLogical()
    {
        // 1 < 2 and 3 > 1 = (1 < 2) and (3 > 1)
        var result = Parser.ParseSyntax("1 < 2 and 3 > 1");
        Assert.False(result.HasErrors);
        var andExpr = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.And, andExpr.Op);
        var lt = Assert.IsType<Expr.Binary>(andExpr.Left);
        Assert.Equal(BinaryOp.Lt, lt.Op);
        var gt = Assert.IsType<Expr.Binary>(andExpr.Right);
        Assert.Equal(BinaryOp.Gt, gt.Op);
    }

    [Fact]
    public void Parse_Precedence_AndBeforeOr()
    {
        // 1 or 2 and 3 = 1 or (2 and 3)
        var result = Parser.ParseSyntax("1 or 2 and 3");
        Assert.False(result.HasErrors);
        var orExpr = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Or, orExpr.Op);
        Assert.Equal(1, ((Expr.Num)orExpr.Left).Value);
        var andExpr = Assert.IsType<Expr.Binary>(orExpr.Right);
        Assert.Equal(BinaryOp.And, andExpr.Op);
    }

    [Fact]
    public void Parse_Precedence_EqualityBeforeComparison()
    {
        // Note: equality (==) at prec 4, comparison (<) at prec 5
        // So 1 == 2 < 3 = 1 == (2 < 3)
        var result = Parser.ParseSyntax("1 == 2 < 3");
        Assert.False(result.HasErrors);
        var eq = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Eq, eq.Op);
        var lt = Assert.IsType<Expr.Binary>(eq.Right);
        Assert.Equal(BinaryOp.Lt, lt.Op);
    }

    [Fact]
    public void Parse_CommentMarkerDoesNotConflictWithSlash()
    {
        // # is comment, / is division — a trailing comment after a division
        // leaves the division untouched.
        var result = Parser.ParseSyntax("10 / 2 # this is a comment");
        Assert.False(result.HasErrors);
        var div = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Div, div.Op);
    }

    [Theory]
    [InlineData("// old comment")]
    [InlineData("value = 6 // old comment")]
    public void Parse_DoubleSlash_IsNoLongerACommentMarker(string source)
    {
        // The former `//` comment syntax is removed: each '/' lexes as the
        // ordinary division token, so the second '/' has no operand and the
        // former comment text is parsed as KatLang instead of being skipped.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.DoesNotContain(Lexer.Tokenize(source).Tokens, t => t.Kind == TokenKind.Comment);
    }

    [Fact]
    public void Parse_PropertyAssignmentNotConfusedWithEqualEqual()
    {
        // X = 5 should be property, not X == 5
        var result = Parser.ParseSyntax("X = 5\nX");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        Assert.Equal("X", result.Root.Properties[0].Name);
    }

    // â"€â"€ Grace operator tests â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

    [Fact]
    public void Parse_PrefixGrace_ProducesGraceNode()
    {
        var result = Parser.ParseSyntax("~x + 1");

        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        var grace = Assert.IsType<Expr.Grace>(binary.Left);
        Assert.Equal(-1, grace.Weight);
        var resolve = Assert.IsType<Expr.Resolve>(grace.Inner);
        Assert.Equal("x", resolve.Name);
    }

    [Fact]
    public void Parse_PostfixGrace_ProducesGraceNode()
    {
        var result = Parser.ParseSyntax("x~ + 1");

        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        var grace = Assert.IsType<Expr.Grace>(binary.Left);
        Assert.Equal(1, grace.Weight);
        var resolve = Assert.IsType<Expr.Resolve>(grace.Inner);
        Assert.Equal("x", resolve.Name);
    }

    [Fact]
    public void Parse_PostfixGrace_CanBeDirectCallee()
    {
        var result = Parser.ParseSyntax("predicate~(x)");

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        var grace = Assert.IsType<Expr.Grace>(call.Function);
        Assert.Equal(1, grace.Weight);
        var resolve = Assert.IsType<Expr.Resolve>(grace.Inner);
        Assert.Equal("predicate", resolve.Name);
        var arg = Assert.IsType<Expr.Resolve>(call.Args[0]);
        Assert.Equal("x", arg.Name);
    }

    [Fact]
    public void Parse_DoublePrefixGrace_WeightMinusTwo()
    {
        var result = Parser.ParseSyntax("~~x");

        Assert.False(result.HasErrors);
        var grace = Assert.IsType<Expr.Grace>(result.Root.Output[0]);
        Assert.Equal(-2, grace.Weight);
    }

    [Fact]
    public void Parse_DoublePostfixGrace_WeightPlusTwo()
    {
        var result = Parser.ParseSyntax("x~~");

        Assert.False(result.HasErrors);
        var grace = Assert.IsType<Expr.Grace>(result.Root.Output[0]);
        Assert.Equal(2, grace.Weight);
    }

    [Fact]
    public void Parse_PrefixAndPostfixCancel_NoGraceNode()
    {
        // ~x~ has weight -1 + 1 = 0, so no Grace wrapper
        var result = Parser.ParseSyntax("~x~");

        Assert.False(result.HasErrors);
        var resolve = Assert.IsType<Expr.Resolve>(result.Root.Output[0]);
        Assert.Equal("x", resolve.Name);
    }

    [Fact]
    public void Parse_GraceOnNonIdentifier_ReportsError()
    {
        var result = Parser.ParseSyntax("~42");

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace `~` can only be applied to a parameter or name occurrence"));
    }

    [Fact]
    public void Parse_GraceOnPropertyName_ReportsError()
    {
        var result = Parser.ParseSyntax("~X = 5\nX");

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace operator cannot be applied to property names"));
    }

    // â"€â"€ Public property parsing â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€â"€

    [Fact]
    public void Parse_PublicProperty_SetsIsPublic()
    {
        var result = Parser.ParseSyntax("public X = 5\nX");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        Assert.Equal("X", result.Root.Properties[0].Name);
        Assert.True(result.Root.Properties[0].IsPublic);
    }

    [Fact]
    public void Parse_PrivateProperty_DefaultIsNotPublic()
    {
        var result = Parser.ParseSyntax("X = 5\nX");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        Assert.False(result.Root.Properties[0].IsPublic);
    }

    [Fact]
    public void Parse_MixedVisibility_BothParsed()
    {
        var result = Parser.ParseSyntax("public A = 1\nB = 2\nA + B");
        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Properties.Count);
        Assert.True(result.Root.Properties[0].IsPublic);
        Assert.False(result.Root.Properties[1].IsPublic);
    }

    [Fact]
    public void Parse_PublicOpen_ReportsError()
    {
        var result = Parser.ParseSyntax("public open Math\nPi");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("'public' cannot be applied to open"));
    }

    [Fact]
    public void Parse_GraceOnPublicProperty_ReportsError()
    {
        var result = Parser.ParseSyntax("~public X = 5\nX");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace operator cannot be applied to property names"));
    }

    // -- Open declaration tests -----------------------------------------------

    [Fact]
    public void Parse_Open_UnbracketedCommaList_TwoOpens()
    {
        // open Lib2, Lib3 -> two open entries
        var result = Parser.ParseSyntax("open Lib2, Lib3\nLib2 = { public Val2 = 20 }\nLib3 = { public Val3 = 30 }\nVal3");
        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Opens.Count);
        Assert.IsType<Expr.Resolve>(result.Root.Opens[0]);
        Assert.Equal("Lib2", ((Expr.Resolve)result.Root.Opens[0]).Name);
        Assert.IsType<Expr.Resolve>(result.Root.Opens[1]);
        Assert.Equal("Lib3", ((Expr.Resolve)result.Root.Opens[1]).Name);
    }

    [Fact]
    public void Parse_Open_SingleItem_OneOpen()
    {
        // open Lib2 -> one open entry
        var result = Parser.ParseSyntax("open Lib2\nLib2 = { public Val2 = 20 }\nVal2");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Opens);
        Assert.IsType<Expr.Resolve>(result.Root.Opens[0]);
        Assert.Equal("Lib2", ((Expr.Resolve)result.Root.Opens[0]).Name);
    }

    [Fact]
    public void Parse_Open_CallInOpenList_BadOpenForm()
    {
        // open F(1,2), Lib3 -> Call is not a valid open form; should report error.
        // The comma inside F(1,2) must NOT split the list.
        var result = Parser.ParseSyntax("open F(1,2), Lib3\nF = { X = 1 }\nLib3 = { Y = 2 }\nY");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Invalid open form") && d.Message.Contains("call"));
    }

    // -- Open DotCall normalization tests -------------------------------------

    [Fact]
    public void Parse_Open_DotPath_NormalizesToDotCall()
    {
        // open Lib.Sub -> parser produces DotCall(Resolve("Lib"), "Sub", null)
        var result = Parser.ParseSyntax("open Lib.Sub\nLib = { public Sub = { public X = 1 } }\nX");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Opens);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Opens[0]);
        Assert.Equal("Sub", dotCall.Name);
        Assert.Null(dotCall.Args);
        Assert.IsType<Expr.Resolve>(dotCall.Target);
    }

    [Fact]
    public void Parse_Open_DotCallWithArgs_ReportsError()
    {
        // open Lib.Sub() -> DotCall with args -> rejected as invalid open form
        var result = Parser.ParseSyntax("open Lib.Sub()\nLib = { public Sub = { public X = 1 } }\nX");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("not allowed in open"));
    }

    [Fact]
    public void Parse_Open_NestedDotPath_NormalizesToNestedDotCall()
    {
        // open A.B.C -> DotCall(DotCall(Resolve("A"), "B", null), "C", null)
        var result = Parser.ParseSyntax("open A.B.C\nA = { public B = { public C = { public X = 1 } } }\nX");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Opens);
        var outer = Assert.IsType<Expr.DotCall>(result.Root.Opens[0]);
        Assert.Equal("C", outer.Name);
        Assert.Null(outer.Args);
        var inner = Assert.IsType<Expr.DotCall>(outer.Target);
        Assert.Equal("B", inner.Name);
        Assert.Null(inner.Args);
        Assert.IsType<Expr.Resolve>(inner.Target);
    }

    // -- Open declaration: new syntax tests -----------------------------------

    [Fact]
    public void Parse_Open_ByIdentifier()
    {
        var result = Parser.ParseSyntax("open A\n1");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Opens);
        var resolve = Assert.IsType<Expr.Resolve>(result.Root.Opens[0]);
        Assert.Equal("A", resolve.Name);
    }

    [Fact]
    public void Parse_Open_ByDottedPath()
    {
        var result = Parser.ParseSyntax("open Lib.Sub\n1");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Opens);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Opens[0]);
        Assert.Equal("Sub", dotCall.Name);
        Assert.Null(dotCall.Args);
        Assert.IsType<Expr.Resolve>(dotCall.Target);
    }

    [Fact]
    public void Parse_Open_ByLoadCall()
    {
        var source = "open load('https://katlang.org/algorithm.kat')\n1";
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Opens);
        var call = Assert.IsType<Expr.Call>(result.Root.Opens[0]);
        var fn = Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("load", fn.Name);
        Assert.NotNull(fn.Span);
    }

    [Fact]
    public void Parse_Open_StringLiteralSugar_DesugarsToLoad()
    {
        var source = "open 'https://katlang.org/algorithm.kat'\n1";
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Opens);
        var call = Assert.IsType<Expr.Call>(result.Root.Opens[0]);
        var fn = Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("load", fn.Name);
        Assert.Null(fn.Span);
        Assert.Single(call.Args);
        var strLit = Assert.IsType<Expr.StringLiteral>(call.Args[0]);
        Assert.Equal("https://katlang.org/algorithm.kat", strLit.Value);
    }

    [Fact]
    public void Parse_Open_MultipleTargets()
    {
        var source = "open A, 'https://katlang.org/algorithm.kat', Lib.Sub\n1";
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Opens.Count);
        Assert.IsType<Expr.Resolve>(result.Root.Opens[0]);
        Assert.IsType<Expr.Call>(result.Root.Opens[1]);
        Assert.IsType<Expr.DotCall>(result.Root.Opens[2]);
    }

    [Fact]
    public void Parse_Open_RepeatedDeclaration_ReportsError()
    {
        var result = Parser.ParseSyntax("open A\nopen B\n1");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Only one") && d.Message.Contains("open"));
    }

    [Fact]
    public void Parse_Open_InExpressionPosition_ReportsError()
    {
        var result = Parser.ParseSyntax("1 + open A");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("declaration") && d.Message.Contains("expression"));
    }

    [Fact]
    public void Parse_Open_InvalidTarget_NumericExpression_ReportsError()
    {
        var result = Parser.ParseSyntax("open 1 + 2\n3");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Invalid open form"));
    }

    [Theory]
    [InlineData("open A, B\n3", 2)]
    [InlineData("open A, B, C\n3", 3)]
    public void Parse_Open_CommaList_ParsesIndividualTargets(string source, int expectedTargets)
    {
        // `open` is a declaration with one comma-separated target list; the
        // targets are individual Lean-compatible forms — no SequenceConstruct and
        // no SequenceSpread node ever lands in the opens list.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(expectedTargets, result.Root.Opens.Count);
        Assert.All(result.Root.Opens, static open => Assert.IsType<Expr.Resolve>(open));
        Assert.Equal(3, Assert.IsType<Expr.Num>(Assert.Single(result.Root.Output)).Value);
    }

    [Fact]
    public void Parse_Open_SingleQuotedStringAndNameTargets_DesugarAndStayInOneList()
    {
        // `open 'url', A`: the single-quoted string desugars through the
        // load sugar and `A` stays a second open target — not an output row.
        var result = Parser.ParseSyntax("open 'https://katlang.org/lib.kat', A");

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Opens.Count);
        var load = Assert.IsType<Expr.Call>(result.Root.Opens[0]);
        Assert.Equal("load", Assert.IsType<Expr.Resolve>(load.Function).Name);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Opens[1]).Name);
        Assert.Empty(result.Root.Output);
    }

    [Fact]
    public void Parse_Open_SemicolonSeparator_ReportsCommaDiagnosticNotTwoTargets()
    {
        // ';' is not an open-target separator: `open` is a declaration, not
        // an output expression.
        var result = Parser.ParseSyntax("open A ; B\n3");

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Open target lists use ',' separators, not ';'"));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
    }

    [Fact]
    public void Parse_Open_SameLineAdjacency_ReportsMissingCommaNotTwoTargets()
    {
        var result = Parser.ParseSyntax("open A B\n3");

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Expected ',' between open targets"));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
    }

    [Theory]
    [InlineData("open A, B, C\n1")]
    [InlineData("open A,\nB,\nC\n1")]
    [InlineData("open A\n, B\n, C\n1")]
    public void Parse_Open_CommaContinuation_SpansLinesLikeGeneralCommaContinuation(string source)
    {
        // Comma keeps its normal explicit line-continuation behavior in
        // open target lists: trailing `open A,` newline `B` and leading
        // `open A` newline `, B` both continue the list.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Opens.Count);
        Assert.All(result.Root.Opens, static open => Assert.IsType<Expr.Resolve>(open));
        Assert.Equal(1, Assert.IsType<Expr.Num>(Assert.Single(result.Root.Output)).Value);
    }

    [Theory]
    [InlineData("open A.B\n1")]
    [InlineData("open A\n.B\n1")]
    [InlineData("open A # comment\n.B\n1")]
    public void Parse_Open_LeadingDotContinuation_ContinuesDottedTarget(string source)
    {
        // A leading '.' is the whitelisted dotted-path continuation, so a
        // dotted open target may span lines; comments stay invisible.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(result.Root.Opens));
        Assert.Equal("B", dotCall.Name);
        Assert.Null(dotCall.Args);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(dotCall.Target).Name);
    }

    [Fact]
    public void Parse_Open_DotContinuationThenCommaTarget_OpensBoth()
    {
        var result = Parser.ParseSyntax("open A\n.B,\nC\n1");

        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Opens.Count);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Opens[0]);
        Assert.Equal("B", dotCall.Name);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(result.Root.Opens[1]).Name);
    }

    [Theory]
    [InlineData("open\nA")]
    [InlineData("open # comment\nA")]
    public void Parse_Open_FirstTargetOnLaterLine_ReportsMissingTargetAndKeepsNextRow(string source)
    {
        // The first target must begin on the same physical line as `open`;
        // a newline right after `open` (comments invisible) is a missing
        // target, and `A` stays the next output row.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Expected an open target after 'open' on the same physical line"));
        Assert.Empty(result.Root.Opens);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Output)).Name);
    }

    [Fact]
    public void Parse_Open_DanglingCommaAtEnd_ReportsMissingTarget()
    {
        var result = Parser.ParseSyntax("open A,");

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Expected an open target after ','"));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
    }

    [Fact]
    public void Parse_Open_DanglingCommaBeforeDefinitionLine_KeepsDefinition()
    {
        // Recovery after a dangling comma leaves a following definition
        // line intact: P stays a property, never an open target.
        var result = Parser.ParseSyntax("open A,\nP = 1\nP");

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Expected an open target after ','"));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
        Assert.Equal("P", Assert.Single(result.Root.Properties).Name);
    }

    [Fact]
    public void Parse_Open_DanglingCommaBeforeDeconstructionLine_KeepsDeconstructionIntact()
    {
        // The open-target recovery boundary and the adjacency rule share ONE
        // declaration-starter relation. Historically the open-side copy missed
        // the binding-pattern form, so `x` was swallowed as a second open
        // target and the deconstruction was torn apart (opens [A, x], a lone
        // property `y`, plus a cascade diagnostic). The dangling comma now
        // reports exactly one targeted diagnostic and the following
        // deconstruction line stays one intact declaration.
        var result = Parser.ParseSyntax("open A,\nx, y = 1");

        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidOpenTargetList, diagnostic.Code);
        Assert.Contains("Expected an open target after ','", diagnostic.Message);
        // The span points at the dangling comma itself (line 1, column 7).
        Assert.Equal(new SourceSpan(1, 7, 1, 7), diagnostic.Span);

        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
        Assert.Empty(result.Root.Output);

        // The deconstruction elaborates exactly like its well-formed
        // counterpart `open A` newline `x, y = 1`: one synthetic shared-RHS
        // property plus one property per target, in declaration order.
        var canonical = Parser.ParseSyntax("open A\nx, y = 1");
        Assert.False(canonical.HasErrors);
        Assert.Equal(
            global::KatLang.ParserFuzz.FrontEndFingerprint.ComputeParseResult(canonical.Root, []),
            global::KatLang.ParserFuzz.FrontEndFingerprint.ComputeParseResult(result.Root, []));
        Assert.Equal(
            canonical.Root.Properties.Select(static p => p.Name),
            result.Root.Properties.Select(static p => p.Name));
        Assert.Equal(
            ["$deconstruct$0", "x", "y"],
            result.Root.Properties.Select(static p => p.Name).ToArray());

    }

    [Fact]
    public void Parse_Open_DanglingCommaBeforeCollectingDeconstruction_KeepsCollectMarker()
    {
        // The torn recovery was even worse for a collecting deconstruction:
        // after swallowing `x` as an open target, the separator-mistake branch
        // consumed the `*` run (the `open 'url'*` guard), so `*y` silently
        // became the PLAIN property `y`. The intact recovery keeps the whole
        // binding pattern, collect marker included.
        var result = Parser.ParseSyntax("open A,\nx, *y = (1, 2)");

        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidOpenTargetList, diagnostic.Code);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
        Assert.Equal(
            ["$deconstruct$0", "x", "y"],
            result.Root.Properties.Select(static p => p.Name).ToArray());

        var canonical = Parser.ParseSyntax("open A\nx, *y = (1, 2)");
        Assert.False(canonical.HasErrors);
        Assert.Equal(
            global::KatLang.ParserFuzz.FrontEndFingerprint.ComputeParseResult(canonical.Root, []),
            global::KatLang.ParserFuzz.FrontEndFingerprint.ComputeParseResult(result.Root, []));

        // `y` still binds through the shared sequence-value pattern as a
        // COLLECTING binding. The target property's body applies an inline
        // pattern helper to the shared RHS property; the pattern lives on
        // that helper.
        var yBody = Assert.IsType<Algorithm.User>(result.Root.Properties[2].Value);
        var helperCall = Assert.IsType<Expr.Call>(Assert.Single(yBody.Output));
        var yHelper = Assert.IsType<Expr.AlgorithmExpr>(helperCall.Function).Algorithm;
        var pattern = Assert.IsType<SequenceValueParameterPattern>(Assert.Single(yHelper.ParameterPatterns));
        Assert.Collection(
            pattern.Items,
            item => Assert.Equal(ParameterKind.Normal, Assert.IsType<CaptureParameterPattern>(item).Kind),
            item => Assert.Equal(ParameterKind.Collecting, Assert.IsType<CaptureParameterPattern>(item).Kind));
    }

    [Theory]
    [InlineData("open A,")]
    [InlineData("open 'url',")]
    public void Parse_Open_DanglingCommaBeforeStarLedDeconstruction_KeepsCollectMarker(string openLine)
    {
        var result = Parser.ParseSyntax(openLine + "\n*items = (1, 2)");

        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidOpenTargetList, diagnostic.Code);
        Assert.Single(result.Root.Opens);
        Assert.Equal(
            ["$deconstruct$0", "items"],
            result.Root.Properties.Select(static property => property.Name).ToArray());

        var itemsBody = Assert.IsType<Algorithm.User>(result.Root.Properties[1].Value);
        var helperCall = Assert.IsType<Expr.Call>(Assert.Single(itemsBody.Output));
        var helper = Assert.IsType<Expr.AlgorithmExpr>(helperCall.Function).Algorithm;
        var pattern = Assert.IsType<SequenceValueParameterPattern>(Assert.Single(helper.ParameterPatterns));
        var item = Assert.IsType<CaptureParameterPattern>(Assert.Single(pattern.Items));
        Assert.Equal(ParameterKind.Collecting, item.Kind);
        Assert.NotNull(item.CollectMarkerSpan);
    }

    [Fact]
    public void Parse_Open_DanglingCommaBeforeMalformedCollectingDeconstruction_KeepsIndependentDiagnostic()
    {
        var result = Parser.ParseSyntax("open A,\nx, * y = (1, 2)");

        Assert.Collection(
            result.Diagnostics,
            diagnostic => Assert.Equal(DiagnosticCode.InvalidOpenTargetList, diagnostic.Code),
            diagnostic => Assert.Equal(DiagnosticCode.InvalidCollectMarker, diagnostic.Code));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
        Assert.Equal(
            ["$deconstruct$0", "x", "y"],
            result.Root.Properties.Select(static property => property.Name).ToArray());

        var yBody = Assert.IsType<Algorithm.User>(result.Root.Properties[2].Value);
        var helperCall = Assert.IsType<Expr.Call>(Assert.Single(yBody.Output));
        var helper = Assert.IsType<Expr.AlgorithmExpr>(helperCall.Function).Algorithm;
        var pattern = Assert.IsType<SequenceValueParameterPattern>(Assert.Single(helper.ParameterPatterns));
        Assert.Equal(
            ParameterKind.Normal,
            Assert.IsType<CaptureParameterPattern>(pattern.Items[1]).Kind);
    }

    [Theory]
    [InlineData("open A,\r\nx, y = 1")]
    [InlineData("open A,\n\nx, y = 1")]
    [InlineData("open A, # trailing comment\n# leading comment\nx, y = 1")]
    public void Parse_Open_DanglingCommaPhysicalLineBoundary_IgnoresNewlineEncodingAndTrivia(string source)
    {
        var result = Parser.ParseSyntax(source);

        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidOpenTargetList, diagnostic.Code);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
        Assert.Equal(
            ["$deconstruct$0", "x", "y"],
            result.Root.Properties.Select(static property => property.Name).ToArray());
    }

    [Theory]
    [InlineData("P(x) = x")]
    [InlineData("public P = 1")]
    [InlineData("public P(x) = x")]
    [InlineData("~P = 1")]
    [InlineData("~public P = 1")]
    public void Parse_Open_DanglingCommaBeforeOtherDeclarationForms_LeavesDeclarationHeadIntact(
        string declaration)
    {
        var result = Parser.ParseSyntax("open A,\n" + declaration);

        Assert.Contains(
            result.Diagnostics,
            diagnostic => diagnostic.Code == DiagnosticCode.InvalidOpenTargetList
                && diagnostic.Message.Contains("Expected an open target after ','"));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
        Assert.Equal("P", Assert.Single(result.Root.Properties).Name);
    }

    [Fact]
    public void Parse_Open_DanglingCommaBeforeSecondOpen_LeavesKeywordForAlgorithmRecovery()
    {
        var result = Parser.ParseSyntax("open A,\nopen B");

        Assert.Contains(
            result.Diagnostics,
            diagnostic => diagnostic.Code == DiagnosticCode.InvalidOpenTargetList);
        Assert.Contains(
            result.Diagnostics,
            diagnostic => diagnostic.Code == DiagnosticCode.InvalidOpenDeclaration
                && diagnostic.Message.Contains("Only one 'open' declaration"));
        Assert.Equal(
            ["A", "B"],
            result.Root.Opens.Select(static open => Assert.IsType<Expr.Resolve>(open).Name).ToArray());
    }

    [Fact]
    public void Parse_Open_DanglingCommaBeforeClosingBrace_LeavesDelimiterForBlockParser()
    {
        var result = Parser.ParseSyntax("{open A,\n}");

        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidOpenTargetList, diagnostic.Code);
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(result.Root.Output)).Algorithm;
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(block.Opens)).Name);
        Assert.Empty(block.Properties);
        Assert.Empty(block.Output);
    }

    [Fact]
    public void Parse_Open_SameLineDeclarationBoundary_IsUnchangedByTheSharedRelation()
    {
        // The comma-spanning binding-pattern arm applies only to a candidate
        // on a NEW physical line: inside the open's own line the list's
        // separator commas are open syntax, so `open A, x, y = 1` keeps
        // today's recovery — `x` parses as a (bogus) open target and the
        // boundary still stops at `y = 1` through the direct property head.
        // This pins the adjacency gate: widening the binding-pattern arm to
        // same-line candidates would reinterpret the open list's own commas
        // and reject `A` itself.
        var result = Parser.ParseSyntax("open A, x, y = 1");

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Code == DiagnosticCode.InvalidOpenTargetList
                && d.Message.Contains("Expected an open target after ','"));
        Assert.Equal(
            ["A", "x"],
            result.Root.Opens.Select(static open => Assert.IsType<Expr.Resolve>(open).Name).ToArray());
        Assert.Equal("y", Assert.Single(result.Root.Properties).Name);
    }

    [Theory]
    [InlineData("open a, b, c\nx, y = 1")]
    [InlineData("open a,\nb,\nc\nx, y = 1")]
    public void Parse_Open_ValidListThenDeconstructionLine_StaysClean(string source)
    {
        // A fully valid open list followed by a deconstruction line parses
        // cleanly: the boundary checks inside the list must neither absorb a
        // target into a binding-pattern reading nor suppress the REAL binding
        // pattern that starts on the next line. The multi-line variant also
        // exercises the failed-scan memo in
        // LookaheadIsBindingPatternAssignment: the new-line candidate `b`
        // scans forward and fails exactly AT `x` (identifier after
        // identifier), `c` sits inside that failed region (the memo answers
        // false — `c` stays a target), and the statement-level consult at `x`
        // lands exactly ON the region's breaking token, which the memo must
        // exclude — a region inclusive of its breaking token would silently
        // swallow the deconstruction that legitimately starts there.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics));
        Assert.Equal(
            ["a", "b", "c"],
            result.Root.Opens.Select(static open => Assert.IsType<Expr.Resolve>(open).Name).ToArray());
        Assert.Equal(
            ["$deconstruct$0", "x", "y"],
            result.Root.Properties.Select(static p => p.Name).ToArray());
        Assert.Empty(result.Root.Output);
    }

    [Fact]
    public void Parse_Adjacency_BindingPatternAtScanBreakToken_StartsDeconstruction()
    {
        // `a b, c = 1` is the output row `a` followed by the deconstruction
        // `b, c = 1`: the statement-head binding-pattern scan at `a` fails
        // exactly AT `b` (identifier after identifier), and the adjacency
        // boundary then consults the relation at `b` itself. A failed-scan
        // memo that included its breaking token would answer false there and
        // tear the deconstruction into output rows and a stray `=`.
        var result = Parser.ParseSyntax("a b, c = 1");

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics));
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Output)).Name);
        Assert.Equal(
            ["$deconstruct$0", "b", "c"],
            result.Root.Properties.Select(static p => p.Name).ToArray());
    }

    [Theory]
    [InlineData("open 'url'*")]
    [InlineData("open 'url'* A")]
    [InlineData("open A, 'url'*")]
    [InlineData("open 'url'...")]
    public void Parse_Open_MarkedStringTarget_ReportsMissingCommaDiagnostic(string source)
    {
        // A string open target has no postfix continuations: a trailing star
        // (or a legacy `...` remnant, which lexes as three dots) is an
        // ordinary separator mistake, never a spread target — opens never
        // contain a SequenceSpread built from a string target.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Expected ',' between open targets"));
        Assert.DoesNotContain(result.Root.Opens, static open => open is Expr.SequenceSpread);
    }

    [Theory]
    [InlineData("open 'url'*")]
    [InlineData("open 'url'* A")]
    [InlineData("open A, 'url'*")]
    [InlineData("open 'url'**")]
    public void Parse_Open_StarAfterStringTarget_DoesNotReportPrefixCollectMarkerDiagnostic(string source)
    {
        // The separator diagnostic above is the whole story for a starred
        // string target. The consumed star must not fall through to statement
        // level, where ParsePrimary would report the PREFIX collect-marker
        // rule — guidance about binding syntax the user never wrote.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.DoesNotContain(
            result.Diagnostics,
            d => d.Message.Contains("Prefix `*` is the collect marker"));
    }

    [Fact]
    public void Parse_Open_CrossLineSemicolon_DoesNotContinueOpenList()
    {
        // Unlike `P = 1` newline `; 2` (where the leading ';' is invalid
        // expression syntax that error recovery still attaches to the body),
        // a ';'-led line after an open declaration is not an open continuation:
        // the declaration ended at the newline.
        var result = Parser.ParseSyntax("open A\n; B");

        Assert.True(result.HasErrors);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
    }

    [Fact]
    public void Parse_Open_DuplicateOpenDeclaration_RemainsInvalid()
    {
        // One `open` declaration per algorithm: a second `open` keeps the
        // existing diagnostic and never becomes multi-open syntax.
        var result = Parser.ParseSyntax("open A\nopen B");

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Only one 'open' declaration is allowed per algorithm"));
    }

    [Fact]
    public void Parse_Open_NewlineEndsTargetList()
    {
        // Open target lists are line-bounded: a plain physical newline ends
        // the list, so `open Math` newline `Math.Pi` stays an open plus a
        // report row — the second line is never a second open target.
        var result = Parser.ParseSyntax("open A\nB");

        Assert.False(result.HasErrors);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Output)).Name);
    }

    [Theory]
    [InlineData("open A...")]
    [InlineData("open A...B")]
    public void Parse_Open_EllipsisRemnantTarget_ReportsOrdinaryDotDiagnostic(string source)
    {
        // `...` is not a token: it lexes as three dots, so a legacy
        // ellipsis-marked open target fails through the ordinary
        // dotted-target diagnostics, and no spread target is ever built.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Expected property name after '.'."));
        Assert.DoesNotContain(result.Root.Opens, static open => open is Expr.SequenceSpread);
    }

    [Fact]
    public void Parse_Open_SpreadTarget_ReportsSourcePositionedSpan()
    {
        // The open-form rejection points at the offending spread target
        // `A*` (columns 6-7), not at the `open` keyword or the whole line.
        var result = Parser.ParseSyntax("open A*");

        Assert.True(result.HasErrors);
        var diagnostic = Assert.Single(
            result.Diagnostics,
            d => d.Message.Contains("Invalid open form: 'spread' is not allowed in open declarations"));
        Assert.Equal(1, diagnostic.Span.StartLineNumber);
        Assert.Equal(6, diagnostic.Span.StartColumn);
        Assert.Equal(1, diagnostic.Span.EndLineNumber);
        Assert.Equal(7, diagnostic.Span.EndColumn);
    }

    [Fact]
    public void Parse_Open_SpreadInCommaList_ReportsDiagnosticAndKeepsValidTargets()
    {
        // Valid comma-separated targets before the invalid spread target do
        // not hide the error; the rejected spread target stays in the parsed
        // opens list (open-form validation reports, it does not remove).
        var result = Parser.ParseSyntax("open A, B*");

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Invalid open form: 'spread' is not allowed in open declarations"));
        Assert.Equal(2, result.Root.Opens.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(result.Root.Opens[0]).Name);
        Assert.IsType<Expr.SequenceSpread>(result.Root.Opens[1]);
    }

    [Theory]
    [InlineData("open A*")]
    [InlineData("open A**")]
    [InlineData("open A, B*")]
    public void Parse_Open_SpreadMarkedTarget_IsRejectedByOpenFormValidation(string source)
    {
        // A spread-marked target parses to a SequenceSpread open target,
        // which open-form validation rejects — spread is not an open form.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Invalid open form: 'spread' is not allowed in open declarations"));
    }

    [Fact]
    public void Parse_Open_SemicolonThenSpreadExpression_ReportsCommaDiagnosticAndKeepsSpreadAsOutputRow()
    {
        // The ';' separator mistake is reported on the open declaration; the
        // rest of the line is ordinary output (where spread is
        // legal), never a second open target. `B*, C` parses as the two
        // expression-list slots `B*` and `C` (a spread takes no right operand).
        var result = Parser.ParseSyntax("open A ; B*, C");

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Open target lists use ',' separators, not ';'"));
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Opens)).Name);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.IsType<Expr.SequenceSpread>(result.Root.Output[0]);
        Assert.Equal("C", Assert.IsType<Expr.Resolve>(result.Root.Output[1]).Name);
    }

    [Fact]
    public void Parse_Open_StringLiteralDoesNotSurviveElaboration()
    {
        var source = "open 'https://katlang.org/test.kat'\n1";
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Opens);
        Assert.IsNotType<Expr.StringLiteral>(result.Root.Opens[0]);
        Assert.IsType<Expr.Call>(result.Root.Opens[0]);
    }

    [Fact]
    public void Parse_Open_AfterProperty_ReportsError()
    {
        var result = Parser.ParseSyntax("X = 1\nopen Math\n2");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("must appear before"));
    }

    [Fact]
    public void Parse_Open_AfterOutput_ReportsError()
    {
        var result = Parser.ParseSyntax("1\nopen Math\n2");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("must appear before"));
    }

    // ── `Output` as an ordinary identifier ──────────────────────────────────
    // There is no explicit output syntax: `Output = expr` is an ordinary
    // property definition, and expression rows are the only output mechanism.

    [Fact]
    public void Parse_Output_IsOrdinaryProperty()
    {
        var result = Parser.ParseSyntax("Output = 42");
        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("Output", property.Name);
        Assert.Empty(result.Root.Output);
    }

    [Fact]
    public void Parse_LowercaseOutput_IsOrdinaryProperty()
    {
        var result = Parser.ParseSyntax("output = 6\noutput");
        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("output", property.Name);
        Assert.Equal("output", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Output)).Name);
    }

    [Fact]
    public void Parse_OutputPropertyAndReferenceRow()
    {
        var result = Parser.ParseSyntax("Output = 5\nOutput");
        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("Output", property.Name);
        Assert.Equal("Output", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Output)).Name);
    }

    [Fact]
    public void Parse_OutputProperty_CaseSensitiveNames_AreDistinct()
    {
        var result = Parser.ParseSyntax("Output = 1\noutput = 2\nOUTPUT = 3");
        Assert.False(result.HasErrors);
        Assert.Equal(["Output", "output", "OUTPUT"], result.Root.Properties.Select(p => p.Name));
        Assert.Empty(result.Root.Output);
    }

    [Fact]
    public void Parse_DuplicateOutputProperty_ReportsOrdinaryDuplicateDiagnostic()
    {
        var result = Parser.ParseSyntax("Output = 1\nOutput = 2");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Property 'Output' is already defined."));
    }

    [Fact]
    public void Parse_OutputRow_InterleavedWithPropertyDefinitions()
    {
        var result = Parser.ParseSyntax("A = 1\nA + 1\nB = 2");
        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Properties.Count);
        Assert.Equal("A", result.Root.Properties[0].Name);
        Assert.Equal("B", result.Root.Properties[1].Name);
        Assert.Single(result.Root.Output);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Add, binary.Op);
    }

    [Fact]
    public void Parse_OutputProperty_WithFollowingRows_HasNoMixingRule()
    {
        // Former explicit/implicit mixing shapes are ordinary programs now: a
        // property named `Output` plus any number of output rows.
        var result = Parser.ParseSyntax("Output = 4\nOutput\n5");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("Output", property.Name);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.Equal("Output", Assert.IsType<Expr.Resolve>(result.Root.Output[0]).Name);
        Assert.Equal(5m, Assert.IsType<Expr.Num>(result.Root.Output[1]).Value);
    }

    [Fact]
    public void Parse_OutputProperty_InNestedBraceAlgorithm_IsOrdinary()
    {
        var result = Parser.ParseSyntax("F = {Output = 1\n3}\nF");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        var block = property.Value;
        Assert.Equal("Output", Assert.Single(block.Properties).Name);
        Assert.Equal(3m, Assert.IsType<Expr.Num>(Assert.Single(block.Output)).Value);
    }

    [Theory]
    [InlineData("1 ; 3")]
    [InlineData("1\n; 3")]
    public void Parse_OutputRows_SemicolonBetweenRows_ReportsUnsupportedExpressionSeparator(string source)
    {
        var result = Parser.ParseSyntax(source);

        AssertUnsupportedSemicolonDiagnostic(result);
        Assert.Equal(2, result.Root.Output.Count);
    }

    [Fact]
    public void Parse_OutputProperty_SemicolonInBody_ReportsUnsupportedExpressionSeparator()
    {
        var result = Parser.ParseSyntax("Output = 1 ; 3");

        AssertUnsupportedSemicolonDiagnostic(result);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("Output", property.Name);
    }

    [Theory]
    [InlineData("P = 1\n    3", false)]
    [InlineData("P = Add(1, 2)\n    3", true)]
    public void Parse_PropertyBody_IndentedNextLine_IsSeparateRowNotBodyContinuation(string source, bool bodyIsCall)
    {
        // Property/definition bodies are line-bounded: an indented expression on
        // the next line is a separate root output row, never silently absorbed
        // into the property body.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        var body = Assert.Single(property.Value.Output);
        if (bodyIsCall)
            Assert.IsType<Expr.Call>(body);
        else
            Assert.Equal(1m, Assert.IsType<Expr.Num>(body).Value);
        // `3` is a separate root output row, not part of P's body.
        Assert.Equal(3m, Assert.IsType<Expr.Num>(Assert.Single(result.Root.Output)).Value);
    }

    [Fact]
    public void Parse_PropertyBody_SameLineComma_StaysOneBodyWithMultipleSlots()
    {
        // Line-bounded bodies still accept same-line adjacency/comma: `P = 1, 2`
        // is one body with two slots.
        var result = Parser.ParseSyntax("P = 1, 2\nP");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        Assert.Equal([1m, 2m], property.Value.Output.Select(static expr => Assert.IsType<Expr.Num>(expr).Value));
    }

    [Theory]
    [InlineData("P = a b")]
    [InlineData("P = a, b")]
    public void Parse_PropertyBody_SameLineAdjacencyMatchesComma_KeepsBothSlotsInBody(string source)
    {
        // Same-line adjacency is an implicit comma inside a property body: `P = a b`
        // parses to the same two-slot body as `P = a, b`. Both `a` and `b` belong
        // to P, and nothing escapes to root output.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        Assert.Empty(result.Root.Output);
        Assert.Equal(["a", "b"], property.Value.Output.Select(static expr => Assert.IsType<Expr.Resolve>(expr).Name));
    }

    [Theory]
    [InlineData("P = a*,b")]
    [InlineData("P = a*, b")]
    public void Parse_PropertyBody_SpreadThenSameLineCommaSlot_KeepsSiblingSlotInBody(string source)
    {
        // The spread opens only its immediate operand `a`; the comma-separated
        // same-line `b` is a sibling expression-list slot inside P's body
        // (tight or spaced), and `b` does NOT escape to root.
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        Assert.Empty(result.Root.Output);
        Assert.Equal(2, property.Value.Output.Count);
        var spread = Assert.IsType<Expr.SequenceSpread>(property.Value.Output[0]);
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(spread.Operand).Name);
        Assert.Equal("b", Assert.IsType<Expr.Resolve>(property.Value.Output[1]).Name);
    }

    [Fact]
    public void Parse_PropertyBody_Column0NextLine_EndsBodyAndStartsRootOutput()
    {
        // A newline ends a simple property body. In `P = a` <newline> `b` with
        // `b` at column 0, P is defined as `a` and `b` is a separate root output
        // row — newline is a body boundary, not a same-line implicit comma.
        var result = Parser.ParseSyntax("P = a\nb");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("P", property.Name);
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(Assert.Single(property.Value.Output)).Name);
        // `b` is a separate root output, not part of P's body.
        Assert.Equal("b", Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Output)).Name);
    }

    [Fact]
    public void Parse_PropertyBody_SpreadSameLineVsNewline_DiffersInBodyMembership()
    {
        // Contrast: same-line `P = a*, b` keeps `b` as a sibling slot inside P;
        // a newline after the spread ends P's body, so `b` becomes a separate
        // root output. Spread does not change the newline boundary.
        var sameLine = Parser.ParseSyntax("P = a*, b");
        Assert.False(sameLine.HasErrors);
        var sameLineProperty = Assert.Single(sameLine.Root.Properties);
        Assert.Empty(sameLine.Root.Output);
        Assert.Equal(2, sameLineProperty.Value.Output.Count);
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(Assert.IsType<Expr.SequenceSpread>(sameLineProperty.Value.Output[0]).Operand).Name);
        Assert.Equal("b", Assert.IsType<Expr.Resolve>(sameLineProperty.Value.Output[1]).Name);

        var newline = Parser.ParseSyntax("P = a*\nb");
        Assert.False(newline.HasErrors);
        var newlineProperty = Assert.Single(newline.Root.Properties);
        var bodySpread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(newlineProperty.Value.Output));
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(bodySpread.Operand).Name);
        // `b` is a separate root output row, not part of P's body.
        Assert.Equal("b", Assert.IsType<Expr.Resolve>(Assert.Single(newline.Root.Output)).Name);
    }

    [Fact]
    public void Parse_PublicOutputProperty_IsOrdinaryPublicProperty()
    {
        var result = Parser.ParseSyntax("public Output = 42");
        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("Output", property.Name);
        Assert.True(property.IsPublic);
        Assert.Empty(result.Root.Output);
    }

    [Fact]
    public void Parse_PublicOutputClauseDefinition_IsOrdinaryPublicClause()
    {
        var result = Parser.ParseSyntax("public Output(x) = x + 1");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("Output", property.Name);
        Assert.True(property.IsPublic);
        var user = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal(["x"], user.Params);
    }

    [Fact]
    public void Parse_OutputRows_InterleavedInsideBlock()
    {
        var result = Parser.ParseSyntax("X = {A = 1\nA + 1\nB = 2}");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        var block = result.Root.Properties[0].Value;
        Assert.Equal(2, block.Properties.Count);
        Assert.Single(block.Output);
    }

    [Fact]
    public void Parse_OutputClauseDefinition_IsOrdinaryCallableProperty()
    {
        var result = Parser.ParseSyntax("Output(x) = x + 1");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("Output", property.Name);
        var user = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal(["x"], user.Params);
    }

    [Fact]
    public void Parse_OutputClauseGroup_IsOrdinaryConditionalFamily()
    {
        var result = Parser.ParseSyntax("Output(0) = 0\nOutput(x) = x");

        Assert.False(result.HasErrors);
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("Output", property.Name);
        var conditional = Assert.IsType<Algorithm.Conditional>(property.Value);
        Assert.Equal(2, conditional.Branches.Count);
    }

    [Fact]
    public void Parse_ParametrizedAlgorithm_WithoutOutput_ReportsError()
    {
        var result = Parser.ParseSyntax(
            """
            Algo(x, y) = {
              Prop = 7
            }
            """);

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d =>
            d.Message.Contains("declares explicit parameters") &&
            d.Message.Contains("does not define an output"));
    }

    [Fact]
    public void Parse_ParametrizedAlgorithm_WithOnlyHelperProperties_ReportsError()
    {
        var result = Parser.ParseSyntax(
            """
            Algo(x) = {
              A = x + 1
              B = 2
            }
            """);

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d =>
            d.Message.Contains("declares explicit parameters") &&
            d.Message.Contains("does not define an output"));
    }

    [Fact]
    public void Parse_ParametrizedAlgorithm_WithOutputRowInBody()
    {
        var result = Parser.ParseSyntax("Algo(x) = { x + 1 }");

        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        var user = Assert.IsType<Algorithm.User>(result.Root.Properties[0].Value);
        Assert.Equal(["x"], user.Params);
        Assert.Single(user.Output);
        var binary = Assert.IsType<Expr.Binary>(user.Output[0]);
        Assert.Equal(BinaryOp.Add, binary.Op);
    }

    private static void AssertCollectingParameters(
        string source,
        string[] expectedNames,
        ParameterKind[] expectedKinds,
        string[]? expectedPatternDisplay = null)
    {
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(diagnostic => diagnostic.Message)));
        var property = Assert.Single(result.Root.Properties);
        var user = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal(expectedNames, user.Params);
        Assert.Equal(expectedNames, user.Parameters.Select(parameter => parameter.Name).ToArray());
        Assert.Equal(expectedKinds, user.Parameters.Select(parameter => parameter.Kind).ToArray());
        Assert.Equal(expectedNames, user.ExplicitParameters.Select(parameter => parameter.Name).ToArray());
        Assert.Equal(expectedKinds, user.ExplicitParameters.Select(parameter => parameter.Kind).ToArray());
        if (expectedPatternDisplay is not null)
            Assert.Equal(expectedPatternDisplay, user.ParameterPatterns.Select(parameter => parameter.DisplayName).ToArray());
    }

    [Fact]
    public void Parse_CollectingExplicitParameter_ParsesNameAndKind()
        => AssertCollectingParameters(
            "Collect(*list) = list",
            ["list"],
            [ParameterKind.Collecting]);

    [Fact]
    public void Parse_NormalThenCollectingExplicitParameter_ParsesNameAndKind()
        => AssertCollectingParameters(
            "Collect(a, *rest) = rest",
            ["a", "rest"],
            [ParameterKind.Normal, ParameterKind.Collecting]);

    [Fact]
    public void Parse_CollectingThenSuffixExplicitParameter_ParsesNameAndKind()
        => AssertCollectingParameters(
            "Scale(*values, factor) = values",
            ["values", "factor"],
            [ParameterKind.Collecting, ParameterKind.Normal]);

    [Fact]
    public void Parse_SequenceValueCollectingExplicitParameter_ParsesFixedSlotKind()
        => AssertCollectingParameters(
            "Collect((*list)) = list",
            ["list"],
            [ParameterKind.Collecting],
            ["(*list)"]);

    [Fact]
    public void Parse_SequenceValueCollectingWithSuffixExplicitParameters_ParsesFixedSlotKind()
        => AssertCollectingParameters(
            "Collect((*history), previous, next) = history",
            ["history", "previous", "next"],
            [ParameterKind.Collecting, ParameterKind.Normal, ParameterKind.Normal],
            ["(*history)", "previous", "next"]);

    [Fact]
    public void Parse_HeadTailSequenceValueExplicitParameter_ParsesRecursivePattern()
        => AssertCollectingParameters(
            "Collect((head, *tail)) = head, tail",
            ["head", "tail"],
            [ParameterKind.Normal, ParameterKind.Collecting],
            ["(head, *tail)"]);

    [Fact]
    public void Parse_FirstMiddleLastSequenceValueExplicitParameter_ParsesRecursivePattern()
        => AssertCollectingParameters(
            "Collect((first, *middle, last)) = first, middle, last",
            ["first", "middle", "last"],
            [ParameterKind.Normal, ParameterKind.Collecting, ParameterKind.Normal],
            ["(first, *middle, last)"]);

    [Fact]
    public void Parse_NestedSequenceValueExplicitParameter_ParsesRecursivePattern()
        => AssertCollectingParameters(
            "Collect(((*history, pre2), pre1)) = history, pre2, pre1",
            ["history", "pre2", "pre1"],
            [ParameterKind.Collecting, ParameterKind.Normal, ParameterKind.Normal],
            ["((*history, pre2), pre1)"]);

    [Fact]
    public void Parse_PrefixCollectingSuffixExplicitParameter_ParsesNameAndKind()
        => AssertCollectingParameters(
            "Surround(prefix, *values, suffix) = values",
            ["prefix", "values", "suffix"],
            [ParameterKind.Normal, ParameterKind.Collecting, ParameterKind.Normal]);

    [Fact]
    public void Parse_SeparateCollectingCapturesAtDifferentPatternLevels_Parses()
        => AssertCollectingParameters(
            "Nested((*inner), *outer) = inner.count, outer.count",
            ["inner", "outer"],
            [ParameterKind.Collecting, ParameterKind.Collecting],
            ["(*inner)", "*outer"]);

    [Fact]
    public void Parse_MultipleCollectingExplicitParameters_ReportsError()
    {
        var result = Parser.ParseSyntax("Bad(*a, *b) = b");

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, diagnostic => diagnostic.Message.Contains("Only one collecting binding is allowed per pattern level."));
    }

    [Fact]
    public void Parse_RepeatedCollectingAndNormalName_ReportsUnsupportedError()
    {
        var result = Parser.ParseSyntax("Bad(*xs, xs) = xs");

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("Repeated parameter names cannot include collecting bindings."));
    }

    [Fact]
    public void Parse_RepeatedCollectingNameAtSameLevel_RemainsRejected()
    {
        var result = Parser.ParseSyntax("Bad(*xs, *xs) = xs");

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("Only one collecting binding is allowed per pattern level."));
    }

    [Fact]
    public void Parse_CollectingExplicitParameterWithGrace_ReportsError()
    {
        var result = Parser.ParseSyntax("Bad(*a~) = a");

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, diagnostic => diagnostic.Message.Contains("Collecting bindings cannot use `~` reordering."));
    }

    [Fact]
    public void Parse_PostfixStarBinding_IsRejectedWithCanonicalReplacement()
    {
        // Postfix `items*` in a binding pattern is the spread marker on a
        // binding name — never a collecting binding.
        var result = Parser.ParseSyntax("Collect(items*) = items");

        Assert.True(result.HasErrors);
        var error = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        Assert.Equal(
            "Postfix `*` is the spread marker and is not valid in a binding pattern. Write `*items` to declare a collecting binding.",
            error.Message);
        Assert.Equal(new SourceSpan(1, 9, 1, 14), error.Span); // covers `items*`

        // The rejected spelling never becomes a collecting binding.
        var property = Assert.Single(result.Root.Properties);
        var user = Assert.IsType<Algorithm.User>(property.Value);
        var capture = Assert.IsType<CaptureParameterPattern>(Assert.Single(user.ParameterPatterns));
        Assert.Equal(ParameterKind.Normal, capture.Kind);
        Assert.Equal("items", capture.DisplayName);
        Assert.Null(capture.CollectMarkerSpan);
    }

    [Fact]
    public void Parse_PrefixCollectingBinding_ParsesCanonicalOrientationAndExactSpans()
    {
        var result = Parser.ParseSyntax("Collect(*items) = items");

        Assert.Empty(result.Diagnostics);
        var property = Assert.Single(result.Root.Properties);
        var user = Assert.IsType<Algorithm.User>(property.Value);
        var capture = Assert.IsType<CaptureParameterPattern>(Assert.Single(user.ParameterPatterns));
        Assert.Equal(ParameterKind.Collecting, capture.Kind);
        Assert.Equal("*items", capture.DisplayName);
        Assert.Equal(new SourceSpan(1, 10, 1, 14), capture.Span);
        Assert.Equal(new SourceSpan(1, 9, 1, 9), capture.CollectMarkerSpan);
    }

    [Fact]
    public void Parse_DetachedCollectMarker_ReportsAttachmentDiagnosticAndKeepsFixedBinding()
    {
        // The collect marker must be DIRECTLY attached: a same-line gap is an
        // attachment error and there is no whitespace-tolerant form.
        var result = Parser.ParseSyntax("Collect(* items) = items");

        Assert.True(result.HasErrors);
        var error = Assert.Single(result.Diagnostics);
        Assert.Equal(
            "The collect marker `*` must be directly attached to its binding name: write `*items`.",
            error.Message);
        Assert.Equal(new SourceSpan(1, 9, 1, 15), error.Span); // covers `* items`

        var property = Assert.Single(result.Root.Properties);
        var user = Assert.IsType<Algorithm.User>(property.Value);
        var capture = Assert.IsType<CaptureParameterPattern>(Assert.Single(user.ParameterPatterns));
        Assert.Equal(ParameterKind.Normal, capture.Kind);
        Assert.Equal("items", capture.DisplayName);
        Assert.Null(capture.CollectMarkerSpan);
    }

    [Fact]
    public void Parse_RepeatedCollectMarker_ReportsRepeatedDiagnosticAndKeepsFixedBinding()
    {
        var result = Parser.ParseSyntax("Collect(**items) = items");

        Assert.True(result.HasErrors);
        var error = Assert.Single(result.Diagnostics);
        Assert.Equal(
            "A collecting binding uses exactly one collect marker: write `*items`.",
            error.Message);
        Assert.Equal(new SourceSpan(1, 9, 1, 15), error.Span); // covers `**items`

        var property = Assert.Single(result.Root.Properties);
        var user = Assert.IsType<Algorithm.User>(property.Value);
        var capture = Assert.IsType<CaptureParameterPattern>(Assert.Single(user.ParameterPatterns));
        Assert.Equal(ParameterKind.Normal, capture.Kind);
        Assert.Equal("items", capture.DisplayName);
        Assert.Null(capture.CollectMarkerSpan);
    }

    [Fact]
    public void Parse_CollectMarker_CannotBeSeparatedFromNameByNewline()
    {
        var result = Parser.ParseSyntax(
            """
            Collect(*
              items) = items
            """);

        Assert.True(result.HasErrors);
        // The cross-line marker is never a collecting binding: the attachment
        // diagnostic fires and `items` stays a fixed binding.
        Assert.Contains(
            result.Diagnostics,
            diagnostic => diagnostic.Message.Contains(
                "The collect marker `*` must be directly attached to its binding name: write `*items`.",
                StringComparison.Ordinal));
        AssertNoCollectingBindings(result.Root);
    }

    [Fact]
    public void Parse_PrefixCollectingDeconstruction_PreservesNameAndMarkerSpans()
    {
        var result = Parser.ParseSyntax("first, *middle, last = values");

        Assert.Empty(result.Diagnostics);
        var middle = Assert.Single(result.Root.Properties, property => property.Name == "middle");
        var body = Assert.IsType<Algorithm.User>(middle.Value);
        var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
        var helperBlock = Assert.IsType<Expr.AlgorithmExpr>(call.Function);
        var sequence = Assert.IsType<SequenceValueParameterPattern>(
            Assert.Single(helperBlock.Algorithm.ParameterPatterns));
        var capture = Assert.IsType<CaptureParameterPattern>(sequence.Items[1]);
        Assert.Equal("middle", capture.Name);
        Assert.Null(capture.Span); // the helper is synthetic; the property declaration owns the name span
        Assert.Equal(new SourceSpan(1, 8, 1, 8), capture.CollectMarkerSpan);
        Assert.Equal(new SourceSpan(1, 9, 1, 14), Assert.Single(middle.DeclarationSpans));
    }

    [Theory]
    [InlineData(
        "first, * middle, last = values",
        "The collect marker `*` must be directly attached to its binding name: write `*middle`.")]
    [InlineData(
        "first, **middle, last = values",
        "A collecting binding uses exactly one collect marker: write `*middle`.")]
    public void Parse_MalformedDeconstructionCollectMarker_ReportsTargetedDiagnosticAndKeepsFixedBinding(
        string source,
        string expectedMessage)
    {
        // The deconstruction lookahead is tolerant of malformed marker shapes
        // so the targeted attachment/repeated-marker diagnostics can fire, but
        // malformed recovery never creates a collecting binding — the name
        // stays an ordinary fixed target.
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            diagnostic => diagnostic.Message.Contains(expectedMessage, StringComparison.Ordinal));
        Assert.All(
            result.Diagnostics,
            diagnostic => Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity));
        AssertNoCollectingBindings(result.Root);
    }

    [Theory]
    [InlineData("Bad(*) = 0", "The collect marker `*` must be followed by a binding name, as in `*items`.")]
    [InlineData("Bad(*1) = 0", "The collect marker `*` must be followed by a binding name, as in `*items`.")]
    [InlineData("Bad(*(item)) = 0", "The collect marker `*` must be followed by a binding name, as in `*items`.")]
    [InlineData("Bad(items*) = 0", "Postfix `*` is the spread marker and is not valid in a binding pattern.")]
    [InlineData("Use(*items)", "Prefix `*` is the collect marker and is valid only in binding patterns")]
    public void Parse_InvalidPatternStarShape_ReportsErrorAndRecovers(
        string source,
        string expectedMessage)
    {
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            diagnostic => diagnostic.Message.Contains(expectedMessage, StringComparison.Ordinal));
        Assert.NotNull(result.Root);
    }

    [Fact]
    public void Parse_MalformedPatternCollectMarker_RecoversToFollowingDeclarationAndOutput()
    {
        var result = Parser.ParseSyntax(
            """
            Bad(*, item) = item
            Good = 7
            Good
            """);

        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            diagnostic => diagnostic.Message.Contains(
                "The collect marker `*` must be followed by a binding name, as in `*items`.",
                StringComparison.Ordinal));
        Assert.Contains(result.Root.Properties, static property => property.Name == "Good");
        Assert.Equal(
            "Good",
            Assert.IsType<Expr.Resolve>(Assert.Single(result.Root.Output)).Name);
    }

    private sealed class ParserCollectingBindingFinder : AstWalker
    {
        public bool Found { get; private set; }

        protected override void VisitExplicitParameterDeclaration(
            Algorithm algorithm,
            ParameterDeclaration declaration)
        {
            if (declaration.Kind == ParameterKind.Collecting)
                Found = true;
        }

        protected override void VisitConditionalBinderDeclaration(Pattern.Bind pattern, SourceSpan span)
        {
            if (pattern.ParameterKind == ParameterKind.Collecting)
                Found = true;
        }
    }

    private static void AssertNoCollectingBindings(Algorithm root)
    {
        var finder = new ParserCollectingBindingFinder();
        finder.VisitAlgorithm(root);
        Assert.False(finder.Found);
    }

    [Fact]
    public void Parse_ContainerWithParametrizedChildProperty_RemainsValid()
    {
        var result = Parser.ParseSyntax("Algo = { Prop(x, y) = 7 }");

        Assert.False(result.HasErrors);
        var algo = Assert.IsType<Algorithm.User>(result.Root.Properties[0].Value);
        Assert.Empty(algo.Params);
        var prop = Assert.Single(algo.Properties);
        var child = Assert.IsType<Algorithm.User>(prop.Value);
        Assert.Equal(["x", "y"], child.Params);
        Assert.Single(child.Output);
    }

    [Fact]
    public void Parse_ImplicitOuterOutputOwnership_MarksNestedPropertyLocalOnly()
    {
        var result = Parser.Parse(
            """
            Algo = {
              Prop = x + 1
              x
            }
            """);

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));
        var algo = Assert.IsType<Algorithm.User>(result.Root.Properties[0].Value);
        Assert.Equal(["x"], algo.Params);

        var prop = Assert.Single(algo.Properties);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, prop.Exposure);

        var propBody = Assert.IsType<Algorithm.User>(prop.Value);
        Assert.Empty(propBody.Params);
    }

    [Fact]
    public void Parse_ExplicitAndImplicitOuterOutputOwnership_AreEquivalent()
    {
        var implicitResult = Parser.Parse(
            """
            Algo = {
              Prop = x + 1
              x
            }
            """);
        var explicitResult = Parser.Parse(
            """
            Algo(x) = {
              Prop = x + 1
              x
            }
            """);

        Assert.False(implicitResult.HasErrors, string.Join(Environment.NewLine, implicitResult.Diagnostics.Select(d => d.Message)));
        Assert.False(explicitResult.HasErrors, string.Join(Environment.NewLine, explicitResult.Diagnostics.Select(d => d.Message)));

        var implicitAlgo = Assert.IsType<Algorithm.User>(implicitResult.Root.Properties[0].Value);
        var explicitAlgo = Assert.IsType<Algorithm.User>(explicitResult.Root.Properties[0].Value);
        Assert.Equal(["x"], implicitAlgo.Params);
        Assert.Equal(["x"], explicitAlgo.Params);

        var implicitProp = Assert.Single(implicitAlgo.Properties);
        var explicitProp = Assert.Single(explicitAlgo.Properties);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, implicitProp.Exposure);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, explicitProp.Exposure);
        Assert.Empty(Assert.IsType<Algorithm.User>(implicitProp.Value).Params);
        Assert.Empty(Assert.IsType<Algorithm.User>(explicitProp.Value).Params);
    }

        [Fact]
        public void Parse_NestedLocalPropertyDependencyOnCapturedSibling_PropagatesLocalOnlyExposure()
        {
                var result = Parser.Parse(
                        """
                        Algo(x) = {
                            Captured = x + 1
                            Wrapper = {
                                Inner = Captured
                                Inner
                            }
                            x
                        }
                        """);

                Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));
                var algo = Assert.IsType<Algorithm.User>(result.Root.Properties[0].Value);

                var captured = Assert.Single(algo.Properties, property => property.Name == "Captured");
                var wrapper = Assert.Single(algo.Properties, property => property.Name == "Wrapper");

                Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, captured.Exposure);
                Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, wrapper.Exposure);

                var wrapperBody = Assert.IsType<Algorithm.User>(wrapper.Value);
                var inner = Assert.Single(wrapperBody.Properties);
                Assert.Equal("Inner", inner.Name);
                Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, inner.Exposure);
        }

    [Fact]
    public void Parse_NestedPropertyOwnsParameter_WhenOuterOutputDoesNotUseIt()
    {
        var result = Parser.Parse(
            """
            Algo = {
              Prop = x + 1
              7
            }
            """);

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));
        var algo = Assert.IsType<Algorithm.User>(result.Root.Properties[0].Value);
        Assert.Empty(algo.Params);

        var prop = Assert.Single(algo.Properties);
        Assert.Equal(PropertyExposure.Exported, prop.Exposure);
        Assert.Equal(["x"], Assert.IsType<Algorithm.User>(prop.Value).Params);
    }

    [Fact]
    public void Parse_PlainContainerAlgorithm_RemainsValid()
    {
        var result = Parser.ParseSyntax("Algo = { Prop = 7 }");

        Assert.False(result.HasErrors);
        var algo = Assert.IsType<Algorithm.User>(result.Root.Properties[0].Value);
        Assert.Empty(algo.Params);
        Assert.Empty(algo.Output);
        Assert.Single(algo.Properties);
    }

    [Fact]
    public void Parse_OutputDotCall_IsOrdinaryDotCall()
    {
        var result = Parser.ParseSyntax(
            """
            Algo = {
              Output(x) = x + 1
            }
            Algo.Output(6)
            """);

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(result.Root.Output));
        Assert.Equal("Output", dotCall.Name);
        Assert.NotNull(dotCall.Args);
    }

    [Fact]
    public void Parse_NestedOutputDotCall_IsOrdinaryDotCall()
    {
        var result = Parser.ParseSyntax(
            """
            Outer = {
              Inner = {
                Output(x) = x + 10
              }
            }
            Outer.Inner.Output(6)
            """);

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(result.Root.Output));
        Assert.Equal("Output", dotCall.Name);
    }

    [Fact]
    public void Parse_BareOutputDotAccess_IsOrdinaryDotCall()
    {
        var result = Parser.ParseSyntax(
            """
            Algo = {
              Output = 9
            }
            Algo.Output
            """);

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(result.Root.Output));
        Assert.Equal("Output", dotCall.Name);
        Assert.Null(dotCall.Args);
    }

    // -- Double-parens: ordinary parentheses unless preserving a sequence-value receiver block ---

    [Fact]
    public void Parse_ParenSubExpr_FirstCallArg_ParsesNormally()
    {
        // f((a + b) mod 2, c) must parse without error now that
        // double-parens detection is removed
        var result = Parser.ParseSyntax("F((a + b) mod 2, c)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(2, call.Args.Count);
        // First arg should be binary mod expression
        var modExpr = Assert.IsType<Expr.Binary>(call.Args[0]);
        Assert.Equal(BinaryOp.Mod, modExpr.Op);
    }

    [Fact]
    public void Parse_If_ParenSubExpr_FirstArg_ParsesNormally()
    {
        var result = Parser.ParseSyntax("if((a + b) mod 2 == 0, 1, 0)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(3, call.Args.Count);
    }

    [Fact]
    public void Parse_DoubleParens_RemainsOrdinaryGrouping()
    {
        // Scalar/sequence-value-free cases still collapse to ordinary nested parentheses.
        var result = Parser.ParseSyntax("X = ((1 + 2))");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        var output = result.Root.Properties[0].Value.Output;
        Assert.Single(output);
        var binary = Assert.IsType<Expr.Binary>(output[0]);
        Assert.Equal(BinaryOp.Add, binary.Op);
    }

    // -- Direct-call argument boundaries for while/repeat ---

    [Fact]
    public void Parse_While_DirectCall_MultiInit_PreservesArgs()
    {
        var result = Parser.ParseSyntax("while(Step, x, 0)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(3, call.Args.Count);
        Assert.IsType<Expr.Resolve>(call.Args[0]);
        Assert.IsType<Expr.Resolve>(call.Args[1]);
        Assert.IsType<Expr.Num>(call.Args[2]);
    }

    [Fact]
    public void Parse_While_DirectCall_TwoArgs_NoLowering()
    {
        // while(Step, init) stays with 2 args, no lowering
        var result = Parser.ParseSyntax("while(Step, init)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(2, call.Args.Count);
        Assert.IsType<Expr.Resolve>(call.Args[1]);
    }

    [Fact]
    public void Parse_Repeat_DirectCall_MultiInit_PreservesArgs()
    {
        var result = Parser.ParseSyntax("repeat(Step, n, x, 0)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(4, call.Args.Count);
        Assert.IsType<Expr.Resolve>(call.Args[0]);
        Assert.IsType<Expr.Resolve>(call.Args[1]);
        Assert.IsType<Expr.Resolve>(call.Args[2]);
        Assert.IsType<Expr.Num>(call.Args[3]);
    }

    [Fact]
    public void Parse_Repeat_DirectCall_ThreeArgs_NoLowering()
    {
        // repeat(Step, n, init) stays with 3 args, no lowering
        var result = Parser.ParseSyntax("repeat(Step, n, init)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(3, call.Args.Count);
        Assert.IsType<Expr.Resolve>(call.Args[2]);
    }

    [Fact]
    public void Parse_First_DirectCall_MultiResult_PreservesOrdinaryArgs()
    {
        // first(x, y, z) should stay as three ordinary call arguments.
        var result = Parser.ParseSyntax("first(x, y, z)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(3, call.Args.Count);
        Assert.All(call.Args, expression => Assert.IsType<Expr.Resolve>(expression));
    }

    [Fact]
    public void Parse_Last_DirectCall_MultiResult_PreservesOrdinaryArgs()
    {
        // last(x, y, z) should stay as three ordinary call arguments.
        var result = Parser.ParseSyntax("last(x, y, z)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(3, call.Args.Count);
        Assert.All(call.Args, expression => Assert.IsType<Expr.Resolve>(expression));
    }

    [Fact]
    public void Parse_Take_DirectCall_PreservesSuffixCountOrder()
    {
        var result = Parser.ParseSyntax("take(x, y, z, n)");
        Assert.False(result.HasErrors);

        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(4, call.Args.Count);
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(call.Args[0]).Name);
        Assert.Equal("y", Assert.IsType<Expr.Resolve>(call.Args[1]).Name);
        Assert.Equal("z", Assert.IsType<Expr.Resolve>(call.Args[2]).Name);
        Assert.Equal("n", Assert.IsType<Expr.Resolve>(call.Args[3]).Name);
    }

    [Fact]
    public void Parse_Skip_DirectCall_PreservesSuffixCountOrder()
    {
        var result = Parser.ParseSyntax("skip(x, y, z, n)");
        Assert.False(result.HasErrors);

        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(4, call.Args.Count);
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(call.Args[0]).Name);
        Assert.Equal("y", Assert.IsType<Expr.Resolve>(call.Args[1]).Name);
        Assert.Equal("z", Assert.IsType<Expr.Resolve>(call.Args[2]).Name);
        Assert.Equal("n", Assert.IsType<Expr.Resolve>(call.Args[3]).Name);
    }

    [Fact]
    public void Parse_DotCall_Take_NoLowering_InParser()
    {
        var result = Parser.ParseSyntax("values.take(n)");
        Assert.False(result.HasErrors);

        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("take", dotCall.Name);
        Assert.NotNull(dotCall.Args);
        Assert.Single(dotCall.Args!);
        Assert.Equal("n", Assert.IsType<Expr.Resolve>(dotCall.Args[0]).Name);
    }

    [Fact]
    public void Parse_DotCall_While_NoLowering_InParser()
    {
        // Step.while(x, 0) keeps both explicit init arguments in the parser.
        var result = Parser.ParseSyntax("Step.while(x, 0)");
        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("while", dotCall.Name);
        Assert.NotNull(dotCall.Args);
        Assert.Equal(2, dotCall.Args!.Count);
    }

    // ── if arity validation ─────────────────────────────────────────────────

    [Fact]
    public void Parse_If_TwoArgs_ReportsBuiltinArityError()
    {
        var result = Parser.ParseSyntax("if(1, 2)");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse."));
    }

    [Fact]
    public void Parse_If_ThreeArgs_RemainsIf()
    {
        var result = Parser.ParseSyntax("if(1, 2, 3)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        var resolve = Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("if", resolve.Name);
        Assert.Equal(3, call.Args.Count);
    }

    [Fact]
    public void Parse_If_TwoArgs_InsideExpression_ReportsBuiltinArityError()
    {
        var result = Parser.ParseSyntax("10 * if(7 < 6, 1)");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse."));
    }

    [Fact]
    public void Parse_If_ZeroArgs_ReportsError()
    {
        var result = Parser.ParseSyntax("if()");
        Assert.True(result.HasErrors);
    }

    [Fact]
    public void Parse_If_OneArg_ReportsError()
    {
        var result = Parser.ParseSyntax("if(1)");
        Assert.True(result.HasErrors);
    }

    [Fact]
    public void Parse_If_FourArgs_ReportsError()
    {
        var result = Parser.ParseSyntax("if(1, 2, 3, 4)");
        Assert.True(result.HasErrors);
    }

    // Issue #131: an explicit spread argument has a runtime-only count, so the
    // static if-arity gate is skipped and the spread marker is preserved for the
    // evaluator to expand.
    [Fact]
    public void Parse_If_SpreadArgument_NoArityError_KeepsSpread()
    {
        var result = Parser.ParseSyntax("if(X*)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        var resolve = Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("if", resolve.Name);
        var argument = Assert.Single(call.Args);
        var spread = Assert.IsType<Expr.SequenceSpread>(argument);
        Assert.IsType<Expr.Resolve>(spread.Operand);
    }

    [Fact]
    public void Parse_If_MixedLiteralAndSpread_NoArityError_KeepsSpread()
    {
        var result = Parser.ParseSyntax("if(1, Pair*)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        var resolve = Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("if", resolve.Name);
        Assert.Equal(2, call.Args.Count);
        Assert.IsType<Expr.SequenceSpread>(call.Args[1]);
    }

    // A bare grouped value used without spread is still one structural argument,
    // so the friendly parse-time diagnostic must still fire.
    [Fact]
    public void Parse_If_SingleNonSpreadArgument_ReportsBuiltinArityError()
    {
        var result = Parser.ParseSyntax("if(X)");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse."));
    }

    // Only a TOP-LEVEL argument spread relaxes the gate. A spread nested inside
    // parentheses materializes one sequence-value argument, so `if((X*), 1)`
    // is two structural arguments and must still report the arity diagnostic.
    [Fact]
    public void Parse_If_ParenthesizedNestedSpread_StillReportsBuiltinArityError()
    {
        var result = Parser.ParseSyntax("if((X*), 1)");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse."));
    }

    // Two top-level spreads also defer arity to the evaluator.
    [Fact]
    public void Parse_If_MultipleSpreads_NoArityError()
    {
        var result = Parser.ParseSyntax("if(A*, B*)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(2, call.Args.Count);
        Assert.All(call.Args, argument => Assert.IsType<Expr.SequenceSpread>(argument));
    }

    // ── Clause definition classification ────────────────────────────────────

    [Fact]
    public void Parse_Clause_FlatMultiBinderSingleBranch_ElaboratesToOrdinaryAlgorithm()
    {
        var result = Parser.ParseSyntax("K(a, b) = a");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        var prop = result.Root.Properties[0];
        Assert.Equal("K", prop.Name);
        var user = Assert.IsType<Algorithm.User>(prop.Value);
        Assert.Equal(["a", "b"], user.Params);
        Assert.Single(user.Output);
    }

    [Fact]
    public void Parse_Clause_SingleBinder_ElaboratesToOrdinaryAlgorithm()
    {
        var result = Parser.ParseSyntax("Id(x) = x");

        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        var user = Assert.IsType<Algorithm.User>(result.Root.Properties[0].Value);
        Assert.Equal(["x"], user.Params);
        Assert.Single(user.Output);
    }

    [Fact]
    public void Parse_Clause_SequenceValuePattern_ElaboratesToOrdinaryParameterPattern()
    {
        var result = Parser.ParseSyntax("Stats(x, (acc, counter)) = (x + acc, counter + 1)");

        Assert.False(result.HasErrors);
        var user = Assert.IsType<Algorithm.User>(result.Root.Properties[0].Value);
        Assert.Equal(["x", "acc", "counter"], user.Params);
        Assert.Equal(["x", "(acc, counter)"], user.ParameterPatterns.Select(pattern => pattern.DisplayName).ToArray());
    }

    [Fact]
    public void Parse_ClauseGroup_DoubleParenSequenceValuePattern_PreservesOuterSingletonGroup()
    {
        var source = """
            MarkSequenceValueRange((a, b, c)) = 1
            MarkSequenceValueRange(x) = 0
            """;
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Equal(2, cond.Branches.Count);

        var outerGroup = Assert.IsType<Pattern.SequenceValue>(cond.Branches[0].Pattern);
        Assert.Single(outerGroup.Items);
        var innerGroup = Assert.IsType<Pattern.SequenceValue>(outerGroup.Items[0]);
        Assert.Equal(3, innerGroup.Items.Count);
        Assert.IsType<Pattern.Bind>(cond.Branches[1].Pattern);
    }

    [Fact]
    public void Parse_Clause_LiteralPattern_RemainsConditionalAlgorithm()
    {
        var result = Parser.ParseSyntax("F(1) = 100");

        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Single(cond.Branches);
        Assert.IsType<Pattern.LitInt>(cond.Branches[0].Pattern);
    }

    [Fact]
    public void Parse_ClauseGroup_LiteralThenPlainBinder_RemainsConditionalAlgorithm()
    {
        var source = """
            F(0) = 0
            F(x) = 1
            """;
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Equal(2, cond.Branches.Count);
        Assert.IsType<Pattern.LitInt>(cond.Branches[0].Pattern);
        Assert.IsType<Pattern.Bind>(cond.Branches[1].Pattern);
    }

    [Fact]
    public void Parse_Conditional_CollectingBranchPattern_ReportsError()
    {
        var source = """
            F(0) = 0
            F(*values) = values.count
            """;
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d =>
            d.Message.Contains("Collecting bindings are only supported in ordinary explicit parameter lists") &&
            d.Message.Contains("F"));
        Assert.Equal(2, diag.Span.StartLineNumber);
    }

    [Fact]
    public void Parse_Conditional_MultipleBranches()
    {
        var source = """
            F(1) = 100
            F((x)) = 0
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Equal(2, cond.Branches.Count);
    }

    [Fact]
    public void Parse_Clause_RepeatedBinder_ElaboratesToOrdinaryEqualityPattern()
    {
        var result = Parser.ParseSyntax("F(a, a) = a");

        Assert.False(result.HasErrors);
        var user = Assert.IsType<Algorithm.User>(result.Root.Properties[0].Value);
        Assert.Equal(["a", "a"], user.Params);
    }

    [Fact]
    public void Parse_Conditional_MixedWithNormalProperty_ReportsError()
    {
        var source = """
            F = 1
            F((x)) = x
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("already defined"));
    }

    [Fact]
    public void Parse_Conditional_NegativeLiteralPattern()
    {
        var result = Parser.ParseSyntax("F(-1) = 100");
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        var pat = cond.Branches[0].Pattern;
        // Single element pattern: outer parens consumed by algorithm parser,
        // ParsePattern returns the atom directly (no sequence-value wrapper)
        var lit = Assert.IsType<Pattern.LitInt>(pat);
        Assert.Equal(-1m, lit.Value);
    }

    [Fact]
    public void Parse_Conditional_NestedGroupPattern()
    {
        var result = Parser.ParseSyntax("F(a, (b, c)) = a");
        Assert.False(result.HasErrors);
        var user = Assert.IsType<Algorithm.User>(result.Root.Properties[0].Value);
        Assert.Equal(["a", "b", "c"], user.Params);
        Assert.Equal(["a", "(b, c)"], user.ParameterPatterns.Select(pattern => pattern.DisplayName).ToArray());
    }

    // ── Grace rejection in clause-head patterns ─────────────────────────────

    [Fact]
    public void Parse_ClauseHead_PrefixGraceInPattern_ReportsError()
    {
        var result = Parser.ParseSyntax("F(~a, b) = a");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in clause-head patterns"));
    }

    [Fact]
    public void Parse_ClauseHead_PostfixGraceInPattern_ReportsError()
    {
        var result = Parser.ParseSyntax("F(a~, b) = a");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in clause-head patterns"));
    }

    [Fact]
    public void Parse_ClauseHead_GraceInNestedPattern_ReportsError()
    {
        var result = Parser.ParseSyntax("F(a, (~b, c)) = a");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in clause-head patterns"));
    }

    // ── Grace rejection in conditional branch bodies ────────────────────────

    [Fact]
    public void Parse_Conditional_PrefixGraceInBody_ReportsError()
    {
        var result = Parser.ParseSyntax("F(1, x) = ~x");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch bodies"));
    }

    [Fact]
    public void Parse_Conditional_PostfixGraceInBody_ReportsError()
    {
        var result = Parser.ParseSyntax("F(1, x) = x~");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch bodies"));
    }

    [Fact]
    public void Parse_Conditional_GraceInNestedBodyExpr_ReportsError()
    {
        var result = Parser.ParseSyntax("F(1, x) = 1 * ~x");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch bodies"));
    }

    [Fact]
    public void Parse_Conditional_GraceInBody_ErrorSpanPointsToGraceLine()
    {
        var source = """
            F(1, qty) = qty
            F(2, qty) = ~qty
            F(3, qty) = qty
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch bodies"));
        Assert.Equal(2, diag.Span.StartLineNumber);
    }

    [Fact]
    public void Parse_Conditional_PostfixGraceBeforeDot_IsOrdinaryWrittenGrace()
    {
        var result = Parser.ParseSyntax("F(1, a, t) = a~.t");

        Assert.True(result.HasErrors);
        Assert.Single(
            result.Diagnostics,
            diagnostic => diagnostic.Message.Contains("Grace is not allowed in conditional branch bodies"));
        var conditional = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        var branch = Assert.Single(conditional.Branches);
        var edge = Assert.IsType<Expr.DotCall>(Assert.Single(branch.Body.Output));
        Assert.Equal("t", edge.Name);
        var receiverGrace = Assert.IsType<Expr.Grace>(edge.Target);
        Assert.Equal(+1, receiverGrace.Weight);
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(receiverGrace.Inner).Name);
    }

    [Fact]
    public void Parse_Conditional_PrefixGraceOnDotMember_IsOrdinaryWrittenGrace()
    {
        var result = Parser.ParseSyntax("F(1, a, t) = a.~t");

        Assert.True(result.HasErrors);
        Assert.Single(
            result.Diagnostics,
            diagnostic => diagnostic.Message.Contains("Grace is not allowed in conditional branch bodies"));
        var conditional = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        var branch = Assert.Single(conditional.Branches);
        var edge = Assert.IsType<Expr.DotCall>(Assert.Single(branch.Body.Output));
        var memberGrace = Assert.IsType<Expr.Grace>(edge.LexicalFallback);
        Assert.Equal(-1, memberGrace.Weight);
        Assert.Equal("t", Assert.IsType<Expr.Resolve>(memberGrace.Inner).Name);
    }

    [Fact]
    public void Parse_Conditional_RepeatedPostfixGraceBeforeDot_ReportsError()
    {
        var result = Parser.ParseSyntax("F(1, a, t) = a~~.t");

        Assert.True(result.HasErrors);
        Assert.Single(
            result.Diagnostics,
            diagnostic => diagnostic.Message.Contains("Grace is not allowed in conditional branch bodies"));
    }

    // ── Uniform top-level pattern arity validation ──────────────────────────

    [Fact]
    public void Parse_Conditional_SameArity_NestedStructureDiffers_Valid()
    {
        // Both branches have top-level arity 2; nested structure differs
        var source = """
            Else(1, (a, b)) = a
            Else(2, x) = x
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Equal(2, cond.Branches.Count);
    }

    [Fact]
    public void Parse_Conditional_SameArity_FlatBranches_Valid()
    {
        // Both branches have top-level arity 3
        var source = """
            F(1, a, b) = a
            F(2, a, b) = b
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Equal(2, cond.Branches.Count);
    }

    [Fact]
    public void Parse_Conditional_SingleBranch_AlwaysValid()
    {
        // Single branch: no arity conflict possible
        var result = Parser.ParseSyntax("K((x)) = x");
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Parse_Conditional_DifferentArity_ReportsError()
    {
        // First branch arity 2, second branch arity 3
        var source = """
            Expense(1, qty) = qty
            Expense(2, a, qty) = a * qty
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d =>
            d.Message.Contains("same top-level pattern arity") &&
            d.Message.Contains("Expense"));
        // Error span should point to the second branch (line 2)
        Assert.Equal(2, diag.Span.StartLineNumber);
    }

    [Fact]
    public void Parse_Conditional_Arity1vs2_ReportsError()
    {
        // First branch arity 1 (sequence-value singleton), second branch arity 2 (sequence value)
        var source = """
            F((x)) = 1
            F(a, (b)) = a
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d =>
            d.Message.Contains("same top-level pattern arity") &&
            d.Message.Contains("Expected 1") &&
            d.Message.Contains("arity 2"));
        // Error span should point to the second branch (line 2)
        Assert.Equal(2, diag.Span.StartLineNumber);
    }

    [Fact]
    public void Parse_Conditional_ThreeBranches_ThirdMismatches_ReportsError()
    {
        // First two branches arity 2, third branch arity 3
        var source = """
            G(1, x) = x
            G(2, x) = x + 1
            G(3, x, y) = x + y
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d =>
            d.Message.Contains("same top-level pattern arity") &&
            d.Message.Contains("G"));
        // Error span should point to the third branch (line 3)
        Assert.Equal(3, diag.Span.StartLineNumber);
    }

    // ── Uniform top-level output arity validation ─────────────────────────

    [Fact]
    public void Parse_Conditional_SameOutputArity1_Valid()
    {
        // Both branches return top-level output arity 1 — valid
        var source = """
            Expense(1, qty) = qty * 2
            Expense(2, qty) = qty * 3
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Parse_Conditional_SameOutputArity2_Valid()
    {
        // Both branches return top-level output arity 2 — valid
        var source = """
            F(1, x) = x, x + 1
            F(2, x) = 0, x
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Parse_Conditional_SameOutputArity_NestedDiffers_Valid()
    {
        // Both branches return top-level output arity 2;
        // nested internal output structure differs — valid
        var source = """
            G(1, x) = x, (x + 1, x + 2)
            G(2, x) = x, x * 2
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Parse_Conditional_SingleBranch_OutputArity_AlwaysValid()
    {
        // Single branch: no output arity conflict possible
        var result = Parser.ParseSyntax("F((x)) = x, x + 1");
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Parse_OrdinarySequenceValueParameterBody_PreservedAsSingleValue()
    {
        var source = """
            Stats(x, (acc, counter)) = (x + acc, counter + 1)
            """;
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var user = Assert.IsType<Algorithm.User>(result.Root.Properties[0].Value);
        var body = user;
        Assert.Single(body.Output);
        var capture = Assert.IsType<Expr.Capture>(body.Output[0]);
        Assert.Equal(2, capture.Body.Count);
    }

    [Fact]
    public void Parse_Conditional_DifferentOutputArity_ReportsError()
    {
        // First branch output arity 2, second branch output arity 1
        var source = """
            Expense(1, qty) = qty * 2, 2
            Expense(2, qty) = qty * 3
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d =>
            d.Message.Contains("same top-level output arity") &&
            d.Message.Contains("Expense"));
        // Error span should point to the second branch (line 2)
        Assert.Equal(2, diag.Span.StartLineNumber);
    }

    [Fact]
    public void Parse_Conditional_OutputArity1vs2_ReportsError()
    {
        // First branch output arity 1, second branch output arity 2
        var source = """
            F(1, x) = x
            F(2, x) = x, x + 1
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d =>
            d.Message.Contains("same top-level output arity") &&
            d.Message.Contains("Expected 1") &&
            d.Message.Contains("output arity 2"));
        // Error span should point to the second branch (line 2)
        Assert.Equal(2, diag.Span.StartLineNumber);
    }

    [Fact]
    public void Parse_Conditional_ThreeBranches_ThirdOutputMismatches_ReportsError()
    {
        // First two branches output arity 1, third branch output arity 2
        var source = """
            G(1, x) = x
            G(2, x) = x + 1
            G(3, x) = x, x + 1
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d =>
            d.Message.Contains("same top-level output arity") &&
            d.Message.Contains("G"));
        // Error span should point to the third branch (line 3)
        Assert.Equal(3, diag.Span.StartLineNumber);
    }

    // ── Old `when` syntax no longer recognized ─────────────────────────────

    [Fact]
    public void Parse_Conditional_WhenSyntax_NotRecognized()
    {
        // Old `when` syntax no longer exists. `when` is now a regular identifier.
        // `F when (1) = 100` parses as: F (output), then when(1)=100 (conditional branch named "when").
        // This is semantically different from the old meaning but NOT a parse error.
        var source = """
            F when (1) = 100
            F when ((x)) = 0
            """;
        var result = Parser.ParseSyntax(source);
        // F is output, when(1)=100 and when(x)=0 are branches of conditional "when"
        Assert.False(result.HasErrors);
        // The old name-based conditional algorithm "F" does NOT exist
        Assert.DoesNotContain(result.Root.Properties, p => p.Name == "F");
        // Instead, "when" is the conditional algorithm name
        Assert.Contains(result.Root.Properties, p => p.Name == "when");
    }

    [Fact]
    public void Parse_Conditional_WhenSyntax_SingleBranch_NotRecognized()
    {
        // K when ((a, b)) = a → parses as K (output), when((a,b))=a (conditional branch named "when")
        var result = Parser.ParseSyntax("K when ((a, b)) = a");
        Assert.False(result.HasErrors);
        Assert.Contains(result.Root.Properties, p => p.Name == "when");
        Assert.Single(result.Root.Output); // K is output
    }

    // ── Disambiguation and edge cases ──────────────────────────────────────

    [Fact]
    public void Parse_Conditional_DefinitionVsCall_Disambiguated()
    {
        // First two lines are definitions (followed by =), last line is a call (no =)
        var source = """
            F(1) = 100
            F((x)) = 0
            F(1)
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        // One property (conditional) + one output expression (the call)
        Assert.Single(result.Root.Properties);
        Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Single(result.Root.Output);
    }

    [Fact]
    public void Parse_Conditional_CallInBodyRemainsCall()
    {
        // F(x) in the body of G is a call, not a branch definition
        var source = """
            F(1) = 100
            F((x)) = 0
            G = F(1)
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Properties.Count);
        // G is a regular property (added first), F is conditional (added after loop)
        var gProp = result.Root.Properties.Single(p => p.Name == "G");
        var fProp = result.Root.Properties.Single(p => p.Name == "F");
        Assert.IsType<Algorithm.Conditional>(fProp.Value);
        // G's body should be a User algorithm, not Conditional
        Assert.IsType<Algorithm.User>(gProp.Value);
    }

    [Fact]
    public void Parse_PublicClause_SetsIsPublicOnOrdinarySingleClause()
    {
        var result = Parser.ParseSyntax("public F(x) = x");

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(diagnostic => diagnostic.Message)));
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("F", property.Name);
        Assert.True(property.IsPublic);
        var user = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal(["x"], user.Params);
    }

    [Fact]
    public void Parse_PublicClause_SetsIsPublicOnSingleBranchConditional()
    {
        var result = Parser.ParseSyntax("public F(0) = 1");

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(diagnostic => diagnostic.Message)));
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("F", property.Name);
        Assert.True(property.IsPublic);
        Assert.IsType<Algorithm.Conditional>(property.Value);
    }

    [Fact]
    public void Parse_PublicClause_MarksWholeClauseFamilyPublic()
    {
        var source = """
            public F(0) = 0
            public F(x) = 1
            """;

        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(diagnostic => diagnostic.Message)));
        var property = Assert.Single(result.Root.Properties);
        Assert.Equal("F", property.Name);
        Assert.True(property.IsPublic);
        var conditional = Assert.IsType<Algorithm.Conditional>(property.Value);
        Assert.Equal(2, conditional.Branches.Count);
        Assert.Equal(2, property.DeclarationSpans.Count);
    }

    [Theory]
    [InlineData("F(0) = 0\npublic F(x) = 1")]
    [InlineData("public F(0) = 0\nF(x) = 1")]
    public void Parse_PublicClause_MixedVisibilityInClauseFamilyReportsError(string source)
    {
        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("All clauses of 'F' must use the same public modifier"));
    }

    // ── Property redefinition detection ────────────────────────────────────────

    [Fact]
    public void Parse_DuplicateProperty_ReportsError()
    {
        var source = """
            A = 5
            A = 6
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Property 'A' is already defined"));
    }

    [Fact]
    public void Parse_DuplicateProperty_WithImplicitParams_ReportsError()
    {
        var source = """
            B = x + 1
            B = x + 2
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Property 'B' is already defined"));
    }

    [Fact]
    public void Parse_DuplicatePublicProperty_ReportsError()
    {
        var source = """
            public A = 5
            public A = 6
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Property 'A' is already defined"));
    }

    [Fact]
    public void Parse_DuplicateProperty_MixedVisibility_ReportsError()
    {
        var source = """
            A = 5
            public A = 6
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Property 'A' is already defined"));
    }

    [Fact]
    public void Parse_DuplicateProperty_PublicThenPrivate_ReportsError()
    {
        var source = """
            public A = 5
            A = 6
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Property 'A' is already defined"));
    }

    [Fact]
    public void Parse_DuplicateConditionalBranchPattern_LitInt_ReportsError()
    {
        var source = """
            F(1) = 100
            F(1) = 200
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d => d.Message.Contains("Duplicate branch pattern"));
        Assert.Equal(2, diag.Span.StartLineNumber);
        Assert.Equal(1, diag.Span.StartColumn);
        Assert.Equal(2, diag.Span.EndLineNumber);
    }

    [Fact]
    public void Parse_DuplicateConditionalBranchPattern_Bind_ReportsError()
    {
        var source = """
            F((x)) = x + 1
            F((x)) = x + 2
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d => d.Message.Contains("Duplicate branch pattern"));
        Assert.Equal(2, diag.Span.StartLineNumber);
        Assert.Equal(1, diag.Span.StartColumn);
        Assert.Equal(2, diag.Span.EndLineNumber);
    }

    [Fact]
    public void Parse_Conditional_RepeatedBinderConstraintAndFallback_AreDistinct()
    {
        var source = """
            Equal(x, x) = 1
            Equal(x, y) = 0
            """;

        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var conditional = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Equal(2, conditional.Branches.Count);
    }

    [Fact]
    public void Parse_DuplicateConditionalRepeatedBinderPattern_UsesAlphaEquivalence()
    {
        var source = """
            Equal(x, x) = 1
            Equal(a, a) = 0
            """;

        var result = Parser.ParseSyntax(source);

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("Duplicate branch pattern"));
    }

    [Fact]
    public void Parse_DuplicateConditionalBranchPattern_WithFinalCall_SpanPointsToDuplicateBranch()
    {
        var source = """
            F(1) = 10
            F(1) = 20
            F(1)
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d => d.Message.Contains("Duplicate branch pattern"));
        Assert.Equal(2, diag.Span.StartLineNumber);
        Assert.Equal(1, diag.Span.StartColumn);
        Assert.Equal(2, diag.Span.EndLineNumber);
    }

    [Fact]
    public void Parse_ConditionalBranchPattern_DifferentLiterals_IsValid()
    {
        var source = """
            F(1) = 100
            F(2) = 200
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Parse_ConditionalBranchPattern_LitAndBind_IsValid()
    {
        var source = """
            F(1) = 100
            F((x)) = 0
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Parse_DistinctProperties_NoError()
    {
        var source = """
            A = 5
            B = 6
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
    }

    // ── String literal pattern tests ────────────────────────────────────────

    [Fact]
    public void Parse_StringLiteralPattern_InConditionalBranch()
    {
        var source = """
            Price('apples') = 0.80
            Price('tomatoes') = 1.20
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(
            result.Root.Properties.Single(p => p.Name == "Price").Value);
        Assert.Equal(2, cond.Branches.Count);
        Assert.IsType<Pattern.LitString>(cond.Branches[0].Pattern);
        Assert.Equal("apples", ((Pattern.LitString)cond.Branches[0].Pattern).Value);
    }

    [Fact]
    public void Parse_StringLiteralExpression_Standalone()
    {
        var source = "'hello'";
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        var output = result.Root.Output;
        Assert.Single(output);
        Assert.IsType<Expr.StringLiteral>(output[0]);
        Assert.Equal("hello", ((Expr.StringLiteral)output[0]).Value);
    }

    [Fact]
    public void Parse_UnterminatedString_ProducesError()
    {
        var source = "'hello";
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
    }

    [Fact]
    public void Parse_DuplicateStringPatterns_ProducesError()
    {
        var source = """
            F('a') = 1
            F('a') = 2
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
    }
}
