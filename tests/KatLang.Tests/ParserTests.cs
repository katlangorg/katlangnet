namespace KatLang.Tests;

public class ParserTests
{
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
    public void Parse_DotAccess_ReturnsDotCallExpr()
    {
        var result = Parser.ParseSyntax("X.length");

        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("length", dotCall.Name);
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
        Assert.Equal(2, call.Args.Output.Count);
    }

    [Fact]
    public void Parse_CallWithBraces_WrapsInBlock()
    {
        // F{x + 1} desugars to F({x + 1}) — the brace content becomes an
        // Expr.Block inside a non-parametrized outer args algorithm.
        var result = Parser.ParseSyntax("F{x + 1}");

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.False(call.Args.IsParametrized);
        var block = Assert.IsType<Expr.Block>(call.Args.Output[0]);
        Assert.True(block.Algorithm.IsParametrized);
    }

    [Fact]
    public void Parse_CallWithParens_NotParametrized()
    {
        var result = Parser.ParseSyntax("F(1)");

        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.False(call.Args.IsParametrized);
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
        Assert.Equal(2, dotCall.Args!.Output.Count);
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
        Assert.Equal(1, dotCall.Args!.Output.Count);
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
        var block = Assert.IsType<Expr.Block>(result.Root.Output[0]);
        Assert.True(block.Algorithm.IsParametrized);
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
    public void Parse_InlineBlock_ReturnsBlockExpr()
    {
        var result = Parser.ParseSyntax("(1, 2)");

        Assert.False(result.HasErrors);
        var block = Assert.IsType<Expr.Block>(result.Root.Output[0]);
        Assert.Equal(2, block.Algorithm.Output.Count);
    }

    [Fact]
    public void Parse_Semicolon_ReturnsCombineExpr()
    {
        var result = Parser.ParseSyntax("A; B");

        Assert.False(result.HasErrors);
        var combine = Assert.IsType<Expr.Combine>(result.Root.Output[0]);
        Assert.IsType<Expr.Resolve>(combine.Left);
        Assert.IsType<Expr.Resolve>(combine.Right);
    }

    [Fact]
    public void Parse_Semicolon_ChainedCombine()
    {
        // 1 + 2; 3 + 4; 5 + 6 → Combine(Combine(1+2, 3+4), 5+6) left-assoc
        var result = Parser.ParseSyntax("1 + 2; 3 + 4; 5 + 6");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Output); // one combine item in output
        var outer = Assert.IsType<Expr.Combine>(result.Root.Output[0]);
        var inner = Assert.IsType<Expr.Combine>(outer.Left);
        Assert.IsType<Expr.Binary>(inner.Left);
        Assert.IsType<Expr.Binary>(inner.Right);
        Assert.IsType<Expr.Binary>(outer.Right);
    }

    [Fact]
    public void Parse_CommaAndSemicolon_CorrectStructure()
    {
        // 1, 2; 3 → output list has two items: [Num(1), Combine(Num(2), Num(3))]
        var result = Parser.ParseSyntax("1, 2; 3");
        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Output.Count);
        Assert.IsType<Expr.Num>(result.Root.Output[0]);
        var combine = Assert.IsType<Expr.Combine>(result.Root.Output[1]);
    }

    [Fact]
    public void Parse_PropertyDetectionWithSemicolon()
    {
        // A = 1; 2 B = 3 → two properties, A has output [Combine(1, 2)]
        var result = Parser.ParseSyntax("A = 1; 2 B = 3");
        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Properties.Count);
    }

    [Fact]
    public void Parse_ArithmeticGroupingUnchanged()
    {
        // 1 + (2 * 3) → Binary with paren grouping
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
        var source = """
            1 // comment
            + 2
            """;
        var result = Parser.ParseSyntax(source);

        Assert.False(result.HasErrors);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Add, binary.Op);
    }

    [Fact]
    public void Parse_RootAlgorithm_IsParametrized()
    {
        var result = Parser.ParseSyntax("x + 1");
        Assert.True(result.Root.IsParametrized);
    }

    [Fact]
    public void Parse_PropertyBody_IsParametrized()
    {
        var result = Parser.ParseSyntax("X = x + 1");
        Assert.True(result.Root.Properties[0].Value.IsParametrized);
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
    public void Parse_CommentDoesNotConflictWithSlash()
    {
        // // is comment, / is division
        var result = Parser.ParseSyntax("10 / 2 // this is a comment");
        Assert.False(result.HasErrors);
        var div = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Div, div.Op);
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
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Expected identifier after '~'"));
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
        var result = Parser.ParseSyntax("open Lib2, Lib3\nLib2 = (public Val2 = 20)\nLib3 = (public Val3 = 30)\nVal3");
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
        var result = Parser.ParseSyntax("open Lib2\nLib2 = (public Val2 = 20)\nVal2");
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
        var result = Parser.ParseSyntax("open F(1,2), Lib3\nF = (X = 1)\nLib3 = (Y = 2)\nY");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Invalid open form") && d.Message.Contains("call"));
    }

    // -- Open DotCall normalization tests -------------------------------------

    [Fact]
    public void Parse_Open_DotPath_NormalizesToDotCall()
    {
        // open Lib.Sub -> parser produces DotCall(Resolve("Lib"), "Sub", null)
        var result = Parser.ParseSyntax("open Lib.Sub\nLib = (public Sub = (public X = 1))\nX");
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
        var result = Parser.ParseSyntax("open Lib.Sub()\nLib = (public Sub = (public X = 1))\nX");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("not allowed in open"));
    }

    [Fact]
    public void Parse_Open_NestedDotPath_NormalizesToNestedDotCall()
    {
        // open A.B.C -> DotCall(DotCall(Resolve("A"), "B", null), "C", null)
        var result = Parser.ParseSyntax("open A.B.C\nA = (public B = (public C = (public X = 1)))\nX");
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
        Assert.Single(call.Args.Output);
        var strLit = Assert.IsType<Expr.StringLiteral>(call.Args.Output[0]);
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

    // ── Explicit output syntax ──────────────────────────────────────────────

    [Fact]
    public void Parse_ExplicitOutput_BasicForm()
    {
        var result = Parser.ParseSyntax("A = 6\nOutput = A");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        Assert.Equal("A", result.Root.Properties[0].Name);
        Assert.Single(result.Root.Output);
        Assert.IsType<Expr.Resolve>(result.Root.Output[0]);
        Assert.Equal("A", ((Expr.Resolve)result.Root.Output[0]).Name);
    }

    [Fact]
    public void Parse_ExplicitOutput_NotAProperty()
    {
        // Output = expr must NOT create a property named "Output"
        var result = Parser.ParseSyntax("Output = 42");
        Assert.False(result.HasErrors);
        Assert.Empty(result.Root.Properties);
        Assert.Single(result.Root.Output);
        Assert.IsType<Expr.Num>(result.Root.Output[0]);
    }

    [Fact]
    public void Parse_ExplicitOutput_Expression()
    {
        var result = Parser.ParseSyntax("A = 1\nOutput = A + 1");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        Assert.Single(result.Root.Output);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Add, binary.Op);
    }

    [Fact]
    public void Parse_ExplicitOutput_InMiddleOfProperties()
    {
        var result = Parser.ParseSyntax("A = 1\nOutput = A + 1\nB = 2");
        Assert.False(result.HasErrors);
        Assert.Equal(2, result.Root.Properties.Count);
        Assert.Equal("A", result.Root.Properties[0].Name);
        Assert.Equal("B", result.Root.Properties[1].Name);
        Assert.Single(result.Root.Output);
        var binary = Assert.IsType<Expr.Binary>(result.Root.Output[0]);
        Assert.Equal(BinaryOp.Add, binary.Op);
    }

    [Fact]
    public void Parse_ExplicitOutput_MultipleValues()
    {
        var result = Parser.ParseSyntax("Output = 1, 2, 3");
        Assert.False(result.HasErrors);
        Assert.Equal(3, result.Root.Output.Count);
    }

    [Fact]
    public void Parse_ExplicitOutput_DuplicateReportsError()
    {
        var result = Parser.ParseSyntax("Output = 1\nOutput = 2");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("output may be defined only once"));
    }

    [Fact]
    public void Parse_ExplicitAndImplicitOutput_ReportsError()
    {
        var result = Parser.ParseSyntax("A = 1\nOutput = A\nA");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Cannot use both"));
    }

    [Fact]
    public void Parse_ImplicitThenExplicitOutput_ReportsError()
    {
        var result = Parser.ParseSyntax("A = 1\nA\nOutput = A");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Cannot use both"));
    }

    [Fact]
    public void Parse_PublicOutput_ReportsError()
    {
        var result = Parser.ParseSyntax("public Output = 42");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("'public' cannot be applied to output"));
    }

    [Fact]
    public void Parse_ExplicitOutput_ImplicitOutputSameAST()
    {
        // Both forms should produce equivalent Output lists
        var implicit_ = Parser.ParseSyntax("A = 6\nA");
        var explicit_ = Parser.ParseSyntax("A = 6\nOutput = A");

        Assert.False(implicit_.HasErrors);
        Assert.False(explicit_.HasErrors);

        Assert.Single(implicit_.Root.Output);
        Assert.Single(explicit_.Root.Output);

        // Both should be Resolve("A")
        var implicitOut = Assert.IsType<Expr.Resolve>(implicit_.Root.Output[0]);
        var explicitOut = Assert.IsType<Expr.Resolve>(explicit_.Root.Output[0]);
        Assert.Equal(implicitOut.Name, explicitOut.Name);
    }

    [Fact]
    public void Parse_ExplicitOutput_InsideBlock()
    {
        var result = Parser.ParseSyntax("X = {A = 1\nOutput = A + 1\nB = 2}");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        var block = result.Root.Properties[0].Value;
        Assert.Equal(2, block.Properties.Count);
        Assert.Single(block.Output);
    }

    // -- Double-parens removal: ordinary grouping ---

    [Fact]
    public void Parse_ParenSubExpr_FirstCallArg_ParsesNormally()
    {
        // f((a + b) mod 2, c) must parse without error now that
        // double-parens detection is removed
        var result = Parser.ParseSyntax("F((a + b) mod 2, c)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(2, call.Args.Output.Count);
        // First arg should be binary mod expression
        var modExpr = Assert.IsType<Expr.Binary>(call.Args.Output[0]);
        Assert.Equal(BinaryOp.Mod, modExpr.Op);
    }

    [Fact]
    public void Parse_If_ParenSubExpr_FirstArg_ParsesNormally()
    {
        var result = Parser.ParseSyntax("if((a + b) mod 2 == 0, 1, 0)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(3, call.Args.Output.Count);
    }

    [Fact]
    public void Parse_DoubleParens_RemainsOrdinaryGrouping()
    {
        // X = ((1 + 2)) is ordinary nested grouping
        var result = Parser.ParseSyntax("X = ((1 + 2))");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        // The inner (1 + 2) is just grouping, outer layer is also grouping
        var output = result.Root.Properties[0].Value.Output;
        Assert.Single(output);
        var binary = Assert.IsType<Expr.Binary>(output[0]);
        Assert.Equal(BinaryOp.Add, binary.Op);
    }

    // -- Direct-call lowering for while/repeat ---

    [Fact]
    public void Parse_While_DirectCall_MultiInit_ProducesBlock()
    {
        // while(Step, x, 0) should lower to while(Step, block([x, 0]))
        var result = Parser.ParseSyntax("while(Step, x, 0)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(2, call.Args.Output.Count);
        // Second arg should be a Block wrapping [x, 0]
        var block = Assert.IsType<Expr.Block>(call.Args.Output[1]);
        Assert.Equal(2, block.Algorithm.Output.Count);
    }

    [Fact]
    public void Parse_While_DirectCall_TwoArgs_NoLowering()
    {
        // while(Step, init) stays with 2 args, no lowering
        var result = Parser.ParseSyntax("while(Step, init)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(2, call.Args.Output.Count);
        Assert.IsType<Expr.Resolve>(call.Args.Output[1]);
    }

    [Fact]
    public void Parse_Repeat_DirectCall_MultiInit_ProducesBlock()
    {
        // repeat(Step, n, x, 0) should lower to repeat(Step, n, block([x, 0]))
        var result = Parser.ParseSyntax("repeat(Step, n, x, 0)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(3, call.Args.Output.Count);
        var block = Assert.IsType<Expr.Block>(call.Args.Output[2]);
        Assert.Equal(2, block.Algorithm.Output.Count);
    }

    [Fact]
    public void Parse_Repeat_DirectCall_ThreeArgs_NoLowering()
    {
        // repeat(Step, n, init) stays with 3 args, no lowering
        var result = Parser.ParseSyntax("repeat(Step, n, init)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(3, call.Args.Output.Count);
        Assert.IsType<Expr.Resolve>(call.Args.Output[2]);
    }

    [Fact]
    public void Parse_DotCall_While_NoLowering_InParser()
    {
        // Step.while(x, 0) should NOT be lowered in the parser
        // (lowering happens in the evaluator after structural property check)
        var result = Parser.ParseSyntax("Step.while(x, 0)");
        Assert.False(result.HasErrors);
        var dotCall = Assert.IsType<Expr.DotCall>(result.Root.Output[0]);
        Assert.Equal("while", dotCall.Name);
        Assert.NotNull(dotCall.Args);
        Assert.Equal(2, dotCall.Args!.Output.Count);
    }

    // ── if arity validation ─────────────────────────────────────────────────

    [Fact]
    public void Parse_If_TwoArgs_RemainsIf()
    {
        var result = Parser.ParseSyntax("if(1, 2)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        var resolve = Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("if", resolve.Name);
        Assert.Equal(2, call.Args.Output.Count);
    }

    [Fact]
    public void Parse_If_ThreeArgs_RemainsIf()
    {
        var result = Parser.ParseSyntax("if(1, 2, 3)");
        Assert.False(result.HasErrors);
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        var resolve = Assert.IsType<Expr.Resolve>(call.Function);
        Assert.Equal("if", resolve.Name);
        Assert.Equal(3, call.Args.Output.Count);
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

    // ── Conditional algorithm parsing ───────────────────────────────────────

    [Fact]
    public void Parse_Conditional_SingleBranch()
    {
        var result = Parser.ParseSyntax("K when (a, b) = a");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Properties);
        var prop = result.Root.Properties[0];
        Assert.Equal("K", prop.Name);
        Assert.IsType<Algorithm.Conditional>(prop.Value);
        var cond = (Algorithm.Conditional)prop.Value;
        Assert.Single(cond.Branches);
        Assert.IsType<Pattern.Group>(cond.Branches[0].Pattern);
    }

    [Fact]
    public void Parse_Conditional_MultipleBranches()
    {
        var source = """
            F when (1) = 100
            F when (x) = 0
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Equal(2, cond.Branches.Count);
    }

    [Fact]
    public void Parse_Conditional_DuplicateBinder_ReportsError()
    {
        var result = Parser.ParseSyntax("F when (a, a) = a");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Duplicate binder"));
    }

    [Fact]
    public void Parse_Conditional_MixedWithNormalProperty_ReportsError()
    {
        var source = """
            F = 1
            F when (x) = x
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Cannot mix"));
    }

    [Fact]
    public void Parse_Conditional_NegativeLiteralPattern()
    {
        var result = Parser.ParseSyntax("F when (-1) = 100");
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        var pat = cond.Branches[0].Pattern;
        // Single element pattern: outer parens consumed by algorithm parser,
        // ParsePattern returns the atom directly (no group wrapper)
        var lit = Assert.IsType<Pattern.LitInt>(pat);
        Assert.Equal(-1m, lit.Value);
    }

    [Fact]
    public void Parse_Conditional_NestedGroupPattern()
    {
        var result = Parser.ParseSyntax("F when (a, (b, c)) = a");
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        var topGroup = Assert.IsType<Pattern.Group>(cond.Branches[0].Pattern);
        Assert.Equal(2, topGroup.Items.Count);
        Assert.IsType<Pattern.Bind>(topGroup.Items[0]);
        Assert.IsType<Pattern.Group>(topGroup.Items[1]);
    }

    // ── Grace rejection in conditional branch patterns ──────────────────────

    [Fact]
    public void Parse_Conditional_PrefixGraceInPattern_ReportsError()
    {
        var result = Parser.ParseSyntax("F when (~a, b) = a");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch patterns"));
    }

    [Fact]
    public void Parse_Conditional_PostfixGraceInPattern_ReportsError()
    {
        var result = Parser.ParseSyntax("F when (a~, b) = a");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch patterns"));
    }

    [Fact]
    public void Parse_Conditional_GraceInNestedPattern_ReportsError()
    {
        var result = Parser.ParseSyntax("F when (a, (~b, c)) = a");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch patterns"));
    }

    // ── Grace rejection in conditional branch bodies ────────────────────────

    [Fact]
    public void Parse_Conditional_PrefixGraceInBody_ReportsError()
    {
        var result = Parser.ParseSyntax("F when (a, b) = ~a + b");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch bodies"));
    }

    [Fact]
    public void Parse_Conditional_PostfixGraceInBody_ReportsError()
    {
        var result = Parser.ParseSyntax("F when (a, b) = a~ + b");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch bodies"));
    }

    [Fact]
    public void Parse_Conditional_GraceInNestedBodyExpr_ReportsError()
    {
        var result = Parser.ParseSyntax("F when (a, b) = a * ~b");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch bodies"));
    }

    [Fact]
    public void Parse_Conditional_GraceInBody_ErrorSpanPointsToGraceLine()
    {
        var source = """
            F when (1, qty) = qty
            F when (2, qty) = ~qty
            F when (3, qty) = qty
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch bodies"));
        Assert.Equal(2, diag.Span.StartLineNumber);
    }

    // ── Uniform top-level pattern arity validation ──────────────────────────

    [Fact]
    public void Parse_Conditional_SameArity_NestedStructureDiffers_Valid()
    {
        // Both branches have top-level arity 2; nested structure differs
        var source = """
            Else when (1, (a, b)) = a
            Else when (2, x) = x
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
            F when (1, a, b) = a
            F when (2, a, b) = b
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
        var result = Parser.ParseSyntax("K when (a, b) = a");
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Parse_Conditional_DifferentArity_ReportsError()
    {
        // First branch arity 2, second branch arity 3
        var source = """
            Expense when (1, qty) = qty
            Expense when (2, a, qty) = a * qty
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
        // First branch arity 1 (bare bind), second branch arity 2 (group)
        var source = """
            F when (x) = 1
            F when (a, b) = a
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
            G when (1, x) = x
            G when (2, x) = x + 1
            G when (3, x, y) = x + y
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
            Expense when (1, qty) = qty * 2
            Expense when (2, qty) = qty * 3
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Parse_Conditional_SameOutputArity2_Valid()
    {
        // Both branches return top-level output arity 2 — valid
        var source = """
            F when (1, x) = x, x + 1
            F when (2, x) = 0, x
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
            G when (1, x) = x, (x + 1, x + 2)
            G when (2, x) = x, x * 2
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Parse_Conditional_SingleBranch_OutputArity_AlwaysValid()
    {
        // Single branch: no output arity conflict possible
        var result = Parser.ParseSyntax("F when (x) = x, x + 1");
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Parse_Conditional_DifferentOutputArity_ReportsError()
    {
        // First branch output arity 2, second branch output arity 1
        var source = """
            Expense when (1, qty) = qty * 2, 2
            Expense when (2, qty) = qty * 3
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
            F when (1, x) = x
            F when (2, x) = x, x + 1
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
            G when (1, x) = x
            G when (2, x) = x + 1
            G when (3, x) = x, x + 1
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        var diag = Assert.Single(result.Diagnostics, d =>
            d.Message.Contains("same top-level output arity") &&
            d.Message.Contains("G"));
        // Error span should point to the third branch (line 3)
        Assert.Equal(3, diag.Span.StartLineNumber);
    }

    // ── Conditional branch sugar: Name(pattern) = body ─────────────────────

    [Fact]
    public void Parse_ConditionalSugar_SingleBranch()
    {
        var result = Parser.ParseSyntax("K(a, b) = a");
        Assert.False(result.HasErrors);
        var prop = Assert.Single(result.Root.Properties);
        Assert.Equal("K", prop.Name);
        var cond = Assert.IsType<Algorithm.Conditional>(prop.Value);
        Assert.Single(cond.Branches);
        Assert.IsType<Pattern.Group>(cond.Branches[0].Pattern);
    }

    [Fact]
    public void Parse_ConditionalSugar_MultipleBranches()
    {
        var source = """
            F(1) = 100
            F(x) = 0
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Equal(2, cond.Branches.Count);
    }

    [Fact]
    public void Parse_ConditionalSugar_NestedGroupPattern()
    {
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Equal(2, cond.Branches.Count);
        // First branch pattern: group[litInt(1), group[bind(a), bind(b)]]
        var pattern0 = Assert.IsType<Pattern.Group>(cond.Branches[0].Pattern);
        Assert.Equal(2, pattern0.Items.Count);
    }

    [Fact]
    public void Parse_ConditionalSugar_NegativeLiteralPattern()
    {
        var result = Parser.ParseSyntax("G(-1) = 100");
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        var lit = Assert.IsType<Pattern.LitInt>(cond.Branches[0].Pattern);
        Assert.Equal(-1m, lit.Value);
    }

    [Fact]
    public void Parse_ConditionalSugar_MixedWithExplicitWhen()
    {
        // Mix both syntax forms within the same conditional algorithm
        var source = """
            F when (1) = 100
            F(x) = 0
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Equal(2, cond.Branches.Count);
    }

    [Fact]
    public void Parse_ConditionalSugar_MixedWithExplicitWhen_Reversed()
    {
        // Sugar first, then explicit when
        var source = """
            F(1) = 100
            F when (x) = 0
            """;
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors);
        var cond = Assert.IsType<Algorithm.Conditional>(result.Root.Properties[0].Value);
        Assert.Equal(2, cond.Branches.Count);
    }

    [Fact]
    public void Parse_ConditionalSugar_DuplicateBinder_ReportsError()
    {
        var result = Parser.ParseSyntax("F(a, a) = a");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Duplicate binder"));
    }

    [Fact]
    public void Parse_ConditionalSugar_GraceInPattern_ReportsError()
    {
        var result = Parser.ParseSyntax("F(~a, b) = a");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch patterns"));
    }

    [Fact]
    public void Parse_ConditionalSugar_GraceInBody_ReportsError()
    {
        var result = Parser.ParseSyntax("F(a) = ~a");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Grace is not allowed in conditional branch bodies"));
    }

    [Fact]
    public void Parse_ConditionalSugar_MixedWithNormalProperty_ReportsError()
    {
        var source = """
            F = 10
            F(x) = 0
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("Cannot mix"));
    }

    [Fact]
    public void Parse_ConditionalSugar_InputArityMismatch_ReportsError()
    {
        var source = """
            F(1, a) = a
            F(2, a, b) = b
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("same top-level pattern arity"));
    }

    [Fact]
    public void Parse_ConditionalSugar_OutputArityMismatch_ReportsError()
    {
        var source = """
            F(1, a) = a, 1
            F(2, a) = a
            """;
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("same top-level output arity"));
    }

    [Fact]
    public void Parse_ConditionalSugar_PublicRejected()
    {
        var source = "public F(x) = x";
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Message.Contains("'public' cannot be applied to conditional algorithm branches"));
    }

    [Fact]
    public void Parse_ConditionalSugar_DefinitionVsCall_Disambiguated()
    {
        // First two lines are definitions (followed by =), last line is a call (no =)
        var source = """
            F(1) = 100
            F(x) = 0
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
    public void Parse_ConditionalSugar_CallInBodyRemainsCall()
    {
        // F(x) in the body of G is a call, not a branch definition
        var source = """
            F when (1) = 100
            F when (x) = 0
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
}
