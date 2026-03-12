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
    public void Parse_Open_DotPath_NormalizesToProp()
    {
        // open Lib.Sub -> parser produces Prop(Resolve("Lib"), "Sub"), NOT DotCall
        var result = Parser.ParseSyntax("open Lib.Sub\nLib = (public Sub = (public X = 1))\nX");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Opens);
        var prop = Assert.IsType<Expr.Prop>(result.Root.Opens[0]);
        Assert.Equal("Sub", prop.Name);
        Assert.IsType<Expr.Resolve>(prop.Target);
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
    public void Parse_Open_NestedDotPath_NormalizesToNestedProp()
    {
        // open A.B.C -> Prop(Prop(Resolve("A"), "B"), "C")
        var result = Parser.ParseSyntax("open A.B.C\nA = (public B = (public C = (public X = 1)))\nX");
        Assert.False(result.HasErrors);
        Assert.Single(result.Root.Opens);
        var outer = Assert.IsType<Expr.Prop>(result.Root.Opens[0]);
        Assert.Equal("C", outer.Name);
        var inner = Assert.IsType<Expr.Prop>(outer.Target);
        Assert.Equal("B", inner.Name);
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
        var prop = Assert.IsType<Expr.Prop>(result.Root.Opens[0]);
        Assert.Equal("Sub", prop.Name);
        Assert.IsType<Expr.Resolve>(prop.Target);
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
        Assert.IsType<Expr.Prop>(result.Root.Opens[2]);
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
}
