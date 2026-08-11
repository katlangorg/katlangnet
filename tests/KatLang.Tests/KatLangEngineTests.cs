namespace KatLang.Tests;

public class KatLangEngineTests
{
    private static Func<string, string> MockDownloader(Dictionary<string, string> files)
    {
        return url =>
        {
            if (files.TryGetValue(url, out var content))
                return content;

            var trimmed = url.TrimEnd('/');
            if (files.TryGetValue(trimmed, out content))
                return content;

            throw new Exception($"404: {url}");
        };
    }

    private static string Lines(params string[] lines)
        => string.Join(Environment.NewLine, lines);

    // ── Run ──────────────────────────────────────────────────────────────────

    [Fact]
    public void Run_SimpleExpression_ReturnsSuccess()
    {
        var result = KatLangEngine.Run("2 + 3");
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([5m], success.Atoms);
        Assert.NotNull(success.Root);
        Assert.NotNull(success.Value);
    }

    [Fact]
    public void Run_MultipleOutputs_ReturnsAllAtoms()
    {
        var result = KatLangEngine.Run("1, 2, 3");
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([1m, 2m, 3m], success.Atoms);
    }

    [Fact]
    public void Run_PropertyOnlyProgram_ReturnsNoProgramOutput()
    {
        var result = KatLangEngine.Run("T = 4");

        var noOutput = Assert.IsType<RunResult.NoProgramOutput>(result);
        Assert.NotNull(noOutput.Root);
        Assert.Equal(RunResult.NoProgramOutput.DefaultMessage, noOutput.Message);
        Assert.Equal(RunResult.NoProgramOutput.DefaultMessage, noOutput.ToDisplayString());
    }

    [Fact]
    public void Run_MultiplePropertyDefinitionsWithoutOutput_ReturnsNoProgramOutput()
    {
        var result = KatLangEngine.Run(
            """
            Price = 10
            Tax = 2
            Total = Price + Tax
            """);

        Assert.IsType<RunResult.NoProgramOutput>(result);
    }

    [Fact]
    public void Run_PropertyOnlyProgram_WithTrailingOutput_ReturnsSuccess()
    {
        var result = KatLangEngine.Run("T = 4\nT");

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([4m], success.Atoms);
        Assert.Equal("4", success.ToDisplayString());
    }

    [Fact]
    public void Run_EmptySequenceValue_ReturnsEmptySequenceSuccess()
    {
        var result = KatLangEngine.Run("()");

        var success = Assert.IsType<RunResult.Success>(result);
        var group = Assert.IsType<Result.SequenceValue>(success.Value);
        Assert.Empty(group.Items);
        Assert.Empty(success.Atoms);
        Assert.Equal("()", success.ToDisplayString());
    }

    [Fact]
    public void Run_PropertyOnlyProgram_WithEmptySequenceOutput_ReturnsEmptySequenceSuccess()
    {
        var result = KatLangEngine.Run("T = 4\n()");

        var success = Assert.IsType<RunResult.Success>(result);
        var group = Assert.IsType<Result.SequenceValue>(success.Value);
        Assert.Empty(group.Items);
        Assert.Empty(success.Atoms);
    }

    [Fact]
    public void Run_EmptySequenceForms_DisplayCanonically()
    {
        AssertDisplay("()", "()");
        AssertDisplay("x = ()\nx", "()");
        AssertDisplay("(())", "()");
        AssertDisplay("x = (())\nx", "()");
        AssertDisplay("((()))", "()");
    }

    [Fact]
    public void Run_EmptyCollectedListOutputSlot_StaysVisibleUnlessSpread()
    {
        // The empty collected list is the exact list [] and stays a visible slot.
        AssertDisplay("x, *rest = 1\nrest", "[]");
        AssertDisplay("x, *rest = 1\nrest\nx", "[]\n1");
        // Spreading the empty list opens it and contributes zero items.
        AssertDisplay("x, *rest = 1\nrest*\nx", "1");
    }

    [Fact]
    public void Run_EmptyAndNestedEmptySpread_Canonicalize()
    {
        AssertDisplay("1, ()*, 2", "1\n2");
        AssertDisplay("1, (())*, 2", "1\n2");
    }

    [Fact]
    public void Run_LoopStepEmptySequenceOutput_PreservesVisibleStateSlot()
        => AssertDisplay("Step(x) = ()\nStep.repeat(1, 1)", "()");

    [Fact]
    public void Run_IfMultiOutputBranchProperty_DisplaysOneGroupedRow()
    {
        // Issue #130: `if` returns the selected branch as one value boundary, so a
        // multi-output property branch displays as a single grouped sequence row.
        AssertDisplay("X = 1, 2, 3\nif(1, X, X)", "(1, 2, 3)");
        AssertDisplay("X = 1, 2, 3\nif(0, X, X)", "(1, 2, 3)");
        // Explicit spread opens it back into separate rows.
        AssertDisplay("X = 1, 2, 3\nif(1, X, X)*", "1\n2\n3");
    }

    [Fact]
    public void Run_IfSpreadArgument_OpensIntoThreeArguments()
    {
        // Issue #131: explicit spread in call-argument position supplies the value's items
        // into the three `if` argument slots, so `if(X*)` ≡ `if(1, 2, 3)` → 2.
        AssertDisplay("TrueResult = 1, 2, 3\nif(TrueResult*)", "2");
        AssertDisplay("TrueResult = (1, 2, 3)\nif(TrueResult*)", "2");
        AssertDisplay("Pair = 2, 3\nif(1, Pair*)", "2");
        // Direct builtin `if` now matches the user-defined wrapper.
        AssertDisplay("TrueResult = 1, 2, 3\nMyIF(a, b, c) = if(a, b, c)\nMyIF(TrueResult*)", "2");
    }

    [Fact]
    public void Run_IfSpreadArgument_WrongExpandedArity_IsEvalFailureNotParseFailure()
    {
        // The spread now parses; a wrong expanded count surfaces as an evaluation
        // arity error, not a parser arity error.
        var result = KatLangEngine.Run("Two = 1, 2\nif(Two*)");
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Contains(failure.Errors, e => e.Message.Contains("3 arguments"));
    }

    private static void AssertDisplay(string source, string expected)
    {
        var result = KatLangEngine.Run(source);
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(expected, success.ToDisplayString().Replace("\r\n", "\n"));
    }

    [Fact]
    public void Run_ParseError_ReturnsParseFai1ure()
    {
        var result = KatLangEngine.Run("2 +");
        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.NotEmpty(failure.Errors);
        Assert.All(failure.Errors, e => Assert.NotNull(e.Message));
    }

    [Fact]
    public void Run_ParseError_HasSpanInfo()
    {
        var result = KatLangEngine.Run("2 +");
        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.NotNull(error.StartLine);
        Assert.NotNull(error.StartColumn);
    }

    [Fact]
    public void Run_ParseFailure_HasNoRoot()
    {
        var result = KatLangEngine.Run("2 +");
        Assert.IsType<RunResult.ParseFailure>(result);
        // ParseFailure has no Root property — enforced by the type system
    }

    [Fact]
    public void Run_LoadWithoutDownloader_ReturnsParseFailure()
    {
        var result = KatLangEngine.Run("open 'https://katlang.org/demo/lib.kat'\n1");

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.Contains(failure.Errors,
            error => error.Message.Contains("module elaboration is unavailable", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void Run_LoadWithDownloader_ReturnsSuccess()
    {
        var source = "open Lib\npublic Lib = load('https://katlang.org/demo/lib.kat')\nX";
        var options = new RunOptions
        {
            DownloadCode = MockDownloader(new Dictionary<string, string>
            {
                ["https://katlang.org/demo/lib.kat"] = "public X = 7"
            })
        };

        var result = KatLangEngine.Run(source, options);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([7m], success.Atoms);
    }

    [Fact]
    public void Run_LoadedHtml_ReportsLoadSiteAndFollowingEvaluationError()
    {
        var source = """
            A = load('https://katlang.org/libraries2/example.kat')
            A.X
            """;
        var options = new RunOptions
        {
            DownloadCode = _ => """
                <!doctype html>
                <html>
                  <body>Not found</body>
                </html>
                """
        };

        var result = KatLangEngine.Run(source, options);

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.Collection(
            failure.Errors,
            error =>
            {
                Assert.Contains("cannot load 'https://katlang.org/libraries2/example.kat'", error.Message);
                Assert.Contains("returned HTML", error.Message);
                Assert.Equal(1, error.StartLine);
                Assert.Equal(5, error.StartColumn);
            },
            error =>
            {
                Assert.Contains("Property 'X' was not found on `A`", error.Message);
                Assert.Contains("visible algorithm or property named 'X'", error.Message);
            });
    }

    [Fact]
    public void Run_EvalError_ReturnsEvalFailure()
    {
        var result = KatLangEngine.Run("1 / 0");
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.NotEmpty(failure.Errors);
        Assert.Contains("zero", failure.Errors[0].Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void Run_EvalError_HasRoot()
    {
        var result = KatLangEngine.Run("1 / 0");
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.NotNull(failure.Root);
        Assert.IsType<Algorithm.User>(failure.Root);
    }

    [Fact]
    public void Run_EvalError_UnknownName_ReturnsEvalFailure()
    {
        var result = KatLangEngine.Run("nonexistent");
        Assert.IsType<RunResult.EvalFailure>(result);
    }

    [Fact]
    public void Run_WhileStepStateArityMismatch_GuidesNestedCapture()
    {
        var source = """
            Outer = {
                Step = {
                    n,
                    acc + 1,
                    acc < 3
                }

                Step.while(n, 0):1
            }

            Outer(5)
            """;

        var result = KatLangEngine.Run(source);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("`while` step expects 1 state value for 1 parameter 'acc'", error.Message, StringComparison.Ordinal);
        Assert.Contains("current loop state has 2 state values", error.Message, StringComparison.Ordinal);
        Assert.Contains("names already bound by an enclosing algorithm are captured", error.Message, StringComparison.Ordinal);
        Assert.Contains("candidate", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Run_RepeatStepStateArityMismatch_GuidesNestedCapture()
    {
        var source = """
            Outer = {
                Step = {
                    n,
                    acc + 1
                }

                Step.repeat(1, n, 0):1
            }

            Outer(5)
            """;

        var result = KatLangEngine.Run(source);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("`repeat` step expects 1 state value for 1 parameter 'acc'", error.Message, StringComparison.Ordinal);
        Assert.Contains("current loop state has 2 state values", error.Message, StringComparison.Ordinal);
        Assert.Contains("names already bound by an enclosing algorithm are captured", error.Message, StringComparison.Ordinal);
        Assert.Contains("candidate", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Run_NoOutputAlgorithmUsedAsValue_ReturnsEvalFailure()
    {
        var result = KatLangEngine.Run(
            """
            Lib = {
              Prop = 7
            }
            Lib == ()
            """);

        Assert.IsType<RunResult.EvalFailure>(result);
    }

    [Fact]
    public void Run_NoOutputBodyForcedThroughDotCall_ReturnsEvalFailure()
    {
        var result = KatLangEngine.Run("C = {}\nC.count");

        Assert.IsType<RunResult.EvalFailure>(result);
    }

    [Theory]
    [InlineData("1 + 'x'")]
    [InlineData("Id(x) = x\nId(1, 2)")]
    [InlineData("Lib = {\n  A = 1\n}\nLib.B")]
    public void Run_OrdinaryEvalErrors_ReturnEvalFailure(string source)
    {
        var result = KatLangEngine.Run(source);

        Assert.IsType<RunResult.EvalFailure>(result);
    }

    [Fact]
    public void Run_If_TwoArgs_ReturnsParseFailure()
    {
        var result = KatLangEngine.Run("10 * if(7 < 6, 1)");

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse.", error.Message);
    }

    [Fact]
    public void Run_OutputDotCall_IsOrdinaryMemberCall()
    {
        var result = KatLangEngine.Run(
            """
            Algo = {
              Output(x) = x + 1
            }
            Algo.Output(6)
            """);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal("7", success.ToDisplayString());
    }

    [Fact]
    public void Run_OutputNamedPropertyAlone_IsNoProgramOutput()
    {
        // The former explicit-output spelling is an ordinary property
        // definition: with no expression rows the program has no output.
        var result = KatLangEngine.Run("Output = 42");

        Assert.IsType<RunResult.NoProgramOutput>(result);
    }

    [Fact]
    public void Run_CallToNoOutputAlgorithm_ReturnsEvalFailureWithMissingOutputMessage()
    {
        var result = KatLangEngine.Run(
            """
            Algo = {
              Prop = 7
            }
            Algo(6)
            """);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(
            "Cannot call 'Algo' because it has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To call one of its properties, use property access instead.",
            error.Message);
    }

    [Fact]
    public void Run_ParametrizedContainerWithoutOutput_ReturnsParseFailure()
    {
        var result = KatLangEngine.Run(
            """
            Algo(x, y) = {
              Prop = 7
            }
            """);

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("declares explicit parameters", error.Message);
        Assert.Contains("does not define an output", error.Message);
    }

    [Fact]
    public void Run_Filter_NonCallablePredicate_ExplainsImplicitItemArgument()
    {
        var result = KatLangEngine.Run("range(1, 5).filter(1)");

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("filter passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact", error.Message);
        Assert.Contains("Expected 0 parameters, but was called with 1 argument.", error.Message);
    }

    [Fact]
    public void Run_HidesBlockWrapping_RootIsAlgorithm()
    {
        var result = KatLangEngine.Run("42");
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.IsType<Algorithm.User>(success.Root);
    }

    [Fact]
    public void Run_IsSuccess_IsFailure_Flags()
    {
        var ok = KatLangEngine.Run("1");
        Assert.True(ok.IsSuccess);
        Assert.False(ok.IsFailure);

        var noOutput = KatLangEngine.Run("T = 4");
        Assert.False(noOutput.IsSuccess);
        Assert.True(noOutput.IsNoProgramOutput);
        Assert.False(noOutput.IsFailure);

        var parseErr = KatLangEngine.Run("2 +");
        Assert.False(parseErr.IsSuccess);
        Assert.True(parseErr.IsFailure);

        var evalErr = KatLangEngine.Run("1 / 0");
        Assert.False(evalErr.IsSuccess);
        Assert.True(evalErr.IsFailure);
    }

    [Fact]
    public void Run_PatternMatchingOnResult_IsExhaustive()
    {
        var result = KatLangEngine.Run("5 * 5");
        var text = result switch
        {
            RunResult.Success s => string.Join(" ", s.Atoms),
            RunResult.NoProgramOutput n => n.ToDisplayString(),
            RunResult.ParseFailure p => $"parse: {p.Errors.Count}",
            RunResult.EvalFailure e => $"eval: {e.Errors.Count}",
            _ => throw new InvalidOperationException("Unknown RunResult variant."),
        };
        Assert.Equal("25", text);
    }

    // ── EvaluateToAtoms ──────────────────────────────────────────────────────

    [Fact]
    public void EvaluateToAtoms_SimpleExpression_ReturnsAtoms()
    {
        var atoms = KatLangEngine.EvaluateToAtoms("3 * 4");
        Assert.Equal([12m], atoms);
    }

    [Fact]
    public void EvaluateToAtoms_MultipleOutputs_ReturnsAll()
    {
        var atoms = KatLangEngine.EvaluateToAtoms("10, 20, 30");
        Assert.Equal([10m, 20m, 30m], atoms);
    }

    [Fact]
    public void EvaluateToAtoms_ParseError_Throws()
    {
        var ex = Assert.Throws<KatLangException>(() => KatLangEngine.EvaluateToAtoms("2 +"));
        Assert.NotEmpty(ex.Errors);
    }

    [Fact]
    public void EvaluateToAtoms_EvalError_Throws()
    {
        var ex = Assert.Throws<KatLangException>(() => KatLangEngine.EvaluateToAtoms("1 / 0"));
        Assert.NotEmpty(ex.Errors);
    }

    [Fact]
    public void EvaluateToAtoms_NoProgramOutput_Throws()
    {
        var ex = Assert.Throws<KatLangException>(() => KatLangEngine.EvaluateToAtoms("T = 4"));

        var error = Assert.Single(ex.Errors);
        Assert.Equal(RunResult.NoProgramOutput.DefaultMessage, error.Message);
    }

    // ── EvaluateToString ─────────────────────────────────────────────────────

    [Fact]
    public void EvaluateToString_SimpleExpression_ReturnsDisplayString()
    {
        var text = KatLangEngine.EvaluateToString("5 + 5");
        Assert.Equal("10", text);
    }

    [Fact]
    public void EvaluateToString_MultipleOutputs_SpaceSeparated()
    {
        var text = KatLangEngine.EvaluateToString("1, 2, 3");
        Assert.Equal("1 2 3", text);
    }

    [Fact]
    public void EvaluateToString_ParseError_ReturnsErrorText()
    {
        var text = KatLangEngine.EvaluateToString("2 +");
        Assert.NotEmpty(text);
    }

    [Fact]
    public void EvaluateToString_EvalError_ReturnsErrorText()
    {
        var text = KatLangEngine.EvaluateToString("1 / 0");
        Assert.NotEmpty(text);
        Assert.Contains("zero", text, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EvaluateToString_NoProgramOutput_ReturnsNoOutputMessage()
    {
        var text = KatLangEngine.EvaluateToString("T = 4");

        Assert.Equal(RunResult.NoProgramOutput.DefaultMessage, text);
    }

    // ── Parser.Parse with RunOptions ─────────────────────────────────────────

    [Fact]
    public void Parser_Parse_WithoutOptions_Works()
    {
        var result = Parser.Parse("42");
        Assert.False(result.HasErrors);
        Assert.NotNull(result.Root);
    }

    [Fact]
    public void Parser_Parse_WithNullParseOptions_Works()
    {
        var result = Parser.Parse("42", (RunOptions?)null);
        Assert.False(result.HasErrors);
        Assert.NotNull(result.Root);
    }

    [Fact]
    public void Parser_Parse_WithEmptyParseOptions_Works()
    {
        var result = Parser.Parse("42", new RunOptions());
        Assert.False(result.HasErrors);
        Assert.NotNull(result.Root);
    }

    [Fact]
    public void Parser_Parse_WithEmptyParseOptions_RejectsLoad()
    {
        var result = Parser.Parse(
            "Lib = load('https://katlang.org/demo/lib.kat')",
            new RunOptions());

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            diagnostic => diagnostic.Message.Contains("module elaboration is unavailable", StringComparison.OrdinalIgnoreCase));
    }

    // ── RunResult.ToDisplayString ────────────────────────────────────────────

    [Fact]
    public void RunResult_ToDisplayString_OnSuccess_ShowsAtoms()
    {
        var result = KatLangEngine.Run("7");
        Assert.Equal("7", result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_FlatMultiOutput_DisplaysRows()
    {
        var result = KatLangEngine.Run("1, 2, 3");

        Assert.Equal(Lines("1", "2", "3"), result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_CommaWithSequenceValue_DisplaysRows()
    {
        var result = KatLangEngine.Run("1, (2, 3)");

        Assert.Equal(Lines("1", "(2, 3)"), result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_NewlineAdjacencyAfterComma_DisplaysRows()
    {
        var result = KatLangEngine.Run(
            """
            1, 2
            3
            """);

        Assert.Equal(Lines("1", "2", "3"), result.ToDisplayString());
    }

    [Theory]
    [InlineData("1 2")]
    [InlineData("(1, 2)")]
    public void RunResult_ToDisplayString_SameLineAdjacencyAndSequenceValueComma_DisplayExpectedShape(string source)
    {
        var result = KatLangEngine.Run(source);

        Assert.Equal(source.StartsWith('(') ? "(1, 2)" : Lines("1", "2"), result.ToDisplayString());
    }

    [Theory]
    [InlineData("1, 2 3")]
    [InlineData("1, (2, 3)")]
    public void RunResult_ToDisplayString_AdjacencyAfterComma_DisplaysRowsOrSequenceValue(string source)
    {
        var result = KatLangEngine.Run(source);

        Assert.Equal(source.Contains("(2, 3)", StringComparison.Ordinal) ? Lines("1", "(2, 3)") : Lines("1", "2", "3"), result.ToDisplayString());
    }

    [Theory]
    [InlineData("(1 2)")]
    [InlineData("((1, 2))")]
    public void RunResult_ToDisplayString_ParenthesizedAdjacency_DisplaysOneSequenceValue(string source)
    {
        var result = KatLangEngine.Run(source);

        Assert.Equal("(1, 2)", result.ToDisplayString());
    }

    [Fact]
    public void Run_CallArgumentAdjacency_SpreadsTwoArguments()
    {
        var source = """
            Add(x, y) = x + y
            Add(1 2)
            """;
        var result = KatLangEngine.Run(source);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([3m], success.Atoms);
    }

    [Theory]
    [InlineData("Add(x, y) = x + y\nAdd(1, 2)")]
    [InlineData("Add(x, y) = x + y\nAdd (1, 2)")]
    public void Run_DirectCallWhitespaceBeforeParen_IsSameCall(string source)
    {
        var result = KatLangEngine.Run(source);

        Assert.Equal("3", result.ToDisplayString());
    }

    [Theory]
    [InlineData("Add(x, y) = x + y\nAdd(\n1, 2\n)")]
    public void Run_OpenedCallDelimiterSpansLines_IsSameCall(string source)
    {
        // Multiline calls open the delimiter before the newline; the
        // already-open argument list spans lines normally.
        var result = KatLangEngine.Run(source);

        Assert.Equal("3", result.ToDisplayString());
    }

    [Theory]
    [InlineData("open A...", "Expected property name after '.'.")]
    [InlineData("open A...B", "Expected property name after '.'.")]
    [InlineData("open 'url'...", "Expected ',' between open targets")]
    [InlineData("open A, 'url'...", "Expected ',' between open targets")]
    public void Run_OpenEllipsisRemnant_ReportsOrdinaryParseFailure(string source, string expectedMessage)
    {
        // `...` is not a token: it lexes as three dots, so a legacy
        // ellipsis-marked open target fails through the ordinary dotted-target
        // and open-separator diagnostics; the rejection happens at parse time,
        // before any evaluation.
        var result = KatLangEngine.Run(source);

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.Contains(
            failure.Errors,
            error => error.Message.Contains(expectedMessage, StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("open A*")]
    [InlineData("open A**")]
    [InlineData("open A, B*")]
    public void Run_OpenSpreadExpressionTarget_ReportsParseFailure(string source)
    {
        // A spread-marked target parses to a spread expression, which is not
        // an open form; the rejection happens at parse time, before any
        // evaluation.
        var result = KatLangEngine.Run(source);

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.Contains(
            failure.Errors,
            static error => error.Message.Contains(
                "Invalid open form: 'spread' is not allowed in open declarations",
                StringComparison.Ordinal));
    }

    [Fact]
    public void Run_ColonLedLineAfterDefinitionBody_ReportsParseFailure()
    {
        // A physical newline never continues a closed expression into
        // postfix indexing: `P = Pair` newline `:0` must not silently define
        // `P = Pair:0`. The ':'-led line is a parse error with a targeted
        // message.
        var result = KatLangEngine.Run("Pair = 1, 2\nP = Pair\n:0\nP");

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.Contains(
            failure.Errors,
            static error => error.Message.Contains(
                "Indexing is postfix and must follow the indexed expression on the same physical line",
                StringComparison.Ordinal));
    }

    [Fact]
    public void Run_ParenLedLineAfterDefinitionBody_DoesNotCreateRecursivePropertyCall()
    {
        // Regression: `A = Identity` newline `(A)` once parsed as
        // `A = Identity(A)`, so report-like programs recursed through their
        // own property and overflowed. The newline ends the body, `(A)` is a
        // report row, and the run terminates with ordinary diagnostics.
        var source = """
            Identity = x

            A = Identity
            (A)

            A
            """;
        var result = KatLangEngine.Run(source);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.All(
            failure.Errors,
            static error => Assert.DoesNotContain("recursi", error.Message, StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void RunResult_ToDisplayString_SingleSequenceValueOutput_PreservesParentheses()
    {
        var result = KatLangEngine.Run("(1, 2, 3)");

        Assert.Equal("(1, 2, 3)", result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_MultipleSequenceValueOutputs_PreservesItemParentheses()
    {
        var result = KatLangEngine.Run("(1, 2), (3, 4)");

        Assert.Equal(Lines("(1, 2)", "(3, 4)"), result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_NestedSequenceValueOutputs_PreservesParentheses()
    {
        var result = KatLangEngine.Run("((1, 2), 3), (4, (5, 6))");

        Assert.Equal(Lines("((1, 2), 3)", "(4, (5, 6))"), result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_MixedTopLevelOutput_DisplaysRows()
    {
        var result = KatLangEngine.Run("1, (2, 3), 4");

        Assert.Equal(Lines("1", "(2, 3)", "4"), result.ToDisplayString());
    }

    [Fact]
    public void RunResult_SemicolonSyntax_ReportsParseFailure()
    {
        var result = KatLangEngine.Run("(1, 2) ; 3");

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.Contains(failure.Errors, error => error.Message.Contains("Semicolon is not supported as an expression separator", StringComparison.Ordinal));
    }

    [Fact]
    public void RunResult_ToDisplayString_ReportStyleOutput_RemainsReadable()
    {
        var result = KatLangEngine.Run(
            """
            SalaryExpenses(amount, recurring, reimbursed) = amount, recurring, reimbursed

            SalaryExpenses(3800, 1, 0)
            ''
            SalaryExpenses(50, 0, 0)
            """);

        Assert.Equal(Lines("(3800, 1, 0)", "", "(50, 0, 0)"), result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_OrdinaryDotCallReceiver_ShowsSingleSequenceValueResult()
    {
        var result = KatLangEngine.Run(
            """
            Collect(list) = list
            (10, 20, 30).Collect
            """);

        Assert.Equal("(10, 20, 30)", result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_VariadicDotCallReceiver_ShowsReceiverSupplyListResult()
    {
        // A call boundary always returns one value. The receiver is one
        // leading argument segment, and the collecting parameter it is
        // allocated to consumes the segment's supply: the inline group emits
        // its three row items, so the collected list is [10, 20, 30],
        // displayed as a single row.
        var result = KatLangEngine.Run(
            """
            Collect(*list) = list
            (10, 20, 30).Collect
            """);

        Assert.Equal("[10, 20, 30]", result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_VariadicDotCallReceiverSpread_OpensIntoRows()
    {
        // The capture-of-spread receiver supplies the same three items through
        // the general receiver-supply rule, so the collected list is
        // [10, 20, 30]; the explicit caller-site spread then re-spreads the
        // returned list into the surrounding item supply, displaying separate
        // rows.
        var result = KatLangEngine.Run(
            """
            Collect(*list) = list
            ((10, 20, 30)*).Collect*
            """);

        Assert.Equal(Lines("10", "20", "30"), result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_DisplayDecimals_FormatsGlobalDecimalOutput()
    {
        var result = KatLangEngine.Run(
            """
            DisplayDecimals = 3

            Math.Pi
            """);

        Assert.Equal("3.142", result.ToDisplayString());
    }

    [Theory]
    [InlineData(0, "3")]
    [InlineData(1, "3.1")]
    [InlineData(2, "3.14")]
    [InlineData(6, "3.141593")]
    public void RunResult_ToDisplayString_DisplayDecimals_RoundsAtCommonPlaces(
        int decimals,
        string expected)
    {
        var result = KatLangEngine.Run(
            $$"""
            DisplayDecimals = {{decimals}}

            Math.Pi
            """);

        Assert.Equal(expected, result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_DisplayDecimals_FormatsNestedNumericLeaves()
    {
        var result = KatLangEngine.Run(
            """
            DisplayDecimals = 3

            (Math.Pi, Math.E)
            """);

        Assert.Equal("(3.142, 2.718)", result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_DisplayDecimals_FormatsDeepNestedNumericLeaves()
    {
        var result = KatLangEngine.Run(
            """
            DisplayDecimals = 2

            (Math.Pi, (Math.E, Math.Pi * 10))
            """);

        Assert.Equal("(3.14, (2.72, 31.42))", result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_DisplayDecimals_RemainsReadableProperty()
    {
        var result = KatLangEngine.Run(
            """
            DisplayDecimals = 6

            DisplayDecimals
            """);

        Assert.Equal("6", result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_DisplayDecimals_CanBeUsedInsideExpression()
    {
        var result = KatLangEngine.Run(
            """
            DisplayDecimals = 6

            A = DisplayDecimals + 1

            A
            """);

        Assert.Equal("7", result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_DisplayDecimals_OnlyUsesTopLevelProperty()
    {
        var result = KatLangEngine.Run(
            """
            A = {
                DisplayDecimals = 2

                Math.Pi
            }

            A
            """);

        Assert.Equal("3.1415926535897932384626433833", result.ToDisplayString());
    }

    [Fact]
    public void EvaluateToString_DisplayDecimals_FormatsFlatAtoms()
    {
        var text = KatLangEngine.EvaluateToString(
            """
            DisplayDecimals = 2

            Math.Pi
            Math.E
            """);

        Assert.Equal("3.14 2.72", text);
    }

    private static void RunUnderCulture(string cultureName, Action assertions)
    {
        var previous = System.Globalization.CultureInfo.CurrentCulture;
        try
        {
            System.Globalization.CultureInfo.CurrentCulture =
                System.Globalization.CultureInfo.GetCultureInfo(cultureName);
            assertions();
        }
        finally
        {
            System.Globalization.CultureInfo.CurrentCulture = previous;
        }
    }

    [Theory]
    [InlineData("de-DE")]
    [InlineData("fr-FR")]
    [InlineData("en-US")]
    public void Display_CanonicalNumberFormatting_IsCultureInvariant(string cultureName)
    {
        // Canonical KatLang value display always uses `.` as the decimal
        // point, so fractional atoms can never collide with the `, ` element
        // separator of sequence/list rendering and output is identical on
        // every machine.
        RunUnderCulture(cultureName, () =>
        {
            Assert.Equal("(2.5, 3.5)", KatLangEngine.Run("(2.5, 3.5)").ToDisplayString());
            Assert.Equal("[1.5, -2.25]", KatLangEngine.Run("[1.5, -2.25]").ToDisplayString());
            Assert.Equal("1.0", KatLangEngine.Run("0.5 + 0.5").ToDisplayString());
            Assert.Equal("[1, (2.5, [3.5])]", KatLangEngine.Run("[1, (2.5, [3.5])]").ToDisplayString());
            Assert.Equal(
                "3.1415926535897932384626433833",
                KatLangEngine.Run("Math.Pi").ToDisplayString());

            // DisplayDecimals path stays invariant too.
            Assert.Equal(
                "3.14",
                KatLangEngine.Run("DisplayDecimals = 2\nMath.Pi").ToDisplayString());

            // Flat-atom string output.
            Assert.Equal("2.5 3.5", KatLangEngine.EvaluateToString("2.5\n3.5"));

            // Diagnostics that render values keep the invariant form.
            var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("[1.5] + 1"));
            Assert.Contains("[1.5]", failure.ToDisplayString(), StringComparison.Ordinal);
        });
    }

    [Fact]
    public void RunResult_ToDisplayString_DisplayDecimals_FormatsMixedNumericOutputRows()
    {
        var result = KatLangEngine.Run(
            """
            DisplayDecimals = 4

            Math.Pi
            Math.E
            """);

        Assert.Equal(Lines("3.1416", "2.7183"), result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_DisplayDecimals_FormatsScaledZero()
    {
        var result = KatLangEngine.Run(
            """
            DisplayDecimals = 6

            0.000000000000000000000000000
            """);

        Assert.Equal("0.000000", result.ToDisplayString());
    }

    [Fact]
    public void RunResult_ToDisplayString_DisplayDecimals_PreservesPrecisionForCalculations()
    {
        var result = KatLangEngine.Run(
            """
            DisplayDecimals = 2

            A = Math.Pi

            A * 1000
            """);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal("3141.59", success.ToDisplayString());
        Assert.NotEqual([3140m], success.Atoms);
    }

    [Fact]
    public void RunResult_ToDisplayString_DisplayDecimalsAbsent_UsesExistingDefaultRendering()
    {
        var result = KatLangEngine.Run("Math.Pi");

        Assert.Equal("3.1415926535897932384626433833", result.ToDisplayString());
    }

    [Theory]
    [InlineData("DisplayDecimals = -1\nMath.Pi", "non-negative integer")]
    [InlineData("DisplayDecimals = 1.5\nMath.Pi", "integer")]
    [InlineData("DisplayDecimals = 'x'\nMath.Pi", "single numeric value")]
    [InlineData("DisplayDecimals = 2, 3\nMath.Pi", "single numeric value")]
    [InlineData("DisplayDecimals = (2, 3)\nMath.Pi", "single numeric value")]
    [InlineData("DisplayDecimals = 100\nMath.Pi", "between 0 and 99")]
    [InlineData("DisplayDecimals = 1000000000\nMath.Pi", "between 0 and 99")]
    public void Run_DisplayDecimals_InvalidGlobalDecimals_ReturnsEvalFailure(
        string source,
        string expectedMessage)
    {
        var result = KatLangEngine.Run(source);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("DisplayDecimals", error.Message, StringComparison.Ordinal);
        Assert.Contains(expectedMessage, error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RunResult_ToDisplayString_OnParseError_ShowsErrors()
    {
        var result = KatLangEngine.Run("2 +");
        var display = result.ToDisplayString();
        Assert.NotEmpty(display);
    }

    [Fact]
    public void RunResult_ToDisplayString_OnEvalError_ShowsErrors()
    {
        var result = KatLangEngine.Run("1 / 0");
        var display = result.ToDisplayString();
        Assert.Contains("zero", display, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void RunResult_ToDisplayString_OnNoProgramOutput_ShowsFriendlyMessage()
    {
        var result = KatLangEngine.Run("T = 4");

        Assert.Equal(RunResult.NoProgramOutput.DefaultMessage, result.ToDisplayString());
    }

    // ── KatLangError ─────────────────────────────────────────────────────────

    [Fact]
    public void KatLangError_FromDiagnostic_MapsFields()
    {
        var diag = new Diagnostic("test error", DiagnosticSeverity.Error,
            new SourceSpan(1, 5, 1, 10));
        var error = KatLangError.FromDiagnostic(diag);
        Assert.Equal("test error", error.Message);
        Assert.Equal(1, error.StartLine);
        Assert.Equal(5, error.StartColumn);
        Assert.Equal(1, error.EndLine);
        Assert.Equal(10, error.EndColumn);
    }

    [Fact]
    public void KatLangError_FromEvalError_WithSpan_MapsFields()
    {
        var evalErr = new EvalError.DivByZero() { Span = new SourceSpan(3, 2, 3, 5) };
        var error = KatLangError.FromEvalError(evalErr);
        Assert.Contains("zero", error.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(3, error.StartLine);
        Assert.Equal(2, error.StartColumn);
    }

    [Fact]
    public void KatLangError_FromEvalError_WithoutSpan_HasNullSpan()
    {
        var evalErr = new EvalError.UnknownName("x");
        var error = KatLangError.FromEvalError(evalErr);
        Assert.Contains("x", error.Message);
        Assert.Null(error.StartLine);
        Assert.Null(error.StartColumn);
    }

    [Fact]
    public void KatLangError_ToString_WithSpan_IncludesLocation()
    {
        var diag = new Diagnostic("oops", DiagnosticSeverity.Error,
            new SourceSpan(2, 3, 2, 7));
        var error = KatLangError.FromDiagnostic(diag);
        var str = error.ToString();
        Assert.Contains("[2:3]", str);
        Assert.Contains("oops", str);
    }

    [Fact]
    public void KatLangError_ToString_WithoutSpan_JustMessage()
    {
        var evalErr = new EvalError.BadIndex();
        var error = KatLangError.FromEvalError(evalErr);
        var str = error.ToString();
        Assert.DoesNotContain("[", str);
    }

    // ── Conditional branch: free identifier detection (end-to-end) ──────────

    [Fact]
    public void Run_ConditionalBranch_FreeIdentifier_ReturnsParseFailure()
    {
        var source = """
            A(2) = x
            A(2)
            """;
        var result = KatLangEngine.Run(source);

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("Identifier 'x' is used in conditional branch 'A'", error.Message);
        Assert.Contains("A(y) = y", error.Message);
    }

    [Fact]
    public void Run_ConditionalBranch_AllBindersBound_Succeeds()
    {
        var source = """
            Expense(1, qty) = 1.20 * qty
            Expense(2, qty) = 0.80 * qty
            Expense(2, 3)
            """;
        var result = KatLangEngine.Run(source);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([2.40m], success.Atoms);
    }

    [Fact]
    public void Run_FlatMultiBinderClause_HigherOrderBinding_Succeeds()
    {
        var source = """
            IsEven = y mod 2 == 0
            Choose(x, predicate) = if(predicate(x), x, 0)
            Choose(4, IsEven)
            """;
        var result = KatLangEngine.Run(source);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([4m], success.Atoms);
    }

    [Fact]
    public void Run_FlatMultiBinderClause_FalsePredicate_UsesElseBranch()
    {
        var source = """
            IsEven = y mod 2 == 0
            Choose(x, predicate) = if(predicate(x), x, 0)
            Choose(3, IsEven)
            """;
        var result = KatLangEngine.Run(source);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([0m], success.Atoms);
    }

    [Fact]
    public void Run_ClauseDefinition_SingleBinder_ElaboratesToOrdinaryAlgorithm()
    {
        var source = """
            Id(x) = x
            Id(7)
            """;
        var result = KatLangEngine.Run(source);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([7m], success.Atoms);
    }

    [Fact]
    public void Run_ClauseGroup_LiteralThenPlainBinder_RemainsConditional()
    {
        var source = """
            F(0) = 0
            F(x) = 1
            F(2)
            """;
        var result = KatLangEngine.Run(source);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([1m], success.Atoms);
    }

    [Fact]
    public void Run_ClauseDefinition_SingleBinder_HigherOrderCallUsesOrdinaryBinding()
    {
        var source = """
            Apply(f) = f(4)
            Double(x) = x * 2
            Apply(Double)
            """;
        var result = KatLangEngine.Run(source);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([8m], success.Atoms);
    }

    [Fact]
    public void Run_MapRecursiveFactorial_Succeeds()
    {
        var source = """
            Factorial = if(n == 0, 1, Factorial(n - 1) * n)
            (0, 1, 2, 3, 4).map(Factorial)
            """;
        var result = KatLangEngine.Run(source);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([1m, 1m, 2m, 6m, 24m], success.Atoms);
    }

    [Fact]
    public void Run_InlineOpenBlock_UsesPreludeBuiltinsWithoutOpenerShadowing()
    {
        var source = """
            open {
            public Use = {1, 2}.sum
            }
            sum = 99
            Use
            """;
        var result = KatLangEngine.Run(source);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([3m], success.Atoms);
    }

    [Fact]
    public void Run_ClauseDefinition_SingleBinder_RejectsExtraArguments()
    {
        var source = """
            Id(x) = x
            Id(1, 2)
            """;
        var result = KatLangEngine.Run(source);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Contains("Callable `Id(x)` expects 1 argument, but was called with 2 arguments.", failure.ToDisplayString(), StringComparison.Ordinal);
    }

    [Fact]
    public void Run_ClauseDefinition_TwoBinders_RejectsMissingArgument()
    {
        var source = """
            Add(a, b) = a + b
            Add(1)
            """;
        var result = KatLangEngine.Run(source);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Equal("Callable `Add(a, b)` expects 2 arguments, but was called with 1 argument.", error.Message);
        Assert.Contains(error.Message, failure.ToDisplayString(), StringComparison.Ordinal);
    }

    [Fact]
    public void Run_FlatFixedCall_MultiOutputPropertyReferenceReportsOneArgument()
    {
        var source = """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair)
            """;
        var result = KatLangEngine.Run(source);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("Callable `Add(x, y)` expects 2 arguments", error.Message, StringComparison.Ordinal);
        Assert.Contains("1 argument", error.Message, StringComparison.Ordinal);
        Assert.Contains(error.Message, failure.ToDisplayString(), StringComparison.Ordinal);
    }

    [Fact]
    public void Run_TopLevel_ImplicitParameter_UsesKatLangFacingMessage()
    {
        var result = KatLangEngine.Run("x + 1");

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("Identifier 'x' does not resolve to a property or other visible name here", error.Message);
        Assert.Contains("KatLang interprets it as an implicit parameter", error.Message);
        Assert.Contains("Its value is provided by the caller", error.Message);
        Assert.DoesNotContain("not defined in the current scope", error.Message);
    }
}
