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
    public void Run_If_TwoArgs_ReturnsParseFailure()
    {
        var result = KatLangEngine.Run("10 * if(7 < 6, 1)");

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse.", error.Message);
    }

    [Fact]
    public void Run_OutputPropertyAccess_ReturnsParseFailureWithGuidance()
    {
        var result = KatLangEngine.Run(
            """
            Algo(x) = {
              Output = x + 1
            }
            Algo.Output(6)
            """);

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("Output is the designated result of an algorithm", error.Message);
        Assert.Contains("Instead of `Algo.Output(6)`, write `Algo(6)`", error.Message);
    }

    [Fact]
    public void Run_NestedOutputPropertyAccess_ReturnsParseFailure()
    {
        var result = KatLangEngine.Run(
            """
            Outer = {
              Inner(x) = {
                Output = x + 10
              }
            }
            Outer.Inner.Output(6)
            """);

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("Output is the designated result of an algorithm", error.Message);
    }

    [Fact]
    public void Run_Filter_NonCallablePredicate_ExplainsImplicitItemArgument()
    {
        var result = KatLangEngine.Run("range(1, 5).filter(1)");

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Contains("filter passes each collection item as one argument to the predicate", error.Message);
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
    public void Run_ClauseDefinition_SingleBinder_RejectsExtraArguments()
    {
        var source = """
            Id(x) = x
            Id(1, 2)
            """;
        var result = KatLangEngine.Run(source);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Contains("Property 'Id' expects 1 parameter, but was called with 2 arguments.", failure.ToDisplayString(), StringComparison.Ordinal);
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
