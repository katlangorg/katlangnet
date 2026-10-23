using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text;
using KatLang.TestInfrastructure;

namespace KatLang.CLI.Tests;

/// <summary>
/// SEC-07: untrusted text in a CLI diagnostic — a command-line argument, a file path, an
/// exception message, a program's source or values echoed by a KatLang diagnostic — must never
/// reach stderr as an actionable terminal control. Unsafe code units are shown as visible
/// <c>\uXXXX</c> escapes; safe text, KatLang's own diagnostic line structure, the structured
/// diagnostic data, and successful program output are unchanged.
/// </summary>
public sealed class TerminalSafeDiagnosticsTests
{
    private const int Failure = 1;

    private const char Esc = (char)0x1B;
    private const char Bel = (char)0x07;
    private const char Csi8 = (char)0x9B;
    private const char Osc8 = (char)0x9D;

    /// <summary>The visible escape the policy renders for one UTF-16 code unit.</summary>
    private static string U(int codeUnit) => "\\" + "u" + codeUnit.ToString("X4", System.Globalization.CultureInfo.InvariantCulture);

    /// <summary>Every code unit a terminal could act on, or that hides or reorders text.</summary>
    private static void AssertNoUnsafeCodeUnit(string text, bool allowLineFeeds)
    {
        for (var i = 0; i < text.Length; i++)
        {
            var ch = text[i];
            if (allowLineFeeds && (ch == '\n' || (ch == '\r' && i + 1 < text.Length && text[i + 1] == '\n')))
                continue;

            if (char.IsHighSurrogate(ch) && i + 1 < text.Length && char.IsLowSurrogate(text[i + 1]))
            {
                Assert.NotEqual(System.Globalization.UnicodeCategory.Format, char.GetUnicodeCategory(text, i));
                i++;
                continue;
            }

            Assert.False(
                char.IsControl(ch) || char.IsSurrogate(ch)
                || char.GetUnicodeCategory(ch) is System.Globalization.UnicodeCategory.Format
                    or System.Globalization.UnicodeCategory.LineSeparator
                    or System.Globalization.UnicodeCategory.ParagraphSeparator,
                $"unsafe code unit U+{(int)ch:X4} at index {i} in: {text}");
        }
    }

    /// <summary>Stderr of one invocation: every line ends in the platform newline, nothing else is a control.</summary>
    private static void AssertSafeStderr(CliResult result)
        => AssertNoUnsafeCodeUnit(result.Error, allowLineFeeds: true);

    // ── T1 / T6: the policy itself ──────────────────────────────────────────

    [Theory]
    [InlineData("Division by zero")]
    [InlineData("katlang: file not found: 'missing.kat'.")]
    [InlineData("[1:5] Unexpected character: '@'.")]
    [InlineData("katlang: cancelled.")]
    [InlineData("Nezināms nosaukums: Ābols")]
    [InlineData("Ελληνικά, Кириллица, 漢字かなカナ")]
    [InlineData("a backslash \\ and a written escape \\u001B stay as written")]
    [InlineData("")]
    public void SafeText_IsReturnedUnchanged_AsTheSameInstance(string text)
    {
        Assert.Same(text, TerminalSafeText.EscapeLine(text));
    }

    [Fact]
    public void ValidSupplementaryCharacter_IsKept_AsOneCharacter()
    {
        var text = "emoji " + char.ConvertFromUtf32(0x1F600) + " and math " + char.ConvertFromUtf32(0x1D400);

        Assert.Same(text, TerminalSafeText.EscapeLine(text));
    }

    [Fact]
    public void SupplementaryFormatCharacter_IsEscaped_AsBothCodeUnits()
    {
        // U+E0001 LANGUAGE TAG is a supplementary format character.
        var tag = char.ConvertFromUtf32(0xE0001);

        Assert.Equal("a" + U(tag[0]) + U(tag[1]) + "b", TerminalSafeText.EscapeLine("a" + tag + "b"));
    }

    [Theory]
    [InlineData(0xD800)]
    [InlineData(0xDBFF)]
    [InlineData(0xDC00)]
    [InlineData(0xDFFF)]
    public void UnpairedSurrogate_IsEscaped(int codeUnit)
    {
        var text = "x" + (char)codeUnit + "y";

        Assert.Equal("x" + U(codeUnit) + "y", TerminalSafeText.EscapeLine(text));
    }

    [Fact]
    public void ReversedSurrogatePair_IsEscaped_AsTwoUnpairedCodeUnits()
    {
        var text = "" + (char)0xDC00 + (char)0xD800;

        Assert.Equal(U(0xDC00) + U(0xD800), TerminalSafeText.EscapeLine(text));
    }

    [Theory]
    [InlineData(0x2028)]
    [InlineData(0x2029)]
    [InlineData(0x0085)] // NEL, a C1 control that some terminals treat as a line break
    public void UnicodeLineBreaks_AreEscaped_EvenInRenderedDiagnostics(int codeUnit)
    {
        var text = "line" + (char)codeUnit + "forged";

        Assert.Equal("line" + U(codeUnit) + "forged", TerminalSafeText.EscapeLine(text));
    }

    // ── T2 / T3 / T4 / T5: control and format characters ────────────────────

    [Fact]
    public void AnsiSequences_LoseTheirIntroducer()
    {
        var text = $"Error: {Esc}[31mFAKE{Esc}[2J{Esc}[?25l{Esc}]52;c;cGF5bG9hZA=={Bel}";

        var escaped = TerminalSafeText.EscapeLine(text);

        Assert.Equal(
            $"Error: {U(0x1B)}[31mFAKE{U(0x1B)}[2J{U(0x1B)}[?25l{U(0x1B)}]52;c;cGF5bG9hZA=={U(0x07)}",
            escaped);
        AssertNoUnsafeCodeUnit(escaped, allowLineFeeds: false);
    }

    [Fact]
    public void C1Introducers_AreEscaped()
    {
        var text = $"{Csi8}2J and {Osc8}0;title{Bel}";

        Assert.Equal($"{U(0x9B)}2J and {U(0x9D)}0;title{U(0x07)}", TerminalSafeText.EscapeLine(text));
    }

    [Fact]
    public void EveryC0Control_Del_AndC1Control_IsEscapedInAFragment()
    {
        for (var code = 0; code <= 0x9F; code++)
        {
            if (code is >= 0x20 and < 0x7F)
                continue;

            Assert.Equal("a" + U(code) + "b", TerminalSafeText.EscapeLine("a" + (char)code + "b"));
        }
    }

    [Fact]
    public void FragmentLineBreaksAndOverwrites_StayOnOneVisibleLine()
    {
        var text = "safe\b\b\b\bevil\rkatlang: forged\nnext\ttab\0nul" + (char)0x7F;

        var escaped = TerminalSafeText.EscapeLine(text);

        Assert.Equal(
            $"safe{U(8)}{U(8)}{U(8)}{U(8)}evil{U(0x0D)}katlang: forged{U(0x0A)}next{U(9)}tab{U(0)}nul{U(0x7F)}",
            escaped);
        AssertNoUnsafeCodeUnit(escaped, allowLineFeeds: false);
    }

    [Fact]
    public void DiagnosticWriter_DoesNotTrustNewlinesInRawDiagnosticMessages()
    {
        var text = "[1:1] first\nDid you mean 'x'?\r\n[2:1] second\rkatlang: overwritten\ttab";
        var diagnostic = new Diagnostic(text, DiagnosticSeverity.Error, null);
        var error = new StringWriter();

        new DiagnosticWriter(error).WriteDiagnostic(KatLangError.FromDiagnostic(diagnostic));

        Assert.Equal(
            $"[1:1] first{U(0x0A)}Did you mean 'x'?{U(0x0D)}{U(0x0A)}[2:1] second{U(0x0D)}katlang: overwritten{U(9)}tab" + Environment.NewLine,
            error.ToString());
        Assert.Equal(text, diagnostic.Message);
    }

    [Theory]
    [InlineData(0x202A)]
    [InlineData(0x202B)]
    [InlineData(0x202C)]
    [InlineData(0x202D)]
    [InlineData(0x202E)]
    [InlineData(0x2066)]
    [InlineData(0x2067)]
    [InlineData(0x2068)]
    [InlineData(0x2069)]
    [InlineData(0x200B)]
    [InlineData(0x200E)]
    [InlineData(0x200F)]
    [InlineData(0xFEFF)]
    public void FormatControls_AreVisible(int codeUnit)
    {
        var text = "file 'a" + (char)codeUnit + "txt.kat'";

        Assert.Equal("file 'a" + U(codeUnit) + "txt.kat'", TerminalSafeText.EscapeLine(text));
    }

    [Fact]
    public void Escaping_IsIdempotent_SoAlreadyEscapedTextIsNotEscapedTwice()
    {
        var hostile = $"{Esc}[2J{(char)0x202E}{(char)0xD800}\r\n{Csi8}";

        var once = TerminalSafeText.EscapeLine(hostile);

        Assert.Same(once, TerminalSafeText.EscapeLine(once));
        Assert.DoesNotContain("\\\\u", once, StringComparison.Ordinal);
    }

    // ── T7: command-line arguments ──────────────────────────────────────────

    [Fact]
    public async Task UnknownOption_WithAnsiSequence_IsEscaped()
    {
        var result = await Cli.InvokeAsync("eval", "1", $"--x{Esc}[2J{Esc}]0;pwned{Bel}");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(
            $"katlang: unknown option '--x{U(0x1B)}[2J{U(0x1B)}]0;pwned{U(0x07)}'.\nRun 'katlang --help' for usage.",
            result.TrimmedError);
        AssertSafeStderr(result);
    }

    [Fact]
    public async Task UnknownCommand_CannotForgeADiagnosticLine()
    {
        var result = await Cli.InvokeAsync($"x\rkatlang: all good\n{Csi8}31m");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(
            $"katlang: unknown command 'x{U(0x0D)}katlang: all good{U(0x0A)}{U(0x9B)}31m'.\nRun 'katlang --help' for usage.",
            result.TrimmedError);
        AssertSafeStderr(result);
    }

    [Fact]
    public async Task UnexpectedPositionalArgument_IsEscaped()
    {
        var result = await Cli.InvokeAsync("eval", "1", $"extra{Esc}[31m{(char)0x202E}");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.StartsWith($"katlang: unexpected argument 'extra{U(0x1B)}[31m{U(0x202E)}'.", result.TrimmedError);
        AssertSafeStderr(result);
    }

    [Fact]
    public async Task InvalidOptionValue_IsEscaped()
    {
        var result = await Cli.InvokeAsync("eval", "1", "--random-seed", $"1{Esc}[2J");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains($"got '1{U(0x1B)}[2J'.", result.TrimmedError);
        AssertSafeStderr(result);
    }

    // ── T8: file paths ──────────────────────────────────────────────────────

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task MissingOrUnreadablePath_WithControls_IsEscaped(string command)
    {
        // Whatever the platform makes of the name — not found on Unix, an invalid name on
        // Windows — the path is echoed and must not carry its controls to the terminal.
        var path = Path.Combine(
            Path.GetTempPath(),
            $"katlang-sec07-{Guid.NewGuid():N}{Esc}[2J{Csi8}{(char)0x202E}\rforged.kat");

        var result = await Cli.InvokeAsync(command, path);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.StartsWith("katlang: ", result.TrimmedError);
        Assert.Contains($"{U(0x1B)}[2J{U(0x9B)}{U(0x202E)}{U(0x0D)}forged.kat", result.TrimmedError);
        Assert.Single(result.TrimmedError.Split('\n'));
        AssertSafeStderr(result);
    }

    // ── T9: unexpected exceptions ───────────────────────────────────────────

    [Fact]
    public void UnexpectedError_IsOneEscapedLine_WithTheEstablishedPrefix()
    {
        var error = new StringWriter();
        var exception = new InvalidOperationException(
            $"\r\n boom {Esc}[2J{Esc}[31mred\r\nkatlang: forged\n{(char)0x202E}txt.exe Ābols {Csi8}?25l ");

        CliApplication.WriteUnexpectedError(exception, error);

        Assert.Equal(
            $"katlang: unexpected error: boom {U(0x1B)}[2J{U(0x1B)}[31mred katlang: forged {U(0x202E)}txt.exe Ābols {U(0x9B)}?25l"
                + Environment.NewLine,
            error.ToString());
        AssertNoUnsafeCodeUnit(error.ToString().TrimEnd('\r', '\n'), allowLineFeeds: false);
    }

    [Fact]
    public async Task UnexpectedError_ThroughTheBoundary_IsEscaped()
    {
        var error = new StringWriter();
        var exception = new InvalidOperationException($"bad {Esc}]52;c;eA=={Bel} news");

        var exitCode = await CliApplication.RunAsync(["--help"], new ThrowingTextWriter(exception), error);

        Assert.Equal(Failure, exitCode);
        Assert.Equal(
            $"katlang: unexpected error: bad {U(0x1B)}]52;c;eA=={U(0x07)} news" + Environment.NewLine,
            error.ToString());
    }

    [Fact]
    public void UnexpectedError_WithOnlyControls_IsShownNotReplaced()
    {
        var error = new StringWriter();

        CliApplication.WriteUnexpectedError(new InvalidOperationException($"{Esc}"), error);

        Assert.Equal($"katlang: unexpected error: {U(0x1B)}" + Environment.NewLine, error.ToString());
    }

    [Theory]
    [InlineData(0x0009)]
    [InlineData(0x000B)]
    [InlineData(0x000C)]
    [InlineData(0x0085)]
    [InlineData(0x2028)]
    [InlineData(0x2029)]
    public void UnexpectedError_DoesNotTrimAwayUnsafeCharacters(int codeUnit)
    {
        var error = new StringWriter();

        CliApplication.WriteUnexpectedError(new InvalidOperationException($" {(char)codeUnit}body{(char)codeUnit} "), error);

        Assert.Equal($"katlang: unexpected error: {U(codeUnit)}body{U(codeUnit)}" + Environment.NewLine, error.ToString());
    }

    // ── T10: parser diagnostics ─────────────────────────────────────────────

    [Fact]
    public async Task ParserDiagnostics_ForControlAndFormatCharacters_AreSafe_AndTheStructuredDataIsUnchanged()
    {
        var source = $"1 +{Esc}[31m{(char)0x202E}";

        var cli = await Cli.InvokeAsync("eval", source);

        Assert.Equal(Failure, cli.ExitCode);
        Assert.Equal("", cli.Output);
        AssertSafeStderr(cli);

        var parsed = Parser.Parse(source);
        var first = parsed.Diagnostics[0];
        Assert.Equal(DiagnosticCode.UnexpectedCharacter, first.Code);
        Assert.Equal(1, first.Span!.Value.Start.Line);
        Assert.Equal(4, first.Span!.Value.Start.Column);
        Assert.StartsWith("[1:4] ", cli.TrimmedError);

        // The CLI's stderr is exactly the library's rendering whenever that rendering is safe —
        // one line per diagnostic, in the library's order.
        var expected = string.Join(
            "\n",
            parsed.Diagnostics.Select(d => TerminalSafeText.EscapeLine(KatLangError.FromDiagnostic(d).ToString())));
        Assert.Equal(expected, cli.TrimmedError);
    }

    [Fact]
    public async Task Check_ForControlCharacters_IsSafe()
    {
        using var file = new TempSourceFile($"x{Esc} = 1\ny = {(char)0x2066}2");

        var result = await Cli.InvokeAsync("check", file.Path);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        AssertSafeStderr(result);
        Assert.StartsWith("[1:2] ", result.TrimmedError);
    }

    // ── T11: evaluation diagnostics ─────────────────────────────────────────

    [Fact]
    public async Task EvaluationError_EchoingAHostileString_IsEscaped_AndItsStructuredDataIsUnchanged()
    {
        // The if-condition type mismatch echoes the offending string value verbatim.
        var source = $"if('a{Esc}[2J{Csi8}31m{(char)0x202E}', 1, 2)";
        Assert.False(Parser.Parse(source).HasErrors);

        var cli = await Cli.InvokeAsync("eval", source);

        Assert.Equal(Failure, cli.ExitCode);
        Assert.Equal("", cli.Output);
        Assert.EndsWith($"'a{U(0x1B)}[2J{U(0x9B)}31m{U(0x202E)}'", cli.TrimmedError);
        AssertSafeStderr(cli);

        var run = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(run.Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.NotNull(error.Source);
        // The library keeps the original text: escaping is CLI presentation only.
        Assert.Contains($"'a{Esc}[2J{Csi8}31m{(char)0x202E}'", error.Message);
        Assert.Equal(TerminalSafeText.EscapeLine(run.ToDisplayString()), cli.TrimmedError);
    }

    [Fact]
    public async Task EvaluationError_CannotForgeAnotherDiagnosticLine()
    {
        const string source = "if(\"safe\\n[1:1] FORGED\\nDid you mean 'fake'?\", 1, 2)";
        Assert.False(Parser.Parse(source).HasErrors);

        var cli = await Cli.InvokeAsync("eval", source);

        Assert.Equal(Failure, cli.ExitCode);
        Assert.Equal("", cli.Output);
        Assert.Single(cli.TrimmedError.Split('\n'));
        Assert.Contains($"safe{U(10)}[1:1] FORGED{U(10)}Did you mean 'fake'?", cli.TrimmedError);
        AssertSafeStderr(cli);
        var run = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var diagnostic = Assert.Single(run.Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, diagnostic.Code);
        Assert.Contains("safe\n[1:1] FORGED\nDid you mean 'fake'?", diagnostic.Message);
        Assert.Equal(TerminalSafeText.EscapeLine(run.ToDisplayString()), cli.TrimmedError);
    }

    [Fact]
    public async Task OrdinaryEvaluationError_IsUnchanged()
    {
        var result = await Cli.InvokeAsync("eval", "1/0");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("[1:1] Division by zero" + Environment.NewLine, result.Error);
    }

    // ── SEC-S2: the CLI and the public library render diagnostics alike ────

    public static TheoryData<string> PublicRenderingPrograms => new()
    {
        $"if('a{Esc}[2J{Csi8}31m{(char)0x202E}', 1, 2)",
        "if(\"safe" + (char)0x5C + "n[1:1] FORGED\", 1, 2)",
        $"1 +{Esc}[31m{(char)0x202E}",
        "Value = 1\nValeu + 1",
        "F(x) = x\nG(y) = F\nG(1)",
        "1/0",
    };

    /// <summary>
    /// For the same errors, the CLI's stderr is exactly the public
    /// <see cref="KatLangError.ToTerminalSafeString"/> rendering, one per diagnostic in run
    /// order, apart from the writer's final newline — for <c>eval</c> and for <c>check</c>.
    /// </summary>
    [Theory]
    [MemberData(nameof(PublicRenderingPrograms))]
    public async Task CliStderr_EqualsThePublicTerminalSafeRendering(string source)
    {
        var errors = KatLangEngine.Run(source) switch
        {
            RunResult.ParseFailure p => p.Errors,
            RunResult.EvalFailure e => e.Errors,
            var other => throw new Xunit.Sdk.XunitException($"expected a failure, got {other}"),
        };
        using var file = new TempSourceFile(source);

        var evaluated = await Cli.InvokeAsync("eval", source);
        var checkedFile = await Cli.InvokeAsync("check", file.Path);

        Assert.Equal(Failure, evaluated.ExitCode);
        Assert.Equal("", evaluated.Output);
        Assert.Equal(string.Join(Environment.NewLine, errors.Select(error => error.ToTerminalSafeString())) + Environment.NewLine,
            evaluated.Error);
        AssertSafeStderr(evaluated);
        var parsed = Parser.Parse(source);
        var frontEnd = parsed.Diagnostics;
        if (parsed.HasErrors)
        {
            Assert.Equal(Failure, checkedFile.ExitCode);
            Assert.Equal(
                string.Join(Environment.NewLine, frontEnd.Select(d => KatLangError.FromDiagnostic(d).ToTerminalSafeString())) + Environment.NewLine,
                checkedFile.Error);
        }
    }

    // ── T12: KatLang's multiline diagnostics ────────────────────────────────

    [Fact]
    public async Task MultilineEvaluationDiagnostic_KeepsItsLines()
    {
        var source = "Value = 1\nValeu + 1";

        var result = await Cli.InvokeAsync("eval", source);

        Assert.Equal(Failure, result.ExitCode);
        var lines = result.TrimmedError.Split('\n');
        Assert.Equal(2, lines.Length);
        Assert.StartsWith("[2:1] Identifier 'Valeu' does not resolve", lines[0]);
        Assert.Equal("Did you mean 'Value'?", lines[1]);
        Assert.Equal(KatLangEngine.Run(source).ToDisplayString() + Environment.NewLine, result.Error);
    }

    [Theory]
    [InlineData("property")]
    [InlineData("parameter")]
    [InlineData("argument")]
    [InlineData("call")]
    [InlineData("dot")]
    [InlineData("legacy")]
    public void MissingOutputNotes_KeepOnlyTheRenderersNewline(string kind)
    {
        const string hostile = "name\r\n[1:1] FORGED";
        ErrorContext context = kind switch
        {
            "property" => new PropertyEvaluationContext(hostile),
            "parameter" => new ParameterEvaluationContext(hostile),
            "argument" => new ArgumentEvaluationContext(hostile),
            "call" => new CallContext(hostile),
            "dot" => new DotCallContext(hostile, "P"),
            "legacy" => new TextErrorContext($"while evaluating property '{hostile}'"),
            _ => throw new ArgumentOutOfRangeException(nameof(kind)),
        };
        var source = new EvalError.WithContext(new CallContext("outer\nFORGED"),
            new EvalError.WithContext(context, new EvalError.MissingOutput()));
        var diagnostic = KatLangError.FromEvalError(source);
        var original = diagnostic.Message;
        var error = new StringWriter();

        new DiagnosticWriter(error).WriteDiagnostic(diagnostic);

        var lines = error.ToString().Replace("\r\n", "\n", StringComparison.Ordinal).TrimEnd('\n').Split('\n');
        Assert.Equal(2, lines.Length);
        Assert.Contains($"outer{U(10)}FORGED", lines[0]);
        Assert.Contains($"name{U(13)}{U(10)}[1:1] FORGED", lines[0]);
        Assert.StartsWith("Add an output expression", lines[1]);
        Assert.Equal(original, diagnostic.Message);
        Assert.Same(source, diagnostic.Source);
    }

    [Theory]
    [InlineData("F(x) = x\nG(y) = F\nG(1)", KatLangErrorCode.UnforwardableParameter)]
    [InlineData("F(0) = 1\nF(1) = 2\nF + 1", KatLangErrorCode.UnliftableClauseFamily)]
    [InlineData("F(0) = 1\nF(1) = 2\nW(x) = F\n0", KatLangErrorCode.UnforwardableCallable)]
    [InlineData("F(a, *xs) = a\nG(b, *ys) = b\nK = F + G\n0", KatLangErrorCode.InvalidCollectingBinding)]
    [InlineData("F(x) = y\n0", KatLangErrorCode.UndeclaredIdentifier)]
    [InlineData("F(M) = { open M\n1 }\n0", KatLangErrorCode.OpenTargetIsParameter)]
    public async Task MultilineFrontEndExplanations_AreUnchanged(string source, KatLangErrorCode code)
    {
        var run = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Contains(run.Errors, error => error.Code == code && error.Message.Contains(Environment.NewLine, StringComparison.Ordinal));
        using var file = new TempSourceFile(source);

        var evaluated = await Cli.InvokeAsync("eval", source);
        var checkedFile = await Cli.InvokeAsync("check", file.Path);

        Assert.Equal(Failure, evaluated.ExitCode);
        Assert.Equal(Failure, checkedFile.ExitCode);
        Assert.Equal(run.ToDisplayString() + Environment.NewLine, evaluated.Error);
        Assert.Equal(string.Join(Environment.NewLine, Parser.Parse(source).Diagnostics.Select(d => KatLangError.FromDiagnostic(d)))
            + Environment.NewLine, checkedFile.Error);
        AssertSafeStderr(evaluated);
        AssertSafeStderr(checkedFile);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(20)]
    [InlineData(256)]
    public void DiagnosticWriter_PreservesTheOriginalDisplayLimitDecision(int limit)
    {
        var source = $"if('{new string(Esc, 32)}', 1, 2)";
        Assert.False(Parser.Parse(source).HasErrors);
        var run = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source, new RunOptions
        {
            EvaluationLimits = new EvaluationLimits { MaxDisplayLength = limit },
        }));
        var rendering = run.RenderDisplay();
        Assert.Equal(limit < 256, rendering.LimitExceeded);
        var error = new StringWriter();

        new DiagnosticWriter(error).WriteFailure(run);

        Assert.Equal(TerminalSafeText.EscapeLine(rendering.Text) + Environment.NewLine, error.ToString());
        Assert.True(error.ToString().Length <= 6L * rendering.Text.Length + Environment.NewLine.Length);
    }

    [Fact]
    public async Task MultipleParseDiagnostics_KeepTheirLinesAndOrder_WithHostileCharacters()
    {
        var source = $"1 +{Esc}[31m";

        var result = await Cli.InvokeAsync("eval", source);

        Assert.Equal(Failure, result.ExitCode);
        AssertSafeStderr(result);
        var lines = result.TrimmedError.Split('\n');
        var diagnostics = Parser.Parse(source).Diagnostics;
        Assert.Equal(diagnostics.Count, lines.Length);
        Assert.True(lines.Length > 1);
        for (var i = 0; i < lines.Length; i++)
        {
            var span = diagnostics[i].Span!.Value.Start;
            Assert.StartsWith($"[{span.Line}:{span.Column}] ", lines[i]);
        }
    }

    // ── T13: module loading ─────────────────────────────────────────────────

    [Fact]
    public async Task ModuleLoadingFailure_KeepsKatLangsEscapes_WithoutDoubleEscaping()
    {
        const string url = "https://katlang.org/demo/cli-sec07.kat";
        var literal = "\\" + "u0041";
        ValueTask<string> Download(string _, CancellationToken __)
            => ValueTask.FromException<string>(new HttpRequestException(
                $"refused {Esc}[2J\r\nkatlang: forged {(char)0x202E} written {literal} Ābols"));

        var result = await Cli.InvokeWithDownloaderAsync(Download, "eval", $"open '{url}'\nVal\n", "--allow-loading");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        AssertSafeStderr(result);
        Assert.Single(result.TrimmedError.Split('\n'));
        Assert.Contains($"refused {U(0x1B)}[2J{U(0x0D)}{U(0x0A)}katlang: forged {U(0x202E)} written {literal} Ābols", result.TrimmedError);
        Assert.DoesNotContain("\\\\u", result.TrimmedError, StringComparison.Ordinal);
    }

    [Fact]
    public async Task DeferredModuleFailure_KeepsDiagnosticSeparatorsAndEscapedFragments()
    {
        const string source = "F(0) = 0\nF(1) = {\n    open 'https://katlang.org/a', 'https://katlang.org/b'\n    1\n}\nF(1)";
        ValueTask<string> Download(string _, CancellationToken __)
            => ValueTask.FromException<string>(new HttpRequestException($"denied {Esc}\n[1:1] FORGED"));
        var parsed = await Parser.ParseAsync(source, new RunOptions { DownloadCode = Download });
        Assert.False(parsed.HasErrors);

        var cli = await Cli.InvokeWithDownloaderAsync(Download, "eval", source, "--allow-loading");

        Assert.Equal(Failure, cli.ExitCode);
        Assert.Equal("", cli.Output);
        Assert.Equal(2, cli.TrimmedError.Split('\n').Length);
        Assert.Contains($"denied {U(27)}{U(10)}[1:1] FORGED", cli.TrimmedError);
        var run = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source, new RunOptions { DownloadCode = Download }));
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, Assert.Single(run.Errors).Code);
        Assert.Equal(run.ToDisplayString() + Environment.NewLine, cli.Error);
        AssertSafeStderr(cli);
    }

    // ── T14: successful stdout is out of scope ──────────────────────────────

    [Fact]
    public async Task SuccessfulOutput_IsTheUnmodifiedCanonicalRendering()
    {
        var source = $"'a{Esc}[31mb{Bel}{(char)0x202E}c'";

        var result = await Cli.InvokeAsync("eval", source);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("", result.Error);
        var expected = KatLangEngine.Run(source).ToDisplayString();
        Assert.Contains(Esc, expected);
        Assert.Equal(expected + Environment.NewLine, result.Output);
    }

    // ── T15: one stderr channel ─────────────────────────────────────────────

    /// <summary>
    /// The raw stderr writer is reachable only at the boundary: every other member of the CLI
    /// that writes diagnostics receives the escaping <see cref="DiagnosticWriter"/>, so a new
    /// stderr branch cannot bypass the policy without changing a signature this test pins.
    /// </summary>
    [Fact]
    public void OnlyTheBoundaryReceivesTheRawStderrWriter()
    {
        var cliTypes = typeof(CliApplication).Assembly.GetTypes()
            .Where(t => t.Namespace == typeof(CliApplication).Namespace && t != typeof(DiagnosticWriter));
        var rawWriterUses = new List<string>();
        foreach (var type in cliTypes)
        {
            const BindingFlags all = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static
                | BindingFlags.Instance | BindingFlags.DeclaredOnly;
            foreach (var method in type.GetMethods(all).Cast<MethodBase>().Concat(type.GetConstructors(all)))
            {
                foreach (var parameter in method.GetParameters())
                {
                    if (typeof(TextWriter).IsAssignableFrom(parameter.ParameterType))
                        rawWriterUses.Add($"{type.Name}.{method.Name}({parameter.Name})");
                }
            }
        }

        // RunAsync's error writer is wrapped on entry; WriteUnexpectedError's TextWriter overload
        // wraps it immediately; `output` is stdout (program output, help, version).
        Assert.Equal(
            [
                "CliApplication.ExecuteAsync(output)",
                "CliApplication.RunAsync(error)",
                "CliApplication.RunAsync(output)",
                "CliApplication.RunCoreAsync(output)",
                "CliApplication.WriteUnexpectedError(error)",
            ],
            rawWriterUses.Order(StringComparer.Ordinal));
    }

    // ── T16: bounded work ───────────────────────────────────────────────────

    [Fact]
    public void Escaping_IsLinear_InOutputAndAllocation()
    {
        static long Measure(string text, out string escaped)
        {
            TerminalSafeText.EscapeLine(text); // warm up
            var before = GC.GetAllocatedBytesForCurrentThread();
            escaped = TerminalSafeText.EscapeLine(text);
            return GC.GetAllocatedBytesForCurrentThread() - before;
        }

        var small = new string(Esc, 10_000);
        var large = new string(Esc, 40_000);

        var smallBytes = Measure(small, out var smallEscaped);
        var largeBytes = Measure(large, out var largeEscaped);

        // Each unsafe code unit becomes exactly six.
        Assert.Equal(6 * small.Length, smallEscaped.Length);
        Assert.Equal(6 * large.Length, largeEscaped.Length);
        // The result string is 12 bytes per input unit; the builder holds as much again
        // plus growth slack. Anything quadratic would be orders of magnitude above this.
        Assert.True(smallBytes <= 64L * small.Length, $"allocated {smallBytes} bytes for {small.Length} code units");
        Assert.True(largeBytes <= 64L * large.Length, $"allocated {largeBytes} bytes for {large.Length} code units");

        // Text that needs no escaping comes back as the same instance; that it costs nothing is
        // measured exactly in Escaping_SafeText_AllocatesNothing_GcIsolatedChild.
        var safe = new string('a', 40_000);
        Assert.Same(safe, TerminalSafeText.EscapeLine(safe));
    }

    /// <summary>
    /// Warmed escaping of text that needs no escaping allocates nothing, on every sample. Runs in
    /// the GC-isolated child (<see cref="GcIsolatedAllocation"/>): under a background collection
    /// the thread counter can read a phantom allocation-context remainder (CI run 39916338803
    /// read 7,096 bytes here).
    /// </summary>
    [Fact]
    public void Escaping_SafeText_AllocatesNothing_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var safe = new string('a', 40_000);
        var unsafeText = new string(Esc, 1_000);
        var safeBytes = new long[16];
        var sameInstance = new bool[safeBytes.Length];
        for (var i = 0; i < 4; i++)
            TerminalSafeText.EscapeLine(safe);
        for (var i = 0; i < safeBytes.Length; i++)
        {
            safeBytes[i] = MeasureEscape(safe, out var escaped);
            sameInstance[i] = ReferenceEquals(safe, escaped);
        }

        // The same window does observe the allocating path, so a zero above is not a dead counter.
        var unsafeBytes = MeasureEscape(unsafeText, out var unsafeEscaped);

        Assert.All(sameInstance, Assert.True);
        Assert.True(safeBytes.All(bytes => bytes == 0), "safe escaping allocated: " + string.Join(", ", safeBytes));
        Assert.Equal(6 * unsafeText.Length, unsafeEscaped.Length);
        Assert.True(unsafeBytes >= 2L * unsafeEscaped.Length, $"unsafe escaping allocated only {unsafeBytes} bytes");
        GcIsolatedAllocation.Complete();
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static long MeasureEscape(string text, out string escaped)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        escaped = TerminalSafeText.EscapeLine(text);
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    private sealed class ThrowingTextWriter(Exception exception) : TextWriter
    {
        public override Encoding Encoding => Encoding.UTF8;

        public override void Write(char value) => throw exception;

        public override void Write(string? value) => throw exception;

        public override void WriteLine(string? value) => throw exception;
    }
}
