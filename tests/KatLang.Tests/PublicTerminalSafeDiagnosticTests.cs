using System.Globalization;
using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// SEC-S2: <see cref="KatLangError.ToTerminalSafeString"/> is the supported terminal/plain-text
/// rendering of a diagnostic. It escapes every source-controlled fragment with the one SEC-07
/// policy (<see cref="TerminalSafeText"/>) BEFORE KatLang inserts its own structural line
/// breaks, so a program can neither send a terminal control nor forge a diagnostic line, while
/// the error's data and its raw renderings (<see cref="KatLangError.Message"/>,
/// <see cref="KatLangError.ToString"/>, <see cref="RunResult.ToDisplayString"/>) are unchanged.
/// The code-unit policy itself is pinned by the CLI's <c>TerminalSafeDiagnosticsTests</c>; this
/// suite pins the public entry point, its integration with the owning renderer, and engine-produced
/// hostile diagnostics. Hostile text is built from code units and only ever inspected in memory.
/// </summary>
public sealed class PublicTerminalSafeDiagnosticTests
{
    private const char Esc = (char)0x1B;
    private const char Bel = (char)0x07;
    private const char Csi8 = (char)0x9B;
    private const char Osc8 = (char)0x9D;
    private const char Lf = (char)0x0A;
    private const char Cr = (char)0x0D;
    private const char Backslash = (char)0x5C;

    /// <summary>The visible escape the policy renders for one UTF-16 code unit.</summary>
    private static string U(int codeUnit) => Backslash + "u" + codeUnit.ToString("X4", CultureInfo.InvariantCulture);

    /// <summary>A KatLang double-quoted string's line-break escape, spelled without a C# escape.</summary>
    private static readonly string KatLangNewLineEscape = Backslash + "n";

    /// <summary>
    /// Nothing a terminal could act on, or that hides or reorders text, except a line break —
    /// LF or CRLF — which in a safe rendering is always KatLang's own.
    /// </summary>
    private static void AssertTerminalSafe(string text)
    {
        for (var i = 0; i < text.Length; i++)
        {
            var ch = text[i];
            if (ch == Lf || (ch == Cr && i + 1 < text.Length && text[i + 1] == Lf))
                continue;

            if (char.IsHighSurrogate(ch) && i + 1 < text.Length && char.IsLowSurrogate(text[i + 1]))
            {
                Assert.NotEqual(UnicodeCategory.Format, char.GetUnicodeCategory(text, i));
                i++;
                continue;
            }

            Assert.False(
                char.IsControl(ch) || char.IsSurrogate(ch)
                || char.GetUnicodeCategory(ch) is UnicodeCategory.Format
                    or UnicodeCategory.LineSeparator
                    or UnicodeCategory.ParagraphSeparator,
                $"unsafe code unit U+{(int)ch:X4} at index {i} in: {TerminalSafeText.EscapeLine(text)}");
        }
    }

    private static int LineBreaks(string text) => text.Count(static ch => ch == Lf);

    private static KatLangError SingleEvalError(string source)
    {
        Assert.False(Parser.Parse(source).HasErrors, "the hostile program must parse cleanly");
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        return Assert.Single(failure.Errors);
    }

    // ── S1: the familiar rendering ──────────────────────────────────────────

    public static TheoryData<string> OrdinaryFailures => new()
    {
        "1/0",
        "1 +",
        "x(",
        "F(x) = x\nF()",
        "Pricee = 1\nPrice + 1",
        "if('yes', 1, 2)",
        "'text' + 1",
        "[1, 2] + 1",
        "Ķēķis = 'Ωμέγα 漢字 😀'\nif(Ķēķis, 1, 2)",
    };

    [Theory]
    [MemberData(nameof(OrdinaryFailures))]
    public void OrdinaryDiagnostics_RenderExactlyLikeToString(string source)
    {
        var errors = KatLangEngine.Run(source) switch
        {
            RunResult.ParseFailure p => p.Errors,
            RunResult.EvalFailure e => e.Errors,
            var other => throw new Xunit.Sdk.XunitException($"expected a failure, got {other}"),
        };

        Assert.NotEmpty(errors);
        foreach (var error in errors)
            Assert.Equal(error.ToString(), error.ToTerminalSafeString());
    }

    [Fact]
    public void PositionPrefixAndWording_AreKept()
    {
        var error = SingleEvalError("1/0");

        Assert.Equal("[1:1] Division by zero", error.ToTerminalSafeString());
        Assert.Equal("Division by zero", KatLangError.FromEvalError(new EvalError.DivByZero()).ToTerminalSafeString());
    }

    // ── S2 / S13: terminal sequences in engine-produced value diagnostics ──

    public static TheoryData<string, string> TerminalSequences => new()
    {
        { "clear screen and home cursor", $"{Esc}[2J{Esc}[H" },
        { "SGR colour", $"{Esc}[31mred{Esc}[0m" },
        { "OSC title with BEL", $"{Esc}]0;pwned{Bel}" },
        { "OSC hyperlink with ST", $"{Esc}]8;;https://evil.test{Esc}{Backslash}" },
        { "8-bit CSI and OSC", $"{Csi8}2J{Osc8}0;t{Bel}" },
        { "bare BEL", $"{Bel}" },
        { "backspace overwrite", $"{(char)0x08}{(char)0x08}ok" },
        { "DEL and NEL", $"{(char)0x7F}{(char)0x85}" },
    };

    /// <summary>
    /// The value-sensitive diagnostics a written program reaches: an <c>if</c> condition, a
    /// Boolean operator, and an arithmetic operator each echo the offending string.
    /// </summary>
    private static readonly string[] ValueSensitivePrograms =
    [
        "if('{0}', 1, 2)",
        "'{0}' and true",
        "'{0}' + 1",
        "['{0}', 1] + 1",
        "F(x) = x * 2\nF('{0}')",
    ];

    [Theory]
    [MemberData(nameof(TerminalSequences))]
    public void EngineValueDiagnostics_ShowTerminalSequencesVisibly(string name, string sequence)
    {
        var echoed = 0;
        foreach (var template in ValueSensitivePrograms)
        {
            var error = SingleEvalError(template.Replace("{0}", "a" + sequence + "b", StringComparison.Ordinal));

            var safe = error.ToTerminalSafeString();

            AssertTerminalSafe(safe);
            Assert.Equal(0, LineBreaks(safe));
            Assert.True(safe.Length <= 6 * error.ToString().Length, name);
            if (!error.Message.Contains(sequence, StringComparison.Ordinal))
            {
                Assert.Equal(error.ToString(), safe);
                continue;
            }

            echoed++;
            Assert.Contains("a" + TerminalSafeText.EscapeLine(sequence) + "b", safe);
            Assert.Equal(error.ToString()[..error.ToString().IndexOf(sequence, StringComparison.Ordinal)],
                safe[..safe.IndexOf(TerminalSafeText.EscapeLine(sequence), StringComparison.Ordinal)]);
        }

        // The if condition, the Boolean operator and the list operand at least quote the value.
        Assert.True(echoed >= 3, $"{name}: only {echoed} programs echoed the string");
    }

    // ── S3: a source-controlled newline cannot forge a diagnostic line ─────

    [Fact]
    public void EngineValueDiagnostic_CannotForgeADiagnosticLine()
    {
        var source = "if(\"safe" + KatLangNewLineEscape + "[1:1] no error" + KatLangNewLineEscape + "Did you mean 'x'?\", 1, 2)";
        var error = SingleEvalError(source);
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.Contains($"safe{Lf}[1:1] no error{Lf}Did you mean 'x'?", error.ToString());

        var safe = error.ToTerminalSafeString();

        Assert.Equal(0, LineBreaks(safe));
        Assert.Contains($"safe{U(0x0A)}[1:1] no error{U(0x0A)}Did you mean 'x'?", safe);
        Assert.StartsWith("[1:1] ", safe);
    }

    // ── S4: KatLang's own line breaks stay; the fragment's are escaped ─────

    [Fact]
    public void FrontEndStructure_KeepsTheSeparator_AndEscapesFragmentNewlines()
    {
        var diagnostic = new Diagnostic(
            DiagnosticMessage.JoinLines($"Explanation 'a{Lf}[1:1] FORGED'", $"Repair 'b{Cr}{Lf}X{Esc}[2J'"),
            DiagnosticSeverity.Error,
            new SourceSpan(new SourcePosition(2, 3), new SourcePosition(2, 4))) { Code = DiagnosticCode.UnforwardableParameter };
        var error = KatLangError.FromDiagnostic(diagnostic);

        var safe = error.ToTerminalSafeString();

        Assert.Equal(
            $"[2:3] Explanation 'a{U(0x0A)}[1:1] FORGED'" + Environment.NewLine + $"Repair 'b{U(0x0D)}{U(0x0A)}X{U(0x1B)}[2J'",
            safe);
        AssertTerminalSafe(safe);
    }

    [Fact]
    public void EngineFrontEndStructure_IsKept()
    {
        // A written program whose front-end diagnostic carries an explanation and a repair line.
        var errors = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("F(x) = x\nG(y) = F\nG(1)")).Errors;
        var multiline = errors.Where(error => error.Message.Contains(Environment.NewLine, StringComparison.Ordinal)).ToList();

        foreach (var error in errors)
        {
            Assert.Equal(error.ToString(), error.ToTerminalSafeString());
            AssertTerminalSafe(error.ToTerminalSafeString());
        }

        Assert.Contains(multiline, error => error.Code == KatLangErrorCode.UnforwardableParameter);
        Assert.All(multiline, error => Assert.True(LineBreaks(error.ToTerminalSafeString()) > 0));
    }

    [Fact]
    public void EvaluationStructure_KeepsTheSeparator_AndEscapesFragmentNewlines()
    {
        // Missing output under an argument context is a two-line report around a source-derived description.
        var hostile = new EvalError.WithContext(
            new ArgumentEvaluationContext($"'s{Lf}[1:1] forged{Esc}[2J'"), new EvalError.MissingOutput());
        var benign = new EvalError.WithContext(new ArgumentEvaluationContext("'s'"), new EvalError.MissingOutput());

        var safe = KatLangError.FromEvalError(hostile).ToTerminalSafeString();
        var plain = KatLangError.FromEvalError(benign).ToTerminalSafeString();

        Assert.True(LineBreaks(plain) > 0, "the missing-output report is multiline");
        Assert.Equal(LineBreaks(plain), LineBreaks(safe));
        Assert.Contains($"'s{U(0x0A)}[1:1] forged{U(0x1B)}[2J'", safe);
        AssertTerminalSafe(safe);
        Assert.Equal(KatLangError.FromEvalError(benign).ToString(), plain);
    }

    [Fact]
    public void NestedContexts_EscapeEveryLevel()
    {
        var error = new EvalError.WithContext(
            new CallContext($"F{Esc}[2J"),
            new EvalError.WithContext(new TextErrorContext($"while{Lf}[1:1] FORGED"), new EvalError.TypeMismatch($"v{Bel}")));

        var safe = KatLangError.FromEvalError(error).ToTerminalSafeString();

        Assert.Equal(0, LineBreaks(safe));
        Assert.Contains($"F{U(0x1B)}[2J", safe);
        Assert.Contains($"while{U(0x0A)}[1:1] FORGED", safe);
        Assert.Contains($"v{U(0x07)}", safe);
        AssertTerminalSafe(safe);
    }

    [Fact]
    public void InferredParameterSuggestions_KeepTheirLines()
    {
        // A misspelled name becomes an implicit parameter; the report adds a suggestion line.
        var error = SingleEvalError("Value = 1\nValeu + 1");
        var safe = error.ToTerminalSafeString();

        Assert.Equal(error.ToString(), safe);
        Assert.EndsWith(Lf + "Did you mean 'Value'?", safe);
        Assert.True(LineBreaks(safe) > 0);
    }

    // ── S5: deferred module diagnostics ─────────────────────────────────────

    [Fact]
    public void DeferredModuleDiagnostics_KeepOneLinePerDiagnostic_AndEscapeTheirFragments()
    {
        var primary = new Diagnostic(DiagnosticMessage.JoinLines($"first{Lf}[1:1] FORGED", $"repair{Esc}[2J"), DiagnosticSeverity.Error, null)
        {
            Code = DiagnosticCode.UnforwardableParameter,
        };
        var secondary = new Diagnostic($"second{Cr}{Lf}[1:1] FORGED{(char)0x202E}", DiagnosticSeverity.Error, null) { Code = DiagnosticCode.InvalidLoadUrl };
        var error = KatLangError.FromEvalError(EvalError.ModuleRegionMaterializationFailed.From([primary, secondary]));

        var safe = error.ToTerminalSafeString();

        Assert.Equal(
            $"first{U(0x0A)}[1:1] FORGED" + Environment.NewLine
            + $"repair{U(0x1B)}[2J" + Environment.NewLine
            + $"second{U(0x0D)}{U(0x0A)}[1:1] FORGED{U(0x202E)}",
            safe);
        Assert.Equal(KatLangErrorCode.UnforwardableParameter, error.Code);
    }

    [Fact]
    public void BoundedStructuredReport_KeepsOnlyItsOriginalSeparators()
    {
        var message = DiagnosticMessage.JoinLines($"first{Lf}[1:1] FORGED", new string('x', 5000));
        var bag = new DiagnosticBag(1);
        bag.Report(DiagnosticCode.UnforwardableParameter, null, message, static text => text);
        var diagnostic = Assert.Single(bag);
        var error = KatLangError.FromDiagnostic(diagnostic);

        var safe = error.ToTerminalSafeString();

        Assert.Equal(DiagnosticBag.MaxRetainedMessageLength + ExprNameRenderer.TruncationMarker.Length, diagnostic.Message.Length);
        Assert.Equal(message.Text[..DiagnosticBag.MaxRetainedMessageLength] + ExprNameRenderer.TruncationMarker, error.Message);
        Assert.StartsWith($"first{U(0x0A)}[1:1] FORGED" + Environment.NewLine, safe);
        Assert.Equal(1, LineBreaks(safe));
        Assert.EndsWith(ExprNameRenderer.TruncationMarker, safe);
        AssertTerminalSafe(safe);
    }

    // ── S6 / S7 / S14: Unicode formatting, malformed UTF-16, host diagnostics ─

    public static TheoryData<int> InvisibleOrReorderingCodeUnits => new()
    {
        0x202A, 0x202B, 0x202C, 0x202D, 0x202E,
        0x2066, 0x2067, 0x2068, 0x2069,
        0x200B, 0x200E, 0x200F, 0xFEFF,
        0x2028, 0x2029,
    };

    [Theory]
    [MemberData(nameof(InvisibleOrReorderingCodeUnits))]
    public void EngineValueDiagnostics_EscapeInvisibleAndReorderingCharacters(int codeUnit)
    {
        var error = SingleEvalError($"if('a{(char)codeUnit}b', 1, 2)");

        var safe = error.ToTerminalSafeString();

        Assert.Contains("a" + U(codeUnit) + "b", safe);
        Assert.Equal(0, LineBreaks(safe));
        AssertTerminalSafe(safe);
    }

    /// <summary>Selected by index: theory serialization would replace a lone surrogate with U+FFFD.</summary>
    private static readonly (string Text, string Expected)[] MalformedOrSupplementaryText =
    [
        ("x" + (char)0xD800 + "y", "x" + U(0xD800) + "y"),
        ("x" + (char)0xDC00 + "y", "x" + U(0xDC00) + "y"),
        ("x" + (char)0xDC00 + (char)0xD800 + "y", "x" + U(0xDC00) + U(0xD800) + "y"),
        ("end" + (char)0xD83D, "end" + U(0xD83D)),
        ("tag" + char.ConvertFromUtf32(0xE0001) + "z", "tag" + U(0xDB40) + U(0xDC01) + "z"),
    ];

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(4)]
    public void MalformedUtf16AndSupplementaryFormatCharacters_AreEscaped(int index)
    {
        var (text, expected) = MalformedOrSupplementaryText[index];
        Assert.Contains(text, static ch => char.IsSurrogate(ch));

        var fromEvaluation = KatLangError.FromEvalError(new EvalError.TypeMismatch(text));
        Assert.Equal("Type mismatch: " + expected, fromEvaluation.ToTerminalSafeString());

        var hostDiagnostic = KatLangError.FromDiagnostic(new Diagnostic(text, DiagnosticSeverity.Error, null));
        Assert.Equal(expected, hostDiagnostic.ToTerminalSafeString());
    }

    [Fact]
    public void HostCreatedDiagnostic_TreatsAllOfItsTextAsUntrusted()
    {
        var message = "first" + Environment.NewLine + $"[1:1] forged{Esc}[2J{Lf}third";
        var diagnostic = new Diagnostic(message, DiagnosticSeverity.Error, new SourceSpan(new SourcePosition(4, 2), new SourcePosition(4, 3)));
        var error = KatLangError.FromDiagnostic(diagnostic);

        var safe = error.ToTerminalSafeString();

        Assert.Equal("[4:2] " + TerminalSafeText.EscapeLine(message), safe);
        Assert.Equal(0, LineBreaks(safe));
        Assert.Equal(KatLangErrorCode.Unspecified, error.Code);
    }

    // ── S8: ordinary Unicode and escape-looking text stay as written ───────

    [Theory]
    [InlineData("Ķēķis ar ģimeni")]
    [InlineData("Ωμέγα λόγος")]
    [InlineData("漢字かな한국어")]
    [InlineData("😀 🚀 𝔸")]
    [InlineData("tab-free, ascii: ~!@#$%^&*()")]
    public void OrdinaryUnicode_IsUnchanged(string text)
    {
        var error = SingleEvalError($"if('{text}', 1, 2)");

        Assert.Equal(error.ToString(), error.ToTerminalSafeString());
        Assert.Contains(text, error.ToTerminalSafeString());
    }

    [Fact]
    public void EscapeLookingText_IsNotEscapedAgain()
    {
        var looksEscaped = U(0x1B) + "[2J";
        Assert.Equal(9, looksEscaped.Length);
        var error = SingleEvalError($"if('{looksEscaped}', 1, 2)");

        Assert.Equal(error.ToString(), error.ToTerminalSafeString());
        Assert.Contains(looksEscaped, error.ToTerminalSafeString());

        var once = TerminalSafeText.EscapeLine($"x{Esc}y");
        Assert.Same(once, TerminalSafeText.EscapeLine(once));
    }

    // ── S9 / S15: diagnostic data and raw renderings are unchanged; stable output ─

    [Fact]
    public void SafeRendering_ChangesNoErrorState_AndIsStable()
    {
        var source = $"if('a{Esc}[2J{Backslash}b{(char)0x202E}', 1, 2)";
        var run = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(run.Errors);
        var (message, code, span, origin, raw, display) = (error.Message, error.Code, error.Span, error.Source, error.ToString(), run.ToDisplayString());

        var first = error.ToTerminalSafeString();
        var second = error.ToTerminalSafeString();

        Assert.Equal(first, second);
        Assert.Equal(message, error.Message);
        Assert.Equal(code, error.Code);
        Assert.Equal(span, error.Span);
        Assert.Same(origin, error.Source);
        Assert.Equal(raw, error.ToString());
        Assert.Equal(display, run.ToDisplayString());
        Assert.Contains(Esc, error.Message);
        Assert.Contains(Esc, run.ToDisplayString());
        Assert.False(error.IsResourceLimit);
    }

    [Fact]
    public void SafeRendering_ChangesNoFrontEndDiagnostic()
    {
        var diagnostic = new Diagnostic(DiagnosticMessage.JoinLines($"a{Esc}", $"b{Lf}c"), DiagnosticSeverity.Error, null)
        {
            Code = DiagnosticCode.UnforwardableParameter,
        };
        var copy = diagnostic with { };
        var error = KatLangError.FromDiagnostic(diagnostic);
        var raw = error.ToString();

        _ = error.ToTerminalSafeString();
        _ = error.ToTerminalSafeString();

        Assert.Equal(copy, diagnostic);
        Assert.Equal(copy.Message, diagnostic.Message);
        Assert.Equal(raw, error.ToString());
        Assert.Equal(diagnostic.Message, error.Message);
        Assert.Null(error.Source);
        Assert.Null(error.Span);
    }

    [Fact]
    public void ParseFailure_OrderAndDisplay_AreUnchanged()
    {
        var source = $"1 +{Esc}[31m{(char)0x202E}";
        var run = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        var display = run.ToDisplayString();
        var codes = run.Errors.Select(error => error.Code).ToArray();

        var safe = run.Errors.Select(error => error.ToTerminalSafeString()).ToArray();

        Assert.Equal(display, run.ToDisplayString());
        Assert.Equal(codes, run.Errors.Select(error => error.Code));
        Assert.All(safe, AssertTerminalSafe);
        Assert.Equal(run.Errors.Count, safe.Length);
    }

    // ── Sweep: no formatter branch bypasses fragment escaping ──────────────

    private static readonly string HostileFragment = $"h{Esc}[2J{Cr}{Lf}[9:9] FORGED{(char)0x202E}{(char)0x2028}{(char)0xD800}";

    /// <summary>
    /// Every public evaluation-error shape, bare and under every public context (and once more
    /// under a call frame), built once with a benign string and once with a hostile one. The safe
    /// rendering of the hostile build must be terminal-safe and have exactly the benign build's
    /// line structure — so no formatter branch concatenates a source-derived string without
    /// escaping it, or lets it add a line — and the benign build must render like ToString.
    /// </summary>
    [Fact]
    public void EveryPublicErrorShape_EscapesItsFragments_AndKeepsItsLineStructure()
    {
        var benignErrors = BuildAll<EvalError>("x", typeof(EvalError.WithContext));
        var hostileErrors = BuildAll<EvalError>(HostileFragment, typeof(EvalError.WithContext));
        var benignContexts = BuildAll<ErrorContext>("x");
        var hostileContexts = BuildAll<ErrorContext>(HostileFragment);
        Assert.Equal(benignErrors.Count, hostileErrors.Count);
        Assert.Equal(benignContexts.Count, hostileContexts.Count);
        Assert.True(benignErrors.Count > 30 && benignContexts.Count > 5,
            $"the sweep reached the public shapes ({benignErrors.Count} errors, {benignContexts.Count} contexts)");

        var failures = new List<string>();
        void Check(EvalError benign, EvalError hostile)
        {
            var benignReport = KatLangError.FromEvalError(benign);
            var hostileReport = KatLangError.FromEvalError(hostile);
            var plain = benignReport.ToTerminalSafeString();
            var safe = hostileReport.ToTerminalSafeString();
            try
            {
                Assert.Equal(benignReport.ToString(), plain);
                AssertTerminalSafe(safe);
                Assert.Equal(LineBreaks(plain), LineBreaks(safe));
                Assert.Equal(hostileReport.Message, KatLangError.FromEvalError(hostile).Message);
            }
            catch (Xunit.Sdk.XunitException exception) when (failures.Count < 20)
            {
                failures.Add($"{hostile}: {exception.Message.Split(Lf)[0]}");
            }
        }

        for (var i = 0; i < benignErrors.Count; i++)
        {
            Check(benignErrors[i], hostileErrors[i]);
            for (var c = 0; c < benignContexts.Count; c++)
            {
                Check(new EvalError.WithContext(benignContexts[c], benignErrors[i]), new EvalError.WithContext(hostileContexts[c], hostileErrors[i]));
                Check(
                    new EvalError.WithContext(new CallContext("F"), new EvalError.WithContext(benignContexts[c], benignErrors[i])),
                    new EvalError.WithContext(new CallContext(HostileFragment), new EvalError.WithContext(hostileContexts[c], hostileErrors[i])));
            }
        }

        Assert.True(failures.Count == 0, "Unescaped or line-adding fragments:\n" + string.Join("\n", failures));
    }

    /// <summary>
    /// Every public sealed variant of <typeparamref name="T"/> through its widest public
    /// constructor, with <paramref name="text"/> for every string (and both items of a string
    /// list) and one ordinary value for every other parameter type.
    /// </summary>
    private static List<T> BuildAll<T>(string text, params Type[] excluded)
    {
        var built = new List<T>();
        var variants = typeof(T).Assembly.GetExportedTypes()
            .Where(type => type.IsSealed && type != typeof(T) && typeof(T).IsAssignableFrom(type) && !excluded.Contains(type))
            .OrderBy(type => type.FullName, StringComparer.Ordinal);
        foreach (var variant in variants)
        {
            var constructor = variant.GetConstructors().OrderByDescending(c => c.GetParameters().Length).First();
            var arguments = constructor.GetParameters().Select(parameter => Argument(parameter.ParameterType, variant.Name)).ToArray();
            built.Add((T)constructor.Invoke(arguments));
        }

        return built;

        object? Argument(Type type, string owner)
        {
            if (type == typeof(string)) return text;
            if (type == typeof(IReadOnlyList<string>)) return new[] { text, text };
            if (type == typeof(int)) return 2;
            if (type == typeof(long)) return 2L;
            if (type == typeof(bool)) return true;
            if (type.IsEnum) return Enum.GetValues(type).GetValue(0);
            throw new NotSupportedException(
                $"{owner} has a constructor parameter of type {type.FullName}; give it a value in {nameof(PublicTerminalSafeDiagnosticTests)}.");
        }
    }
}
