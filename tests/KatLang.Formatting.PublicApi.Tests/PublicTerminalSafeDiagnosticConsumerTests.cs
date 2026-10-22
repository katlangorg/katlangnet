using System.Globalization;
using System.Reflection;
using System.Runtime.Loader;
using System.Text;
using System.Text.RegularExpressions;

namespace KatLang.Formatting.PublicApi.Tests;

[CollectionDefinition(Name, DisableParallelization = true)]
public sealed class ConsoleCaptureCollection
{
    /// <summary>Tests that redirect the process-wide console and exit code run alone.</summary>
    public const string Name = "Console capture";
}

/// <summary>
/// SEC-S2, as a NuGet consumer meets it: this assembly is not a friend of KatLang, so every
/// call here proves <see cref="KatLangError.ToTerminalSafeString"/> is public package surface.
/// The official embedding examples — the README's explicit and asynchronous handling and the
/// DemoApp — are compiled as consumer executables, run in-process with their console captured
/// in memory, and fed hostile programs: diagnostics must reach stderr terminal-safe with a
/// nonzero exit status, and successful output must reach stdout exactly as before. Hostile text
/// is built from code units and never written to a real terminal.
/// </summary>
[Collection(ConsoleCaptureCollection.Name)]
public sealed class PublicTerminalSafeDiagnosticConsumerTests
{
    private const char Esc = (char)0x1B;
    private const char Bel = (char)0x07;
    private const char Lf = (char)0x0A;
    private const char Cr = (char)0x0D;
    private const char Backslash = (char)0x5C;
    private const char Quote = (char)0x22;

    private static string U(int codeUnit) => Backslash + "u" + codeUnit.ToString("X4", CultureInfo.InvariantCulture);

    /// <summary>
    /// An evaluation failure whose quoted string carries a clear-screen sequence, an OSC title,
    /// a forged diagnostic line (KatLang's <c>\n</c> escape), and a bidirectional override.
    /// </summary>
    private static readonly string HostileEvaluation =
        $"if({Quote}x{Esc}[2J{Esc}]0;pwned{Bel}{Backslash}n[1:1] FORGED{(char)0x202E}{Quote}, 1, 2)";

    /// <summary>A front-end failure at a control character followed by a colour sequence.</summary>
    private static readonly string HostileParse = $"1 +{Esc}[31m{(char)0x202E}";

    private static void AssertTerminalSafe(string text)
    {
        for (var i = 0; i < text.Length; i++)
        {
            var ch = text[i];
            if (ch == Lf || (ch == Cr && i + 1 < text.Length && text[i + 1] == Lf))
                continue;

            if (char.IsHighSurrogate(ch) && i + 1 < text.Length && char.IsLowSurrogate(text[i + 1]))
            {
                i++;
                continue;
            }

            Assert.False(
                char.IsControl(ch) || char.IsSurrogate(ch)
                || char.GetUnicodeCategory(ch) is UnicodeCategory.Format
                    or UnicodeCategory.LineSeparator
                    or UnicodeCategory.ParagraphSeparator,
                $"unsafe code unit U+{(int)ch:X4} at index {i}");
        }
    }

    private static IReadOnlyList<KatLangError> Errors(RunResult result) => result switch
    {
        RunResult.ParseFailure p => p.Errors,
        RunResult.EvalFailure e => e.Errors,
        _ => throw new Xunit.Sdk.XunitException($"expected a failure, got {result}"),
    };

    /// <summary>What a conforming example writes to stderr: one safe rendering per error, in order.</summary>
    private static string ExpectedStderr(string source)
        => string.Concat(Errors(KatLangEngine.Run(source)).Select(error => error.ToTerminalSafeString() + Environment.NewLine));

    // ── S1 / S11: public surface ───────────────────────────────────────────

    [Fact]
    public void ToTerminalSafeString_IsOnePublicParameterlessMethod()
    {
        var method = typeof(KatLangError).GetMethod(nameof(KatLangError.ToTerminalSafeString), BindingFlags.Public | BindingFlags.Instance, Type.EmptyTypes);

        Assert.NotNull(method);
        Assert.Equal(typeof(string), method.ReturnType);
        Assert.Single(typeof(KatLangError).GetMethods(BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static),
            candidate => candidate.Name == nameof(KatLangError.ToTerminalSafeString));
        Assert.DoesNotContain(typeof(KatLangError).Assembly.GetExportedTypes(), type => type.Name == "TerminalSafeText");
    }

    [Fact]
    public void Consumer_RendersAnOrdinaryErrorLikeToString()
    {
        var error = Assert.Single(Errors(KatLangEngine.Run("1/0")));

        Assert.Equal("[1:1] Division by zero", error.ToTerminalSafeString());
        Assert.Equal(error.ToString(), error.ToTerminalSafeString());
    }

    [Fact]
    public void Consumer_EscapesAnEngineProducedHostileDiagnostic()
    {
        Assert.False(Parser.Parse(HostileEvaluation).HasErrors);
        var error = Assert.Single(Errors(KatLangEngine.Run(HostileEvaluation)));
        var message = error.Message;

        var safe = error.ToTerminalSafeString();

        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.StartsWith("[1:1] ", safe);
        Assert.DoesNotContain(Lf, safe);
        Assert.Contains($"x{U(0x1B)}[2J{U(0x1B)}]0;pwned{U(0x07)}{U(0x0A)}[1:1] FORGED{U(0x202E)}", safe);
        AssertTerminalSafe(safe);
        Assert.Equal(message, error.Message);
        Assert.Contains(Esc, error.ToString());
    }

    [Fact]
    public void Consumer_TreatsAHostCreatedDiagnosticAsUntrusted()
    {
        var diagnostic = new Diagnostic("first" + Environment.NewLine + "[1:1] forged", DiagnosticSeverity.Error, null);
        var error = KatLangError.FromDiagnostic(diagnostic);

        var safe = error.ToTerminalSafeString();

        Assert.DoesNotContain(Lf, safe);
        Assert.StartsWith("first", safe);
        Assert.EndsWith("[1:1] forged", safe);
        Assert.Equal(KatLangErrorCode.Unspecified, error.Code);
        Assert.Equal($"Diagnostic {{ Message = {diagnostic.Message}, Severity = Error, Span = , Code = Unspecified }}", diagnostic.ToString());
    }

    [Fact]
    public void Consumer_TreatsARewrittenDiagnosticAsUntrusted()
    {
        var parsed = Parser.Parse("F(x) = x\nG(y) = F\nG(1)");
        var original = Assert.Single(parsed.Diagnostics,
            diagnostic => diagnostic.Code == DiagnosticCode.UnforwardableParameter);
        var separator = original.Message.IndexOf(Environment.NewLine, StringComparison.Ordinal);
        Assert.True(separator > 0);
        var originalSafe = KatLangError.FromDiagnostic(original).ToTerminalSafeString();
        Assert.Contains(Environment.NewLine, originalSafe);

        // Keep the old separator's offset while replacing its surrounding text. That position
        // alone does not make the newline in a host-rewritten message formatter-owned.
        var message = new string('x', separator) + Environment.NewLine + $"[1:1] FORGED{Esc}[2J";
        var rewritten = original with { Message = message };
        var error = KatLangError.FromDiagnostic(rewritten);

        var safe = error.ToTerminalSafeString();

        Assert.DoesNotContain(Lf, safe);
        Assert.DoesNotContain(Cr, safe);
        Assert.Contains(U(0x0A) + "[1:1] FORGED" + U(0x1B) + "[2J", safe);
        Assert.Equal(message, error.Message);
        Assert.Equal(rewritten.Span, error.Span);
        Assert.Equal(KatLangError.FromDiagnostic(original).Code, error.Code);
        Assert.Equal(originalSafe, KatLangError.FromDiagnostic(original with { }).ToTerminalSafeString());
        Assert.Equal(original, original with { Message = original.Message });
        Assert.Equal(original.GetHashCode(), (original with { Message = original.Message }).GetHashCode());
        AssertTerminalSafe(safe);
    }

    // ── S12: the official examples, compiled and run as consumers ───────────

    [Fact]
    public void ReadmeExplicitHandling_KeepsOutput_AndWritesSafeDiagnosticsToStderr()
    {
        var fence = ReadmeFence("NetSalary(1600, 2)");
        var (original, replace) = SourceLiteral(fence);

        var success = RunExample(fence, "readme-explicit-success");
        Assert.Equal(KatLangEngine.Run(original).ToDisplayString() + Environment.NewLine, success.Stdout);
        Assert.Equal("", success.Stderr);
        Assert.Equal(0, success.ExitCode);

        foreach (var hostile in new[] { HostileEvaluation, HostileParse })
            AssertSafeFailure(RunExample(replace(hostile), "readme-explicit-failure"), hostile);
    }

    [Fact]
    public void ReadmeAsyncHandling_KeepsOutput_AndWritesSafeDiagnosticsToStderr()
    {
        var fence = ReadmeFence("TaxRate");
        var call = Regex.Match(fence, "KatLangEngine\\.RunAsync\\(\"[^\"]*\"");
        Assert.True(call.Success, "the asynchronous README example passes its source as one string literal");

        var success = RunExample(fence, "readme-async-success");
        Assert.Equal("", success.Stderr);
        Assert.Equal(0, success.ExitCode);
        Assert.StartsWith("1192", success.Stdout);
        Assert.EndsWith(Environment.NewLine, success.Stdout);

        foreach (var hostile in new[] { HostileEvaluation, HostileParse })
        {
            var program = fence[..call.Index] + "KatLangEngine.RunAsync(" + CSharpLiteral(hostile) + fence[(call.Index + call.Length)..];
            AssertSafeFailure(RunExample(program, "readme-async-failure"), hostile);
        }
    }

    [Fact]
    public void ReadmeAsyncHandling_PreservesEverySuccessfulResult()
    {
        var fence = ReadmeFence("TaxRate");
        var call = Regex.Match(fence, "KatLangEngine\\.RunAsync\\(\"[^\"]*\"");
        Assert.True(call.Success);

        foreach (var source in new[] { "'ordinary output'", "[1, 2]", "", $"'x{Esc}[2Jy'" })
        {
            var result = KatLangEngine.Run(source);
            Assert.True(result is RunResult.Success or RunResult.NoProgramOutput);
            var program = fence[..call.Index] + "KatLangEngine.RunAsync(" + CSharpLiteral(source) + fence[(call.Index + call.Length)..];

            var run = RunExample(program, "readme-async-success-variants");

            Assert.Equal(result.ToDisplayString() + Environment.NewLine, run.Stdout);
            Assert.Equal("", run.Stderr);
            Assert.Equal(0, run.ExitCode);
        }
    }

    [Fact]
    public void DemoApp_KeepsOutput_AndWritesSafeDiagnosticsToStderr()
    {
        var program = File.ReadAllText(Path.Combine(RepoRoot.Find(), "src", "DemoApp", "Program.cs")).ReplaceLineEndings("\n");
        var (original, replace) = SourceLiteral(program);

        var success = RunExample(program, "demo-success");
        Assert.Equal(KatLangEngine.Run(original).ToDisplayString() + Environment.NewLine, success.Stdout);
        Assert.Equal("", success.Stderr);
        Assert.Equal(0, success.ExitCode);

        foreach (var hostile in new[] { HostileEvaluation, HostileParse })
            AssertSafeFailure(RunExample(replace(hostile), "demo-failure"), hostile);
    }

    private static void AssertSafeFailure(ExampleRun run, string hostile)
    {
        Assert.Equal("", run.Stdout);
        Assert.Equal(1, run.ExitCode);
        Assert.Equal(ExpectedStderr(hostile), run.Stderr);
        Assert.DoesNotContain(Esc, run.Stderr);
        // The evaluation error quotes the string, so its controls appear as visible escapes; the
        // front end already names an unexpected character by code point.
        Assert.Contains(hostile == HostileEvaluation ? U(0x1B) : "U+001B", run.Stderr);
        AssertTerminalSafe(run.Stderr);
    }

    // ── Harness ─────────────────────────────────────────────────────────────

    private sealed record ExampleRun(string Stdout, string Stderr, int ExitCode);

    /// <summary>The README's one C# fence containing <paramref name="marker"/>.</summary>
    private static string ReadmeFence(string marker)
    {
        var readme = File.ReadAllText(Path.Combine(RepoRoot.Find(), "README.md")).ReplaceLineEndings("\n");
        var fences = Regex.Matches(readme, @"^```c#\n(?<body>.*?)^```", RegexOptions.Multiline | RegexOptions.Singleline)
            .Select(match => match.Groups["body"].Value)
            .Where(body => body.Contains(marker, StringComparison.Ordinal))
            .ToList();
        return Assert.Single(fences);
    }

    /// <summary>
    /// The KatLang program of a <c>var source = """ … """;</c> raw literal, and a function that
    /// replaces the whole literal with another program.
    /// </summary>
    private static (string Source, Func<string, string> Replace) SourceLiteral(string program)
    {
        var literal = Regex.Match(program, "var source = \"\"\"\n(?<body>.*?)\n(?<indent>[ ]*)\"\"\";", RegexOptions.Singleline);
        Assert.True(literal.Success, "the example declares its program as one raw string literal");
        var indent = literal.Groups["indent"].Value;
        var source = string.Join("\n", literal.Groups["body"].Value.Split('\n')
            .Select(line => line.StartsWith(indent, StringComparison.Ordinal) ? line[indent.Length..] : line));
        return (source, replacement =>
            program[..literal.Index] + "var source = " + CSharpLiteral(replacement) + ";" + program[(literal.Index + literal.Length)..]);
    }

    /// <summary>A C# string literal for <paramref name="text"/> that spells every non-printable code unit as an escape.</summary>
    private static string CSharpLiteral(string text)
    {
        var builder = new StringBuilder().Append(Quote);
        foreach (var ch in text)
        {
            if (ch is >= ' ' and <= '~' && ch != Quote && ch != Backslash)
                builder.Append(ch);
            else
                builder.Append(U(ch));
        }

        return builder.Append(Quote).ToString();
    }

    /// <summary>
    /// Compiles <paramref name="program"/> as a consumer executable with the SDK's implicit usings,
    /// runs its entry point in a collectible load context with stdout and stderr captured in memory,
    /// and restores the console and process exit code afterwards.
    /// </summary>
    private static ExampleRun RunExample(string program, string probeName)
    {
        const string implicitUsings =
            "global using System;\nglobal using System.Collections.Generic;\nglobal using System.IO;\nglobal using System.Linq;\n"
            + "global using System.Net.Http;\nglobal using System.Threading;\nglobal using System.Threading.Tasks;\n";
        var (compilation, image) = ConsumerCompiler.CompileExecutable(implicitUsings + program, probeName);
        Assert.True(compilation.ExitCode == 0 && compilation.Diagnostics.Count == 0 && image is not null,
            "The example must compile as a consumer executable:\n" + compilation.Output);

        var context = new AssemblyLoadContext(probeName, isCollectible: true);
        var (previousOut, previousError, previousExitCode) = (Console.Out, Console.Error, Environment.ExitCode);
        var stdout = new StringWriter();
        var stderr = new StringWriter();
        try
        {
            var entryPoint = context.LoadFromStream(new MemoryStream(image!)).EntryPoint
                ?? throw new InvalidOperationException("The example has no entry point.");
            Console.SetOut(stdout);
            Console.SetError(stderr);
            Environment.ExitCode = 0;
            var returned = entryPoint.Invoke(null, entryPoint.GetParameters().Length == 0 ? null : [Array.Empty<string>()]);
            if (returned is Task task)
                task.GetAwaiter().GetResult();
            return new ExampleRun(stdout.ToString(), stderr.ToString(), Environment.ExitCode);
        }
        finally
        {
            Console.SetOut(previousOut);
            Console.SetError(previousError);
            Environment.ExitCode = previousExitCode;
            context.Unload();
        }
    }
}
