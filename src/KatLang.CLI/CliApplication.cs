using System.Globalization;

namespace KatLang.CLI;

/// <summary>
/// The CLI boundary: command-line arguments and output streams in, a process
/// exit code out.
///
/// <para>The pipeline is deliberately flat — parse the command line, obtain the
/// source, configure the public KatLang API, run or check, print, with
/// <c>--code-link</c> write the program's code link last, exit. No KatLang
/// language semantics live here: parsing, elaboration, module loading,
/// evaluation, diagnostics, and result formatting all belong to the KatLang
/// package, and so does the code-link format (<see cref="CodeLink"/>): the CLI
/// words its results (<see cref="CodeLinkText"/>). <c>source</c> is the one
/// command with no program to process: it writes the program a code link
/// carries and stops.</para>
/// </summary>
public static class CliApplication
{
    /// <summary>Exit code for a command that completed successfully.</summary>
    public const int SuccessExitCode = 0;

    /// <summary>
    /// Exit code for every unsuccessful command — a usage error, an unreadable
    /// file, KatLang diagnostics, a failed evaluation, or output that could not
    /// be rendered within KatLang's display limit. v1 deliberately keeps a
    /// two-value exit contract rather than a public exit-code taxonomy.
    /// </summary>
    public const int FailureExitCode = 1;

    /// <param name="loadingDownloader">
    /// The downloader used when <c>--allow-loading</c> is supplied. Defaults to
    /// the HTTP transport; tests substitute their own. It is NEVER handed to
    /// KatLang without the flag, which is what keeps loading disabled by default.
    /// </param>
    public static async Task<int> RunAsync(
        IReadOnlyList<string> args,
        TextWriter output,
        TextWriter error,
        Func<string, CancellationToken, ValueTask<string>>? loadingDownloader = null,
        CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(args);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);

        // The raw stderr writer stops here: everything below reports through the one
        // terminal-safe diagnostic channel (SEC-07).
        var diagnostics = new DiagnosticWriter(error);

        // With --code-link, the program text, recorded once the command has it and before the
        // command runs, so that the link line follows whatever happens next: output,
        // diagnostics, a cancellation, or an unexpected error. A usage or file error stops the
        // command before it has a source, and so before there is a link.
        string? linkedSource = null;
        int exitCode;
        try
        {
            var parsed = CommandLine.Parse(args);
            if (parsed.Error is { } usageError)
            {
                // The usage error quotes raw arguments; as one CLI line, any line break or
                // control character in them is escaped.
                diagnostics.WriteLine($"{CommandLine.ProgramName}: {usageError}");
                diagnostics.WriteLine(HelpText.UsageHint);
                return FailureExitCode;
            }

            var invocation = parsed.Invocation!;

            switch (invocation.Kind)
            {
                case CliCommandKind.Help:
                    output.WriteLine(HelpText.Usage);
                    return SuccessExitCode;

                case CliCommandKind.Version:
                    output.WriteLine(HelpText.VersionLine());
                    return SuccessExitCode;

                case CliCommandKind.Source:
                    return WriteLinkedProgram(invocation.Argument, output, diagnostics);
            }

            string source;
            if (invocation.Kind == CliCommandKind.Eval)
            {
                source = invocation.Argument;
            }
            else
            {
                var fileRead = await TryReadSourceFileAsync(
                    invocation.Argument,
                    diagnostics,
                    cancellationToken).ConfigureAwait(false);

                if (!fileRead.Success)
                    return FailureExitCode;

                source = fileRead.Source;
            }

            if (invocation.Options.CodeLink)
                linkedSource = source;

            exitCode = await RunCommandAsync(
                invocation,
                source,
                output,
                diagnostics,
                loadingDownloader,
                cancellationToken).ConfigureAwait(false);
        }
        catch (OperationCanceledException) when (cancellationToken.IsCancellationRequested)
        {
            diagnostics.WriteLine($"{CommandLine.ProgramName}: cancelled.");
            exitCode = FailureExitCode;
        }
        catch (Exception ex)
        {
            diagnostics.WriteUnexpectedError(ex);
            exitCode = FailureExitCode;
        }

        if (linkedSource is not null)
            exitCode = WriteCodeLink(linkedSource, output, diagnostics, exitCode);

        return exitCode;
    }

    /// <summary>
    /// <c>run</c>, <c>eval</c> and <c>check</c> once the source has been obtained: configure the
    /// public KatLang API from the command options, then run or check.
    /// </summary>
    private static async Task<int> RunCommandAsync(
        CliInvocation invocation,
        string source,
        TextWriter output,
        DiagnosticWriter error,
        Func<string, CancellationToken, ValueTask<string>>? loadingDownloader,
        CancellationToken cancellationToken)
    {
        // The ONE place the command options map onto the KatLang package. With
        // --allow-loading, KatLang gets a downloader and resolves load /
        // open '<url>' under its own host and module policy; without it,
        // DownloadCode stays null and KatLang itself rejects loading source with
        // a diagnostic. The evaluation options (run/eval only; the parser refused
        // them for check) are KatLang's own: --random-seed is RunOptions.RandomSeed,
        // and --min-decimal-places / --max-decimal-places are RunOptions.MinDecimalPlaces /
        // RunOptions.MaxDecimalPlaces, the host decimal-places settings that KatLang
        // composes with a program's own MinDecimalPlaces / MaxDecimalPlaces properties,
        // each by their minimum. An option that was not written stays null — the CLI never
        // derives one setting from the other. The CLI adds no randomness or display semantics of its own:
        // every result below is rendered by the package from the run's own display
        // configuration.
        var options = new RunOptions
        {
            DownloadCode = invocation.Options.AllowLoading
                ? loadingDownloader ?? HttpSourceDownloader.Shared.DownloadAsync
                : null,
            RandomSeed = invocation.Options.RandomSeed,
            MinDecimalPlaces = invocation.Options.MinDecimalPlaces,
            MaxDecimalPlaces = invocation.Options.MaxDecimalPlaces,
            SourceProcessingCancellationToken = cancellationToken,
            EvaluationCancellationToken = cancellationToken,
        };

        return invocation.Kind switch
        {
            CliCommandKind.Check => await CheckAsync(source, options, error)
                .ConfigureAwait(false),
            _ => await ExecuteAsync(source, options, output, error)
                .ConfigureAwait(false),
        };
    }

    /// <summary>
    /// <c>run</c> and <c>eval</c>: identical once the source has been obtained.
    /// The asynchronous engine entry point is used unconditionally — it is the
    /// one that can suspend for a module download, and it completes
    /// synchronously when nothing suspends.
    /// </summary>
    private static async Task<int> ExecuteAsync(
        string source,
        RunOptions options,
        TextWriter output,
        DiagnosticWriter error)
    {
        var result = await KatLangEngine.RunAsync(source, options).ConfigureAwait(false);

        switch (result)
        {
            case RunResult.Success success:
                // A successful zero-row emission is silent; an explicitly
                // emitted empty value still has one OutputRows entry and keeps
                // its terminating output newline.
                if (success.OutputRows.Count == 0)
                    return SuccessExitCode;

                var rendering = success.RenderDisplay();
                if (rendering.LimitExceeded)
                {
                    // The program evaluated, but its output cannot be rendered
                    // within KatLang's display limit. That is a failed command,
                    // not program output: the notice goes to stderr, stdout
                    // stays empty, and the exit code says so. The decision is
                    // structural, so a program whose genuine output happens to
                    // equal the notice text still prints it as output.
                    error.WriteDiagnostic(rendering.LimitError);
                    return FailureExitCode;
                }

                // The package's canonical display form, unmodified: program output is
                // stdout, outside the stderr diagnostic policy.
                output.WriteLine(rendering.Text);
                return SuccessExitCode;

            case RunResult.NoProgramOutput:
                // Definitions-only and otherwise output-free programs completed
                // successfully. There is simply nothing to print.
                return SuccessExitCode;

            case RunResult.ParseFailure parseFailure:
                error.WriteFailure(parseFailure);
                return FailureExitCode;

            case RunResult.EvalFailure evalFailure:
                error.WriteFailure(evalFailure);
                return FailureExitCode;

            default:
                throw new InvalidOperationException(
                    $"Unknown KatLang RunResult variant: {result.GetType().Name}.");
        }
    }

    /// <summary>
    /// <c>check</c>: the public KatLang front end WITHOUT evaluation. Parsing,
    /// load elaboration, parameter detection, implicit-argument resolution, and
    /// property-exposure resolution all run; nothing is executed.
    /// </summary>
    private static async Task<int> CheckAsync(
        string source,
        RunOptions options,
        DiagnosticWriter error)
    {
        var parseResult = await Parser.ParseAsync(source, options).ConfigureAwait(false);

        foreach (var diagnostic in parseResult.Diagnostics)
        {
            // KatLangError renders "[line:column] message", the same form the
            // run/eval diagnostics use.
            error.WriteDiagnostic(KatLangError.FromDiagnostic(diagnostic));
        }

        if (!parseResult.HasErrors)
            return SuccessExitCode;

        return FailureExitCode;
    }

    /// <summary>
    /// <c>--code-link</c>: after everything else the command wrote, the program's code link
    /// (<see cref="CodeLinkText.Line"/>) as the last line of stderr. Program output is flushed first,
    /// so a reader of both streams sees the rows before the link. The link is presentation only:
    /// stdout and the exit code stay what the command made them, unless stdout itself fails
    /// here, which is reported like any other output failure.
    /// </summary>
    private static int WriteCodeLink(string source, TextWriter output, DiagnosticWriter error, int exitCode)
    {
        try
        {
            output.Flush();
        }
        catch (Exception ex)
        {
            error.WriteUnexpectedError(ex);
            exitCode = FailureExitCode;
        }

        error.WriteLine(CodeLinkText.Line(source));
        return exitCode;
    }

    /// <summary>
    /// <c>source</c>: the program the code link <paramref name="link"/> carries, written to
    /// stdout EXACTLY — every code unit as the link carries it, control characters included,
    /// and no line break added — so that redirecting stdout to a file reproduces the program
    /// byte for byte as UTF-8. Nothing is parsed or run. The link is read exactly as given
    /// (<see cref="CodeLink.DecodeLink"/>), with nothing trimmed.
    ///
    /// <para>A link that carries no program is not a usage error (the command line was valid):
    /// one line on stderr says why, nothing is written to stdout, and the command fails. So
    /// does a program with an unpaired surrogate, which a code link can carry and UTF-8 cannot:
    /// an encoder would write U+FFFD in its place, and the file would not be the program.</para>
    /// </summary>
    private static int WriteLinkedProgram(string link, TextWriter output, DiagnosticWriter error)
    {
        switch (CodeLink.DecodeLink(link))
        {
            case CodeLinkDecoding.Program program:
                if (HasUnpairedSurrogate(program.Source))
                {
                    error.WriteLine(
                        $"{CommandLine.ProgramName}: cannot print the program: " +
                        "it contains an unpaired surrogate, which UTF-8 cannot represent.");
                    return FailureExitCode;
                }

                // The program itself, outside the stderr diagnostic policy like all program
                // output, and unlike it not a line: nothing is appended.
                output.Write(program.Source);
                return SuccessExitCode;

            case CodeLinkDecoding.Refused refused:
                error.WriteLine(
                    $"{CommandLine.ProgramName}: invalid code link: {CodeLinkText.RefusalReason(refused.Reason)}");
                return FailureExitCode;

            default:
                throw new InvalidOperationException("Unknown KatLang CodeLinkDecoding variant.");
        }
    }

    /// <summary>
    /// Whether <paramref name="text"/> has a surrogate code unit that is not half of a pair: a
    /// high one not followed by a low one, or a low one not preceded by a high one.
    /// </summary>
    private static bool HasUnpairedSurrogate(string text)
    {
        for (var i = 0; i < text.Length; i++)
        {
            if (!char.IsSurrogate(text[i]))
                continue;

            if (!char.IsHighSurrogate(text[i]) || i + 1 == text.Length || !char.IsLowSurrogate(text[i + 1]))
                return true;

            i++;
        }

        return false;
    }

    private static async Task<(bool Success, string Source)> TryReadSourceFileAsync(
        string path,
        DiagnosticWriter error,
        CancellationToken cancellationToken)
    {
        try
        {
            // Bounded while reading: an oversized, growing, or endless file is refused as
            // soon as its decoded text crosses KatLang's source-length ceiling, never read
            // whole and then measured. The refusal is the front end's own limit, worded in
            // its family; only the lower bound is known, so no total length is claimed.
            var read = await BoundedSourceReader.ReadFileAsync(
                path,
                SourceProcessingLimits.MaxSupportedSourceLength,
                cancellationToken).ConfigureAwait(false);

            if (!read.ExceedsLimit)
                return (true, read.Source!);

            error.WriteLine(SourceLengthExceededMessage(SourceProcessingLimits.MaxSupportedSourceLength));
        }
        catch (Exception ex) when (ex is FileNotFoundException or DirectoryNotFoundException)
        {
            error.WriteLine($"{CommandLine.ProgramName}: file not found: '{path}'.");
        }
        catch (ArgumentException)
        {
            // The file API rejects a malformed path SHAPE before touching the file system,
            // with a message addressed to .NET callers ("... (Parameter 'path')"), so the
            // CLI words it. The case a command line can reach is an empty path — on
            // Windows a whitespace-only one too, which the platform treats as empty.
            var reason = string.IsNullOrWhiteSpace(path) ? "the path is empty" : "the path is not valid";
            error.WriteLine($"{CommandLine.ProgramName}: cannot read file '{path}': {reason}.");
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException or NotSupportedException)
        {
            error.WriteLine($"{CommandLine.ProgramName}: cannot read file '{path}': {ex.Message}");
        }

        return (false, string.Empty);
    }

    internal static string SourceLengthExceededMessage(int limit)
        => $"Source length exceeds the maximum of {limit.ToString(CultureInfo.InvariantCulture)} UTF-16 code unit{(limit == 1 ? "" : "s")}.";

    internal static void WriteUnexpectedError(Exception exception, TextWriter error)
        => new DiagnosticWriter(error).WriteUnexpectedError(exception);
}
