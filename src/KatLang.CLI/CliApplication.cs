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
/// command with no program to process: it writes the program a link names
/// and stops.</para>
///
/// <para>The source of <c>run</c>, <c>check</c> and <c>source</c> comes from ONE place,
/// <see cref="TryReadProgramAsync"/>: a file, a code link decoded offline, or a program URL
/// downloaded as text (<see cref="ProgramOperand"/> tells them apart). Only how the text is
/// obtained differs; once it is in hand the command is the same for all three.</para>
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

    /// <param name="downloader">
    /// What the CLI downloads through: the program a URL operand names and, when
    /// <c>--allow-loading</c> is supplied, every module. Defaults to the guarded HTTP
    /// transport (<see cref="HttpSourceDownloader"/>); tests substitute their own, so they
    /// never touch the network. It is NEVER handed to KatLang without the flag, which is what
    /// keeps loading disabled by default, and it is never called for a file or a code link.
    /// </param>
    public static Task<int> RunAsync(
        IReadOnlyList<string> args,
        TextWriter output,
        TextWriter error,
        Func<string, CancellationToken, ValueTask<string>>? downloader = null,
        CancellationToken cancellationToken = default)
        => RunAsync(
            args,
            output,
            error,
            downloader is null ? CliDownloads.Production : CliDownloads.Through(downloader),
            cancellationToken);

    /// <summary>
    /// The same command line with every download made through <paramref name="transport"/>: a
    /// test's own instance of the real downloader, so its rules run in the test.
    /// </summary>
    internal static Task<int> RunAsync(
        IReadOnlyList<string> args,
        TextWriter output,
        TextWriter error,
        HttpSourceDownloader transport,
        CancellationToken cancellationToken = default)
        => RunAsync(args, output, error, CliDownloads.Through(transport), cancellationToken);

    private static async Task<int> RunAsync(
        IReadOnlyList<string> args,
        TextWriter output,
        TextWriter error,
        CliDownloads downloads,
        CancellationToken cancellationToken)
    {
        ArgumentNullException.ThrowIfNull(args);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);

        // The raw stderr writer stops here: everything below reports through the one
        // terminal-safe diagnostic channel (SEC-07).
        var diagnostics = new DiagnosticWriter(error);

        // With --code-link, the program text, recorded once the command has it and before the
        // command runs, so that the link line follows whatever happens next: output,
        // diagnostics, a cancellation, or an unexpected error. A usage error, or a file or
        // link that cannot be read, stops the command before it has a source, and so before
        // there is a link.
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
            }

            string source;
            if (invocation.Kind == CliCommandKind.Eval)
            {
                source = invocation.Argument;
            }
            else
            {
                var read = await TryReadProgramAsync(
                    invocation,
                    diagnostics,
                    downloads,
                    cancellationToken).ConfigureAwait(false);

                if (!read.Success)
                    return FailureExitCode;

                source = read.Source;
            }

            if (invocation.Kind == CliCommandKind.Source)
                return WriteProgram(source, output, diagnostics);

            if (invocation.Options.CodeLink)
                linkedSource = source;

            exitCode = await RunCommandAsync(
                invocation,
                source,
                output,
                diagnostics,
                downloads.Module,
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
        Func<string, CancellationToken, ValueTask<string>> moduleDownloader,
        CancellationToken cancellationToken)
    {
        // The ONE place the command options map onto the KatLang package. With
        // --allow-loading, KatLang gets the CLI's downloader and admits a module on ANY host
        // (RunOptions.AllowAnyHost): its own checks of a load / open '<url>' target stay —
        // HTTPS, no user information, a valid host name or IP literal — and which ADDRESS a
        // host may be at is the downloader's rule (public addresses only; see
        // HttpSourceDownloader). Without the flag, DownloadCode stays null and KatLang itself
        // rejects loading source with a diagnostic: a plain run never contacts a host a
        // program names. The evaluation options (run/eval only; the parser refused
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
            DownloadCode = invocation.Options.AllowLoading ? moduleDownloader : null,
            AllowAnyHost = invocation.Options.AllowLoading,
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

                // The package's canonical display form: program output is stdout, outside
                // the stderr diagnostic policy. The one thing the CLI decides is an unpaired
                // surrogate, which no byte encoding of stdout can represent (see WellFormed).
                output.WriteLine(WellFormed(rendering.Text));
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
    /// <c>source</c>: the program a link names, written to stdout EXACTLY — every code unit as
    /// it was read, control characters included, and no line break added — so that redirecting
    /// stdout to a file reproduces the program byte for byte as UTF-8. Nothing is parsed or run.
    ///
    /// <para>A program with an unpaired surrogate, which a code link can carry and UTF-8
    /// cannot, is not printed: an encoder would write U+FFFD in its place, and the file would
    /// not be the program. One line on stderr says so, nothing is written to stdout, and the
    /// command fails.</para>
    /// </summary>
    private static int WriteProgram(string source, TextWriter output, DiagnosticWriter error)
    {
        if (IndexOfUnpairedSurrogate(source, 0) >= 0)
        {
            error.WriteLine(
                $"{CommandLine.ProgramName}: cannot print the program: " +
                "it contains an unpaired surrogate, which UTF-8 cannot represent.");
            return FailureExitCode;
        }

        // The program itself, outside the stderr diagnostic policy like all program
        // output, and unlike it not a line: nothing is appended.
        output.Write(source);
        return SuccessExitCode;
    }

    /// <summary>
    /// The index, from <paramref name="start"/>, of the first surrogate code unit of
    /// <paramref name="text"/> that is not half of a pair — a high one not followed by a low
    /// one, or a low one not preceded by a high one — or -1.
    /// </summary>
    private static int IndexOfUnpairedSurrogate(string text, int start)
    {
        for (var i = start; i < text.Length; i++)
        {
            if (!char.IsSurrogate(text[i]))
                continue;

            if (!char.IsHighSurrogate(text[i]) || i + 1 == text.Length || !char.IsLowSurrogate(text[i + 1]))
                return i;

            i++;
        }

        return -1;
    }

    /// <summary>
    /// Program output as stdout can carry it: <paramref name="text"/> with every unpaired
    /// surrogate code unit replaced by U+FFFD REPLACEMENT CHARACTER. A program can hold one —
    /// a code link carries a program's code units exactly, and <c>run</c> evaluates it as it
    /// is, as the Playground does — and a string value can then put it in an output row. No
    /// byte encoding of stdout represents it, so the CLI writes the substitute every UTF-8
    /// encoder writes instead of leaving the choice to whichever encoder stdout has (a legacy
    /// code page would write a question mark). The program's VALUE is unchanged: only this
    /// rendering substitutes. Well-formed text, which is nearly all output, is returned as the
    /// same instance. Diagnostics need no such rule: the stderr channel already shows an
    /// unpaired surrogate as a visible escape (<see cref="DiagnosticWriter"/>).
    /// </summary>
    internal static string WellFormed(string text)
    {
        var index = IndexOfUnpairedSurrogate(text, 0);
        if (index < 0)
            return text;

        var builder = new System.Text.StringBuilder(text.Length);
        var copied = 0;
        do
        {
            builder.Append(text, copied, index - copied).Append((char)0xFFFD);
            copied = index + 1;
            index = IndexOfUnpairedSurrogate(text, copied);
        }
        while (index >= 0);

        return builder.Append(text, copied, text.Length - copied).ToString();
    }

    /// <summary>
    /// The source of <c>run</c>, <c>check</c> and <c>source</c>, whatever the operand names: a
    /// file, a code link or a program URL (<see cref="ProgramOperand.Classify"/>). On failure
    /// one line has been written to stderr, and nothing else: no source was read, so the
    /// command stops with no output, no usage hint, and no <c>katlang-link:</c> line.
    /// </summary>
    private static async Task<(bool Success, string Source)> TryReadProgramAsync(
        CliInvocation invocation,
        DiagnosticWriter error,
        CliDownloads downloads,
        CancellationToken cancellationToken)
    {
        var operand = invocation.Argument;
        switch (ProgramOperand.Classify(invocation.Kind, operand))
        {
            case ProgramOperandKind.CodeLink:
                return TryReadCodeLink(operand, error);

            case ProgramOperandKind.ProgramUrl:
                return await TryDownloadProgramAsync(operand, error, downloads.Program, cancellationToken)
                    .ConfigureAwait(false);

            default:
                return await TryReadSourceFileAsync(operand, error, cancellationToken).ConfigureAwait(false);
        }
    }

    /// <summary>
    /// A code link: the program is in the link, so it is decoded here, offline — the network
    /// is never touched. The link is read exactly as given (<see cref="CodeLink.DecodeLink"/>),
    /// with nothing trimmed or percent-decoded, and the program is exactly what it carries, as
    /// UTF-16 code units: nothing is stripped, so a leading U+FEFF and every line break stay,
    /// as the Playground runs it. A link that carries no program is not a usage error (the
    /// command line was valid): one line on stderr says why.
    /// </summary>
    private static (bool Success, string Source) TryReadCodeLink(string link, DiagnosticWriter error)
    {
        switch (CodeLink.DecodeLink(link))
        {
            case CodeLinkDecoding.Program program:
                return (true, program.Source);

            case CodeLinkDecoding.Refused refused:
                error.WriteLine(
                    $"{CommandLine.ProgramName}: invalid code link: {CodeLinkText.RefusalReason(refused.Reason)}");
                return (false, string.Empty);

            default:
                throw new InvalidOperationException("Unknown KatLang CodeLinkDecoding variant.");
        }
    }

    /// <summary>
    /// A program URL: the text at <see cref="ProgramUrl.DownloadAddress"/>, fetched through
    /// the CLI's downloader and its guardrails. Naming the address as the operand is the
    /// request to download it, so no option is needed; only a module a program names needs
    /// <c>--allow-loading</c>. Every failure is one exact line
    /// (<see cref="DownloadFailureLine"/>).
    /// </summary>
    private static async Task<(bool Success, string Source)> TryDownloadProgramAsync(
        string link,
        DiagnosticWriter error,
        Func<string, CancellationToken, ValueTask<string>> download,
        CancellationToken cancellationToken)
    {
        string? text = null;
        Exception? failure = null;
        try
        {
            text = await download(ProgramUrl.DownloadAddress(link), cancellationToken).ConfigureAwait(false);
        }
        catch (Exception ex) when (ex is not OperationCanceledException || !cancellationToken.IsCancellationRequested)
        {
            // Everything but the caller's own cancellation is a failed download.
            failure = ex;
        }

        if (text is not null)
            return (true, text);

        error.WriteLine(DownloadFailureLine(link, failure));
        return (false, string.Empty);
    }

    /// <summary>
    /// The ONE wording of a program URL that gave no program. The link is quoted as given
    /// (<see cref="ProgramUrl.Echo"/>), so a shared program's page is named as the user wrote
    /// it, not as the raw-code address that was downloaded:
    /// <list type="bullet">
    ///   <item><c>katlang: not found: '&lt;link&gt;'.</c> for a <c>404</c> — for a shared
    ///   program: private, unshared or unknown;</item>
    ///   <item><c>katlang: not KatLang source: '&lt;link&gt;' returned &lt;what&gt;.</c> for a response
    ///   that is not served as source text;</item>
    ///   <item><c>katlang: cannot download '&lt;link&gt;': &lt;reason&gt;</c> for everything else, with
    ///   the downloader's own sentence (<see cref="DownloadException"/>).</item>
    /// </list>
    /// </summary>
    internal static string DownloadFailureLine(string link, Exception? failure)
    {
        var quoted = ProgramUrl.Echo(link);
        return failure switch
        {
            DownloadException { Failure: DownloadFailure.UnexpectedStatus, StatusCode: System.Net.HttpStatusCode.NotFound }
                => $"{CommandLine.ProgramName}: not found: '{quoted}'.",
            DownloadException { Failure: DownloadFailure.NotKatLangSource } refused
                => $"{CommandLine.ProgramName}: not KatLang source: '{quoted}' returned {refused.Returned}.",
            DownloadException refused
                => $"{CommandLine.ProgramName}: cannot download '{quoted}': {refused.Message}",

            // Not the CLI's downloader (a substitute one): its text is not the CLI's to print.
            _ => $"{CommandLine.ProgramName}: cannot download '{quoted}': the download failed.",
        };
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

/// <summary>
/// What the CLI downloads through, as two functions of one downloader: the program a URL
/// operand names, and a module. Production's are the two entry points of the ONE guarded
/// transport, <see cref="HttpSourceDownloader.Shared"/>, which is not created until a command
/// actually downloads.
/// </summary>
internal readonly record struct CliDownloads(
    Func<string, CancellationToken, ValueTask<string>> Program,
    Func<string, CancellationToken, ValueTask<string>> Module)
{
    public static CliDownloads Production { get; } = new(
        static (url, cancellationToken) => HttpSourceDownloader.Shared.DownloadProgramAsync(url, cancellationToken),
        static (url, cancellationToken) => HttpSourceDownloader.Shared.DownloadAsync(url, cancellationToken));

    /// <summary>Both kinds through one instance of the real downloader.</summary>
    public static CliDownloads Through(HttpSourceDownloader transport)
        => new(transport.DownloadProgramAsync, transport.DownloadAsync);

    /// <summary>Both kinds through one substitute function (address to text), which applies no rule of its own.</summary>
    public static CliDownloads Through(Func<string, CancellationToken, ValueTask<string>> downloader)
        => new(downloader, downloader);
}
