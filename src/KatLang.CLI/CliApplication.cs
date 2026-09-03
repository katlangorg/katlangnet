namespace KatLang.CLI;

/// <summary>
/// The CLI boundary: command-line arguments and output streams in, a process
/// exit code out.
///
/// <para>The pipeline is deliberately flat — parse the command line, obtain the
/// source, configure the public KatLang API, run or check, print, exit. No
/// KatLang language semantics live here: parsing, elaboration, module loading,
/// evaluation, diagnostics, and result formatting all belong to the KatLang
/// package.</para>
/// </summary>
public static class CliApplication
{
    /// <summary>Exit code for a command that completed successfully.</summary>
    public const int SuccessExitCode = 0;

    /// <summary>
    /// Exit code for every unsuccessful command — a usage error, an unreadable
    /// file, KatLang diagnostics, or a failed evaluation. v1 deliberately keeps
    /// a two-value exit contract rather than a public exit-code taxonomy.
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

        try
        {
            return await RunCoreAsync(
                args,
                output,
                error,
                loadingDownloader,
                cancellationToken).ConfigureAwait(false);
        }
        catch (OperationCanceledException) when (cancellationToken.IsCancellationRequested)
        {
            error.WriteLine($"{CommandLine.ProgramName}: cancelled.");
            return FailureExitCode;
        }
        catch (Exception ex)
        {
            WriteUnexpectedError(ex, error);
            return FailureExitCode;
        }
    }

    private static async Task<int> RunCoreAsync(
        IReadOnlyList<string> args,
        TextWriter output,
        TextWriter error,
        Func<string, CancellationToken, ValueTask<string>>? loadingDownloader,
        CancellationToken cancellationToken)
    {
        var parsed = CommandLine.Parse(args);
        if (parsed.Error is { } usageError)
        {
            error.WriteLine($"{CommandLine.ProgramName}: {usageError}");
            error.WriteLine(HelpText.UsageHint);
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
            var fileRead = await TryReadSourceFileAsync(
                invocation.Argument,
                error,
                cancellationToken).ConfigureAwait(false);

            if (!fileRead.Success)
                return FailureExitCode;

            source = fileRead.Source;
        }

        // The ONE place --allow-loading maps onto the KatLang package: with the
        // flag, KatLang gets a downloader and resolves load / open '<url>' under
        // its own host and module policy; without it, DownloadCode stays null
        // and KatLang itself rejects loading source with a diagnostic.
        var options = new RunOptions
        {
            DownloadCode = invocation.AllowLoading
                ? loadingDownloader ?? HttpSourceDownloader.DownloadAsync
                : null,
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
        TextWriter error)
    {
        var result = await KatLangEngine.RunAsync(source, options).ConfigureAwait(false);

        switch (result)
        {
            case RunResult.Success success:
                // The package's canonical display form, unmodified.
                // A successful zero-row emission is silent; an explicitly
                // emitted empty value still has one OutputRows entry and keeps
                // its terminating output newline.
                if (success.OutputRows.Count != 0)
                    output.WriteLine(success.ToDisplayString());
                return SuccessExitCode;

            case RunResult.NoProgramOutput:
                // Definitions-only and otherwise output-free programs completed
                // successfully. There is simply nothing to print.
                return SuccessExitCode;

            case RunResult.ParseFailure parseFailure:
                error.WriteLine(parseFailure.ToDisplayString());
                return FailureExitCode;

            case RunResult.EvalFailure evalFailure:
                error.WriteLine(evalFailure.ToDisplayString());
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
        TextWriter error)
    {
        var parseResult = await Parser.ParseAsync(source, options).ConfigureAwait(false);

        foreach (var diagnostic in parseResult.Diagnostics)
        {
            // KatLangError renders "[line:column] message", the same form the
            // run/eval diagnostics use.
            error.WriteLine(KatLangError.FromDiagnostic(diagnostic).ToString());
        }

        if (!parseResult.HasErrors)
            return SuccessExitCode;

        return FailureExitCode;
    }

    private static async Task<(bool Success, string Source)> TryReadSourceFileAsync(
        string path,
        TextWriter error,
        CancellationToken cancellationToken)
    {
        try
        {
            var source = await File.ReadAllTextAsync(path, cancellationToken).ConfigureAwait(false);
            return (true, source);
        }
        catch (Exception ex) when (ex is FileNotFoundException or DirectoryNotFoundException)
        {
            error.WriteLine($"{CommandLine.ProgramName}: file not found: '{path}'.");
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException
                                      or NotSupportedException or ArgumentException)
        {
            error.WriteLine($"{CommandLine.ProgramName}: cannot read file '{path}': {ex.Message}");
        }

        return (false, string.Empty);
    }

    internal static void WriteUnexpectedError(Exception exception, TextWriter error)
    {
        var message = exception.Message
            .Replace("\r\n", " ", StringComparison.Ordinal)
            .Replace('\r', ' ')
            .Replace('\n', ' ')
            .Trim();

        if (message.Length == 0)
            message = "An unexpected error occurred.";

        error.WriteLine($"{CommandLine.ProgramName}: unexpected error: {message}");
    }
}
