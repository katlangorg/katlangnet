namespace KatLang.CLI;

/// <summary>The v1 command surface.</summary>
internal enum CliCommandKind
{
    Run,
    Eval,
    Check,
    Help,
    Version,
}

/// <summary>
/// A fully parsed command line. <see cref="Argument"/> is the single positional
/// argument of the command — a file path for <c>run</c>/<c>check</c>, KatLang
/// source text for <c>eval</c> — and is empty for <c>--help</c>/<c>--version</c>.
/// </summary>
internal sealed record CliInvocation(CliCommandKind Kind, string Argument, bool AllowLoading);

/// <summary>
/// Either a parsed invocation or a user-facing message describing why the
/// command line could not be understood. Exactly one of the two is non-null.
/// </summary>
internal sealed record CommandLineParseResult(CliInvocation? Invocation, string? Error)
{
    public static CommandLineParseResult Ok(CliInvocation invocation) => new(invocation, null);

    public static CommandLineParseResult Fail(string error) => new(null, error);
}

/// <summary>
/// The whole v1 grammar:
/// <c>katlang (run &lt;file&gt; | eval &lt;source&gt; | check &lt;file&gt;) [--allow-loading]</c>
/// plus the standalone <c>--help</c> and <c>--version</c> flags. It is small
/// enough that a hand-written parser is clearer — and dependency-free — compared
/// with a command-line framework.
/// </summary>
internal static class CommandLine
{
    public const string ProgramName = "katlang";

    public const string AllowLoadingOption = "--allow-loading";
    public const string HelpOption = "--help";
    public const string VersionOption = "--version";

    public static CommandLineParseResult Parse(IReadOnlyList<string> args)
    {
        var positionals = new List<string>();
        var allowLoading = false;
        var helpCount = 0;
        var versionCount = 0;
        var optionsEnded = false;

        foreach (var arg in args)
        {
            if (!optionsEnded && arg == "--")
            {
                optionsEnded = true;
                continue;
            }

            // ONLY a "--" prefix marks an option. A single leading "-" stays a
            // positional so that ordinary KatLang source such as `-1` survives
            // `katlang eval "-1"` unchanged. The conventional bare `--` above
            // allows a file/source argument that itself starts with two dashes.
            if (optionsEnded || !arg.StartsWith("--", StringComparison.Ordinal))
            {
                positionals.Add(arg);
                continue;
            }

            switch (arg)
            {
                case AllowLoadingOption:
                    if (allowLoading)
                        return CommandLineParseResult.Fail($"option '{AllowLoadingOption}' was specified more than once.");

                    allowLoading = true;
                    break;
                case HelpOption:
                    helpCount++;
                    break;
                case VersionOption:
                    versionCount++;
                    break;
                default:
                    return CommandLineParseResult.Fail($"unknown option '{arg}'.");
            }
        }

        if (helpCount > 1)
            return CommandLineParseResult.Fail($"option '{HelpOption}' was specified more than once.");

        if (versionCount > 1)
            return CommandLineParseResult.Fail($"option '{VersionOption}' was specified more than once.");

        if (helpCount != 0 || versionCount != 0)
        {
            if (helpCount != 0 && versionCount != 0)
                return CommandLineParseResult.Fail($"options '{HelpOption}' and '{VersionOption}' cannot be combined.");

            var option = helpCount != 0 ? HelpOption : VersionOption;
            if (allowLoading || positionals.Count != 0)
                return CommandLineParseResult.Fail($"option '{option}' cannot be combined with other arguments.");

            var globalKind = helpCount != 0 ? CliCommandKind.Help : CliCommandKind.Version;
            return CommandLineParseResult.Ok(new CliInvocation(globalKind, string.Empty, false));
        }

        if (positionals.Count == 0)
            return CommandLineParseResult.Fail("no command specified.");

        var commandName = positionals[0];
        CliCommandKind kind;
        switch (commandName)
        {
            case "run":
                kind = CliCommandKind.Run;
                break;
            case "eval":
                kind = CliCommandKind.Eval;
                break;
            case "check":
                kind = CliCommandKind.Check;
                break;
            default:
                return CommandLineParseResult.Fail($"unknown command '{commandName}'.");
        }

        if (positionals.Count == 1)
        {
            var missing = kind == CliCommandKind.Eval ? "<source>" : "<file>";
            return CommandLineParseResult.Fail($"'{commandName}' requires a {missing} argument.");
        }

        if (positionals.Count > 2)
            return CommandLineParseResult.Fail($"unexpected argument '{positionals[2]}'.");

        return CommandLineParseResult.Ok(new CliInvocation(kind, positionals[1], allowLoading));
    }
}
