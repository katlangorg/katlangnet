using System.Globalization;

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
/// <see cref="RandomSeed"/> is the <c>--seed</c> value, present only for the
/// evaluating commands (<c>run</c> and <c>eval</c>).
/// </summary>
internal sealed record CliInvocation(CliCommandKind Kind, string Argument, bool AllowLoading, long? RandomSeed);

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
/// <c>katlang (run &lt;file&gt; | eval &lt;source&gt;) [--allow-loading] [--seed &lt;integer&gt;]</c>,
/// <c>katlang check &lt;file&gt; [--allow-loading]</c>,
/// plus the standalone <c>--help</c> and <c>--version</c> flags. It is small
/// enough that a hand-written parser is clearer — and dependency-free — compared
/// with a command-line framework.
///
/// <para><c>--seed</c> takes its value as the NEXT token only (<c>--seed=5</c> is an
/// unknown option like any other unrecognized <c>--</c> spelling). The value is a
/// signed 64-bit integer in the invariant culture with an optional leading sign
/// (<see cref="NumberStyles.AllowLeadingSign"/>): <c>0</c>, <c>-5</c>, <c>+5</c>, and both
/// <see cref="long"/> extremes are accepted; decimals, exponents, hex, digit
/// separators, embedded whitespace, and overflow are rejected. A following token
/// that is missing, the bare <c>--</c> terminator, or another <c>--</c> option is a
/// missing value, never consumed; a single-dash token such as <c>-5</c> is a value
/// (single dashes never introduce options in this CLI). The value is parsed and
/// validated where it appears, BEFORE the command it applies to is known, so a
/// malformed seed is reported ahead of <c>check</c>'s refusal of the option.</para>
/// </summary>
internal static class CommandLine
{
    public const string ProgramName = "katlang";

    public const string AllowLoadingOption = "--allow-loading";
    public const string SeedOption = "--seed";
    public const string HelpOption = "--help";
    public const string VersionOption = "--version";

    public static CommandLineParseResult Parse(IReadOnlyList<string> args)
    {
        var positionals = new List<string>();
        var allowLoading = false;
        long? randomSeed = null;
        var helpCount = 0;
        var versionCount = 0;
        var optionsEnded = false;

        for (var index = 0; index < args.Count; index++)
        {
            var arg = args[index];
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
                case SeedOption:
                    if (randomSeed is not null)
                        return CommandLineParseResult.Fail($"option '{SeedOption}' was specified more than once.");

                    // The value is the next token, and only a token that cannot be an
                    // option: absent, the bare terminator, or any "--" spelling is a
                    // missing value — a following option is never swallowed as the seed.
                    if (index + 1 >= args.Count || args[index + 1] == "--"
                        || args[index + 1].StartsWith("--", StringComparison.Ordinal))
                    {
                        return CommandLineParseResult.Fail($"option '{SeedOption}' requires a value.");
                    }

                    var value = args[++index];
                    if (!long.TryParse(value, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture, out var seed))
                    {
                        return CommandLineParseResult.Fail(
                            $"option '{SeedOption}' requires an integer between {long.MinValue.ToString(CultureInfo.InvariantCulture)} " +
                            $"and {long.MaxValue.ToString(CultureInfo.InvariantCulture)}; got '{value}'.");
                    }

                    randomSeed = seed;
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
            if (allowLoading || randomSeed is not null || positionals.Count != 0)
                return CommandLineParseResult.Fail($"option '{option}' cannot be combined with other arguments.");

            var globalKind = helpCount != 0 ? CliCommandKind.Help : CliCommandKind.Version;
            return CommandLineParseResult.Ok(new CliInvocation(globalKind, string.Empty, false, null));
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

        // A seed configures evaluation; `check` validates without evaluating, so the
        // option has nothing to apply to there and is refused rather than ignored.
        if (kind == CliCommandKind.Check && randomSeed is not null)
            return CommandLineParseResult.Fail($"option '{SeedOption}' is not valid for 'check': check does not evaluate.");

        return CommandLineParseResult.Ok(new CliInvocation(kind, positionals[1], allowLoading, randomSeed));
    }
}
