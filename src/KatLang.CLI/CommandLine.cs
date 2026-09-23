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
/// The command options a command line wrote, each ABSENT by default, so <c>default</c> is
/// exactly "no command option was written". That is the test <c>--help</c> and
/// <c>--version</c> use to stand alone, so a new option joins it by being a field here, never
/// by being listed again. <see cref="RandomSeed"/> (<c>--random-seed</c>) and
/// <see cref="DisplayDecimals"/> (<c>--display-decimals</c>) configure evaluation and are
/// present only for the evaluating commands (<c>run</c> and <c>eval</c>).
/// </summary>
internal readonly record struct CliOptions(bool AllowLoading, long? RandomSeed, int? DisplayDecimals);

/// <summary>
/// A fully parsed command line. <see cref="Argument"/> is the single positional
/// argument of the command — a file path for <c>run</c>/<c>check</c>, KatLang
/// source text for <c>eval</c> — and is empty for <c>--help</c>/<c>--version</c>,
/// whose <see cref="Options"/> are always <c>default</c>.
/// </summary>
internal sealed record CliInvocation(CliCommandKind Kind, string Argument, CliOptions Options);

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
/// <c>katlang (run &lt;file&gt; | eval &lt;source&gt;) [--allow-loading] [--random-seed &lt;integer&gt;] [--display-decimals &lt;integer&gt;]</c>,
/// <c>katlang check &lt;file&gt; [--allow-loading]</c>,
/// plus the standalone <c>--help</c> and <c>--version</c> flags. It is small
/// enough that a hand-written parser is clearer — and dependency-free — compared
/// with a command-line framework.
///
/// <para>Options may appear anywhere before the bare <c>--</c> terminator — before the
/// command, between the command and its operand, or after the operand — and compose
/// independently of their order. Every option may be written at most once. ONLY a
/// <c>--</c> prefix marks an option; everything after the terminator is positional.</para>
///
/// <para>The value-taking options (<c>--random-seed</c>, <c>--display-decimals</c>) share ONE value
/// rule (<see cref="TryTakeValue"/>) and ONE integer spelling (<see cref="IntegerValueStyle"/>).
/// The value is the NEXT token only (<c>--random-seed=5</c> is an unknown option like any other
/// unrecognized <c>--</c> spelling). A following token that is missing, the bare <c>--</c>
/// terminator, or another <c>--</c> option is a missing value, never consumed; a single-dash
/// token such as <c>-5</c> is a value (single dashes never introduce options in this CLI), and
/// so is any word — it is tried where it appears, never searched for. The value is an integer
/// in the invariant culture with an optional leading sign
/// (<see cref="NumberStyles.AllowLeadingSign"/>), so <c>+5</c> and <c>05</c> spell 5;
/// decimals, exponents, hex, digit separators, whitespace, and overflow are rejected, and so is
/// an integer outside the option's range — <c>--random-seed</c> accepts every signed 64-bit
/// integer, <c>--display-decimals</c> exactly KatLang's display-decimals range
/// (0 through <see cref="RunOptions.MaxDisplayDecimals"/>), never clamped. A value is parsed and
/// validated where it appears, BEFORE the command it applies to is known, so a malformed value
/// is reported ahead of <c>check</c>'s refusal of the option.</para>
/// </summary>
internal static class CommandLine
{
    public const string ProgramName = "katlang";

    public const string AllowLoadingOption = "--allow-loading";
    public const string RandomSeedOption = "--random-seed";
    public const string DisplayDecimalsOption = "--display-decimals";
    public const string HelpOption = "--help";
    public const string VersionOption = "--version";

    /// <summary>The one integer spelling of every numeric option value; see the class remarks.</summary>
    private const NumberStyles IntegerValueStyle = NumberStyles.AllowLeadingSign;

    public static CommandLineParseResult Parse(IReadOnlyList<string> args)
    {
        var positionals = new List<string>();
        var allowLoading = false;
        long? randomSeed = null;
        int? displayDecimals = null;
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
                        return SpecifiedMoreThanOnce(AllowLoadingOption);

                    allowLoading = true;
                    break;
                case RandomSeedOption:
                    if (randomSeed is not null)
                        return SpecifiedMoreThanOnce(RandomSeedOption);

                    if (!TryTakeValue(args, ref index, out var seedText))
                        return RequiresAValue(RandomSeedOption);

                    if (!long.TryParse(seedText, IntegerValueStyle, CultureInfo.InvariantCulture, out var seed))
                        return RequiresAnIntegerBetween(RandomSeedOption, long.MinValue, long.MaxValue, seedText);

                    randomSeed = seed;
                    break;
                case DisplayDecimalsOption:
                    if (displayDecimals is not null)
                        return SpecifiedMoreThanOnce(DisplayDecimalsOption);

                    if (!TryTakeValue(args, ref index, out var decimalsText))
                        return RequiresAValue(DisplayDecimalsOption);

                    // KatLang owns the range (RunOptions.MaxDisplayDecimals, shared with the
                    // DisplayDecimals property); checking it here makes an out-of-range count
                    // a usage error like any malformed value, never an exception or a clamp.
                    if (!int.TryParse(decimalsText, IntegerValueStyle, CultureInfo.InvariantCulture, out var decimals)
                        || decimals is < 0 or > RunOptions.MaxDisplayDecimals)
                    {
                        return RequiresAnIntegerBetween(DisplayDecimalsOption, 0, RunOptions.MaxDisplayDecimals, decimalsText);
                    }

                    displayDecimals = decimals;
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

        var options = new CliOptions(allowLoading, randomSeed, displayDecimals);

        if (helpCount > 1)
            return SpecifiedMoreThanOnce(HelpOption);

        if (versionCount > 1)
            return SpecifiedMoreThanOnce(VersionOption);

        if (helpCount != 0 || versionCount != 0)
        {
            if (helpCount != 0 && versionCount != 0)
                return CommandLineParseResult.Fail($"options '{HelpOption}' and '{VersionOption}' cannot be combined.");

            var option = helpCount != 0 ? HelpOption : VersionOption;
            if (options != default || positionals.Count != 0)
                return CommandLineParseResult.Fail($"option '{option}' cannot be combined with other arguments.");

            var globalKind = helpCount != 0 ? CliCommandKind.Help : CliCommandKind.Version;
            return CommandLineParseResult.Ok(new CliInvocation(globalKind, string.Empty, default));
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

        // --random-seed and --display-decimals configure evaluation; `check` validates without
        // evaluating (and so displays nothing), so they have nothing to apply to there and
        // are refused rather than ignored — the seed first when both were written.
        if (kind == CliCommandKind.Check)
        {
            if (randomSeed is not null)
                return NotValidForCheck(RandomSeedOption);

            if (displayDecimals is not null)
                return NotValidForCheck(DisplayDecimalsOption);
        }

        return CommandLineParseResult.Ok(new CliInvocation(kind, positionals[1], options));
    }

    /// <summary>
    /// The ONE value rule of every value-taking option: the value is the NEXT token, and only a
    /// token that cannot be an option. A missing token, the bare <c>--</c> terminator, or any
    /// other <c>--</c> spelling is a missing value and is never consumed, so a following option
    /// is never swallowed as a value. A single-dash token such as <c>-5</c> IS a value, and so
    /// is any word: the value is tried where it appears — the command name and its operand are
    /// never skipped over to find one.
    /// </summary>
    private static bool TryTakeValue(IReadOnlyList<string> args, ref int index, out string value)
    {
        if (index + 1 < args.Count && !args[index + 1].StartsWith("--", StringComparison.Ordinal))
        {
            value = args[++index];
            return true;
        }

        value = string.Empty;
        return false;
    }

    private static CommandLineParseResult SpecifiedMoreThanOnce(string option)
        => CommandLineParseResult.Fail($"option '{option}' was specified more than once.");

    private static CommandLineParseResult RequiresAValue(string option)
        => CommandLineParseResult.Fail($"option '{option}' requires a value.");

    private static CommandLineParseResult RequiresAnIntegerBetween(string option, long minimum, long maximum, string value)
        => CommandLineParseResult.Fail(
            $"option '{option}' requires an integer between {minimum.ToString(CultureInfo.InvariantCulture)} " +
            $"and {maximum.ToString(CultureInfo.InvariantCulture)}; got '{value}'.");

    private static CommandLineParseResult NotValidForCheck(string option)
        => CommandLineParseResult.Fail($"option '{option}' is not valid for 'check': check does not evaluate.");
}
