using System.Reflection;

namespace KatLang.CLI;

/// <summary>Static user-facing text: usage, the usage hint, and the version line.</summary>
internal static class HelpText
{
    // The transport bounds quoted under --allow-loading are HttpSourceDownloader's
    // MaxResponseBodyBytes and DownloadTimeout, and the range quoted under
    // --display-decimals is KatLang's RunOptions.MaxDisplayDecimals; the help tests pin
    // them to those constants.
    public const string Usage = """
        Usage:
          katlang run <file> [--allow-loading] [--seed <integer>]
                             [--display-decimals <integer>]
          katlang eval <source> [--allow-loading] [--seed <integer>]
                                [--display-decimals <integer>]
          katlang check <file> [--allow-loading]

        Options:
          --allow-loading    Allow KatLang algorithms to be loaded.
                             Disabled by default. Modules are fetched over
                             HTTPS from allowed hosts only; redirects are
                             refused. Each download has an absolute deadline of
                             15 seconds for request and body acquisition.
                             Each module is limited to 1 MiB (1,048,576 content
                             bytes), excluding HTTP headers and chunk framing.
                             These stricter CLI limits can refuse valid source.
                             KatLang's source-length limits still apply to
                             the decoded module text.

          --seed <integer>   Seed KatLang's random operations (Math.Random,
                             random, Math.RandomInt, randomInt) so that run and
                             eval reproduce the same random values for the same
                             program, seed, and KatLang version. Any signed
                             64-bit integer is valid, with an optional leading
                             sign. Without a seed, random values may differ
                             between invocations. Not valid for check, which does
                             not evaluate. KatLang randomness is not
                             cryptographically secure.

          --display-decimals <integer>
                             Default number of digits shown after the decimal
                             point in displayed numbers, from 0 through 99. A
                             program's own DisplayDecimals property overrides
                             it. Display only: values, calculations, and
                             comparisons are unchanged. Not valid for check,
                             which does not evaluate.

          --version          Show the KatLang version.
          --help             Show help.

          --                 End of options: every later argument is a file or
                             source, even one that begins with two dashes
                             (katlang eval -- "--1").
        """;

    public const string UsageHint = $"Run '{CommandLine.ProgramName} {CommandLine.HelpOption}' for usage.";

    /// <summary>
    /// Reports the ONE version that identifies this distribution: the KatLang
    /// language runtime.
    ///
    /// <para>It is read from the loaded KatLang assembly rather than from the
    /// CLI's own — the project file keeps the two in lock-step from a single
    /// version property, so they are equal by construction, and reading the
    /// runtime that is genuinely executing is what makes the number meaningful
    /// in a bug report. No version is written here.</para>
    /// </summary>
    public static string VersionLine()
        => $"KatLang {DescribeVersion(typeof(KatLangEngine).Assembly)}";

    private static string DescribeVersion(Assembly assembly)
    {
        var informational = assembly
            .GetCustomAttribute<AssemblyInformationalVersionAttribute>()
            ?.InformationalVersion;

        if (!string.IsNullOrWhiteSpace(informational))
        {
            // The SDK appends "+<source-revision-id>" build metadata; the
            // package version is the part before it.
            var metadata = informational.IndexOf('+');
            return metadata >= 0 ? informational[..metadata] : informational;
        }

        return assembly.GetName().Version?.ToString() ?? "unknown";
    }
}
