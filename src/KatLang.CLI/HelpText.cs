using System.Reflection;

namespace KatLang.CLI;

/// <summary>Static user-facing text: usage, the usage hint, and the version line.</summary>
internal static class HelpText
{
    // The transport bounds quoted under --allow-loading are HttpSourceDownloader's
    // MaxResponseBodyBytes and DownloadTimeout, and the range quoted under
    // --min-decimal-places and --max-decimal-places is KatLang's
    // RunOptions.DecimalPlacesLimit; the help tests pin them to those constants.
    public const string Usage = """
        Usage:
          katlang run <file> [--allow-loading] [--random-seed <integer>]
                             [--min-decimal-places <integer>]
                             [--max-decimal-places <integer>]
          katlang eval <source> [--allow-loading] [--random-seed <integer>]
                                [--min-decimal-places <integer>]
                                [--max-decimal-places <integer>]
          katlang check <file> [--allow-loading]

        Options:
          --allow-loading    Allow the program to download and run KatLang
                             modules (load and open '<url>').
                             Disabled by default. Modules are fetched over
                             HTTPS from katlang.org and its subdomains only;
                             redirects are refused. Each download has an
                             absolute deadline of 15 seconds for request and
                             body acquisition.
                             Each module is limited to 1 MiB (1,048,576 content
                             bytes), excluding HTTP headers and chunk framing.
                             These stricter CLI limits can refuse valid source.
                             KatLang's source-length limits still apply to
                             the decoded module text.

          --random-seed <integer>
                             Seed KatLang's random operations (Math.Random,
                             random, Math.RandomInt, randomInt) so that run and
                             eval reproduce the same random values for the same
                             program, seed, and KatLang version. Any signed
                             64-bit integer is valid, with an optional leading
                             sign. Without a seed, random values may differ
                             between invocations. Not valid for check, which does
                             not evaluate. KatLang randomness is not
                             cryptographically secure.

          --min-decimal-places <integer>
                             The fewest digits shown after the decimal point
                             in displayed numbers, from 0 through 99: a
                             number with fewer is padded with zeros (10 shows
                             as 10.00 at 2). It never rounds. A program's own
                             MinDecimalPlaces property is a minimum too; when
                             both are set, the smaller count applies.
                             Not valid for check, which does not evaluate.

          --max-decimal-places <integer>
                             The most digits shown after the decimal point in
                             displayed numbers, from 0 through 99: a number
                             with more is rounded, ties away from zero. It
                             never pads. A program's own MaxDecimalPlaces
                             property is a maximum too; when both are set,
                             the smaller count applies.
                             Not valid for check, which does not evaluate.

                             The two options are independent, and both are
                             display only: values, calculations, and
                             comparisons are unchanged. With either one set,
                             zeros at the end of the decimal part are shown
                             only when the minimum asks for them. Set both to
                             the same count for a fixed number of places
                             (2 and 2 for money). A minimum above the maximum
                             is an error.

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
