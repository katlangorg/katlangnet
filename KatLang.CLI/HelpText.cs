using System.Reflection;

namespace KatLang.CLI;

/// <summary>Static user-facing text: usage, the usage hint, and the version line.</summary>
internal static class HelpText
{
    public const string Usage = """
        Usage:
          katlang run <file> [--allow-loading]
          katlang eval <source> [--allow-loading]
          katlang check <file> [--allow-loading]

        Options:
          --allow-loading    Allow KatLang algorithms to be loaded.
                             Disabled by default.

          --version          Show the KatLang version.
          --help             Show help.
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
