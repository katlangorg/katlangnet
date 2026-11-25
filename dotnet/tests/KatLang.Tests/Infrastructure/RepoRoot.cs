namespace KatLang.TestInfrastructure;

/// <summary>Locates the repository root (the directory holding KatLang.ebnf) above the test output directory.</summary>
internal static class RepoRoot
{
    public static string Find()
    {
        var directory = AppContext.BaseDirectory;
        while (directory is not null && !File.Exists(Path.Combine(directory, "KatLang.ebnf")))
            directory = Path.GetDirectoryName(directory);

        return directory
            ?? throw new InvalidOperationException("Could not locate repo root (KatLang.ebnf) above test bin directory.");
    }
}
