using KatLang.TestInfrastructure;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace KatLang.Tests;

/// <summary>
/// The source ratchet behind <see cref="SafeReadOnlyCollection{T}"/>: nothing in
/// <c>src/KatLang</c> builds a plain read-only wrapper, because a plain wrapper's non-generic
/// <c>SyncRoot</c> is the array or list it wraps (<see cref="SafeReadOnlyCollectionTests"/>).
/// <c>Array.AsReadOnly(…)</c>, <c>….AsReadOnly()</c>, <c>new ReadOnlyCollection&lt;…&gt;(…)</c>,
/// <c>ReadOnlyCollection&lt;…&gt;.Empty</c> and a class deriving from the plain collection are refused
/// outside the helper's own file and the exact allowlist below.
/// <para>
/// The allowlist is for a wrapping that publishes nothing: kind <c>C</c>, a fresh copy made for one
/// call that no one else reads, or kind <c>D</c>, internal only. Each entry carries its reason. A
/// wrapping over engine-owned or shared storage (kind A) or over a snapshot a result, error, options
/// or model object holds (kind B) is never listed: use
/// <see cref="SafeReadOnlyCollection.Over{T}(T[])"/> or
/// <see cref="SafeReadOnlyCollection.OverList{T}(IList{T})"/>. In November 2026 every wrapping was
/// converted, so the list is empty; prefer converting to adding an entry.
/// </para>
/// </summary>
public class ReadOnlyViewSourcePolicyTests
{
    private const string HelperFile = "src/KatLang/SafeReadOnlyCollection.cs";

    /// <summary>One permitted plain wrapping: the file, the trimmed source line, its kind (C or D), and why it publishes nothing.</summary>
    private sealed record Allowed(string File, string Line, char Kind, string Reason);

    private static readonly Allowed[] Allowlist = [];

    [Fact]
    public void NoSourceFile_BuildsAPlainReadOnlyWrapper()
    {
        var root = RepoRoot.Find();
        var sourceDirectory = Path.Combine(root, "src", "KatLang");
        var files = Directory.EnumerateFiles(sourceDirectory, "*.cs", SearchOption.AllDirectories)
            .Select(path => (Path: path, Relative: Path.GetRelativePath(root, path).Replace('\\', '/')))
            .Where(static file => !file.Relative.Contains("/bin/", StringComparison.Ordinal)
                && !file.Relative.Contains("/obj/", StringComparison.Ordinal))
            .ToList();

        // The evaluator, the value model and the helper are all here, so a short listing is a broken scan.
        Assert.True(files.Count > 100, $"The scan found only {files.Count} source files under {sourceDirectory}.");
        Assert.Contains(files, static file => file.Relative == HelperFile);
        Assert.Contains(files, static file => file.Relative == "src/KatLang/Result.cs");

        var found = new List<(string File, string Line, string Rule)>();
        foreach (var (path, relative) in files)
        {
            if (relative == HelperFile)
                continue;
            foreach (var (line, rule) in Scan(File.ReadAllText(path)))
                found.Add((relative, line, rule));
        }

        var unlisted = found
            .Where(static violation => !Allowlist.Any(entry => entry.File == violation.File && entry.Line == violation.Line))
            .Select(static violation => $"{violation.File}: [{violation.Rule}] {violation.Line}")
            .Order(StringComparer.Ordinal)
            .ToList();
        Assert.True(unlisted.Count == 0,
            "A plain read-only wrapper hands out its storage through ICollection.SyncRoot. Use SafeReadOnlyCollection.Over "
            + "(an array the view owns) or SafeReadOnlyCollection.OverList (a list read in place):\n"
            + string.Join("\n", unlisted));

        var stale = Allowlist
            .Where(entry => !found.Any(violation => violation.File == entry.File && violation.Line == entry.Line))
            .Select(static entry => $"{entry.File}: {entry.Line}")
            .ToList();
        Assert.True(stale.Count == 0, "Allowlist entries that match no source line (remove them):\n" + string.Join("\n", stale));
    }

    [Fact]
    public void TheAllowlist_RecordsAKindAndAReason_ForEveryEntry()
    {
        Assert.All(Allowlist, static entry =>
        {
            Assert.True(entry.Kind is 'C' or 'D', $"{entry.File}: kind {entry.Kind} is not C (fresh copy) or D (internal only).");
            Assert.False(string.IsNullOrWhiteSpace(entry.Reason), $"{entry.File}: an allowlist entry needs its reason.");
            Assert.Equal(entry.Line.Trim(), entry.Line);
        });
        Assert.Equal(Allowlist.Length, Allowlist.Select(static entry => (entry.File, entry.Line)).Distinct().Count());
    }

    [Fact]
    public void Scan_RecognizesWrappersAcrossLinesAndIgnoresTextAndTypeUses()
    {
        const string code = """
            using System.Collections.ObjectModel;
            class Test<T> : System.Collections.ObjectModel.ReadOnlyCollection<T>
            {
                string hint = "new ReadOnlyCollection<T>(x)";
                // Array.AsReadOnly(array)
                object Wrap(T[] items, List<T> list) => new object[] {
                    list
                        .AsReadOnly(),
                    Array /* owner */ .AsReadOnly<T>(items),
                    new
                        global::System.Collections.ObjectModel.ReadOnlyCollection<T>(items),
                    System.Collections.ObjectModel.ReadOnlyCollection<T>
                        .Empty
                };
                IReadOnlyList<T> AlreadySafe(T[] items) => SafeReadOnlyCollection.Over(items);
                ReadOnlyCollection<T> View { get; }
            }
            """;
        Assert.Equal(
            ["base class", "AsReadOnly", "AsReadOnly", "constructor", "Empty"],
            Scan(code).Select(found => found.Rule));
    }

    private static IEnumerable<(string Line, string Rule)> Scan(string source)
    {
        if (!source.Contains("AsReadOnly", StringComparison.Ordinal) && !source.Contains("ReadOnlyCollection", StringComparison.Ordinal))
            yield break;

        var tree = CSharpSyntaxTree.ParseText(source, CSharpParseOptions.Default.WithLanguageVersion(LanguageVersion.Preview));
        foreach (var node in tree.GetRoot().DescendantNodes())
        {
            var rule = node switch
            {
                MemberAccessExpressionSyntax { Name.Identifier.ValueText: "AsReadOnly" } => "AsReadOnly",
                MemberBindingExpressionSyntax { Name.Identifier.ValueText: "AsReadOnly" } => "AsReadOnly",
                ObjectCreationExpressionSyntax creation when IsPlainCollection(creation.Type) => "constructor",
                MemberAccessExpressionSyntax { Name.Identifier.ValueText: "Empty" } access when IsPlainCollection(access.Expression) => "Empty",
                BaseTypeSyntax parent when IsPlainCollection(parent.Type) => "base class",
                _ => null,
            };
            if (rule is not null)
                yield return (node.ToString().Trim(), rule);
        }
    }

    private static bool IsPlainCollection(SyntaxNode syntax) => syntax switch
    {
        GenericNameSyntax name => name.Identifier.ValueText == "ReadOnlyCollection",
        QualifiedNameSyntax name => IsPlainCollection(name.Right),
        AliasQualifiedNameSyntax name => IsPlainCollection(name.Name),
        MemberAccessExpressionSyntax member => IsPlainCollection(member.Name),
        _ => false,
    };
}
