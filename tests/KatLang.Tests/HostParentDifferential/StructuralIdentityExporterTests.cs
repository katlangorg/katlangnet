using System.Text.RegularExpressions;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// KL-07: the hand-reviewed examples of the Lean <c>kl-struct-v1</c> exporter pilot
/// (<c>lean/CoreTests/StructuralIdentity.lean</c>, <see cref="StructuralIdentityExamples"/>). The C#
/// encoder gives each example's reviewed text; the hand-written Lean module guards the same texts; and
/// the generated host-parent artifact cross-checks the Lean exporter against the C# encoder on every
/// Lean-comparable example (its successful cases are pinned by <see cref="HostParentDifferentialTests"/>).
/// </summary>
public class StructuralIdentityExporterTests
{
    private const string LeanModuleRelativePath = "lean/CoreTests/StructuralIdentity.lean";

    public static TheoryData<string> ExampleNames => new(StructuralIdentityExamples.All.Select(static e => e.Name));

    [Fact]
    public void Examples_HaveUniqueNames_AndCoverTheReviewedShapes()
    {
        var names = StructuralIdentityExamples.All.Select(static e => e.Name).ToList();
        Assert.Equal(names.Count, names.Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(["fraction-1.5", "fraction-1.50"],
            StructuralIdentityExamples.All.Where(static e => !e.LeanComparable).Select(static e => e.Name));
    }

    [Theory]
    [MemberData(nameof(ExampleNames))]
    public void CSharpEncoder_GivesTheHandReviewedText(string name)
    {
        var example = StructuralIdentityExamples.All.Single(e => e.Name == name);
        Assert.Equal(example.Expected, MetamorphicStructuralIdentity.Encode(example.Value));
        Assert.True(MetamorphicStructuralIdentity.TryDecode(example.Expected, out var decoded, out var problem), problem);
        Assert.True(Result.ValueComparer.Equals(example.Value, decoded), name);
    }

    /// <summary>
    /// Equal texts are exactly equal values over the whole table: the reviewed classes (both zeros,
    /// <c>1200</c> / <c>1200.00</c>, <c>1.5</c> / <c>1.50</c>, shared / independent subtrees) share a
    /// text, and the KL-07 pair shares only its neutral text.
    /// </summary>
    [Fact]
    public void ExampleTexts_AreEqualExactlyWhenTheValuesAre()
    {
        var examples = StructuralIdentityExamples.All;
        foreach (var left in examples)
        {
            foreach (var right in examples)
            {
                Assert.True(
                    Result.ValueComparer.Equals(left.Value, right.Value) == (left.Expected == right.Expected),
                    $"{left.Name} vs {right.Name}");
            }
        }

        string Text(string name) => examples.Single(e => e.Name == name).Expected;
        Result Value(string name) => examples.Single(e => e.Name == name).Value;
        Assert.Equal(Text("zero"), Text("negative-zero"));
        Assert.Equal(Text("integer-1200"), Text("integer-1200.00"));
        Assert.Equal(Text("fraction-1.5"), Text("fraction-1.50"));
        Assert.Equal(Text("shared-subtree"), Text("independent-subtrees"));
        Assert.Equal("L['a', 'b']", SemanticExplorerHarness.Neutral(Value("collision-two-strings")));
        Assert.Equal("L['a', 'b']", SemanticExplorerHarness.Neutral(Value("collision-one-string")));
        Assert.NotEqual(Text("collision-two-strings"), Text("collision-one-string"));
    }

    /// <summary>
    /// The hand-written Lean module guards exactly the reviewed texts of the Lean-comparable
    /// examples: every <c>encode … == some "…"</c> text there is one of them, and each of them is there.
    /// </summary>
    [Fact]
    public void LeanModule_GuardsTheReviewedTextOfEveryLeanComparableExample()
    {
        var module = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanModuleRelativePath)).ReplaceLineEndings("\n");
        var guarded = Regex.Matches(module, @"^#guard encode [^\n]*(?:\n  [^\n]*)?== some (?<text>""(?:[^""\\\n]|\\.)*"")$", RegexOptions.Multiline)
            .Select(static m => m.Groups["text"].Value)
            .ToHashSet(StringComparer.Ordinal);
        var reviewed = StructuralIdentityExamples.LeanComparable
            .Select(static e => LeanAstEncoder.QuoteString(e.Expected))
            .ToHashSet(StringComparer.Ordinal);

        Assert.Equal(reviewed.Order(StringComparer.Ordinal), guarded.Order(StringComparer.Ordinal));
    }

    /// <summary>
    /// The generated host-parent artifact cross-checks every Lean-comparable example, in table order:
    /// the C#-built value as a Lean literal, against the C# encoder's text of that value.
    /// </summary>
    [Fact]
    public void GeneratedArtifact_CrossChecksEveryLeanComparableExample()
    {
        var artifact = HostParentDifferentialTests.GenerateArtifact([HostParentDifferentialCorpus.AllCases()[0]]);
        var guards = artifact.Split('\n').Where(static line => line.StartsWith("#guard StructuralIdentity.encode ", StringComparison.Ordinal));
        var expected = StructuralIdentityExamples.LeanComparable.Select(static e =>
            $"#guard StructuralIdentity.encode {StructuralIdentityExamples.LeanLiteral(e.Value)} == some {LeanAstEncoder.QuoteString(e.Expected)}");
        Assert.Equal(expected, guards);
    }

    [Fact]
    public void LeanLiteral_WritesIntegralClassesExactly_AndRefusesWhatLeanCannotHold()
    {
        static Result Num(string text) => new Result.Atom(System.Numerics.Decimal128.Parse(text, System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture));

        Assert.Equal("(.atom 1200)", StructuralIdentityExamples.LeanLiteral(Num("1200.00")));
        Assert.Equal("(.atom 1200)", StructuralIdentityExamples.LeanLiteral(Num("12e2")));
        Assert.Equal("(.atom 0)", StructuralIdentityExamples.LeanLiteral(Num("-0")));
        Assert.Equal("(.atom (-120))", StructuralIdentityExamples.LeanLiteral(Num("-120")));
        Assert.Equal(
            "(.sequenceValue [(.listValue [(.str \"a', 'b\")]), (.bool true), (.sequenceValue [])])",
            StructuralIdentityExamples.LeanLiteral(new Result.SequenceValue(
                [new Result.ListValue([new Result.Str("a', 'b")]), new Result.Bool(true), new Result.SequenceValue([])])));

        Assert.Throws<NotSupportedException>(() => StructuralIdentityExamples.LeanLiteral(Num("1.5")));
        Assert.Throws<NotSupportedException>(() => StructuralIdentityExamples.LeanLiteral(new Result.Atom(System.Numerics.Decimal128.NaN)));
        Assert.Throws<NotSupportedException>(() => StructuralIdentityExamples.LeanLiteral(new Result.Str("\uD800")));
    }
}
