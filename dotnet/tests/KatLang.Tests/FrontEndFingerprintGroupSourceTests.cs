using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// The parser-fuzz <see cref="FrontEndFingerprint"/> sees the exact source of every structural pattern group: the
/// written extent of a clause-head group (<see cref="Pattern.SequenceValue"/>, <see cref="Pattern.ListValue"/>) and
/// the <see cref="PatternGroupSource"/> of an elaborated parameter-pattern group, filtered or not, at any depth.
/// Equality, hashing and <see cref="ParameterPattern.DisplayName"/> ignore that metadata, so before these entries a
/// moved, dropped or wrongly filtered group source left every fingerprint consumer (the frontend determinism and
/// wrapper-parity invariants, the UTF-16 relations, the parser round-trip tests) unchanged.
/// </summary>
public class FrontEndFingerprintGroupSourceTests
{
    private const string Example = "F((x, y), [a, [b, c]]) = x + y + a + b + c\nG((x, y), [3]) = x\nG(p, q) = p\nP(x, [x, a]) = x + a\nQ = P + 1\n0";

    private static string Print(Algorithm algorithm) => FrontEndFingerprint.ComputeParseResult(algorithm, []);

    private static Algorithm.User User(Algorithm root, string name)
        => Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == name).Value);

    private static Algorithm.Conditional Family(Algorithm root, string name)
        => Assert.IsType<Algorithm.Conditional>(Assert.Single(root.Properties, property => property.Name == name).Value);

    private static SourceSpan Shifted(SourceSpan span)
        => new(span.Start.Line, span.Start.Column + 1, span.End.Line, span.End.Column + 1);

    [Fact]
    public void TheFingerprint_NamesEveryGroupSource_WrittenFilteredAndNested()
    {
        var fingerprint = Print(SourceProvenance.ParseValid(Example).Root);

        // F's elaborated groups, the nested list included.
        Assert.Contains("GSeq@1,3,1,9[", fingerprint);
        Assert.Contains("GList@1,11,1,22[", fingerprint);
        Assert.Contains("GList@1,15,1,21[", fingerprint);
        // G's clause-head groups; the head's own argument list claims no location.
        Assert.Contains("PSeq@-[PSeq@2,3,2,9[", fingerprint);
        Assert.Contains("PList@2,11,2,14[", fingerprint);
        // Q's lifted list is a filtered copy of P's written [x, a].
        Assert.Contains("GList@~4,6,4,12[", fingerprint);
    }

    [Fact]
    public void TheFingerprint_IsDeterministic_AndHoldsNoProcessIdentity()
    {
        var first = Print(SourceProvenance.ParseValid(Example).Root);
        var second = Print(SourceProvenance.ParseValid(Example).Root);
        Assert.Equal(first, second);

        // A fixed text: the group entries are spans and flags only, never an id a process hands out.
        var patterns = first[(first.IndexOf("patterns[GSeq", StringComparison.Ordinal) + "patterns[".Length)..];
        Assert.StartsWith(FPatterns, patterns);
    }

    private const string FPatterns =
        "GSeq@1,3,1,9[Cap{x:Normal@1,4,1,5#collecting@-;},Cap{y:Normal@1,7,1,8#collecting@-;},];"
        + "GList@1,11,1,22[Cap{a:Normal@1,12,1,13#collecting@-;},GList@1,15,1,21[Cap{b:Normal@1,16,1,17#collecting@-;},Cap{c:Normal@1,19,1,20#collecting@-;},],];]";

    /// <summary>
    /// A span regression in an elaborated parameter-pattern group — moved, dropped, or its filtered mark flipped — is
    /// invisible to <see cref="ParameterPattern.DisplayName"/> (by which the former fingerprint printed patterns), and
    /// now changes the fingerprint. A clause-head group's span is likewise invisible to the Lean encoding.
    /// </summary>
    [Fact]
    public void AParameterPatternGroupSourceRegression_ChangesTheFingerprint()
    {
        var root = SourceProvenance.ParseValid(Example).Root;
        var f = User(root, "F");
        var sequence = Assert.IsType<SequenceValueParameterPattern>(f.ParameterPatterns[0]);
        var list = Assert.IsType<ListValueParameterPattern>(f.ParameterPatterns[1]);
        var nested = Assert.IsType<ListValueParameterPattern>(list.Items[1]);
        var written = sequence.Source!.Value;

        ParameterPattern[][] regressions =
        [
            [sequence with { Source = new PatternGroupSource(Shifted(written.OriginSpan)) }, list],
            [sequence with { Source = null }, list],
            [sequence with { Source = written with { IsFiltered = true } }, list],
            [sequence, list with { Items = [list.Items[0], nested with { Source = new PatternGroupSource(Shifted(nested.Source!.Value.OriginSpan)) }] }],
        ];

        var baseline = Print(f);
        foreach (var patterns in regressions)
        {
            var regressed = f.WithParameterPatterns(patterns);
            Assert.Equal(f.ParameterPatterns.Select(static p => p.DisplayName), Assert.IsType<Algorithm.User>(regressed).ParameterPatterns.Select(static p => p.DisplayName));
            Assert.NotEqual(baseline, Print(regressed));
        }

        Assert.Equal(baseline, Print(f.WithParameterPatterns([sequence with { }, list with { }])));
    }

    [Fact]
    public void AClausePatternGroupSpanRegression_ChangesTheFingerprint()
    {
        var family = Family(SourceProvenance.ParseValid(Example).Root, "G");
        var branch = family.Branches[0];
        var head = Assert.IsType<Pattern.SequenceValue>(branch.Pattern);
        var group = Assert.IsType<Pattern.SequenceValue>(head.Items[0]);

        Pattern[] regressions =
        [
            head with { Items = [group with { Span = Shifted(group.Span!.Value) }, head.Items[1]] },
            head with { Items = [group with { Span = null }, head.Items[1]] },
            head with { Span = group.Span },
        ];

        var baseline = Print(family);
        foreach (var pattern in regressions)
        {
            Assert.Equal(LeanAstEncoder.EncodePattern(head), LeanAstEncoder.EncodePattern(pattern));
            Assert.NotEqual(baseline, Print(family with { Branches = [branch with { Pattern = pattern }, .. family.Branches.Skip(1)] }));
        }
    }
}
