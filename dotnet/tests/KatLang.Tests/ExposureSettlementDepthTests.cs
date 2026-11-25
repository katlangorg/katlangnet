namespace KatLang.Tests;

/// <summary>
/// The exposure pass settles a member read — <c>P.A</c>, or <c>A</c> through <c>open P</c> — by
/// charging the member's requirement seed, whose own member reads are settled in turn: as deep as a
/// CHAIN of such reads, which source can make arbitrarily long with no deep syntax at all (every link
/// is a sibling). The settlement therefore runs on an explicit stack of heap frames, never the host
/// stack. Before, a chain of about 470 siblings reading each other through <c>open</c> (about 590
/// through dotted reads, fewer in a debug build) overflowed a 1 MiB thread and killed the host
/// process, on HEAD as well. Pinned on a 1 MiB thread, together with the classification the whole
/// chain implies, so the fix is shown to settle every link rather than merely to return.
/// </summary>
public sealed class ExposureSettlementDepthTests
{
    private const int Length = 1000;

    /// <summary>Runs <paramref name="work"/> on a thread with exactly a 1 MiB stack: a host stack overflow would end the test run.</summary>
    private static T OnOneMebibyteStack<T>(Func<T> work)
        => AstStructuralDepthProcessTests.RunOnThreadWithStack(1024 * 1024, work);

    /// <summary>
    /// <c>P(i)</c> reads <c>A(i+1)</c> — through its own <c>open P(i+1)</c>, or as the dotted
    /// <c>P(i+1).A(i+1)</c> — and the last member is <paramref name="last"/>.
    /// </summary>
    private static string Chain(bool throughOpen, int length, string last, string indent = "", bool mixed = false)
    {
        var source = new System.Text.StringBuilder();
        for (var i = 1; i <= length; i++)
        {
            source.Append(indent).Append($"P{i} = {{\n");
            var useOpen = throughOpen || mixed && i % 2 == 1;
            if (useOpen && i < length)
                source.Append(indent).Append($"    open P{i + 1}\n");
            var value = i == length ? last : useOpen ? $"A{i + 1} + 1" : $"P{i + 1}.A{i + 1} + 1";
            if (mixed)
            {
                source.Append(indent).Append($"    Local{i} = {value}\n");
                value = $"Local{i} + 0";
            }
            source.Append(indent).Append($"    public A{i} = {value}\n");
            source.Append(indent).Append("    0\n");
            source.Append(indent).Append("}\n");
        }

        return source.ToString();
    }

    [Fact]
    public void MixedChain_PreservesEveryCapture_AndEditorReferences_OnASmallStack()
    {
        var source = "O(p) = {\n" + Chain(false, Length, "p", "    ", mixed: true) + "    0\n}\n0";
        OnOneMebibyteStack(() =>
        {
            var parsed = SourceProvenance.ParseValid(source).Parsed;
            var owner = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single().Value);
            foreach (var property in owner.Properties)
            {
                var provider = Assert.IsType<Algorithm.User>(property.Value);
                foreach (var member in provider.Properties)
                {
                    Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, member.Exposure);
                    Assert.Equal(["p"], member.RequiredAncestorParameters);
                    Assert.Equal([new CapturedParameterRequirement("p", 1)], member.CaptureRequirements);
                }
            }

            var model = KatLang.Semantics.SemanticModelBuilder.Build(parsed);
            var prefix = source[..source.IndexOf("A2 + 1", StringComparison.Ordinal)];
            var position = new SourcePosition(prefix.Count(character => character == '\n') + 1,
                prefix.Length - prefix.LastIndexOf('\n'));
            var reference = model.FindResolutionAt(position);
            Assert.NotNull(reference);
            Assert.Equal("A2", reference.ResolvedProperty?.Name);
            Assert.NotNull(reference.ResolvedDeclaration);
            return true;
        });
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void ALongChainOfMemberReads_CarriesTheFarEndsCapturedInputToEveryLink(bool throughOpen)
    {
        // The far end reads the owner's parameter, so every link that reads it — through the whole
        // chain — requires that input and is local-only to O.
        var source = "O(p) = {\n" + Chain(throughOpen, Length, "p", "    ") + "    0\n}\n0";
        var parsed = OnOneMebibyteStack(() => Parser.Parse(source));
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));

        var owner = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(static property => property.Name == "O").Value);
        foreach (var index in new[] { 1, 2, Length / 2, Length })
        {
            var provider = Assert.IsType<Algorithm.User>(owner.Properties.Single(property => property.Name == $"P{index}").Value);
            var member = provider.Properties.Single(property => property.Name == $"A{index}");
            Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, member.Exposure);
            Assert.Equal(["p"], member.RequiredAncestorParameters);
        }
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void ALongChainOfMemberReads_ThatCapturesNothing_IsExportedThroughout_AndRuns(bool throughOpen)
    {
        // The task's reproducer: a self-contained chain opened at its head.
        var source = Chain(throughOpen, Length, "5") + (throughOpen ? "R = {\n    open P1\n    A1\n}\nR" : "R = P1.A1\nR");
        var parsed = OnOneMebibyteStack(() => Parser.Parse(source));
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        foreach (var index in new[] { 1, Length })
        {
            var provider = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(property => property.Name == $"P{index}").Value);
            Assert.Equal(PropertyExposure.Exported, provider.Properties.Single(property => property.Name == $"A{index}").Exposure);
        }

        // Evaluating a thousand nested reads is the evaluator's own depth question; a short chain
        // of the same shape shows the elaboration means what it says.
        const int Short = 40;
        var shortSource = Chain(throughOpen, Short, "5") + (throughOpen ? "R = {\n    open P1\n    A1\n}\nR" : "R = P1.A1\nR");
        Assert.Equal(
            (5 + Short - 1).ToString(System.Globalization.CultureInfo.InvariantCulture),
            Assert.IsType<RunResult.Success>(OnOneMebibyteStack(() => KatLangEngine.Run(shortSource))).ToDisplayString());
    }
}
