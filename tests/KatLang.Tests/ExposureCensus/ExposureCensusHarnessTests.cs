namespace KatLang.Tests.ExposureCensus;

/// <summary>Negative controls for the census itself: incomplete evidence and failed programs stay visible.</summary>
public sealed class ExposureCensusHarnessTests
{
    [Fact]
    public async Task OpenProvidedHeads_ReachEveryNonOpenConsumer()
    {
        foreach (var pos in new[] { "value", "callee", "spread", "fallback" })
        {
            Assert.Null(CensusGrid.Exclusion("opened", pos, "own-used", "plain", "outside", "found", "member"));
            var @case = CensusGrid.Build(["opened", pos, "own-used", "plain", "outside", "found", "member"]);
            SourceProvenance.ParseValid(@case.Body + CensusRunner.Inside5);
            var result = await CensusRunner.Run(@case, collectLean: false);
            Assert.Null(result.Skipped);
            Assert.True(result.InsideWorks);
            Assert.StartsWith("LocalOnlyCapturedAncestorParameters[y@", result.Metadata["A"], StringComparison.Ordinal);
        }
    }

    [Fact]
    public void DeepRequirements_AreGeneratedForReadersOutsideTheirOwner()
    {
        foreach (var place in new[] { "outside", "in-lib", "in-box" })
        {
            Assert.Null(CensusGrid.Exclusion("name", "value", "none", "plain", place, "found", "deep"));
            var @case = CensusGrid.Build(["name", "value", "none", "plain", place, "found", "deep"]);
            SourceProvenance.ParseValid(@case.Body + CensusRunner.Inside5);
        }
    }

    // A reader under which every head's found member parses: an rt-alg head's runtime member `L.Q` parses only in a
    // reader with an explicit parameter list (the grid's own validity; its plain readers are skipped).
    private static string ValidReader(string head) => head == "rt-alg" ? "param" : "plain";

    /// <summary>
    /// The intermediate-fallback ending (da209fa0) exists for every head kind: with <c>req=fallback</c> the fallback
    /// <c>Missing</c> reads <c>y</c> and the path continues through <c>Next</c>, so the reader is charged <c>y</c>, keeps one
    /// value per activation and is refused outside the call. An <c>rt-alg</c> head is excluded from <c>req=fallback</c>: its
    /// <c>L = &lt;path&gt;.Algorithm</c> fails on <c>Sub</c>'s numeric value before any fallback runs. The open positions call
    /// no fallback.
    /// </summary>
    [Fact]
    public async Task IntermediateFallbackEnding_ChargesTheFallbackForEveryHead()
    {
        foreach (var head in CensusGrid.Heads)
        {
            var open = head == "opened" ? "own-used" : "none";
            var reader = ValidReader(head);
            foreach (var pos in new[] { "value", "fallback" })
            {
                string[] values = [head, pos, open, reader, "outside", "mid-fallback", "fallback"];
                var excluded = CensusGrid.Exclusion(values[0], values[1], values[2], values[3], values[4], values[5], values[6]);
                if (head == "rt-alg")
                {
                    Assert.NotNull(excluded);
                    Assert.Null(CensusGrid.Exclusion(values[0], values[1], values[2], values[3], values[4], values[5], "container"));
                    continue;
                }
                Assert.Null(excluded);
                var @case = CensusGrid.Build(values);
                Assert.Contains(pos == "value" ? ".Missing.Next + 0" : ".Q.Missing.Next + 0", @case.Body, StringComparison.Ordinal);
                Assert.Contains("Missing(r) = r * 0 + y", @case.Body, StringComparison.Ordinal);
                SourceProvenance.ParseValid(@case.Body + CensusRunner.SameRun);
                var result = await CensusRunner.Run(@case, collectLean: false);
                Assert.Null(result.Skipped);
                var observed = $"{result.Metadata["A"]}; {string.Join("; ", result.Outcomes.Select(o => $"{o.Key}: {o.Value}"))}";
                Assert.True(result.Metadata["A"].StartsWith("LocalOnlyCapturedAncestorParameters[y@", StringComparison.Ordinal)
                    && (result.Outcomes["in5"], result.Outcomes["in7"], result.Outcomes["same"]) == ("ok 5", "ok 7", "ok S[5, 7]")
                    && result.Outcomes["esc:A"] == "err localOnlyProperty:A",
                    $"{@case.Id}: {observed}\n{@case.Body}");
                Assert.Empty(result.Gaps);
            }
        }
        foreach (var pos in new[] { "open", "open-dotted" })
        {
            Assert.NotNull(CensusGrid.Exclusion("name", pos, "own-used", "plain", "outside", "mid-fallback", "none"));
            Assert.NotNull(CensusGrid.Exclusion("name", pos, "own-used", "plain", "outside", "found", "fallback"));
        }
        // A selection that calls no Missing has no fallback to read y.
        Assert.NotNull(CensusGrid.Exclusion("name", "value", "none", "plain", "outside", "found", "fallback"));
    }

    /// <summary>
    /// The deconstruction position exists for every head kind and every ending, and each valid cell gives what its rows
    /// twin gives; the twin differs from the cell in the deconstruction lines alone. A cell parses exactly when its
    /// value-position cell does: the found, missing and mid-fallback endings for every head, while a runtime ending names
    /// its member <c>Q</c> after <c>.Algorithm</c>, which without a lexical <c>Q</c> (a static head's) does not parse.
    /// </summary>
    [Fact]
    public async Task DeconstructionPosition_MatchesItsRowsTwinForEveryHead()
    {
        foreach (var head in CensusGrid.Heads)
        {
            var open = head == "opened" ? "own-used" : "none";
            var reader = ValidReader(head);
            foreach (var end in CensusGrid.Ends)
            {
                string[] values = [head, "deconstruction", open, reader, "outside", end, "member"];
                Assert.Null(CensusGrid.Exclusion(values[0], values[1], values[2], values[3], values[4], values[5], values[6]));
                var @case = CensusGrid.Build(values);
                var valueCellParses = CensusRunner.Probes(CensusGrid.Build([head, "value", open, reader, "outside", end, "member"])) is not null;
                Assert.True(valueCellParses == CensusRunner.Probes(@case) is not null, @case.Id);
                Assert.True(valueCellParses || (end == "runtime" && !head.StartsWith("rt-", StringComparison.Ordinal)), $"{@case.Id} does not parse cleanly");
                if (!valueCellParses) continue;
                var twin = CensusGrid.DeconstructionTwin(@case);
                Assert.Equal((@case.Id, "deconstruction-twin"), (twin.Id, twin.Kind));
                Assert.Equal(@case.Readers.Select(r => (r.Label, string.Join(".", r.Path), r.Escaped)),
                    twin.Readers.Select(r => (r.Label, string.Join(".", r.Path), r.Escaped)));
                // `a, b = <selection> + 0, 0` (one line, or a block literal's lines) and `a, b` become `<selection> + 0, 0`.
                const string deconstruction = "a, b = ", items = " + 0, 0\n";
                var start = @case.Body.IndexOf(deconstruction, StringComparison.Ordinal);
                Assert.Equal(start, @case.Body.LastIndexOf(deconstruction, StringComparison.Ordinal));
                var indent = @case.Body[(@case.Body.LastIndexOf('\n', start) + 1)..start];
                Assert.True(indent.All(c => c == ' '), @case.Id);
                var close = @case.Body.IndexOf(items, start, StringComparison.Ordinal) + items.Length;
                Assert.Equal(indent + "a, b\n", @case.Body[close..(close + indent.Length + 5)]);
                Assert.Equal(@case.Body[..start] + @case.Body[(start + deconstruction.Length)..close] + @case.Body[(close + indent.Length + 5)..], twin.Body);
                SourceProvenance.ParseValid(@case.Body + CensusRunner.SameRun);
                SourceProvenance.ParseValid(twin.Body + CensusRunner.SameRun);
                var result = await CensusRunner.Run(@case, collectLean: false);
                Assert.Null(result.Skipped);
                // The inside calls work exactly when the value position's do (rt-alg's `.Algorithm` step fails in both).
                var valueCell = await CensusRunner.Run(CensusGrid.Build([head, "value", open, reader, "outside", end, "member"]), collectLean: false);
                Assert.True(valueCell.InsideWorks == result.InsideWorks
                    && (!result.InsideWorks || result.Outcomes["in5"].StartsWith("ok S[", StringComparison.Ordinal)),
                    $"{@case.Id}: {result.Outcomes["in5"]}; value position: {valueCell.Outcomes["in5"]}\n{@case.Body}");
                Assert.True(end != "found" || head == "rt-alg" || result.InsideWorks, @case.Id);
                Assert.True(!result.Gaps.Any(gap => gap.Check == "T"), $"{@case.Id}: {string.Join("\n", result.Gaps.Select(gap => gap.Line))}");
            }
        }
    }

    /// <summary>
    /// Check T flags a deconstruction cell whose probe or reader metadata differs from its rows twin's: the refusal of
    /// a captured block member inside its own owner's call (the outcome before da209fa0) is such a difference.
    /// </summary>
    [Fact]
    public void DeconstructionTwinCheck_FlagsEveryDifference()
    {
        var outcomes = new Dictionary<string, string> { ["in5"] = "ok S[5, 0]", ["in7"] = "ok S[7, 0]", ["esc:A"] = "err localOnlyProperty:A" };
        var metadata = new Dictionary<string, string> { ["A"] = "LocalOnlyCapturedAncestorParameters[y@0]" };
        Assert.Empty(CensusRunner.TwinDifferences("cell", outcomes, metadata, outcomes, metadata));

        var refused = new Dictionary<string, string>(outcomes) { ["in5"] = "err localOnlyProperty:Q", ["in7"] = "err localOnlyProperty:Q" };
        var gaps = CensusRunner.TwinDifferences("cell", refused, metadata, outcomes, metadata);
        Assert.Equal(["in5", "in7"], gaps.Select(gap => gap.Detail[..gap.Detail.IndexOf(':')]));
        Assert.All(gaps, gap => Assert.Equal(("T", "deconstruction-twin-differs", "cell", "-"), (gap.Check, gap.Class, gap.Id, gap.Reader)));

        var exported = new Dictionary<string, string> { ["A"] = "exported" };
        var metadataGap = Assert.Single(CensusRunner.TwinDifferences("cell", outcomes, exported, outcomes, metadata));
        Assert.Equal(("A", "metadata: deconstruction=exported; rows=LocalOnlyCapturedAncestorParameters[y@0]"), (metadataGap.Reader, metadataGap.Detail));
        // A probe the twin lacks (it did not run) is a difference, never a match.
        Assert.Single(CensusRunner.TwinDifferences("cell", outcomes, metadata, new Dictionary<string, string>(outcomes) { ["in5"] = "invalid" }, metadata));
    }

    [Fact]
    public void SourceRunErrors_KeepCategoryAndSubject()
    {
        foreach (var (source, expected) in new[]
        {
            ("1 / 0", "err div0"),
            ("true + 0", "err type"),
            ("F(y) = {\n A = y + 0\n 0\n}\nF.A", "err localOnlyProperty:A"),
        })
        {
            SourceProvenance.ParseValid(source);
            Assert.Equal(expected, CensusRunner.RenderEngine(KatLangEngine.Run(source)));
        }
    }

    /// <summary>
    /// The front end charges this reader (<c>y@0</c>; before owner decision Q3, 2026-11-14, a name provided through a
    /// block-headed reference was the under-charge this control ran on, and Q3 removed it). The control therefore
    /// shows the census a HOST-BUILT tree with the reader exported: the escaped read fails at <c>Q</c>, and the
    /// failing inside call must not hide it.
    /// </summary>
    [Fact]
    public async Task FailingInside_DoesNotSuppressTheEscapedUndercharge()
    {
        var @case = new CensusCase("harness=failed-inside-undercharge", [], """
            F(y) = {
              L = { public Sub = { public Q = y
                0 } }.Sub
              A = {
                open L
                Q + 0
              }
              1 / 0
            }

            """, [new CensusReader("A", ["F", "A"], "F.A")]);
        string[] reader = ["F", "A"];
        var charged = await CensusRunner.Run(@case, collectLean: false);
        Assert.Null(charged.Skipped);
        Assert.Equal("LocalOnlyCapturedAncestorParameters[y@0]", charged.Metadata["A"]);
        Assert.DoesNotContain(charged.Gaps, gap => gap.Check == "U");

        var result = await CensusRunner.Run(@case, collectLean: false, hostBuilt: root =>
        {
            var property = CensusRunner.Find(root, reader)!;
            return CensusRunner.Replace(root, reader,
                current => CensusRunner.Requirements(property).Aggregate(current, CensusRunner.Without));
        });
        Assert.Null(result.Skipped);
        Assert.False(result.InsideWorks);
        Assert.Equal("exported", result.Metadata["A"]);
        Assert.Contains(result.Gaps, gap => gap.Class == "under-charge-masked-access");
    }

    [Fact]
    public async Task FailingInside_DoesNotSuppressNeededCopiesInTheModelCheck()
    {
        var @case = new CensusCase("harness=failed-inside-copy", [], """
            F(y) = {
              Lib = { public Sub = { public Q = 1
                y }
                0 }
              A = Lib.Sub.Q + 0
              1 / 0
            }

            """, [new CensusReader("A", ["F", "A"], "F.A")]);
        var result = await CensusRunner.Run(@case, collectLean: true);
        Assert.Null(result.Skipped);
        Assert.False(result.InsideWorks);
        Assert.Contains(result.Lean, item => item.Role == "copy-needed");
        Assert.DoesNotContain(result.Lean, item => item.Role == "copy-dead");
    }

    [Fact]
    public void ExternalEvidence_RejectsMissingDuplicateMalformedAndStaleResults()
    {
        var directory = Path.Combine(Path.GetTempPath(), "katlang-census-evidence-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(directory);
        try
        {
            var root = SourceProvenance.ParseValid("1").Root;
            CensusLeanItem[] items = [new("one#real#in5", "one", "real", "real", root, "ok 1")];
            CensusLean.Emit(items, directory);
            Assert.Throws<InvalidDataException>(() => CensusLean.Check(directory, items));
            var path = Path.Combine(directory, "census-0000.out");
            const string observation = "CENSUS\tone#real#in5\ttrue\ttrue\tok 1\n";
            File.WriteAllText(path, observation + observation);
            Assert.Throws<InvalidDataException>(() => CensusLean.Check(directory, items));
            File.WriteAllText(path, observation.Replace("true", "unknown", StringComparison.Ordinal));
            Assert.Throws<InvalidDataException>(() => CensusLean.Check(directory, items));
            File.WriteAllText(path, observation);
            Assert.Empty(CensusLean.Check(directory, items));
            Assert.Throws<InvalidDataException>(() => CensusLean.Check(directory,
                [items[0] with { Tree = SourceProvenance.ParseValid("2").Root }]));
            File.WriteAllText(Path.Combine(directory, "manifest.tsv"), "");
            Assert.Throws<InvalidDataException>(() => CensusLean.Check(directory, items));

            var headPath = Path.Combine(directory, "head.out");
            const string head = "one\tin5\tOUT\tOK 1\n";
            File.WriteAllText(headPath, head);
            Assert.Throws<InvalidDataException>(() => ExposureCensusTests.HeadOutput.Read(headPath).RequireComplete([("one", "in5")]));
            File.WriteAllText(headPath, head + head);
            Assert.Throws<InvalidDataException>(() => ExposureCensusTests.HeadOutput.Read(headPath));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }
}
