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

    // ── The extension (2026-11-17) ──────────────────────────────────────────────────────────────

    /// <summary>
    /// The runtime head whose value reads nothing of F (<c>rt-capture</c>, <c>L = Cap(Seed()).Algorithm</c>): a fallback
    /// that reads y is the reader's only charge, through an intermediate edge (<c>mid-fallback</c>, <c>result-member</c>)
    /// and in the fallback position alike, so the reader keeps one value per activation and is refused outside the call.
    /// Without a fallback that reads y the reader stays exported. (rt-param's <c>L = y</c> is charged by its head whatever
    /// the fallback reads, so it cannot show a lost fallback charge.)
    /// </summary>
    [Fact]
    public async Task RuntimeCaptureHead_IsChargedOnlyThroughItsFallback()
    {
        foreach (var pos in new[] { "value", "fallback" })
        foreach (var end in new[] { "mid-fallback", "result-member" })
        {
            string[] values = ["rt-capture", pos, "none", "plain", "outside", end, "fallback"];
            Assert.Null(CensusGrid.Exclusion(values[0], values[1], values[2], values[3], values[4], values[5], values[6]));
            var @case = CensusGrid.Build(values);
            Assert.Contains("L = Cap(Seed()).Algorithm", @case.Body, StringComparison.Ordinal);
            Assert.DoesNotContain("L = y", @case.Body, StringComparison.Ordinal);
            var result = await CensusRunner.Run(@case, collectLean: false);
            Assert.Null(result.Skipped);
            var observed = $"{result.Metadata["A"]}; {string.Join("; ", result.Outcomes.Select(o => $"{o.Key}: {o.Value}"))}";
            Assert.True(result.Metadata["A"] == "LocalOnlyCapturedAncestorParameters[y@0]"
                && (result.Outcomes["in5"], result.Outcomes["in7"], result.Outcomes["same"]) == ("ok 5", "ok 7", "ok S[5, 7]")
                && result.Outcomes["esc:A"] == "err localOnlyProperty:A", $"{@case.Id}: {observed}\n{@case.Body}");
            Assert.Empty(result.Gaps);
        }
        var plain = await CensusRunner.Run(CensusGrid.Build(["rt-capture", "value", "none", "plain", "outside", "found", "none"]), collectLean: false);
        Assert.Equal("exported", plain.Metadata["A"]);
        Assert.All(plain.Outcomes, o => Assert.Equal("ok " + (o.Key == "same" ? "S[1, 1]" : "1"), o.Value));
        Assert.Empty(plain.Gaps);
    }

    /// <summary>
    /// The callable <c>rt-alg</c> fixture (<c>rt-alg-call</c>): Sub returns a captured call of its member <c>Run</c>, so
    /// <c>L = &lt;path&gt;.Algorithm</c> is Run's algorithm and every non-open position and selection ending produces values,
    /// where rt-alg fails with a type error. Each such cell gives what its static-route twin gives (check R), and no check
    /// finds a gap.
    /// </summary>
    [Fact]
    public async Task CallableAlgorithmHead_ProducesValues_AndAgreesWithItsStaticRoute()
    {
        foreach (var pos in new[] { "value", "callee", "spread", "fallback", "deconstruction" })
        foreach (var end in new[] { "found", "missing", "mid-fallback", "result-member" })
        {
            string[] values = ["rt-alg-call", pos, "none", "plain", "outside", end, "container"];
            if (CensusGrid.Exclusion(values[0], values[1], values[2], values[3], values[4], values[5], values[6]) is not null)
            {
                Assert.True(end == "missing" && pos is "callee" or "spread" or "fallback", string.Join("|", values));
                continue;
            }
            var @case = CensusGrid.Build(values);
            Assert.True(CensusRunner.HasStaticRouteTwin(@case));
            var twin = CensusGrid.StaticRouteTwin(@case);
            Assert.Equal((@case.Id, "static-route-twin"), (twin.Id, twin.Kind));
            Assert.Equal(@case.Body.Replace("L = Lib.Sub.Algorithm\n", "L = Lib.Sub.Run\n", StringComparison.Ordinal), twin.Body);
            Assert.Contains("      public Run = y\n      Cap(Run())\n", @case.Body, StringComparison.Ordinal);
            var result = await CensusRunner.Run(@case, collectLean: false);
            Assert.Null(result.Skipped);
            Assert.True(result.InsideWorks && result.Outcomes["esc:A"] == "err localOnlyProperty:A",
                $"{@case.Id}: {string.Join("; ", result.Outcomes.Select(o => $"{o.Key}: {o.Value}"))}\n{@case.Body}");
            Assert.Empty(result.Gaps);
        }
        // The same selection over rt-alg's fixture fails before any value: Sub returns a number, not a call reference.
        var failing = await CensusRunner.Run(CensusGrid.Build(["rt-alg", "value", "none", "param", "outside", "found", "container"]), collectLean: false);
        Assert.Equal("err type", failing.Outcomes["in5"]);
        Assert.Throws<ArgumentException>(() => CensusGrid.StaticRouteTwin(CensusGrid.Build(["rt-alg", "value", "none", "param", "outside", "found", "container"])));
        // Open positions also compare with the static route. OD-C opens L's own namespace, but in this fixture every
        // valid cell still agrees with its twin. Keep a charged and an uncharged open in the default harness coverage.
        foreach (var requirement in new[] { "none", "container" })
        {
            var opened = CensusGrid.Build(["rt-alg-call", "open", "own-unused", "plain", "outside", "found", requirement]);
            Assert.True(CensusRunner.HasStaticRouteTwin(opened));
            var result = await CensusRunner.Run(opened, collectLean: false);
            Assert.Null(result.Skipped);
            Assert.True(result.InsideWorks);
            Assert.Empty(result.Gaps);
        }
    }

    /// <summary>
    /// The member-of-the-fallback's-result ending exists for every head: the fallback returns a captured call of its local
    /// <c>Mk</c>, the selection reads the result's member <c>.Invoke()</c>, and with <c>req=fallback</c> the run of <c>Mk</c>
    /// reads y, so the reader is charged y, keeps one value per activation and is refused outside the call. rt-alg is
    /// excluded from <c>req=fallback</c> as for the other endings; the open positions call no fallback.
    /// </summary>
    [Fact]
    public async Task ResultMemberEnding_ChargesTheFallbackForEveryHead()
    {
        foreach (var head in CensusGrid.AllHeads)
        {
            var open = head == "opened" ? "own-used" : "none";
            var reader = ValidReader(head);
            foreach (var pos in new[] { "value", "fallback" })
            {
                string[] values = [head, pos, open, reader, "outside", "result-member", "fallback"];
                var excluded = CensusGrid.Exclusion(values[0], values[1], values[2], values[3], values[4], values[5], values[6]);
                if (head == "rt-alg")
                {
                    Assert.NotNull(excluded);
                    continue;
                }
                Assert.Null(excluded);
                var @case = CensusGrid.Build(values);
                Assert.Contains(pos == "value" ? ".Missing.Invoke() + 0" : ".Q.Missing.Invoke() + 0", @case.Body, StringComparison.Ordinal);
                Assert.Contains("Missing(r) = {\n    Mk(k) = r * 0 + k + y\n    Cap(Mk(0))\n  }", @case.Body, StringComparison.Ordinal);
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
            Assert.NotNull(CensusGrid.Exclusion("name", pos, "own-used", "plain", "outside", "result-member", "none"));
        // The callee position calls the result's captured algorithm afresh: Mk(1) reads y too.
        var callee = await CensusRunner.Run(CensusGrid.Build(["name", "callee", "none", "plain", "outside", "result-member", "fallback"]), collectLean: false);
        Assert.Equal(("ok 6", "ok 8", "ok S[6, 8]"), (callee.Outcomes["in5"], callee.Outcomes["in7"], callee.Outcomes["same"]));
        Assert.Empty(callee.Gaps);
    }

    /// <summary>
    /// Check R flags every probe whose outcome differs from the static-route twin's, a probe the twin lacks, and every reader
    /// whose metadata differs (the runtime route of rt-alg's own fixture, which fails with a type error, is such a difference).
    /// </summary>
    [Fact]
    public async Task StaticRouteCheck_FlagsEveryDifference()
    {
        var outcomes = new Dictionary<string, string> { ["in5"] = "ok 1", ["in7"] = "ok 1", ["esc:A"] = "ok 1" };
        var metadata = new Dictionary<string, string> { ["A"] = "exported" };
        Assert.Empty(CensusRunner.RouteDifferences("cell", outcomes, metadata, outcomes, metadata));
        var differing = new Dictionary<string, string>(outcomes) { ["in7"] = "err type" };
        var gap = Assert.Single(CensusRunner.RouteDifferences("cell", differing, metadata, outcomes, metadata));
        Assert.Equal(("R", "static-route-differs", "cell", "-", "in7: runtime=err type; static=ok 1"), (gap.Check, gap.Class, gap.Id, gap.Reader, gap.Detail));
        Assert.Single(CensusRunner.RouteDifferences("cell", outcomes, metadata, new Dictionary<string, string>(outcomes) { ["esc:A"] = "invalid" }, metadata));
        Assert.Single(CensusRunner.RouteDifferences("cell", outcomes, metadata, outcomes.Where(o => o.Key != "in5").ToDictionary(), metadata));
        var charged = new Dictionary<string, string> { ["A"] = "LocalOnlyCapturedAncestorParameters[y@0]" };
        var metadataGap = Assert.Single(CensusRunner.RouteDifferences("cell", outcomes, charged, outcomes, metadata));
        Assert.Equal(("A", "metadata: runtime=LocalOnlyCapturedAncestorParameters[y@0]; static=exported"), (metadataGap.Reader, metadataGap.Detail));

        // A real pair that differs: rt-alg's runtime route over its numeric Sub against the callable cell's static route.
        var callable = CensusGrid.Build(["rt-alg-call", "value", "none", "param", "outside", "found", "container"]);
        var failing = await CensusRunner.Run(CensusGrid.Build(["rt-alg", "value", "none", "param", "outside", "found", "container"]), collectLean: false);
        var labels = failing.Outcomes.Keys.ToArray();
        var (twinOutcomes, twinMetadata) = CensusRunner.TwinFacts(CensusGrid.StaticRouteTwin(callable), labels);
        Assert.Contains(CensusRunner.RouteDifferences(callable.Id, failing.Outcomes, failing.Metadata, twinOutcomes, twinMetadata),
            difference => difference.Detail == "in5: runtime=err type; static=ok 1");
    }

    /// <summary>
    /// The settlement families of 0a1718d2 as census cases: the nested-read programs publish the footprint tests'
    /// metadata (<c>Mid</c> exported, every member read back through <c>F.Mid</c> charged <c>Mid</c>'s own <c>y@0</c>) and
    /// work inside; the re-entry programs' exported readers fail only at the impossible check their case names. No check
    /// finds a gap.
    /// </summary>
    [Fact]
    public async Task SettlementFamilies_KeepTheFootprintWitnesses_WithoutGaps()
    {
        var families = CensusGrid.SettlementFamilies().ToDictionary(f => f.Id, StringComparer.Ordinal);
        Assert.Equal(11, families.Count);
        foreach (var family in families.Values)
        {
            var result = await CensusRunner.Run(family, collectLean: false);
            Assert.Null(result.Skipped);
            Assert.True(result.Gaps.Count == 0, $"{family.Id}: {string.Join("\n", result.Gaps.Select(g => g.Line))}");
            if (family.Id.StartsWith("settlement=nested-read-", StringComparison.Ordinal))
            {
                Assert.True(result.InsideWorks, family.Id);
                foreach (var (reader, metadata) in result.Metadata)
                    Assert.Equal(reader is "Mid" or "O" or "P" ? "exported" : "LocalOnlyCapturedAncestorParameters[y@0]", metadata);
            }
            else
            {
                Assert.All(result.Impossible, gap => Assert.Equal($"err localOnlyProperty:{family.ImpossibleSubject}", gap.Detail));
            }
        }
        var reEntry = await CensusRunner.Run(families["settlement=re-entry-1"], collectLean: false);
        Assert.Equal("exported", reEntry.Metadata["H"]);
        Assert.Equal(("U", "impossible-check", "H"), Assert.Single(reEntry.Impossible) is var h ? (h.Check, h.Class, h.Reader) : default);
        var hop = await CensusRunner.Run(families["settlement=re-entry-hop"], collectLean: false);
        Assert.Contains(hop.Impossible, gap => gap.Reader == "V");
    }

    /// <summary>
    /// The HEAD probe (<see cref="CensusHeadProbe"/>, the tracked source the <c>check-head</c> scratch project compiles) writes
    /// exactly the protocol <see cref="ExposureCensusTests.HeadOutput"/> reads: run here against today's KatLang, its metadata
    /// and its outcomes on all three routes are the census's own, a program that does not parse is reported on all three, and
    /// the scratch project it writes compiles this very file.
    /// </summary>
    [Fact]
    public async Task HeadProbe_WritesTheProtocolHeadOutputReads()
    {
        var directory = Path.Combine(Path.GetTempPath(), "katlang-census-head-probe-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(directory);
        try
        {
            var @case = CensusGrid.Build(["name", "value", "none", "plain", "outside", "found", "member"]);
            var lines = CensusRunner.Probes(@case)!.Select(p => $"{@case.Id}\t{p.Label}\t{p.Source.Replace("\n", "\\n")}")
                .Append("broken\tin5\tF(y) = {\\n  A = \\n").ToArray();
            var (programs, output) = (Path.Combine(directory, "head-programs.tsv"), Path.Combine(directory, "head.out"));
            File.WriteAllLines(programs, lines);
            Assert.Equal((lines.Length, 0), await CensusHeadProbe.RunAsync(programs, output));

            var head = ExposureCensusTests.HeadOutput.Read(output);
            head.RequireComplete(lines.Select(line => line.Split('\t')).Select(parts => (parts[0], parts[1])).ToArray());
            var census = await CensusRunner.Run(@case, collectLean: false);
            Assert.Equal(census.Metadata["A"], head.Metadata(@case.Id, "in5")["root.F.A"]);
            Assert.Equal(["in5"], head.Metadata(@case.Id, "in5").Keys.Select(_ => "in5").Distinct());
            foreach (var (label, outcome) in census.Outcomes)
            {
                var spelled = outcome.StartsWith("ok ", StringComparison.Ordinal) ? "OK " + outcome[3..]
                    : outcome.StartsWith("err localOnlyProperty:", StringComparison.Ordinal) ? "FAIL LocalOnlyProperty:" + outcome["err localOnlyProperty:".Length..]
                    : throw new InvalidOperationException($"Unexpected outcome {outcome}");
                foreach (var suffix in new[] { "", ":async", ":forced" })
                    Assert.Equal(spelled, head.Outcomes(@case.Id)[label + suffix]);
            }
            Assert.All(head.Outcomes("broken").Values, outcome => Assert.StartsWith("PARSE ", outcome, StringComparison.Ordinal));
            Assert.Empty(head.Metadata("broken", "in5"));

            var project = Path.Combine(directory, "head-probe");
            CensusHeadProbe.WriteProject(project, ExposureCensusTests.HeadProbeSourcePath);
            var text = File.ReadAllText(Path.Combine(project, CensusHeadProbe.ProjectFileName));
            _ = System.Xml.Linq.XDocument.Parse(text);
            Assert.Contains($"<Compile Include=\"{ExposureCensusTests.HeadProbeSourcePath}\"", text, StringComparison.Ordinal);
            Assert.Contains("<AssemblyName>KatLang.Benchmarks</AssemblyName>", text, StringComparison.Ordinal);
            Assert.Contains("<ProjectReference Include=\"$(KatLangHeadProject)\" />", text, StringComparison.Ordinal);
            Assert.Contains("CensusHeadProbe.RunAsync(args[0], args[1])", File.ReadAllText(Path.Combine(project, CensusHeadProbe.EntryFileName)), StringComparison.Ordinal);
            Assert.Throws<FileNotFoundException>(() => CensusHeadProbe.WriteProject(project, Path.Combine(directory, "missing.cs")));
            Assert.Contains(CensusHeadProbe.Steps(directory), step => step.Contains($"git archive {CensusHeadProbe.Revision} ", StringComparison.Ordinal));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
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
