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
                var valueCellParses = await CensusRunner.Probes(CensusGrid.Build([head, "value", open, reader, "outside", end, "member"])) is not null;
                Assert.Equal(valueCellParses, await CensusRunner.Probes(@case) is not null);
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
    /// The extension heads' W families (<see cref="CensusWork.ExtensionFamilies"/>): one family per head, reader, placement,
    /// level and use, disjoint from the grid's, whose list and ids stay those of earlier runs; a used family is excluded (a
    /// runtime reference opens its own namespace). One unused family per head parses and settles within the doubling bound.
    /// </summary>
    [Fact]
    public void ExtensionWorkFamilies_ExistForTheNewHeads_AndSettleWithinTheBound()
    {
        var grid = CensusWork.Families().ToArray();
        var extension = CensusWork.ExtensionFamilies().ToArray();
        Assert.Equal(CensusGrid.Heads.Length * CensusGrid.ReaderKinds.Length * CensusGrid.Places.Length * CensusWork.Levels.Length * 2, grid.Length);
        Assert.Equal(CensusGrid.ExtensionHeads.Length * CensusGrid.ReaderKinds.Length * CensusGrid.Places.Length * CensusWork.Levels.Length * 2, extension.Length);
        Assert.Empty(grid.Select(f => f.Family.Id).Intersect(extension.Select(f => f.Family.Id)));
        Assert.All(extension.Where(f => f.Family.Id.EndsWith("|use=used", StringComparison.Ordinal)), f => Assert.NotNull(f.Excluded));
        foreach (var head in CensusGrid.ExtensionHeads)
        {
            Assert.Contains(extension, f => f.Excluded is null && f.Family.Id.StartsWith($"W|head={head}|", StringComparison.Ordinal));
            var (family, excluded) = extension.Single(f => f.Family.Id == $"W|head={head}|reader=plain|place=outside|level=enc1|use=unused");
            Assert.Null(excluded);
            var program = family.Program(CensusWork.Widths[0]);
            Assert.Null(CensusWork.Diagnostics(program));
            Assert.Contains(head == "rt-capture" ? "L24 = Cap(Seed()).Algorithm" : "L24 = X24.Sub.Algorithm", program, StringComparison.Ordinal);
            Assert.Contains("Cap(meta op) = op", program, StringComparison.Ordinal);
            var measured = CensusWork.Measure(family);
            Assert.True(measured.WithinBound, $"{family.Id}: {measured.Problem}");
            Assert.All(measured.Frames, frames => Assert.True(frames > 0, family.Id));
        }
    }

    // ── The module dimension (2026-11-19) ─────────────────────────────────────────────────────────

    // Provider twins whose open level is charged: `open Lib.Sub, Other` walks Sub, whose row reads y, at the reader's own
    // value block and at F, the plain reader's enclosing level.
    private static string[] ChargedModuleTwin(string open) => ["name", "open", open, "plain", "outside", "found", "container"];

    /// <summary>
    /// One loaded module is one open provider (Q-32 I-U) on both module spellings, through the real asynchronous front end
    /// over the census's in-memory server: two root holders of one canonical URL and a holder plus a written load of it give
    /// the reader <c>X</c> exactly as <c>Other</c> does, so the reader is charged the walk of <c>Lib.Sub</c> at the level the
    /// module decides and every probe and the metadata equal the provider twin's. The control's two canonical URLs serve the
    /// same text and stay two providers: the unqualified read is the front end's AmbiguousOpen, and its clean qualified
    /// fixture <c>ModA.X</c> is a lexical read. Where the reader writes the open itself the census also records I25.
    /// </summary>
    [Fact]
    public async Task ModuleHead_OneModuleIsOneProvider_AndTwoUrlsAreTwo()
    {
        foreach (var open in new[] { "own-unused", "enc1-unused" })
        {
            var twin = CensusGrid.Build(ChargedModuleTwin(open));
            Assert.Contains("open Lib.Sub, Other\n", twin.Body, StringComparison.Ordinal);
            var twinResult = await CensusRunner.Run(twin, collectLean: false);
            Assert.Equal("LocalOnlyCapturedAncestorParameters[y@0]", twinResult.Metadata["A"]);
            Assert.Empty(twinResult.Gaps);
            foreach (var module in CensusGrid.ModuleValues)
            {
                string[] values = [.. ChargedModuleTwin(open), module];
                var @case = CensusGrid.BuildModule(values);
                Assert.Equal((twin.Id + "|module=" + module, "module"), (@case.Id, @case.Kind));
                Assert.Equal(@case.Id, CensusGrid.TryParseId(@case.Id)?.Id);
                Assert.Equal(twin.Id, CensusGrid.ModuleTwin(@case).Id);
                var (providers, holders, read) = module switch
                {
                    "holders" => ("ModA, ModB", $"ModA = load('{CensusGrid.ModuleUrl}')\nModB = load('{CensusGrid.ModuleUrl}')\n", "X + 0"),
                    "holder-load" => ($"ModA, load('{CensusGrid.ModuleUrl}')", $"ModA = load('{CensusGrid.ModuleUrl}')\n", "X + 0"),
                    _ => ("ModA, ModB", $"ModA = load('{CensusGrid.ModuleUrl}')\nModB = load('{CensusGrid.ModuleCopyUrl}')\n", "ModA.X + 0"),
                };
                // The twin's program with the module's holders before F, the module as the level's second provider, and
                // the control's qualified read (` X + 0` is the reader's one read of X: own block or `A = X + 0`).
                Assert.Equal(holders + twin.Body.Replace("open Lib.Sub, Other\n", $"open Lib.Sub, {providers}\n", StringComparison.Ordinal)
                    .Replace(" X + 0\n", " " + read + "\n", StringComparison.Ordinal), @case.Body);
                await SourceProvenance.ParseValidAsync(@case.Body + CensusRunner.SameRun + "\n", CensusRunner.ModuleServer(@case).Options());

                var result = await CensusRunner.Run(@case, collectLean: false);
                Assert.Null(result.Skipped);
                Assert.Equal(CensusGrid.ExpectedProviderVerdict(@case), result.ProviderVerdict);
                var ownOpenCharge = module == "two-urls" && open == "own-unused";
                if (ownOpenCharge)
                    Assert.Equal(new CensusGap("O", "over-charge", @case.Id, "A", "r=y@0"), Assert.Single(result.Gaps));
                else
                    Assert.Empty(result.Gaps);
                Assert.Equal(module == "two-urls" ? 2 : 1, CensusRunner.ModuleIdentities(
                    (await SourceProvenance.ParseValidAsync(@case.Body + CensusRunner.Inside5 + "\n", CensusRunner.ModuleServer(@case).Options())).Root));
                var unqualified = CensusGrid.ModuleUnqualifiedRead(@case);
                if (module != "two-urls")
                {
                    Assert.True(CensusRunner.HasModuleTwin(@case));
                    Assert.Equal(twinResult.Metadata, result.Metadata);
                    Assert.Equal(twinResult.Outcomes, result.Outcomes);
                    Assert.Equal(("ok 1", "ok 1", "ok S[1, 1]", "err localOnlyProperty:A"),
                        (result.Outcomes["in5"], result.Outcomes["in7"], result.Outcomes["same"], result.Outcomes["esc:A"]));
                    // The unqualified read is the cell itself.
                    Assert.Same(@case, unqualified);
                    continue;
                }
                // The qualified fixture and the separate unqualified front-end control.
                Assert.False(CensusRunner.HasModuleTwin(@case));
                Assert.Equal(ownOpenCharge ? "LocalOnlyCapturedAncestorParameters[y@0]" : "exported", result.Metadata["A"]);
                Assert.All(result.Outcomes, o => Assert.Equal(o.Key == "same" ? "ok S[1, 1]"
                    : ownOpenCharge && o.Key == "esc:A" ? "err localOnlyProperty:A" : "ok 1", o.Value));
                Assert.Equal(@case.Body.Replace("ModA.X + 0", "X + 0", StringComparison.Ordinal), unqualified.Body);
                var parsed = await Parser.ParseAsync(unqualified.Body + CensusRunner.Inside5 + "\n", CensusRunner.ModuleServer(unqualified).Options());
                var error = Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
                Assert.Equal(DiagnosticCode.AmbiguousOpen, error.Code);
            }
        }
        // An uncharged level: the module decides the same name, and the reader stays exported.
        var uncharged = await CensusRunner.Run(CensusGrid.BuildModule(["name", "open", "own-unused", "plain", "outside", "found", "none", "holders"]), collectLean: false);
        Assert.Equal(("exported", 0), (uncharged.Metadata["A"], uncharged.Gaps.Count));

        Assert.NotNull(CensusGrid.ModuleExclusion("clause", "own-unused", "holder-load"));
        Assert.Null(CensusGrid.ModuleExclusion("clause", "enc1-unused", "holder-load"));
    }

    /// <summary>
    /// The inherited eager own-open charge (I25) in its container form: a container whose own
    /// open no lookup consults is charged the open's walk, so an exported reader inside it cannot be read from outside, while a
    /// host-built copy of the container without that requirement reads it on every route. The program needs no module.
    /// </summary>
    [Fact]
    public async Task ContainerOwnOpen_ChargesTheContainer_OnTheQualifiedControl()
    {
        var control = CensusGrid.BuildModule(["name", "open", "enc1-unused", "plain", "in-lib", "found", "container", "two-urls"]);
        var observed = await CensusRunner.Run(control, collectLean: false);
        Assert.Equal(new CensusGap("U", "under-charge-masked-access", control.Id, "A", "err localOnlyProperty:Lib"), Assert.Single(observed.Gaps));
        var body = control.Body[control.Body.IndexOf("F(y) = {", StringComparison.Ordinal)..]
            .Replace("open Lib.Sub, ModA, ModB", "open Lib.Sub, Other", StringComparison.Ordinal)
            .Replace("A = ModA.X + 0", "A = Other.X + 0", StringComparison.Ordinal);
        Assert.Contains("  Lib = {\n    open Lib.Sub, Other\n", body, StringComparison.Ordinal);
        foreach (var (row, expected) in new[] { ("F(5)", "ok 1"), ("F.Lib.A", "err localOnlyProperty:Lib") })
        {
            var root = SourceProvenance.ParseValid(body + row + "\n").Root;
            var lib = CensusRunner.Find(root, ["F", "Lib"])!;
            Assert.Equal("LocalOnlyCapturedAncestorParameters[y@0]", CensusRunner.Describe(lib));
            Assert.Equal("exported", CensusRunner.Describe(CensusRunner.Find(root, ["F", "Lib", "A"])));
            Assert.Equal((expected, null), await CensusRunner.EvaluateTree(root));
            var copy = CensusRunner.Replace(root, ["F", "Lib"], p => CensusRunner.Requirements(lib).Aggregate(p, CensusRunner.Without));
            Assert.Equal(("ok 1", null), await CensusRunner.EvaluateTree(copy));
        }
    }

    /// <summary>
    /// The provider verdict cannot pass by accident: a module cell whose download is missing is a P gap (its twin parses,
    /// so the skip is a validity difference, never a silent drop), and a control that loads one canonical URL twice shows
    /// one identity and a clean unqualified read, which is not the control's verdict.
    /// </summary>
    [Fact]
    public async Task ModuleHead_AMissingDownloadOrAMergedControlCannotPass()
    {
        var holders = CensusGrid.BuildModule([.. ChargedModuleTwin("own-unused"), "holders"]);
        var missing = await CensusRunner.Run(holders with { Modules = [new(CensusGrid.ModuleCopyUrl, CensusGrid.ModuleText)] }, collectLean: false);
        Assert.NotNull(missing.Skipped);
        var gap = Assert.Single(missing.Gaps);
        Assert.Equal(("P", "module-validity-differs"), (gap.Check, gap.Class));

        var control = CensusGrid.BuildModule([.. ChargedModuleTwin("enc1-unused"), "two-urls"]);
        var merged = control with { Body = control.Body.Replace($"ModB = load('{CensusGrid.ModuleCopyUrl}')", $"ModB = load('{CensusGrid.ModuleUrl}')", StringComparison.Ordinal) };
        Assert.NotEqual(control.Body, merged.Body);
        var result = await CensusRunner.Run(merged, collectLean: false);
        Assert.Null(result.Skipped);
        Assert.Equal($"providers 1; identities 1; fetched {CensusGrid.ModuleUrl}; unqualified clean", result.ProviderVerdict);
        Assert.Contains(result.Gaps, g => g is { Check: "P", Class: "provider-verdict-differs" });

        var unopened = holders with { Body = holders.Body.Replace("ModA, ModB", "Other", StringComparison.Ordinal) };
        var unused = await CensusRunner.Run(unopened, collectLean: false);
        Assert.Null(unused.Skipped);
        Assert.Equal($"providers 1 (0 loaded); identities 1; fetched {CensusGrid.ModuleUrl}; unqualified clean", unused.ProviderVerdict);
        Assert.Contains(unused.Gaps, g => g is { Check: "P", Class: "provider-verdict-differs" });
    }

    // ── The deconstruction and carrier families, and U2's unknown-required-name arm (2026-11-20) ──

    private static readonly string[] ReaderA = ["F", "A"];
    private static readonly string[] ProbeLabels = ["in5", "in7", "same", "esc:A"];

    private static CensusCase DeconstructionCase(string name) => CensusGrid.DeconstructionFamilies().Single(c => c.Id == "deconstruction=" + name);

    private static CensusCase CarrierCase(string name) => CensusGrid.CarrierFamilies().Single(c => c.Id == "carrier=" + name);

    private static (string In5, string In7, string Same, string Escaped) Probes(IReadOnlyDictionary<string, string> outcomes)
        => (outcomes["in5"], outcomes["in7"], outcomes["same"], outcomes["esc:A"]);

    /// <summary>
    /// The deconstruction family: each case reads an extension route over a block WRITTEN IN the deconstruction's right-hand
    /// side, differs from its rows twin in the deconstruction lines alone, and gives what that twin gives (check T), the
    /// inline <c>.Algorithm</c> case also what its static route gives (check R). Four cases read the block's captured member
    /// and keep one value per activation; <c>result-member-receiver</c>, the route of the extension's own block-headed
    /// cells (a block-headed path continued through a lexical fallback into a call reference's intrinsic), is refused
    /// inside the call in the case and in its twin alike. Their runtime outcomes cannot distinguish the lost level.
    /// </summary>
    [Fact]
    public async Task DeconstructionFamily_ReadsABlockWrittenInTheRightHandSide_AndMatchesItsRowsTwin()
    {
        var family = CensusGrid.DeconstructionFamilies();
        Assert.Equal(["deconstruction=inline-alg-call", "deconstruction=inline-capture", "deconstruction=inline-capture-invoke",
            "deconstruction=result-member-argument", "deconstruction=result-member-receiver"], family.Select(c => c.Id));
        var values = ("ok S[5, 0]", "ok S[7, 0]", "ok S[S[5, 0], S[7, 0]]", "err localOnlyProperty:A");
        var expected = new Dictionary<string, (string, string, string, string)>
        {
            ["deconstruction=inline-alg-call"] = values,
            ["deconstruction=inline-capture"] = values,
            ["deconstruction=inline-capture-invoke"] = values,
            // Mk(k) = r * 0 + k + 2, called afresh with the block's Q = y.
            ["deconstruction=result-member-argument"] = ("ok S[7, 0]", "ok S[9, 0]", "ok S[S[7, 0], S[9, 0]]", "err localOnlyProperty:A"),
            ["deconstruction=result-member-receiver"] = ("err localOnlyProperty:Sub", "err localOnlyProperty:Sub", "err localOnlyProperty:Sub", "err localOnlyProperty:A"),
        };
        foreach (var @case in family)
        {
            Assert.Equal(("deconstruction-family", 0), (@case.Kind, @case.Dims.Count));
            Assert.Null(CensusGrid.ImpossibleMember(@case));
            Assert.True(CensusGrid.HasRowsTwin(@case));
            var twin = CensusGrid.DeconstructionTwin(@case);
            Assert.Equal((@case.Id, "deconstruction-twin"), (twin.Id, twin.Kind));
            // `a, b = <selection> + 0, 0` and the row `a, b` become `<selection> + 0, 0`; every other line is the case's own.
            const string deconstruction = "    a, b = ", targets = " + 0, 0\n    a, b\n";
            var start = @case.Body.IndexOf(deconstruction, StringComparison.Ordinal);
            Assert.True(start >= 0 && start == @case.Body.LastIndexOf(deconstruction, StringComparison.Ordinal), @case.Id);
            var close = @case.Body.IndexOf(targets, start, StringComparison.Ordinal);
            Assert.True(close > start, @case.Id);
            Assert.Equal(@case.Body[..start] + "    " + @case.Body[(start + deconstruction.Length)..close] + " + 0, 0\n" + @case.Body[(close + targets.Length)..], twin.Body);
            // The selection writes a block inside the right-hand side.
            Assert.Contains("{\n", @case.Body[start..close], StringComparison.Ordinal);
            SourceProvenance.ParseValid(@case.Body + CensusRunner.SameRun);
            SourceProvenance.ParseValid(twin.Body + CensusRunner.SameRun);

            var result = await CensusRunner.Run(@case, collectLean: false);
            Assert.Null(result.Skipped);
            Assert.True(result.Gaps.Count == 0, $"{@case.Id}: {string.Join("\n", result.Gaps.Select(gap => gap.Line))}");
            Assert.Empty(result.UnknownName);
            Assert.Equal("LocalOnlyCapturedAncestorParameters[y@0]", result.Metadata["A"]);
            Assert.Equal(expected[@case.Id], Probes(result.Outcomes));
            var (twinOutcomes, twinMetadata) = CensusRunner.TwinFacts(twin, ProbeLabels);
            Assert.Equal(expected[@case.Id], Probes(twinOutcomes));
            Assert.Equal(result.Metadata, twinMetadata);
        }

        // Check R: the inline .Algorithm route against the static selection of the algorithm whose call Sub captures.
        var inline = DeconstructionCase("inline-alg-call");
        Assert.True(CensusRunner.HasStaticRouteTwin(inline));
        var route = CensusGrid.StaticRouteTwin(inline);
        Assert.Equal((inline.Id, "static-route-twin"), (route.Id, route.Kind));
        Assert.Equal(inline.Body.Replace("}.Sub.Algorithm + 0, 0\n", "}.Sub.Run + 0, 0\n", StringComparison.Ordinal), route.Body);
        Assert.NotEqual(inline.Body, route.Body);
        Assert.Equal(values, Probes(CensusRunner.TwinFacts(route, ProbeLabels).Outcomes));
        foreach (var other in family.Where(c => c.Id != inline.Id))
        {
            Assert.False(CensusRunner.HasStaticRouteTwin(other));
            Assert.Throws<ArgumentException>(() => CensusGrid.StaticRouteTwin(other));
        }
        Assert.Throws<ArgumentException>(() => CensusGrid.DeconstructionTwin(CarrierCase("row")));

        // The refused route is the extension's own block-headed cell: refused in the cell and in its rows twin alike, where
        // the same literal read through a lexical continuation (the grid's mid-fallback ending) is admitted in both.
        foreach (var (end, inside) in new[] { ("result-member", "err localOnlyProperty:Sub"), ("mid-fallback", "ok S[2, 0]") })
        {
            var cell = CensusGrid.Build(["block", "deconstruction", "none", "plain", "outside", end, "container"]);
            var observed = await CensusRunner.Run(cell, collectLean: false);
            Assert.Null(observed.Skipped);
            Assert.Empty(observed.Gaps);
            Assert.Equal(inside, observed.Outcomes["in5"]);
            Assert.Equal(inside, CensusRunner.TwinFacts(CensusGrid.DeconstructionTwin(cell), ProbeLabels).Outcomes["in5"]);
        }
        // The refusal does not come from reading the receiver: a fallback whose result never reads it is refused too.
        var receiver = DeconstructionCase("result-member-receiver");
        var unread = receiver with { Body = receiver.Body.Replace("Mk(k) = r * 0 + k + 2", "Mk(k) = k + 2", StringComparison.Ordinal) };
        Assert.NotEqual(receiver.Body, unread.Body);
        Assert.Equal("err localOnlyProperty:Sub", CensusRunner.TwinFacts(unread, ProbeLabels).Outcomes["in5"]);
    }

    /// <summary>
    /// What check T rests on for a block written in a deconstruction's right-hand side, read from the front end's own tree:
    /// the block's captured member publishes its capture position ONE LEVEL DEEPER than the same block in the rows twin,
    /// the synthetic source property's level (da209fa0, <c>ExposureWalkMemos.ForDeconstructionSourceRows</c>). A position
    /// counted on the written chain alone would equal the twin's, and the evaluators would refuse the member inside its own
    /// owner's call. Every family case shows it, and so does the original grid's block-headed cell, the positive control the
    /// stored cover and <see cref="DeconstructionPosition_MatchesItsRowsTwinForEveryHead"/> keep. The refused
    /// <c>result-member-receiver</c> publishes the right position too: its refusal is not the position's.
    /// </summary>
    [Fact]
    public void DeconstructionSource_CountsItsLevelInABlocksCapturePositions()
    {
        (CensusCase Case, string Member)[] blocks =
        [
            (DeconstructionCase("inline-alg-call"), "Run"),
            (DeconstructionCase("inline-capture"), "Seed"),
            (DeconstructionCase("inline-capture-invoke"), "Seed"),
            (DeconstructionCase("result-member-argument"), "Q"),
            (DeconstructionCase("result-member-receiver"), "Sub"),
            (CensusGrid.Build(["block", "deconstruction", "none", "plain", "outside", "found", "member"]), "G"),
            (CensusGrid.Build(["group-block", "deconstruction", "none", "plain", "outside", "found", "member"]), "G"),
        ];
        foreach (var (@case, member) in blocks)
        {
            var written = Position(@case, member);
            var rows = Position(CensusGrid.DeconstructionTwin(@case), member);
            Assert.True(written.Name == "y" && rows.Name == "y" && written.OwnerDepth == rows.OwnerDepth + 1,
                $"{@case.Id} {member}: deconstruction {CensusRunner.Requirement(written)}; rows {CensusRunner.Requirement(rows)}");
        }

        // The one declaration of that name the reader writes, in a block of its expressions, and its one requirement.
        static CapturedParameterRequirement Position(CensusCase @case, string member)
        {
            var root = SourceProvenance.ParseValid(@case.Body + CensusRunner.Inside5 + "\n").Root;
            var reader = CensusRunner.Find(root, ReaderA) ?? throw new InvalidDataException($"No reader A: {@case.Id}");
            Assert.Null(CensusRunner.Find(root, [.. ReaderA, member]));
            var declaration = Assert.Single(CensusRunner.DeclarationsNamed(reader.Value, member));
            return Assert.Single(CensusRunner.Requirements(declaration));
        }
    }

    /// <summary>
    /// The carrier family: a loaded module whose single output row names an algorithm elaborates to an alias carrier that
    /// keeps the module mark, and its ordinary alias twin writes the same text in braces at the holder's own place. Two
    /// holders of one canonical URL (in both spellings) are one provider of <c>X</c>, charged the walk of <c>Lib.Sub</c>
    /// exactly as the twin; two canonical URLs serving the text are two, whose unqualified read is AmbiguousOpen in the
    /// module program and in the twin that writes the carrier twice; the single output read as a value forwards to the
    /// row's target. Where the holder stands in <c>F</c> beside <c>W = y</c> the loaded carrier is cut from that chain: its
    /// row, its member and its member read through an open give the module's own 3 from an exported reader, while the
    /// written carrier reads <c>F</c>'s <c>W</c> and is charged <c>y</c>.
    /// </summary>
    [Fact]
    public async Task CarrierFamily_ALoadedAliasCarrierIsOneProviderPerUrl_AndIsCutFromItsHolder()
    {
        var family = CensusGrid.CarrierFamilies();
        Assert.Equal(["carrier=open-same-url", "carrier=open-holder-load", "carrier=open-two-urls", "carrier=row",
            "carrier=cut-row", "carrier=cut-member", "carrier=cut-open"], family.Select(c => c.Id));
        const string charged = "LocalOnlyCapturedAncestorParameters[y@0]";
        var provided = (("ok 1", "ok 1", "ok S[1, 1]", "err localOnlyProperty:A"), charged);
        var constant = (("ok 3", "ok 3", "ok S[3, 3]", "ok 3"), "exported");
        var holderRead = (("ok 5", "ok 7", "ok S[5, 7]", "err localOnlyProperty:A"), charged);
        // (the loaded program's probes and reader metadata; its ordinary alias twin's)
        var expected = new Dictionary<string, (((string, string, string, string), string) Module, ((string, string, string, string), string) Ordinary)>
        {
            ["carrier=open-same-url"] = (provided, provided),
            ["carrier=open-holder-load"] = (provided, provided),
            ["carrier=open-two-urls"] = ((("ok 1", "ok 1", "ok S[1, 1]", "ok 1"), "exported"), (("ok 1", "ok 1", "ok S[1, 1]", "ok 1"), "exported")),
            ["carrier=row"] = (constant, constant),
            ["carrier=cut-row"] = (constant, holderRead),
            ["carrier=cut-member"] = (constant, holderRead),
            ["carrier=cut-open"] = (constant, holderRead),
        };
        var one = $"providers 1; identities 1; fetched {CensusGrid.CarrierUrl}; unqualified clean";
        var none = $"providers 0; identities 1; fetched {CensusGrid.CarrierUrl}; unqualified clean";
        var verdicts = new Dictionary<string, string>
        {
            ["carrier=open-same-url"] = one,
            ["carrier=open-holder-load"] = one,
            ["carrier=open-two-urls"] = $"providers 2; identities 2; fetched {CensusGrid.CarrierCopyUrl},{CensusGrid.CarrierUrl}; unqualified AmbiguousOpen",
            ["carrier=row"] = none,
            ["carrier=cut-row"] = none,
            ["carrier=cut-member"] = none,
            ["carrier=cut-open"] = one,
        };
        // The module's one row names an algorithm, and nothing else is a row.
        Assert.EndsWith("public V = W + 0\nW\n", CensusGrid.CarrierText, StringComparison.Ordinal);
        foreach (var @case in family)
        {
            var cut = @case.Id.StartsWith("carrier=cut-", StringComparison.Ordinal);
            string[] holderPath = cut ? ["F", "M"] : ["ModA"];
            Assert.Equal(("carrier", 0), (@case.Kind, @case.Dims.Count));
            string[] urls = @case.Id == "carrier=open-two-urls" ? [CensusGrid.CarrierUrl, CensusGrid.CarrierCopyUrl] : [CensusGrid.CarrierUrl];
            Assert.Equal(urls, @case.Modules!.Select(m => m.Key));
            Assert.All(@case.Modules!, module => Assert.Equal(CensusGrid.CarrierText, module.Value));
            Assert.Equal(verdicts[@case.Id], CensusGrid.ExpectedProviderVerdict(@case));

            // The loaded holder is an alias that keeps the module mark: a carrier, never a transparent reference.
            var root = (await SourceProvenance.ParseValidAsync(@case.Body + CensusRunner.Inside5 + "\n", CensusRunner.ModuleServer(@case).Options())).Root;
            var holder = CensusRunner.Find(root, holderPath)!;
            var loaded = Assert.IsType<Algorithm.Alias>(holder.Value);
            Assert.True(loaded.IsModuleRoot && !loaded.IsReference, @case.Id);
            Assert.Equal("exported", CensusRunner.Describe(holder));
            Assert.Equal(@case.Id == "carrier=open-two-urls" ? 2 : 1, CensusRunner.ModuleIdentities(root));

            // The ordinary alias twin loads nothing: the same text in braces at the holder's place, an ordinary carrier.
            var twin = CensusGrid.CarrierTwin(@case);
            Assert.Equal((@case.Id, "carrier-twin"), (twin.Id, twin.Kind));
            Assert.Null(twin.Modules);
            Assert.DoesNotContain("load(", twin.Body, StringComparison.Ordinal);
            Assert.Contains($"{holderPath[^1]} = {{\n{CensusGrid.Indent(CensusGrid.CarrierText.TrimEnd('\n'), cut ? 4 : 2)}\n", twin.Body, StringComparison.Ordinal);
            var twinRoot = SourceProvenance.ParseValid(twin.Body + CensusRunner.Inside5 + "\n").Root;
            var written = Assert.IsType<Algorithm.Alias>(CensusRunner.Find(twinRoot, holderPath)!.Value);
            Assert.True(!written.IsModuleRoot && !written.IsReference, @case.Id);
            Assert.Equal(0, CensusRunner.ModuleIdentities(twinRoot));

            var result = await CensusRunner.Run(@case, collectLean: false);
            Assert.Null(result.Skipped);
            Assert.True(result.Gaps.Count == 0, $"{@case.Id}: {string.Join("\n", result.Gaps.Select(gap => gap.Line))}");
            Assert.Empty(result.UnknownName);
            Assert.Empty(result.Impossible);
            Assert.Equal(verdicts[@case.Id], result.ProviderVerdict);
            Assert.Equal(expected[@case.Id].Module, (Probes(result.Outcomes), result.Metadata["A"]));
            var (twinOutcomes, twinMetadata) = CensusRunner.TwinFacts(twin, ProbeLabels);
            Assert.Equal(expected[@case.Id].Ordinary, (Probes(twinOutcomes), twinMetadata["A"]));
            // The twin relation is those two rows' difference: none, or the cut's five lines.
            Assert.Equal(cut ? 5 : 0, CensusGrid.CarrierContrast(@case).Count);
            Assert.Equal(cut ? charged : "exported", CensusRunner.Describe(CensusRunner.Find(twinRoot, holderPath)));
        }

        // The same-URL twin's second holder is a transparent reference to the written carrier: one declaration, one provider.
        var sameUrl = SourceProvenance.ParseValid(CensusGrid.CarrierTwin(CarrierCase("open-same-url")).Body + CensusRunner.Inside5 + "\n").Root;
        Assert.True(Assert.IsType<Algorithm.Alias>(CensusRunner.Find(sameUrl, ["ModB"])!.Value).IsReference);

        // The distinct-URL control: the unqualified read is AmbiguousOpen in the loaded program and in the twin's two carriers.
        var control = CarrierCase("open-two-urls");
        foreach (var program in new[] { control, CensusGrid.CarrierTwin(control) })
        {
            var unqualified = CensusGrid.ModuleUnqualifiedRead(program);
            Assert.Equal(program.Body.Replace("A = ModA.X + 0", "A = X + 0", StringComparison.Ordinal), unqualified.Body);
            Assert.NotEqual(program.Body, unqualified.Body);
            var source = unqualified.Body + CensusRunner.Inside5 + "\n";
            var parsed = program.Modules is null ? Parser.Parse(source) : await Parser.ParseAsync(source, CensusRunner.ModuleServer(unqualified).Options());
            Assert.Equal(DiagnosticCode.AmbiguousOpen, Assert.Single(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error).Code);
        }
        // Every other case reads X unqualified already, or not at all.
        Assert.All(family.Where(c => c.Id != control.Id), c => Assert.Same(c, CensusGrid.ModuleUnqualifiedRead(c)));
    }

    /// <summary>
    /// The carrier checks cannot pass by accident: a distinct-URL control that loads one canonical URL twice shows one
    /// provider and a clean unqualified read (not the control's verdict), a missing download is a validity difference (the
    /// ordinary twin parses), a carrier that read its holder's chain would equal its twin and miss every difference of the
    /// cut, and a twin that differs where the relation says equal is a difference of its own class.
    /// </summary>
    [Fact]
    public async Task CarrierFamily_AMergedControlAMissingDownloadOrALostCutCannotPass()
    {
        var control = CarrierCase("open-two-urls");
        var merged = control with
        {
            Body = control.Body.Replace($"ModB = load('{CensusGrid.CarrierCopyUrl}')", $"ModB = load('{CensusGrid.CarrierUrl}')", StringComparison.Ordinal),
        };
        Assert.NotEqual(control.Body, merged.Body);
        var result = await CensusRunner.Run(merged, collectLean: false);
        Assert.Null(result.Skipped);
        Assert.Equal($"providers 1; identities 1; fetched {CensusGrid.CarrierUrl}; unqualified clean", result.ProviderVerdict);
        Assert.Contains(result.Gaps, g => g is { Check: "P", Class: "provider-verdict-differs" });

        var sameUrl = CarrierCase("open-same-url");
        var missing = await CensusRunner.Run(sameUrl with { Modules = [new(CensusGrid.CarrierCopyUrl, CensusGrid.CarrierText)] }, collectLean: false);
        Assert.NotNull(missing.Skipped);
        var gap = Assert.Single(missing.Gaps);
        Assert.Equal(("P", "module-validity-differs"), (gap.Check, gap.Class));

        var cut = CarrierCase("cut-row");
        var observed = await CensusRunner.Run(cut, collectLean: false);
        var (twinOutcomes, twinMetadata) = CensusRunner.TwinFacts(CensusGrid.CarrierTwin(cut), ProbeLabels);
        Assert.Empty(CensusRunner.CarrierTwinGaps(cut.Id, CensusGrid.CarrierContrast(cut), observed.Outcomes, observed.Metadata, twinOutcomes, twinMetadata));
        var lost = CensusRunner.CarrierTwinGaps(cut.Id, CensusGrid.CarrierContrast(cut), twinOutcomes, twinMetadata, twinOutcomes, twinMetadata);
        Assert.Equal(5, lost.Count);
        Assert.All(lost, g => Assert.Equal(("P", "carrier-cut-missing", cut.Id), (g.Check, g.Class, g.Id)));
        Assert.Equal(["-", "-", "-", "-", "A"], lost.Select(g => g.Reader));

        var row = CarrierCase("row");
        var differing = CensusRunner.CarrierTwinGaps(row.Id, CensusGrid.CarrierContrast(row), observed.Outcomes, observed.Metadata, twinOutcomes, twinMetadata);
        Assert.Equal(5, differing.Count);
        Assert.All(differing, g => Assert.Equal(("P", "carrier-twin-differs", row.Id), (g.Check, g.Class, g.Id)));
        Assert.Throws<ArgumentException>(() => CensusGrid.CarrierTwin(DeconstructionCase("inline-capture")));
    }

    /// <summary>
    /// U2's unknown-required-name arm, on HOST-BUILT trees (the front end charges both readers, so no source of the census
    /// shows the arm). A reader whose only charge is its fallback's read of <c>y</c> is exported by the host: its escaped
    /// read then fails with <c>UnknownName: y</c>, no access refusal. With parameters of its own the reader is not cached
    /// across activations, so U1 sees consistent values and no existing check reports anything; the arm records the read
    /// (<c>unknown-name-alone</c>). A parameterless reader is cached, U1 reports the wrong value, and the arm records the
    /// same reader beside it (<c>unknown-name-with-wrong-value</c>). Neither observation is a gap.
    /// </summary>
    [Fact]
    public async Task UnknownRequiredNameArm_SeesTheReadTheOtherChecksMiss()
    {
        static Func<Algorithm.User, Algorithm.User> Exported(string[] reader) => root =>
        {
            var property = CensusRunner.Find(root, reader)!;
            return CensusRunner.Replace(root, reader, current => CensusRunner.Requirements(property).Aggregate(current, CensusRunner.Without));
        };

        var parameterized = CensusGrid.Build(["rt-capture", "value", "none", "param", "outside", "mid-fallback", "fallback"]);
        var charged = await CensusRunner.Run(parameterized, collectLean: false);
        Assert.Equal("LocalOnlyCapturedAncestorParameters[y@0]", charged.Metadata["A"]);
        Assert.Empty(charged.Gaps);
        Assert.Empty(charged.UnknownName);

        var uncached = await CensusRunner.Run(parameterized, collectLean: false, hostBuilt: Exported(ReaderA));
        Assert.Equal("exported", uncached.Metadata["A"]);
        Assert.Equal(("ok 5", "ok 7", "ok S[5, 7]", "err unknownName:y"), Probes(uncached.Outcomes));
        Assert.Empty(uncached.Gaps);
        Assert.Empty(uncached.Impossible);
        Assert.Equal(new CensusGap("U", "unknown-name-alone", parameterized.Id, "A", "err unknownName:y; requires y of F; inside=ok 5 / ok 7 / ok S[5, 7]"),
            Assert.Single(uncached.UnknownName));

        var plain = CensusGrid.Build(["rt-capture", "value", "none", "plain", "outside", "mid-fallback", "fallback"]);
        var cached = await CensusRunner.Run(plain, collectLean: false, hostBuilt: Exported(ReaderA));
        Assert.Equal("exported", cached.Metadata["A"]);
        var wrong = Assert.Single(cached.Gaps);
        Assert.Equal(("U", "under-charge-wrong-value"), (wrong.Check, wrong.Class));
        var seen = Assert.Single(cached.UnknownName);
        Assert.Equal(("U", "unknown-name-with-wrong-value", "A"), (seen.Check, seen.Class, seen.Reader));
        Assert.EndsWith("case verdicts=U/under-charge-wrong-value", seen.Detail, StringComparison.Ordinal);

        // The same exported parameterized reader on the .Algorithm route disagrees with its source twin in R.
        // Its escaped unknown name is additional evidence, while the case already has a verdict.
        var routed = CensusGrid.Build(["rt-alg-call", "value", "none", "param", "outside", "mid-fallback", "fallback"]);
        var overlap = await CensusRunner.Run(routed, collectLean: false, hostBuilt: Exported(ReaderA));
        Assert.Contains(overlap.Gaps, g => g.Check == "R");
        var alongsideTwin = Assert.Single(overlap.UnknownName);
        Assert.Equal("unknown-name-with-other-verdict", alongsideTwin.Class);
        Assert.Contains("case verdicts=R/", alongsideTwin.Detail, StringComparison.Ordinal);

        // The arm names a parameter an ENCLOSING level binds: no other unknown name, and never the reader's own parameter.
        var tree = SourceProvenance.ParseValid(parameterized.Body + CensusRunner.Inside5 + "\n").Root;
        Assert.Equal("y of F", CensusRunner.UnknownRequiredName(tree, ReaderA, "err unknownName:y"));
        Assert.Null(CensusRunner.UnknownRequiredName(tree, ReaderA, "err unknownName:z"));
        Assert.Null(CensusRunner.UnknownRequiredName(tree, ReaderA, "err unknownName:Undeclared"));
        Assert.Null(CensusRunner.UnknownRequiredName(tree, ReaderA, "err localOnlyProperty:y"));
        Assert.Null(CensusRunner.UnknownRequiredName(tree, ["F", "Absent", "A"], "err unknownName:y"));
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
            var module = CensusGrid.BuildModule([.. ChargedModuleTwin("enc1-unused"), "two-urls"]);
            var lines = (await CensusRunner.Probes(@case))!.Select(p => CensusHeadProbe.InputLine(@case.Id, p.Label, p.Source, null))
                .Concat((await CensusRunner.Probes(module))!.Select(p => CensusHeadProbe.InputLine(module.Id, p.Label, p.Source, module.Modules)))
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
            Assert.Equal("OK S[1, 1]", head.Outcomes(module.Id)["same:forced"]);

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

            // The extension's sample has batches and a manifest of its own: neither sample reads the other's output.
            CensusLean.Emit(items, directory);
            File.WriteAllText(path, observation);
            CensusLeanItem[] extension = [new("two#real#in5", "two", "real", "real", SourceProvenance.ParseValid("2").Root, "ok 2")];
            Assert.Equal(1, CensusLean.Emit(extension, directory, "census-extension"));
            Assert.True(File.Exists(Path.Combine(directory, "census-extension-0000.lean")));
            Assert.Equal("manifest-extension.tsv", CensusLean.ManifestName("census-extension"));
            Assert.Throws<InvalidDataException>(() => CensusLean.Check(directory, extension, "census-extension"));
            File.WriteAllText(Path.Combine(directory, "census-extension-0000.out"), "CENSUS\ttwo#real#in5\ttrue\ttrue\tok 2\n");
            Assert.Empty(CensusLean.Check(directory, extension, "census-extension"));
            Assert.Empty(CensusLean.Check(directory, items));
            Assert.Throws<ArgumentException>(() => CensusLean.ManifestName("extension"));

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
