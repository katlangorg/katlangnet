using System.Text;

namespace KatLang.Tests;

/// <summary>
/// Presence witnesses at a level whose closed member index waits once ordinary work is quiescent (November 2026).
/// A name's deferred presence (<see cref="StaticQueryProjection.DeferredOpenPresence"/>) reads its presence witnesses
/// only while that index is unknown. Three things make an index wait: a provider that depends on one of the level's
/// own names (SELF-DEPENDENT), a target that an open receiver-expansion verdict decides (VERDICT), and a target that
/// another level's emptiness certificate decides (CERTIFICATE). Every name of such a level used to build all 2K − 1
/// witness ranges over the level's K targets, and a preserved-presence certificate solved every earlier target per
/// present name. A settled range with at most one occurrence of the name answers from Q2's shared provider range,
/// a certificate reads a settled earlier target directly, and a deferred presence yields to the pending verdicts.
/// Facts, diagnostics, provider order and wording are those of the generic paths.
/// </summary>
public sealed class OpenWitnessSettlementTests
{
    private static string Opens(int targets) => string.Join(", ", Enumerable.Range(0, targets).Select(i => $"L{i}"));

    private static string Sum(IEnumerable<string> names) => string.Join(" + ", names);

    private static IEnumerable<string> Names(int names) => Enumerable.Range(0, names).Select(j => $"a{j}");

    /// <summary>K libraries <c>L0..</c>; library <c>i</c> declares the public members <paramref name="members"/> gives it (or one unread member).</summary>
    private static string Libraries(int targets, Func<int, IEnumerable<string>> members)
    {
        var text = new StringBuilder();
        for (var i = 0; i < targets; i++)
        {
            text.Append($"L{i} = {{\n");
            var any = false;
            foreach (var member in members(i))
            {
                text.Append($"    public {member} = {i}\n");
                any = true;
            }
            if (!any) text.Append($"    public z{i} = {i}\n");
            text.Append("}\n");
        }
        return text.ToString();
    }

    private static IEnumerable<string> Own(int library, int targets, int names) => Names(names).Where((_, j) => j % targets == library);

    /// <summary>
    /// SELF-DEPENDENT: P's provider <c>R = C</c> is a reference only if C has no input, and C reads <c>q</c>, which is P's
    /// input unless an open provides it, so P's index settles only after <c>q</c>'s presence is known.
    /// <paramref name="late"/> places R among the K library targets ("first", "middle" or "last"). With
    /// <paramref name="members"/>, C declares those public members and <c>L.q</c> is a number, so R provides C's members;
    /// otherwise <c>L.q = P.R</c> makes R's target a refused cycle that provides nothing.
    /// </summary>
    private static string SelfDependent(int targets, int names, string late = "last", string[]? members = null, string extra = "",
        Func<int, IEnumerable<string>>? libraries = null)
    {
        var list = Enumerable.Range(0, targets).Select(i => $"L{i}").ToList();
        list.Insert(late switch { "first" => 0, "middle" => targets / 2, _ => targets }, "R");
        var c = string.Concat((members ?? []).Select(member => $"    public {member} = 9\n"));
        return Libraries(targets, libraries ?? (i => (i == 0 ? ["q"] : Array.Empty<string>()).Concat(Own(i, targets, names))))
            + $"L = {{\n    public q = {(members is null ? "P.R" : "5")}\n}}\n"
            + $"P = {{\n    open {string.Join(", ", list)}\n    public R = C\n    C = {{ open L\n{c}    q }}\n"
            + $"    {Sum(Names(names).Prepend("q").Concat(extra.Length == 0 ? [] : [extra]))}\n}}\n"
            + "0\n";
    }

    /// <summary>VERDICT: Use's last target <c>P3 = C1</c> sits on a ring of member-path bodies, decided by an open receiver-expansion verdict.</summary>
    private static string VerdictTarget(int targets, int names)
        => Libraries(targets, i => Own(i, targets, names))
            + "A1 = B1\nB1 = { public M = C2\n 0 }\nC1 = A1.M.abs\nA2 = B2\nB2 = { public M = C1\n 0 }\nC2 = A2.M.abs\nP3 = C1\n"
            + $"Use = {{\n    open {Opens(targets)}, P3\n    {Sum(Names(names))}\n}}\n1\n";

    /// <summary>
    /// CERTIFICATE: Use's last target <c>G.Sub = W</c> reads <c>W</c> through G's own open, which G's level-wide emptiness
    /// certificate (a closure observer, queued after Use's) decides. An open target never resolves through another open,
    /// so the program reports <see cref="DiagnosticCode.UnresolvedOpenTarget"/>.
    /// </summary>
    private static string CertificateTarget(int targets, int names)
        => Libraries(targets, i => Own(i, targets, names))
            + $"Use = {{\n    open {Opens(targets)}, G.Sub\n    {Sum(Names(names))}\n}}\n"
            + "M = { public W = { public zz = 1 } }\nG = {\n  open M\n  public Sub = W\n}\n1\n";

    private static (FrontEndTraversalObservations Observations, DetectedProgram Program, Algorithm Syntax) Detect(string source)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var observations = new FrontEndTraversalObservations();
        var program = ParameterDetector.DetectPrevalidated(syntax, observations: observations);
        return (observations, program, syntax);
    }

    /// <summary>The written declaration <paramref name="member"/> of the root property <paramref name="owner"/> (a dotted path).</summary>
    private static Property Declared(Algorithm syntax, string owner, string member)
    {
        var body = syntax;
        foreach (var step in owner.Split('.')) body = body.Properties.Single(property => property.Name == step).Value;
        return body.Properties.Single(property => property.Name == member);
    }

    private static List<StaticQueryKey> Witnesses(FrontEndTraversalObservations observations)
        => observations.StaticQueryEvaluations.Keys.Where(key => key.Projection == StaticQueryProjection.OpenPresenceWitnesses).ToList();

    private static int Log2Ceiling(int value) => value <= 1 ? 0 : 32 - System.Numerics.BitOperations.LeadingZeroCount((uint)(value - 1));

    private static StaticScopeKey Body(DetectedProgram program, string name)
    {
        var operation = program.Operation!;
        return operation.ContextOf(operation.Root, program.Root.Properties.Single(property => property.Name == name).Value);
    }

    // ── Self-dependent levels ─────────────────────────────────────────────────────────────────

    /// <summary>
    /// SELF-DEPENDENT, with the unsettled provider last. Each name still reads its witnesses, which decide <c>q</c>'s
    /// presence before the provider list settles, but its tree now splits only towards that one unsettled target: a
    /// range whose targets have all settled answers in one pass. A tree is 2⌈log2(K + 1)⌉ + 1 ranges (17 at K = 128)
    /// instead of 2(K + 1) − 1 (257); at K = N = 128 detection built 33,924 witness ranges, now 2,244.
    /// </summary>
    [Theory]
    [InlineData(8)]
    [InlineData(32)]
    [InlineData(128)]
    public void ASelfDependentLevel_SplitsOnlyTowardsItsUnsettledTarget(int targets)
    {
        const int names = 32;
        var (observations, program, _) = Detect(SelfDependent(targets, names));
        Assert.Empty(program.Diagnostics);
        var operation = program.Operation!;
        var p = Body(program, "P");
        Assert.Equal(StaticFactKind.No, operation.Read(StaticQueryKey.IsInput(p, "q")).Kind);
        Assert.Empty(Assert.IsType<string[]>(operation.Read(StaticQueryKey.Inputs(p)).Data));

        var witnesses = Witnesses(observations);
        Assert.All(witnesses, key => Assert.Same(p, key.Scope));
        var trees = witnesses.Select(key => (key.Name, key.Stratum)).Distinct().Count();
        // The 32 written names and q and C in the formation stratum, q and C again in the lower one.
        Assert.Equal(names + 4, trees);
        Assert.Equal(trees * (2 * Log2Ceiling(targets + 1) + 1), witnesses.Count);
        Assert.True(observations.StaticSettledWitnessRanges >= trees);
        // Each present name is certified once at its own position, as before.
        Assert.Equal(names + 2, observations.StaticQueryEvaluations.Keys.Count(key => key.Projection == StaticQueryProjection.PreservedOpenPresence));
    }

    /// <summary>
    /// Where the unsettled provider sits changes which ranges settle, never the answers: first, in the middle and last,
    /// every written name is P's opened declaration, <c>q</c> is no input and nothing is ambiguous.
    /// </summary>
    [Theory]
    [InlineData("first")]
    [InlineData("middle")]
    [InlineData("last")]
    public void TheUnsettledProvidersPosition_ChangesNoAnswer(string late)
    {
        const int targets = 16, names = 16;
        var (observations, program, syntax) = Detect(SelfDependent(targets, names, late));
        Assert.Empty(program.Diagnostics);
        var operation = program.Operation!;
        var p = Body(program, "P");
        Assert.Empty(Assert.IsType<string[]>(operation.Read(StaticQueryKey.Inputs(p)).Data));
        foreach (var (name, library) in Names(names).Select((name, j) => (name, j % targets)))
        {
            var binding = operation.Read(StaticQueryKey.Binding(p, name, StaticCycleCheck.Formation));
            Assert.Equal(StaticFactKind.Declaration, binding.Kind);
            Assert.Same(Declared(syntax, $"L{library}", name), binding.Property);
        }
        Assert.NotEmpty(Witnesses(observations));
        Assert.True(observations.StaticSettledWitnessRanges > 0);
    }

    /// <summary>
    /// GUARD AGAINST PREMATURE ANSWERS. While P's provider R is unsettled, a settled range that offers a name may say only
    /// that the name is present (it is no input), never which declaration it selects, and a settled range that does not
    /// offer it may not make it absent. Here R = C ends up providing C's <c>a0</c>, which L0 also offers, and <c>b</c>,
    /// which no library offers: <c>a0</c> is ambiguous between L0 and R and <c>b</c> is C's declaration, while
    /// <c>x0</c>, which nothing provides, is P's input. Answering from the settled libraries alone would have selected
    /// L0's <c>a0</c> and made <c>b</c> an input.
    /// </summary>
    [Fact]
    public void ALateProvider_DecidesTheNamesItOffers()
    {
        const int targets = 12, names = 12;
        var source = SelfDependent(targets, names, "middle", members: ["a0", "b"], extra: "b + x0");
        var (observations, program, syntax) = Detect(source);
        var diagnostic = Assert.Single(program.Diagnostics);
        Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code);
        Assert.StartsWith("'a0' is ambiguous: 2 different opened algorithms provide it at the same open level (L0, R)", diagnostic.Message, StringComparison.Ordinal);
        var operation = program.Operation!;
        var p = Body(program, "P");
        Assert.Equal(["x0"], Assert.IsType<string[]>(operation.Read(StaticQueryKey.Inputs(p)).Data));
        Assert.Equal(StaticFactKind.No, operation.Read(StaticQueryKey.IsInput(p, "b")).Kind);
        var b = operation.Read(StaticQueryKey.Binding(p, "b", StaticCycleCheck.Formation));
        Assert.Equal(StaticFactKind.Declaration, b.Kind);
        Assert.Same(Declared(syntax, "P.C", "b"), b.Property);
        Assert.Equal(StaticFactKind.Ambiguous, operation.Read(StaticQueryKey.Binding(p, "a0", StaticCycleCheck.Formation)).Kind);
        Assert.NotEmpty(Witnesses(observations));
        Assert.True(observations.StaticSettledWitnessRanges > 0);
    }

    /// <summary>
    /// Genuine ambiguity at a self-dependent level: names two libraries offer are reported in written order, each naming
    /// its providers in open order, exactly as the generic witness path reported them.
    /// </summary>
    [Fact]
    public void AmbiguousNamesAtASelfDependentLevel_KeepTheirOrderAndWording()
    {
        const int targets = 16, names = 16;
        var source = SelfDependent(targets, names, libraries: i => (i == 0 ? ["q"] : Array.Empty<string>())
            .Concat(Names(names).Where((_, j) => j % targets == i || j % 4 == 1 && (j + 1) % targets == i)));
        var (observations, program, _) = Detect(source);
        var expected = Names(names).Select((name, j) => (name, j)).Where(pair => pair.j % 4 == 1)
            .Select(pair => $"'{pair.name}' is ambiguous: 2 different opened algorithms provide it at the same open level (L{pair.j % targets}, L{(pair.j + 1) % targets})")
            .ToArray();
        Assert.Equal(4, expected.Length);
        Assert.Equal(expected.Length, program.Diagnostics.Count);
        Assert.All(program.Diagnostics, diagnostic => Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code));
        Assert.All(expected.Zip(program.Diagnostics), pair => Assert.StartsWith(pair.First, pair.Second.Message, StringComparison.Ordinal));
        Assert.NotEmpty(Witnesses(observations));
    }

    [Theory]
    [InlineData(32)]
    [InlineData(128)]
    public void RepeatedOccurrencesAtAWaitingLevel_BoundCertificateFanIn(int repeats)
    {
        var opens = string.Join(", ", Enumerable.Repeat("Lib", repeats));
        var source = $"Lib = {{ public a = 1 }}\nL0 = {{ public q = 1 }}\nL = {{ public q = P.R }}\n"
            + $"P = {{\n    open {opens}, L0, R\n    public R = C\n    C = {{ open L\n    q }}\n    q + a\n}}\n0\n";
        var root = SourceProvenance.ParseSyntaxValidRoot(source);
        var observations = new FrontEndTraversalObservations();
        var q = new StaticStructureQueries(root, new(1_000_000, 4, 100_000, 4_000_000)) { Observations = observations };
        var p = q.BodyIn(q.Root, root.Properties.Single(property => property.Name == "P").Value);
        Assert.Empty(Assert.IsType<string[]>(q.Get(StaticQueryKey.Inputs(p)).Data));
        Assert.Same(Declared(root, "Lib", "a"), q.Get(StaticQueryKey.Binding(p, "a", StaticCycleCheck.Formation)).Property);

        // One certificate per written position may settle separately. Subscribing a single range to all of them
        // ran its busiest equation 18/66 times and visited 1,809/15,411 tree nodes at widths 32/128.
        var counts = observations.StaticQueryEvaluations
            .Where(entry => entry.Key.Projection == StaticQueryProjection.OpenPresenceWitnesses && entry.Key.Name == "a");
        Assert.NotEmpty(counts);
        Assert.All(counts, entry => Assert.InRange(entry.Value, 1, 6));
        Assert.InRange(observations.StaticSettledWitnessNodeVisits, 1, 48L * repeats);
    }

    [Fact]
    public void ALowerWitness_UsesTheProviderRangeInItsOwnStratum()
    {
        var root = SourceProvenance.ParseSyntaxValidRoot("L = { public a = 1 }\nM = { public b = 1 }\nP = { open L, M\n 0 }\n0\n");
        var observations = new FrontEndTraversalObservations();
        var q = new StaticStructureQueries(root, new(100_000, 4, 50_000, 1_000_000)) { Observations = observations };
        var p = q.BodyIn(q.Root, root.Properties.Single(property => property.Name == "P").Value);
        var witness = q.Get(StaticQueryKey.Project(StaticQueryKind.Binding, p, StaticQueryProjection.OpenPresenceWitnesses,
            "a", StaticCycleCheck.Lower, length: 2));
        var match = Assert.IsType<StaticOpenMatch>(witness.Data);
        Assert.True(match.Pending);
        Assert.NotNull(match.Provider);
        var ranges = observations.StaticQueryEvaluations.Keys.Where(key => key.Scope == p && key.Projection == StaticQueryProjection.ProviderRange);
        Assert.NotEmpty(ranges);
        Assert.All(ranges, key => Assert.Equal(StaticCycleCheck.Lower, key.Stratum));
    }

    // ── Levels waiting on observers ───────────────────────────────────────────────────────────

    /// <summary>
    /// VERDICT. Use's index waits on an open receiver-expansion verdict, another decision observer. The deferred presences
    /// of Use's names used to run first, FIFO, and build every witness range over the still-unsettled target; now they
    /// yield to the verdict, the index settles and answers every name. (Before: 4,128 witness ranges at K = 64, N = 32.)
    /// </summary>
    [Theory]
    [InlineData(8)]
    [InlineData(64)]
    public void AVerdictTarget_SettlesTheIndexBeforeTheNamesAskForWitnesses(int targets)
    {
        const int names = 32;
        var (observations, program, _) = Detect(VerdictTarget(targets, names));
        Assert.Empty(program.Diagnostics);
        Assert.Empty(Witnesses(observations));
        Assert.Equal(0, observations.StaticQueryEvaluations.Keys.Count(key => key.Projection == StaticQueryProjection.PreservedOpenPresence));
        var use = Body(program, "Use");
        var deferred = observations.StaticQueryEvaluations.Where(entry => entry.Key.Projection == StaticQueryProjection.DeferredOpenPresence).ToList();
        Assert.Equal(names, deferred.Count);
        Assert.All(deferred, entry => Assert.Same(use, entry.Key.Scope));
        // Each presence runs once, after the index has settled.
        Assert.All(deferred, entry => Assert.Equal(1, entry.Value));
        Assert.Contains(observations.StaticQueryEvaluations.Keys, key => key.Projection == StaticQueryProjection.OpenReceiverExpansionVerdict);
    }

    /// <summary>
    /// CERTIFICATE. Use's index waits on G's emptiness certificate, a closure observer that runs after every decision
    /// observer, so Use's names still read their witnesses (moving the presences below the certificates is a separate
    /// settlement-policy decision); each tree now splits only towards the one unsettled target.
    /// </summary>
    [Theory]
    [InlineData(8)]
    [InlineData(64)]
    public void ACertificateTarget_StillReadsWitnesses_OnlyTowardsTheUnsettledTarget(int targets)
    {
        const int names = 32;
        var source = CertificateTarget(targets, names);
        var (observations, program, _) = Detect(source);
        Assert.Empty(program.Diagnostics);
        // Open validation, after detection, refuses the target.
        Assert.Equal([DiagnosticCode.UnresolvedOpenTarget], Parser.Parse(source).Diagnostics.Select(diagnostic => diagnostic.Code).ToArray());
        var witnesses = Witnesses(observations);
        var use = Body(program, "Use");
        Assert.All(witnesses, key => Assert.Same(use, key.Scope));
        var trees = witnesses.Select(key => (key.Name, key.Stratum)).Distinct().Count();
        Assert.Equal(names, trees);
        Assert.Equal(trees * (2 * Log2Ceiling(targets + 1) + 1), witnesses.Count);
    }

    // ── Agreement with the generic paths ──────────────────────────────────────────────────────

    public static TheoryData<string> AgreementShapes => new()
    {
        "self-last", "self-first", "self-middle", "self-members", "self-ambiguous", "self-repeated", "self-absent",
        "verdict", "certificate",
    };

    /// <summary>The names the waiting level's row writes.</summary>
    private static IEnumerable<string> AgreementNames(string shape)
        => shape.StartsWith("self", StringComparison.Ordinal)
            ? Names(12).Prepend("q").Concat(shape == "self-members" ? ["b", "x0"] : [])
            : Names(12);

    private static string AgreementSource(string shape) => shape switch
    {
        "self-last" => SelfDependent(9, 12),
        "self-first" => SelfDependent(9, 12, "first"),
        "self-middle" => SelfDependent(9, 12, "middle"),
        "self-members" => SelfDependent(9, 12, "middle", members: ["a0", "b"], extra: "b + x0"),
        // q from two libraries: P's q is ambiguous, still no input.
        "self-ambiguous" => SelfDependent(9, 12, libraries: i => (i is 0 or 5 ? ["q"] : Array.Empty<string>()).Concat(Own(i, 9, 12))),
        // A library written again after the unsettled provider: its presence is certified past R.
        "self-repeated" => SelfDependent(9, 12, "middle").Replace("    open L0, ", "    open L3, L0, ", StringComparison.Ordinal)
            .Replace(", L8\n", ", L8, L3, L1\n", StringComparison.Ordinal),
        // Names no settled library offers: absent from every settled range, decided only by R.
        "self-absent" => SelfDependent(9, 12, libraries: i => i == 0 ? ["q"] : []),
        "verdict" => VerdictTarget(9, 12),
        "certificate" => CertificateTarget(9, 12),
        _ => throw new ArgumentOutOfRangeException(nameof(shape)),
    };

    /// <summary>
    /// The reuse of settled targets and the presences' late scheduling, each on or off, reach the same facts for every
    /// written name of the waiting level — its input verdict, binding and opened match — and the same inputs: on the
    /// shapes above (the unsettled provider first, in the middle and last, a late provider with members of its own, an
    /// ambiguous <c>q</c>, a library repeated after the unsettled provider, names no library offers, a verdict and a
    /// certificate target). Declarations and providers are compared by identity across the two models.
    /// </summary>
    [Theory]
    [MemberData(nameof(AgreementShapes))]
    public void SettledTargetReuseAndLatePresences_AgreeWithTheGenericPaths(string shape)
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(AgreementSource(shape));
        var ids = new Dictionary<object, int>(ReferenceEqualityComparer.Instance);
        string Id(object? value) => value is null ? "-" : (ids.TryGetValue(value, out var id) ? id : ids[value] = ids.Count).ToString(System.Globalization.CultureInfo.InvariantCulture);
        string Describe(StaticFact fact) => fact.Data switch
        {
            StaticOpenMatch match => $"{fact.Kind}:{Id(match.Provider?.Declaration)}:{match.Pending}",
            string[] inputs => $"{fact.Kind}:[{string.Join(',', inputs)}]",
            _ => $"{fact.Kind}:{Id(fact.Scope?.Declaration)}:{Id(fact.Property)}",
        };
        (List<string> Facts, int Witnesses, long Settled) Solve(bool reuse, bool late)
        {
            var q = new StaticStructureQueries(root, new(1_000_000, 4, 100_000, 4_000_000))
            {
                SettledOpenTargetReuseForTesting = reuse,
                LateDeferredPresenceForTesting = late,
                Observations = new FrontEndTraversalObservations(),
            };
            var level = q.BodyIn(q.Root, root.Properties.Single(property => property.Name is "P" or "Use").Value);
            var facts = new List<string> { Describe(q.Get(StaticQueryKey.Inputs(level))) };
            foreach (var name in AgreementNames(shape))
            {
                facts.Add($"{name} input {Describe(q.Get(StaticQueryKey.IsInput(level, name)))}");
                facts.Add($"{name} binding {Describe(q.Get(StaticQueryKey.Binding(level, name, StaticCycleCheck.Formation)))}");
                facts.Add($"{name} opened {Describe(q.Get(StaticQueryKey.Project(StaticQueryKind.Binding, level, StaticQueryProjection.OpenMatches,
                    name, StaticCycleCheck.Formation, length: q.BodyOf(level).Opens.Count)))}");
            }
            return (facts, Witnesses(q.Observations).Count, q.Observations.StaticSettledWitnessRanges);
        }

        var generic = Solve(reuse: false, late: false);
        Assert.Equal(0, generic.Settled);
        foreach (var (reuse, late) in new[] { (true, true), (true, false), (false, true) })
        {
            var candidate = Solve(reuse, late);
            Assert.Equal(generic.Facts, candidate.Facts);
            Assert.True(candidate.Witnesses <= generic.Witnesses, $"{shape} reuse={reuse} late={late}: {candidate.Witnesses} > {generic.Witnesses}");
        }
        var both = Solve(reuse: true, late: true);
        if (shape.StartsWith("self", StringComparison.Ordinal) || shape == "certificate")
        {
            Assert.True(both.Settled > 0, shape);
            Assert.True(both.Witnesses < generic.Witnesses, shape);
        }
        else
            Assert.Equal(0, both.Witnesses);
    }

    /// <summary>
    /// An earlier view of the SAME provider that lacks a name hides it, so a settled range whose provider offers the name
    /// still waits for that provider's preserved-presence certificate, which never holds here. Host-built: <c>Lib2</c> is a
    /// <c>with</c> copy of <c>Lib1</c>'s body (one declaration identity, ONE provider) without <c>a</c>, written first, so
    /// the level's one provider is that view: <c>a</c> is absent and P's input, and <c>c</c> is visible only if the
    /// first view makes it public. Both
    /// paths agree. Counting the later view's <c>a</c> as present, in the settled range or in the certificate's read of
    /// the settled earlier target, would refine the name's presence to a match and then to absence, which is no
    /// refinement.
    /// </summary>
    [Theory]
    [InlineData("public c = 2", true)]
    [InlineData("c = 2", false)]
    [InlineData("0", false)]
    public void AnEarlierViewOfTheSameProvider_StillHidesAName_AtAWaitingLevel(string firstView, bool publicC)
    {
        var parsed = (Algorithm.User)SourceProvenance.ParseSyntaxValidRoot(
            "L0 = {\n    public q = 0\n}\nLib1 = {\n    public a = 1\n    public c = 1\n}\n"
            + $"Lib2 = {{\n    {firstView}\n}}\nL1 = {{\n    public z1 = 1\n}}\n"
            + "L = {\n    public q = P.R\n}\n"
            + "P = {\n    open Lib2, Lib1, L0, L1, R\n    public R = C\n    C = { open L\n    q }\n    q + a + c\n}\n0\n");
        var lib1 = (Algorithm.User)parsed.Properties.Single(property => property.Name == "Lib1").Value;
        var lib2 = parsed.Properties.Single(property => property.Name == "Lib2");
        var view = lib1 with { Properties = lib2.Value.Properties };
        Assert.Same(lib1.Declaration, view.Declaration);
        var root = parsed with { Properties = [.. parsed.Properties.Select(property => property.Name == "Lib2" ? property with { Value = view } : property)] };
        foreach (var reuse in new[] { false, true })
        {
            var q = new StaticStructureQueries(root, new(1_000_000, 4, 100_000, 4_000_000))
            {
                SettledOpenTargetReuseForTesting = reuse,
                Observations = new FrontEndTraversalObservations(),
            };
            var p = q.BodyIn(q.Root, root.Properties.Single(property => property.Name == "P").Value);
            string[] expectedInputs = publicC ? ["a"] : ["a", "c"];
            Assert.Equal(expectedInputs, Assert.IsType<string[]>(q.Get(StaticQueryKey.Inputs(p)).Data));
            Assert.Equal(StaticFactKind.Parameter, q.Get(StaticQueryKey.Binding(p, "a", StaticCycleCheck.Formation)).Kind);
            var c = q.Get(StaticQueryKey.Binding(p, "c", StaticCycleCheck.Formation));
            Assert.Equal(publicC ? StaticFactKind.Declaration : StaticFactKind.Parameter, c.Kind);
            if (publicC) Assert.Same(lib2.Value.Properties.Single(), c.Property);
            Assert.NotEmpty(Witnesses(q.Observations));
            Assert.Equal(reuse, q.Observations.StaticSettledWitnessRanges > 0);
        }
    }

    [Fact]
    public void AStillUndecidedEarlierTarget_CanHideALaterViewWithAnEmptyNamespace()
    {
        // R's open structure depends on q's presence. R eventually points at C, a first view of Later's
        // declaration with no public members. Certifying Later.a while R is undecided would contradict Q2.
        var syntax = (Algorithm.User)SourceProvenance.ParseSyntaxValidRoot(
            "L0 = { public q = 0 }\nL = { public q = 5 }\nP = { open R, Later, L0\n public R = C\n"
            + " C = { open L\n q }\n Later = { public a = 1 }\n q + a }\n0");
        var property = syntax.Properties.Single(p => p.Name == "P");
        var body = (Algorithm.User)property.Value;
        var first = (Algorithm.User)body.Properties.Single(p => p.Name == "C").Value;
        var properties = body.Properties.Select(p => p.Name == "Later" ? p with { Value = first with { Properties = p.Value.Properties } } : p);
        var replacement = property with { Value = body with { Properties = [.. properties] } };
        var root = syntax with { Properties = [.. syntax.Properties.Select(p => ReferenceEquals(p, property) ? replacement : p)] };
        foreach (var reuse in new[] { false, true })
        {
            var q = new StaticStructureQueries(root, new(1_000_000, 4, 100_000, 4_000_000)) { SettledOpenTargetReuseForTesting = reuse };
            var level = q.BodyIn(q.Root, replacement.Value);
            Assert.Equal(["a"], Assert.IsType<string[]>(q.Get(StaticQueryKey.Inputs(level)).Data));
            Assert.Equal(StaticFactKind.Parameter, q.Get(StaticQueryKey.Binding(level, "a", StaticCycleCheck.Formation)).Kind);
        }
    }

    // ── Cancellation and the ledger ───────────────────────────────────────────────────────────

    /// <summary>A settled range's one-pass walk observes cancellation at every range node and faults the operation.</summary>
    [Fact]
    public void ASettledRangeWalk_ObservesCancellation()
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(SelfDependent(32, 8));
        using var cancellation = new CancellationTokenSource();
        var q = new StaticStructureQueries(root, new(1_000_000, 4, 100_000, 4_000_000), cancellationToken: cancellation.Token);
        var visits = 0;
        q.SettledRangeVisitForTesting = () => { if (++visits == 5) cancellation.Cancel(); };
        var p = q.BodyIn(q.Root, root.Properties.Single(property => property.Name == "P").Value);
        var error = Assert.ThrowsAny<OperationCanceledException>(() => q.Get(StaticQueryKey.Inputs(p)));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(5, visits);
        Assert.True(q.Resources.IsFailed);
        Assert.Throws<InvalidOperationException>(() => q.Get(StaticQueryKey.Inputs(p)));
    }

    /// <summary>Every visited range node is charged to the operation's work bound; a bound reached inside the walk refuses the operation.</summary>
    [Fact]
    public void ASettledRangeWalk_ChargesTheWorkBound()
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(SelfDependent(32, 8));
        var q = new StaticStructureQueries(root, new(1_000_000, 4, 100_000, 4_000_000));
        long? first = null;
        q.SettledRangeVisitForTesting = () => first ??= q.Resources.WorkCharged;
        var p = q.BodyIn(q.Root, root.Properties.Single(property => property.Name == "P").Value);
        q.Get(StaticQueryKey.Inputs(p));
        Assert.NotNull(first);

        // The same operation with its work bound at the first visit: the walk's own charge refuses it.
        var tight = new StaticStructureQueries(root, new(first!.Value, 4, 100_000, 4_000_000));
        var walked = false;
        tight.SettledRangeVisitForTesting = () => walked = true;
        var bounded = tight.BodyIn(tight.Root, root.Properties.Single(property => property.Name == "P").Value);
        var refusal = Assert.Throws<StaticQueryLimitExceededException>(() => tight.Get(StaticQueryKey.Inputs(bounded)));
        Assert.Equal(StaticQueryBoundKind.Work, refusal.Bound);
        Assert.True(walked);
        Assert.True(tight.Resources.IsFailed);
    }
}
