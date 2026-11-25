using System.Text;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Front-end work for names written under wide <c>open</c> levels (November 2026). A name's opened binding is
/// answered from its level's closed member index once that index settles; until then the name waits on its
/// deferred presence (<see cref="StaticQueryProjection.DeferredOpenPresence"/>, a decision observer), so only a
/// level whose index is still unknown once ordinary work is quiescent builds per-name presence witnesses. Each
/// level's providers are built once per operation and stratum and retained for every question the lookup
/// adapters ask (<c>StaticStructureOperation.Providers</c>), and a level of more than eight providers whose
/// index is final answers an absent or single name from it (<c>StaticStructureOperation.SelectOpenLevel</c>).
/// Every program here keeps its selections, diagnostics, provider order and wording.
/// </summary>
public sealed class OpenLevelPresenceReuseTests
{
    private static string Opens(int targets) => string.Join(", ", Enumerable.Range(0, targets).Select(i => $"L{i}"));

    private static string Sum(IEnumerable<string> names) => string.Join(" + ", names);

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

    /// <summary>The written programs of the measured shapes: K open targets and N written names in one body <c>Use</c>.</summary>
    private static string Shape(string shape, int targets, int names)
    {
        IEnumerable<string> Opened(int i) => Enumerable.Range(0, names).Where(j => j % targets == i).Select(j => $"a{j}");
        var a = Enumerable.Range(0, names).Select(j => $"a{j}");
        var x = Enumerable.Range(0, names).Select(j => $"x{j}");
        return shape switch
        {
            // Inferred parameters: every name misses every provider.
            "free" => Libraries(targets, i => [$"m{i}"]) + $"Use = {{\n    open {Opens(targets)}\n    {Sum(x)}\n}}\n1\n",
            // Each name offered by exactly one provider.
            "opened" => Libraries(targets, Opened) + $"Use = {{\n    open {Opens(targets)}\n    {Sum(a)}\n}}\nUse\n",
            // Eligible Grace on inferred parameters.
            "graced-free" => Libraries(targets, i => [$"m{i}"]) + $"Use = {{\n    open {Opens(targets)}\n    {Sum(x.Select(n => "~" + n))}\n}}\n1\n",
            // Grace on opened names: every marker is ineligible (InvalidGraceMarker).
            "graced-opened" => Libraries(targets, Opened) + $"Use = {{\n    open {Opens(targets)}\n    {Sum(a.Select(n => "~" + n))}\n}}\nUse\n",
            // Each name offered by two providers (AmbiguousOpen).
            "ambiguous" => Libraries(targets, i => Enumerable.Range(0, names).Where(j => j % targets == i || (j + 1) % targets == i).Select(j => $"a{j}"))
                + $"Use = {{\n    open {Opens(targets)}\n    {Sum(a)}\n}}\nUse\n",
            // One library opened K times: ONE provider.
            "repeated" => Libraries(1, _ => a) + $"Use = {{\n    open {string.Join(", ", Enumerable.Repeat("L0", targets))}\n    {Sum(a)}\n}}\nUse\n",
            // Names read one level below the open level.
            "nested" => Libraries(targets, Opened) + $"Use = {{\n    open {Opens(targets)}\n    W = {{\n        {Sum(a)}\n    }}\n    W\n}}\nUse\n",
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
    }

    private static (FrontEndTraversalObservations Observations, DetectedProgram Program) Detect(string source)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var observations = new FrontEndTraversalObservations();
        var program = ParameterDetector.DetectPrevalidated(syntax, observations: observations);
        return (observations, program);
    }

    private static int Keys(FrontEndTraversalObservations observations, StaticQueryProjection projection)
        => observations.StaticQueryEvaluations.Keys.Count(key => key.Projection == projection);

    /// <summary>The first single-quoted name of a diagnostic message, quotes included.</summary>
    private static string FirstQuotedName(string message)
    {
        var start = message.IndexOf('\'', StringComparison.Ordinal);
        return message[start..(message.IndexOf('\'', start + 1) + 1)];
    }

    // ── No witness ranges while the level index settles ───────────────────────────────────────

    /// <summary>
    /// Every name a body writes asks Q1 for its opened binding at each level with opens. A name used to read the
    /// level's closed index first and, finding it still settling, build its own presence witnesses: a binary range
    /// tree of 2K − 1 queries over the K targets, one tree per name, though the one index settled a few rounds later.
    /// Now no name builds a witness range at a level whose providers settle: each waits on one deferred presence,
    /// which the settled index answers. Small lists (one or two targets) and wide ones alike; inferred and opened
    /// names, Grace markers, a repeated target and names read below the open level alike.
    /// </summary>
    [Theory]
    [InlineData("free", 1)]
    [InlineData("free", 2)]
    [InlineData("free", 9)]
    [InlineData("free", 64)]
    [InlineData("opened", 1)]
    [InlineData("opened", 8)]
    [InlineData("opened", 9)]
    [InlineData("opened", 64)]
    [InlineData("graced-free", 2)]
    [InlineData("graced-free", 64)]
    [InlineData("graced-opened", 2)]
    [InlineData("graced-opened", 64)]
    [InlineData("ambiguous", 2)]
    [InlineData("ambiguous", 64)]
    [InlineData("repeated", 2)]
    [InlineData("repeated", 64)]
    [InlineData("nested", 9)]
    [InlineData("nested", 64)]
    public void ASettlingLevel_BuildsNoWitnessRanges(string shape, int targets)
    {
        const int names = 32;
        var (observations, program) = Detect(Shape(shape, targets, names));
        var code = shape switch
        {
            "graced-opened" => DiagnosticCode.InvalidGraceMarker,
            "ambiguous" => DiagnosticCode.AmbiguousOpen,
            _ => (DiagnosticCode?)null,
        };
        // One diagnostic per written name where the shape has one, in the names' written order.
        var expected = code is { } reported ? Enumerable.Repeat(reported, names).ToArray() : [];
        Assert.Equal(expected, program.Diagnostics.Select(diagnostic => diagnostic.Code).ToArray());
        Assert.Equal(code is null ? [] : Enumerable.Range(0, names).Select(j => $"'a{j}'").ToArray(),
            program.Diagnostics.Select(diagnostic => FirstQuotedName(diagnostic.Message)).ToArray());
        Assert.Equal(0, Keys(observations, StaticQueryProjection.OpenPresenceWitnesses));
        Assert.Equal(0, Keys(observations, StaticQueryProjection.PreservedOpenPresence));
        Assert.InRange(Keys(observations, StaticQueryProjection.DeferredOpenPresence), 1, names);
        Assert.Equal(1, observations.StaticOpenIndexBuilds);
    }

    /// <summary>
    /// The total structural work of detection grows with the written names plus the targets, not with their product.
    /// At K = 64 and N = 64 detection made 21,000 evaluations and 10,000 entries, 8,000 of them witness ranges.
    /// </summary>
    [Theory]
    [InlineData("free")]
    [InlineData("opened")]
    [InlineData("graced-free")]
    public void DetectionWork_IsLinearInNamesAndTargets(string shape)
    {
        StaticQueryStatistics Work(int targets, int names)
        {
            var (_, program) = Detect(Shape(shape, targets, names));
            Assert.Empty(program.Diagnostics);
            return program.Operation!.Queries.Statistics;
        }

        var baseline = Work(16, 64);
        var wider = Work(64, 64);
        var longer = Work(16, 256);
        // Four times the targets add work per target; four times the names add work per name. The product would
        // multiply both (the witnesses: 2K − 1 entries per name).
        Assert.True(wider.Entries - baseline.Entries <= 48 * 24, $"targets: {baseline.Entries} -> {wider.Entries} entries");
        Assert.True(longer.Entries - baseline.Entries <= 192 * 24, $"names: {baseline.Entries} -> {longer.Entries} entries");
        Assert.True(wider.Evaluations - baseline.Evaluations <= 48 * 48, $"targets: {baseline.Evaluations} -> {wider.Evaluations} evaluations");
        Assert.True(longer.Evaluations - baseline.Evaluations <= 192 * 48, $"names: {baseline.Evaluations} -> {longer.Evaluations} evaluations");
    }

    /// <summary>
    /// A target repeated K times is one provider, but each name's witnesses asked, for every repeated position, whether
    /// an earlier view of the same provider hides the name (a certificate over every earlier position): O(N·K²)
    /// certificate work, which exhausted the program-scaled work bound. <c>open L0</c> written 48 times with 64 names
    /// was refused as <see cref="DiagnosticCode.StaticStructureLimitExceeded"/>; it is an ordinary program with one
    /// provider, and every route, the editor included, reads it so.
    /// </summary>
    [Fact]
    public async Task ARepeatedTarget_IsOneProvider_WithinTheStaticBudget()
    {
        const int targets = 64;
        const int names = 64;
        static string Repeated(int names)
            => "L0 = {\n" + string.Concat(Enumerable.Range(0, names).Select(j => $"    public a{j} = {j}\n")) + "}\n"
                + $"Use = {{\n    open {string.Join(", ", Enumerable.Repeat("L0", targets))}\n    {Sum(Enumerable.Range(0, names).Select(j => $"a{j}"))}\n}}\nUse\n";
        var members = Enumerable.Range(0, names).Select(j => $"a{j}").ToArray();
        var source = Repeated(names);

        var (observations, program) = Detect(source);
        Assert.Empty(program.Diagnostics);
        Assert.Equal(0, Keys(observations, StaticQueryProjection.PreservedOpenPresence));
        // What certificate work remains belongs to the written targets, not to the names read through them.
        var (_, single) = Detect(Repeated(1));
        Assert.Empty(single.Diagnostics);
        var work = program.Operation!.Queries.Statistics.AuxiliaryWork;
        Assert.Equal(single.Operation!.Queries.Statistics.AuxiliaryWork, work);
        Assert.True(work <= 64 * targets, $"certificate work {work}");

        var parsed = SourceProvenance.ParseValid(source).Parsed;
        var model = SemanticModelBuilder.Build(parsed);
        foreach (var member in members)
        {
            var reference = Assert.Single(model.FindResolutions(member), resolution => resolution.Occurrence.Kind == OccurrenceKind.ResolveReference);
            Assert.Equal(IdentifierClassification.PropertyReference, reference.Classification);
            Assert.Equal(2 + Array.IndexOf(members, member), reference.ResolvedDeclaration!.Span.Start.Line);
        }

        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal((names * (names - 1) / 2).ToString(System.Globalization.CultureInfo.InvariantCulture), outcome.Value);
    }

    /// <summary>
    /// A level whose provider waits on a name of that level (<c>R = C</c>, whose body reads <c>q</c>, which is P's
    /// input unless an open provides it) has no settled index until some name's presence is known, so its names
    /// still read their witnesses, which decide known presence before the provider list settles: <c>q</c> is no input,
    /// and the provider settles. A settled level beside it builds no witness range for its own names.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ABlockedLevel_StillDecidesKnownPresence_WhileASettledLevelBuildsNoWitnesses(bool ambiguous)
    {
        const int targets = 12;
        var library = Libraries(targets, i => i == 0 || ambiguous && i == 1 ? ["q", $"a{i}"] : [$"a{i}"]);
        var source = library
            + "L = { public q = P.R }\n"
            + $"P = {{\n    open {Opens(targets)}, R\n    public R = C\n    C = {{ open L\n    q }}\n    q + {Sum(Enumerable.Range(0, targets).Select(i => $"a{i}"))}\n}}\n"
            + $"Use = {{\n    open {Opens(targets)}\n    {Sum(Enumerable.Range(0, targets).Select(i => $"a{i}"))}\n}}\n"
            + "0\n";
        var (observations, program) = Detect(source);
        var operation = program.Operation!;
        var p = operation.ContextOf(operation.Root, program.Root.Properties.Single(property => property.Name == "P").Value);
        var use = operation.ContextOf(operation.Root, program.Root.Properties.Single(property => property.Name == "Use").Value);

        if (ambiguous)
        {
            var diagnostic = Assert.Single(program.Diagnostics);
            Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code);
            Assert.StartsWith("'q' is ambiguous: 2 different opened algorithms provide it at the same open level (L0, L1)", diagnostic.Message, StringComparison.Ordinal);
        }
        else
            Assert.Empty(program.Diagnostics);
        Assert.Equal(StaticFactKind.No, operation.Read(StaticQueryKey.IsInput(p, "q")).Kind);
        Assert.Empty(Assert.IsType<string[]>(operation.Read(StaticQueryKey.Inputs(p)).Data));
        var witnesses = observations.StaticQueryEvaluations.Keys.Where(key => key.Projection == StaticQueryProjection.OpenPresenceWitnesses).ToList();
        Assert.NotEmpty(witnesses);
        Assert.All(witnesses, key => Assert.Same(p, key.Scope));
        Assert.DoesNotContain(observations.StaticQueryEvaluations.Keys, key => ReferenceEquals(key.Scope, use)
            && key.Projection is StaticQueryProjection.OpenPresenceWitnesses or StaticQueryProjection.PreservedOpenPresence);
    }

    // ── Retained providers ────────────────────────────────────────────────────────────────────

    /// <summary>
    /// The Q-29 ambiguity check, a Grace marker's reason and a structural member provider each ask the levels a name
    /// reaches for their providers. Each question rebuilt the level's list — a provider, its identity and its
    /// declaring chain per provider — and charged four ledger slots per provider again, so every name written below a
    /// K-provider level added O(K) ledger units (153,944 units at K = 128, N = 256). The list is built once per level
    /// and stratum, so what a written name adds to the ledger no longer depends on how many providers its level has:
    /// 128 more names add the same units beside 2 providers and beside 64 (before: 9,600 and 41,344).
    /// </summary>
    [Fact]
    public void ALevelsProviders_AreBuiltOnce_HoweverManyNamesAskForThem()
    {
        var added = new Dictionary<int, long>();
        foreach (var targets in new[] { 2, 64 })
        {
            var (fewer, fewerProgram) = Detect(Shape("opened", targets, 64));
            var (more, moreProgram) = Detect(Shape("opened", targets, 192));
            Assert.Empty(fewerProgram.Diagnostics);
            Assert.Empty(moreProgram.Diagnostics);
            Assert.Equal(fewer.StaticLevelProviderBuilds, more.StaticLevelProviderBuilds);
            Assert.InRange(more.StaticLevelProviderBuilds, 1, 3); // one per OD-D stratum asked
            Assert.Equal(targets * more.StaticLevelProviderBuilds, more.StaticLevelProviderEntries);
            added[targets] = moreProgram.Operation!.Queries.Statistics.MetadataUnits - fewerProgram.Operation!.Queries.Statistics.MetadataUnits;
        }
        Assert.True(added[64] - added[2] <= 128 * 4, $"128 more names added {added[2]} ledger units beside 2 providers, {added[64]} beside 64");
    }

    /// <summary>
    /// A retained list is served while its providers' declaring levels are the ones registered for their contexts.
    /// A level registered over the one a provider was declared at (detection registers its own level for a context
    /// another read may have built first) makes the next read rebuild the list at the new level, as every read used
    /// to; a replacement elsewhere keeps the list.
    /// </summary>
    [Fact]
    public void AReplacedDeclaringLevel_RebuildsTheRetainedProviders()
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot("Lib = {\n    public X = 1\n}\nUse = {\n    open Lib\n    X\n}\nUse\n");
        var operation = StaticStructureAdmission.Create(syntax).Operation;
        var lib = syntax.Properties.Single(property => property.Name == "Lib").Value;
        var use = operation.ContextOf(operation.Root, syntax.Properties.Single(property => property.Name == "Use").Value);
        var first = operation.Providers(use, StaticCycleCheck.Formation);
        var provider = Assert.Single(first);
        Assert.Same(lib, provider.Target);
        Assert.Same(first, operation.Providers(use, StaticCycleCheck.Formation));

        // Another context's level, registered and then replaced: the list stays.
        var libKey = operation.ContextOf(operation.Root, lib);
        foreach (var _ in new[] { 0, 1 })
        {
            operation.RegisterLevel(ElaboratedScopeLookup.CreateScope(lib, operation.LookupLevel(operation.Root),
                staticContext: operation.Context(libKey)));
            Assert.Same(first, operation.Providers(use, StaticCycleCheck.Formation));
        }

        // The declaring level itself: the list is rebuilt there, with the same provider identity and provenance.
        var root = ElaboratedScopeLookup.CreateScope(syntax, operation.LookupLevel(operation.Queries.Keys.Root),
            staticContext: operation.Context(operation.Root));
        operation.RegisterLevel(root);
        var rebuilt = operation.Providers(use, StaticCycleCheck.Formation);
        Assert.NotSame(first, rebuilt);
        var again = Assert.Single(rebuilt);
        Assert.Same(root, again.Level);
        Assert.Same(lib, again.Target);
        Assert.Equal(provider.Identity, again.Identity);
        Assert.Same(provider.Written, again.Written);
        Assert.Same(rebuilt, operation.Providers(use, StaticCycleCheck.Formation));
    }

    /// <summary>A retained list never outlives its operation's cancellation: every read checks the token first.</summary>
    [Fact]
    public void RetainedProviders_ObserveCancellation()
    {
        var source = Shape("opened", 12, 24);
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        using var cancellation = new CancellationTokenSource();
        var operation = StaticStructureAdmission.Create(syntax, cancellationToken: cancellation.Token).Operation;
        var program = ParameterDetector.DetectPrevalidated(syntax, structuralOperation: operation);
        Assert.Empty(program.Diagnostics);
        var use = operation.ContextOf(operation.Root, syntax.Properties.Single(property => property.Name == "Use").Value);
        var level = operation.LookupLevel(use);
        Assert.Equal(12, operation.Providers(use, StaticCycleCheck.Formation).Count);
        Assert.Equal(1, ElaboratedScopeLookup.SelectOpenLevel(level, "a5").Count);

        cancellation.Cancel();
        Assert.Throws<OperationCanceledException>(() => operation.Providers(use, StaticCycleCheck.Formation));
        Assert.Throws<OperationCanceledException>(() => ElaboratedScopeLookup.SelectOpenLevel(level, "a5"));
        Assert.Throws<OperationCanceledException>(() => ElaboratedScopeLookup.FindAmbiguousOpenProviders(level, "a5"));
    }

    // ── Wide-level selection against the ordered scan ──────────────────────────────────────────

    [Theory]
    [InlineData(8)]
    [InlineData(9)]
    public void UniqueHits_UseThePublicDeclarationAlreadyIndexedAtAWideLevel(int targets)
    {
        const int names = 32;
        var (observations, program) = Detect(Shape("opened", targets, names));
        Assert.Empty(program.Diagnostics);
        Assert.Equal(targets == 8 ? 0 : names, observations.StaticSettledOpenSelections);
        Assert.Equal(targets == 8 ? targets : 0, observations.LookupOpenMemberIndexBuilds);
    }

    [Fact]
    public void AProviderPositionTableThatExceedsTheBudget_PropagatesTheFailure()
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(Shape("opened", 9, 9));
        var limits = StaticQueryLimits.Default with { MaxStorageUnits = 100_000 };
        var operation = new StaticStructureOperation(syntax, limits);
        var use = operation.ContextOf(operation.Root, syntax.Properties.Single(p => p.Name == "Use").Value);
        operation.Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, use, StaticQueryProjection.OpenMemberIndex));
        var level = operation.LookupLevel(use);
        Assert.Equal(9, level.GetResolvedOpenProviders().Count);
        Assert.Equal(0, ElaboratedScopeLookup.SelectOpenLevel(level, "absent").Count);

        // The provider list and closed index already exist. Only the positions of the selected providers need storage.
        var budget = operation.Queries.Resources;
        budget.Reserve(limits.MaxStorageUnits - budget.StorageUnits);
        Assert.Throws<StaticQueryLimitExceededException>(() => ElaboratedScopeLookup.SelectOpenLevel(level, "a5"));
        Assert.True(budget.IsFailed);
        Assert.Throws<InvalidOperationException>(() => ElaboratedScopeLookup.SelectOpenLevel(level, "absent"));
    }

    [Fact]
    public void AFrozenIndex_AnswersInTheNewUnit_WithoutImportingAQuery()
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(Shape("opened", 9, 9));
        using var eagerCancellation = new CancellationTokenSource();
        var eager = new StaticStructureQueries(syntax, StaticQueryLimits.Default, cancellationToken: eagerCancellation.Token);
        var use = eager.BodyIn(eager.Root, syntax.Properties.Single(p => p.Name == "Use").Value);
        var lib = syntax.Properties.Single(p => p.Name == "L5").Value;
        var provider = eager.BodyIn(eager.Root, lib);
        var index = StaticQueryKey.Project(StaticQueryKind.OpenProviders, use, StaticQueryProjection.OpenMemberIndex);
        eager.Get(index);
        using var forkCancellation = new CancellationTokenSource();
        var fork = new StaticStructureQueries(eager.Freeze(), StaticQueryLimits.Default, forkCancellation.Token);
        eagerCancellation.Cancel();

        Assert.True(fork.TrySettledOpenMember(use, StaticCycleCheck.Formation, "a5", out var match));
        Assert.True(match.HasValue);
        Assert.Same(provider, match.Value.Provider);
        Assert.Same(lib, match.Value.Hit.Owner);
        Assert.Same(Assert.Single(lib.Properties), match.Value.Hit.Property);
        Assert.True(fork.TrySettledOpenMember(use, StaticCycleCheck.Formation, "absent", out var absent));
        Assert.Null(absent);
        Assert.False(fork.TrySettledOpenMember(use, StaticCycleCheck.None, "a5", out _));
        Assert.Equal(0, fork.Statistics.Entries);

        forkCancellation.Cancel();
        var failure = Assert.Throws<OperationCanceledException>(() => fork.TrySettledOpenMember(use, StaticCycleCheck.Formation, "a5", out _));
        Assert.Equal(forkCancellation.Token, failure.CancellationToken);
    }

    /// <summary>
    /// The adapters' first-deciding-level selection, read from scratch by scanning every provider of every level in
    /// order (the selection before the settled index answered wide levels).
    /// </summary>
    private static OpenNameSelection ScanFirstOpenLevel(ElaboratedPropertyScope scope, string name)
    {
        for (var current = scope; current is not null; current = current.Parent)
        {
            var selection = ElaboratedScopeLookup.ScanOpenLevel(current, current.GetResolvedOpenProviders(), name);
            if (selection.Count > 0) return selection;
        }
        return default;
    }

    private static void AssertSameSelection(OpenNameSelection expected, OpenNameSelection actual, string name)
    {
        Assert.True(expected.Count == actual.Count, $"'{name}': {expected.Count} matches scanned, {actual.Count} selected");
        Assert.Same(expected.Level, actual.Level);
        for (var index = 0; index < expected.Count; index++)
        {
            Assert.Same(expected[index].Provider, actual[index].Provider);
            Assert.Same(expected[index].Hit.Owner, actual[index].Hit.Owner);
            Assert.Same(expected[index].Hit.Property, actual[index].Hit.Property);
        }
    }

    /// <summary>
    /// Two nested wide levels (twelve and nine providers) with a repeated target, a private member, names offered by
    /// one, two and four providers, a nearer level whose only offer is private (the farther ambiguity decides), a
    /// nearer single offer hiding a farther ambiguity and a nearer ambiguity hiding a farther single offer. At every
    /// level of the chain, for every name, the selection equals the ordered scan — the same deciding level, providers
    /// and members, by reference, in provider order — and the settled index answered the wide levels.
    /// </summary>
    [Fact]
    public void WideLevelSelection_EqualsTheOrderedScan()
    {
        // Outer L0..L11: o{i} once each; shared3 four times; two twice; near everywhere; hidden twice; deep once.
        var outer = Libraries(12, i => new[] { $"o{i}", i % 3 == 0 ? "shared3" : $"p{i}", i is 2 or 7 ? "two" : $"q{i}", "near" }
            .Concat(i is 4 or 8 ? ["hidden"] : []).Concat(i == 4 ? ["deep"] : []));
        // Inner M0..M8: n{i} once each; far and deep twice; single once; hidden once; near only privately.
        var inner = string.Concat(Enumerable.Range(0, 9).Select(i => $"M{i} = {{\n    public n{i} = {i}\n"
            + (i is 1 or 5 ? "    public far = 1\n    public deep = 1\n" : "") + (i == 3 ? "    near = 2\n    public single = 3\n" : "")
            + (i == 6 ? "    public hidden = 6\n" : "") + "}\n"));
        var source = outer + inner
            + $"Use = {{\n    open {Opens(12)}, L3\n    W = {{\n        open {string.Join(", ", Enumerable.Range(0, 9).Select(i => $"M{i}"))}\n"
            + "        near + o1 + single + n4 + hidden + deep\n    }\n    o0 + W\n}\nUse\n";
        var diagnostics = SourceProvenance.ExpectFrontEndError(source);
        Assert.Equal(["'near'", "'deep'"], diagnostics.Select(diagnostic =>
        {
            Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code);
            return diagnostic.Message[..diagnostic.Message.IndexOf(' ', StringComparison.Ordinal)];
        }));
        Assert.Contains("12 different opened algorithms", diagnostics[0].Message, StringComparison.Ordinal);
        Assert.Contains("(M1, M5)", diagnostics[1].Message, StringComparison.Ordinal);

        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var observations = new FrontEndTraversalObservations();
        var program = ParameterDetector.DetectPrevalidated(syntax, observations: observations);
        var operation = program.Operation!;
        var useKey = operation.ContextOf(operation.Root, syntax.Properties.Single(property => property.Name == "Use").Value);
        var useBody = operation.SourceOf(useKey);
        var wKey = operation.ContextOf(useKey, useBody.Properties.Single(property => property.Name == "W").Value);
        var names = new[] { "o0", "o1", "o11", "shared3", "p4", "two", "q2", "near", "hidden", "deep", "far", "single", "n0", "n4", "n8",
            "missing", "z0", "M3", "L3", "" };
        var selections = observations.StaticSettledOpenSelections;
        foreach (var key in new[] { wKey, useKey, operation.Root })
        {
            var scope = operation.LookupLevel(key);
            foreach (var name in names)
            {
                AssertSameSelection(ScanFirstOpenLevel(scope, name), ElaboratedScopeLookup.SelectFirstOpenLevel(scope, name), name);
                AssertSameSelection(ElaboratedScopeLookup.ScanOpenLevel(scope, scope.GetResolvedOpenProviders(), name),
                    ElaboratedScopeLookup.SelectOpenLevel(scope, name), name);
            }
        }
        Assert.True(observations.StaticSettledOpenSelections > selections, "the settled index answered no selection");
        Assert.Equal(12, operation.Providers(useKey, StaticCycleCheck.Formation).Count); // L3 twice is one provider
        Assert.Equal(9, operation.Providers(wKey, StaticCycleCheck.Formation).Count);

        // Exactly which selections the index answers: an absent or single name at a wide level, never an ambiguous one,
        // and never a level without opens.
        var use = operation.LookupLevel(useKey);
        var w = operation.LookupLevel(wKey);
        var root = operation.LookupLevel(operation.Root);
        foreach (var (scope, name, answered) in new[]
        {
            (use, "o1", true), (use, "missing", true), (use, "deep", true), (use, "near", false), (use, "shared3", false),
            (w, "single", true), (w, "hidden", true), (w, "o1", true), (w, "far", false), (w, "deep", false), (root, "o1", false),
        })
        {
            var before = observations.StaticSettledOpenSelections;
            _ = ElaboratedScopeLookup.SelectOpenLevel(scope, name);
            Assert.True(before + (answered ? 1 : 0) == observations.StaticSettledOpenSelections, $"'{name}' answered by the index: {!answered}");
        }
    }

    /// <summary>
    /// On a wide level the ambiguity names its providers as written, in provider order — the first target that reaches
    /// each one, a repeated spelling adding nothing — and a Grace marker on an opened name keeps its reason.
    /// </summary>
    [Fact]
    public void WideLevelDiagnostics_KeepTheirProvidersOrderAndWording()
    {
        var library = Libraries(12, i => i is 3 or 9 ? ["x", $"y{i}"] : [$"y{i}"]);
        // Ten one-member libraries (three lines each) and two with x (four lines): Use's row is line 41.
        var ambiguity = Assert.Single(SourceProvenance.ExpectFrontEndError(library + $"Use = {{\n    open L9, {Opens(12)}, L3\n    x\n}}\nUse\n"));
        Assert.Equal(DiagnosticCode.AmbiguousOpen, ambiguity.Code);
        Assert.Equal("'x' is ambiguous: 2 different opened algorithms provide it at the same open level (L9, L3), so it names no single declaration. "
            + "Qualify it with the algorithm you mean, or open only one of them.", ambiguity.Message);
        Assert.Equal(new SourceSpan(41, 5, 41, 6), ambiguity.Span);

        var grace = Assert.Single(SourceProvenance.ExpectFrontEndError(library + $"Use = {{\n    open {Opens(12)}\n    ~y5 + 1\n}}\nUse\n"));
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, grace.Code);
        Assert.Equal("Grace cannot reorder 'y5' because it already resolves to an opened property. "
            + "Grace `~` only reorders the parameters an algorithm infers from its own free names; remove the marker.", grace.Message);
        Assert.Equal(new SourceSpan(41, 5, 41, 8), grace.Span);
    }
}
