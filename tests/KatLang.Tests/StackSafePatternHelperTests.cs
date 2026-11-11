using KatLang.TestInfrastructure;
using KatLang.Tests.LanguageSpec;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// The public pattern DISPLAY and CLAUSE-HEAD helpers no longer recurse on the caller's stack
/// (docs/design/language-rules/evaluator-and-hosting.md § Shared-DAG guarantee, PUBLIC PATTERN
/// HELPERS). This class pins what the rewrite must not change and what it promises on shared
/// host DAGs; the 200,000-level stack pins live beside the other host-safety pins in
/// <see cref="AstStructuralDepthTests"/>.
/// <list type="bullet">
///   <item>PARITY: the former recursive implementations are kept here verbatim as oracles, and
///   every parameter pattern and every clause head of the parser corpus (language spec, semantic
///   explorer, tutorial) gives the same text, records, names and verdict.</item>
///   <item>TREE EQUIVALENCE: on generated trees and shared DAGs each helper answers what the
///   oracle answers for the tree the DAG denotes.</item>
///   <item>DAG WORK: the Boolean query, the name list and bare forwarding's contract conversion
///   read a shared head once per distinct node; <see cref="Algorithm.ElaborateClauseGroup"/>
///   deliberately returns one record per occurrence.</item>
///   <item>THE RESOLVER ROUTE: a host edit of a deferred body's clause-head list reaches bare
///   forwarding's branch-head contracts, with the result of the tree the edit denotes.</item>
/// </list>
/// </summary>
public class StackSafePatternHelperTests(ITestOutputHelper output)
{
    // ── The former recursive implementations, verbatim (oracles) ─────────────

    private static string LegacyDisplayName(ParameterPattern pattern) => pattern switch
    {
        CaptureParameterPattern capture => capture.Parameter.DisplayName,
        SequenceValueParameterPattern sequence => $"({string.Join(", ", sequence.Items.Select(static item => LegacyDisplayName(item)))})",
        ListValueParameterPattern list => $"[{string.Join(", ", list.Items.Select(static item => LegacyDisplayName(item)))}]",
        UnpackingParameterPattern unpacking => string.Join(", ", unpacking.Items.Select(static item => LegacyDisplayName(item))),
        _ => throw new InvalidOperationException("no pattern"),
    };

    // The record layout the compiler generates for a structural pattern, over the legacy text.
    private static string LegacyToString(ParameterPattern structure)
        => $"{structure.GetType().Name} {{ DisplayName = {LegacyDisplayName(structure)}, Captures = {structure.Captures}, "
            + $"ContainsCollectingCapture = {structure.ContainsCollectingCapture}, Items = {ParameterPattern.StructuralItems(structure)} }}";

    private static bool LegacyTryCreate(Pattern pattern, out ParameterPattern? parameterPattern)
    {
        if (pattern is Pattern.Bind binder)
        {
            parameterPattern = new CaptureParameterPattern(new ParameterDeclaration(binder.Name, binder.NameSpan, binder.ParameterKind)
            {
                CollectMarkerSpan = binder.CollectMarkerSpan,
                IsRecoveryPlaceholder = binder.IsRecoveryPlaceholder,
            });
            return true;
        }

        var (structuralItems, isList, groupSpan) = pattern switch
        {
            Pattern.SequenceValue sequence => (sequence.Items, false, sequence.Span),
            Pattern.ListValue list => (list.Items, true, list.Span),
            _ => ((IReadOnlyList<Pattern>?)null, false, (SourceSpan?)null),
        };
        if (structuralItems is not null)
        {
            var childPatterns = new List<ParameterPattern>(structuralItems.Count);
            foreach (var item in structuralItems)
            {
                if (!LegacyTryCreate(item, out var childPattern))
                {
                    parameterPattern = null;
                    return false;
                }

                childPatterns.Add(childPattern!);
            }

            parameterPattern = isList
                ? new ListValueParameterPattern(childPatterns) { Source = PatternGroupSource.Written(groupSpan) }
                : new SequenceValueParameterPattern(childPatterns) { Source = PatternGroupSource.Written(groupSpan) };
            return true;
        }

        parameterPattern = null;
        return false;
    }

    private static IReadOnlyList<ParameterPattern>? LegacyParameterPatterns(Pattern head)
    {
        if (head is not Pattern.SequenceValue(var items))
            return LegacyTryCreate(head, out var single) ? [single!] : null;

        var parameterPatterns = new List<ParameterPattern>(items.Count);
        foreach (var item in items)
        {
            if (!LegacyTryCreate(item, out var parameterPattern))
                return null;

            parameterPatterns.Add(parameterPattern!);
        }

        return parameterPatterns;
    }

    private static IReadOnlyList<string>? LegacyParams(Pattern head)
        => LegacyParameterPatterns(head) is { } patterns
            ? ParameterPattern.FlattenCaptures(patterns).Select(static parameter => parameter.Name).ToList()
            : null;

    private static Algorithm LegacyElaborateClauseGroup(IReadOnlyList<CondBranch> clauses)
    {
        if (clauses.Count == 1 && LegacyParameterPatterns(clauses[0].Pattern) is { } explicitParameterPatterns)
        {
            return clauses[0].Body switch
            {
                Algorithm.User body => body with { ParameterPatterns = explicitParameterPatterns, HasExplicitParameterList = true },
                _ => clauses[0].Body,
            };
        }

        if (clauses.Count == 0)
            return new Algorithm.Conditional(Parent: null, Opens: [], Branches: []);

        return new Algorithm.Conditional(
            clauses[0].Body.Parent,
            Opens: [],
            clauses.Select(branch => branch with { Body = branch.Body.WithParams([]) }).ToList());
    }

    // ── 1. Parity over the parser corpus ─────────────────────────────────────

    [Fact]
    public void ParserCorpus_EveryParameterPattern_PrintsTheLegacyText()
    {
        var patterns = 0;
        var structural = 0;
        var nested = 0;
        foreach (var (source, root) in ParsedCorpus())
        {
            foreach (var user in Collect(root).Users)
            {
                var pending = new Stack<(ParameterPattern Pattern, int Depth)>();
                foreach (var pattern in user.ParameterPatterns)
                    pending.Push((pattern, 0));
                while (pending.TryPop(out var entry))
                {
                    var (pattern, depth) = entry;
                    patterns++;
                    var expected = LegacyDisplayName(pattern);
                    Assert.True(expected == pattern.DisplayName, $"display '{pattern.DisplayName}' is not '{expected}' in:\n{source}");
                    if (ParameterPattern.StructuralItems(pattern) is not { } items)
                        continue;
                    structural++;
                    nested += depth > 0 ? 1 : 0;
                    Assert.True(LegacyToString(pattern) == pattern.ToString(), $"record text of '{expected}' changed in:\n{source}");
                    foreach (var item in items)
                        pending.Push((item, depth + 1));
                }
            }
        }

        output.WriteLine($"{patterns} parameter patterns, {structural} structural, {nested} nested structural");
        Assert.True(patterns > 2000, $"too few patterns: {patterns}");
        Assert.True(structural > 200, $"too few structural patterns: {structural}");
        Assert.True(nested > 10, $"too few nested structural patterns: {nested}");
    }

    [Fact]
    public void ParserCorpus_EveryClauseHead_ConvertsLikeTheLegacyRecursion()
    {
        var familyHeads = 0;
        var ordinaryFamilyHeads = 0;
        var writtenLists = 0;
        var roundTrips = 0;
        var structuredLists = 0;
        foreach (var (source, root) in ParsedCorpus())
        {
            var collected = Collect(root);

            // Heads the tree retains: every clause of a family.
            foreach (var family in collected.Families)
            {
                foreach (var branch in family.Branches)
                {
                    familyHeads++;
                    ordinaryFamilyHeads += AssertHeadParity(branch.Pattern, source) ? 1 : 0;
                }
            }

            // Heads elaboration consumed: an ordinary clause keeps only its parameter list, which
            // determines the head it was written with.
            foreach (var user in collected.Users)
            {
                if (!user.HasExplicitParameterList || HeadOf(user.ParameterPatterns) is not { } head)
                    continue;
                writtenLists++;
                Assert.True(AssertHeadParity(head, source), $"a written parameter list is no ordinary head in:\n{source}");
                var converted = head.TryGetOrdinaryClauseParameterPatterns()!;
                Assert.True(user.ParameterPatterns.Count == converted.Count, source);
                for (var index = 0; index < converted.Count; index++)
                    AssertSameRecords(user.ParameterPatterns[index], converted[index], compareListTypes: false, source);
                Assert.True(user.Params.SequenceEqual(head.TryGetOrdinaryClauseParams()!), source);
                roundTrips++;
                structuredLists += user.ParameterPatterns.Any(static pattern => pattern is not CaptureParameterPattern) ? 1 : 0;

                // The public elaboration entry gives the legacy algorithm for that head.
                var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
                var elaborated = Assert.IsType<Algorithm.User>(Algorithm.ElaborateClauseDefinition(head, body));
                var legacy = Assert.IsType<Algorithm.User>(LegacyElaborateClauseGroup([new CondBranch(head, body)]));
                Assert.True(elaborated.HasExplicitParameterList && legacy.HasExplicitParameterList, source);
                Assert.True(legacy.ParameterPatterns.Count == elaborated.ParameterPatterns.Count, source);
                for (var index = 0; index < legacy.ParameterPatterns.Count; index++)
                    AssertSameRecords(legacy.ParameterPatterns[index], elaborated.ParameterPatterns[index], compareListTypes: true, source);
            }
        }

        output.WriteLine(
            $"{familyHeads} family heads ({ordinaryFamilyHeads} literal-free), {writtenLists} written parameter lists, "
            + $"{roundTrips} round trips, {structuredLists} with structural patterns");
        Assert.True(familyHeads > 300, $"too few family heads: {familyHeads}");
        Assert.True(ordinaryFamilyHeads > 50, $"too few literal-free family heads: {ordinaryFamilyHeads}");
        Assert.True(writtenLists > 1000, $"too few written lists: {writtenLists}");
        Assert.True(structuredLists > 100, $"too few structured lists: {structuredLists}");
    }

    // Every helper against its oracle for one head; returns whether the head is ordinary.
    private static bool AssertHeadParity(Pattern head, string context)
    {
        var legacy = LegacyParameterPatterns(head);
        var actual = head.TryGetOrdinaryClauseParameterPatterns();
        Assert.True((legacy is null) == (actual is null), context);
        Assert.True((legacy is null) == head.RequiresConditionalClauseSemantics(), context);
        var legacyNames = LegacyParams(head);
        var names = head.TryGetOrdinaryClauseParams();
        Assert.True((legacyNames is null) == (names is null), context);
        if (legacy is null)
            return false;

        Assert.True(legacy.GetType().FullName == actual!.GetType().FullName, context);
        Assert.True(legacy.Count == actual.Count, context);
        for (var index = 0; index < legacy.Count; index++)
            AssertSameRecords(legacy[index], actual[index], compareListTypes: true, context);
        Assert.IsType<List<string>>(names);
        Assert.True(legacyNames!.SequenceEqual(names!), context);
        Assert.True(names!.SequenceEqual(head.BoundNames()), context);
        return true;
    }

    // ── 2. Trees and shared DAGs against the oracle ──────────────────────────

    [Fact]
    public void OnTreesAndSharedDags_EveryHelper_AnswersLikeTheLegacyRecursion()
    {
        var random = new Random(20261111);
        var shared = 0;
        var ordinary = 0;
        var ordinaryShared = 0;
        var keptSharing = 0;
        var refusedItems = 0;
        for (var round = 0; round < 2000; round++)
        {
            var (head, sharesNodes) = RandomHead(random);
            var context = $"round {round}";
            shared += sharesNodes ? 1 : 0;

            // The per-occurrence conversion, the names and the verdict are the oracle's.
            var isOrdinary = AssertHeadParity(head, context);
            ordinary += isOrdinary ? 1 : 0;
            ordinaryShared += isOrdinary && sharesNodes ? 1 : 0;
            if (isOrdinary)
            {
                // One record per occurrence: nothing of the result is shared, whatever the head shares.
                var (occurrences, distinct) = CountRecords(head.TryGetOrdinaryClauseParameterPatterns()!);
                Assert.True(occurrences == distinct, context);
            }

            // Bare forwarding's conversion: one memo for the head's items, as the resolver uses it.
            var items = head is Pattern.SequenceValue(var topLevelItems) ? topLevelItems : [head];
            Dictionary<Pattern, ParameterPattern?>? memo = null;
            var kept = new List<ParameterPattern>();
            foreach (var item in items)
            {
                var legacyOk = LegacyTryCreate(item, out var legacy);
                var ok = Pattern.TryCreateOrdinaryClauseParameterPatternKeepingSharing(item, ref memo, out var sharedPattern);
                Assert.True(legacyOk == ok, context);
                refusedItems += ok ? 0 : 1;
                if (!ok)
                    continue;

                // The same contract and the same captures in order: the result denotes the legacy tree.
                Assert.True(ParameterPattern.ContractComparer.Equals(legacy, sharedPattern), context);
                Assert.True(
                    ParameterPattern.ContractComparer.GetHashCode(legacy!) == ParameterPattern.ContractComparer.GetHashCode(sharedPattern!),
                    context);
                Assert.True(
                    ParameterPattern.FlattenCaptures([legacy!]).SequenceEqual(ParameterPattern.FlattenCaptures([sharedPattern!])),
                    context);
                Assert.True(LegacyDisplayName(legacy!) == sharedPattern!.DisplayName, context);
                kept.Add(sharedPattern);
            }

            var (keptOccurrences, keptDistinct) = CountRecords(kept);
            Assert.True(keptDistinct <= CountDistinctGroups(head), context);
            keptSharing += keptOccurrences > keptDistinct ? 1 : 0;
        }

        output.WriteLine(
            $"2000 heads: {shared} share nodes, {ordinary} ordinary ({ordinaryShared} of them shared), "
            + $"{keptSharing} conversions kept sharing, {refusedItems} items refused for a literal");
        Assert.True(shared > 1000, $"too few shared heads: {shared}");
        Assert.True(ordinary > 1000 && 2000 - ordinary > 300, $"vacuous split: {ordinary} ordinary");
        Assert.True(ordinaryShared > 200, $"too few ordinary shared heads: {ordinaryShared}");
        Assert.True(keptSharing > 200, $"too few shared conversions: {keptSharing}");
        Assert.True(refusedItems > 200, $"too few refused items: {refusedItems}");
    }

    [Fact]
    public void OnTreesAndSharedDags_DisplayAndRecordText_AreTheLegacyText()
    {
        var random = new Random(20261112);
        var shared = 0;
        for (var round = 0; round < 2000; round++)
        {
            var (pattern, sharesNodes) = RandomParameterPattern(random);
            shared += sharesNodes ? 1 : 0;
            var expected = LegacyDisplayName(pattern);
            Assert.True(expected == pattern.DisplayName, $"round {round}: '{pattern.DisplayName}' is not '{expected}'");
            if (pattern is not CaptureParameterPattern)
                Assert.True(LegacyToString(pattern) == pattern.ToString(), $"round {round}: record text of '{expected}'");
        }

        Assert.True(shared > 800, $"too few shared patterns: {shared}");
    }

    [Fact]
    public void DisplayName_KeepsEveryDelimiterAndSeparatorForm()
    {
        var a = new CaptureParameterPattern("a");
        var rest = new CaptureParameterPattern("rest", Kind: ParameterKind.Collecting);
        var m = new CaptureParameterPattern("m", Kind: ParameterKind.Meta);
        Assert.Equal("()", new SequenceValueParameterPattern([]).DisplayName);
        Assert.Equal("[]", new ListValueParameterPattern([]).DisplayName);
        Assert.Equal("", new UnpackingParameterPattern([]).DisplayName);
        Assert.Equal("(a)", new SequenceValueParameterPattern([a]).DisplayName);
        Assert.Equal("[a, *rest]", new ListValueParameterPattern([a, rest]).DisplayName);
        Assert.Equal("a, *rest, meta m", new UnpackingParameterPattern([a, rest, m]).DisplayName);
        Assert.Equal(
            "(a, [(), []], (a, *rest), [])",
            new SequenceValueParameterPattern(
            [
                a,
                new ListValueParameterPattern([new SequenceValueParameterPattern([]), new ListValueParameterPattern([])]),
                new SequenceValueParameterPattern([a, rest]),
                new ListValueParameterPattern([]),
            ]).DisplayName);

        // An unpacking receiver has no delimiters wherever a host puts it, and an empty one
        // still takes its separators.
        Assert.Equal(
            "[a, a, *rest, , (a)]",
            new ListValueParameterPattern(
            [
                a,
                new UnpackingParameterPattern([a, rest]),
                new UnpackingParameterPattern([]),
                new SequenceValueParameterPattern([a]),
            ]).DisplayName);

        // The text is read from the lists on every call: no cache.
        var items = new List<ParameterPattern> { a };
        var live = new SequenceValueParameterPattern(items);
        Assert.Equal("(a)", live.DisplayName);
        items.Add(rest);
        Assert.Equal("(a, *rest)", live.DisplayName);
        Assert.Equal(
            "SequenceValueParameterPattern { DisplayName = (a, *rest), Captures = System.Collections.Generic.List`1[KatLang.ParameterDeclaration], "
            + "ContainsCollectingCapture = True, Items = System.Collections.Generic.List`1[KatLang.ParameterPattern] }",
            live.ToString());
    }

    [Fact]
    public void ANullItemOrList_IsStillAnException_NeverAWrongAnswer()
    {
        // Host-built lists may hold what no parser writes. Display keeps failing on a null item;
        // the clause-head helpers keep treating a null item, like a literal, as no binder.
        Assert.Throws<NullReferenceException>(() => new SequenceValueParameterPattern([null!]).DisplayName);
        Assert.Throws<NullReferenceException>(() => new ListValueParameterPattern([new CaptureParameterPattern("a"), null!]).DisplayName);
        // A null items list keeps Enumerable.Select's ArgumentNullException, even when nested,
        // for display and for the record text that prints it.
        foreach (var kind in KindNames)
        {
            var group = Structural(kind, null!);
            foreach (var pattern in new[] { group, new UnpackingParameterPattern([group]) })
            {
                var legacy = Assert.Throws<ArgumentNullException>(() => LegacyDisplayName(pattern));
                var display = Assert.Throws<ArgumentNullException>(() => pattern.DisplayName);
                var record = Assert.Throws<ArgumentNullException>(() => pattern.ToString());
                Assert.Equal(legacy.ParamName, display.ParamName);
                Assert.Equal(legacy.ParamName, record.ParamName);
            }
        }

        var withNull = new Pattern.SequenceValue([new Pattern.Bind("a"), new Pattern.ListValue([null!])]);
        Assert.True(withNull.RequiresConditionalClauseSemantics());
        Assert.Null(withNull.TryGetOrdinaryClauseParams());
        Assert.Null(withNull.TryGetOrdinaryClauseParameterPatterns());
        Assert.True(LegacyParameterPatterns(withNull) is null);

        var nullItems = new Pattern.SequenceValue([new Pattern.ListValue(null!)]);
        Assert.True(nullItems.RequiresConditionalClauseSemantics());
        Assert.Null(nullItems.TryGetOrdinaryClauseParams());
        Assert.True(LegacyParameterPatterns(nullItems) is null);
        Assert.True(new Pattern.ListValue(null!).RequiresConditionalClauseSemantics());
        Assert.True(LegacyParameterPatterns(new Pattern.ListValue(null!)) is null);

        // The head's own argument list was never optional.
        Assert.Throws<NullReferenceException>(() => new Pattern.SequenceValue(null!).RequiresConditionalClauseSemantics());
        Assert.Throws<NullReferenceException>(() => LegacyParameterPatterns(new Pattern.SequenceValue(null!)));

        Dictionary<Pattern, ParameterPattern?>? memo = null;
        Assert.False(Pattern.TryCreateOrdinaryClauseParameterPatternKeepingSharing(null!, ref memo, out _));
        Assert.False(Pattern.TryCreateOrdinaryClauseParameterPatternKeepingSharing(withNull, ref memo, out _));
        Assert.False(Pattern.TryCreateOrdinaryClauseParameterPatternKeepingSharing(withNull, ref memo, out _));
    }

    // ── 3. Work on shared DAGs ───────────────────────────────────────────────

    public static TheoryData<string, int> DiamondCases()
    {
        var cases = new TheoryData<string, int>();
        foreach (var bottom in new[] { "binder", "empty", "literal", "lateLiteral" })
        {
            foreach (var depth in new[] { 15, 30, 45, 90, 5000 })
                cases.Add(bottom, depth);
        }

        return cases;
    }

    [Theory]
    [MemberData(nameof(DiamondCases))]
    public void RequiresConditionalClauseSemantics_ReadsASharedHeadOncePerNode(string bottom, int depth)
    {
        // depth + 1 distinct nodes, 2^depth paths: a per-path walk exhausts the budget at once.
        var budget = new PatternReadBudget(4 * (depth + 2));
        var head = DiamondHead(bottom, depth, budget);
        var expected = bottom is "literal" or "lateLiteral";

        Assert.Equal(expected, head.RequiresConditionalClauseSemantics());
        output.WriteLine($"{bottom}: depth {depth}, reads = {budget.Reads}");
        Assert.InRange(budget.Reads, MinimumReads(bottom, depth), 2 * (depth + 1));

        // Asking again reads the head again: nothing was attached to it.
        var first = budget.Reads;
        Assert.Equal(expected, head.RequiresConditionalClauseSemantics());
        Assert.Equal(2 * first, budget.Reads);
    }

    [Theory]
    [InlineData(12)]
    [InlineData(24)]
    [InlineData(48)]
    [InlineData(96)]
    public void RequiresConditionalClauseSemantics_WorkGrowsLinearlyWithDepth(int depth)
    {
        foreach (var bottom in new[] { "binder", "empty" })
        {
            var budget = new PatternReadBudget(8 * depth);
            Assert.False(DiamondHead(bottom, depth, budget).RequiresConditionalClauseSemantics());
            // Two item reads per level, exactly: the first expands the shared child, the second finds it expanded.
            Assert.Equal(2 * depth, budget.Reads);
        }
    }

    [Theory]
    [InlineData("literal", 90, 0)]
    [InlineData("lateLiteral", 90, 0)]
    [InlineData("empty", 90, 0)]
    [InlineData("empty", 5000, 0)]
    [InlineData("binder", 10, 1 << 10)]
    [InlineData("binder", 16, 1 << 16)]
    public void TryGetOrdinaryClauseParams_IsOutputSensitiveOnASharedHead(string bottom, int depth, int expectedNames)
    {
        var budget = new PatternReadBudget(8 * (depth + 2));
        var head = DiamondHead(bottom, depth, budget);

        var names = head.TryGetOrdinaryClauseParams();

        output.WriteLine($"{bottom}: depth {depth}, reads = {budget.Reads}, names = {names?.Count}");
        if (bottom is "literal" or "lateLiteral")
        {
            Assert.Null(names);
        }
        else
        {
            // One name per occurrence, as for the expanded tree; the reads stay per distinct node.
            Assert.Equal(expectedNames, names!.Count);
            Assert.All(names, static name => Assert.Equal("x", name));
        }

        Assert.InRange(budget.Reads, MinimumReads(bottom, depth), 4 * (depth + 1));
    }

    // Every level is read at least once, except that a literal standing in the head's own
    // argument list is found before anything below it is read.
    private static int MinimumReads(string bottom, int depth) => bottom == "lateLiteral" ? 1 : depth;

    [Theory]
    [InlineData("literal")]
    [InlineData("lateLiteral")]
    public void ElaborateClauseGroup_RefusesASharedLiteralHeadWithoutExpandingIt(string bottom)
    {
        const int Depth = 90;
        var budget = new PatternReadBudget(4 * (Depth + 2));
        var head = DiamondHead(bottom, Depth, budget);
        var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);

        var family = Assert.IsType<Algorithm.Conditional>(Algorithm.ElaborateClauseDefinition(head, body));

        Assert.Same(head, Assert.Single(family.Branches).Pattern);
        Assert.InRange(budget.Reads, MinimumReads(bottom, Depth), 2 * (Depth + 1));
    }

    [Fact]
    public void ElaborateClauseGroup_ReturnsOneRecordPerOccurrenceOfASharedGroup()
    {
        // THE DECISION (evaluator-and-hosting.md, PUBLIC PATTERN HELPERS): the elaborated parameter
        // list is public, and two occurrences of one group are DISTINCT records in it — unequal
        // under record equality, whose items lists compare by reference. Keeping the head's sharing
        // would make them one record, which a host can observe; the expansion is kept.
        var shared = new Pattern.ListValue([new Pattern.Bind("a"), new Pattern.Bind("b")]);
        var head = new Pattern.SequenceValue([shared, shared]);
        var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);

        var user = Assert.IsType<Algorithm.User>(Algorithm.ElaborateClauseDefinition(head, body));
        var legacy = Assert.IsType<Algorithm.User>(LegacyElaborateClauseGroup([new CondBranch(head, body)]));

        Assert.Equal(["a", "b", "a", "b"], user.Params);
        foreach (var result in new[] { user, legacy })
        {
            Assert.Equal(2, result.ParameterPatterns.Count);
            Assert.NotSame(result.ParameterPatterns[0], result.ParameterPatterns[1]);
            Assert.False(result.ParameterPatterns[0].Equals(result.ParameterPatterns[1]));
            Assert.Equal("[a, b]", result.ParameterPatterns[0].DisplayName);
            Assert.Equal("[a, b]", result.ParameterPatterns[1].DisplayName);
        }

        // The resolver-only conversion keeps the sharing, and is the same contract.
        Dictionary<Pattern, ParameterPattern?>? memo = null;
        Assert.True(Pattern.TryCreateOrdinaryClauseParameterPatternKeepingSharing(shared, ref memo, out var first));
        Assert.True(Pattern.TryCreateOrdinaryClauseParameterPatternKeepingSharing(shared, ref memo, out var second));
        Assert.Same(first, second);
        Assert.True(ParameterPattern.ContractComparer.Equals(first, user.ParameterPatterns[0]));

        // A deeper shared head expands to its tree: 2^depth leaves, every record its own.
        const int Depth = 10;
        var budget = new PatternReadBudget(1 << (Depth + 3));
        var diamond = DiamondHead("binder", Depth, budget);
        var expanded = Assert.IsType<Algorithm.User>(Algorithm.ElaborateClauseDefinition(diamond, body));
        Assert.Equal(1 << Depth, expanded.ParameterCount);
        var (occurrences, distinct) = CountRecords(expanded.ParameterPatterns);
        Assert.Equal((1 << Depth) - 2, occurrences);
        Assert.Equal(occurrences, distinct);
        output.WriteLine($"expanded depth {Depth}: {occurrences} structural records, reads = {budget.Reads}");
        Assert.InRange(budget.Reads, 1 << Depth, 1 << (Depth + 2));
    }

    [Theory]
    [InlineData("binder", 90)]
    [InlineData("empty", 90)]
    [InlineData("literal", 90)]
    [InlineData("binder", 250)]
    public void BareForwardingConversion_ConvertsASharedHeadOncePerNode(string bottom, int depth)
    {
        var budget = new PatternReadBudget(4 * (depth + 2));
        var item = Diamond(BottomOf(bottom), depth, budget);

        Dictionary<Pattern, ParameterPattern?>? memo = null;
        var converted = Pattern.TryCreateOrdinaryClauseParameterPatternKeepingSharing(item, ref memo, out var pattern);

        output.WriteLine($"{bottom}: depth {depth}, reads = {budget.Reads}");
        Assert.InRange(budget.Reads, depth, 2 * (depth + 1));
        Assert.Equal(bottom != "literal", converted);
        if (converted)
        {
            // depth distinct records, each holding its one child twice.
            var distinct = new HashSet<ParameterPattern>(ReferenceEqualityComparer.Instance);
            var levels = 0;
            for (var current = pattern!; ParameterPattern.StructuralItems(current) is { Count: 2 } items; current = items[0])
            {
                // A shared group is one record; a binder is converted per occurrence.
                Assert.True(items[0] is CaptureParameterPattern ? items[0].Equals(items[1]) : ReferenceEquals(items[0], items[1]));
                Assert.True(distinct.Add(current));
                levels++;
            }

            Assert.Equal(depth, levels);
            // Its contract hash is computed once per node as well.
            _ = ParameterPattern.ContractComparer.GetHashCode(pattern!);
        }

        // A second item of the same head is answered from the memo: no further read.
        var reads = budget.Reads;
        Assert.Equal(converted, Pattern.TryCreateOrdinaryClauseParameterPatternKeepingSharing(item, ref memo, out var again));
        Assert.Same(pattern, again);
        Assert.Equal(reads, budget.Reads);
    }

    // ── 4. The resolver route: a host edit of a deferred body's clause head ──

    [Theory]
    [InlineData(1, false)]
    [InlineData(1, true)]
    [InlineData(3, false)]
    [InlineData(3, true)]
    [InlineData(6, false)]
    [InlineData(6, true)]
    public async Task DeferredClauseHead_EditedByTheHost_ReachesBareForwardingContracts(int depth, bool expanded)
    {
        // K's second clause forwards to G only if its head declares G's pattern. As written it does
        // not ([u, v] against G's nested lists); the host installs the matching pattern — a shared
        // diamond, or the tree it denotes — in the deferred body before it is first compiled.
        var result = await RunDeferredForwarding(depth, edit: expanded ? "tree" : "diamond");
        Assert.True(result.Outcome.IsOk, result.Outcome.IsError ? result.Outcome.Error.ToString() : "");
        Assert.Equal(new Result.Atom(42), result.Outcome.Value);
        output.WriteLine($"depth {depth}, {(expanded ? "tree" : "diamond")}: reads = {result.Reads}, result = 42");
    }

    [Fact]
    public async Task DeferredClauseHead_LeftAsWritten_IsNotForwardable()
    {
        // The control: without the edit the same program is refused, so the 42 above is decided by
        // the head the host installed.
        var result = await RunDeferredForwarding(depth: 3, edit: "none");
        Assert.True(result.Outcome.IsError);
        var error = result.Outcome.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var failure = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
        Assert.Equal(DiagnosticCode.UnforwardableParameter, failure.Primary.Code);
        Assert.Contains("'[[[x, x], [x, x]], [[x, x], [x, x]]]' is not bound by the pattern of conditional branch 'K'", failure.Primary.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task DeferredClauseHead_DeeperThanTheStructuralGate_IsRefusedBeforeTheResolver()
    {
        // A host cannot send a head deeper than the structural gate to the resolver: the run's
        // admission refuses it, so the 200,000-level pins of the public helpers have no resolver twin.
        var result = await RunDeferredForwarding(depth: 3, edit: "spine");
        Assert.True(result.Outcome.IsError);
        Assert.Equal(EvaluationLimits.MaxSupportedAstDepth, Assert.IsType<EvalError.AstDepthLimitExceeded>(result.Outcome.Error).Limit);
    }

    private static async Task<(EvalResult<Result> Outcome, int Reads)> RunDeferredForwarding(int depth, string edit)
    {
        var source = "F(0) = 0\nF(n) = { open 'https://katlang.org/clause-head-probe'\n"
            + $"G({Nested("x", depth)}) = x + 41\nK(0, 0) = 0\nK([u, v], 1) = G\nK({Nested("1", depth)}, 1) }}\nF(1)";
        var downloads = 0;
        var parsed = await SourceProvenance.ParseValidAsync(source, new RunOptions
        {
            DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult("public ModuleValue = 1"); },
        });
        Assert.Equal(0, downloads);
        var outer = Assert.IsType<Algorithm.Conditional>(parsed.Root.Properties.Single(static p => p.Name == "F").Value);
        var deferredBody = outer.Branches[1].Body;
        var family = Assert.IsType<Algorithm.Conditional>(deferredBody.Properties.Single(static p => p.Name == "K").Value);
        var head = Assert.IsType<Pattern.SequenceValue>(family.Branches[1].Pattern);
        var group = Assert.IsType<Pattern.ListValue>(head.Items[0]);
        // The public placeholder view retains this membership from the raw deferred body.
        var items = Assert.IsAssignableFrom<IList<Pattern>>(group.Items);
        var budget = new PatternReadBudget(1_000_000);
        switch (edit)
        {
            case "diamond":
                items[0] = Diamond(new Pattern.Bind("x"), depth - 1, budget, list: true);
                items[1] = items[0];
                break;
            case "tree":
                items[0] = Tree(depth - 1);
                items[1] = Tree(depth - 1);
                break;
            case "spine":
                Pattern spine = new Pattern.Bind("x");
                for (var level = 0; level < 200_000; level++)
                    spine = new Pattern.ListValue([spine]);
                items[0] = spine;
                break;
        }

        var outcome = await Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root));
        return (outcome, budget.Reads);
    }

    // "[[x, x], [x, x]]" for depth 2: the written form of a depth-level list diamond.
    private static string Nested(string leaf, int depth)
    {
        var text = leaf;
        for (var level = 0; level < depth; level++)
            text = $"[{text}, {text}]";
        return text;
    }

    private static Pattern Tree(int levels)
        => levels == 0
            ? new Pattern.Bind("x")
            : new Pattern.ListValue(new List<Pattern> { Tree(levels - 1), Tree(levels - 1) });

    // ── Shapes ───────────────────────────────────────────────────────────────

    private static Pattern BottomOf(string bottom) => bottom switch
    {
        "binder" or "lateLiteral" => new Pattern.Bind("x"),
        "empty" => new Pattern.ListValue([]),
        _ => new Pattern.LitInt(0),
    };

    // Shares one sub-pattern twice per level: levels + 1 distinct nodes, 2^levels bottom occurrences.
    private static Pattern Diamond(Pattern bottom, int levels, PatternReadBudget budget, bool list = false)
    {
        var pattern = bottom;
        for (var level = 0; level < levels; level++)
        {
            var items = new BudgetedPatternItems<Pattern>(pattern, pattern, budget);
            pattern = list || level % 2 == 1 ? new Pattern.ListValue(items) : new Pattern.SequenceValue(items);
        }

        return pattern;
    }

    // A head whose argument list is the diamond's top level; "lateLiteral" hides one literal
    // behind the whole shared part, where a per-path walk would reach it last.
    private static Pattern DiamondHead(string bottom, int depth, PatternReadBudget budget)
    {
        if (bottom != "lateLiteral")
            return AsHead(Diamond(BottomOf(bottom), depth, budget));

        var below = Diamond(BottomOf(bottom), depth - 1, budget);
        return new Pattern.SequenceValue(new BudgetedPatternItems<Pattern>(below, new Pattern.LitInt(7), budget));
    }

    // The top level of a diamond as the head's own argument list.
    private static Pattern AsHead(Pattern diamond)
        => diamond is Pattern.SequenceValue ? diamond : new Pattern.SequenceValue(((Pattern.ListValue)diamond).Items);

    private static readonly string[] Names = ["a", "b", "c"];

    private static Pattern RandomLeaf(Random random)
    {
        switch (random.Next(16))
        {
            case 0 or 1 or 2:
                return new Pattern.LitInt(random.Next(3));
            case 3 or 4:
                return random.Next(2) == 0 ? new Pattern.LitString("s") : new Pattern.LitBool(true);
            default:
                var kind = random.Next(5) switch { 0 => ParameterKind.Collecting, 1 => ParameterKind.Meta, _ => ParameterKind.Normal };
                var located = random.Next(2) == 0;
                return new Pattern.Bind(Names[random.Next(Names.Length)])
                {
                    NameSpan = located ? new SourceSpan(1, random.Next(1, 9), 1, 10) : null,
                    ParameterKind = kind,
                    CollectMarkerSpan = located && kind == ParameterKind.Collecting ? new SourceSpan(1, 1, 1, 2) : null,
                    IsRecoveryPlaceholder = random.Next(8) == 0,
                };
        }
    }

    private static Pattern Group(Random random, IReadOnlyList<Pattern> items)
    {
        SourceSpan? span = random.Next(2) == 0 ? new SourceSpan(2, random.Next(1, 9), 2, 12) : null;
        return random.Next(2) == 0
            ? new Pattern.SequenceValue(items) { Span = span }
            : new Pattern.ListValue(items) { Span = span };
    }

    // Uneven multi-parent heads: leaves and empty groups shared at several heights.
    private static (Pattern Head, bool SharesNodes) RandomHead(Random random)
    {
        var pool = new List<(Pattern Node, int Height)>();
        for (var index = random.Next(1, 4); index > 0; index--)
            pool.Add((RandomLeaf(random), 0));
        for (var index = random.Next(0, 3); index > 0; index--)
            pool.Add((Group(random, new List<Pattern>()), 1));

        var uses = new Dictionary<Pattern, int>(ReferenceEqualityComparer.Instance);
        Pattern Pick(int window)
        {
            var candidates = pool.Where(static entry => entry.Height < 6).ToList();
            var pick = candidates[Math.Max(0, candidates.Count - 1 - random.Next(Math.Min(window, candidates.Count)) - (random.Next(3) == 0 ? random.Next(candidates.Count) : 0))];
            uses[pick.Node] = uses.GetValueOrDefault(pick.Node) + 1;
            return pick.Node;
        }

        int HeightOf(Pattern node) => pool.First(entry => ReferenceEquals(entry.Node, node)).Height;

        for (var index = random.Next(1, 8); index > 0; index--)
        {
            var items = new List<Pattern>();
            for (var item = random.Next(0, 4); item > 0; item--)
                items.Add(Pick(window: 3));
            pool.Add((Group(random, items), items.Count == 0 ? 1 : items.Max(HeightOf) + 1));
        }

        Pattern head;
        if (random.Next(4) == 0)
        {
            // A head that is one parameter position (a binder, a literal or a host-built lone group).
            head = Pick(window: 3);
        }
        else
        {
            var top = new List<Pattern>();
            for (var index = random.Next(0, 4); index > 0; index--)
                top.Add(Pick(window: 3));
            head = new Pattern.SequenceValue(top);
        }

        return (head, uses.Any(static use => use.Value > 1 && use.Key is Pattern.SequenceValue or Pattern.ListValue));
    }

    private static readonly string[] KindNames = ["sequence", "list", "unpack"];

    private static ParameterPattern Structural(string kind, IReadOnlyList<ParameterPattern> items) => kind switch
    {
        "sequence" => new SequenceValueParameterPattern(items),
        "list" => new ListValueParameterPattern(items),
        _ => new UnpackingParameterPattern(items),
    };

    private static (ParameterPattern Pattern, bool SharesNodes) RandomParameterPattern(Random random)
    {
        var pool = new List<(ParameterPattern Node, int Height)>();
        for (var index = random.Next(1, 4); index > 0; index--)
        {
            var kind = random.Next(4) switch { 0 => ParameterKind.Collecting, 1 => ParameterKind.Meta, _ => ParameterKind.Normal };
            pool.Add((new CaptureParameterPattern(Names[random.Next(Names.Length)], Kind: kind), 0));
        }

        for (var index = random.Next(0, 3); index > 0; index--)
            pool.Add((Structural(KindNames[random.Next(KindNames.Length)], new List<ParameterPattern>()), 1));

        var uses = new Dictionary<ParameterPattern, int>(ReferenceEqualityComparer.Instance);
        for (var index = random.Next(1, 8); index > 0; index--)
        {
            var items = new List<ParameterPattern>();
            var height = 0;
            for (var item = random.Next(0, 4); item > 0; item--)
            {
                var candidates = pool.Where(static entry => entry.Height < 6).ToList();
                var pick = candidates[Math.Max(0, candidates.Count - 1 - random.Next(Math.Min(3, candidates.Count)) - (random.Next(3) == 0 ? random.Next(candidates.Count) : 0))];
                items.Add(pick.Node);
                uses[pick.Node] = uses.GetValueOrDefault(pick.Node) + 1;
                height = Math.Max(height, pick.Height + 1);
            }

            pool.Add((Structural(KindNames[random.Next(KindNames.Length)], items), Math.Max(1, height)));
        }

        return (pool[^1].Node, uses.Values.Any(static count => count > 1));
    }

    // ── Corpus and comparison plumbing ───────────────────────────────────────

    private static readonly Lazy<IReadOnlyList<(string Source, Algorithm.User Root)>> Corpus = new(BuildCorpus);

    private static IReadOnlyList<(string Source, Algorithm.User Root)> ParsedCorpus() => Corpus.Value;

    // Every program of the three shared corpora, elaborated; an erroneous program contributes its
    // recovered tree, which the parser built as well (hence the permissive parse: the subject is
    // every pattern the parser produces, and no evaluator outcome is read from these trees).
    private static IReadOnlyList<(string Source, Algorithm.User Root)> BuildCorpus()
    {
        var sources = new List<string>();
        foreach (var specCase in LanguageSpecCorpus.AllCases())
        {
            sources.Add(specCase.Source);
            sources.AddRange(specCase.Probes.Select(static probe => probe.Probe));
        }

        sources.AddRange(SemanticExplorerCorpus.AllCases().Select(static explorerCase => explorerCase.Source));
        sources.AddRange(TutorialCorpus.Examples.Select(static example => example.Source));
        return sources.Distinct(StringComparer.Ordinal)
            .Select(static source => (source, SourceProvenance.ParseAllowingDiagnostics(source).Root))
            .ToList();
    }

    private sealed class AlgorithmCollector : AstWalker
    {
        public List<Algorithm.User> Users { get; } = [];

        public List<Algorithm.Conditional> Families { get; } = [];

        protected override bool VisitsExplicitParameterDeclarations => false;

        protected override void VisitUserAlgorithm(Algorithm.User algorithm)
        {
            Users.Add(algorithm);
            base.VisitUserAlgorithm(algorithm);
        }

        protected override void VisitConditionalAlgorithm(Algorithm.Conditional algorithm)
        {
            Families.Add(algorithm);
            base.VisitConditionalAlgorithm(algorithm);
        }
    }

    private static AlgorithmCollector Collect(Algorithm root)
    {
        var collector = new AlgorithmCollector();
        collector.VisitAlgorithm(root);
        return collector;
    }

    // The clause head a written parameter list was elaborated from (the parser's own wrapping
    // rule), or null for a list no clause head denotes: a deconstruction receiver, or a group
    // that is only part of what was written.
    private static Pattern? HeadOf(IReadOnlyList<ParameterPattern> patterns)
    {
        var items = new List<Pattern>(patterns.Count);
        foreach (var pattern in patterns)
        {
            if (ItemOf(pattern) is not { } item)
                return null;
            items.Add(item);
        }

        if (items.Count != 1)
            return new Pattern.SequenceValue(items);
        return items[0] is Pattern.SequenceValue or Pattern.ListValue ? new Pattern.SequenceValue(items) : items[0];
    }

    private static Pattern? ItemOf(ParameterPattern pattern)
    {
        if (pattern is CaptureParameterPattern capture)
        {
            return new Pattern.Bind(capture.Name)
            {
                NameSpan = capture.Span,
                ParameterKind = capture.Kind,
                CollectMarkerSpan = capture.CollectMarkerSpan,
                IsRecoveryPlaceholder = capture.Parameter.IsRecoveryPlaceholder,
            };
        }

        if (pattern is UnpackingParameterPattern || ParameterPattern.GroupSource(pattern) is { IsFiltered: true })
            return null;

        var items = new List<Pattern>();
        foreach (var child in ParameterPattern.StructuralItems(pattern)!)
        {
            if (ItemOf(child) is not { } item)
                return null;
            items.Add(item);
        }

        var span = ParameterPattern.GroupSource(pattern)?.WrittenSpan;
        return pattern is ListValueParameterPattern
            ? new Pattern.ListValue(items) { Span = span }
            : new Pattern.SequenceValue(items) { Span = span };
    }

    // Record for record: kinds, declarations (name, span, kind, collect marker, recovery mark),
    // group sources and — between two fresh conversions — the runtime types of the items lists.
    private static void AssertSameRecords(ParameterPattern expected, ParameterPattern actual, bool compareListTypes, string context)
    {
        var pending = new Stack<(ParameterPattern Expected, ParameterPattern Actual)>();
        pending.Push((expected, actual));
        while (pending.TryPop(out var pair))
        {
            Assert.True(pair.Expected.GetType() == pair.Actual.GetType(), context);
            if (pair.Expected is CaptureParameterPattern expectedCapture)
            {
                var actualCapture = (CaptureParameterPattern)pair.Actual;
                Assert.True(expectedCapture.Parameter == actualCapture.Parameter, context);
                Assert.True(expectedCapture.Parameter.IsRecoveryPlaceholder == actualCapture.Parameter.IsRecoveryPlaceholder, context);
                continue;
            }

            var expectedItems = ParameterPattern.StructuralItems(pair.Expected)!;
            var actualItems = ParameterPattern.StructuralItems(pair.Actual)!;
            Assert.True(expectedItems.Count == actualItems.Count, context);
            Assert.True(ParameterPattern.GroupSource(pair.Expected) == ParameterPattern.GroupSource(pair.Actual), context);
            if (compareListTypes)
                Assert.True(expectedItems.GetType().FullName == actualItems.GetType().FullName, context);
            for (var index = 0; index < expectedItems.Count; index++)
                pending.Push((expectedItems[index], actualItems[index]));
        }
    }

    // Structural records per path, and how many of them are distinct objects.
    private static (int Occurrences, int Distinct) CountRecords(IReadOnlyList<ParameterPattern> patterns)
    {
        var occurrences = 0;
        var distinct = new HashSet<ParameterPattern>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<ParameterPattern>(patterns);
        while (pending.TryPop(out var pattern))
        {
            if (ParameterPattern.StructuralItems(pattern) is not { } items)
                continue;
            occurrences++;
            distinct.Add(pattern);
            foreach (var item in items)
                pending.Push(item);
        }

        return (occurrences, distinct.Count);
    }

    private static int CountDistinctGroups(Pattern head)
    {
        var distinct = new HashSet<Pattern>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Pattern>();
        pending.Push(head);
        while (pending.TryPop(out var pattern))
        {
            var items = pattern switch
            {
                Pattern.SequenceValue sequence => sequence.Items,
                Pattern.ListValue list => list.Items,
                _ => null,
            };
            if (items is null || !distinct.Add(pattern))
                continue;
            foreach (var item in items)
                pending.Push(item);
        }

        return distinct.Count;
    }
}
