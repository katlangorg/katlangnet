namespace KatLang.Tests;

/// <summary>
/// FE-1 exactness of deferred near-miss suggestions: <see cref="SuggestionContexts"/> derives each
/// promotion's candidate set incrementally — per parameter map and per scope level, with open
/// providers folded in level by level — instead of re-collecting and re-resolving every visible name
/// per promotion. These tests compare that derivation against a VERBATIM copy of the collector it
/// replaced (the per-name authoritative lookups <see cref="ElaboratedScopeLookup.TryLookupDirectLexicalProperty"/>
/// and <see cref="ElaboratedScopeLookup.LookupOpenPropertyMatches"/> over every potential spelling),
/// over written programs and over generated scope trees with shadowing, private members, single,
/// duplicate, ambiguous, nested, and unresolvable opens, unsuggestible spellings, and the work bound
/// on both sides of its edge. Equal candidate sets (and equal refusals) make every suggestion equal,
/// because the unchanged selection is the unique closest candidate whatever the enumeration order.
/// </summary>
public class SuggestionContextDifferentialTests
{
    private const int MaxNameLength = NameSuggestions.MaxNameLength;
    private const int MaxCandidates = NameSuggestions.MaxCandidates;

    // ── The replaced collector, verbatim in behavior ──────────────────────────

    private static bool LegacyTryAddCandidate(HashSet<string> candidates, string candidate)
    {
        if (candidate.Length == 0 || candidate.Length > MaxNameLength)
            return true;
        if (candidates.Contains(candidate))
            return true;
        if (candidates.Count >= MaxCandidates)
            return false;
        candidates.Add(candidate);
        return true;
    }

    /// <summary>The legacy lexical candidates, or null when the work bound refused the suggestion.</summary>
    private static HashSet<string>? LegacyLexicalCandidates(ElaboratedPropertyScope scope, ParameterOwnership parameters)
    {
        var candidates = new HashSet<string>(StringComparer.Ordinal);
        foreach (var boundName in parameters.Names)
        {
            if (!LegacyTryAddCandidate(candidates, boundName))
                return null;
        }

        var names = new HashSet<string>(candidates, StringComparer.Ordinal);
        bool AddPotential(string name)
        {
            if (name.Length == 0 || name.Length > MaxNameLength || names.Contains(name))
                return true;
            if (names.Count >= MaxCandidates)
                return false;
            names.Add(name);
            return true;
        }

        for (var current = scope; current is not null; current = current.Parent)
        {
            foreach (var hit in current.Properties)
            {
                if (!AddPotential(hit.Property.Name))
                    return null;
            }

            foreach (var provider in current.GetResolvedOpenProviders())
            {
                foreach (var property in provider.Target.Properties)
                {
                    if (property.IsPublic && !AddPotential(property.Name))
                        return null;
                }
            }
        }

        foreach (var name in names)
        {
            var resolves = ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, name) is not null
                || ElaboratedScopeLookup.LookupOpenPropertyMatches(scope, name).Count == 1;
            if (resolves && !LegacyTryAddCandidate(candidates, name))
                return null;
        }

        return candidates;
    }

    /// <summary>The legacy receiver-member candidates in first-occurrence order, or null when the work bound refused them.</summary>
    private static List<string>? LegacyMemberCandidates(Algorithm receiver)
    {
        var candidates = new Dictionary<string, Property>(StringComparer.Ordinal);
        var order = new List<string>();
        foreach (var property in receiver.Properties)
        {
            if (property.Name.Length == 0 || property.Name.Length > MaxNameLength)
                continue;
            if (candidates.Count >= MaxCandidates)
                return null;
            if (candidates.TryAdd(property.Name, property))
                order.Add(property.Name);
        }

        return order;
    }

    // ── Comparison ─────────────────────────────────────────────────────────────

    private static readonly string[] ProbeNames = ["zz", "Alpah", "alpha", "Bta", "cnt", "Count", "vaule", "q1", "abcdefgh", "Math"];

    private static void AssertLexicalAgreement(SuggestionContexts contexts, ElaboratedPropertyScope scope, ParameterOwnership parameters, string where)
    {
        var legacy = LegacyLexicalCandidates(scope, parameters);
        foreach (var probe in ProbeNames)
        {
            var captured = contexts.Capture(probe, scope, parameters, receiver: null);
            if (legacy is null || legacy.Count == 0)
            {
                Assert.True(captured is null, $"{where}: expected no context for '{probe}', legacy {(legacy is null ? "refused" : "had no candidate")}");
                continue;
            }

            var query = Assert.IsType<LexicalSuggestionQuery>(captured);
            var derived = query.Candidates.Names.ToHashSet(StringComparer.Ordinal);
            Assert.True(
                legacy.SetEquals(derived),
                $"{where}: candidate sets differ; legacy-only [{string.Join(", ", legacy.Except(derived))}], derived-only [{string.Join(", ", derived.Except(legacy))}]");
            Assert.Equal(legacy.Count, query.Candidates.Count);

            // The selection is the unique closest candidate: the legacy enumeration order and the
            // interner's order agree, and so does the deferred evaluation.
            var expected = NameSuggestions.SelectLexicalName(probe, legacy, observations: null)?.EligibleName;
            Assert.Equal(expected, query.Evaluate()?.EligibleName);
        }

        Assert.Null(contexts.Capture(string.Empty, scope, parameters, receiver: null));
        Assert.Null(contexts.Capture(new string('z', MaxNameLength + 1), scope, parameters, receiver: null));
    }

    private static void AssertMemberAgreement(SuggestionContexts contexts, Algorithm receiver, ElaboratedPropertyScope scope, string where)
    {
        var dotReceiver = new DotMemberReceiver(receiver, "R");
        foreach (var probe in ProbeNames)
        {
            var captured = contexts.Capture(probe, scope, ParameterOwnership.Empty, dotReceiver);
            if (receiver.Properties.Count == 0)
            {
                // A memberless receiver is answered lexically, exactly like a bare name.
                var lexical = contexts.Capture(probe, scope, ParameterOwnership.Empty, receiver: null);
                Assert.Equal(lexical?.Evaluate()?.EligibleName, captured?.Evaluate()?.EligibleName);
                continue;
            }

            var legacy = LegacyMemberCandidates(receiver);
            if (legacy is null || legacy.Count == 0)
            {
                Assert.True(captured is null, $"{where}: expected no member context for '{probe}'");
                continue;
            }

            var query = Assert.IsType<ReceiverMemberSuggestionQuery>(captured);
            Assert.Equal(legacy, query.Members);
            var expected = NameSuggestions.SelectReceiverMember(probe, legacy, "R", observations: null)?.EligibleName;
            Assert.Equal(expected, query.Evaluate()?.EligibleName);
        }
    }

    // ── Scope trees ────────────────────────────────────────────────────────────

    private static ElaboratedPropertyScope PreludeScope()
        => ElaboratedScopeLookup.CreateScope(BuiltinRegistry.CreateSemanticPreludeAlgorithm());

    /// <summary>Every algorithm reachable through property values and written blocks, with its scope.</summary>
    private static List<(Algorithm Algorithm, ElaboratedPropertyScope Scope)> Scopes(Algorithm root, ElaboratedPropertyScope parent)
    {
        var scopes = new List<(Algorithm, ElaboratedPropertyScope)>();
        var pending = new Stack<(Algorithm Algorithm, ElaboratedPropertyScope Parent)>();
        pending.Push((root, parent));
        while (pending.TryPop(out var entry))
        {
            var scope = ElaboratedScopeLookup.CreateScope(entry.Algorithm, entry.Parent);
            scopes.Add((entry.Algorithm, scope));
            foreach (var property in entry.Algorithm.Properties)
                pending.Push((property.Value, scope));
            foreach (var row in entry.Algorithm.Output)
            {
                if (row is Expr.AlgorithmExpr { Algorithm: var block })
                    pending.Push((block, scope));
            }

            foreach (var open in entry.Algorithm.Opens)
            {
                if (open is Expr.AlgorithmExpr { Algorithm: var inline })
                    pending.Push((inline, scope));
            }
        }

        return scopes;
    }

    private static void AssertProgramAgreement(Algorithm root, Random random, string where)
    {
        // One capture instance per program, visited in a shuffled order, so each derivation is
        // exercised both from memoized ancestors and ahead of them.
        var contexts = new SuggestionContexts();
        var scopes = Scopes(root, PreludeScope());
        random.Shuffle(System.Runtime.InteropServices.CollectionsMarshal.AsSpan(scopes));
        var maps = new List<ParameterOwnership> { ParameterOwnership.Empty };
        foreach (var (algorithm, scope) in scopes)
        {
            // Parameter maps extend one another by a few names, as the owner walk's maps do.
            var parentMap = maps[random.Next(maps.Count)];
            var map = parentMap.Extend(scope, Enumerable.Range(0, random.Next(3)).Select(_ => Pool[random.Next(Pool.Length)]));
            maps.Add(map);

            AssertLexicalAgreement(contexts, scope, map, where);
            AssertLexicalAgreement(contexts, scope, ParameterOwnership.Empty, where);
            AssertMemberAgreement(contexts, algorithm, scope, where);
        }
    }

    [Theory]
    [InlineData("Lib = { public Alpha = 1\npublic Beta = 2\nGamma = 3 }\nUse = { open Lib\nAlpha + Beta }\nUse")]
    [InlineData("A = { public X = 1\npublic Shared = 2 }\nB = { public Y = 1\npublic Shared = 3 }\nUse = { open A, B\nX + Y }\nUse")]
    [InlineData("A = { public Shared = 1 }\nUse = { open A, A\nShared }\nUse")]
    [InlineData("A = { public X = 1 }\nB = { public X = 2 }\nOuter = { open A\nInner = { open B\nX }\nInner }\nOuter")]
    // An inner level where two providers supply `X` decides it — ambiguous — even though an outer
    // level supplies it uniquely; and an inner unique provider decides over an outer ambiguity.
    [InlineData("A = { public X = 1 }\nB = { public X = 2 }\nC = { public X = 3 }\nOuter = { open A\nInner = { open B, C\n1 }\nInner }\nOuter")]
    [InlineData("A = { public X = 1 }\nB = { public X = 2 }\nC = { public X = 3 }\nOuter = { open B, C\nInner = { open A\n1 }\nInner }\nOuter")]
    [InlineData("A = { public X = 1 }\nX = 5\nUse = { open A\nX }\nUse")]
    [InlineData("Use = { open { public Alpha = 1 }, { public Alpha = 2 }\n1 }\nUse")]
    [InlineData("Use = { open Math\nPi + sin(1) }\nUse")]
    [InlineData("F(alpha, beta) = { G = { Alpha = alpha\nAlpha + beta }\nG }\nF(1, 2)")]
    [InlineData("Count = 1\nL = { public count = 2 }\nU = { open L\ncount }\nU + Count")]
    public void WrittenPrograms_DerivedCandidatesMatchTheReplacedCollector(string source)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        AssertProgramAgreement(root, new Random(source.Length), source);
    }

    private static readonly string[] Pool =
    [
        "a", "A", "b", "ab", "Ab", "aB", "abc", "abd", "acb", "Alpha", "alpha", "Alpah", "Beta", "beta", "Bta",
        "count", "Count", "cnt", "sum", "Sum", "value", "Value", "vaule", "q1", "q2", "Q1", "x", "y", "Shared",
        "abcdefgh", "abcdefgj", "bacdefgh", "Math", "math", "if", "If", new string('L', MaxNameLength), new string('L', MaxNameLength + 1),
    ];

    private static Algorithm.User GenerateAlgorithm(Random random, int depth, List<string> siblings)
    {
        var properties = new List<Property>();
        var names = new List<string>();
        for (var index = random.Next(5); index > 0; index--)
        {
            var name = Pool[random.Next(Pool.Length)];
            names.Add(name);
            var value = depth > 0 && random.Next(3) == 0
                ? GenerateAlgorithm(random, depth - 1, names)
                : new Algorithm.User(null, [], [], [], new OutputBundle([new Expr.Num(1)]));
            properties.Add(new Property(name, value, IsPublic: random.Next(3) != 0));
        }

        var opens = new List<Expr>();
        for (var index = random.Next(3); index > 0; index--)
        {
            opens.Add(random.Next(4) switch
            {
                0 when depth > 0 => new Expr.AlgorithmExpr(GenerateAlgorithm(random, depth - 1, [])),
                1 => new Expr.Resolve(Pool[random.Next(Pool.Length)]),
                _ when siblings.Count > 0 => new Expr.Resolve(siblings[random.Next(siblings.Count)]),
                _ => new Expr.Resolve(names.Count > 0 ? names[random.Next(names.Count)] : "Missing"),
            });
        }

        var output = new List<Expr> { new Expr.Num(1) };
        if (depth > 0 && random.Next(2) == 0)
            output.Add(new Expr.AlgorithmExpr(GenerateAlgorithm(random, depth - 1, names)));

        return new Algorithm.User(null, [], opens, properties, new OutputBundle(output));
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(5)]
    [InlineData(8)]
    [InlineData(13)]
    [InlineData(21)]
    [InlineData(34)]
    public void GeneratedScopeTrees_DerivedCandidatesMatchTheReplacedCollector(int seed)
    {
        var random = new Random(seed);
        for (var program = 0; program < 25; program++)
        {
            var root = GenerateAlgorithm(random, depth: 4, []);
            AssertProgramAgreement(root, random, $"seed {seed}, program {program}");
        }
    }

    /// <summary>
    /// The work bound on both sides of its edge, split every way between bound parameter names,
    /// own properties, enclosing properties, and opened members: exactly 512 distinct suggestible
    /// names still yield a context; 513 refuse it, whichever sets contribute them.
    /// </summary>
    [Theory]
    [InlineData(512, 0, 0, 0)]
    [InlineData(513, 0, 0, 0)]
    [InlineData(0, 512, 0, 0)]
    [InlineData(0, 513, 0, 0)]
    [InlineData(200, 200, 112, 0)]
    [InlineData(200, 200, 113, 0)]
    [InlineData(100, 100, 100, 211)]
    [InlineData(100, 100, 100, 212)]
    [InlineData(300, 0, 0, 211)]
    [InlineData(300, 0, 0, 212)]
    public void WorkBound_IsExactWhateverContributesTheNames(int bound, int own, int enclosing, int opened)
    {
        static Property Leaf(string name, bool isPublic = false)
            => new(name, new Algorithm.User(null, [], [], [], new OutputBundle([new Expr.Num(1)])), isPublic);

        var library = new Algorithm.User(null, [], [], [.. Enumerable.Range(0, opened).Select(i => Leaf($"o{i}", isPublic: true))], OutputBundle.Empty);
        var outer = new Algorithm.User(
            null, [], [],
            [.. Enumerable.Range(0, enclosing).Select(i => Leaf($"e{i}")), .. opened > 0 ? [new Property("Lib", library)] : Array.Empty<Property>()],
            OutputBundle.Empty);
        var inner = new Algorithm.User(null, [], opened > 0 ? [new Expr.Resolve("Lib")] : [], [.. Enumerable.Range(0, own).Select(i => Leaf($"p{i}"))], OutputBundle.Empty);

        // An empty outermost level in place of the prelude keeps the arithmetic exact.
        var outerScope = ElaboratedScopeLookup.CreateScope(outer, ElaboratedScopeLookup.CreateScope(new Algorithm.User(null, [], [], [], OutputBundle.Empty)));
        var innerScope = ElaboratedScopeLookup.CreateScope(inner, outerScope);
        var parameters = ParameterOwnership.Empty.Extend(innerScope, Enumerable.Range(0, bound).Select(i => $"b{i}"));

        // `Lib`, the opened library's holder, is one more enclosing name.
        var total = bound + own + enclosing + (opened > 0 ? 1 + opened : 0);
        var contexts = new SuggestionContexts();
        AssertLexicalAgreement(contexts, innerScope, parameters, $"bound {bound}, own {own}, enclosing {enclosing}, opened {opened}");
        Assert.Equal(total <= MaxCandidates && total > 0, contexts.Capture("zz", innerScope, parameters, receiver: null) is not null);
    }

    [Theory]
    [InlineData(511)]
    [InlineData(512)]
    [InlineData(513)]
    public void ReceiverMemberBound_IsExact_AndCountsDeclarationsPastTheEdge(int members)
    {
        // Duplicates and unsuggestible spellings around the edge: the legacy rule refuses once a
        // suggestible declaration remains after 512 distinct members were collected.
        var properties = Enumerable.Range(0, members)
            .Select(i => new Property($"m{i}", new Algorithm.User(null, [], [], [], OutputBundle.Empty)))
            .Append(new Property("m0", new Algorithm.User(null, [], [], [], OutputBundle.Empty)))
            .Append(new Property(new string('m', MaxNameLength + 1), new Algorithm.User(null, [], [], [], OutputBundle.Empty)))
            .ToList();
        var receiver = new Algorithm.User(null, [], [], properties, OutputBundle.Empty);

        AssertMemberAgreement(new SuggestionContexts(), receiver, PreludeScope(), $"{members} members");
    }
}
