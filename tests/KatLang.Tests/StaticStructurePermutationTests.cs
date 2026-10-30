namespace KatLang.Tests;

public sealed class StaticStructurePermutationTests
{
    [Fact]
    public void RandomizedPublicQueryDemands_AgreeAcrossRealWitnesses()
    {
        var sources = StaticStructureWitnessSources.Cases.Values.Concat(new[]
        {
            "F(v)=0\nK(v)=7\nA=A.F\nP=A.x\nP(K)",
            "F(v)=0\nA=B.F\nB=A\n0",
            "F(v)=0\nBox={ public C=A.F\n0 }\nA=Box.C\n0",
            "A=A.Algorithm\nB=A\n0",
        });
        var random = new Random(0xB320);
        foreach (var source in sources)
        {
            var root = SourceProvenance.ParseSyntaxValidRoot(source);
            var declarations = new Dictionary<object, int>(ReferenceEqualityComparer.Instance);
            string[]? expected = null;
            for (var profile = 0; profile < 32; profile++)
            {
                var q = new StaticStructureQueries(root, new(1_000_000, 4, 100_000, 4_000_000));
                var requests = Requests(q);
                foreach (var index in Enumerable.Range(0, requests.Count).OrderBy(_ => random.Next())) q.Get(requests[index]);
                var actual = requests.Select(key => Describe(q, q.Get(key), declarations)).ToArray();
                if (expected is not null) Assert.Equal(expected, actual);
                expected = actual;
            }
        }
    }

    private static List<StaticQueryKey> Requests(StaticStructureQueries q)
    {
        var result = new List<StaticQueryKey>();
        var seen = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<StaticScopeKey>();
        pending.Push(q.Root);
        while (pending.TryPop(out var scope))
        {
            if (!seen.Add(scope)) continue;
            var body = q.BodyOf(scope);
            result.Add(StaticQueryKey.Members(scope));
            result.Add(StaticQueryKey.Inputs(scope));
            foreach (var stratum in Enum.GetValues<StaticCycleCheck>())
            {
                result.Add(StaticQueryKey.TargetWalk(scope, stratum));
                result.Add(StaticQueryKey.OpenProviders(scope, stratum));
            }
            foreach (var property in body.Properties.Reverse()) pending.Push(q.BodyIn(scope, property.Value));
            if (body is not Algorithm.User user) continue;
            var syntax = new StaticInputGraph(AstHelpers.WrittenRows(user));
            foreach (var name in syntax.Names)
            {
                result.Add(StaticQueryKey.IsInput(scope, name));
                foreach (var stratum in Enum.GetValues<StaticCycleCheck>()) result.Add(StaticQueryKey.Binding(scope, name, stratum));
            }
            foreach (var expression in syntax.Nodes.Keys)
            {
                if (expression is Expr.DotCall edge) result.Add(StaticQueryKey.MissSelection(scope, edge));
                if (expression is Expr.AlgorithmExpr(var block)) pending.Push(q.BodyIn(scope, block));
            }
        }
        return result;
    }

    private static string Describe(StaticStructureQueries q, StaticFact fact, Dictionary<object, int> ids)
    {
        string Scope(StaticScopeKey scope)
        {
            if (ReferenceEquals(scope, q.Keys.Root)) return "$prelude";
            var parent = scope.Parent!;
            var body = q.BodyOf(scope);
            // Raw witness declarations are shared across profiles. Prelude declarations may be fresh objects,
            // so name their stable prelude binding rather than their allocation identity.
            if (ReferenceEquals(parent, q.Keys.Root))
            {
                var predefined = q.BodyOf(parent).Properties.FirstOrDefault(p => ReferenceEquals(p.Value, body));
                if (predefined is not null) return "$prelude." + predefined.Name;
            }
            if (!ids.TryGetValue(scope.Declaration, out var id)) ids.Add(scope.Declaration, id = ids.Count);
            return Scope(parent) + "/" + id;
        }
        return fact.Kind + ":" + (fact.Scope is { } scope ? Scope(scope) : "") + ":" + fact.Property?.Name + ":" + (fact.Data switch
        {
            string[] names => string.Join(',', names),
            StaticScopeKey[] providers => string.Join(',', providers.Select(Scope)),
            _ => "",
        });
    }
}
