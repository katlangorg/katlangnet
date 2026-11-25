namespace KatLang.Tests;

public sealed class StaticStructureBranchAgreementTests
{
    [Theory]
    [InlineData("P={open R\nR=h\nh}\nP(5)", "P", "h")]
    [InlineData("P={open R1,R2\nR1=h1\nR2=h2\nh1+h2}\nP(2,3)", "P", "h1,h2")]
    [InlineData("A=A.F\n0", "A", "F")]
    [InlineData("X={public h=P.N.A}\nP={open N.A\nN={open X\npublic A=h\n0}\nh}\n0", "P", "h")]
    [InlineData("R=B\nB={public h=S.R2\nR}\nS={open R,R2\npublic R2=C2\nC2={public g=7\nh}\nh+g}\nS(10)", "S", "h")]
    [InlineData("X={public h={public K=P.Z\npublic K2=7}}\nP={N={open X\npublic A=h\n0}\nW=N.A.K2\nZ=C\nC={public tv=1\nN.A.K}\nW.h+Z.tv}\n5", "P", "h")]
    public void SharedObservableFactsDoNotRequireASelectedIdentity(string source, string property, string expected)
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(source);
        foreach (var reverse in new[] { false, true })
        {
            var syntax = reverse ? root with { Properties = root.Properties.Reverse().ToArray() } : root;
            var queries = new StaticStructureQueries(syntax, new(2_000_000, 4, 200_000, 8_000_000));
            var body = queries.BodyIn(queries.Root, syntax.Properties.Single(p => p.Name == property).Value);
            var inputs = queries.Get(StaticQueryKey.Inputs(body));
            Assert.Equal(StaticFactKind.Inputs, inputs.Kind);
            Assert.Equal(expected.Split(','), Assert.IsType<string[]>(inputs.Data));
            Assert.True(queries.Statistics.AuxiliaryWork > 0);
        }
        var compiled = FrontEndPipeline.Process(source);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
    }

    [Theory]
    [InlineData("A.3.1")]
    [InlineData("A.3.2")]
    [InlineData("A.3.3a")]
    [InlineData("A.3.3b")]
    public void VaryingStructuralObservationsRemainSelfDependent(string witness)
    {
        var result = FrontEndPipeline.Process(StaticStructureWitnessSources.Cases[witness]);
        Assert.Contains(result.Diagnostics, d => d.Code == DiagnosticCode.SelfDependentInferredParameters);
    }

    [Fact]
    public void AnAmbiguousReceiverDoesNotAcquireAFallbackInput()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("open L,R\nL={public A=1}\nR={public A=2}\nP=A.M\n0");
        var queries = new StaticStructureQueries(raw, new(2_000_000, 4, 200_000, 8_000_000));
        var p = queries.BodyIn(queries.Root, raw.Properties.Single(p => p.Name == "P").Value);
        Assert.Equal(StaticFactKind.No, queries.Get(StaticQueryKey.IsInput(p, "M")).Kind);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void CallbackBoundsAreTerminalEvenWhenCaught(bool work)
    {
        var definition = new ChargedDefinition(work ? 3 : 1, work ? 0 : 1);
        var engine = new StaticQueryEngine<int, int>(definition, limits: new(work ? 2 : 100, 4, work ? 100 : 1, 100));
        Assert.Throws<StaticQueryLimitExceededException>(() => engine.Get(0));
        Assert.Throws<InvalidOperationException>(() => engine.Get(0));
    }

    [Fact]
    public void EmptyOpenLevelSharesOneCoverAcrossItsNames()
    {
        var small = Measure(16);
        var large = Measure(64);
        // Four times as many independent empty providers/names must not create their Cartesian product.
        Assert.True(large.Entries < 6 * small.Entries);
        Assert.True(large.Dependencies < 6 * small.Dependencies);
        Assert.True(large.AuxiliaryWork < 6 * small.AuxiliaryWork);

        static StaticQueryStatistics Measure(int width)
        {
            var source = "P={open " + string.Join(',', Enumerable.Range(0, width).Select(i => $"R{i}")) + "\n"
                + string.Join('\n', Enumerable.Range(0, width).Select(i => $"R{i}=h{i}")) + "\n"
                + string.Join('\n', Enumerable.Range(0, width).Select(i => $"h{i}")) + "}\n0";
            var raw = SourceProvenance.ParseSyntaxValidRoot(source);
            var queries = new StaticStructureQueries(raw, new(2_000_000, 4, 200_000, 8_000_000));
            var p = queries.BodyIn(queries.Root, raw.Properties.Single().Value);
            Assert.Equal(width, Assert.IsType<string[]>(queries.Get(StaticQueryKey.Inputs(p)).Data).Length);
            return queries.Statistics;
        }
    }

    private sealed class ChargedDefinition(int steps, int entries) : IStaticQueryDefinition<int, int>
    {
        public int Initial(int key) => 0;
        public int PathCycleValue => 0;
        public bool ValueEquals(int a, int b) => a == b;
        public bool IsRefinement(int a, int b) => a == 0 || a == b;
        public StaticQueryStep<int> Compute(int key, StaticQueryReader<int, int> reader)
        {
            try { for (var i = 0; i < steps; i++) reader.ChargeAuxiliary(entries); }
            catch (StaticQueryLimitExceededException) { }
            return StaticQueryStep.Complete(1);
        }
    }
}
