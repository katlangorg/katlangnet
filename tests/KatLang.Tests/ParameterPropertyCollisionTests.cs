namespace KatLang.Tests;

public class ParameterPropertyCollisionTests
{
    public static TheoryData<string, int, int, int, int> Conflicts => new()
    {
        { "Outer(v) = {\n    v = 5\n    Inner = v + 1\n    Inner + v\n}\nOuter(7)", 2, 5, 1, 7 },
        { "Outer(v) = {\n    Inner = v + 1\n    v = 5\n    Inner\n}\nOuter(7)", 3, 5, 1, 7 },
        { "Outer(v) = {\n    v = 5\n    v\n}\nOuter(7)", 2, 5, 1, 7 },
        { "Outer(v) = {\n    public v = 5\n    0\n}\n0", 2, 12, 1, 7 },
        { "Outer((v, w)) = {\n    v = 5\n    w\n}\n0", 2, 5, 1, 8 },
        { "Outer(*v) = {\n    v = 5\n    0\n}\n0", 2, 5, 1, 8 },
        { "Outer((q, *v)) = {\n    v = 5\n    0\n}\n0", 2, 5, 1, 12 },
        { "F(0) = 0\nF(v) = {\n    v = 5\n    0\n}\n0", 3, 5, 2, 3 },
        { "F((0, v)) = {\n    v = 5\n    0\n}\n0", 2, 5, 1, 7 },
        // A parameter of Need is lifted into Outer's COMPLETED signature.
        { "Need(v) = v\nOuter = {\n    v = 5\n    Need\n}\n0", 3, 5, 1, 6 },
        { "Need((v, w)) = v + w\nOuter = {\n    v = 5\n    Need\n}\n0", 3, 5, 1, 7 },
        { "Need(*v) = v.count\nOuter = {\n    v = 5\n    Need\n}\n0", 3, 5, 1, 7 },
        { "Need(v) = v\nv = 5\nNeed + 1", 2, 1, 1, 6 },
        // Hoisted deconstruction targets remain properties of the written owner.
        { "Outer(v) = {\n    v, w = 5, 6\n    w\n}\n0", 2, 5, 1, 7 },
        // A property cannot hide a completed parameter of ANY enclosing owner.
        { "Outer(v) = {\n    Inner = {\n        v = 5\n        v + 1\n    }\n    Inner\n}\nOuter(7)", 3, 9, 1, 7 },
        { "Outer(v) = {\n    Inner = {\n        Read = v\n        public v = 5\n        Read\n    }\n    Inner\n}\n0", 4, 16, 1, 7 },
        { "Outer((q, *v)) = {\n    Inner = {\n        v = 5\n        0\n    }\n    0\n}\n0", 3, 9, 1, 12 },
        { "F((0, v)) = {\n    Inner = {\n        v = 5\n        0\n    }\n    0\n}\n0", 3, 9, 1, 7 },
        { "Need(v) = v\nOuter = {\n    Inner = {\n        v = 5\n        v\n    }\n    Need + Inner\n}\n0", 4, 9, 1, 6 },
        // The nearest enclosing parameter supplies the related declaration location.
        { "Outer(v) = {\n    Mid(v) = {\n        Inner = { v = 5\n0 }\n0\n}\n0\n}\n0", 3, 19, 2, 9 },
    };

    [Theory]
    [MemberData(nameof(Conflicts))]
    public void CompletedOwnerCollision_IsOneDeclarationErrorAtTheProperty(
        string source, int line, int column, int parameterLine, int parameterColumn)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.ParameterPropertyCollision, diagnostic.Code);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(new SourceSpan(line, column, line, column), diagnostic.Span);
        Assert.Contains("Property 'v' conflicts with parameter 'v'", diagnostic.Message);
        Assert.Contains($"line {parameterLine}, column {parameterColumn}", diagnostic.Message);
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Equal(KatLangErrorCode.ParameterPropertyCollision, Assert.Single(failure.Errors).Code);
        Assert.Equal(parsed.Diagnostics, Parser.Parse(source).Diagnostics);
    }

    [Fact]
    public void InferredLift_PreservesGraceOrder_AndDoesNotInventADeclarationLocation()
    {
        const string source = "Need = a~ + v\nOuter = { v = 5\nNeed }\n0";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.ParameterPropertyCollision, diagnostic.Code);
        Assert.DoesNotContain("declared at", diagnostic.Message);
        var need = parsed.Root.Properties.Single(p => p.Name == "Need").Value;
        var outer = parsed.Root.Properties.Single(p => p.Name == "Outer").Value;
        Assert.Equal(["v", "a"], need.Params);
        Assert.Equal(need.Params, outer.Params);
    }

    [Fact]
    public void EachConflictingClauseHead_IsReportedEvenWithoutAnyReference()
    {
        const string source = "Outer(v) = {\nv(0) = 5\nv(n) = 6\n0\n}\n0";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.Equal([new SourceSpan(2, 1, 2, 1), new SourceSpan(3, 1, 3, 1)], parsed.Diagnostics.Select(d => d.Span));
        Assert.All(parsed.Diagnostics, d => Assert.Equal(DiagnosticCode.ParameterPropertyCollision, d.Code));
    }

    [Fact]
    public async Task CollisionPreventsEvaluationInSyncAndAsyncEngines()
    {
        var calls = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Touch", (_, _) =>
            {
                calls++;
                return new Result.Atom(1);
            })),
        };
        const string source = "Outer(v) = { Inner = { v = 5\nv }\nInner }\nTouch()\nOuter(7)";
        foreach (var result in new[] { KatLangEngine.Run(source, options), await KatLangEngine.RunAsync(source, options) })
            Assert.Equal(KatLangErrorCode.ParameterPropertyCollision,
                Assert.Single(Assert.IsType<RunResult.ParseFailure>(result).Errors).Code);
        Assert.Equal(0, calls);
    }

    [Fact]
    public void SharedBranchBody_ReportsEachDeclarationOnceAcrossBinderContexts()
    {
        var vSpan = new SourceSpan(2, 1, 2, 1);
        var qSpan = new SourceSpan(3, 1, 3, 1);
        var body = new Algorithm.User(null, [], [],
            [new Property("v", new Algorithm.User(null, [], [], [], [new Expr.Num(5)])) { DeclarationSpans = [vSpan] },
             new Property("q", new Algorithm.User(null, [], [], [], [new Expr.Num(6)])) { DeclarationSpans = [qSpan] }],
            [new Expr.Num(0)]);
        var family = new Algorithm.Conditional(null, [],
            [new CondBranch(new Pattern.Bind("v"), body), new CondBranch(new Pattern.Bind("q"), body), new CondBranch(new Pattern.Bind("v"), body)]);
        for (var run = 0; run < 2; run++)
        {
            var diagnostics = new List<Diagnostic>();
            new ParameterPropertyCollisionValidator(diagnostics).VisitAlgorithm(family);
            Assert.Equal([vSpan, qSpan], diagnostics.Select(d => d.Span));
            Assert.All(diagnostics, d => Assert.Equal(DiagnosticCode.ParameterPropertyCollision, d.Code));
        }
    }

    [Theory]
    [InlineData(32)]
    [InlineData(128)]
    public void SharedBranchBody_EquivalentBinderSetsDoNotRescanDeclarations(int width)
    {
        var value = new Algorithm.User(null, [], [], [], [new Expr.Num(5)]);
        var properties = new ObservedProperties(Enumerable.Range(0, width).Select(i =>
            new Property($"p{i}", value) { DeclarationSpans = [new SourceSpan(i + 1, 1, i + 1, 1)] }).ToArray());
        var body = new Algorithm.User(null, [], [], properties, [new Expr.Num(0)]);
        // Distinct pattern objects and binder order, but the SAME semantic input.
        var branches = Enumerable.Range(0, width).Select(i => new CondBranch(
            new Pattern.SequenceValue(i % 2 == 0
                ? [new Pattern.Bind("p0"), new Pattern.Bind("p1")]
                : [new Pattern.Bind("p1"), new Pattern.Bind("p0")]), body)).ToList();
        branches.Add(new CondBranch(new Pattern.Bind("p2"), body));
        var diagnostics = new List<Diagnostic>();
        new ParameterPropertyCollisionValidator(diagnostics).VisitAlgorithm(new Algorithm.Conditional(null, [], branches));

        Assert.Equal([1, 2, 3], diagnostics.Select(d => d.Span!.StartLineNumber));
        Assert.All(diagnostics, d => Assert.Equal(DiagnosticCode.ParameterPropertyCollision, d.Code));
        Assert.InRange(properties.Reads, width, 5 * width);
    }

    [Fact]
    public void SharedNestedExpression_IsValidatedInEachAncestorContext_WithoutSiblingLeakage()
    {
        var span = new SourceSpan(3, 1, 3, 1);
        var parameterSpan = new SourceSpan(1, 7, 1, 7);
        var value = new Algorithm.User(null, [], [], [], [new Expr.Num(5)]);
        var body = new Algorithm.User(null, [], [], [new Property("v", value) { DeclarationSpans = [span] }], [new Expr.Num(0)]);
        var shared = new Expr.Capture(new OutputBundle([new Expr.AlgorithmExpr(body)]));
        var withoutV = new Algorithm.User(null, [new ParameterDeclaration("q")], [], [], [shared]);
        var withV = new Algorithm.User(null, [new ParameterDeclaration("v", parameterSpan)], [], [], [shared]);
        foreach (var owners in new[] { new[] { withoutV, withV }, new[] { withV, withoutV } })
        {
            var diagnostics = new List<Diagnostic>();
            var root = new Algorithm.User(null, [], [], [], new OutputBundle(owners.Select(a => (Expr)new Expr.AlgorithmExpr(a)).ToArray()));
            new ParameterPropertyCollisionValidator(diagnostics).VisitAlgorithm(root);
            var diagnostic = Assert.Single(diagnostics);
            Assert.Same(span, diagnostic.Span);
            Assert.Contains("line 1, column 7", diagnostic.Message);
        }
        var isolated = new List<Diagnostic>();
        new ParameterPropertyCollisionValidator(isolated).VisitAlgorithm(withoutV);
        Assert.Empty(isolated);
    }

    [Theory]
    [InlineData(32)]
    [InlineData(128)]
    public void SharedCompletedSignature_IsReadOncePerEnclosingContext(int width)
    {
        var parameters = new ObservedParameters(Enumerable.Range(0, width)
            .Select(i => new ParameterDeclaration($"p{i}")).ToArray());
        var children = Enumerable.Range(0, width).Select(_ => (Expr)new Expr.AlgorithmExpr(
            new Algorithm.User(null, parameters, [], [], [new Expr.Num(0)]))).ToArray();
        parameters.Reads = 0; // Ignore AST construction; observe the validator itself.
        var diagnostics = new List<Diagnostic>();
        new ParameterPropertyCollisionValidator(diagnostics).VisitAlgorithm(new Algorithm.User(null, [], [], [], new OutputBundle(children)));
        Assert.Empty(diagnostics);
        Assert.InRange(parameters.Reads, width, 2 * width);
    }

    private sealed class ObservedParameters(IReadOnlyList<ParameterDeclaration> parameters) : IReadOnlyList<ParameterDeclaration>
    {
        public int Reads { get; set; }
        public int Count => parameters.Count;
        public ParameterDeclaration this[int index] { get { Reads++; return parameters[index]; } }
        public IEnumerator<ParameterDeclaration> GetEnumerator()
        {
            for (var i = 0; i < Count; i++)
                yield return this[i];
        }
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    private sealed class ObservedProperties(IReadOnlyList<Property> properties) : IReadOnlyList<Property>
    {
        public int Reads { get; private set; }
        public int Count => properties.Count;
        public Property this[int index] { get { Reads++; return properties[index]; } }
        public IEnumerator<Property> GetEnumerator()
        {
            for (var i = 0; i < Count; i++)
                yield return this[i];
        }
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    [Theory]
    [InlineData("v = 99\nOuter(v) = { Inner = v + 1\nInner }\nOuter(7)", "8")]
    [InlineData("Lib = { public v = 99 }\nOuter(v) = { open Lib\nv + 1 }\nOuter(7)", "8")]
    [InlineData("Outer(pi) = pi + 1\nOuter(7)", "8")]
    [InlineData("Outer = { v = 5\nv + 1 }\nOuter", "6")]
    [InlineData("Outer(v) = { Inner = { w = 5\nw + v }\nInner }\nOuter(7)", "12")]
    [InlineData("Outer(v) = v\nOther = { v = 5\nv }\nOther", "5")]
    [InlineData("F(0) = { v = 5\nv }\nF(v) = v\nF(0)", "5")]
    [InlineData("Outer(v) = { open { public v = 99 }\nv + 1 }\nOuter(7)", "8")]
    public void AncestorPropertiesSiblingParametersAndImportsRemainLegal(string source, string expected)
    {
        _ = SourceProvenance.ParseValid(source);
        Assert.Equal(expected, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }
}
