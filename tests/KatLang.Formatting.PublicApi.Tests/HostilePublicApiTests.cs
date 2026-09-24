using System.Numerics;
using System.Reflection;
using System.Text;
using System.Xml.Linq;
using KatLang.Semantics;

namespace KatLang.Formatting.PublicApi.Tests;

public class HostilePublicApiTests
{
    [Theory]
    [InlineData(typeof(RunResult.Success))]
    [InlineData(typeof(RunResult.NoProgramOutput))]
    [InlineData(typeof(RunResult.ParseFailure))]
    [InlineData(typeof(RunResult.EvalFailure))]
    [InlineData(typeof(ParseResult))]
    public void ProducedResults_CannotBeConstructedOrRewrittenExternally(Type type)
    {
        Assert.Empty(type.GetConstructors());
        Assert.All(type.GetProperties(), property => Assert.False(property.SetMethod?.IsPublic == true,
            $"{type.Name}.{property.Name} can contradict the other engine-produced payloads."));
    }

    [Theory]
    [InlineData("DisplayDecimals = -1\n1", 100)]
    [InlineData("A = [1, 2]\n[A, A]", 3)]
    public async Task EveryEngineFailurePath_PublishesReadOnlyErrors(string source, int maxItems)
    {
        var options = new RunOptions { EvaluationLimits = new() { MaxCollectionItems = maxItems } };
        foreach (var run in new[] { KatLangEngine.Run(source, options), await KatLangEngine.RunAsync(source, options) })
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(run);
            var expectedCode = source.StartsWith("DisplayDecimals", StringComparison.Ordinal)
                ? KatLangErrorCode.IllegalInEval : KatLangErrorCode.CollectionSizeLimitExceeded;
            Assert.Equal(expectedCode, Assert.Single(failure.Errors).Code);
            RejectMutation(failure.Errors);
        }
    }

    [Fact]
    public void OutputBundles_RejectNullCollectionsAndSlotsOnEveryConstructionPath()
    {
        Assert.Equal("items", Assert.Throws<ArgumentNullException>(() => new OutputBundle(null!)).ParamName);
        Assert.Equal("items", Assert.Throws<ArgumentNullException>(() => OutputBundle.From(null!)).ParamName);
        Assert.Equal("items", Assert.Throws<ArgumentNullException>(() => { OutputBundle b = (Expr[])null!; }).ParamName);
        Assert.Equal("items", Assert.Throws<ArgumentException>(() => new OutputBundle(new Expr[] { null! })).ParamName);
        Assert.Equal("items", Assert.Throws<ArgumentException>(() => OutputBundle.Create(new Expr[] { null! })).ParamName);
        Assert.Equal("items", Assert.Throws<ArgumentException>(() => { OutputBundle b = new Expr[] { null! }; }).ParamName);
    }

    [Theory]
    [InlineData(0, 1, 1, 1, "startLine")]
    [InlineData(1, 0, 1, 1, "startColumn")]
    [InlineData(1, 1, 0, 1, "endLine")]
    [InlineData(1, 1, 1, 0, "endColumn")]
    [InlineData(2, 1, 1, 1, "endLine")]
    [InlineData(1, 2, 1, 1, "endColumn")]
    public void SourceSpan_ReportsItsOwnParameter(int sl, int sc, int el, int ec, string parameter)
        => Assert.Equal(parameter, Assert.Throws<ArgumentOutOfRangeException>(() => new SourceSpan(sl, sc, el, ec)).ParamName);

    [Fact]
    public void SemanticBuilder_ReportsItsPublicRootParameter()
    {
        Expr expr = new Expr.Num(1);
        for (var i = 0; i < EvaluationLimits.MaxSupportedAstDepth + 2; i++)
            expr = new Expr.Unary(UnaryOp.Minus, expr);
        var root = new Algorithm.User(null, [], [], [], [expr]);
        Assert.Equal("root", Assert.Throws<ArgumentException>(() => SemanticModelBuilder.Build(root)).ParamName);
    }

    [Fact]
    public void CompatibilityOnlySurface_IsAbsent()
    {
        Assert.Null(typeof(ErrorContext).GetMethod("ToLegacyString"));
        Assert.DoesNotContain(typeof(ScopeCtx).GetMethods(), m => m.Name == "Deconstruct" && m.GetParameters().Length == 3);
        Assert.DoesNotContain("LoadedExternalMemberReference", Enum.GetNames<IdentifierClassification>());
        Assert.Equal("while evaluating property A", new PropertyEvaluationContext("A").ToString());
    }

    [Fact]
    public async Task SharedOptions_KeepRunStateSeparateAcrossSuspendedCalls()
    {
        var gate = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var entered = 0;
        var operations = HostOperations.Create(HostOperation.CreateAsync("Wait", async (_, token) =>
        {
            Interlocked.Increment(ref entered);
            await gate.Task.WaitAsync(token);
            return new Result.Bool(true);
        }));
        var options = new RunOptions { HostOperations = operations, RandomSeed = 42, DefaultDisplayDecimals = 2 };
        const string source = "Wait(), Math.RandomInt(1, 1000), 1 / 7";
        var tasks = Enumerable.Range(0, 12).Select(_ => KatLangEngine.RunAsync(source, options)).ToArray();
        Assert.Equal(tasks.Length, entered);
        Assert.All(tasks, t => Assert.False(t.IsCompleted));
        gate.SetResult();
        var runs = await Task.WhenAll(tasks);
        var expected = Assert.IsType<RunResult.Success>(runs[0]).ToDisplayString();
        Assert.All(runs, run => Assert.Equal(expected, Assert.IsType<RunResult.Success>(run).ToDisplayString()));
        Assert.EndsWith("0.14", expected, StringComparison.Ordinal);
        Assert.Equal("0.142857", (await KatLangEngine.RunAsync("DisplayDecimals = 6\n1 / 7", options)).ToDisplayString());
        Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync("1 / 0", options));
        Assert.Equal(expected, (await KatLangEngine.RunAsync(source, options)).ToDisplayString());
    }

    [Fact]
    public void AllowedHosts_EnumeratesOnceAtInitializationAndKeepsAnUnnormalizedSnapshot()
    {
        var enumerations = 0;
        IEnumerable<string> Hosts()
        {
            enumerations++;
            yield return "  EXAMPLE.ORG  ";
        }
        var options = new RunOptions { AllowedHosts = Hosts() };
        Assert.Equal(1, enumerations);
        Assert.Equal("  EXAMPLE.ORG  ", Assert.Single(options.AllowedHosts!));
        Assert.IsType<RunResult.Success>(KatLangEngine.Run("1", options));
        Assert.IsType<RunResult.Success>(KatLangEngine.Run("1", options));
        Assert.Equal(1, enumerations);
        RejectMutation(Assert.IsAssignableFrom<IReadOnlyList<string>>(options.AllowedHosts));
        var invalid = new RunOptions { AllowedHosts = new[] { (string)null! } };
        Assert.Throws<ArgumentException>(() => KatLangEngine.Run("1", invalid));
    }

    [Fact]
    public void EqualityAndHashing_HaveSeparateRepresentationAndValueContracts()
    {
        foreach (var (x, y) in new[] { ("NaN", "NaN"), ("0", "-0"), ("1.5", "1.50") })
        {
            Result a = new Result.Atom(Decimal128.Parse(x, System.Globalization.CultureInfo.InvariantCulture));
            Result b = new Result.Atom(Decimal128.Parse(y, System.Globalization.CultureInfo.InvariantCulture));
            Assert.Equal(a, b);
            Assert.Equal(a.GetHashCode(), b.GetHashCode());
            foreach (var pair in new[] { (a, b), (new Result.ListValue([a]), (Result)new Result.ListValue([b])),
                (new Result.SequenceValue([new Result.ListValue([a])]), (Result)new Result.SequenceValue([new Result.ListValue([b])])) })
            {
                Assert.True(Result.ValueComparer.Equals(pair.Item1, pair.Item2));
                Assert.Equal(Result.ValueComparer.GetHashCode(pair.Item1), Result.ValueComparer.GetHashCode(pair.Item2));
            }
        }
        var list = new Result.ListValue([new Result.Atom(1)]);
        Assert.NotEqual(list, new Result.ListValue([new Result.Atom(1)]));
        Assert.Equal(list, list with { });
        Assert.Equal(list.GetHashCode(), (list with { }).GetHashCode());
    }

    private static void RejectMutation<T>(IReadOnlyList<T> values)
    {
        Assert.NotEmpty(values);
        if (values is IList<T> list)
            Assert.Throws<NotSupportedException>(() => list[0] = list[0]);
        if (values is System.Collections.IList untyped)
            Assert.Throws<NotSupportedException>(() => untyped[0] = untyped[0]);
    }

    [Fact]
    public void LexicalAndSemanticQueries_PublishReadOnlyCollections()
    {
        var (tokens, diagnostics) = Lexer.Tokenize("A @= 1\nA");
        RejectMutation(tokens);
        RejectMutation(diagnostics);
        var model = SemanticModelBuilder.Build(Parser.Parse("A = 1\nA"));
        RejectMutation(model.FindDeclarations("A"));
        RejectMutation(model.FindResolutions("A"));
        RejectMutation(model.FindProperties("A"));
        RejectMutation(model.GetVisibleSymbolsAt(new SourcePosition(2, 1)));
        Assert.Equal("name", Assert.Throws<ArgumentNullException>(() => model.FindResolutions(null!)).ParamName);
        Assert.Equal("name", Assert.Throws<ArgumentNullException>(() => model.FindDeclarations(null!)).ParamName);
        Assert.Equal("name", Assert.Throws<ArgumentNullException>(() => model.FindProperties(null!)).ParamName);
        Assert.Equal("declaration", Assert.Throws<ArgumentNullException>(() => model.FindPropertyByDeclaration(null!)).ParamName);
    }

    [Fact]
    public async Task FlatHostOperations_UseTheBoundedProjectionAndActuallySuspend()
    {
        Result value = new Result.ListValue([new Result.Atom(1), new Result.Bool(true), new Result.Str("s")]);
        var synchronous = HostOperations.Create(HostOperation.Create("Data", (_, _) => value));
        var expr = new Expr.Call(new Expr.Resolve("Data"), []);
        Assert.Equal(new Decimal128[] { 1 }, Evaluator.RunFlat(expr, synchronous, null, 42, default).Value);
        Assert.Equal(new Decimal128[] { 1 }, (await Evaluator.RunFlatAsync(expr, synchronous, null, 42, default)).Value);

        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var asynchronous = HostOperations.Create(HostOperation.CreateAsync("Data", (_, token) => new(gate.Task.WaitAsync(token))));
        var pending = Evaluator.RunFlatAsync(expr, asynchronous, null, null, default);
        Assert.False(pending.IsCompleted);
        gate.SetResult(value);
        Assert.Equal(new Decimal128[] { 1 }, (await pending).Value);
        Assert.Throws<InvalidOperationException>(() => Evaluator.RunFlat(expr, asynchronous, null, null, default));

        // Only 25 distinct values, but 2^24 numeric paths. Evaluation can retain sharing;
        // flattening must refuse after the configured bound instead of allocating the tree.
        value = new Result.Atom(1);
        for (var i = 0; i < 24; i++) value = new Result.ListValue([value, value]);
        var bounded = new EvaluationLimits { MaxCollectionItems = 128 };
        Assert.Equal(KatLangErrorCode.CollectionSizeLimitExceeded,
            Evaluator.RunFlat(expr, synchronous, bounded, null, default).Error.Code);
        Assert.Equal(KatLangErrorCode.CollectionSizeLimitExceeded,
            (await Evaluator.RunFlatAsync(expr, synchronous, bounded, null, default)).Error.Code);
        Assert.Equal("hostOperations", Assert.Throws<ArgumentNullException>(
            () => Evaluator.RunFlat(expr, null!, null, null, default)).ParamName);
        Task asyncMisuse = Evaluator.RunFlatAsync(expr, null!, null, null, default);
        Assert.Equal("hostOperations", (await Assert.ThrowsAsync<ArgumentNullException>(() => asyncMisuse)).ParamName);
    }

    [Fact]
    public void ConsumerCannotForgeProducedResults_ButCanReadAndDeconstructThem()
    {
        var positive = ConsumerCompiler.Compile("""
            using KatLang;
            public class Consumer {
                public object Read(RunResult.Success success, ParseResult parsed) {
                    var (root, value, atoms) = success;
                    var (tree, diagnostics) = parsed;
                    return new object[] { root, value, atoms, tree, diagnostics, success with { } };
                }
            }
            """, "produced-results-readable");
        Assert.Equal(0, positive.ExitCode);
        var negative = ConsumerCompiler.Compile("""
            using KatLang;
            public class Consumer {
                public object Rewrite(RunResult.Success s, ParseResult p) =>
                    new object[] { s with { Value = new Result.Atom(7) }, p with { Diagnostics = [] } };
                public object Forge(Algorithm.User root) => new RunResult.Success(root, new Result.Atom(7), []);
            }
            """, "produced-results-not-forgeable");
        Assert.NotEqual(0, negative.ExitCode);
        Assert.Equal(3, negative.Diagnostics.Count);
        Assert.Equal(2, negative.Diagnostics.Count(d => d.Code == "CS0200"));
        Assert.Contains(negative.Diagnostics, d => d.Code is "CS1729" or "CS0122");
    }

    [Fact]
    public async Task SourceErrors_NeverInvokeHostOperationsOnAnySourceEntryPoint()
    {
        var calls = 0;
        var options = new RunOptions { HostOperations = HostOperations.Create(
            HostOperation.Create("Touch", (_, _) => { calls++; return new Result.Atom(1); })) };
        const string source = "Touch(), @";
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, options));
        Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options));
        Assert.Throws<KatLangException>(() => KatLangEngine.EvaluateToAtoms(source, options));
        await Assert.ThrowsAsync<KatLangException>(() => KatLangEngine.EvaluateToAtomsAsync(source, options));
        Assert.Equal(0, calls);
    }

    [Fact]
    public void LanguageBuiltDoublingGraph_CannotEscapeTheHostAtomBound()
    {
        var source = new StringBuilder("A0 = [1]\n");
        for (var i = 1; i <= 24; i++) source.AppendLine($"A{i} = [A{i - 1}, A{i - 1}]");
        source.Append("A24");
        var parsed = Parser.Parse(source.ToString());
        Assert.False(parsed.HasErrors);
        var limits = new EvaluationLimits { MaxCollectionItems = 128 };
        var expr = new Expr.AlgorithmExpr(parsed.Root);
        Assert.True(Evaluator.Run(expr, limits).IsOk); // the compact structure itself is valid
        var flat = Evaluator.RunFlat(expr, limits);
        Assert.Equal(KatLangErrorCode.CollectionSizeLimitExceeded, flat.Error.Code);
        var run = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source.ToString(), new RunOptions { EvaluationLimits = limits }));
        Assert.Equal(KatLangErrorCode.CollectionSizeLimitExceeded, Assert.Single(run.Errors).Code);
    }

    [Fact]
    public void PackageProject_EnforcesDocumentationCorrectnessAndAotAnalysis()
    {
        var project = XDocument.Load(Path.Combine(RepoRoot.Find(), "src/KatLang/KatLang.csproj"));
        Assert.Equal("true", project.Descendants("GenerateDocumentationFile").Single().Value);
        Assert.Equal("true", project.Descendants("IsAotCompatible").Single().Value);
        var errors = string.Join(';', project.Descendants("WarningsAsErrors").Select(e => e.Value)).Split(';');
        Assert.All(new[] { "CS0419", "CS1570", "CS1572", "CS1574", "CS1584", "CS1734" }, id => Assert.Contains(id, errors));
        Assert.DoesNotContain("CS1591", errors); // absent comments are not incorrect comments
    }
}
