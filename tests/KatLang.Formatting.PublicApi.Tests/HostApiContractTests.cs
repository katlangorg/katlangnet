using System.Numerics;
using System.Reflection;
using System.Text;
using System.Text.RegularExpressions;
using System.Xml.Linq;
using KatLang.Semantics;

namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// The pre-release public API audit (#11, September 2026), pinned from a NON-friend consumer:
/// the contracts a NuGet host relies on that the exact public API baseline alone would not
/// protect — a regeneration can bless a re-exposed implementation type, and the baseline says
/// nothing about how an entry point answers a null argument, whether an overload set is
/// ambiguous, whether the package carries its documentation, or whether the README's examples
/// still compile.
/// </summary>
public class HostApiContractTests
{
    private static readonly Assembly KatLangAssembly = typeof(KatLangEngine).Assembly;

    // ── Implementation machinery stays internal ──────────────────────────────

    /// <summary>
    /// Implementation machinery the audit made internal or deleted, by full name. Re-exposing
    /// one is a deliberate public API decision, never a baseline refresh.
    /// </summary>
    private static readonly string[] NonPublicTypeNames =
    [
        "KatLang.CallableArityFacts",
        "KatLang.CallableBindingCapture",
        "KatLang.CallableBindingNode",
        "KatLang.CallableBindingPlan",
        "KatLang.CallableParameter",
        "KatLang.CallableParameterSource",
        "KatLang.CallableSignature",
        "KatLang.CallableSignatureDiagnostics",
        "KatLang.CaptureBindingNode",
        "KatLang.CollectingCaptureBindingNode",
        "KatLang.PatternListBindingPlan",
        "KatLang.SequenceValueBindingNode",
        "KatLang.Semantics.SyntaxWalker",
    ];

    [Fact]
    public void ImplementationMachinery_IsNotPublic()
    {
        var exported = KatLangAssembly.GetExportedTypes()
            .Select(static type => type.FullName)
            .ToHashSet(StringComparer.Ordinal);

        Assert.DoesNotContain(NonPublicTypeNames, exported.Contains);
    }

    [Theory]
    [InlineData(typeof(KatLangEngine), "EvaluateToString")]
    [InlineData(typeof(KatLangEngine), "EvaluateToStringAsync")]
    [InlineData(typeof(SemanticModelBuilder), "EnumerateIdentifierOccurrences")]
    [InlineData(typeof(SemanticModelBuilder), "EnumerateDeclarationOccurrences")]
    [InlineData(typeof(SemanticModelBuilder), "EnumeratePropertyInfos")]
    [InlineData(typeof(Result), "Normalize")]
    [InlineData(typeof(Result), "LanguageAtoms")]
    [InlineData(typeof(Result), "ToHostAtoms")]
    [InlineData(typeof(Result), "ValueCount")]
    [InlineData(typeof(Result), "SingleAtomicNumber")]
    [InlineData(typeof(Result), "ToItems")]
    [InlineData(typeof(Result), "SpreadItems")]
    [InlineData(typeof(Result), "StructureItems")]
    [InlineData(typeof(Result), "Index")]
    [InlineData(typeof(Result), "AsIndex")]
    [InlineData(typeof(Result), "FromItems")]
    [InlineData(typeof(RunResult.NoProgramOutput), "DefaultMessage")]
    [InlineData(typeof(EvalError.ArityMismatch), "Signature")]
    [InlineData(typeof(EvalError.VariadicArityMismatch), "Signature")]
    public void RemovedOrInternalizedMember_IsNotPublic(Type type, string memberName)
        => Assert.Empty(type.GetMember(memberName, BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static));

    [Fact]
    public void SemanticModels_ComeOnlyFromTheBuilder()
        => Assert.Empty(typeof(SemanticModel).GetConstructors());

    [Fact]
    public void ResultKeepsTheHostValueModel()
    {
        // The documented host views survive the internalization of the evaluator's views.
        Assert.Equal((Decimal128?)5, new Result.SequenceValue([new Result.Atom(5)]).AsNum());
        Assert.True(new Result.SequenceValue([new Result.Bool(true)]).AsBool());
        Assert.Equal(
            new Result.ListValue([new Result.Atom(1), new Result.Str("a")]),
            new Result.ListValue([new Result.Atom(1), new Result.Str("a")]),
            Result.ValueComparer);
    }

    // ── Overload sets are unambiguous ─────────────────────────────────────────

    [Theory]
    [InlineData(nameof(Evaluator.Run))]
    [InlineData(nameof(Evaluator.RunAsync))]
    [InlineData(nameof(Evaluator.RunFlat))]
    [InlineData(nameof(Evaluator.RunFlatAsync))]
    public void EvaluatorEntryFamily_HasExactlyOneOverloadPerArity(string name)
    {
        var arities = typeof(Evaluator).GetMethods(BindingFlags.Public | BindingFlags.Static)
            .Where(method => method.Name == name)
            .Select(static method => method.GetParameters().Length)
            .ToList();

        Assert.NotEmpty(arities);
        Assert.Equal(arities.Count, arities.Distinct().Count());
    }

    /// <summary>
    /// A compile-time pin as much as a runtime one: these positional-<c>null</c> calls were
    /// ambiguous (CS0121) while a four-argument host-operation overload sat beside the
    /// four-argument seeded one, so reintroducing it breaks this project's build.
    /// </summary>
    [Fact]
    public async Task PositionalNullArguments_SelectExactlyOneOverload()
    {
        var expr = new Expr.Binary(BinaryOp.Add, new Expr.Num(1), new Expr.Num(2));

        Assert.Equal((Decimal128?)3, Evaluator.Run(expr, null, null, CancellationToken.None).Value.AsNum());
        Assert.Equal((Decimal128?)3, (await Evaluator.RunAsync(expr, null, null, CancellationToken.None)).Value.AsNum());
        Assert.Single(Evaluator.RunFlat(expr, null, null, CancellationToken.None).Value);
        Assert.Single((await Evaluator.RunFlatAsync(expr, null, null, CancellationToken.None)).Value);
    }

    // ── CLR arguments fail predictably ───────────────────────────────────────

    [Fact]
    public void SynchronousEntryPoints_RejectNullArguments()
    {
        var one = new Expr.Num(1);

        AssertNullArgument("source", () => KatLangEngine.Run(null!));
        AssertNullArgument("source", () => KatLangEngine.EvaluateToAtoms(null!));
        AssertNullArgument("source", () => Parser.Parse(null!));
        AssertNullArgument("source", () => Parser.Parse(null!, new RunOptions()));
        AssertNullArgument("expr", () => Evaluator.Run(null!));
        AssertNullArgument("expr", () => Evaluator.Run(null!, (EvaluationLimits?)null));
        AssertNullArgument("expr", () => Evaluator.Run(null!, null, null, CancellationToken.None));
        AssertNullArgument("expr", () => Evaluator.Run(null!, HostOperations.Create(), null, null, CancellationToken.None));
        AssertNullArgument("hostOperations", () => Evaluator.Run(one, (HostOperations)null!, null, null, CancellationToken.None));
        AssertNullArgument("expr", () => Evaluator.RunFlat(null!));
        AssertNullArgument("diag", () => KatLangError.FromDiagnostic(null!));
        AssertNullArgument("error", () => KatLangError.FromEvalError(null!));
        AssertNullArgument("errors", () => new KatLangException(null!));
        AssertNullArgument("root", () => SemanticModelBuilder.Build((Algorithm)null!));
        AssertNullArgument("parseResult", () => SemanticModelBuilder.Build((ParseResult)null!));
        AssertNullArgument("source", () => Lexer.Tokenize(null!));
        AssertNullArgument("text", () => Lexer.IsValidIdentifier(null!));
        AssertNullArgument("result", () => OutputFormatters.Exact.Format(null!));
    }

    [Fact]
    public async Task AsynchronousEntryPoints_DeliverArgumentValidationThroughTheTask()
    {
        await AssertNullArgumentThroughTask("source", () => KatLangEngine.RunAsync(null!));
        await AssertNullArgumentThroughTask("source", () => KatLangEngine.EvaluateToAtomsAsync(null!));
        await AssertNullArgumentThroughTask("source", () => Parser.ParseAsync(null!));
        await AssertNullArgumentThroughTask("expr", () => Evaluator.RunAsync(null!));
        await AssertNullArgumentThroughTask("expr", () => Evaluator.RunFlatAsync(null!));
        await AssertNullArgumentThroughTask(
            "hostOperations",
            () => Evaluator.RunAsync(new Expr.Num(1), (HostOperations)null!, null, null, CancellationToken.None));
    }

    [Fact]
    public void HostConstructedValuesAndErrors_RejectNullsWhereTheyAreBuilt()
    {
        AssertNullArgument("Value", () => new Result.Str(null!));
        AssertNullArgument("Value", () => new Result.Str("text") with { Value = null! });
        AssertNullArgument("items", () => new Result.SequenceValue(null!));
        AssertNullArgument("items", () => new Result.ListValue(null!));

        Assert.Equal("items", Assert.Throws<ArgumentException>(() => new Result.SequenceValue([new Result.Atom(1), null!])).ParamName);
        Assert.Equal("items", Assert.Throws<ArgumentException>(() => new Result.ListValue([null!])).ParamName);
        Assert.Equal("errors", Assert.Throws<ArgumentException>(() => new KatLangException([null!])).ParamName);
    }

    [Fact]
    public void KatLangException_SnapshotsItsErrors()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("1 / 0"));
        var errors = new List<KatLangError>(failure.Errors);

        var exception = new KatLangException(errors);
        errors.Clear();

        Assert.Equal(failure.Errors, exception.Errors);
        Assert.Contains("zero", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    /// <summary>
    /// A published result is immutable: its collections are read-only views, so a host that
    /// downcasts one (or shares a cached result) cannot change it — not even element-wise, as a
    /// raw array would allow despite reporting <c>IsReadOnly</c>.
    /// </summary>
    [Fact]
    public void PublishedResultCollections_AreReadOnly()
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("1, [2, 3]"));
        AssertReadOnly(success.Atoms);
        AssertReadOnly(success.OutputRows);
        AssertReadOnly(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("1 +")).Errors);
        AssertReadOnly(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("1 / 0")).Errors);
        AssertReadOnly(Parser.Parse("1 +").Diagnostics);
        AssertReadOnly(KatLangEngine.EvaluateToAtoms("1, 2"));
        AssertReadOnly(Evaluator.RunFlat(new Expr.Num(1)).Value);

        static void AssertReadOnly<T>(IReadOnlyList<T> list)
        {
            Assert.NotEmpty(list);
            if (list is not IList<T> writable)
                return;

            Assert.True(writable.IsReadOnly, $"{list.GetType().Name} is writable through IList<T>.");
            Assert.ThrowsAny<NotSupportedException>(() => writable[0] = writable[0]);
        }
    }

    // ── Configuration carries no run state ───────────────────────────────────

    [Fact]
    public void AllowedHosts_IsSnapshottedWhenTheOptionsAreInitialized()
    {
        var hosts = new List<string> { "example.org" };
        var options = new RunOptions { AllowedHosts = hosts };

        hosts.Add(" ");
        hosts[0] = "evil.example";

        Assert.Equal(["example.org"], options.AllowedHosts!);
        Assert.IsType<RunResult.Success>(KatLangEngine.Run("1", options));
    }

    [Fact]
    public void ReusedOptions_CarryNoStateFromEarlierRuns()
    {
        var options = new RunOptions { RandomSeed = 11, DefaultDisplayDecimals = 2 };
        const string program = "Math.RandomInt(1, 1000), 1 / 7";
        var first = KatLangEngine.Run(program, options).ToDisplayString();

        // A run whose program declares its own DisplayDecimals, then a failing run, between
        // two identical runs: neither leaves anything behind in the shared options object.
        Assert.Equal("0.142857", KatLangEngine.Run("DisplayDecimals = 6\n1 / 7", options).ToDisplayString());
        Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("1 / 0", options));

        Assert.Equal(first, KatLangEngine.Run(program, options).ToDisplayString());
        Assert.EndsWith("0.14", first, StringComparison.Ordinal);
        Assert.Equal(11, options.RandomSeed);
        Assert.Equal(2, options.DefaultDisplayDecimals);
    }

    // ── The package a consumer receives ──────────────────────────────────────

    [Fact]
    public void Package_ShipsItsXmlDocumentation()
    {
        var path = Path.ChangeExtension(KatLangAssembly.Location, ".xml");
        Assert.True(File.Exists(path), $"{path} is missing: consumers would get no IntelliSense documentation.");

        var documented = XDocument.Load(path)
            .Descendants("member")
            .Select(static member => (string?)member.Attribute("name"))
            .OfType<string>()
            .ToHashSet(StringComparer.Ordinal);

        string[] contractMembers =
        [
            "T:KatLang.KatLangEngine",
            "M:KatLang.KatLangEngine.Run(System.String,KatLang.RunOptions)",
            "M:KatLang.KatLangEngine.RunAsync(System.String,KatLang.RunOptions)",
            "M:KatLang.KatLangEngine.EvaluateToAtoms(System.String,KatLang.RunOptions)",
            "T:KatLang.RunOptions",
            "P:KatLang.RunOptions.RandomSeed",
            "P:KatLang.RunOptions.DefaultDisplayDecimals",
            "P:KatLang.RunOptions.EvaluationCancellationToken",
            "P:KatLang.RunOptions.SourceProcessingCancellationToken",
            "P:KatLang.RunOptions.AllowedHosts",
            "T:KatLang.RunResult",
            "T:KatLang.Result",
            "T:KatLang.HostOperation",
            "T:KatLang.KatLangError",
            "P:KatLang.KatLangError.Message",
            "P:KatLang.KatLangError.Code",
            "T:KatLang.KatLangException",
            "T:KatLang.DiagnosticSeverity",
            "T:KatLang.Parser",
            "M:KatLang.Parser.Parse(System.String)",
            "M:KatLang.Evaluator.Run(KatLang.Expr)",
            "T:KatLang.Formatting.OutputFormatter",
        ];

        Assert.All(contractMembers, member => Assert.Contains(member, documented));
    }

    [Fact]
    public void Assembly_IsMarkedTrimmable_ForNativeAotConsumers()
        => Assert.Contains(
            KatLangAssembly.GetCustomAttributes<AssemblyMetadataAttribute>(),
            static attribute => attribute.Key == "IsTrimmable" && attribute.Value == "True");

    /// <summary>
    /// Every C# example in the README compiles, as a consumer, against the public surface: each
    /// fence becomes one method (its <c>using</c> directives hoisted, and <c>source</c> /
    /// <c>result</c> supplied as parameters where a fragment reads them without declaring them).
    /// A removed or renamed API therefore cannot linger in the primary documentation.
    /// </summary>
    [Fact]
    public void ReadmeCSharpExamples_CompileAgainstThePublicSurface()
    {
        var readme = File.ReadAllText(Path.Combine(RepoRoot.Find(), "README.md")).ReplaceLineEndings("\n");
        var fences = Regex.Matches(readme, @"^```c#\n(?<body>.*?)^```", RegexOptions.Multiline | RegexOptions.Singleline);
        Assert.True(fences.Count >= 7, $"Expected the README's C# examples, found {fences.Count}.");

        var directives = new SortedSet<string>(StringComparer.Ordinal)
        {
            "using System;",
            "using System.Collections.Generic;",
            "using System.Linq;",
            "using System.Threading;",
            "using System.Threading.Tasks;",
        };
        var methods = new StringBuilder();
        for (var i = 0; i < fences.Count; i++)
        {
            var lines = fences[i].Groups["body"].Value.Split('\n');
            foreach (var line in lines.Where(IsUsingDirective))
                directives.Add(line.Trim());

            var body = string.Join('\n', lines.Where(line => !IsUsingDirective(line)));
            var parameters = new List<string>();
            if (Reads(body, "source") && !Declares(body, "source"))
                parameters.Add("string source");
            if (Reads(body, "result") && !Declares(body, "result"))
                parameters.Add("KatLang.RunResult result");

            methods.Append("    public static async Task Example").Append(i).Append('(')
                .Append(string.Join(", ", parameters)).Append(")\n    {\n")
                .Append(body).Append("\n        await Task.CompletedTask;\n    }\n\n");
        }

        var source = string.Join('\n', directives) + "\n\npublic static class ReadmeExamples\n{\n" + methods + "}\n";
        var compilation = ConsumerCompiler.Compile(source, "readme-examples");

        Assert.True(
            compilation.ExitCode == 0 && compilation.Diagnostics.Count == 0,
            "The README's C# examples must compile against the public package surface:\n" + compilation.Output);

        static bool IsUsingDirective(string line) => Regex.IsMatch(line, @"^\s*using\s+[A-Za-z_][\w.]*\s*;\s*$");
        static bool Reads(string body, string name) => Regex.IsMatch(body, $@"\b{name}\b");
        static bool Declares(string body, string name) => Regex.IsMatch(body, $@"\b(var|string|RunResult)\s+{name}\b");
    }

    /// <summary>
    /// The maintained, host-facing documents never name an API the audit removed or made
    /// internal. History may: the design documents and the alignment manifest record the
    /// removals, so they are deliberately not scanned.
    /// </summary>
    [Fact]
    public void MaintainedDocs_NeverNameARemovedOrInternalApi()
    {
        string[] documents =
        [
            "README.md",
            "tutorial.md",
            ".github/agents/katlang-generator.agent.md",
            "experimental/prompts/katlang-generator.txt",
        ];
        string[] retiredNames =
        [
            "EvaluateToString",
            "SyntaxWalker",
            "EnumerateIdentifierOccurrences",
            "EnumerateDeclarationOccurrences",
            "EnumeratePropertyInfos",
            "RequiredNormalParameterCount",
            "CallableSignature",
            "CallableBindingPlan",
            "ToHostAtoms",
            "LanguageAtoms",
        ];

        var root = RepoRoot.Find();
        foreach (var document in documents)
        {
            var text = File.ReadAllText(Path.Combine(root, document));
            foreach (var name in retiredNames)
                Assert.False(text.Contains(name, StringComparison.Ordinal), $"{document} still names `{name}`, which is not public API.");
        }
    }

    // ── Helpers ──────────────────────────────────────────────────────────────

    private static void AssertNullArgument(string parameterName, Func<object?> action)
        => Assert.Equal(parameterName, Assert.Throws<ArgumentNullException>(action).ParamName);

    private static async Task AssertNullArgumentThroughTask(string parameterName, Func<Task> start)
    {
        Task task;
        try
        {
            task = start();
        }
        catch (Exception exception)
        {
            Assert.Fail($"The asynchronous entry point threw {exception.GetType().Name} synchronously instead of faulting its task.");
            return;
        }

        var failure = await Assert.ThrowsAsync<ArgumentNullException>(() => task);
        Assert.Equal(parameterName, failure.ParamName);
    }
}
