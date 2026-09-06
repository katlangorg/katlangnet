using System.Numerics;
namespace KatLang.Tests;

/// <summary>
/// Tests for the load directive: compile-time module loading.
/// load is elaborated after parsing but before parameter detection and evaluation.
/// The evaluator never sees load calls Ã¢â‚¬â€ they are fully resolved to Block nodes.
/// </summary>
public class ModuleLoaderTests
{
    /// <summary>
    /// Creates a mock async downloader that serves content from a dictionary keyed by URL.
    /// The returned ValueTasks complete synchronously, so parsing with these mocks never
    /// actually suspends — genuine-suspension coverage lives in
    /// <see cref="ModuleLoaderAsyncTests"/>.
    /// </summary>
    private static Func<string, CancellationToken, ValueTask<string>> MockDownloader(
        Dictionary<string, string> files)
    {
        return (url, _) =>
        {
            // Normalize URL for lookup (Uri class may add trailing slash, etc.)
            if (files.TryGetValue(url, out var content))
                return ValueTask.FromResult(content);
            // Try without trailing slash
            var trimmed = url.TrimEnd('/');
            if (files.TryGetValue(trimmed, out content))
                return ValueTask.FromResult(content);
            throw new Exception($"404: {url}");
        };
    }

    /// <summary>Helper: parse with load elaboration using mock downloader.</summary>
    private static async Task<ParseResult> ParseWithLoad(string source, Dictionary<string, string> remoteFiles)
    {
        var downloader = MockDownloader(remoteFiles);
        return await Parser.ParseAsync(source, new RunOptions { DownloadCode = downloader });
    }

    private static bool ContainsRawLoad(Algorithm algorithm)
    {
        foreach (var open in algorithm.Opens)
        {
            if (ContainsRawLoad(open))
                return true;
        }

        foreach (var property in algorithm.Properties)
        {
            if (ContainsRawLoad(property.Value))
                return true;
        }

        foreach (var expr in algorithm.Output)
        {
            if (ContainsRawLoad(expr))
                return true;
        }

        if (algorithm is Algorithm.Conditional conditional)
        {
            foreach (var branch in conditional.Branches)
            {
                if (ContainsRawLoad(branch.Body))
                    return true;
            }
        }

        return false;
    }

    private static bool ContainsRawLoad(Expr expr)
        => expr switch
        {
            Expr.Call(Expr.Resolve("load"), _) => true,
            Expr.Call(var function, var args) => ContainsRawLoad(function) || args.Any(ContainsRawLoad),
            Expr.AlgorithmExpr(var algorithm) => ContainsRawLoad(algorithm),
            Expr.Capture(var captureBody) => captureBody.Any(row => ContainsRawLoad(row)),
            Expr.DotCall(var target, _, var args) => ContainsRawLoad(target) || (args is not null && args.Any(ContainsRawLoad)),
            Expr.Unary(_, var operand) => ContainsRawLoad(operand),
            Expr.Binary(_, var left, var right) => ContainsRawLoad(left) || ContainsRawLoad(right),
            Expr.Index(var target, var selector) => ContainsRawLoad(target) || ContainsRawLoad(selector),
            Expr.SequenceConstruct(var left, var right) => ContainsRawLoad(left) || ContainsRawLoad(right),
            Expr.SequenceSpread(var operand) => ContainsRawLoad(operand),
            Expr.Grace(var inner, _) => ContainsRawLoad(inner),
            _ => false,
        };

    /// <summary>Helper: parse + evaluate with load elaboration.</summary>
    private static async Task<EvalResult<IReadOnlyList<Decimal128>>> EvalWithLoad(
        string source, Dictionary<string, string> remoteFiles)
    {
        var result = await ParseWithLoad(source, remoteFiles);
        if (result.HasErrors)
            throw new Exception(
                "Parse/elaborate errors: " +
                string.Join("; ", result.Diagnostics
                    .Where(d => d.Severity == DiagnosticSeverity.Error)
                    .Select(d => d.Message)));
        return Evaluator.RunFlat(new Expr.AlgorithmExpr(result.Root));
    }

    [Fact]
    public async Task StrictAsyncProvenance_LoadedModule_EvaluatesThroughParseValidAsync()
    {
        // Strict provenance for a loading program: ParseValidAsync goes
        // through the authoritative async front end — the only entry that can
        // elaborate `open 'url'` when a downloader is configured (the sync
        // entry points reject downloader-configured options before parsing) —
        // fails loudly on any diagnostic, and hands back the elaborated root
        // without ever discarding front-end diagnostics.
        var provenance = await SourceProvenance.ParseValidAsync(
            "open 'https://katlang.org/lib/answers.kat'\nAnswer",
            new RunOptions
            {
                DownloadCode = MockDownloader(new Dictionary<string, string>
                {
                    ["https://katlang.org/lib/answers.kat"] = "public Answer = 42",
                }),
            });

        Assert.False(ContainsRawLoad(provenance.Root));

        var result = provenance.Evaluate();
        Assert.False(result.IsError);
        Assert.True(Result.ValueComparer.Equals(result.Value, new Result.Atom(42)));
    }

    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â
    //  A) Basic load into lib definition
    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â

    [Fact]
    public async Task Load_BasicLibDefinition_EvaluatesRemoteValue()
    {
        // Lib2 = load("https://katlang.org/demo/lib2.kat")
        // open Lib2
        // Val
        var source = """
            open Lib2
            public Lib2 = load('https://katlang.org/demo/lib2.kat')
            Val
            """;

        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/demo/lib2.kat"] = "public Val = 2"
        };

        var result = await EvalWithLoad(source, remoteFiles);
        Assert.True(result.IsOk, $"Expected success but got: {(result.IsError ? result.Error.ToString() : "")}");
        Assert.Equal([2m], result.Value);
    }

    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â
    //  B) load in open list
    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â

    [Fact]
    public async Task Load_InOpenList_EvaluatesRemoteValue()
    {
        var source = """
            open load('https://katlang.org/demo/lib3.kat')
            Val2
            """;

        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/demo/lib3.kat"] = "public Val2 = 3"
        };

        var result = await EvalWithLoad(source, remoteFiles);
        Assert.True(result.IsOk, $"Expected success but got: {(result.IsError ? result.Error.ToString() : "")}");
        Assert.Equal([3m], result.Value);
    }

    [Fact]
    public async Task Load_InOpenList_PublicApiCallingPrivateHelperWithCapturedNestedLocal_IsImported()
    {
        var source = """
            open load('https://katlang.org/demo/local-helper.kat')
            PublicApi(5)
            """;

        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/demo/local-helper.kat"] = """
                PrivateHelper(Candidate) = {
                    Step = Candidate + 1
                    Step
                }

                public PublicApi(N) = PrivateHelper(N)
                """
        };

        var result = await EvalWithLoad(source, remoteFiles);

        Assert.True(result.IsOk, $"Expected success but got: {(result.IsError ? result.Error.ToString() : "")}");
        Assert.Equal([6m], result.Value);
    }

    [Fact]
    public async Task OpenStringLiteral_PublicTopLevelWrapperOverPrivateNestedHelpers_RemainsImportable()
    {
        var source = """
            open 'https://katlang.org/libraries/math/number-theory.kat'
            IsPrime(11)
            """;

        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/libraries/math/number-theory.kat"] = """
                LargestPrimeSaved = 10

                IsSmallPrime(Candidate) = {
                    IsSmallPrimeStep = Candidate + 2
                    IsSmallPrimeStep
                }

                _IsPrime(Candidate) = {
                    IsPrimeStep = Candidate + 1
                    IsPrimeStep
                }

                public IsPrime(N) = if(
                    N <= LargestPrimeSaved,
                    IsSmallPrime(N),
                    _IsPrime(N)
                )
                """
        };

        var result = await EvalWithLoad(source, remoteFiles);

        Assert.True(result.IsOk, $"Expected success but got: {(result.IsError ? result.Error.ToString() : "")}");
        Assert.Equal([12m], result.Value);
    }

    [Fact]
    public async Task OpenStringLiteral_LoadedCallable_DetectsParameters()
    {
        var source = """
            open 'https://katlang.org/demo/vec.kat'
            Scale(Vector(2, 3), 4)
            """;

        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/demo/vec.kat"] = """
                public _x = 0
                public _y = 1
                public Vector = (x, y)
                public Scale = Vector(q~ * v:_x, q * v:_y)
                """
        };

        var result = await EvalWithLoad(source, remoteFiles);

        Assert.True(result.IsOk, $"Expected success but got: {(result.IsError ? result.Error.ToString() : "")}");
        Assert.Equal([8m, 12m], result.Value);
    }

    [Fact]
    public async Task OpenStringLiteral_LoadedCallable_CanUseSequenceBuiltins()
    {
        // The spread supplies each vector as its own argument slot, so the
        // loaded single-variadic callable collects [(3, 4), (0, 0)].
        var source = """
            open 'https://katlang.org/demo/vec.kat'
            Add((Vector(3, 4), Vector(0, 0))*)
            """;

        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/demo/vec.kat"] = """
                public _x = 0
                public _y = 1
                GetX = v:_x
                GetY = v:_y
                public Vector = (x, y)
                public Add(*vectors) = Vector(vectors.map(GetX).sum, vectors.map(GetY).sum)
                """
        };

        var result = await EvalWithLoad(source, remoteFiles);

        Assert.True(result.IsOk, $"Expected success but got: {(result.IsError ? result.Error.ToString() : "")}");
        Assert.Equal([3m, 4m], result.Value);
    }

    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â
    //  C) Domain blocked
    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â

    [Fact]
    public async Task Load_DomainBlocked_ProducesError()
    {
        var source = """
            Lib = load('https://evil.com/x.kat')
            """;

        var remoteFiles = new Dictionary<string, string>();

        var result = await ParseWithLoad(source, remoteFiles);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error &&
                 d.Message.Contains("domain not allowed"));
    }

    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â
    //  D) Dynamic URL blocked
    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â

    [Fact]
    public async Task Load_DynamicUrl_ProducesError()
    {
        // url = "https://katlang.org/demo/lib3.kat"
        // Lib = load(url)
        // Here 'url' parses as Resolve("url"), not a StringLiteral
        var source = """
            url = 'https://katlang.org/demo/lib3.kat'
            Lib = load(url)
            """;

        var remoteFiles = new Dictionary<string, string>();

        var result = await ParseWithLoad(source, remoteFiles);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error &&
                 d.Message.Contains("load URL must be a literal"));
    }

    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â
    //  E) Runtime-position blocked
    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â

    [Fact]
    public async Task Load_RuntimePosition_ProducesError()
    {
        var source = """
            x = 1
            y = load('https://katlang.org/demo/lib3.kat') + 1
            """;

        var remoteFiles = new Dictionary<string, string>();

        var result = await ParseWithLoad(source, remoteFiles);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error &&
                 d.Message.Contains("load not allowed in runtime expression"));
    }

    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â
    //  F) Cycle detection
    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â

    [Fact]
    public async Task Load_CycleDetection_ProducesError()
    {
        var source = """
            LibA = load('https://katlang.org/demo/A.kat')
            """;

        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/demo/A.kat"] = """
                LibB = load('https://katlang.org/demo/B.kat')
                """,
            ["https://katlang.org/demo/B.kat"] = """
                LibA = load('https://katlang.org/demo/A.kat')
                """,
        };

        var result = await ParseWithLoad(source, remoteFiles);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error &&
                 d.Message.Contains("load cycle detected"));
    }

    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â
    //  Additional edge cases
    // Ã¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢ÂÃ¢â€¢Â

    [Fact]
    public async Task Load_HttpScheme_Rejected()
    {
        var source = """
            Lib = load('http://katlang.org/demo/lib.kat')
            """;

        var result = await ParseWithLoad(source, new Dictionary<string, string>());
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error &&
                 d.Message.Contains("only HTTPS"));
    }

    [Fact]
    public async Task Load_InvalidUrl_Rejected()
    {
        var source = """
            Lib = load('not-a-url')
            """;

        var result = await ParseWithLoad(source, new Dictionary<string, string>());
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error &&
                 d.Message.Contains("invalid URL"));
    }

    [Fact]
    public async Task Load_MultipleArgs_Rejected()
    {
        var source = """
            Lib = load('https://katlang.org/a.kat', 'https://katlang.org/b.kat')
            """;

        var result = await ParseWithLoad(source, new Dictionary<string, string>());
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error &&
                 d.Message.Contains("exactly 1 argument"));
    }

    [Fact]
    public async Task Load_SubdomainAllowed()
    {
        var source = """
            open Lib
            public Lib = load('https://cdn.katlang.org/demo/lib.kat')
            X
            """;

        var remoteFiles = new Dictionary<string, string>
        {
            ["https://cdn.katlang.org/demo/lib.kat"] = "public X = 42"
        };

        var result = await EvalWithLoad(source, remoteFiles);
        Assert.True(result.IsOk, $"Expected success but got: {(result.IsError ? result.Error.ToString() : "")}");
        Assert.Equal([42m], result.Value);
    }

    [Fact]
    public async Task Load_CachesResults_SameUrlLoadedOnce()
    {
        var fetchCount = 0;
        Func<string, CancellationToken, ValueTask<string>> countingDownloader = (url, _) =>
        {
            fetchCount++;
            return ValueTask.FromResult("public Val = 99");
        };

        var source = """
            open Lib1
            Lib1 = load('https://katlang.org/demo/shared.kat')
            Lib2 = load('https://katlang.org/demo/shared.kat')
            Val
            """;

        var result = await Parser.ParseAsync(source, new RunOptions { DownloadCode = countingDownloader });
        Assert.False(result.HasErrors, string.Join("; ", result.Diagnostics.Select(d => d.Message)));
        Assert.Equal(1, fetchCount);
    }

    [Fact]
    public async Task Load_FetchFailure_ProducesError()
    {
        Func<string, CancellationToken, ValueTask<string>> failingDownloader = (url, _) =>
            throw new Exception("Network error");

        var source = """
            Lib = load('https://katlang.org/demo/broken.kat')
            """;

        var result = await Parser.ParseAsync(source, new RunOptions { DownloadCode = failingDownloader });
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error &&
                 d.Message.Contains("failed to fetch"));
    }

    [Fact]
    public async Task Load_FetchedHtml_ProducesSingleUrlDiagnostic()
    {
        Func<string, CancellationToken, ValueTask<string>> htmlDownloader = (_, _) => ValueTask.FromResult("""
            <!doctype html>
            <html>
              <body>Not found</body>
            </html>
            """);

        var source = """
            A = load('https://katlang.org/libraries2/example.kat')
            A.X
            """;

        var result = await Parser.ParseAsync(source, new RunOptions { DownloadCode = htmlDownloader });

        var errors = result.Diagnostics
            .Where(d => d.Severity == DiagnosticSeverity.Error)
            .ToList();
        var error = Assert.Single(errors);
        Assert.Contains("cannot load 'https://katlang.org/libraries2/example.kat'", error.Message);
        Assert.Contains("returned HTML", error.Message);
        Assert.Contains("points directly to a KatLang .kat file", error.Message);
        Assert.DoesNotContain("Unexpected", error.Message);
    }

    [Fact]
    public async Task Load_SizeExceeded_ProducesError()
    {
        var hugeContent = new string('x', 3 * 1024 * 1024); // 3 MB
        Func<string, CancellationToken, ValueTask<string>> hugeDownloader = (_, _) => ValueTask.FromResult(hugeContent);

        var source = """
            Lib = load('https://katlang.org/demo/huge.kat')
            """;

        var result = await Parser.ParseAsync(source, new RunOptions { DownloadCode = hugeDownloader });
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error &&
                 d.Message.Contains("UTF-16 code units, over the maximum of"));
    }

    [Fact]
    public async Task Load_TransitiveLoad_Works()
    {
        // A loads B; main loads A Ã¢â€ â€™ transitive loading
        var source = """
            open LibA
            public LibA = load('https://katlang.org/demo/A.kat')
            Val
            """;

        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/demo/A.kat"] = """
                open LibB
                public LibB = load('https://katlang.org/demo/B.kat')
                public Val = Val2 + 10
                """,
            ["https://katlang.org/demo/B.kat"] = """
                public Val2 = 7
                """,
        };

        var result = await EvalWithLoad(source, remoteFiles);
        Assert.True(result.IsOk, $"Expected success but got: {(result.IsError ? result.Error.ToString() : "")}");
        Assert.Equal([17m], result.Value);
    }

    [Fact]
    public async Task Load_WithoutDownloader_LoadFreePublicPathsWorkNormally()
    {
        const string Source = "42";

        Assert.False(Parser.Parse(Source).HasErrors);
        Assert.False((await Parser.ParseAsync(Source)).HasErrors);

        Assert.IsType<RunResult.Success>(KatLangEngine.Run(Source));
        Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(Source));
    }

    [Fact]
    public void Load_WithoutDownloader_DefaultPipeline_RejectsLoad()
    {
        var source = "Lib = load('https://katlang.org/demo/lib.kat')";

        var result = Parser.Parse(source);

        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, diagnostic.Code);
        Assert.Equal(LoadElaborationGuard.ModuleElaborationUnavailableDiagnostic, diagnostic.Message);
        Assert.Equal(new SourceSpan(1, 7, 1, 46), diagnostic.Span);
    }

    [Fact]
    public void OpenStringLiteralSugar_WithoutDownloader_DefaultPipeline_RejectsLoad()
    {
        var source = "open 'https://katlang.org/demo/lib.kat'\n1";

        var result = Parser.Parse(source);

        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, diagnostic.Code);
        Assert.Equal(LoadElaborationGuard.ModuleElaborationUnavailableDiagnostic, diagnostic.Message);
        Assert.Equal(new SourceSpan(1, 6, 1, 39), diagnostic.Span);
    }

    [Fact]
    public async Task Load_WithoutDownloader_AsyncParserAndEngineKeepTheStructuredDiagnostic()
    {
        const string Source = "Lib = load('https://katlang.org/demo/lib.kat')";

        var parsed = await Parser.ParseAsync(Source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, diagnostic.Code);
        Assert.Equal(LoadElaborationGuard.ModuleElaborationUnavailableDiagnostic, diagnostic.Message);
        Assert.Equal(new SourceSpan(1, 7, 1, 46), diagnostic.Span);

        static void AssertEngineProjection(RunResult result)
        {
            var failure = Assert.IsType<RunResult.ParseFailure>(result);
            var error = Assert.Single(failure.Errors);
            Assert.Equal(KatLangErrorCode.LoadElaborationUnavailable, error.Code);
            Assert.Equal(LoadElaborationGuard.ModuleElaborationUnavailableDiagnostic, error.Message);
            Assert.Equal(1, error.StartLine);
            Assert.Equal(7, error.StartColumn);
            Assert.Equal(1, error.EndLine);
            Assert.Equal(46, error.EndColumn);
            Assert.Null(error.Source);
            Assert.False(error.IsResourceLimit);
        }

        AssertEngineProjection(KatLangEngine.Run(Source));
        AssertEngineProjection(await KatLangEngine.RunAsync(Source));
    }

    /// <summary>
    /// M1 completion (v0.8.189): a <see cref="ModuleLoader"/> cannot exist without an
    /// explicit downloader. The former nullable parameter silently substituted a
    /// built-in HttpClient fetcher — a hidden second transport beside the ONE
    /// <c>RunOptions.DownloadCode</c> contract, whose default redirect-following could
    /// fetch from a host the allowlist check never saw. Both constructors now reject
    /// null instead of substituting any transport.
    /// </summary>
    [Fact]
    public void ModuleLoader_Constructors_RequireAnExplicitDownloader()
    {
        var convenienceException = Assert.Throws<ArgumentNullException>(
            () => new ModuleLoader([], downloadCode: null!));

        var pipelineException = Assert.Throws<ArgumentNullException>(
            () => new ModuleLoader(
                [],
                downloadCode: null!,
                allowedHosts: null,
                budget: new SourceProcessingBudget(null),
                sourceProcessingCancellationToken: CancellationToken.None));

        Assert.Equal("downloadCode", convenienceException.ParamName);
        Assert.Equal("downloadCode", pipelineException.ParamName);
    }

    [Fact]
    public async Task Load_WithDownloader_SuccessfulParseContainsNoRawLoadCalls()
    {
        var source = "Lib = load('https://katlang.org/demo/lib.kat')\nLib.X";
        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/demo/lib.kat"] = "public X = 9"
        };

        var result = await ParseWithLoad(source, remoteFiles);

        Assert.False(result.HasErrors, string.Join("; ", result.Diagnostics.Select(d => d.Message)));
        Assert.False(ContainsRawLoad(result.Root));
    }

    [Fact]
    public void ContainsRawLoad_TraversesSequenceConstruct()
    {
        // Regression: the helper must traverse Expr.SequenceConstruct so a raw `load`
        // sitting in a joined expression is not silently skipped.
        var rawLoad = new Expr.Call(
            new Expr.Resolve("load"),
            [new Expr.StringLiteral("https://katlang.org/x.kat")]);

        Assert.True(ContainsRawLoad(new Expr.SequenceConstruct(new Expr.Num(1), rawLoad)));
        Assert.True(ContainsRawLoad(new Expr.SequenceConstruct(rawLoad, new Expr.Num(1))));
        Assert.False(ContainsRawLoad(new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2))));
    }

    [Fact]
    public async Task Load_NoArguments_Rejected()
    {
        var source = """
            Lib = load()
            """;

        var result = await ParseWithLoad(source, new Dictionary<string, string>());
        Assert.True(result.HasErrors);
    }

    [Fact]
    public async Task Load_NumericArg_Rejected()
    {
        var source = """
            Lib = load(42)
            """;

        var result = await ParseWithLoad(source, new Dictionary<string, string>());
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error &&
                 d.Message.Contains("load URL must be a literal"));
    }

    [Fact]
    public void StringLiteral_InEvaluator_ReturnsStringResult()
    {
        // String literals are first-class values and should evaluate to Result.Str
        var source = """
            'hello'
            """;

        var provenance = SourceProvenance.ParseValid(source);
        var evalResult = provenance.Evaluate();
        Assert.True(evalResult.IsOk);
        Assert.IsType<Result.Str>(evalResult.Value);
        Assert.Equal("hello", ((Result.Str)evalResult.Value).Value);
    }

    [Fact]
    public async Task Load_InsideListLiteral_InheritsSurroundingContext()
    {
        // List-literal elements inherit the surrounding load context exactly
        // like parenthesized-group output slots: a load in a property-RHS list
        // elaborates, and no raw load call survives elaboration.
        var source = """
            X = [load('https://katlang.org/m')]
            X
            """;
        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/m"] = "public Answer = 42",
        };

        var result = await ParseWithLoad(source, remoteFiles);
        Assert.False(
            result.HasErrors,
            string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));
        Assert.False(ContainsRawLoad(result.Root));
    }

    // ── B2c: alternative branch bodies are deferred module-elaboration regions ──
    //
    // Initial module elaboration never descends into a load-bearing conditional branch body:
    // nothing under it is fetched, parsed, elaborated, or budget-charged until evaluation
    // selects that branch. Family-owned opens (host trees only) are shared by every
    // alternative and stay eager. These pins are C#-only by nature (module transport is a
    // host facility the Lean model does not have), so this is the family that owns them; the
    // engine-level acceptance matrix lives in BranchLazyModuleLoadingTests.

    [Theory]
    // Directly in a branch body's open list.
    [InlineData("F(0) = {\n    open 'https://katlang.org/demo/m.kat'\n    ImportedValue\n}\nF(n) = n\nF(0)")]
    // In a nested brace body inside the branch.
    [InlineData("F(0) = {\n    G = {\n        open 'https://katlang.org/demo/m.kat'\n        ImportedValue\n    }\n    G\n}\nF(n) = n\nF(0)")]
    // Two conditional levels down.
    [InlineData("F(0) = {\n    G(0) = {\n        open 'https://katlang.org/demo/m.kat'\n        ImportedValue\n    }\n    G(k) = k\n    G(0)\n}\nF(n) = n\nF(0)")]
    // In an expression-position block inside the branch.
    [InlineData("F(0) = {\n    { open 'https://katlang.org/demo/m.kat'\n      ImportedValue }\n}\nF(n) = n\nF(0)")]
    // As a branch-local property value, promoted to the module itself like any `X = load(...)`.
    [InlineData("F(0) = {\n    Lib = load('https://katlang.org/demo/m.kat')\n    Lib.ImportedValue\n}\nF(n) = n\nF(0)")]
    public async Task Load_InsideConditionalBranch_IsDeferredUntilTheBranchIsSelected(string source)
    {
        var downloads = 0;
        var files = MockDownloader(new Dictionary<string, string>
        {
            ["https://katlang.org/demo/m.kat"] = "public ImportedValue = 5",
        });
        Func<string, CancellationToken, ValueTask<string>> counting = (url, token) =>
        {
            downloads++;
            return files(url, token);
        };

        var parsed = await Parser.ParseAsync(source, new RunOptions { DownloadCode = counting });

        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));
        Assert.Equal(0, downloads);
        var family = Assert.IsType<Algorithm.Conditional>(parsed.Root.Properties.Single(p => p.Name == "F").Value);
        Assert.True(DeferredModuleRegions.TryGet(family.Branches[0].Body, out var region));
        Assert.False(region!.IsMaterialized);
        Assert.Equal(0, region.MaterializationAttempts);
        // The directive stays inside the deferred region by design (never an unresolved load
        // the pipeline forgot), and the load-free alternative is an ordinary eager branch.
        Assert.True(ContainsRawLoad(family.Branches[0].Body));
        Assert.False(DeferredModuleRegions.IsDeferred(family.Branches[1].Body));

        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));

        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([5m], result.Value);
        Assert.Equal(1, downloads);
        Assert.True(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.True(region.TryGetMaterialized(out var materialized));
        // Nested laziness: an inner alternative (case 3) keeps its own directive inside its own
        // deferred region; nothing outside a deferred region is left unresolved.
        Assert.False(LoadElaborationGuard.TryFindFirstUnresolvedLoad(materialized!, out _));
    }

    [Fact]
    public async Task Load_HostFamilyOwnedOpenIsShared_WhileSharedBranchBodiesDeferSeparately()
    {
        // Ownership-first: a family-owned open (host trees only) belongs to every alternative
        // and is elaborated eagerly; each branch body's own load is branch-exclusive and
        // deferred. ONE raw body object shared by two branches (a legal host DAG) yields two
        // distinct regions — the second branch materializes on its own selection, and the
        // per-URL module cache keeps one download per module across both.
        var downloads = new Dictionary<string, int>();
        var files = MockDownloader(new Dictionary<string, string>
        {
            ["https://katlang.org/demo/family.kat"] = "public FamilyValue = 7",
            ["https://katlang.org/demo/branch.kat"] = "public BranchValue = 8",
        });
        Func<string, CancellationToken, ValueTask<string>> counting = (url, token) =>
        {
            downloads[url] = downloads.GetValueOrDefault(url) + 1;
            return files(url, token);
        };
        static Expr Load(string url)
            => new Expr.Call(new Expr.Resolve("load"), new OutputBundle([new Expr.StringLiteral(url)]));
        var sharedBody = new Algorithm.User(
            null,
            [],
            [Load("https://katlang.org/demo/branch.kat")],
            [],
            [new Expr.Binary(BinaryOp.Add, new Expr.Resolve("FamilyValue"), new Expr.Resolve("BranchValue"))]);
        var conditional = new Algorithm.Conditional(
            null,
            [Load("https://katlang.org/demo/family.kat")],
            [
                new CondBranch(new Pattern.LitInt(0), sharedBody),
                new CondBranch(new Pattern.LitInt(1), sharedBody),
                new CondBranch(new Pattern.Bind("n"), new Algorithm.User(null, [], [], [], [new Expr.Resolve("n")])),
            ]);
        var root = new Algorithm.User(null, [], [], [new Property("F", conditional)], OutputBundle.Empty);
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(diagnostics, counting);

        var elaborated = await loader.ElaborateAsync(root);

        Assert.Empty(diagnostics);
        Assert.Equal(1, downloads.GetValueOrDefault("https://katlang.org/demo/family.kat"));
        Assert.Equal(0, downloads.GetValueOrDefault("https://katlang.org/demo/branch.kat"));
        Assert.Equal(2, loader.DeferredRegionCount);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(elaborated.Properties).Value);
        var familyModule = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(family.Opens)).Algorithm;
        Assert.Contains(familyModule.Properties, p => p.Name == "FamilyValue");
        Assert.NotSame(family.Branches[0].Body, family.Branches[1].Body);
        Assert.True(DeferredModuleRegions.TryGet(family.Branches[0].Body, out var loaderRegion0));
        Assert.True(DeferredModuleRegions.TryGet(family.Branches[1].Body, out var loaderRegion1));
        Assert.NotSame(loaderRegion0, loaderRegion1);
        Assert.Same(loaderRegion0!.RawBody, loaderRegion1!.RawBody);
        Assert.False(DeferredModuleRegions.IsDeferred(family.Branches[2].Body));

        var (detected, detectorDiagnostics) = ParameterDetector.Detect(elaborated);
        Assert.Empty(detectorDiagnostics);
        var exposed = PropertyExposureResolver.Resolve(ImplicitArgumentResolver.Resolve(detected));
        family = Assert.IsType<Algorithm.Conditional>(Assert.Single(exposed.Properties).Value);
        Assert.True(DeferredModuleRegions.TryGet(family.Branches[0].Body, out var region0));
        Assert.True(DeferredModuleRegions.TryGet(family.Branches[1].Body, out var region1));

        Algorithm Program(int literal)
        {
            var program = exposed with
            {
                Output = new OutputBundle([new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(literal)]))]),
            };
            DeferredModuleRegions.MarkRootRequiresAsyncEvaluation(program);
            return program;
        }

        var first = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(Program(0)));
        Assert.False(first.IsError, first.IsError ? first.Error.ToString() : null);
        Assert.Equal([15m], first.Value);
        Assert.Equal(1, downloads["https://katlang.org/demo/branch.kat"]);
        Assert.Equal(1, region0!.MaterializationAttempts);
        Assert.Equal(0, region1!.MaterializationAttempts);

        var second = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(Program(1)));
        Assert.False(second.IsError, second.IsError ? second.Error.ToString() : null);
        Assert.Equal([15m], second.Value);
        // The second region materializes on its own selection; the module cache served it.
        Assert.Equal(1, downloads["https://katlang.org/demo/branch.kat"]);
        Assert.Equal(1, region1.MaterializationAttempts);
        Assert.Equal(1, downloads["https://katlang.org/demo/family.kat"]);
    }
}
