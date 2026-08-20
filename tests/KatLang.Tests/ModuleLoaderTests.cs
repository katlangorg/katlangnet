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
    public void Load_WithoutDownloader_DefaultPipeline_NoLoadCalls()
    {
        // Without load calls, the normal pipeline (no downloadCode) works fine
        var source = "42";
        var result = Parser.Parse(source);
        Assert.False(result.HasErrors);
    }

    [Fact]
    public void Load_WithoutDownloader_DefaultPipeline_RejectsLoad()
    {
        var source = "Lib = load('https://katlang.org/demo/lib.kat')";

        var result = Parser.Parse(source);

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error
                 && d.Message.Contains("module elaboration is unavailable", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void OpenStringLiteralSugar_WithoutDownloader_DefaultPipeline_RejectsLoad()
    {
        var source = "open 'https://katlang.org/demo/lib.kat'\n1";

        var result = Parser.Parse(source);

        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error
                 && d.Message.Contains("module elaboration is unavailable", StringComparison.OrdinalIgnoreCase));
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

        var result = Parser.Parse(source);
        var evalResult = Evaluator.Run(new Expr.AlgorithmExpr(result.Root));
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
}
