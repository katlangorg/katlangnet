using System.Runtime.ExceptionServices;
using KatLang.Evaluation.Caching;

namespace KatLang.Benchmarks;

/// <summary>
/// Diagnostic sweep (not a benchmark): characterizes how many SYNCHRONOUSLY-COMPLETING
/// recursion levels the async twin family supports on a 1 MiB thread (the documented
/// minimum supported stack) compared with the synchronous evaluator, per recursion
/// shape. Run with <c>--async-stack-capacity</c>.
///
/// <para>For the call shapes the sweep finds the largest requested depth n (below the
/// deterministic ceiling of 128) that completes without the structured stack backstop
/// firing; for the structural shape it finds the deepest nested zero-declaration body
/// chain. Both paths stay STRUCTURED beyond their boundary — the point of the sweep is
/// the boundary itself, which informs the async-path documentation.</para>
/// </summary>
internal static class AsyncStackCapacityDiagnosticRunner
{
    private const int OneMiB = 1_048_576;

    public static bool TryRun(string[] args)
    {
        if (!args.Contains("--async-stack-capacity", StringComparer.Ordinal))
        {
            return false;
        }

        WriteReport();
        return true;
    }

    private static void WriteReport()
    {
        Console.WriteLine($"Async twin-path stack capacity on a {OneMiB / 1024} KiB thread ({BuildConfiguration()})");
        Console.WriteLine("Largest recursion request completing WITHOUT the structured stack backstop; ceiling column = deterministic MaxDepth request cap probed.");
        Console.WriteLine();
        Console.WriteLine($"{"shape",-24} {"sync",-12} {"async twin",-12} probed-cap");

        foreach (var (label, sourceForDepth, cap) in CallShapes())
        {
            var syncCapacity = FindLargestSucceeding(n => RunSyncOnThread(sourceForDepth(n)), cap);
            var asyncCapacity = FindLargestSucceeding(n => RunTwinOnThread(sourceForDepth(n)), cap);
            Console.WriteLine($"{label,-24} {Describe(syncCapacity),-12} {Describe(asyncCapacity),-12} {cap}");
        }

        var syncStructural = FindLargestSucceeding(n => RunSyncOnThread(NestedBodiesAst(n)), 150);
        var asyncStructural = FindLargestSucceeding(n => RunTwinOnThread(NestedBodiesAst(n)), 150);
        Console.WriteLine($"{"nested-bodies (AST)",-24} {Describe(syncStructural),-12} {Describe(asyncStructural),-12} 150");
    }

    private static string BuildConfiguration()
    {
#if DEBUG
        return "Debug";
#else
		return "Release";
#endif
    }

    private static IEnumerable<(string Label, Func<int, Expr> Source, int Cap)> CallShapes()
    {
        yield return ("plain-clause", n => ParsedAst($"F(0) = 0\nF(n) = F(n - 1)\nF({n})"), 127);
        yield return ("through-if", n => ParsedAst($"F(n) = if(n, F(n - 1), 0)\nF({n})"), 127);
        yield return ("dotted", n => ParsedAst($"Lib = {{public F(n) = if(n, Lib.F(n - 1), 0)}}\nLib.F({n})"), 127);
        yield return ("collection-callback", n => ParsedAst($"F(n) = if(n, [n - 1].map(F).first, 0)\nF({n})"), 127);
    }

    private static Expr ParsedAst(string source)
    {
        var frontEndResult = FrontEndPipeline.Process(source);
        if (frontEndResult.HasErrors)
        {
            throw new InvalidOperationException($"Probe source failed front-end processing: {source}");
        }

        return new Expr.AlgorithmExpr(frontEndResult.ElaboratedRoot);
    }

    private static Expr NestedBodiesAst(int depth)
    {
        Expr expr = new Expr.Num(42);
        for (var level = 0; level < depth; level++)
        {
            expr = new Expr.AlgorithmExpr(new Algorithm.User(
                Parent: null, Parameters: [], Opens: [], Properties: [], Output: [expr]));
        }

        return expr;
    }

    /// <summary>Binary search for the largest n in [1, cap] whose run SUCCEEDS.</summary>
    private static int FindLargestSucceeding(Func<int, bool> succeeds, int cap)
    {
        if (!succeeds(1))
        {
            return 0;
        }

        var low = 1;
        var high = cap;
        while (low < high)
        {
            var middle = (low + high + 1) / 2;
            if (succeeds(middle))
            {
                low = middle;
            }
            else
            {
                high = middle - 1;
            }
        }

        return low;
    }

    private static string Describe(int capacity)
        => capacity switch
        {
            0 => "none",
            127 => ">=ceiling",
            150 => ">=150",
            _ => capacity.ToString(),
        };

    private static bool RunSyncOnThread(Expr ast)
        => RunOnThread(() =>
        {
            var result = Evaluator.RunCounted(ast);
            return result.IsOk;
        });

    private static bool RunTwinOnThread(Expr ast)
        => RunOnThread(() =>
        {
            var pending = Evaluator.RunCountedAsync(ast, new RunScopedAsyncZeroArgPropertyResultCache());
            if (!pending.IsCompleted)
            {
                throw new InvalidOperationException("Twin probe run did not complete synchronously.");
            }

            return pending.Result.IsOk;
        });

    private static bool RunOnThread(Func<bool> body)
    {
        var outcome = false;
        Exception? failure = null;
        var thread = new Thread(() =>
        {
            try
            {
                outcome = body();
            }
            catch (Exception exception)
            {
                failure = exception;
            }
        }, OneMiB);
        thread.Start();
        thread.Join();

        if (failure is not null)
        {
            ExceptionDispatchInfo.Capture(failure).Throw();
        }

        return outcome;
    }
}
