using BenchmarkDotNet.Attributes;

namespace KatLang.Benchmarks;

/// <summary>Native AST record equality and hashing over prebuilt host trees and DAGs.</summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 5, iterationCount: 10)]
public class NativeRecordEqualityBenchmarks
{
    private Expr _left = null!;
    private Expr _right = null!;

    [Params("Flat", "Nested", "Mixed", "SharedLeaf", "Chain1000", "Diamond40")]
    public string Shape { get; set; } = "";

    [GlobalSetup]
    public void Setup()
    {
        var args = new OutputBundle([new Expr.Num(1)]);
        var sharedLeaf = new Expr.Resolve("x");
        _left = Build();
        _right = Build();

        Expr Build() => Shape switch
        {
            "Flat" => new Expr.Binary(BinaryOp.Add, new Expr.Resolve("x"), new Expr.Num(2)),
            "Nested" => new Expr.Unary(UnaryOp.Minus, new Expr.Unary(UnaryOp.Minus, new Expr.Num(1))),
            "Mixed" => Mixed(),
            "SharedLeaf" => new Expr.Unary(UnaryOp.Minus, new Expr.Unary(UnaryOp.Minus, sharedLeaf)),
            "Chain1000" => Wrap(1000, diamond: false),
            "Diamond40" => Wrap(40, diamond: true),
            _ => throw new InvalidOperationException(Shape),
        };

        Expr Mixed()
        {
            Expr expr = new Expr.Call(new Expr.Resolve("F"), args);
            for (var level = 0; level < 6; level++)
                expr = new Expr.Binary(BinaryOp.Mul, new Expr.Unary(UnaryOp.Minus, expr), new Expr.DotCall(new Expr.Resolve("r"), "m"));
            return expr;
        }

        static Expr Wrap(int depth, bool diamond)
        {
            Expr expr = new Expr.Num(1);
            for (var level = 0; level < depth; level++)
                expr = diamond ? new Expr.Binary(BinaryOp.Add, expr, expr) : new Expr.Unary(UnaryOp.Minus, expr);
            return expr;
        }
    }

    [Benchmark]
    public bool Equal() => _left.Equals(_right);

    [Benchmark]
    public int Hash() => _left.GetHashCode();
}
