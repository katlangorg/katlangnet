using System.Numerics;
namespace KatLang.Tests;

/// <summary>
/// Regression coverage for the sequence-builtin callback-argument evaluation
/// path. A callback whose parameter name collides with a sibling call argument
/// used to recurse without bound (process-crashing StackOverflowException)
/// instead of producing a structured KatLang diagnostic. See
/// <c>BuildCallableCallItems</c>: callback arguments must not have their bodies
/// evaluated standalone while their parameters are unbound.
/// </summary>
public class SequenceCallbackArgumentTests
{
    private static EvalResult<Result> Eval(string source)
    {
        var ast = SourceProvenance.ParseValid(source).Root;
        return Evaluator.Run(new Expr.AlgorithmExpr(ast));
    }

    private static IReadOnlyList<Decimal128> Atoms(string source)
    {
        var r = Eval(source);
        Assert.True(r.IsOk, r.IsError ? r.Error.ToString() : "");
        // Host-boundary flattening opens exact-list builtin results (e.g. take)
        // so flat expectations keep working across the list-result change.
        return r.Value.ToHostAtoms();
    }

    // ── The crash repro: must fail cleanly, never crash the process ──────────

    [Fact]
    public void CallbackParamCollidesWithSiblingArgument_FailsCleanly()
    {
        // Vector's parameter `x` collides with X's pattern variable `x`. The
        // spread call supplies the vector's scalar items as separate slots, so
        // `vectors` collects [1, 2] and map(X) is an invalid shape (scalar
        // elements against a deconstruction callback). It must report a
        // structured error, not recurse.
        var source = """
            Vector(x, y) = (x, y)
            X((x, y)) = x
            Y((x, y)) = y
            Sum(*vectors) = Vector(vectors.map(X).sum, vectors.map(Y).sum)
            Sum(Vector(1, 2)*)
            """;

        var result = Eval(source);

        Assert.True(result.IsError, "expected a structured evaluation error, not success");
    }

    [Fact]
    public void CallbackArgumentInsideUserCall_FailsCleanly()
    {
        // Minimal shape: a map callback whose parameter name (x) matches the
        // enclosing fixed-call parameter (x), evaluated as a call argument.
        var source = """
            Wrap(x) = x
            Pick((x, y)) = x
            F(items) = Wrap(items.map(Pick).sum)
            F((1, 2))
            """;

        var result = Eval(source);

        Assert.True(result.IsError, "expected a structured evaluation error, not success");
    }

    // ── Valid sequence-callback behavior must be unchanged ───────────────────

    [Fact]
    public void MapSum_OverNumbers_StillWorks()
        => Assert.Equal(new Decimal128[] { 9 }, Atoms("Inc(n) = n + 1\n(1, 2, 3).map(Inc).sum"));

    [Fact]
    public void MapSum_CallbackArgumentInsideUserCall_StillWorks()
    {
        // Same structural shape as the crash repro (callback inside a user call),
        // but the spread supplies whole vectors as the collected elements →
        // must compute, not error.
        var source = """
            Vector(x, y) = (x, y)
            X((x, y)) = x
            Y((x, y)) = y
            Sum(*vectors) = Vector(vectors.map(X).sum, vectors.map(Y).sum)
            Sum((Vector(1, 2), Vector(3, 4), Vector(5, 6))*)
            """;
        Assert.Equal(new Decimal128[] { 9, 12 }, Atoms(source));
    }

    [Fact]
    public void Filter_CallbackInsideUserCall_StillWorks()
        => Assert.Equal(new Decimal128[] { 2 }, Atoms("GreaterThanOne(n) = n > 1\nId(a) = a\nId((1, 2, 3).filter(GreaterThanOne).count)"));

    [Fact]
    public void Reduce_CallbackInsideUserCall_StillWorks()
        => Assert.Equal(new Decimal128[] { 10 }, Atoms("Add(x, total) = x + total\nId(a) = a\nId(reduce((1, 2, 3, 4), Add, 0))"));

    [Fact]
    public void Take_ValueSuffixInsideUserCall_StillWorks()
        => Assert.Equal(new Decimal128[] { 1, 2 }, Atoms("Id(a) = a\nId(take((1, 2, 3), 2))"));
}
