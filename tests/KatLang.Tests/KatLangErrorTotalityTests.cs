using System.Reflection;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// <see cref="KatLangError.FromEvalError"/> is TOTAL: it returns a report for every error a host can
/// hold, and throws only <see cref="ArgumentNullException"/> for a null argument.
///
/// <para>The regression it pins: a HOST-BUILT program root (or a written block demanded as a value)
/// that requires a supplied argument but binds no name for it evaluates to
/// <see cref="EvalError.UnresolvedImplicitParams"/> with an EMPTY name list, and the facade's message
/// builder used to index the last name of that empty list, so
/// <see cref="KatLangError.FromEvalError"/> threw <see cref="ArgumentOutOfRangeException"/>. The trees
/// that reach it are a clause family without a zero-arity clause (empty or not) and a user algorithm
/// whose only pattern is nameless (<c>()</c>, <c>[]</c>). Source never produces them: a parsed root is
/// always an <see cref="Algorithm.User"/> whose inferred parameters are names (constitution FORMAL-08).
/// The structured error is unchanged and is Lean's own verdict for the same trees: <c>runResultM</c>
/// reports <c>unresolvedImplicitParams (Algorithm.params wired)</c>, which is <c>[]</c> here, and the
/// written-block arm of <c>zeroArgumentDemandError?</c> reports the same for a block. Only the C#
/// presentation changed (the manifest row "Diagnostic wording only").</para>
/// </summary>
public class KatLangErrorTotalityTests
{
    private const string NamelessReport =
        "The algorithm being evaluated requires supplied arguments, but it names no implicit parameter for them. " +
        "No arguments were provided, so the program cannot be executed.";

    private static Algorithm.User Body(params Expr[] output) => new(null, [], [], [], output);

    private static Algorithm.Conditional EmptyFamily() => new(Parent: null, Opens: [], Branches: []);

    private static Algorithm.Conditional OneArityFamily() => new(Parent: null, Opens: [],
    [
        new CondBranch(new Pattern.LitInt(0), Body(new Expr.Num(1))),
        new CondBranch(new Pattern.Bind("x"), Body(new Expr.Param("x"))),
    ]);

    private static Algorithm.User NamelessSequenceRoot() =>
        new(null, [new SequenceValueParameterPattern([])], [], [], [new Expr.Num(5)]);

    private static Algorithm.User NamelessListRoot() =>
        new(null, [new ListValueParameterPattern([])], [], [], [new Expr.Num(5)]);

    /// <summary>Every host-built route to an empty-name <see cref="EvalError.UnresolvedImplicitParams"/>.</summary>
    private static Expr NamelessProgram(string route) => route switch
    {
        "root: empty clause family" => new Expr.AlgorithmExpr(EmptyFamily()),
        "root: family without a zero-arity clause" => new Expr.AlgorithmExpr(OneArityFamily()),
        "root: nameless sequence pattern" => new Expr.AlgorithmExpr(NamelessSequenceRoot()),
        "root: nameless list pattern" => new Expr.AlgorithmExpr(NamelessListRoot()),
        "block: nameless pattern as a row" => new Expr.AlgorithmExpr(Body(new Expr.Num(1), new Expr.AlgorithmExpr(NamelessSequenceRoot()))),
        "block: nameless pattern in a builtin value slot" => new Expr.AlgorithmExpr(Body(
            new Expr.Call(new Expr.Resolve("count"), [new Expr.AlgorithmExpr(NamelessSequenceRoot())]))),
        _ => throw new ArgumentOutOfRangeException(nameof(route)),
    };

    public static TheoryData<string, string> NamelessRoutes => new()
    {
        { "root: empty clause family", NamelessReport },
        { "root: family without a zero-arity clause", NamelessReport },
        { "root: nameless sequence pattern", NamelessReport },
        { "root: nameless list pattern", NamelessReport },
        { "block: nameless pattern as a row", NamelessReport },
        { "block: nameless pattern in a builtin value slot", "while evaluating call to count: " + NamelessReport },
    };

    private static EvalError AssertEmptyNameReport(EvalResult<Result> result, string expectedMessage)
    {
        Assert.True(result.IsError, "expected an unresolved-implicit-parameter failure");
        var inner = result.Error;
        while (inner is EvalError.WithContext withContext)
            inner = withContext.Inner;
        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(inner);
        Assert.Empty(unresolved.ParamNames);

        var report = KatLangError.FromEvalError(result.Error);
        Assert.Equal(KatLangErrorCode.UnresolvedImplicitParams, report.Code);
        Assert.Equal(expectedMessage, report.Message);
        Assert.Same(result.Error, report.Source);
        return result.Error;
    }

    [Theory]
    [MemberData(nameof(NamelessRoutes))]
    public void EmptyNameReport_IsRendered_Synchronously(string route, string expectedMessage)
    {
        var error = AssertEmptyNameReport(Evaluator.Run(NamelessProgram(route)), expectedMessage);

        // The structured context is unchanged: the root/block report still carries the ONE
        // implicit-parameter context, naming no parameter.
        var context = FindContext<ImplicitParameterContext>(error);
        Assert.Empty(context.ParamNames);
        Assert.Equal(0, context.ProvidedArgumentCount);
    }

    [Theory]
    [MemberData(nameof(NamelessRoutes))]
    public async Task EmptyNameReport_IsRendered_OnTheAsyncTwin(string route, string expectedMessage)
    {
        var result = await AsyncEvaluationHarness.Complete(
            Evaluator.RunAsync(NamelessProgram(route), new RunScopedAsyncZeroArgPropertyResultCache()));
        AssertEmptyNameReport(result, expectedMessage);
    }

    [Fact]
    public void EmptyNameReport_NamesTheProvidedCount_WhenAHostSuppliesOne()
    {
        // A host may build the structured error and its context itself; a nonzero provided count is
        // reported as such rather than as "No arguments were provided".
        var error = new EvalError.WithContext(
            new ImplicitParameterContext([], 2),
            new EvalError.UnresolvedImplicitParams([]));
        Assert.Equal(
            "The algorithm being evaluated requires supplied arguments, but it names no implicit parameter for them. " +
            "Only 2 arguments were provided, so the program cannot be executed.",
            KatLangError.FromEvalError(error).Message);

        Assert.Equal(NamelessReport, KatLangError.FromEvalError(new EvalError.UnresolvedImplicitParams([])).Message);
    }

    [Fact]
    public void Controls_KeepTheirReports()
    {
        // A family root WITH a zero-arity clause is demanded through it.
        var zeroArity = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.SequenceValue([]), Body(new Expr.Num(7)))]);
        var accepted = Evaluator.RunFlat(new Expr.AlgorithmExpr(zeroArity));
        Assert.False(accepted.IsError);
        Assert.Equal([7m], accepted.Value);

        // A named root parameter keeps the enumerating report.
        var named = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Param("x")]);
        var namedResult = Evaluator.Run(new Expr.AlgorithmExpr(named));
        Assert.True(namedResult.IsError);
        Assert.Equal(
            "Identifier 'x' does not resolve to a property or other visible name here, so KatLang interprets it as an " +
            "implicit parameter. Its value is provided by the caller. No argument was provided, so the program cannot be " +
            "executed (expected 1 argument, got 0).",
            KatLangError.FromEvalError(namedResult.Error).Message);

        // A family BLOCK demanded as a value takes the family arm of the zero-argument value-demand
        // law, as in Lean (`zeroArgumentDemandError?`): NoMatchingBranch, never the empty-name report.
        var familyBlock = Evaluator.Run(new Expr.AlgorithmExpr(Body(
            new Expr.Call(new Expr.Resolve("count"), [new Expr.AlgorithmExpr(EmptyFamily())]))));
        Assert.True(familyBlock.IsError);
        var report = KatLangError.FromEvalError(familyBlock.Error);
        Assert.Equal(KatLangErrorCode.NoMatchingBranch, report.Code);
        Assert.Equal("while evaluating call to count: No matching branch for 'conditional'", report.Message);
    }

    // ----- Facade totality over every public error shape ---------------------------------------

    private static readonly int[] IntCandidates = [0, -1, 1, int.MinValue, int.MaxValue];
    private static readonly long[] LongCandidates = [0, -1, long.MaxValue];
    private static readonly string[] StringCandidates = ["", "x"];
    private static readonly IReadOnlyList<string>[] ListCandidates = [[], ["a"], ["a", "b"], ["a", "b", "c"]];

    /// <summary>
    /// The degenerate values a host may pass for a constructor parameter. A public error or context
    /// variant with a parameter type not listed here fails this suite loudly, so a new variant must be
    /// given candidates (and thereby a totality check) when it is added.
    /// </summary>
    private static object?[] Candidates(Type type, string owner)
    {
        if (type == typeof(int)) return [.. IntCandidates.Cast<object?>()];
        if (type == typeof(long)) return [.. LongCandidates.Cast<object?>()];
        if (type == typeof(string)) return StringCandidates;
        if (type == typeof(bool)) return [false, true];
        if (type == typeof(IReadOnlyList<string>)) return ListCandidates;
        if (type.IsEnum) return [.. Enum.GetValues(type).Cast<object?>()];
        throw new NotSupportedException(
            $"{owner} has a constructor parameter of type {type.FullName}; give it degenerate candidates in {nameof(KatLangErrorTotalityTests)}.");
    }

    /// <summary>Every public sealed variant of <typeparamref name="T"/>, built with every candidate combination.</summary>
    private static List<T> BuildAll<T>(params Type[] excluded)
    {
        var built = new List<T>();
        var variants = typeof(T).Assembly.GetExportedTypes()
            .Where(type => type.IsSealed && type != typeof(T) && typeof(T).IsAssignableFrom(type) && !excluded.Contains(type))
            .OrderBy(type => type.FullName, StringComparer.Ordinal);
        foreach (var variant in variants)
        {
            var constructor = variant.GetConstructors().OrderByDescending(c => c.GetParameters().Length).First();
            IEnumerable<object?[]> argumentSets = [[]];
            foreach (var parameter in constructor.GetParameters())
            {
                var options = Candidates(parameter.ParameterType, variant.Name);
                argumentSets = argumentSets.SelectMany(prefix => options.Select(option => prefix.Append(option).ToArray()));
            }

            foreach (var arguments in argumentSets)
                built.Add((T)constructor.Invoke(arguments));
        }

        return built;
    }

    [Fact]
    public void FromEvalError_IsTotal_OverEveryPublicErrorShape()
    {
        var errors = BuildAll<EvalError>(typeof(EvalError.WithContext));
        var contexts = BuildAll<ErrorContext>();

        // Sanity: the enumeration reached the variants this regression is about.
        Assert.Contains(errors, error => error is EvalError.UnresolvedImplicitParams { ParamNames.Count: 0 });
        Assert.Contains(contexts, context => context is ImplicitParameterContext { ParamNames.Count: 0 });

        var failures = new List<string>();
        void Check(EvalError error)
        {
            try
            {
                var report = KatLangError.FromEvalError(error);
                Assert.NotNull(report.Message);
                Assert.Equal(report.ToString(), report.RenderDiagnostic(static fragment => fragment));
            }
            catch (Exception exception) when (exception is not Xunit.Sdk.XunitException)
            {
                if (failures.Count < 20)
                    failures.Add($"{exception.GetType().Name} for {error}");
            }
        }

        foreach (var error in errors)
        {
            Check(error);
            foreach (var context in contexts)
            {
                // Bare inside each context, and one level deeper under an ordinary call frame: the
                // facade's (context, inner) recognizers match at the top only, so both positions matter.
                Check(new EvalError.WithContext(context, error));
                Check(new EvalError.WithContext(new CallContext("F"), new EvalError.WithContext(context, error)));
            }
        }

        Assert.True(failures.Count == 0, "KatLangError.FromEvalError threw:\n" + string.Join("\n", failures));
    }

    [Fact]
    public void FromEvalError_RejectsOnlyANullArgument()
        => Assert.Throws<ArgumentNullException>(() => KatLangError.FromEvalError(null!));

    private static TContext FindContext<TContext>(EvalError error) where TContext : ErrorContext
    {
        for (var current = error; current is EvalError.WithContext withContext; current = withContext.Inner)
        {
            if (withContext.ErrorContext is TContext found)
                return found;
        }

        throw new Xunit.Sdk.XunitException($"no {typeof(TContext).Name} in the error chain");
    }
}
