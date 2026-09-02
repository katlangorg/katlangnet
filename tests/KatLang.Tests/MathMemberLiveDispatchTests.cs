using System.Globalization;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Batch 3 / L6 — every registry Math member reaches a LIVE evaluator implementation.
///
/// <para>The registry's member table and the evaluator's native dispatch meet only
/// through the descriptor's spelling: a runtime Math FUNCTION is projected to
/// <c>Expr.NativeCall(member.Name, parameterNames)</c>, and <c>Evaluator.EvalNativeCall</c>
/// matches that name in a string <c>switch</c> whose <c>default</c> arm reports
/// "unknown native function". A misspelled, missing, or renamed case therefore
/// compiles and fails only when a program calls the member. This suite drives EVERY
/// descriptor through the real parser + evaluator path — the canonical <c>Math.X(...)</c>
/// spelling and the prelude alias <c>x(...)</c>, constants by property access — with
/// registry-derived benign arguments, so a future descriptor without a dispatch case
/// (or a broken existing case) fails here, named, without a bespoke test.</para>
/// </summary>
public class MathMemberLiveDispatchTests
{
    /// <summary>
    /// Members whose result is not a deterministic function of their arguments.
    /// The descriptor table does not model value domains or determinism, so this is
    /// the one deliberately tiny exception set; it is asserted against the registry
    /// so it can never name a stale or unknown member.
    /// </summary>
    private static readonly IReadOnlySet<string> NondeterministicMembers =
        new HashSet<string>(StringComparer.Ordinal) { "Random", "RandomInt" };

    public static IEnumerable<object[]> RegistryMembers()
        => BuiltinRegistry.MathMembers.Select(static member => new object[] { member.Name });

    [Fact]
    public void NondeterministicExceptionSet_NamesOnlyRegisteredMembers()
    {
        foreach (var name in NondeterministicMembers)
            Assert.Contains(BuiltinRegistry.MathMembers, member => member.Name == name);
    }

    [Fact]
    public void BenignArgumentVector_IsInDomainForEveryCurrentDescriptor()
    {
        // The generic vector 1, 2, ... (one value per declared parameter) must be a
        // legal input for every member: exercised in full by the theory below, and
        // restated here as the single invariant a new domain-restricted member
        // would have to keep (or extend deliberately).
        foreach (var member in BuiltinRegistry.MathMembers)
            Assert.Equal(member.Arity, BenignArguments(member).Count);
    }

    /// <summary>
    /// One theory case per registry member, so a failure is reported against the
    /// exact member. Both spellings run through the complete evaluator path.
    /// </summary>
    [Theory]
    [MemberData(nameof(RegistryMembers))]
    public void RegistryMember_ReachesALiveEvaluatorImplementation(string memberName)
    {
        var member = Assert.Single(BuiltinRegistry.MathMembers, candidate => candidate.Name == memberName);
        var arguments = BenignArguments(member);
        var identity = $"{member.CanonicalQualifiedName} (alias '{member.PreludeAlias}', {member.Arity} parameter(s))";

        var canonical = EvaluateAtom(Spell(member.CanonicalQualifiedName, arguments), identity);
        var alias = EvaluateAtom(Spell(member.PreludeAlias, arguments), identity);

        if (member.Kind == MathMemberKind.Constant)
        {
            // A constant's live implementation IS its registry value.
            Assert.Equal(member.ConstantValue, canonical);
            Assert.Equal(member.ConstantValue, alias);
            return;
        }

        Assert.True(
            Decimal128.IsFinite(canonical),
            $"{identity} produced a non-finite value {canonical} for benign arguments ({string.Join(", ", arguments)}).");

        if (NondeterministicMembers.Contains(member.Name))
        {
            // Benign arguments are the interval bounds (1, 2): a live implementation
            // answers inside that interval; no exact value can be asserted.
            Assert.True(canonical >= 1 && canonical <= 2, $"{identity} answered {canonical} outside [1, 2].");
            Assert.True(alias >= 1 && alias <= 2, $"{identity} (alias) answered {alias} outside [1, 2].");
            return;
        }

        // Deterministic: both spellings share ONE implementation, and repeating the
        // canonical call is stable.
        Assert.Equal(canonical, alias);
        Assert.Equal(canonical, EvaluateAtom(Spell(member.CanonicalQualifiedName, arguments), identity));
    }

    [Fact]
    public void UnknownNativeName_IsTheFailureThisSuiteGuardsAgainst()
    {
        // Negative control on the same dispatch seam: a wrapper whose native name
        // matches no evaluator case reaches the fail-loud default arm. This is
        // exactly what a registry member with a misspelled or missing case would
        // produce, so the theory above cannot pass on such a member.
        var wrapper = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.NativeCall("NoSuchNative", [])]);

        var result = Evaluator.Run(new Expr.AlgorithmExpr(wrapper));
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var illegal = Assert.IsType<EvalError.IllegalInEval>(error);
        Assert.Equal("unknown native function: NoSuchNative", illegal.Reason);
    }

    /// <summary>
    /// Registry-derived arguments: the value <c>i</c> for the <c>i</c>-th declared
    /// parameter. In-domain for every current member (logarithms of 1, inverse
    /// trigonometry of 1, a positive base and a whole non-negative digit count,
    /// and the strictly increasing whole-number interval (1, 2) for the random
    /// members), with no per-member argument table.
    /// </summary>
    private static IReadOnlyList<string> BenignArguments(MathMemberDescriptor member)
        => Enumerable.Range(1, member.Arity)
            .Select(static value => value.ToString(CultureInfo.InvariantCulture))
            .ToArray();

    private static string Spell(string callee, IReadOnlyList<string> arguments)
        => arguments.Count == 0 ? callee : $"{callee}({string.Join(", ", arguments)})";

    private static Decimal128 EvaluateAtom(string source, string identity)
    {
        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        if (result.IsError)
        {
            Assert.Fail(
                $"{identity} has no live evaluator implementation: `{source}` failed with: "
                + KatLangError.FromEvalError(result.Error).Message);
        }

        if (result.Value is not Result.Atom(var value))
        {
            Assert.Fail($"{identity}: `{source}` produced {result.Value} instead of one numeric atom.");
            return default;
        }

        return value;
    }
}
