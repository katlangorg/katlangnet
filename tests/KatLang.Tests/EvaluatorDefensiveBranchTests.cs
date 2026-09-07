using System.Numerics;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// Witnesses for evaluator branches that ordinary KatLang source can no longer
/// reach because the FRONT END guarantees the condition away — but which the
/// evaluator deliberately revalidates because <c>Evaluator.Run</c> /
/// <c>RunCounted</c> are a public API that accepts prebuilt ASTs from hosts and
/// from internal elaboration stages.
///
/// <para>
/// Track 12 classified these as <b>P</b> (pre-empted defensive). Every one of
/// them survived a mutation of the branch itself against the entire suite,
/// because no surface program can reach them: the parser rejects the shape, or
/// an elaboration pass rewrites it first. That makes them invisible to the
/// language corpora by construction, so they are pinned HERE, at the API
/// boundary that actually justifies their existence, rather than with a
/// misleading LanguageSpec or Lean case for behavior the language cannot
/// express.
/// </para>
///
/// <para>
/// Each test states the front-end invariant that pre-empts the branch, so a
/// future change that makes the shape surface-reachable will be recognized as
/// a deliberate contract change rather than a puzzle.
/// </para>
/// </summary>
public class EvaluatorDefensiveBranchTests
{
    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static EvalError FailsWith(Expr root)
    {
        var result = Evaluator.Run(root);
        Assert.True(result.IsError, "Expected the defensive branch to reject this AST.");
        return Innermost(result.Error);
    }

    private static Expr.AlgorithmExpr Program(Algorithm.User root) => new(root);

    private static Algorithm.User Root(
        IReadOnlyList<Expr>? opens = null,
        IReadOnlyList<Property>? properties = null,
        OutputBundle? output = null)
        => new(Parent: null, Parameters: [], Opens: opens ?? [], Properties: properties ?? [], Output: output ?? OutputBundle.Empty);

    private static Algorithm.User Value(decimal n)
        => new(Parent: null, Parameters: [], Opens: [], Properties: [], Output: [new Expr.Num(n)]);

    /// <summary>
    /// <c>Expr.Grace</c> is the implicit-argument placeholder (<c>~</c>). The
    /// front end's implicit-argument resolver replaces every grace node during
    /// elaboration, so a parsed program never carries one into evaluation — the
    /// evaluator's catch-all rejects it only for prebuilt ASTs.
    /// </summary>
    [Fact]
    public void Grace_ReachesTheEvaluatorCatchAll_OnlyFromAPrebuiltAst()
    {
        var error = FailsWith(Program(Root(output: [new Expr.Grace(new Expr.Num(1), Weight: 0)])));

        var illegal = Assert.IsType<EvalError.IllegalInEval>(error);
        Assert.Equal("grace", illegal.Reason);
    }

    /// <summary>
    /// <c>Expr.SequenceConstruct</c> is an INTERNAL sequence-join node the parser
    /// must never produce (guarded by <c>SequenceConstructContainmentTests</c>).
    /// It is a legal evaluation node, but never a legal <c>open</c> target.
    /// </summary>
    [Fact]
    public void SequenceConstructOpenTarget_IsRejected_OnlyFromAPrebuiltAst()
    {
        var error = FailsWith(Program(Root(
            opens: [new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2))],
            output: [new Expr.Resolve("Missing")])));

        Assert.IsType<EvalError.BadOpenForm>(error);
    }

    /// <summary>
    /// The open-form validation pass in <c>ResolveAllOpens</c>. The parser
    /// rejects every non-open form in open position with its own targeted
    /// diagnostic ("Invalid open form: 'spread' is not allowed in open
    /// declarations"), so this loop only ever fires for a prebuilt AST.
    /// </summary>
    [Fact]
    public void NonOpenFormTarget_IsRejected_OnlyFromAPrebuiltAst()
    {
        var error = FailsWith(Program(Root(
            opens: [new Expr.Num(7)],
            output: [new Expr.Resolve("Missing")])));

        Assert.IsType<EvalError.BadOpenForm>(error);
    }

    /// <summary>
    /// <c>ResolveAllOpens</c> validates the SHAPE of every open target before
    /// resolving any of them. That ordering is the only observable difference
    /// between the up-front validation loop and the per-target rejection inside
    /// <c>ResolveAlgForOpen</c> — both produce <c>BadOpenForm</c> on their own,
    /// so a test that merely asserts "a bad form is rejected" cannot tell
    /// whether the loop still exists.
    ///
    /// <para>
    /// Here the FIRST target would fail resolution with <c>IllegalInOpen</c>
    /// (a builtin) while a LATER target is malformed. Validating shapes first
    /// means the malformed target wins.
    /// </para>
    /// </summary>
    [Fact]
    public void OpenFormsAreAllValidatedBeforeAnyTargetIsResolved()
    {
        var error = FailsWith(Program(Root(
            opens: [new Expr.Resolve("count"), new Expr.Num(7)],
            output: [new Expr.Resolve("Missing")])));

        Assert.IsType<EvalError.BadOpenForm>(error);
    }

    /// <summary>
    /// Runtime duplicate-property validation. The parser reports "Property 'X'
    /// is already defined", so this check is pure host-AST defense.
    /// </summary>
    [Fact]
    public void DuplicateProperty_IsRejected_OnlyFromAPrebuiltAst()
    {
        var error = FailsWith(Program(Root(
            properties:
            [
                new Property("X", Value(1)),
                new Property("X", Value(2)),
            ],
            output: [new Expr.Resolve("X")])));

        var duplicate = Assert.IsType<EvalError.DuplicateProperty>(error);
        Assert.Equal("X", duplicate.Name);
    }

    /// <summary>
    /// A spread whose operand has no output must report the spread-specific
    /// error, not the plain missing-output one. Track 4 aligned Lean and C# on
    /// exactly this distinction; the surface spelling is reachable, and this
    /// pins the prebuilt-AST route to the same branch so a host cannot observe
    /// a different verdict.
    /// </summary>
    [Fact]
    public void SpreadOfAnOutputlessBlock_ReportsTheSpreadSpecificError()
    {
        var outputless = new Algorithm.User(
            Parent: null, Parameters: [], Opens: [],
            Properties: [new Property("Q", Value(1))], Output: []);

        var error = FailsWith(Program(Root(
            output: [new Expr.SequenceSpread(new Expr.AlgorithmExpr(outputless))])));

        Assert.IsType<EvalError.SpreadMissingOutput>(error);
    }

    /// <summary>
    /// The same program written in KatLang reaches the same branch, so the
    /// prebuilt-AST route above is defense, not a second semantics.
    /// </summary>
    [Fact]
    public void SpreadOfAnOutputlessBlock_AgreesWithTheSurfaceSpelling()
    {
        var parsed = Parser.Parse("A = {\n    Q = 1\n}\nA*");
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));

        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(result.IsError);
        Assert.IsType<EvalError.SpreadMissingOutput>(Innermost(result.Error));
    }

    // ── Math native-call arity gate (bug-hunt B5a) ──────────────────────────
    //
    // `Expr.NativeCall` is publicly host-constructible for Math compatibility, and
    // the registry builds every runtime Math wrapper as `NativeCall(member.Name,
    // parameterNames)` with EXACTLY the member's arity. The shared pure
    // `ApplyMathNative` then reads fixed argument positions, so a host-built call
    // whose ArgNames list was SHORTER than the arity escaped as a CLR
    // IndexOutOfRangeException out of Run, RunAsync, and RunFlat. The gate lives in
    // that one shared implementation (both dispatch twins call it), sits AFTER
    // argument binding, and is driven by the registry's descriptor table. Pinned
    // policy: the count must EQUAL the arity — a surplus name is rejected too
    // (before this change it was silently tolerated), mirroring the exact
    // host-operation signature rule.

    /// <summary>
    /// Every Math FUNCTION member of the live registry table, so a member added
    /// later is covered without a bespoke row (the coverage pin below proves the
    /// partition).
    /// </summary>
    public static IEnumerable<object[]> MathFunctionMembers()
        => BuiltinRegistry.MathMembers
            .Where(static member => member.Kind != MathMemberKind.Constant)
            .Select(static member => new object[] { member.Name });

    private static MathMemberDescriptor FunctionMember(string name)
    {
        var member = Assert.Single(BuiltinRegistry.MathMembers, candidate => candidate.Name == name);
        Assert.NotEqual(MathMemberKind.Constant, member.Kind);
        return member;
    }

    private static string ExpectedArityReason(string memberName, int arity, int supplied)
        => $"invalid native-call signature for Math.{memberName}: expected {arity} argument name(s), got {supplied}";

    /// <summary>
    /// A host-built wrapper of the registry's runtime shape — parameters plus a
    /// <c>NativeCall</c> body — except that the native call's ArgNames list is
    /// chosen by the test. The zero-argument property <c>Value</c> calls it with
    /// one benign argument per wrapper parameter (or the supplied arguments), so
    /// every wrapper parameter is value-bound and the only thing under test is
    /// the ArgNames list handed to native dispatch; routing the call through a
    /// zero-argument property additionally makes the run touch the property
    /// cache seam, which selects the async TWIN family below. Value-bound native
    /// arguments themselves touch no cache seam; algorithm-channel native reads
    /// are covered by AsyncDispatchExhaustivenessTests.
    /// </summary>
    private static Expr NativeWrapperProgram(
        string nativeName,
        IReadOnlyList<string> wrapperParameters,
        IReadOnlyList<string> argNames,
        IReadOnlyList<Expr>? callArguments = null)
    {
        var wrapper = new Algorithm.User(
            Parent: null,
            Parameters: Algorithm.NormalParameters(wrapperParameters),
            Opens: [],
            Properties: [],
            Output: [new Expr.NativeCall(nativeName, argNames)]);
        var arguments = callArguments
            ?? wrapperParameters.Select(static (_, index) => (Expr)new Expr.Num(index + 1)).ToArray();
        var call = new Expr.Call(new Expr.Resolve("Wrapper"), new OutputBundle(arguments));
        var value = new Algorithm.User(Parent: null, Parameters: [], Opens: [], Properties: [], Output: [call]);
        return Program(Root(
            properties: [new Property("Wrapper", wrapper), new Property("Value", value)],
            output: [new Expr.Resolve("Value")]));
    }

    private static string IllegalReason(EvalResult<Result> result)
    {
        Assert.True(result.IsError, "Expected the arity gate to reject this AST.");
        return Assert.IsType<EvalError.IllegalInEval>(Innermost(result.Error)).Reason;
    }

    private static string IllegalReason(EvalResult<IReadOnlyList<Decimal128>> result)
    {
        Assert.True(result.IsError, "Expected the arity gate to reject this AST.");
        return Assert.IsType<EvalError.IllegalInEval>(Innermost(result.Error)).Reason;
    }

    /// <summary>
    /// One ArgName below the arity: before the gate this was
    /// <c>IndexOutOfRangeException</c> out of <c>Evaluator.Run</c> (FailsWith lets
    /// any exception escape, so passing here IS the no-throw assertion).
    /// </summary>
    [Theory]
    [MemberData(nameof(MathFunctionMembers))]
    public void MathNativeCall_OneArgumentNameBelowArity_IsRejectedStructurally(string memberName)
    {
        var member = FunctionMember(memberName);
        var parameters = Enumerable.Range(0, member.Arity).Select(static i => $"p{i}").ToArray();
        var argNames = parameters.Take(member.Arity - 1).ToArray();

        var error = FailsWith(NativeWrapperProgram(member.Name, parameters, argNames));

        var illegal = Assert.IsType<EvalError.IllegalInEval>(error);
        Assert.Equal(ExpectedArityReason(member.Name, member.Arity, argNames.Length), illegal.Reason);
    }

    /// <summary>
    /// Pinned extra-name policy: the ArgNames count must EQUAL the registry
    /// arity. A surplus name is silently-ignored binding metadata the
    /// registry-built wrappers never carry, so it is rejected like the
    /// host-operation signature rule rejects it — not tolerated as before.
    /// </summary>
    [Theory]
    [MemberData(nameof(MathFunctionMembers))]
    public void MathNativeCall_OneArgumentNameAboveArity_IsRejectedToo(string memberName)
    {
        var member = FunctionMember(memberName);
        var parameters = Enumerable.Range(0, member.Arity + 1).Select(static i => $"p{i}").ToArray();

        var error = FailsWith(NativeWrapperProgram(member.Name, parameters, parameters));

        var illegal = Assert.IsType<EvalError.IllegalInEval>(error);
        Assert.Equal(ExpectedArityReason(member.Name, member.Arity, parameters.Length), illegal.Reason);
    }

    /// <summary>
    /// The theories above are driven by the live registry table, so a future
    /// member cannot escape them. This pins the partition explicitly: every table
    /// member is either a function member — covered, with an arity of at least
    /// one so "one below" exists, and known to the gate's arity lookup — or a
    /// constant, which evaluates as <c>Expr.Num</c>, never reaches native
    /// dispatch, and is deliberately unknown to the gate.
    /// </summary>
    [Fact]
    public void ArityGateTheories_CoverEveryMathFunctionMemberOfTheRegistry()
    {
        var covered = MathFunctionMembers().Select(static row => (string)row[0]).ToHashSet(StringComparer.Ordinal);
        var runtime = BuiltinRegistry.CreateMathAlgorithm(MathAlgorithmFlavor.Runtime);

        foreach (var member in BuiltinRegistry.MathMembers)
        {
            var runtimeMember = Assert.Single(
                runtime.Properties,
                property => property.Name == member.Name);
            var output = Assert.Single(Assert.IsType<Algorithm.User>(runtimeMember.Value).Output);
            if (member.Kind == MathMemberKind.Constant)
            {
                Assert.Equal(0, member.Arity);
                Assert.IsType<Expr.Num>(output);
                Assert.DoesNotContain(member.Name, covered);
                Assert.False(BuiltinRegistry.TryGetMathFunctionArity(member.Name, out _));
            }
            else
            {
                Assert.True(member.Arity >= 1, $"{member.Name} has arity {member.Arity}");
                Assert.Contains(member.Name, covered);
                Assert.True(BuiltinRegistry.TryGetMathFunctionArity(member.Name, out var arity));
                Assert.Equal(member.Arity, arity);
                var native = Assert.IsType<Expr.NativeCall>(output);
                Assert.Equal(member.Name, native.FnName);
                Assert.Equal(member.Arity, native.ArgNames.Count);
            }
        }

        Assert.Equal(
            BuiltinRegistry.MathMembers.Count(static member => member.Kind != MathMemberKind.Constant),
            covered.Count);
    }

    /// <summary>
    /// Entry-point agreement: the synchronous entry points, the asynchronous fast
    /// path (which executes the synchronous pipeline inline), the flat
    /// projections, and the async TWIN family (selected by an async-capable cache,
    /// observed at the enclosing Value property) all answer
    /// with the same structured verdict — none of them throws.
    /// </summary>
    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(3)]
    public async Task MathNativeCallArityGate_AgreesAcrossEveryEvaluatorEntryPoint(int supplied)
    {
        // Every written name is bound, so only native signature validation rejects.
        var parameters = new[] { "x", "y", "z" };
        var program = NativeWrapperProgram("Pow", parameters, parameters.Take(supplied).ToArray());
        var expected = ExpectedArityReason("Pow", 2, supplied);

        Assert.Equal(expected, IllegalReason(Evaluator.Run(program)));
        Assert.Equal(expected, IllegalReason(Evaluator.RunFlat(program)));
        Assert.Equal(expected, IllegalReason(await Evaluator.RunAsync(program)));
        Assert.Equal(expected, IllegalReason(await Evaluator.RunFlatAsync(program)));

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var twin = await AsyncEvaluationHarness.Complete(Evaluator.RunAsync(program, cache));
        Assert.Equal(expected, IllegalReason(twin));
        Assert.True(cache.AsyncAccesses > 0, "The twin path must have served `Value` through the async cache seam.");
        Assert.Equal(0, cache.SyncAccesses);
    }

    /// <summary>
    /// The gate sits AFTER argument binding: an unbound ArgName is still the
    /// first failure, with too few names (binding never reaches the gate) and
    /// with the right count alike — the established ordering is unchanged.
    /// </summary>
    [Fact]
    public void MathNativeCall_UnboundArgumentName_StillReportsUnknownNameFirst()
    {
        var tooFew = FailsWith(NativeWrapperProgram("Pow", ["x", "y"], ["nope"]));
        Assert.Equal("nope", Assert.IsType<EvalError.UnknownName>(tooFew).Name);

        var exactCount = FailsWith(NativeWrapperProgram("Pow", ["x", "y"], ["x", "nope"]));
        Assert.Equal("nope", Assert.IsType<EvalError.UnknownName>(exactCount).Name);

        var tooMany = FailsWith(NativeWrapperProgram("Pow", ["x", "y"], ["x", "y", "nope"]));
        Assert.Equal("nope", Assert.IsType<EvalError.UnknownName>(tooMany).Name);
    }

    /// <summary>
    /// A native name that is no Math function member is not the gate's business:
    /// with any ArgNames count it still reaches the existing unknown-native arm.
    /// </summary>
    [Theory]
    [InlineData("NoSuchNative", 0)]
    [InlineData("NoSuchNative", 1)]
    [InlineData("Pi", 0)]
    [InlineData("Pi", 1)]
    [InlineData("sqrt", 0)]
    public void MathNativeCall_UnknownNativeName_StillReachesTheUnknownNativeArm(string name, int argNameCount)
    {
        var argNames = new[] { "x" }.Take(argNameCount).ToArray();

        var error = FailsWith(NativeWrapperProgram(name, ["x"], argNames));

        Assert.Equal($"unknown native function: {name}", Assert.IsType<EvalError.IllegalInEval>(error).Reason);
    }

    [Fact]
    public async Task MathNativeCall_NullNativeName_KeepsTheStructuredUnknownNativeError()
    {
        // Deliberately malformed host AST. Before the arity gate, a null name
        // reached the switch's default arm; dictionary lookup must not introduce
        // an ArgumentNullException in its place.
        var program = new Expr.NativeCall(null!, []);
        const string expected = "unknown native function: ";
        Assert.Equal(expected, IllegalReason(Evaluator.Run(program)));
        Assert.Equal(expected, IllegalReason(Evaluator.RunFlat(program)));
        Assert.Equal(expected, IllegalReason(await Evaluator.RunAsync(program)));
        Assert.Equal(expected, IllegalReason(await Evaluator.RunFlatAsync(program)));
        var twin = await AsyncEvaluationHarness.Complete(
            Evaluator.RunAsync(program, new PassThroughAsyncZeroArgPropertyResultCache()));
        Assert.Equal(expected, IllegalReason(twin));
    }

    [Theory]
    [MemberData(nameof(MathFunctionMembers))]
    public async Task MathNativeCall_EveryRegisteredFunctionDispatchesWithExactArity(string memberName)
    {
        var member = FunctionMember(memberName);
        var parameters = Enumerable.Range(0, member.Arity).Select(static i => $"p{i}").ToArray();
        // 1 for unary functions, (1, 2) for binary functions are admitted by every
        // current member, including random bounds. This must reach computation:
        // malformed-count tests alone pass even if a new member has no switch arm.
        var program = NativeWrapperProgram(member.Name, parameters, parameters);
        var sync = Evaluator.Run(program);
        Assert.True(sync.IsOk, sync.IsError ? sync.Error.ToString() : null);
        Assert.IsType<Result.Atom>(sync.Value);

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var twin = await AsyncEvaluationHarness.Complete(Evaluator.RunAsync(program, cache));
        Assert.True(twin.IsOk, twin.IsError ? twin.Error.ToString() : null);
        Assert.IsType<Result.Atom>(twin.Value);
        Assert.Equal(0, cache.SyncAccesses);
    }

    /// <summary>Positive control: a wrapper of the registry's exact shape still computes.</summary>
    [Fact]
    public void MathNativeCall_WithExactArity_StillComputes()
    {
        var program = NativeWrapperProgram("Sqrt", ["x"], ["x"], callArguments: [new Expr.Num(9)]);

        var result = Evaluator.Run(program);

        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        Assert.True(Result.ValueComparer.Equals(new Result.Atom(3), result.Value));
    }
}
