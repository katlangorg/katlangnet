using System.Text;

namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// Pins the VARIANT-OWNED payload contract of the public <see cref="Algorithm"/> hierarchy
/// against the compiled assembly, exactly as a NuGet consumer meets it (this project is
/// deliberately not a friend assembly): the base type carries no payload member, so a
/// consumer can neither give an algorithm payload its variant does not own — a builtin
/// with properties, a clause family with an output, a user algorithm with branches — nor
/// set payload through a base-typed value. Lean's inductive cannot represent those states;
/// here they are COMPILE errors, witnessed by the pinned SDK's own compiler, never runtime
/// exceptions. The same compiler must accept every legitimate construction and update, so
/// the negative verdicts cannot be vacuous.
///
/// <para>The runtime half pins what the type system cannot: the derived parameter
/// projections follow the one stored channel, structural equality covers exactly the
/// variant's own payload, and the Lean-total updates are the identity on the variants
/// that have no parameter list.</para>
/// </summary>
public class AlgorithmPublicSurfaceTests
{
    /// <summary>
    /// One invalid consumer statement per row: the payload it tries to give, the variant
    /// it targets, and the compiler error a consumer must get. The receiver is a
    /// non-null expression of the exact static type, so every row fails for the reason
    /// named and not for a missing constructor or an inaccessible type.
    /// </summary>
    private static readonly IReadOnlyList<(string Name, string Statement, string Code, string MemberNamed)> InvalidStates =
    [
        // Builtin + user payload.
        ("BuiltinProperties", "_ = Builtin with { Properties = [] };", "CS0117", "Properties"),
        ("BuiltinOutput", "_ = Builtin with { Output = OutputBundle.Empty };", "CS0117", "Output"),
        ("BuiltinOpens", "_ = Builtin with { Opens = [] };", "CS0117", "Opens"),
        ("BuiltinParent", "_ = Builtin with { Parent = null };", "CS0117", "Parent"),
        ("BuiltinPatterns", "_ = Builtin with { ParameterPatterns = [] };", "CS0117", "ParameterPatterns"),
        ("BuiltinInitializer", "_ = new Algorithm.Builtin(BuiltinId.count) { Output = OutputBundle.Empty };", "CS0117", "Output"),
        // Conditional + user payload.
        ("FamilyOutput", "_ = Family with { Output = OutputBundle.Empty };", "CS0117", "Output"),
        ("FamilyProperties", "_ = Family with { Properties = [] };", "CS0117", "Properties"),
        ("FamilyPatterns", "_ = Family with { ParameterPatterns = [] };", "CS0117", "ParameterPatterns"),
        ("FamilyExplicitList", "_ = Family with { HasExplicitParameterList = true };", "CS0117", "HasExplicitParameterList"),
        // User + conditional payload.
        ("UserBranches", "_ = User with { Branches = [] };", "CS0117", "Branches"),
        // Base-typed writes: no payload member exists on Algorithm.
        ("BaseOpens", "_ = Base with { Opens = [] };", "CS0117", "Opens"),
        ("BaseProperties", "_ = Base with { Properties = [] };", "CS0117", "Properties"),
        ("BaseOutput", "_ = Base with { Output = OutputBundle.Empty };", "CS0117", "Output"),
        ("BaseBranches", "_ = Base with { Branches = [] };", "CS0117", "Branches"),
        ("BaseParent", "_ = Base with { Parent = null };", "CS0117", "Parent"),
        // Derived projections are read-only: the one channel is ParameterPatterns.
        ("UserParameters", "_ = User with { Parameters = [] };", "CS0200", "Parameters"),
        ("UserParams", "_ = User with { Params = [] };", "CS0200", "Params"),
        // The former parallel explicit lists no longer exist.
        ("UserExplicitParameters", "_ = User with { ExplicitParameters = [] };", "CS0117", "ExplicitParameters"),
        ("UserExplicitPatterns", "_ = User with { ExplicitParameterPatterns = [] };", "CS0117", "ExplicitParameterPatterns"),
        // Base-typed reads and variant-specific helpers on the wrong variant.
        ("BaseReadProperties", "_ = Base.Properties;", "CS1061", "Properties"),
        ("BaseReadParams", "_ = Base.Params;", "CS1061", "Params"),
        ("FamilyReadProperties", "_ = Family.Properties;", "CS1061", "Properties"),
        ("UserReadBranches", "_ = User.Branches;", "CS1061", "Branches"),
        ("BaseDuplicateProperty", "_ = Base.FindDuplicatePropName();", "CS1061", "FindDuplicatePropName"),
        ("FamilyDuplicateProperty", "_ = Family.FindDuplicatePropName();", "CS1061", "FindDuplicatePropName"),
        ("UserDuplicateBranches", "_ = User.HasDuplicateBranchPatterns();", "CS1061", "HasDuplicateBranchPatterns"),
        ("BuiltinExplicitList", "_ = Builtin.HasExplicitParameterList;", "CS1061", "HasExplicitParameterList"),
    ];

    private const string ProbePreamble = """
        using System.Collections.Generic;
        using KatLang;
        namespace Consumer;
        public static class Fixtures
        {
            public static readonly Algorithm.User User = new(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Param("x")]);
            public static readonly Algorithm.Conditional Family = new(null, [], [new CondBranch(new Pattern.Bind("x"), User)]);
            public static readonly Algorithm.Builtin Builtin = new(BuiltinId.count);
            public static Algorithm Base => User;
        }

        """;

    [Fact]
    public void PayloadAVariantDoesNotOwn_CannotBeSetOrRead_ByAConsumer()
    {
        // Every invalid state in one compilation, one method per row so each verdict is
        // attributable: the compiler must report exactly the named error for each row and
        // nothing else (an unrelated error would mean a probe was stopped for the wrong
        // reason and proves nothing about ownership).
        var source = new StringBuilder(ProbePreamble);
        source.Append("public static class Invalid\n{\n");
        foreach (var (name, statement, _, _) in InvalidStates)
        {
            source.Append($"    public static void {name}()\n    {{\n");
            source.Append("        var User = Fixtures.User; var Family = Fixtures.Family; var Builtin = Fixtures.Builtin; var Base = Fixtures.Base;\n");
            source.Append("        _ = (User, Family, Builtin, Base);\n");
            source.Append("        ").Append(statement).Append('\n');
            source.Append("    }\n");
        }

        source.Append("}\n");

        var compilation = ConsumerCompiler.Compile(source.ToString(), "algorithm-ownership");

        Assert.NotEqual(0, compilation.ExitCode);
        var lines = source.ToString().Split('\n');
        foreach (var (name, statement, code, memberNamed) in InvalidStates)
        {
            // Each verdict is attributed by LINE (the statement is unique per row), so a row
            // cannot pass on another row's refusal of the same member name.
            var line = Array.FindIndex(lines, l => l.Contains(statement, StringComparison.Ordinal)) + 1;
            Assert.True(line > 0, $"probe {name} not found in the generated source");
            var diagnostic = Assert.Single(
                compilation.Diagnostics,
                d => d.Line == line);
            Assert.True(
                diagnostic.Code == code && diagnostic.Message.Contains(memberNamed, StringComparison.Ordinal),
                $"{name}: expected {code} naming {memberNamed} for `{statement}`; got {diagnostic.Code}: {diagnostic.Message}"
                + Environment.NewLine + compilation.Output);
        }

        // Exactly one refusal per row: the only errors are the ownership refusals.
        Assert.Equal(InvalidStates.Count, compilation.Diagnostics.Count);
    }

    [Fact]
    public void EveryLegitimateConstructionAndUpdate_CompilesForAConsumer()
    {
        // The positive control: each variant is constructed with, updated through, and read
        // by its OWN payload; the typed roots need no pattern match; a consumer switch over
        // the closed hierarchy reads variant payload per arm with no catch-all arm; and
        // consumers that hold a base-typed value narrow to update.
        const string source = ProbePreamble + """
            public static class Valid
            {
                public static Algorithm.User UpdateUser(Algorithm.User user) => user with
                {
                    Parent = new ScopeCtx(null, [], []),
                    ParameterPatterns = [new SequenceValueParameterPattern([new CaptureParameterPattern("a"), new CaptureParameterPattern("b", Kind: ParameterKind.Collecting)])],
                    Opens = [new Expr.Resolve("Math")],
                    Properties = [new Property("P", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))],
                    Output = [new Expr.Num(2)],
                    HasExplicitParameterList = true,
                };

                public static Algorithm.Conditional UpdateFamily(Algorithm.Conditional family) => family with
                {
                    Parent = new ScopeCtx(null, [], []),
                    Opens = [new Expr.Resolve("Math")],
                    Branches = [new CondBranch(new Pattern.LitInt(0), Fixtures.User)],
                };

                public static Algorithm.Builtin UpdateBuiltin(Algorithm.Builtin builtin) => builtin with { Id = BuiltinId.sum };

                public static int ReadUser(Algorithm.User user)
                    => user.Parameters.Count + user.Params.Count + user.ParameterPatterns.Count + user.Opens.Count
                        + user.Properties.Count + user.Output.Count + (user.HasExplicitParameterList ? 1 : 0)
                        + (user.FindDuplicatePropName() is null ? 0 : 1) + (user.Parent is null ? 0 : 1);

                public static int ReadFamily(Algorithm.Conditional family)
                    => family.Branches.Count + family.Opens.Count + (family.HasDuplicateBranchPatterns() ? 1 : 0) + (family.Parent is null ? 0 : 1);

                public static int Classify(Algorithm algorithm) => algorithm switch
                {
                    Algorithm.User user => ReadUser(user),
                    Algorithm.Conditional family => ReadFamily(family),
                    Algorithm.Builtin builtin => (int)builtin.Id,
                };

                public static Algorithm Narrowed(Algorithm algorithm) => algorithm switch
                {
                    Algorithm.User user => user with { Output = [new Expr.Num(1)] },
                    Algorithm.Conditional family => family with { Branches = [] },
                    Algorithm.Builtin builtin => builtin,
                };

                public static Algorithm Total(Algorithm algorithm)
                    => algorithm.WithParams(["a"]).WithParameters([new ParameterDeclaration("b")]).WithParameterPatterns([new CaptureParameterPattern("c")]);

                public static IReadOnlyList<Property> RootProperties(string program)
                {
                    Algorithm.User root = Parser.Parse(program).Root;
                    var (deconstructedRoot, diagnostics) = Parser.Parse(program);
                    Algorithm.User typed = deconstructedRoot;
                    return root.Properties.Count + typed.Properties.Count + diagnostics.Count >= 0 ? root.Properties : typed.Properties;
                }

                public static Algorithm.User? RunRoot(string program) => KatLangEngine.Run(program) switch
                {
                    RunResult.Success success => success.Root,
                    RunResult.NoProgramOutput noOutput => noOutput.Root,
                    RunResult.EvalFailure failure => failure.Root,
                    RunResult.ParseFailure => null,
                };

                public static ParameterDeclaration CaptureLeaf(CaptureParameterPattern capture) => capture.Parameter;
            }

            """;

        var compilation = ConsumerCompiler.Compile(source, "algorithm-ownership-valid");

        Assert.True(
            compilation.ExitCode == 0 && compilation.Diagnostics.Count == 0,
            "Every legitimate variant-owned construction, update, and read must compile for a consumer."
            + Environment.NewLine + compilation.Output);
    }

    // ── Runtime half: what the type system cannot state ─────────────────────

    [Fact]
    public void Parameters_AndParams_AreProjectionsOfTheStoredPatterns()
    {
        var user = new Algorithm.User(
            null,
            [new CaptureParameterPattern("x"), new SequenceValueParameterPattern([new CaptureParameterPattern("y", Kind: ParameterKind.Collecting)])],
            [],
            [],
            [new Expr.Num(1)]);
        Assert.Equal(["x", "y"], user.Params);
        Assert.Equal(["x", "y"], user.Parameters.Select(p => p.Name));
        Assert.Equal(ParameterKind.Collecting, user.Parameters[1].Kind);
        Assert.Same(((CaptureParameterPattern)user.ParameterPatterns[0]).Parameter, user.Parameters[0]);

        // Replacing the channel replaces the projections; nothing is stored beside the channel.
        var replaced = user with { ParameterPatterns = [new CaptureParameterPattern("z")] };
        Assert.Equal(["z"], replaced.Params);
        Assert.Equal(["x", "y"], user.Params);

        // A caller-owned list is read through.
        var live = new List<ParameterPattern> { new CaptureParameterPattern("a") };
        var hosted = new Algorithm.User(null, live, [], [], [new Expr.Num(1)]);
        live.Add(new CaptureParameterPattern("b"));
        Assert.Equal(["a", "b"], hosted.Params);
        Assert.Equal(2, hosted.Parameters.Count);
    }

    [Fact]
    public void ExplicitListBit_IsSetByClauseElaboration_AndIsPartOfTheValue()
    {
        var body = new Algorithm.User(null, [], [], [], [new Expr.Param("x")]);
        var ordinary = Assert.IsType<Algorithm.User>(
            Algorithm.ElaborateClauseDefinition(new Pattern.SequenceValue([new Pattern.Bind("x")]), body));
        Assert.True(ordinary.HasExplicitParameterList);
        Assert.Equal(["x"], ordinary.Params);
        Assert.False(body.HasExplicitParameterList);

        // A host-built inferred signature and a written list with the same patterns are
        // different values: the bit is variant payload like any other.
        var patterns = ordinary.ParameterPatterns;
        var inferred = new Algorithm.User(null, patterns, [], [], body.Output);
        var written = inferred with { HasExplicitParameterList = true };
        Assert.NotEqual(inferred, written);
        Assert.Equal(written, written with { });

        // The total update is the identity on a body that has no parameter list.
        var builtinBody = new Algorithm.Builtin(BuiltinId.count);
        Assert.Same(builtinBody, Algorithm.ElaborateClauseDefinition(new Pattern.SequenceValue([new Pattern.Bind("x")]), builtinBody));
    }

    [Fact]
    public void StructuralEquality_CoversExactlyTheVariantsOwnPayload()
    {
        IReadOnlyList<ParameterPattern> patterns = [new CaptureParameterPattern("x")];
        IReadOnlyList<Expr> opens = [];
        IReadOnlyList<Property> properties = [];
        OutputBundle output = [new Expr.Param("x")];
        var first = new Algorithm.User(null, patterns, opens, properties, output);
        var second = new Algorithm.User(null, patterns, opens, properties, output);
        Assert.Equal(first, second);
        Assert.Equal(first.GetHashCode(), second.GetHashCode());
        Assert.NotEqual(first, first with { Output = [new Expr.Num(1)] });
        Assert.NotEqual(first, first with { ParameterPatterns = [new CaptureParameterPattern("y")] });
        Assert.Equal(first, first with { ParameterPatterns = patterns });

        IReadOnlyList<CondBranch> branches = [new CondBranch(new Pattern.Bind("x"), first)];
        Assert.Equal(new Algorithm.Conditional(null, opens, branches), new Algorithm.Conditional(null, opens, branches));
        Assert.NotEqual(new Algorithm.Conditional(null, opens, branches), new Algorithm.Conditional(null, opens, []));
        Assert.Equal(new Algorithm.Builtin(BuiltinId.count), new Algorithm.Builtin(BuiltinId.count));
        Assert.NotEqual(new Algorithm.Builtin(BuiltinId.count), new Algorithm.Builtin(BuiltinId.sum));

        // The three variants never compare equal to one another, whatever they hold.
        Assert.NotEqual<Algorithm>(new Algorithm.Conditional(null, [], []), new Algorithm.User(null, [], [], [], []));
        Assert.NotEqual<Algorithm>(new Algorithm.Builtin(BuiltinId.count), new Algorithm.User(null, [], [], [], []));
    }

    [Fact]
    public void Copies_PreserveTheVariantsOwnPayload()
    {
        var parent = new ScopeCtx(null, [], []);
        var user = new Algorithm.User(
            parent,
            [new CaptureParameterPattern("x")],
            [new Expr.Resolve("Math")],
            [new Property("P", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))],
            [new Expr.Param("x")])
        {
            HasExplicitParameterList = true,
        };
        var userCopy = user with { Output = [new Expr.Num(2)] };
        Assert.Same(user.Parent, userCopy.Parent);
        Assert.Same(user.ParameterPatterns, userCopy.ParameterPatterns);
        Assert.Same(user.Opens, userCopy.Opens);
        Assert.Same(user.Properties, userCopy.Properties);
        Assert.True(userCopy.HasExplicitParameterList);
        Assert.Equal(["x"], userCopy.Params);

        var family = new Algorithm.Conditional(parent, [new Expr.Resolve("Math")], [new CondBranch(new Pattern.Bind("x"), user)]);
        var familyCopy = family with { Opens = [] };
        Assert.Same(family.Parent, familyCopy.Parent);
        Assert.Same(family.Branches, familyCopy.Branches);
        Assert.Empty(familyCopy.Opens);

        var builtin = new Algorithm.Builtin(BuiltinId.count);
        Assert.Equal(BuiltinId.sum, (builtin with { Id = BuiltinId.sum }).Id);
        Assert.Equal(BuiltinId.count, builtin.Id);
    }

    [Fact]
    public void RootsOfParseAndRunResults_AreUserAlgorithms()
    {
        // Typed at compile time (see the consumer probe) and true at run time for every
        // shape of program the pipeline can produce: a normal program, a source that only
        // defines properties, one with an evaluation error, and unparseable or oversized
        // recovery placeholders.
        var parsed = Parser.Parse("A = 1\nA");
        Assert.False(parsed.HasErrors);
        Assert.Equal(["A"], parsed.Root.Properties.Select(p => p.Name));
        var oversized = Parser.Parse(new string('1', SourceProcessingLimits.MaxSupportedSourceLength + 1));
        Assert.True(oversized.HasErrors);
        Assert.Empty(oversized.Root.Properties);
        Assert.Empty(oversized.Root.Output);
        var recovered = Parser.Parse("this is not ) katlang");
        Assert.True(recovered.HasErrors);
        Assert.Empty(recovered.Root.Properties);

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("A = 1\nA"));
        Assert.Equal(["A"], success.Root.Properties.Select(p => p.Name));
        var noOutput = Assert.IsType<RunResult.NoProgramOutput>(KatLangEngine.Run("A = 1"));
        Assert.Equal(["A"], noOutput.Root.Properties.Select(p => p.Name));
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("1 / 0"));
        Assert.Single(failure.Root.Output);
    }
}
