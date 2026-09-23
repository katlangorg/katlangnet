using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Name-resolution audit #8 (September 2026). Two halves:
/// <list type="number">
/// <item>A GENERATED cross-layer resolution matrix: three nested owners, each declaring the
/// probed name as nothing, a property, a parameter, or through an <c>open</c>; a root that
/// declares it as nothing, a property, or through a root <c>open</c>; with and without a host
/// operation of the same name. An INDEPENDENT oracle states the documented ordered model
/// (owner walk — parameter before property per level, prelude outermost — then opens level by
/// level, then promotion); every program is checked against it in every layer that answers
/// the question: the runtime (sync engine, forced-async twin, generic and planned evaluator),
/// the editor model (classification and declaration identity at the reference), and parameter
/// detection (whether the name was promoted). Perturbations — redundant parentheses around the
/// reference, and an unrelated property plus an unrelated opened provider at every level —
/// must change nothing. Because every combination is in the matrix, adding one legitimate
/// nearer declaration is pinned too: that program is another row, and all layers must switch
/// to the new declaration together.</item>
/// <item>Focused regressions for the defects the audit repaired (see
/// <c>docs/design/language-rules/ownership-and-lookup.md</c>).</item>
/// </list>
/// </summary>
public class NameResolutionAuditTests
{
    // ── The generated matrix ────────────────────────────────────────────────

    public enum LevelDeclaration { None, Property, Parameter, Open }

    public enum RootDeclaration { None, Property, Open }

    private const int RootPropertySentinel = 7;
    private const int RootOpenSentinel = 30;
    private const int HostOperationSentinel = 99;

    private static int PropertySentinel(int level) => 10 + level;
    private static int ArgumentSentinel(int level) => 20 + level;
    private static int OpenSentinel(int level) => 30 + level;

    /// <summary>What the oracle says the reference denotes.</summary>
    private sealed record Expected(
        int? Value,
        IdentifierClassification Classification,
        (int Line, int Column)? Declaration,
        bool Promoted);

    private sealed class MatrixSource
    {
        private readonly List<string> _lines = [];

        public Dictionary<string, (int Line, int Column)> Sites { get; } = new(StringComparer.Ordinal);

        public void Line(string text) => _lines.Add(text);

        /// <summary>Appends a line and records the column of <paramref name="token"/> in it (1-based).</summary>
        public void Line(string text, string key, string token, int occurrence = 1)
        {
            var index = -1;
            for (var i = 0; i < occurrence; i++)
                index = text.IndexOf(token, index + 1, StringComparison.Ordinal);
            Assert.True(index >= 0, $"token '{token}' not in '{text}'");
            _lines.Add(text);
            Sites[key] = (_lines.Count, index + 1);
        }

        public string Text => string.Join("\n", _lines);
    }

    private static (string Source, Dictionary<string, (int Line, int Column)> Sites) BuildProgram(
        LevelDeclaration[] levels,
        RootDeclaration root,
        bool redundantParentheses,
        bool unrelatedNoise)
    {
        var source = new MatrixSource();
        if (root == RootDeclaration.Open)
            source.Line(unrelatedNoise ? "open Lp0, U" : "open Lp0");
        else if (unrelatedNoise)
            source.Line("open U");

        for (var i = 0; i <= 3; i++)
        {
            source.Line($"Lp{i} = {{");
            source.Line($"    public p = {30 + i}", $"open{i}", "p =");
            source.Line("}");
        }

        source.Line("U = {");
        source.Line("    public u = 5");
        source.Line("}");
        if (unrelatedNoise)
            source.Line("w = 6");
        if (root == RootDeclaration.Property)
            source.Line($"p = {RootPropertySentinel}", "rootProperty", "p");

        for (var level = 1; level <= 3; level++)
        {
            var indent = new string(' ', 4 * (level - 1));
            var inner = new string(' ', 4 * level);
            var declaration = levels[level - 1];
            if (declaration == LevelDeclaration.Parameter)
                source.Line($"{indent}N{level}(p) = {{", $"parameter{level}", "p");
            else
                source.Line($"{indent}N{level} = {{");

            if (declaration == LevelDeclaration.Open)
                source.Line(unrelatedNoise ? $"{inner}open Lp{level}, U" : $"{inner}open Lp{level}");
            else if (unrelatedNoise)
                source.Line($"{inner}open U");

            if (unrelatedNoise)
                source.Line($"{inner}w{level} = u + {level}");
            if (declaration == LevelDeclaration.Property)
                source.Line($"{inner}p = {PropertySentinel(level)}", $"property{level}", "p");
        }

        source.Line($"{new string(' ', 12)}{(redundantParentheses ? "((p))" : "p")}", "reference", "p");
        for (var level = 3; level >= 1; level--)
        {
            // Close N{level}, then call it as the output row of the enclosing body.
            var indent = new string(' ', 4 * (level - 1));
            source.Line($"{indent}}}");
            source.Line(indent + (levels[level - 1] == LevelDeclaration.Parameter ? $"N{level}({ArgumentSentinel(level)})" : $"N{level}"));
        }

        return (source.Text, source.Sites);
    }

    /// <summary>
    /// The independent statement of the model. Validity: a property may not share its name
    /// with a parameter of its own or an enclosing owner. Selection: the owner walk from the
    /// reference's owner outward — parameter before property at each level — then the root's
    /// property and the prelude (the host operation), then the open providers level by level,
    /// innermost first; nothing at all promotes the name.
    /// </summary>
    private static (bool Valid, Expected Expected) Oracle(
        LevelDeclaration[] levels, RootDeclaration root, bool hostOperation,
        Dictionary<string, (int Line, int Column)> sites)
    {
        var valid = true;
        for (var property = 1; property <= 3; property++)
        {
            if (levels[property - 1] != LevelDeclaration.Property)
                continue;
            for (var owner = 1; owner <= property; owner++)
                valid &= levels[owner - 1] != LevelDeclaration.Parameter;
        }

        for (var level = 3; level >= 1; level--)
        {
            if (levels[level - 1] == LevelDeclaration.Parameter)
                return (valid, new(ArgumentSentinel(level), IdentifierClassification.ExplicitParameterReference, sites[$"parameter{level}"], false));
            if (levels[level - 1] == LevelDeclaration.Property)
                return (valid, new(PropertySentinel(level), IdentifierClassification.PropertyReference, sites[$"property{level}"], false));
        }

        if (root == RootDeclaration.Property)
            return (valid, new(RootPropertySentinel, IdentifierClassification.PropertyReference, sites["rootProperty"], false));
        if (hostOperation)
            return (valid, new(HostOperationSentinel, IdentifierClassification.Builtin, null, false));

        for (var level = 3; level >= 1; level--)
        {
            if (levels[level - 1] == LevelDeclaration.Open)
                return (valid, new(OpenSentinel(level), IdentifierClassification.PropertyReference, sites[$"open{level}"], false));
        }

        if (root == RootDeclaration.Open)
            return (valid, new(RootOpenSentinel, IdentifierClassification.PropertyReference, sites["open0"], false));

        return (valid, new(null, IdentifierClassification.ImplicitParameterReference, null, true));
    }

    public static TheoryData<string> MatrixIds()
    {
        var data = new TheoryData<string>();
        foreach (var l1 in Enum.GetValues<LevelDeclaration>())
            foreach (var l2 in Enum.GetValues<LevelDeclaration>())
                foreach (var l3 in Enum.GetValues<LevelDeclaration>())
                    foreach (var root in Enum.GetValues<RootDeclaration>())
                        foreach (var host in new[] { false, true })
                            data.Add($"{l1}-{l2}-{l3}/root-{root}/{(host ? "host" : "plain")}");
        return data;
    }

    private static RunOptions HostOptions(bool asynchronous)
    {
        var operations = new List<HostOperation>
        {
            HostOperation.Create("p", static (_, _) => new Result.Atom(HostOperationSentinel)),
        };
        if (asynchronous)
        {
            operations.Add(HostOperation.CreateAsync("ZzForceAsync", static async (_, _) =>
            {
                await Task.Yield();
                return new Result.Atom(0);
            }));
        }

        return new RunOptions { HostOperations = HostOperations.Create([.. operations]) };
    }

    private static RunOptions ForcedAsyncOnlyOptions()
        => new()
        {
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("ZzForceAsync", static async (_, _) =>
            {
                await Task.Yield();
                return new Result.Atom(0);
            })),
        };

    [Theory]
    [MemberData(nameof(MatrixIds))]
    public async Task ResolutionMatrix_EveryLayerSelectsTheOracleDeclaration(string id)
    {
        var parts = id.Split('/');
        var levels = parts[0].Split('-').Select(Enum.Parse<LevelDeclaration>).ToArray();
        var root = Enum.Parse<RootDeclaration>(parts[1]["root-".Length..]);
        var hostOperation = parts[2] == "host";

        foreach (var (parentheses, noise) in new[] { (false, false), (true, false), (false, true), (true, true) })
        {
            var (source, sites) = BuildProgram(levels, root, parentheses, noise);
            var (valid, expected) = Oracle(levels, root, hostOperation, sites);
            var context = $"[{id} parens={parentheses} noise={noise}]\n{source}";
            var options = hostOperation ? HostOptions(asynchronous: false) : null;
            var parsed = options is null ? Parser.Parse(source) : Parser.Parse(source, options);

            if (!valid)
            {
                Assert.True(parsed.Diagnostics.Count > 0, context);
                Assert.All(parsed.Diagnostics, d => Assert.Equal(DiagnosticCode.ParameterPropertyCollision, d.Code));
            }
            else
            {
                Assert.True(parsed.Diagnostics.Count == 0,
                    $"{context}\n{string.Join(" | ", parsed.Diagnostics.Select(d => d.Message))}");
            }

            // Editor: the same declaration (or the same promotion / prelude member) at the
            // reference — also in recovery trees, whose owner walk is the same one.
            var model = SemanticModelBuilder.Build(parsed);
            var reference = sites["reference"];
            var resolution = model.FindResolutionAt(new SourcePosition(reference.Line, reference.Column));
            Assert.True(resolution is not null, context);
            Assert.True(expected.Classification == resolution!.Classification,
                $"{context}\neditor classified {resolution.Classification}, oracle {expected.Classification}");
            var declared = resolution.ResolvedDeclaration?.Span.Start;
            Assert.True(
                (expected.Declaration is null && declared is null)
                || (expected.Declaration is { } site && declared is { } start && start.Line == site.Line && start.Column == site.Column),
                $"{context}\neditor declaration {declared}, oracle {expected.Declaration}");

            // Detector: the name was promoted exactly when nothing declares or provides it.
            Assert.Equal(expected.Promoted, ContainsInferredParameter(parsed.Root, "p"));

            if (!valid)
                continue;

            // Runtime, every execution path.
            var run = KatLangEngine.Run(source, options);
            if (expected.Value is { } value)
            {
                var success = Assert.IsType<RunResult.Success>(run);
                Assert.True(new Result.Atom(value) == success.Value, $"{context}\nruntime {success.ToDisplayString()}, oracle {value}");

                var asyncRun = await KatLangEngine.RunAsync(source, hostOperation ? HostOptions(asynchronous: true) : ForcedAsyncOnlyOptions());
                Assert.Equal(success.ToDisplayString(), Assert.IsType<RunResult.Success>(asyncRun).ToDisplayString());

                if (!hostOperation)
                {
                    var planned = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
                    var generic = Evaluator.Run(
                        new Expr.AlgorithmExpr(parsed.Root),
                        new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(),
                        enableLoopOptimization: false,
                        loopDiagnostics: null,
                        enableSequencePipelineOptimization: false,
                        sequenceDiagnostics: null);
                    Assert.Equal(new Result.Atom(value), planned.Value);
                    Assert.Equal(new Result.Atom(value), generic.Value);
                }
            }
            else
            {
                // The promoted name lifts through N3, N2, and N1; the root row `N1` then
                // demands a one-parameter property with no argument (the root is never called).
                var failure = Assert.IsType<RunResult.EvalFailure>(run);
                var error = Assert.Single(failure.Errors);
                Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
                Assert.Contains("An implicit parameter 'p' was inferred", error.Message, StringComparison.Ordinal);
            }
        }
    }

    [Fact]
    public void ResolutionMatrix_CoversEveryOutcomeKind()
    {
        var kinds = new HashSet<IdentifierClassification>();
        var invalid = 0;
        foreach (var l1 in Enum.GetValues<LevelDeclaration>())
            foreach (var l2 in Enum.GetValues<LevelDeclaration>())
                foreach (var l3 in Enum.GetValues<LevelDeclaration>())
                    foreach (var root in Enum.GetValues<RootDeclaration>())
                        foreach (var host in new[] { false, true })
                        {
                            LevelDeclaration[] levels = [l1, l2, l3];
                            var (_, sites) = BuildProgram(levels, root, false, false);
                            var (valid, expected) = Oracle(levels, root, host, sites);
                            kinds.Add(expected.Classification);
                            invalid += valid ? 0 : 1;
                        }

        Assert.Equal(
            new[]
            {
                IdentifierClassification.PropertyReference,
                IdentifierClassification.ExplicitParameterReference,
                IdentifierClassification.ImplicitParameterReference,
                IdentifierClassification.Builtin,
            }.Order(),
            kinds.Order());
        Assert.True(invalid > 0, "the matrix must also exercise recovery trees");
    }

    private static bool ContainsInferredParameter(Algorithm algorithm, string name)
    {
        if (algorithm is Algorithm.User { HasExplicitParameterList: false } user && user.Params.Contains(name))
            return true;

        foreach (var property in algorithm.Properties)
        {
            if (ContainsInferredParameter(property.Value, name))
                return true;
        }

        return false;
    }

    // ── D2: closed-list diagnostics are positioned at the FREE occurrence ────

    [Theory]
    [InlineData("F(n) = {\n    X = 1\n    X\n} + X\nF(1)", 4, 5, "used in an explicitly parameterized algorithm")]
    [InlineData("F(0) = {\n    X = 1\n    X\n} + X\nF(n) = n\nF(0)", 4, 5, "used in conditional branch 'F'")]
    public void UndeclaredIdentifier_IsPositionedAtTheFreeOccurrence_NeverAtABoundNestedOne(
        string source, int line, int column, string fragment)
    {
        // The block's own `X` (line 3) resolves to the block's property; only the `X` after
        // the block (line 4) is free at the closed level. The span search used to descend into
        // the block and report the bound occurrence.
        var diagnostic = Assert.Single(SourceProvenance.ParseAllowingDiagnostics(source).Diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Contains(fragment, diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(line, column, line, column + 1), diagnostic.Span);
    }

    [Fact]
    public void UndeclaredIdentifier_InsideANestedBlockOfAClosedList_IsStillReportedAtItsOwnOccurrence()
    {
        var diagnostic = Assert.Single(SourceProvenance.ParseAllowingDiagnostics("F(n) = {\n    X + 1\n}\nF(1)").Diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Equal(new SourceSpan(2, 5, 2, 6), diagnostic.Span);
    }

    // ── D3: every open target must resolve, statically ───────────────────────

    [Theory]
    [InlineData("A = {\n    open Nope\n    1\n}\nA", "'Nope' cannot be opened because no property named 'Nope' is visible here")]
    [InlineData("Lib = {\n    public Y = 1\n}\nA = {\n    open Lib.Nope\n    1\n}\nA", "'Lib.Nope' cannot be opened because 'Lib' has no property named 'Nope'.")]
    [InlineData("Lib = {\n    Sub = {\n        public X = 1\n    }\n}\nA = {\n    open Lib.Sub\n    1\n}\nA", "'Lib.Sub' cannot be opened because property 'Sub' of 'Lib' is not public")]
    [InlineData("Lib = {\n    public F(0) = {\n        public Sub = { public X = 1 }\n        0\n    }\n    public F(n) = n\n}\nA = {\n    open Lib.F.Sub\n    1\n}\nA", "'Lib.F.Sub' cannot be opened because 'Sub' is declared only inside a conditional branch of 'Lib.F'")]
    [InlineData("Outer = {\n    public Lib = {\n        public X = 1\n    }\n}\nA = {\n    open Outer, Lib\n    X\n}\nA", "'Lib' cannot be opened because no property named 'Lib' is visible here")]
    [InlineData("Lib = {\n    public X = 1\n}\nA = {\n    open Lib, Nope\n    X\n}\nA", "'Nope' cannot be opened because no property named 'Nope' is visible here")]
    public void OpenTargetThatResolvesToNothing_IsRefusedStatically_WhateverTheLookupsDo(string source, string message)
    {
        var diagnostic = Assert.Single(SourceProvenance.ParseAllowingDiagnostics(source).Diagnostics);
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, diagnostic.Code);
        Assert.StartsWith(message, diagnostic.Message, StringComparison.Ordinal);
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Equal(KatLangErrorCode.UnresolvedOpenTarget, Assert.Single(failure.Errors).Code);
    }

    [Theory]
    // declared later in the same body, dotted public path, inline block, Math, parameterized head navigated by identity
    [InlineData("A = {\n    open Lib\n    Lib = {\n        public X = 3\n    }\n    X\n}\nA", "3")]
    [InlineData("Lib = {\n    public S = {\n        public X = 4\n    }\n}\nA = {\n    open Lib.S\n    X\n}\nA", "4")]
    [InlineData("A = {\n    open { public X = 5 }\n    X\n}\nA", "5")]
    [InlineData("A = {\n    open Math\n    Abs(-6)\n}\nA", "6")]
    [InlineData("Lib(p) = {\n    public S = {\n        public X = 7\n    }\n    p\n}\nA = {\n    open Lib.S\n    X\n}\nA", "7")]
    public void OpenTargetThatResolves_IsUnchanged(string source, string display)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(display, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Fact]
    public void OpenTargetRejections_NeverDoubleReport_AParameterHeadOrABuiltinHead()
    {
        var parameterHead = SourceProvenance.ParseAllowingDiagnostics("F(Lib) = {\n    open Lib.Sub\n    1\n}\nF(1)");
        Assert.Equal(DiagnosticCode.OpenTargetIsParameter, Assert.Single(parameterHead.Diagnostics).Code);

        var builtinHead = SourceProvenance.ParseAllowingDiagnostics("A = {\n    open count.X\n    1\n}\nA");
        Assert.Equal(DiagnosticCode.IllegalInOpen, Assert.Single(builtinHead.Diagnostics).Code);
    }

    // ── D6: an ambiguous open charges NOTHING in exposure analysis ──────────

    [Theory]
    [InlineData("open A, B")]
    [InlineData("open B, A")]
    public void AmbiguousOpen_DoesNotLetTargetOrderDecideExposure(string openList)
    {
        var source = $"Outer(p) = {{\n    A = {{\n        public X = p\n    }}\n    B = {{\n        public X = 7\n    }}\n    public Y = {{\n        {openList}\n        X\n    }}\n    0\n}}\nOuter.Y";
        var parsed = SourceProvenance.ParseValid(source);
        var y = parsed.Root.Properties.Single(p => p.Name == "Outer").Value.Properties.Single(p => p.Name == "Y");
        Assert.Equal(PropertyExposure.Exported, y.Exposure);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        Assert.Equal(KatLangErrorCode.AmbiguousOpen, Assert.Single(failure.Errors).Code);
    }

    [Fact]
    public void UnambiguousOpenedCapture_StillChargesItsOwner()
    {
        // Control: with ONE provider the captured member is charged, exactly as before.
        const string source = "Outer(p) = {\n    A = {\n        public X = p\n    }\n    public Y = {\n        open A\n        X\n    }\n    0\n}\nOuter.Y";
        var y = SourceProvenance.ParseValid(source).Root.Properties.Single(p => p.Name == "Outer").Value.Properties.Single(p => p.Name == "Y");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, y.Exposure);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty,
            Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors).Code);
    }

    // ── D4 / D7: the Math value-demand contract follows the CONSUMER's identity ──

    [Theory]
    [InlineData("A = q + 1\nF = sin(A)\nF(0)")]
    [InlineData("A = q + 1\nF = Math.Sin(A)\nF(0)")]
    [InlineData("open Math\nA = q + 1\nF = Sin(A)\nF(0)")]
    [InlineData("A = q + 1\nF = {\n    open Math\n    Sin(A)\n}\nF(0)")]
    [InlineData("A = q + 1\nF = A.sin\nF(0)")]
    [InlineData("open Math\nA = q + 1\nF = A.Sin\nF(0)")]
    // order independence: the consumer is processed after the transitively lifted sibling
    [InlineData("open Math\nF = Sin(A)\nA = B + 1\nB = q + 1\nF(-1)")]
    [InlineData("F = A.sin\nA = B + 1\nB = q + 1\nF(-1)")]
    public void MathConsumerContract_LiftsTheArgument_WhateverTheSpelling(string source)
    {
        var parsed = SourceProvenance.ParseValid(source);
        Assert.Equal(["q"], parsed.Root.Properties.Single(p => p.Name == "F").Value.Params);
        Assert.Equal("0.841470984807896506652502321630299",
            Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Theory]
    [InlineData("A = q + 1\nF = 2.pow(A)\nF(1)", "4")]
    [InlineData("A = q + 1\nF = pow(2, A)\nF(1)", "4")]
    [InlineData("open Math\nA = q + 1\nF = 2.Pow(A)\nF(1)", "4")]
    public void MathFallbackEdge_IsTheCallItStandsFor(string source, string display)
    {
        var parsed = SourceProvenance.ParseValid(source);
        Assert.Equal(["q"], parsed.Root.Properties.Single(p => p.Name == "F").Value.Params);
        Assert.Equal(display, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Theory]
    [InlineData("open Math\nA = q + 1\nF(x) = Sin(A)\nF(0)", 3, 12)]
    [InlineData("A = q + 1\nF(x) = A.sin\nF(0)", 2, 8)]
    [InlineData("A = q + 1\nF(x) = 2.pow(A)\nF(0)", 2, 14)]
    public void MathConsumerContract_UnderAClosedList_IsDiagnosedLikeTheAliasCall(string source, int line, int column)
    {
        var diagnostic = Assert.Single(SourceProvenance.ParseAllowingDiagnostics(source).Diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Contains("'A' is required as a value here", diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(line, column, line, column + 1), diagnostic.Span);
    }

    [Theory]
    // an opened library's own `Sin`, a user `Math`, and an ambiguous open are not the Math member
    [InlineData("Lib = {\n    public Sin(x) = x * 100\n}\nA = {\n    open Lib\n    F = Sin(Z)\n    Z = q + 1\n    F\n}\nA")]
    [InlineData("Math = {\n    public Sin(x) = x * 100\n}\nA = {\n    open Math\n    F = Sin(Z)\n    Z = q + 1\n    F\n}\nA")]
    [InlineData("Lib = {\n    public Sin(x) = x * 100\n}\nA = {\n    open Math, Lib\n    F = Sin(Z)\n    Z = q + 1\n    F\n}\nA")]
    // a callee that is a user callable keeps neutral arguments, dotted or not
    [InlineData("G(v) = v\nA = {\n    Z = q + 1\n    F = Z.G\n    F\n}\nA")]
    public void NonMathCallees_KeepNeutralArguments(string source)
    {
        var parsed = SourceProvenance.ParseValid(source);
        var a = parsed.Root.Properties.Single(p => p.Name == "A").Value;
        Assert.Empty(a.Properties.Single(p => p.Name == "F").Value.Params);
    }

    [Fact]
    public void BareMathFunction_Lifts_OnlyThroughOwnerWalkAndQualifiedRoutes()
    {
        // The alias (a prelude property) and the qualified spelling lift the member's own
        // parameter; a callable reached through `open` is never implicitly forwarded — the
        // opened Math member exactly like an opened user callable.
        Assert.Equal(["radians"], SourceProvenance.ParseValid("A = sin * 2\nA(0)").Root.Properties.Single(p => p.Name == "A").Value.Params);
        Assert.Equal(["radians"], SourceProvenance.ParseValid("A = Math.Sin * 2\nA(0)").Root.Properties.Single(p => p.Name == "A").Value.Params);
        Assert.Empty(SourceProvenance.ParseValid("A = {\n    open Math\n    Sin * 2\n}\nA").Root.Properties.Single(p => p.Name == "A").Value.Params);
        Assert.Empty(SourceProvenance.ParseValid("Lib = {\n    public G = x + 1\n}\nA = {\n    open Lib\n    G * 2\n}\nA").Root.Properties.Single(p => p.Name == "A").Value.Params);
    }

    // ── D5: host operations are prelude members in EVERY layer ───────────────

    private static RunOptions DataOperation()
        => new() { HostOperations = HostOperations.Create(HostOperation.Create("Data", static (_, _) => new Result.Atom(41))) };

    [Fact]
    public void HostOperation_BeatsAnOpenedMember_InExposureAnalysis()
    {
        // `Inner` reads the prelude's `Data` (the prelude precedes every open), which captures
        // nothing: it is exported, so `Outer.Inner` is accessible from the root.
        const string source = "Outer(p) = {\n    Lib = {\n        public Data = p\n    }\n    public Inner = {\n        open Lib\n        Data\n    }\n    0\n}\nOuter.Inner";
        var parsed = Parser.Parse(source, DataOperation());
        Assert.Empty(parsed.Diagnostics);
        var inner = parsed.Root.Properties.Single(p => p.Name == "Outer").Value.Properties.Single(p => p.Name == "Inner");
        Assert.Equal(PropertyExposure.Exported, inner.Exposure);
        Assert.Equal("41", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, DataOperation())).ToDisplayString());
    }

    [Fact]
    public void HostOperation_IsWhatTheEditorResolves_WhereTheEvaluatorSelectsIt()
    {
        const string source = "Lib = {\n    public Data = 9\n}\nA = {\n    open Lib\n    Data\n}\nA";
        var parsed = Parser.Parse(source, DataOperation());
        Assert.Empty(parsed.Diagnostics);
        Assert.Equal("41", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, DataOperation())).ToDisplayString());

        var model = SemanticModelBuilder.Build(parsed);
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(6, 5)));
        Assert.Equal(IdentifierClassification.Builtin, resolution.Classification);
        Assert.Null(resolution.ResolvedDeclaration);
        Assert.Equal("Data", resolution.ResolvedProperty?.Name);

        // Completion offers the operation as a prelude name, and the opened member it shadows
        // is not offered as a second `Data`.
        var visible = model.GetVisibleSymbolsAt(new SourcePosition(6, 5)).Where(s => s.Name == "Data").ToList();
        Assert.Equal(IdentifierClassification.Builtin, Assert.Single(visible).Classification);

        // Without the configuration the same source is the ordinary opened member.
        var plain = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        var plainResolution = Assert.IsType<IdentifierResolution>(plain.FindResolutionAt(new SourcePosition(6, 5)));
        Assert.Equal(IdentifierClassification.PropertyReference, plainResolution.Classification);
        Assert.Equal(new SourcePosition(2, 12), plainResolution.ResolvedDeclaration!.Span.Start);
        Assert.Equal("9", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Fact]
    public void ParseResult_CarriesItsHostConfiguration_WithoutChangingEquality()
    {
        var options = DataOperation();
        var configured = Parser.Parse("Data", options);
        var plain = Parser.Parse("Data");
        Assert.Same(options.HostOperations, configured.HostOperations);
        Assert.Null(plain.HostOperations);
        Assert.Equal(configured, configured with { HostOperations = null });
    }

    // ── Identity: aliases, wrappers, forwarding, and the Math spellings ───────

    [Theory]
    [InlineData("A(*xs) = 5\nP(f, f, f) = f(7)\nP(A, A, A)", "5")]
    [InlineData("A(*xs) = 5\nP(f, f, f) = f(7)\nUse(g) = P(g, g, g)\nUse(A)", "5")]
    [InlineData("P(f, f) = f\nP(pi, pi)", "3.141592653589793238462643383279503")]
    [InlineData("P(f, f) = f\nA = {\n    open Math\n    P(Pi, Pi)\n}\nA", "3.141592653589793238462643383279503")]
    public void OneCallable_BindsARepeatedName(string source, string display)
        => Assert.Equal(display, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());

    [Theory]
    // `Alias = A` is a new declaration (a wrapper), never an identity alias
    [InlineData("A(*xs) = 5\nAlias = A\nP(f, f, f) = f(7)\nP(A, Alias, A)")]
    // the prelude alias and the canonical member are distinct BINDINGS (wired under the
    // prelude and under Math) sharing one algorithm
    [InlineData("P(f, f) = f\nA = {\n    open Math\n    P(Pi, pi)\n}\nA")]
    // every argumentless dot expression is a fresh dot-result wrapper on the algorithm channel
    [InlineData("P(f, f) = f\nP(Math.Pi, Math.Pi)")]
    [InlineData("Lib = {\n    public X = 5\n}\nP(f, f) = f\nA = {\n    open Lib\n    P(X, Lib.X)\n}\nA")]
    public void DistinctCallables_RejectARepeatedName(string source)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.Contains("same callable identity", error.Message, StringComparison.Ordinal);
    }
}
