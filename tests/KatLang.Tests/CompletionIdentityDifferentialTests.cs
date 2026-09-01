using System.Numerics;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Completion (<c>SemanticModelBuilder.ComputeVisibleSymbols</c>, surfaced as
/// <see cref="SemanticModel.ScopeVisibilities"/> / <see cref="SemanticModel.GetVisibleSymbolsAt"/>)
/// is an ENUMERATION of the names ownership-first lexical lookup can resolve in a
/// scope. It is not the lookup: it walks the scope chain and the open providers
/// itself, so its precedence could drift from the authoritative relation while
/// still offering the right NAMES. This differential pins declaration IDENTITY —
/// which declaration completion attaches to each offered name — against the
/// authoritative relation, mechanically, without restating the precedence
/// algorithm in test code:
/// <list type="number">
/// <item>Oracle 1 — <see cref="ElaboratedScopeLookup.LookupLexicalPropertyMatches"/>
/// on the very chain shape the builder walks (prelude → root → nested levels),
/// the relation the parameter detector and the semantic model resolve every
/// reference through (M18's authoritative lookup).</item>
/// <item>Oracle 2 — the editor's own resolution of a reference WRITTEN at the
/// probe position, which also covers parameters and binders (they live outside
/// property lookup).</item>
/// <item>Oracle 3 — the Lean-modeled runtime: a reference written at the probe
/// must evaluate to the unique sentinel on the very declaration line completion
/// named (the <see cref="LookupCoherenceTests"/> identity loop).</item>
/// </list>
/// The check is bidirectional: every offered symbol must be what the authority
/// selects (wrong-owner drift), and everything the authority resolves uniquely
/// must be offered (missing-symbol drift). Ordering is pinned separately.
/// </summary>
public class CompletionIdentityDifferentialTests
{
    private const string ProbeMarker = "PROBE";

    private static readonly Algorithm.User SemanticPrelude =
        BuiltinRegistry.CreateSemanticPreludeAlgorithm(BuiltinRegistry.CreateMathAlgorithm(MathAlgorithmFlavor.SignatureOnly));

    // ----- expectation model --------------------------------------------------

    private abstract record Expectation(string Name);

    /// <summary>Offered, attached to the declaration on <paramref name="DeclarationLine"/>.</summary>
    private sealed record OfferedFrom(
        string Name,
        int DeclarationLine,
        IdentifierClassification Classification = IdentifierClassification.PropertyReference) : Expectation(Name);

    /// <summary>Offered from a binding that intentionally has no source declaration (an implicit parameter).</summary>
    private sealed record OfferedWithoutDeclaration(
        string Name,
        IdentifierClassification Classification) : Expectation(Name);

    /// <summary>Not offered at the probe (ambiguous, not exported, or out of scope).</summary>
    private sealed record NotOffered(string Name, string Reason) : Expectation(Name);

    /// <summary>Not a scope symbol; reaches the merged view only as the prelude builtin.</summary>
    private sealed record PreludeOnly(string Name) : Expectation(Name);

    /// <param name="Id">Stable program id.</param>
    /// <param name="Template">Program with one <c>PROBE</c> row inside the scope under test.</param>
    /// <param name="ScopePath">
    /// Structural path from the root to the probe scope's algorithm: property
    /// names, or <c>#i</c> for the i-th branch body of a clause family.
    /// </param>
    /// <param name="ProbeExpressions">
    /// Reference spellings for names a bare reference cannot evaluate (a clause
    /// family is called); every other name is probed as itself.
    /// </param>
    /// <param name="Expectations">Hand-written precedence rows for the report and a readable failure.</param>
    private sealed record ProbeProgram(
        string Id,
        string Template,
        IReadOnlyList<string> ScopePath,
        IReadOnlyDictionary<string, string> ProbeExpressions,
        IReadOnlyList<Expectation> Expectations);

    private static readonly IReadOnlyList<ProbeProgram> Programs =
    [
        // Root-scope identity and ordinal case sensitivity: both spellings are
        // independently visible and resolve to their own declaration.
        new("rootCaseSensitive",
            """
            Upper = 101
            upper = 202
            PROBE
            """,
            [],
            new Dictionary<string, string>(StringComparer.Ordinal),
            [
                new OfferedFrom("Upper", 1),
                new OfferedFrom("upper", 2),
                new PreludeOnly("sum"),
                new PreludeOnly("Math"),
            ]),

        // Every candidate declaration carries a unique sentinel (>= 100). Inner's
        // probe sees: its parent A's X (parent direct beats BOTH the nearer open
        // Lib.X and the root X), the root's count (direct beats prelude AND open),
        // y but not Y (Y is provided by two opens at the same level — ambiguous),
        // W (one provider), F (a clause family whose identity is its first clause),
        // and never Lib's non-exported Hidden or F's binder n.
        new("precedence",
            """
            X = 101
            count = 505
            y = 1111
            Lib = {
                public X = 202
                public Y = 303
                public count = 606
                Hidden = 707
            }
            L2 = {
                public Y = 404
                public W = 808
            }
            F(0) = 909
            F(n) = 1212
            A = {
                X = 1010
                Inner = {
                    open Lib, L2
                    PROBE
                }
                Inner
            }
            A
            """,
            ["A", "Inner"],
            new Dictionary<string, string>(StringComparer.Ordinal) { ["F"] = "F(0)" },
            [
                new OfferedFrom("X", 17),
                new OfferedFrom("count", 2),
                new OfferedFrom("y", 3),
                new NotOffered("Y", "provided by Lib and L2 at the same level: ambiguous"),
                new OfferedFrom("W", 12),
                new NotOffered("Hidden", "not exported through open"),
                new OfferedFrom("F", 14),
                new OfferedFrom("Lib", 4),
                new OfferedFrom("L2", 10),
                new OfferedFrom("A", 16),
                new OfferedFrom("Inner", 18),
                new PreludeOnly("sum"),
                new PreludeOnly("Math"),
                new NotOffered("n", "binder of another scope"),
            ]),

        // A clause body: the binder is a scope symbol with its own declaration, the
        // family itself resolves to its first clause, and the root X is reached
        // through the conditional's level.
        new("clauseBody",
            """
            X = 101
            F(0) = 202
            F(n) = PROBE
            F(1)
            """,
            ["F", "#1"],
            new Dictionary<string, string>(StringComparer.Ordinal) { ["F"] = "F(0)" },
            [
                new OfferedFrom("n", 3, IdentifierClassification.ConditionalBinderReference),
                new OfferedFrom("X", 1),
                new OfferedFrom("F", 2),
                new PreludeOnly("count"),
            ]),

        // Explicit parameters and an own property shadowing the root's.
        new("explicitParameters",
            """
            X = 101
            G(a, b) = {
                X = 303
                Local = a + b
                PROBE
            }
            G(1, 2)
            """,
            ["G"],
            new Dictionary<string, string>(StringComparer.Ordinal),
            [
                new OfferedFrom("a", 2, IdentifierClassification.ExplicitParameterReference),
                new OfferedFrom("b", 2, IdentifierClassification.ExplicitParameterReference),
                new OfferedFrom("X", 3),
                new OfferedFrom("Local", 4),
                new OfferedFrom("G", 2),
            ]),

        // An inferred parameter is a completion namespace outside property lookup:
        // it is offered and resolves as a parameter, but has no declaration span.
        new("implicitParameters",
            """
            G = x + PROBE
            G(1)
            """,
            ["G"],
            new Dictionary<string, string>(StringComparer.Ordinal),
            [
                new OfferedWithoutDeclaration("x", IdentifierClassification.ImplicitParameterReference),
                new OfferedFrom("G", 1),
            ]),
    ];

    public static TheoryData<string> ProgramIds()
    {
        var data = new TheoryData<string>();
        foreach (var program in Programs)
            data.Add(program.Id);
        return data;
    }

    private static ProbeProgram Program(string id) => Programs.Single(program => program.Id == id);

    // ----- the mechanical differential ----------------------------------------

    [Theory]
    [MemberData(nameof(ProgramIds))]
    public void CompletionAttachesExactlyTheDeclarationsAuthoritativeLookupSelects(string programId)
    {
        var program = Program(programId);
        var probe = ProbeSite(program.Template);
        var baseSource = program.Template.Replace(ProbeMarker, "0", StringComparison.Ordinal);
        var provenance = SourceProvenance.ParseValid(baseSource);
        var model = SemanticModelBuilder.Build(provenance.Parsed);
        var scope = model.FindScopeAt(probe.Line, probe.Column);
        var merged = model.GetVisibleSymbolsAt(probe.Line, probe.Column);
        var chain = BuildAuthoritativeChain(provenance.Root, program.ScopePath);

        if (program.ScopePath.Count == 0)
            Assert.Null(scope.Span);
        else
            Assert.NotNull(scope.Span); // the probe must sit inside the nested scope under test
        var checkedNames = 0;

        foreach (var name in CandidateNames(baseSource, program))
        {
            var offered = scope.Symbols.Where(symbol => symbol.Name == name).ToList();
            Assert.True(offered.Count <= 1, $"[{programId}] '{name}' is offered {offered.Count} times.");
            var symbol = offered.SingleOrDefault();

            // Oracle 1 — authoritative front-end lookup by declaration identity.
            var hits = ElaboratedScopeLookup.LookupLexicalPropertyMatches(chain, name);
            if (hits.Count == 1 && ReferenceEquals(hits[0].Owner, SemanticPrelude))
            {
                Assert.True(
                    symbol is null,
                    $"[{programId}] '{name}' resolves to the prelude here, but completion offers it as a scope symbol declared at {Describe(symbol?.Declaration)}.");
                var preludeSymbol = Assert.Single(merged, candidate => candidate.Name == name);
                Assert.Equal(IdentifierClassification.Builtin, preludeSymbol.Classification);
                Assert.Null(preludeSymbol.Declaration);
            }
            else if (hits.Count == 1 && hits[0].Property.DeclarationSpans.Count > 0)
            {
                var expected = hits[0].Property.DeclarationSpans[0];
                Assert.True(
                    symbol is not null,
                    $"[{programId}] authoritative lookup resolves '{name}' to the declaration at {Describe(expected)}, but completion does not offer it.");
                Assert.Equal(IdentifierClassification.PropertyReference, symbol!.Classification);
                Assert.True(
                    expected == symbol.Declaration?.Span,
                    $"[{programId}] completion attaches '{name}' to {Describe(symbol.Declaration)}, but authoritative lookup selects {Describe(expected)}.");
            }
            else
            {
                // No unique property declaration: nothing may be offered as a PROPERTY.
                // A parameter of an enclosing algorithm lives outside property lookup and
                // may be offered; Oracle 2 checks its identity below.
                Assert.True(
                    symbol is null || IsParameterClassification(symbol.Classification),
                    $"[{programId}] '{name}' has no unique property declaration here ({hits.Count} candidate(s)), but completion offers it as {symbol?.Classification} declared at {Describe(symbol?.Declaration)}.");
            }

            // Oracle 2 — the editor's resolution of a reference written at the probe.
            var variant = program.Template.Replace(ProbeMarker, ProbeExpression(program, name), StringComparison.Ordinal);
            var parsedVariant = Parser.Parse(variant);
            Assert.False(
                parsedVariant.HasErrors,
                $"[{programId}] probing '{name}' produced front-end errors: {string.Join(" | ", parsedVariant.Diagnostics.Select(d => d.Message))}");
            var resolution = SemanticModelBuilder.Build(parsedVariant).FindResolutionAt(probe.Line, probe.Column);
            Assert.True(resolution is not null, $"[{programId}] no editor resolution at the probe for '{name}'.");
            Assert.Equal(name, resolution!.Occurrence.Name);

            if (symbol is not null)
            {
                Assert.Equal(symbol.Classification, resolution.Classification);
                Assert.True(
                    symbol.Declaration?.Span == resolution.ResolvedDeclaration?.Span,
                    $"[{programId}] completion attaches '{name}' to {Describe(symbol.Declaration)}, but a written reference resolves to {Describe(resolution.ResolvedDeclaration)}.");
            }
            else
            {
                Assert.True(
                    resolution.Classification is IdentifierClassification.Builtin
                        or IdentifierClassification.Unresolved
                        or IdentifierClassification.ImplicitParameterReference,
                    $"[{programId}] a reference to '{name}' at the probe resolves as {resolution.Classification} (declared at {Describe(resolution.ResolvedDeclaration)}), but completion does not offer '{name}'.");
            }

            // Oracle 3 — the runtime produces the sentinel on the line completion named.
            if (symbol is { Classification: IdentifierClassification.PropertyReference, Declaration: { } declaration }
                && TryFindSentinel(baseSource, declaration.Span.StartLineNumber, out var sentinel))
            {
                Assert.Equal(
                    $"ok raw={sentinel} n=1",
                    SemanticExplorerHarness.Observe($"{programId}.{name}", variant).Neutral);
            }

            checkedNames++;
        }

        Assert.True(checkedNames >= program.Expectations.Count, $"[{programId}] too few candidates checked ({checkedNames}).");
    }

    // ----- the hand-written precedence rows -----------------------------------

    [Theory]
    [MemberData(nameof(ProgramIds))]
    public void PrecedenceRowsHoldByDeclarationLine(string programId)
    {
        var program = Program(programId);
        var probe = ProbeSite(program.Template);
        var model = SemanticModelBuilder.Build(
            SourceProvenance.ParseValid(program.Template.Replace(ProbeMarker, "0", StringComparison.Ordinal)).Parsed);
        var scope = model.FindScopeAt(probe.Line, probe.Column);
        var merged = model.GetVisibleSymbolsAt(probe.Line, probe.Column);

        Assert.NotEmpty(program.Expectations);
        foreach (var expectation in program.Expectations)
        {
            switch (expectation)
            {
                case OfferedFrom(var name, var line, var classification):
                {
                    var symbol = Assert.Single(scope.Symbols, candidate => candidate.Name == name);
                    Assert.Equal(classification, symbol.Classification);
                    Assert.True(symbol.Declaration is not null, $"[{programId}] '{name}' is offered without a declaration.");
                    Assert.Equal(line, symbol.Declaration!.Span.StartLineNumber);

                    var mergedSymbol = Assert.Single(merged, candidate => candidate.Name == name);
                    Assert.Same(symbol, mergedSymbol);
                    break;
                }

                case OfferedWithoutDeclaration(var name, var classification):
                {
                    var symbol = Assert.Single(scope.Symbols, candidate => candidate.Name == name);
                    Assert.Equal(classification, symbol.Classification);
                    Assert.Null(symbol.Declaration);

                    var mergedSymbol = Assert.Single(merged, candidate => candidate.Name == name);
                    Assert.Same(symbol, mergedSymbol);
                    break;
                }

                case NotOffered(var name, _):
                    Assert.DoesNotContain(scope.Symbols, candidate => candidate.Name == name);
                    Assert.DoesNotContain(merged, candidate => candidate.Name == name);
                    break;

                case PreludeOnly(var name):
                {
                    Assert.DoesNotContain(scope.Symbols, candidate => candidate.Name == name);
                    var builtin = Assert.Single(merged, candidate => candidate.Name == name);
                    Assert.Equal(IdentifierClassification.Builtin, builtin.Classification);
                    Assert.Null(builtin.Declaration);
                    break;
                }

                default:
                    throw new InvalidOperationException($"Unhandled expectation for '{programId}'.");
            }
        }
    }

    /// <summary>
    /// The differential is about WHICH declaration owns a name, not where the
    /// name appears: scope symbols stay ordinal-sorted by name and the merged
    /// view lists the scope's symbols before the unshadowed prelude names.
    /// </summary>
    [Theory]
    [MemberData(nameof(ProgramIds))]
    public void OrderingIsByNameAndUnchangedByIdentity(string programId)
    {
        var program = Program(programId);
        var probe = ProbeSite(program.Template);
        var model = SemanticModelBuilder.Build(
            SourceProvenance.ParseValid(program.Template.Replace(ProbeMarker, "0", StringComparison.Ordinal)).Parsed);
        var scope = model.FindScopeAt(probe.Line, probe.Column);
        var merged = model.GetVisibleSymbolsAt(probe.Line, probe.Column);

        var scopeNames = scope.Symbols.Select(static symbol => symbol.Name).ToList();
        Assert.Equal(scopeNames.OrderBy(static name => name, StringComparer.Ordinal).ToList(), scopeNames);
        Assert.Equal(scopeNames, merged.Take(scopeNames.Count).Select(static symbol => symbol.Name).ToList());
        Assert.All(merged.Skip(scopeNames.Count), static symbol => Assert.Equal(IdentifierClassification.Builtin, symbol.Classification));
    }

    [Fact]
    public void OpenCompletion_AttachesTheFirstQualifyingSameNameDeclaration()
    {
        // Host ASTs may contain same-name properties. Open lookup skips an earlier
        // private member and an earlier local-only public member, then selects the
        // first public+exported member. Completion must attach that exact declaration,
        // not merely offer the correct spelling.
        var privateX = PropertyAt("X", line: 1, isPublic: false, PropertyExposure.Exported);
        var localOnlyX = PropertyAt("X", line: 2, isPublic: true, PropertyExposure.LocalOnlyCapturedAncestorParameters);
        var exportedX = PropertyAt("X", line: 3, isPublic: true, PropertyExposure.Exported);
        var library = User(properties: [privateX, localOnlyX, exportedX]);
        var use = User(
            opens: [new Expr.Resolve("Lib") { Span = new SourceSpan(5, 10, 5, 12) }],
            output: [new Expr.Num(0) { Span = new SourceSpan(6, 1, 6, 1) }]);
        var root = User(
            properties:
            [
                new Property("Lib", library) { DeclarationSpans = [new SourceSpan(4, 1, 4, 3)] },
                new Property("Use", use) { DeclarationSpans = [new SourceSpan(5, 1, 5, 3)] },
            ],
            output: [new Expr.Resolve("Use") { Span = new SourceSpan(7, 1, 7, 3) }]);

        var model = SemanticModelBuilder.Build(root);
        var completion = model.FindScopeAt(6, 1);
        var x = Assert.Single(completion.Symbols, static symbol => symbol.Name == "X");
        Assert.Equal(new SourceSpan(3, 1, 3, 1), x.Declaration?.Span);

        var rootScope = ElaboratedScopeLookup.CreateScope(root, ElaboratedScopeLookup.CreateScope(SemanticPrelude));
        var useScope = ElaboratedScopeLookup.CreateScope(use, rootScope);
        var hit = Assert.Single(ElaboratedScopeLookup.LookupLexicalPropertyMatches(useScope, "X"));
        Assert.Same(exportedX, hit.Property);
        Assert.Equal(hit.Property.DeclarationSpans[0], x.Declaration?.Span);
    }

    [Fact]
    public void DirectCompletion_AttachesTheFirstSameNameDeclaration()
    {
        // Recovery/host ASTs may retain duplicate same-name declarations. The
        // authoritative direct index is first-declaration-wins; enumerating the
        // ordered list must attach that same identity rather than a later duplicate.
        var first = PropertyAt("Dup", line: 1, isPublic: false, PropertyExposure.Exported);
        var second = PropertyAt("Dup", line: 2, isPublic: false, PropertyExposure.Exported);
        var root = User(
            properties: [first, second],
            output: [new Expr.Num(0) { Span = new SourceSpan(3, 1, 3, 1) }]);

        var model = SemanticModelBuilder.Build(root);
        var completion = model.FindScopeAt(3, 1);
        var dup = Assert.Single(completion.Symbols, static symbol => symbol.Name == "Dup");
        Assert.Equal(new SourceSpan(1, 1, 1, 1), dup.Declaration?.Span);

        var scope = ElaboratedScopeLookup.CreateScope(root, ElaboratedScopeLookup.CreateScope(SemanticPrelude));
        var hit = Assert.Single(ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope, "Dup"));
        Assert.Same(first, hit.Property);
        Assert.Equal(hit.Property.DeclarationSpans[0], dup.Declaration?.Span);
    }

    // ----- helpers ------------------------------------------------------------

    private static bool IsParameterClassification(IdentifierClassification classification)
        => classification is IdentifierClassification.ExplicitParameterReference
            or IdentifierClassification.ImplicitParameterReference
            or IdentifierClassification.ConditionalBinderReference;

    private static string ProbeExpression(ProbeProgram program, string name)
        => program.ProbeExpressions.TryGetValue(name, out var expression) ? expression : name;

    /// <summary>
    /// Every identifier spelled in the program plus a few prelude names, so the
    /// reverse direction (authority resolves → completion offers) is checked for
    /// every declared name, not only for names completion happened to offer.
    /// </summary>
    private static IReadOnlyList<string> CandidateNames(string baseSource, ProbeProgram program)
    {
        var (tokens, _) = Lexer.Tokenize(baseSource);
        var names = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var token in tokens)
        {
            if (token.Kind == TokenKind.Identifier && token.StringValue is { } identifier)
                names.Add(identifier);
        }

        names.Add("sum");
        names.Add("Math");
        foreach (var expectation in program.Expectations)
            names.Add(expectation.Name);

        return names.ToList();
    }

    /// <summary>
    /// The chain shape <c>SemanticModelBuilder</c> walks for the probe scope —
    /// prelude → root → each nested level — built from the elaborated AST. Only
    /// the nesting is restated here; every precedence decision stays inside
    /// <see cref="ElaboratedScopeLookup"/>.
    /// </summary>
    private static ElaboratedPropertyScope BuildAuthoritativeChain(Algorithm root, IReadOnlyList<string> path)
    {
        var scope = ElaboratedScopeLookup.CreateScope(root, ElaboratedScopeLookup.CreateScope(SemanticPrelude));
        var algorithm = root;
        foreach (var step in path)
        {
            algorithm = step.StartsWith('#')
                ? Assert.IsType<Algorithm.Conditional>(algorithm).Branches[int.Parse(step[1..])].Body
                : algorithm.Properties.Single(property => property.Name == step).Value;
            scope = ElaboratedScopeLookup.CreateScope(algorithm, scope);
        }

        return scope;
    }

    private static (int Line, int Column) ProbeSite(string template)
    {
        var lines = template.Split('\n');
        for (var i = 0; i < lines.Length; i++)
        {
            var column = lines[i].IndexOf(ProbeMarker, StringComparison.Ordinal);
            if (column >= 0)
                return (i + 1, column + 1);
        }

        throw new InvalidOperationException("The template has no PROBE row.");
    }

    /// <summary>The unique sentinel literal (>= 100) written on <paramref name="line"/>, if any.</summary>
    private static bool TryFindSentinel(string source, int line, out int sentinel)
    {
        var (tokens, _) = Lexer.Tokenize(source.Split('\n')[line - 1]);
        var sentinels = tokens
            .Where(static token => token.Kind == TokenKind.Number)
            .Select(static token => token.NumValue)
            .Where(static value => value >= 100 && Decimal128.IsInteger(value))
            .Select(static value => (int)value)
            .ToList();

        sentinel = sentinels.Count == 1 ? sentinels[0] : 0;
        return sentinels.Count == 1;
    }

    private static string Describe(SourceSpan? span)
        => span is null ? "<none>" : $"{span.StartLineNumber}:{span.StartColumn}";

    private static string Describe(DeclarationOccurrence? declaration)
        => Describe(declaration?.Span);

    private static Property PropertyAt(string name, int line, bool isPublic, PropertyExposure exposure)
        => new(name, User(), IsPublic: isPublic)
        {
            Exposure = exposure,
            DeclarationSpans = [new SourceSpan(line, 1, line, 1)],
        };

    private static Algorithm.User User(
        IReadOnlyList<Expr>? opens = null,
        IReadOnlyList<Property>? properties = null,
        IReadOnlyList<Expr>? output = null)
        => new(
            Parent: null,
            Parameters: [],
            Opens: opens ?? [],
            Properties: properties ?? [],
            Output: OutputBundle.From(output ?? []));
}
