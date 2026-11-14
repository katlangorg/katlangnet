using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using RoslynSyntaxTree = Microsoft.CodeAnalysis.SyntaxTree;
using RoslynDiagnosticSeverity = Microsoft.CodeAnalysis.DiagnosticSeverity;
using RoslynTextSpan = Microsoft.CodeAnalysis.Text.TextSpan;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>Where a <c>MIRROR OF</c> comment sits relative to the member it documents.</summary>
internal enum TwinMarkerPlacement
{
    /// <summary>In the leading trivia (documentation or line comment) of a method or local function.</summary>
    Declaration,

    /// <summary>A line comment heading the first statement of a method or local function body.</summary>
    BodyHead,

    /// <summary>Anywhere else: inside a body, or on a type or other member.</summary>
    Inner,
}

/// <summary>One method or local function of <c>src/KatLang/</c>, the unit a twin pair compares.</summary>
internal sealed class TwinMethod
{
    internal TwinMethod(string file, string typeName, string name, string? outerName, SyntaxNode declaration,
        ParameterListSyntax parameters, TypeSyntax returnType, SyntaxTokenList modifiers, BlockSyntax? body,
        ArrowExpressionClauseSyntax? expressionBody, int line, ImmutableArray<string> canonicalParameterTypes)
    {
        File = file;
        TypeName = typeName;
        Name = name;
        OuterName = outerName;
        Declaration = declaration;
        Parameters = parameters;
        ReturnType = returnType;
        Modifiers = modifiers;
        Body = body;
        ExpressionBody = expressionBody;
        Line = line;
        ParameterTypes = [.. parameters.Parameters.Select(static p => TwinNormalization.Compact(p.Type?.ToString() ?? ""))];
        CanonicalParameterTypes = canonicalParameterTypes;
    }

    public string File { get; }
    public string TypeName { get; }
    public string Name { get; }

    /// <summary>The enclosing member's name for a local function; null for a type member.</summary>
    public string? OuterName { get; }

    public SyntaxNode Declaration { get; }
    public ParameterListSyntax Parameters { get; }
    public TypeSyntax ReturnType { get; }
    public SyntaxTokenList Modifiers { get; }
    public BlockSyntax? Body { get; }
    public ArrowExpressionClauseSyntax? ExpressionBody { get; }
    public int Line { get; }

    /// <summary>Parameter types as written (whitespace compacted): the readable part of an overloaded key.</summary>
    public ImmutableArray<string> ParameterTypes { get; }

    /// <summary>Parameter types with global aliases expanded and tuples spelled <c>ValueTuple</c>: what a cref matches.</summary>
    public ImmutableArray<string> CanonicalParameterTypes { get; }

    /// <summary>Set once the whole inventory is known: the name has several overloads in its type.</summary>
    public bool IsOverloaded { get; internal set; }

    /// <summary>Stable identity: <c>Type.Name</c>, <c>Type.Outer.Local</c>, plus parameter types when overloaded.</summary>
    public string Key
        => TypeName + "." + (OuterName is null ? "" : OuterName + ".") + Name
            + (IsOverloaded ? "(" + string.Join(", ", ParameterTypes) + ")" : "");

    public bool HasAsynchronousFlag
        => Parameters.Parameters.Any(static p => p.Identifier.ValueText == TwinNormalization.FlagName
            && p.Type is PredefinedTypeSyntax { Keyword.RawKind: (int)SyntaxKind.BoolKeyword });

    /// <summary>An async-shaped member: <c>async</c>, or returning <c>Task</c>/<c>ValueTask</c>.</summary>
    public bool IsAsyncShaped
        => Modifiers.Any(SyntaxKind.AsyncKeyword) || ReturnsAwaitable(ReturnType);

    private static bool ReturnsAwaitable(TypeSyntax type)
    {
        var name = type switch
        {
            GenericNameSyntax generic => generic.Identifier.ValueText,
            IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
            QualifiedNameSyntax qualified => qualified.Right.Identifier.ValueText,
            _ => "",
        };
        return name is "Task" or "ValueTask";
    }
}

/// <summary>One occurrence of the words <c>MIRROR OF</c> in a comment.</summary>
internal sealed record TwinMarker(
    string File,
    int Line,
    TwinMarkerPlacement Placement,
    TwinMethod? Attached,
    string EnclosingMember,
    string Text,
    bool IsProseMention,
    ImmutableArray<TwinMarkerTarget> Targets)
{
    /// <summary>Stable identity of the marker: its file, its enclosing member, and its words up to the end of the line.</summary>
    public string Key => File + " :: " + EnclosingMember + " :: " + Text;
}

/// <summary>
/// A counterpart named by a marker: a method name, plus canonical parameter types when the marker
/// spells them.
/// </summary>
internal sealed record TwinMarkerTarget(string Name, ImmutableArray<string>? ParameterTypes, string? ContainingType = null)
{
    public override string ToString()
        => (ContainingType is null ? "" : ContainingType + ".")
            + (ParameterTypes is { } types ? Name + "(" + string.Join(", ", types) + ")" : Name);
}

/// <summary>A resolved mirror pair: the twin bearing the marker, and the synchronous method it names.</summary>
internal sealed record TwinPair(TwinMarker Marker, TwinMethod Twin, TwinMethod Counterpart)
{
    public string Id => Twin.Key + " ~ " + Counterpart.Key;
}

/// <summary>A marker that forms no compared pair, and why.</summary>
internal sealed record UnpairedTwinMarker(TwinMarker Marker, string Why);

/// <summary>A marker whose named counterpart could not be resolved to exactly one method.</summary>
internal sealed record TwinResolutionFailure(TwinMarker Marker, TwinMarkerTarget Target, string Reason);

/// <summary>
/// A use of a <c>bool asynchronous</c> parameter that selects between behaviors. <see cref="ArmsMirror"/> holds when the
/// selection is <c>asynchronous ? a : b</c> (or <c>if (asynchronous) a else b</c>) whose two arms normalize to the same
/// tokens: the await-or-call shape, where the asynchronous arm awaits the twin of what the synchronous arm calls.
/// </summary>
internal sealed record FlagBranchPoint(TwinMethod Method, int Ordinal, string Kind, string Hash, string Text, bool ArmsMirror)
{
    public string Key => Method.Key + " #" + Ordinal;
}

/// <summary>The normalized comparison of one pair.</summary>
internal sealed record TwinComparison(
    TwinPair Pair,
    ImmutableArray<string> CounterpartTokens,
    ImmutableArray<string> TwinTokens,
    ImmutableArray<TwinDiffHunk> Hunks)
{
    public bool IsIdentical => Hunks.IsEmpty;

    /// <summary>
    /// The normalized difference INCLUDING each hunk's token offsets on both sides. Changed tokens alone
    /// would let a one-sided move of an allowed difference keep its hash (for example, hopping before an
    /// error check instead of after it). Common edits on both sides may require re-pinning the offsets.
    /// </summary>
    public string DifferenceText => string.Join("\n", Hunks.Select(static h =>
        $"@{h.CounterpartOffset},{h.TwinOffset} {h}"));

    public string DifferenceHash => TwinNormalization.Hash(DifferenceText);

    public int ChangedTokens => Hunks.Sum(static h => h.Removed.Length + h.Added.Length);

    /// <summary>1 - changed / total normalized tokens of both sides.</summary>
    public double Similarity
        => CounterpartTokens.Length + TwinTokens.Length == 0
            ? 1.0
            : 1.0 - (double)ChangedTokens / (CounterpartTokens.Length + TwinTokens.Length);
}

/// <summary>One run of removed and added normalized tokens, anchored at its offsets in both token streams.</summary>
internal sealed record TwinDiffHunk(int CounterpartOffset, int TwinOffset, ImmutableArray<string> Removed, ImmutableArray<string> Added)
{
    public override string ToString()
        => "-[" + string.Join(" ", Removed) + "] +[" + string.Join(" ", Added) + "]";
}

/// <summary>Everything the twin drift guard reads from <c>src/KatLang/</c>, parsed once.</summary>
internal sealed record TwinInventory(
    ImmutableArray<string> Files,
    ImmutableArray<string> ParseErrors,
    ImmutableArray<TwinMarker> Markers,
    ImmutableArray<TwinPair> Pairs,
    ImmutableArray<UnpairedTwinMarker> UnpairedMarkers,
    ImmutableArray<TwinResolutionFailure> ResolutionFailures,
    ImmutableArray<TwinComparison> Comparisons,
    ImmutableDictionary<string, string> TwinRenames,
    ImmutableArray<TwinMethod> FlagMethods,
    ImmutableArray<FlagBranchPoint> FlagBranchPoints,
    ImmutableArray<string> BlockingFlagCalls,
    TimeSpan BuildTime);

/// <summary>
/// The mechanical side of the <c>MIRROR OF</c> rule (see <c>TwinNormalizationTests</c>): Roslyn syntax
/// trees of every <c>src/KatLang/</c> source, the marker inventory, pair resolution, the ONE normalization
/// with its synchronous-only blocking adapter, and a token-level difference.
///
/// <para><b>Markers.</b> Every occurrence of the words <c>MIRROR OF</c> in a comment is a marker. A marker
/// in the leading comments of a method or local function (or heading its body's first statement) whose
/// first word after <c>MIRROR OF</c> is a <c>&lt;see cref&gt;</c> or a PascalCase identifier names that
/// member's COUNTERPART; it must resolve to exactly one method, and when the marked member is asynchronous
/// (async, awaitable, or carrying a <c>bool asynchronous</c> flag) and the counterpart is not, the two form
/// a compared PAIR. Every other marker — prose about the convention, a comment inside a body about one arm,
/// a marker relating two members of the same family — forms no pair.</para>
///
/// <para><b>Normalization</b> (comments, whitespace and every other trivia
/// are dropped by comparing tokens): an <c>await</c> is removed; <c>x.ConfigureAwait(false)</c> becomes
/// <c>x</c>; on the synchronous counterpart ONLY, <c>x.GetAwaiter().GetResult()</c> becomes <c>x</c> (the synchronous family's way of
/// completing a <c>bool asynchronous</c> body, the counterpart of the twin's <c>await</c>); a twin's name
/// becomes the name of the counterpart its marker resolves to (so <c>DispatchPlannedAsync</c> reads
/// <c>DispatchPlannedCounted</c>), and any other identifier <c>XAsync</c> becomes <c>X</c>; the <c>async</c>
/// modifier is dropped; a named argument <c>asynchronous: true</c> becomes <c>asynchronous: false</c>. A
/// twin may not hide blocking behind the synchronous completion adapter. An expression body <c>=&gt; e</c> is compared as the block <c>{ return e; }</c> (<c>{ e; }</c> for a
/// <c>void</c>, <c>Task</c> or <c>ValueTask</c> member). The parameter list is compared too (types, names,
/// defaults); the return type and modifiers are not, since they are what makes a twin a twin.</para>
/// </summary>
internal static class TwinNormalization
{
    internal const string MarkerText = "MIRROR OF";

    internal const string FlagName = "asynchronous";

    private static readonly CSharpParseOptions ParseOptions = new(LanguageVersion.Preview, DocumentationMode.Parse);

    private static readonly Lazy<TwinInventory> CurrentInventory = new(() => Build(RepoRoot.Find()));

    /// <summary>The inventory of the checkout under test, built at most once per test run.</summary>
    internal static TwinInventory Current => CurrentInventory.Value;

    internal static TwinInventory Build(string repoRoot)
    {
        var stopwatch = System.Diagnostics.Stopwatch.StartNew();
        var sourceRoot = Path.Combine(repoRoot, "src", "KatLang");
        var files = Directory.GetFiles(sourceRoot, "*.cs", SearchOption.AllDirectories)
            .Select(path => (Path: path, Relative: Path.GetRelativePath(repoRoot, path).Replace('\\', '/')))
            .Where(static f => !f.Relative.Contains("/bin/", StringComparison.Ordinal) && !f.Relative.Contains("/obj/", StringComparison.Ordinal))
            .OrderBy(static f => f.Relative, StringComparer.Ordinal)
            .ToList();

        var trees = files
            .Select(f => (f.Relative, Tree: CSharpSyntaxTree.ParseText(File.ReadAllText(f.Path), ParseOptions, f.Relative)))
            .ToList();
        var parseErrors = trees
            .SelectMany(static t => t.Tree.GetDiagnostics()
                .Where(static d => d.Severity == RoslynDiagnosticSeverity.Error)
                .Select(d => t.Relative + ": " + d.GetMessage(System.Globalization.CultureInfo.InvariantCulture)))
            .ToImmutableArray();

        // Global using aliases (`global using ValEnv = …;`): a cref may spell the aliased type.
        var aliases = new Dictionary<string, TypeSyntax>(StringComparer.Ordinal);
        foreach (var (_, tree) in trees)
        {
            foreach (var directive in tree.GetCompilationUnitRoot().Usings)
            {
                if (directive.GlobalKeyword.IsKind(SyntaxKind.GlobalKeyword) && directive.Alias is { } alias && directive.NamespaceOrType is { } target)
                    aliases[alias.Name.Identifier.ValueText] = target;
            }
        }

        var methods = new List<TwinMethod>();
        var methodByNode = new Dictionary<SyntaxNode, TwinMethod>();
        foreach (var (relative, tree) in trees)
        {
            foreach (var node in tree.GetRoot().DescendantNodes())
            {
                TwinMethod? method = node switch
                {
                    MethodDeclarationSyntax m => new TwinMethod(relative, TypeNameOf(m), m.Identifier.ValueText, null, m,
                        m.ParameterList, m.ReturnType, m.Modifiers, m.Body, m.ExpressionBody, LineOf(tree, m.Identifier.SpanStart),
                        CanonicalTypes(m.ParameterList, aliases)),
                    LocalFunctionStatementSyntax l => new TwinMethod(relative, TypeNameOf(l), l.Identifier.ValueText,
                        OuterMemberName(l), l, l.ParameterList, l.ReturnType, l.Modifiers, l.Body, l.ExpressionBody,
                        LineOf(tree, l.Identifier.SpanStart), CanonicalTypes(l.ParameterList, aliases)),
                    _ => null,
                };
                if (method is null)
                    continue;
                methods.Add(method);
                methodByNode[node] = method;
            }
        }

        foreach (var group in methods.GroupBy(static m => (m.TypeName, m.OuterName, m.Name)))
        {
            if (group.Count() > 1)
            {
                foreach (var method in group)
                    method.IsOverloaded = true;
            }
        }

        var markers = new List<TwinMarker>();
        foreach (var (relative, tree) in trees)
            markers.AddRange(MarkersOf(relative, tree, methodByNode, aliases));

        var pairs = new List<TwinPair>();
        var unpaired = new List<UnpairedTwinMarker>();
        var failures = new List<TwinResolutionFailure>();
        foreach (var marker in markers)
        {
            if (marker.IsProseMention)
            {
                unpaired.Add(new(marker, "prose mention of the convention"));
                continue;
            }

            if (marker.Placement == TwinMarkerPlacement.Inner || marker.Attached is not { } twin)
            {
                unpaired.Add(new(marker, "comment inside a body or on a non-method member"));
                continue;
            }

            if (marker.Targets.IsEmpty)
            {
                unpaired.Add(new(marker, "names no counterpart"));
                continue;
            }

            var target = marker.Targets[0];
            if (marker.Targets.Length != 1)
            {
                var markerReason = "ambiguous marker: name exactly one canonical counterpart after MIRROR OF, "
                    + "rather than selecting the first of " + string.Join(" / ", marker.Targets)
                    + "; describe delegating wrappers outside the marker";
                failures.Add(new TwinResolutionFailure(marker, target, markerReason));
                unpaired.Add(new(marker, "unresolved: " + markerReason));
                continue;
            }

            var resolved = Resolve(twin, target, methods, out var reason);
            if (resolved is null)
            {
                failures.Add(new TwinResolutionFailure(marker, target, reason));
                unpaired.Add(new(marker, "unresolved: " + reason));
                continue;
            }

            var twinIsAsynchronous = twin.IsAsyncShaped || twin.HasAsynchronousFlag;
            if (!twinIsAsynchronous || resolved.IsAsyncShaped || resolved.HasAsynchronousFlag)
            {
                unpaired.Add(new(marker, $"relates two members of one family ({twin.Key} ~ {resolved.Key})"));
                continue;
            }

            if (pairs.Any(p => p.Twin == twin && p.Counterpart == resolved))
            {
                unpaired.Add(new(marker, $"restates the pair {twin.Key} ~ {resolved.Key}"));
                continue;
            }

            pairs.Add(new TwinPair(marker, twin, resolved));
        }

        // The twin-name map: each twin reads as the counterpart its marker names, when that is unambiguous.
        var renames = pairs
            .GroupBy(static p => p.Twin.Name, StringComparer.Ordinal)
            .Where(static g => g.Select(static p => p.Counterpart.Name).Distinct(StringComparer.Ordinal).Count() == 1)
            .ToImmutableDictionary(static g => g.Key, static g => g.First().Counterpart.Name, StringComparer.Ordinal);
        var normalizer = new Normalizer(renames);

        var comparisons = pairs.Select(pair => Compare(pair, normalizer)).ToImmutableArray();
        var flagMethods = methods.Where(static m => m.HasAsynchronousFlag).ToImmutableArray();
        var branchPoints = flagMethods.SelectMany(method => BranchPointsOf(method, normalizer)).ToImmutableArray();
        var blocking = trees.SelectMany(static t => BlockingFlagCallsOf(t.Relative, t.Tree)).ToImmutableArray();

        return new TwinInventory(
            [.. trees.Select(static t => t.Relative)],
            parseErrors,
            [.. markers],
            [.. pairs],
            [.. unpaired],
            [.. failures],
            comparisons,
            renames,
            flagMethods,
            branchPoints,
            blocking,
            stopwatch.Elapsed);
    }

    // ── Markers ─────────────────────────────────────────────────────────────

    private static IEnumerable<TwinMarker> MarkersOf(
        string file, RoslynSyntaxTree tree, Dictionary<SyntaxNode, TwinMethod> methodByNode, Dictionary<string, TypeSyntax> aliases)
    {
        foreach (var trivia in tree.GetRoot().DescendantTrivia(descendIntoTrivia: false))
        {
            if (!trivia.IsKind(SyntaxKind.SingleLineCommentTrivia)
                && !trivia.IsKind(SyntaxKind.SingleLineDocumentationCommentTrivia)
                && !trivia.IsKind(SyntaxKind.MultiLineCommentTrivia)
                && !trivia.IsKind(SyntaxKind.MultiLineDocumentationCommentTrivia))
                continue;
            if (!trivia.ToFullString().Contains(MarkerText, StringComparison.Ordinal))
                continue;

            var token = trivia.Token;
            var isLeading = token.LeadingTrivia.Contains(trivia);
            var enclosing = token.Parent?.AncestorsAndSelf()
                .FirstOrDefault(static n => n is LocalFunctionStatementSyntax or MemberDeclarationSyntax);
            var placement = TwinMarkerPlacement.Inner;
            TwinMethod? attached = null;
            if (enclosing is not null && methodByNode.TryGetValue(enclosing, out var method))
            {
                if (isLeading && enclosing.GetFirstToken() == token)
                {
                    placement = TwinMarkerPlacement.Declaration;
                    attached = method;
                }
                else if (isLeading && method.Body is { Statements.Count: > 0 } body && body.Statements[0].GetFirstToken() == token)
                {
                    placement = TwinMarkerPlacement.BodyHead;
                    attached = method;
                }
            }

            var enclosingName = enclosing switch
            {
                null => "(file)",
                _ when methodByNode.TryGetValue(enclosing, out var m) => m.Key,
                BaseTypeDeclarationSyntax type => "type " + type.Identifier.ValueText,
                _ => enclosing.Kind().ToString(),
            };

            var occurrences = trivia.GetStructure() is DocumentationCommentTriviaSyntax documentation
                ? DocumentationOccurrences(documentation, aliases)
                : LineCommentOccurrences(trivia, aliases);
            foreach (var (position, words, prose, targets) in occurrences)
                yield return new TwinMarker(file, LineOf(tree, position), placement, attached, enclosingName, words, prose, targets);
        }
    }

    /// <summary>
    /// The occurrences in a documentation comment. A counterpart is the <c>&lt;see cref&gt;</c> that directly
    /// follows the words (further ones introduced by <c>/</c>); words inside a <c>&lt;c&gt;</c> element are a
    /// prose mention of the convention; words followed by text name a counterpart only as a line comment would.
    /// </summary>
    private static List<(int Position, string Words, bool Prose, ImmutableArray<TwinMarkerTarget> Targets)> DocumentationOccurrences(
        DocumentationCommentTriviaSyntax documentation, Dictionary<string, TypeSyntax> aliases)
    {
        // Document-order pieces: one per text token (a marker never spans lines) or cref.
        var pieces = new List<(SyntaxToken? Text, CrefSyntax? Cref, bool InCode)>();
        foreach (var node in documentation.DescendantNodes())
        {
            switch (node)
            {
                case XmlTextSyntax text:
                    var inCode = text.Ancestors().OfType<XmlElementSyntax>()
                        .Any(static e => e.StartTag.Name.LocalName.ValueText is "c" or "code");
                    foreach (var textToken in text.TextTokens)
                    {
                        if (textToken.IsKind(SyntaxKind.XmlTextLiteralToken) && textToken.ValueText.Trim().Length != 0)
                            pieces.Add((textToken, null, inCode));
                    }

                    break;
                case XmlCrefAttributeSyntax cref:
                    pieces.Add((null, cref.Cref, false));
                    break;
            }
        }

        var result = new List<(int, string, bool, ImmutableArray<TwinMarkerTarget>)>();
        for (var i = 0; i < pieces.Count; i++)
        {
            if (pieces[i].Text is not { } textToken)
                continue;
            var text = textToken.ValueText;
            for (var at = text.IndexOf(MarkerText, StringComparison.Ordinal); at >= 0;
                 at = text.IndexOf(MarkerText, at + MarkerText.Length, StringComparison.Ordinal))
            {
                var position = textToken.SpanStart + at;
                var words = WordsOf(documentation, position);
                if (pieces[i].InCode)
                {
                    result.Add((position, words, true, []));
                    continue;
                }

                var rest = text[(at + MarkerText.Length)..];
                if (rest.Trim().Length != 0)
                {
                    // A PARTIAL mirror: "MIRROR OF the <part> of <see cref="X"/>" names X as its counterpart.
                    var trimmed = rest.Trim();
                    if (trimmed.StartsWith("the ", StringComparison.Ordinal) && trimmed.EndsWith(" of", StringComparison.Ordinal)
                        && i + 1 < pieces.Count && pieces[i + 1].Cref is { } partOf)
                    {
                        result.Add((position, words, false, [TargetOf(partOf, aliases)]));
                        continue;
                    }

                    result.Add((position, words, false, LineCommentTargets(rest, aliases)));
                    continue;
                }

                var targets = ImmutableArray.CreateBuilder<TwinMarkerTarget>();
                var j = i + 1;
                while (j < pieces.Count && pieces[j].Cref is { } cref)
                {
                    targets.Add(TargetOf(cref, aliases));
                    if (j + 2 < pieces.Count && pieces[j + 1].Text is { } separator && separator.ValueText.Trim() == "/" && pieces[j + 2].Cref is not null)
                        j += 2;
                    else
                    {
                        // `<see cref="A"/> / B`: a further counterpart spelled as text is read too (ambiguous).
                        if (j + 1 < pieces.Count && pieces[j + 1].Text is { } tail
                            && tail.ValueText.TrimStart() is ['/', .. var afterSlash])
                            targets.AddRange(LineCommentTargets(afterSlash, aliases));
                        break;
                    }
                }

                result.Add((position, words, false, targets.ToImmutable()));
            }
        }

        return result;
    }

    private static List<(int Position, string Words, bool Prose, ImmutableArray<TwinMarkerTarget> Targets)> LineCommentOccurrences(
        SyntaxTrivia trivia, Dictionary<string, TypeSyntax> aliases)
    {
        var text = trivia.ToString();
        var result = new List<(int, string, bool, ImmutableArray<TwinMarkerTarget>)>();
        for (var at = text.IndexOf(MarkerText, StringComparison.Ordinal); at >= 0;
             at = text.IndexOf(MarkerText, at + MarkerText.Length, StringComparison.Ordinal))
        {
            result.Add((trivia.SpanStart + at, FirstLine(text[at..]), false, LineCommentTargets(text[(at + MarkerText.Length)..], aliases)));
        }

        return result;
    }

    private static TwinMarkerTarget TargetOf(CrefSyntax cref, Dictionary<string, TypeSyntax> aliases)
        => cref switch
        {
            NameMemberCrefSyntax member => new TwinMarkerTarget(
                member.Name is GenericNameSyntax generic ? generic.Identifier.ValueText : member.Name.ToString(),
                member.Parameters is { } parameters
                    ? [.. parameters.Parameters.Select(p => Canonical(p.Type, aliases))]
                    : null),
            QualifiedCrefSyntax qualified => TargetOf(qualified.Member, aliases) with
            {
                ContainingType = Compact(qualified.Container.ToString()),
            },
            _ => new TwinMarkerTarget(cref.ToString(), null),
        };

    /// <summary>
    /// Reads the counterpart of a line-comment marker with the C# lexer: a PascalCase identifier right after
    /// the words, and a parenthesized parameter-type list if one follows it. Prose (<c>MIRROR OF the …</c>)
    /// names no counterpart. A further counterpart introduced by <c>/</c> (<c>MIRROR OF A / B</c>) is read
    /// too, so the marker is reported as ambiguous instead of silently resolving to its first name.
    /// </summary>
    private static ImmutableArray<TwinMarkerTarget> LineCommentTargets(string rest, Dictionary<string, TypeSyntax> aliases)
    {
        var tokens = SyntaxFactory.ParseTokens(rest).Where(static t => !t.IsKind(SyntaxKind.EndOfFileToken)).ToList();
        var targets = ImmutableArray.CreateBuilder<TwinMarkerTarget>();
        var at = 0;
        while (at < tokens.Count && tokens[at].IsKind(SyntaxKind.IdentifierToken) && char.IsUpper(tokens[at].ValueText[0]))
        {
            targets.Add(LineCommentTarget(tokens, ref at, aliases));
            if (at >= tokens.Count || !tokens[at].IsKind(SyntaxKind.SlashToken))
                break;
            at++;
        }

        return targets.ToImmutable();
    }

    /// <summary>One counterpart at <paramref name="at"/>: its name and, when a closed parameter-type list follows, its types.</summary>
    private static TwinMarkerTarget LineCommentTarget(List<SyntaxToken> tokens, ref int at, Dictionary<string, TypeSyntax> aliases)
    {
        var name = tokens[at].ValueText;
        at++;
        if (at >= tokens.Count || !tokens[at].IsKind(SyntaxKind.OpenParenToken))
            return new TwinMarkerTarget(name, null);

        var parameters = new List<string>();
        var current = new StringBuilder();
        var depth = 0;
        for (var i = at + 1; i < tokens.Count; i++)
        {
            var token = tokens[i];
            if (depth == 0 && token.IsKind(SyntaxKind.CloseParenToken))
            {
                if (current.Length > 0)
                    parameters.Add(current.ToString());
                at = i + 1;
                return new TwinMarkerTarget(name, [.. parameters.Select(p => Canonical(SyntaxFactory.ParseTypeName(p), aliases))]);
            }

            if (token.IsKind(SyntaxKind.LessThanToken) || token.IsKind(SyntaxKind.OpenParenToken))
                depth++;
            else if (token.IsKind(SyntaxKind.GreaterThanToken) || token.IsKind(SyntaxKind.CloseParenToken))
                depth--;
            if (depth == 0 && token.IsKind(SyntaxKind.CommaToken))
            {
                parameters.Add(current.ToString());
                current.Clear();
                continue;
            }

            current.Append(token.Text).Append(' ');
        }

        // An unclosed list: the name alone, and nothing after it is read.
        at = tokens.Count;
        return new TwinMarkerTarget(name, null);
    }

    // ── Resolution ──────────────────────────────────────────────────────────

    /// <summary>
    /// Resolves a marker's counterpart: a method or local function of that name in the twin's own type
    /// (partial declarations merged), else anywhere in <c>src/KatLang/</c>. A qualified cref restricts the
    /// search to its containing type; it never falls back to a same-named member of another type. Overloads are told apart by the
    /// parameter types the marker spells; a marker that spells none must then name exactly one method.
    /// </summary>
    private static TwinMethod? Resolve(TwinMethod twin, TwinMarkerTarget target, List<TwinMethod> methods, out string reason)
    {
        var named = methods.Where(m => m.Name == target.Name && m != twin).ToList();
        var sameType = named.Where(m => m.TypeName == twin.TypeName).ToList();
        var candidates = target.ContainingType is { } containingType
            ? named.Where(m =>
            {
                var qualifiedType = string.Join(".", m.Declaration.Ancestors().OfType<BaseNamespaceDeclarationSyntax>()
                    .Reverse().Select(static n => n.Name.ToString()).Append(m.TypeName));
                return containingType.StartsWith("global::", StringComparison.Ordinal)
                    ? qualifiedType == containingType["global::".Length..]
                    : qualifiedType == containingType || qualifiedType.EndsWith("." + containingType, StringComparison.Ordinal);
            }).ToList()
            : sameType.Count > 0 ? sameType : named;
        if (candidates.Count == 0)
        {
            reason = $"no method or local function named '{target.Name}' exists"
                + (target.ContainingType is { } type ? $" in containing type '{type}'" : "");
            return null;
        }

        if (target.ParameterTypes is { } types)
        {
            var exact = candidates.Where(m => m.CanonicalParameterTypes.SequenceEqual(types, StringComparer.Ordinal)).ToList();
            if (exact.Count == 1)
            {
                reason = "";
                return exact[0];
            }

            reason = exact.Count == 0
                ? $"no overload of '{target.Name}' has the parameter types ({string.Join(", ", types)}); candidates: "
                    + string.Join("; ", candidates.Select(static c => c.Key + " at " + c.File + ":" + c.Line))
                : $"several methods named '{target.Name}' have the parameter types ({string.Join(", ", types)})";
            return null;
        }

        if (candidates.Count == 1)
        {
            reason = "";
            return candidates[0];
        }

        reason = $"'{target.Name}' is ambiguous ({candidates.Count} candidates: "
            + string.Join("; ", candidates.Select(static c => c.Key + " at " + c.File + ":" + c.Line))
            + "); spell the parameter types in the marker's cref";
        return null;
    }

    // ── Canonical types ─────────────────────────────────────────────────────

    private static ImmutableArray<string> CanonicalTypes(ParameterListSyntax parameters, Dictionary<string, TypeSyntax> aliases)
        => [.. parameters.Parameters.Select(p => p.Type is null ? "" : Canonical(p.Type, aliases))];

    /// <summary>A type spelled canonically: global aliases expanded, namespace qualifiers dropped, tuples as <c>ValueTuple</c>, cref braces as angle brackets.</summary>
    private static string Canonical(TypeSyntax type, Dictionary<string, TypeSyntax> aliases)
        => type switch
        {
            IdentifierNameSyntax identifier when aliases.TryGetValue(identifier.Identifier.ValueText, out var target)
                => Canonical(target, aliases),
            IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
            GenericNameSyntax generic => generic.Identifier.ValueText + "<"
                + string.Join(", ", generic.TypeArgumentList.Arguments.Select(a => Canonical(a, aliases))) + ">",
            QualifiedNameSyntax qualified => Canonical(qualified.Right, aliases),
            AliasQualifiedNameSyntax aliasQualified => Canonical(aliasQualified.Name, aliases),
            NullableTypeSyntax nullable => Canonical(nullable.ElementType, aliases) + "?",
            ArrayTypeSyntax array => Canonical(array.ElementType, aliases) + string.Concat(array.RankSpecifiers.Select(static r => Compact(r.ToString()))),
            TupleTypeSyntax tuple => "ValueTuple<" + string.Join(", ", tuple.Elements.Select(e => Canonical(e.Type, aliases))) + ">",
            RefTypeSyntax reference => "ref " + Canonical(reference.Type, aliases),
            PredefinedTypeSyntax predefined => predefined.Keyword.ValueText,
            _ => Compact(type.ToString()),
        };

    // ── Normalization and comparison ────────────────────────────────────────

    /// <summary>
    /// Compares a pair after replacing its twin's declaration with an edited copy, under the inventory's
    /// normalization: the guard's own self-test of a one-sided edit.
    /// </summary>
    internal static TwinComparison CompareReplacingTwin(TwinInventory inventory, TwinPair pair, MethodDeclarationSyntax replacement)
    {
        var twin = new TwinMethod(pair.Twin.File, pair.Twin.TypeName, pair.Twin.Name, pair.Twin.OuterName, replacement,
            replacement.ParameterList, replacement.ReturnType, replacement.Modifiers, replacement.Body, replacement.ExpressionBody,
            pair.Twin.Line, pair.Twin.CanonicalParameterTypes);
        return Compare(pair with { Twin = twin }, new Normalizer(inventory.TwinRenames));
    }

    private static TwinComparison Compare(TwinPair pair, Normalizer normalizer)
    {
        var counterpart = NormalizedTokens(pair.Counterpart, normalizer);
        var twin = NormalizedTokens(pair.Twin, normalizer.ForTwin());
        return new TwinComparison(pair, counterpart, twin, Diff(counterpart, twin));
    }

    /// <summary>The normalized token stream of a member: its parameter list, then its body.</summary>
    private static ImmutableArray<string> NormalizedTokens(TwinMethod method, Normalizer normalizer)
    {
        var builder = ImmutableArray.CreateBuilder<string>();
        builder.AddRange(TokensOf(normalizer.Visit(method.Parameters)));
        if (method.Body is { } body)
            builder.AddRange(TokensOf(normalizer.Visit(body)));
        else if (method.ExpressionBody is { } arrow)
        {
            builder.Add("{");
            var statementForm = method.ReturnType is PredefinedTypeSyntax { Keyword.RawKind: (int)SyntaxKind.VoidKeyword }
                || method.ReturnType is IdentifierNameSyntax { Identifier.ValueText: "Task" or "ValueTask" };
            if (!statementForm)
                builder.Add("return");
            builder.AddRange(TokensOf(normalizer.Visit(arrow.Expression)));
            builder.Add(";");
            builder.Add("}");
        }

        return builder.ToImmutable();
    }

    private sealed class Normalizer(ImmutableDictionary<string, string> renames, bool normalizeBlockingAdapter = true) : CSharpSyntaxRewriter
    {
        internal Normalizer ForTwin() => new(renames, normalizeBlockingAdapter: false);

        public override SyntaxNode? VisitAwaitExpression(AwaitExpressionSyntax node) => Visit(node.Expression);

        public override SyntaxNode? VisitInvocationExpression(InvocationExpressionSyntax node)
        {
            // x.ConfigureAwait(false) → x
            if (node.Expression is MemberAccessExpressionSyntax { Name.Identifier.ValueText: "ConfigureAwait" } configure
                && node.ArgumentList.Arguments is [{ Expression: var argument }]
                && argument.IsKind(SyntaxKind.FalseLiteralExpression))
                return Visit(configure.Expression);

            // x.GetAwaiter().GetResult() → x
            if (normalizeBlockingAdapter
                && node.Expression is MemberAccessExpressionSyntax { Name.Identifier.ValueText: "GetResult" } getResult
                && node.ArgumentList.Arguments.Count == 0
                && getResult.Expression is InvocationExpressionSyntax
                {
                    Expression: MemberAccessExpressionSyntax { Name.Identifier.ValueText: "GetAwaiter" } getAwaiter,
                    ArgumentList.Arguments.Count: 0,
                })
                return Visit(getAwaiter.Expression);

            return base.VisitInvocationExpression(node);
        }

        public override SyntaxNode? VisitArgument(ArgumentSyntax node)
        {
            // asynchronous: true → asynchronous: false
            if (node.NameColon?.Name.Identifier.ValueText == FlagName && node.Expression.IsKind(SyntaxKind.TrueLiteralExpression))
                return node.WithExpression(SyntaxFactory.LiteralExpression(SyntaxKind.FalseLiteralExpression));
            return base.VisitArgument(node);
        }

        public override SyntaxToken VisitToken(SyntaxToken token)
        {
            if (token.IsKind(SyntaxKind.IdentifierToken))
            {
                // A twin's name → its counterpart's name; otherwise XAsync → X.
                if (renames.TryGetValue(token.ValueText, out var counterpart))
                    return SyntaxFactory.Identifier(counterpart);
                if (token.ValueText.Length > "Async".Length && token.ValueText.EndsWith("Async", StringComparison.Ordinal))
                    return SyntaxFactory.Identifier(token.ValueText[..^"Async".Length]);
            }

            return base.VisitToken(token);
        }
    }

    /// <summary>
    /// Token-level difference, as positioned runs of removed synchronous tokens and added twin tokens: the common
    /// prefix and suffix are matched first, then Myers' O(ND) algorithm aligns the middle (keeping only
    /// each round's live diagonals, so memory is O(D²)). Deterministic, so its rendering and hash are
    /// stable for an unchanged pair.
    /// </summary>
    internal static ImmutableArray<TwinDiffHunk> Diff(ImmutableArray<string> a, ImmutableArray<string> b)
    {
        var prefix = 0;
        while (prefix < a.Length && prefix < b.Length && string.Equals(a[prefix], b[prefix], StringComparison.Ordinal))
            prefix++;
        var suffix = 0;
        while (suffix < a.Length - prefix && suffix < b.Length - prefix
               && string.Equals(a[a.Length - 1 - suffix], b[b.Length - 1 - suffix], StringComparison.Ordinal))
            suffix++;

        var edits = MyersEdits(
            a.AsSpan(prefix, a.Length - prefix - suffix).ToArray(),
            b.AsSpan(prefix, b.Length - prefix - suffix).ToArray());

        var hunks = ImmutableArray.CreateBuilder<TwinDiffHunk>();
        var removed = new List<string>();
        var added = new List<string>();
        var counterpartOffset = prefix;
        var twinOffset = prefix;
        foreach (var (op, token) in edits)
        {
            switch (op)
            {
                case '-':
                    removed.Add(token);
                    break;
                case '+':
                    added.Add(token);
                    break;
                default:
                    Flush();
                    counterpartOffset++;
                    twinOffset++;
                    break;
            }
        }

        Flush();
        return hunks.ToImmutable();

        void Flush()
        {
            if (removed.Count == 0 && added.Count == 0)
                return;
            hunks.Add(new TwinDiffHunk(counterpartOffset, twinOffset, [.. removed], [.. added]));
            counterpartOffset += removed.Count;
            twinOffset += added.Count;
            removed.Clear();
            added.Clear();
        }
    }

    private static List<(char Op, string Token)> MyersEdits(string[] a, string[] b)
    {
        int n = a.Length, m = b.Length, max = n + m;
        var edits = new List<(char Op, string Token)>();
        if (max == 0)
            return edits;

        // v[o + k] is the furthest x on diagonal k; snapshots[d] holds v over k ∈ [-d-1, d+1] as it stood
        // when round d began.
        var o = max + 1;
        var v = new int[2 * max + 3];
        var snapshots = new List<int[]>();
        var rounds = 0;
        for (var d = 0; d <= max; d++)
        {
            snapshots.Add(v.AsSpan(o - d - 1, 2 * d + 3).ToArray());
            var done = false;
            for (var k = -d; k <= d; k += 2)
            {
                var x = k == -d || (k != d && v[o + k - 1] < v[o + k + 1])
                    ? v[o + k + 1]
                    : v[o + k - 1] + 1;
                var y = x - k;
                while (x < n && y < m && string.Equals(a[x], b[y], StringComparison.Ordinal))
                {
                    x++;
                    y++;
                }

                v[o + k] = x;
                if (x >= n && y >= m)
                {
                    done = true;
                    break;
                }
            }

            rounds = d;
            if (done)
                break;
        }

        int cx = n, cy = m;
        for (var d = rounds; d > 0; d--)
        {
            var snapshot = snapshots[d];
            var round = d;
            int At(int diagonal) => snapshot[diagonal + round + 1];
            var k = cx - cy;
            var prevK = k == -d || (k != d && At(k - 1) < At(k + 1)) ? k + 1 : k - 1;
            var prevX = At(prevK);
            var prevY = prevX - prevK;
            while (cx > prevX && cy > prevY)
            {
                edits.Add(('=', a[cx - 1]));
                cx--;
                cy--;
            }

            if (cx == prevX)
            {
                edits.Add(('+', b[cy - 1]));
                cy--;
            }
            else
            {
                edits.Add(('-', a[cx - 1]));
                cx--;
            }
        }

        while (cx > 0 && cy > 0)
        {
            edits.Add(('=', a[cx - 1]));
            cx--;
            cy--;
        }

        edits.Reverse();
        return edits;
    }

    // ── The `bool asynchronous` pattern ─────────────────────────────────────

    /// <summary>
    /// Every read of a method's own <c>bool asynchronous</c> parameter that is NOT merely passed on as an
    /// argument: each such read selects between the asynchronous and the synchronous behavior. The
    /// branch point is the smallest enclosing <c>if</c> statement, conditional expression, or other
    /// statement, hashed after normalization so an edit to either arm is visible.
    /// </summary>
    private static IEnumerable<FlagBranchPoint> BranchPointsOf(TwinMethod method, Normalizer normalizer)
    {
        var bodyNode = (SyntaxNode?)method.Body ?? method.ExpressionBody;
        if (bodyNode is null)
            yield break;
        var ordinal = 0;
        foreach (var identifier in bodyNode.DescendantNodes().OfType<IdentifierNameSyntax>())
        {
            if (identifier.Identifier.ValueText != FlagName)
                continue;
            // A nested local function or lambda that declares its own flag owns the reads below it.
            if (identifier.Ancestors().TakeWhile(a => a != method.Declaration).Any(static a =>
                    (a is LocalFunctionStatementSyntax local && local.ParameterList.Parameters.Any(static p => p.Identifier.ValueText == FlagName))
                    || (a is ParenthesizedLambdaExpressionSyntax lambda && lambda.ParameterList.Parameters.Any(static p => p.Identifier.ValueText == FlagName))))
                continue;
            if (identifier.Parent is ArgumentSyntax || identifier.Parent is NameColonSyntax)
                continue;

            var construct = identifier.Ancestors().First(static a =>
                a is ConditionalExpressionSyntax or SwitchExpressionSyntax or StatementSyntax or ArrowExpressionClauseSyntax);
            var text = string.Join(" ", TokensOf(normalizer.Visit(construct)));
            var mirror = construct switch
            {
                ConditionalExpressionSyntax { Condition: IdentifierNameSyntax { Identifier.ValueText: FlagName } } conditional
                    => TokensOf(normalizer.Visit(conditional.WhenTrue)).SequenceEqual(TokensOf(normalizer.Visit(conditional.WhenFalse)), StringComparer.Ordinal),
                IfStatementSyntax { Condition: IdentifierNameSyntax { Identifier.ValueText: FlagName }, Else: { } otherwise } branch
                    => TokensOf(normalizer.Visit(branch.Statement)).SequenceEqual(TokensOf(normalizer.Visit(otherwise.Statement)), StringComparer.Ordinal),
                _ => false,
            };
            yield return new FlagBranchPoint(method, ordinal++, construct.Kind().ToString(), Hash(text), text, mirror);
        }
    }

    /// <summary>
    /// A call that passes <c>asynchronous: true</c> and then blocks on it with
    /// <c>.GetAwaiter().GetResult()</c>: sync-over-async, which the pattern never allows.
    /// </summary>
    private static IEnumerable<string> BlockingFlagCallsOf(string file, RoslynSyntaxTree tree)
    {
        foreach (var invocation in tree.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            if (!invocation.ArgumentList.Arguments.Any(static a =>
                    a.NameColon?.Name.Identifier.ValueText == FlagName && a.Expression.IsKind(SyntaxKind.TrueLiteralExpression)))
                continue;
            if (invocation.Parent is MemberAccessExpressionSyntax { Name.Identifier.ValueText: "GetAwaiter" })
                yield return file + ":" + LineOf(tree, invocation.SpanStart) + ": " + Compact(invocation.ToString());
        }
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static IEnumerable<string> TokensOf(SyntaxNode? node)
        => node is null
            ? []
            : node.DescendantTokens().Where(static t => !t.IsKind(SyntaxKind.AsyncKeyword) && !t.IsMissing && t.Text.Length != 0)
                .Select(static t => t.Text);

    internal static string Hash(string text)
        => Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(text)))[..16].ToLowerInvariant();

    internal static string Compact(string text)
        => string.Join(" ", text.Split((char[])[' ', '\t', '\r', '\n'], StringSplitOptions.RemoveEmptyEntries))
            .Replace(" ,", ",", StringComparison.Ordinal);

    /// <summary>The marker's words from <c>MIRROR OF</c> to the end of its source line, documentation markup kept.</summary>
    private static string WordsOf(DocumentationCommentTriviaSyntax documentation, int position)
    {
        var text = documentation.SyntaxTree!.GetText();
        var line = text.Lines.GetLineFromPosition(position);
        return FirstLine(text.ToString(RoslynTextSpan.FromBounds(position, line.End)));
    }

    private static string FirstLine(string text)
    {
        var line = text.Split('\n')[0].Replace("\r", "", StringComparison.Ordinal);
        foreach (var end in new[] { "</summary>", "*/" })
        {
            var at = line.IndexOf(end, StringComparison.Ordinal);
            if (at >= 0)
                line = line[..at];
        }

        return Compact(line);
    }

    private static string TypeNameOf(SyntaxNode node)
        => string.Join(".", node.Ancestors().OfType<BaseTypeDeclarationSyntax>().Reverse().Select(static t => t.Identifier.ValueText));

    private static string? OuterMemberName(LocalFunctionStatementSyntax local)
    {
        var names = local.Ancestors()
            .TakeWhile(static a => a is not BaseTypeDeclarationSyntax)
            .Select(static a => a switch
            {
                LocalFunctionStatementSyntax l => l.Identifier.ValueText,
                MethodDeclarationSyntax m => m.Identifier.ValueText,
                ConstructorDeclarationSyntax => ".ctor",
                PropertyDeclarationSyntax p => p.Identifier.ValueText,
                AccessorDeclarationSyntax accessor => accessor.Keyword.ValueText,
                _ => null,
            })
            .Where(static n => n is not null)
            .Reverse()
            .ToList();
        return names.Count == 0 ? "?" : string.Join(".", names);
    }

    private static int LineOf(RoslynSyntaxTree tree, int position)
        => tree.GetLineSpan(new RoslynTextSpan(position, 0)).StartLinePosition.Line + 1;
}
