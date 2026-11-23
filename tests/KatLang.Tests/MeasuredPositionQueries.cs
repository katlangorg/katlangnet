using KatLang.Semantics;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Text;

namespace KatLang.Tests;

/// <summary>
/// The work checks of the editor's position queries count the probes of
/// <see cref="SemanticModel.FindScopeAtCounted"/> and <see cref="SemanticModel.FindResolutionAtCounted"/>.
/// Those seams run the generic search core with a counting probe. The counts bound the public
/// <see cref="SemanticModel.FindScopeAt"/> and <see cref="SemanticModel.FindResolutionAt"/> only while each
/// public query runs that same core and nothing else. Work written into the public one-line wrapper
/// returns the same answers outside the counted core. An indexed walk of an array or a list allocates
/// nothing, so it also passes the queries' allocation bounds. Nothing at run time can see such a walk
/// without timing, so this check reads <c>SemanticModel.cs</c> and requires three things:
/// <list type="number">
///   <item>the public query's whole body is ONE call of the core with the uncounted probe, passing the
///   query's own position;</item>
///   <item>the counted seam calls that core exactly once, with the counting probe and its own position;</item>
///   <item>the core is the only method of its name in the class, so both calls bind to the method the
///   seam measures.</item>
/// </list>
/// The check pins the delegation only. The core's algorithm stays free to change.
/// </summary>
internal static class MeasuredPositionQueries
{
    private const string UncountedProbes = "UncountedScopeProbes";
    private const string CountedProbes = "CountedScopeProbes";

    /// <summary>
    /// Requires the public <paramref name="query"/> and its <paramref name="countedSeam"/> to run the same
    /// generic <paramref name="core"/>, the query with nothing around the call (see the class summary).
    /// </summary>
    internal static void RequireDelegation(string query, string countedSeam, string core)
    {
        var path = Path.Combine(RepoRoot.Find(), "src", "KatLang", "Semantics", "SemanticModel.cs");
        var root = CSharpSyntaxTree.ParseText(File.ReadAllText(path)).GetRoot();
        var model = root.DescendantNodes().OfType<ClassDeclarationSyntax>()
            .Single(type => type.Identifier.ValueText == nameof(SemanticModel));
        // The class's own methods: nested types (the position index, the probe structs) do not count.
        var methods = model.Members.OfType<MethodDeclarationSyntax>().ToList();

        var cores = methods.Where(method => method.Identifier.ValueText == core).ToList();
        Assert.True(
            cores is [{ TypeParameterList.Parameters.Count: 1 }],
            $"SemanticModel must declare exactly one {core}<TProbes>, the core {countedSeam} measures; found {cores.Count}.");

        var publicQuery = Single(methods, query);
        var seam = Single(methods, countedSeam);
        // The syntax tree sees just one preprocessor branch. A conditional inside or around a
        // wrapper could hide a scan or select a different counted core in the compiled assembly.
        // Conditionals elsewhere, including inside the search itself, do not affect this check.
        foreach (var start in root.DescendantTrivia().Select(trivia => trivia.GetStructure()).OfType<IfDirectiveTriviaSyntax>())
        {
            var region = TextSpan.FromBounds(start.SpanStart, start.GetRelatedDirectives().Last().Span.End);
            Assert.False(region.OverlapsWith(publicQuery.Span) || region.OverlapsWith(seam.Span),
                $"The delegation from {query} and {countedSeam} to {core} must be visible in every preprocessor branch.");
        }

        var position = Assert.Single(publicQuery.ParameterList.Parameters).Identifier.ValueText;
        var body = publicQuery.ExpressionBody?.Expression
            ?? (publicQuery.Body?.Statements is [ReturnStatementSyntax returned] ? returned.Expression : null);
        Assert.True(
            body is not null && SyntaxFactory.AreEquivalent(CoreCall(core, UncountedProbes, position), body),
            $"{query} must delegate its entire search to {core}<{UncountedProbes}>({position}), the query {countedSeam} measures; "
                + $"its body is: {publicQuery.ExpressionBody?.ToString() ?? publicQuery.Body?.ToString()}");

        var seamPosition = seam.ParameterList.Parameters[0].Identifier.ValueText;
        var coreCalls = seam.DescendantNodes().OfType<InvocationExpressionSyntax>()
            .Where(call => call.Expression is GenericNameSyntax name && name.Identifier.ValueText == core)
            .ToList();
        Assert.True(
            coreCalls is [var counted] && SyntaxFactory.AreEquivalent(CoreCall(core, CountedProbes, seamPosition), counted),
            $"{countedSeam} must measure {query}'s core with exactly one call {core}<{CountedProbes}>({seamPosition}); "
                + $"found: [{string.Join(", ", coreCalls)}]");
    }

    private static MethodDeclarationSyntax Single(List<MethodDeclarationSyntax> methods, string name)
    {
        var matches = methods.Where(method => method.Identifier.ValueText == name).ToList();
        Assert.True(matches.Count == 1, $"SemanticModel must declare exactly one {name}; found {matches.Count}.");
        return matches[0];
    }

    private static ExpressionSyntax CoreCall(string core, string probes, string position)
        => SyntaxFactory.ParseExpression($"{core}<{probes}>({position})");
}
