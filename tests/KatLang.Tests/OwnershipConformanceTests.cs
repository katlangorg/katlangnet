using System.Text.RegularExpressions;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Independent Lean/C# classification conformance, separate from LeanAstEncoder's
/// execution parity. The hand-written Lean table supplies both owner inputs and
/// expected selections. These sources must elaborate to the corresponding owner
/// inputs and binding identities; no expectation is derived from the selector.
/// </summary>
public class OwnershipConformanceTests
{
    private sealed record SourceCase(string Source, string Path, string Display);

    private static readonly IReadOnlyDictionary<string, SourceCase> Sources = new Dictionary<string, SourceCase>
    {
        ["captured"] = new("v = 99\nOuter(v) = { Inner = v\nInner }\nOuter(7)", "Outer/Inner", "7"),
        ["same-owner-nested"] = new("Outer(v) = { v = 5\nInner = v\nInner }\nOuter(7)", "Outer/Inner", "7"),
        ["same-owner-direct"] = new("Outer(v) = { v = 5\nv }\nOuter(7)", "Outer", "7"),
        ["nearer-property"] = new("v = 99\nOuter(v) = { Mid = { v = 5\nInner = v\nInner }\nMid }\nOuter(7)", "Outer/Mid/Inner", "5"),
        ["nearest-parameter"] = new("v = 99\nOuter(v) = { Mid(v) = { Inner = v\nInner }\nMid(7) }\nOuter(20)", "Outer/Mid/Inner", "7"),
        ["inferred-later-row"] = new("Lib = { public v = 99 }\nOuter = { Inner = { open Lib\nv }\nInner, v }\nOuter(7)", "Outer/Inner", "(7, 7)"),
        ["lifted-later-reference"] = new("Lib = { public v = 99 }\nOuter = { Inner = { open Lib\nv }\nNeed = v\nInner + Need }\nOuter(7)", "Outer/Inner", "14"),
        ["lifted-collision"] = new("Need(v) = v\nOuter = { v = 5\nInner = v\nNeed + Inner }\nOuter(7)", "Outer/Inner", ""),
        ["lifted-ancestor-collision"] = new("Need(v) = v\nOuter = { Mid = { v = 5\nInner = v\nInner }\nNeed + Mid }\n0", "Outer/Mid/Inner", ""),
        ["inferred-ancestor-collision"] = new("Outer = { Inner = { v = 5\nv }\nv }\n0", "Outer/Inner", ""),
        ["collecting-collision"] = new("Outer(*v) = { v = 5\nInner = v\nInner }\nOuter(7, 20)", "Outer/Inner", ""),
        ["branch-binder"] = new("v = 99\nF(0) = 0\nF(v) = { v = 5\nInner = v\nInner }\nF(7)", "F/@1/Inner", "7"),
        ["branch-nearer-property"] = new("v = 99\nF(0) = 0\nF(v) = { Mid = { v = 5\nInner = v\nInner }\nMid }\nF(7)", "F/@1/Mid/Inner", "5"),
        ["grouped-parameter"] = new("v = 99\nOuter((v, w)) = { Inner = v\nInner }\nOuter((7, 20))", "Outer/Inner", "7"),
        ["collecting-parameter"] = new("v = 99\nOuter(*v) = { Inner = v\nInner }\nOuter(7, 20)", "Outer/Inner", "[7, 20]"),
        ["grouped-branch-binder"] = new("v = 99\nF((0, v)) = { v = 5\nInner = v\nInner }\nF((0, 7))", "F/@0/Inner", "7"),
        ["ancestor-property"] = new("v = 99\nOuter(q) = { Inner = v\nInner }\nOuter(7)", "Outer/Inner", "99"),
    };

    public static TheoryData<string, string, string, int, bool> Inputs()
    {
        var lean = File.ReadAllText(Path.Combine(RepoRoot.Find(), "lean", "CoreTests", "NameOwnership.lean"));
        var table = lean.Split("def ownershipConformanceInputs : List (String × List Nat × OwnedDeclaration × Bool) := [", StringSplitOptions.None)[1]
            .Split("\n]", StringSplitOptions.None)[0];
        var rows = new TheoryData<string, string, string, int, bool>();
        foreach (var line in table.Split('\n', StringSplitOptions.RemoveEmptyEntries).Where(line => !string.IsNullOrWhiteSpace(line)))
        {
            // Deliberately a small, fail-closed data grammar, not a Lean parser.
            var match = Regex.Match(line.Trim(), "^\\(\"([a-z-]+)\", \\[([0-3, ]+)\\], \\.(parameter|property) ([0-9]+), (true|false)\\),?$");
            Assert.True(match.Success, $"Unrecognized ownership conformance row: {line}");
            rows.Add(match.Groups[1].Value, match.Groups[2].Value, match.Groups[3].Value, int.Parse(match.Groups[4].Value), bool.Parse(match.Groups[5].Value));
        }
        Assert.Equal(Sources.Keys.Order(), rows.Select(row => (string)row[0]).Order());
        return rows;
    }

    [Theory]
    [MemberData(nameof(Inputs))]
    public void RealElaborationMatchesIndependentLeanOwnershipInput(string id, string masks, string kind, int ownerIndex, bool valid)
    {
        var test = Sources[id];
        var parsed = SourceProvenance.ParseAllowingDiagnostics(test.Source);
        if (valid)
            Assert.Empty(parsed.Diagnostics);
        else
            Assert.Equal(DiagnosticCode.ParameterPropertyCollision, Assert.Single(parsed.Diagnostics).Code);
        var levels = OwnerChain(parsed.Root, test.Path);
        Assert.Equal(masks.Split(',').Select(int.Parse), levels.Select(level =>
            (level.ParameterNames.Contains("v") ? 1 : 0) + (level.Algorithm.Properties.Any(p => p.Name == "v") ? 2 : 0)));

        var scopes = new ElaboratedPropertyScope[levels.Count];
        var parameters = ParameterOwnership.Empty;
        ElaboratedPropertyScope? parent = null;
        for (var i = levels.Count - 1; i >= 0; i--)
        {
            scopes[i] = ElaboratedScopeLookup.CreateScope(levels[i].Algorithm, parent);
            parameters = parameters.Extend(scopes[i], levels[i].ParameterNames);
            parent = scopes[i];
        }

        var selected = ElaboratedScopeLookup.SelectOwnedDeclaration(scopes[0], "v", parameters);
        Assert.Equal(kind == "parameter" ? OwnedDeclarationKind.Parameter : OwnedDeclarationKind.Property, selected.Kind);
        Assert.Same(scopes[ownerIndex], selected.OwnerScope);
        var decidingOwner = levels[ownerIndex];
        var reference = Assert.Single(levels[0].Algorithm.Output);
        SourceSpan? declaration;
        IdentifierClassification classification;
        if (kind == "parameter")
        {
            Assert.Equal("v", Assert.IsType<Expr.Param>(reference).Name);
            Assert.Null(selected.PropertyHit);
            declaration = decidingOwner.Binder is null
                ? decidingOwner.Algorithm.ExplicitParameters.SingleOrDefault(p => p.Name == "v")?.Span
                : BinderSpan(decidingOwner.Binder, "v");
            classification = decidingOwner.Binder is not null ? IdentifierClassification.ConditionalBinderReference
                : declaration is not null ? IdentifierClassification.ExplicitParameterReference
                : IdentifierClassification.ImplicitParameterReference;
        }
        else
        {
            Assert.Equal("v", Assert.IsType<Expr.Resolve>(reference).Name);
            var property = decidingOwner.Algorithm.Properties.Single(p => p.Name == "v");
            Assert.Same(property, selected.PropertyHit!.Value.Property);
            Assert.Same(decidingOwner.Algorithm, selected.PropertyHit.Value.Owner);
            Assert.Same(property, ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scopes[0], "v")!.Value.Property);
            declaration = property.DeclarationSpans.Single();
            classification = IdentifierClassification.PropertyReference;
        }

        var model = SemanticModelBuilder.Build(parsed.Root);
        var site = reference.Span!;
        var resolution = model.FindResolutionAt(site.StartLineNumber, site.StartColumn);
        Assert.NotNull(resolution);
        Assert.Equal(classification, resolution.Classification);
        Assert.Equal(declaration, resolution.ResolvedDeclaration?.Span);
        var visible = Assert.Single(model.GetVisibleSymbolsAt(site.StartLineNumber, site.StartColumn), symbol => symbol.Name == "v");
        Assert.Equal(classification, visible.Classification);
        Assert.Equal(declaration, visible.Declaration?.Span);
        var propertyInfo = model.FindPropertyAt(site.StartLineNumber, site.StartColumn);
        if (kind == "parameter")
        {
            Assert.Null(propertyInfo);
            Assert.Null(visible.Property);
        }
        else
        {
            Assert.NotNull(propertyInfo);
            Assert.Equal(declaration, propertyInfo.Declaration?.Span);
            Assert.Same(propertyInfo, visible.Property);
        }
        if (valid)
            Assert.Equal(test.Display, Assert.IsType<RunResult.Success>(KatLangEngine.Run(test.Source)).ToDisplayString());
        else
            Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(test.Source));
    }

    private sealed record Level(Algorithm Algorithm, Pattern? Binder = null)
    {
        public IEnumerable<string> ParameterNames => Binder?.BoundNames() ?? Algorithm.Params;
    }

    private static List<Level> OwnerChain(Algorithm root, string path)
    {
        var chain = new List<Level> { new(root) };
        var current = root;
        foreach (var step in path.Split('/'))
        {
            if (step.StartsWith('@'))
            {
                var branch = current.Branches[int.Parse(step[1..])];
                current = branch.Body;
                chain.Add(new(current, branch.Pattern));
            }
            else
            {
                current = current.Properties.Single(property => property.Name == step).Value;
                // Detector families with no family-owned opens add no owner level.
                if (current is not Algorithm.Conditional || current.Opens.Count > 0)
                    chain.Add(new(current));
            }
        }
        chain.Reverse();
        return chain;
    }

    private static SourceSpan? BinderSpan(Pattern pattern, string name) => pattern switch
    {
        Pattern.Bind bind => bind.Name == name ? bind.NameSpan : null,
        Pattern.SequenceValue group => group.Items.Select(child => BinderSpan(child, name)).FirstOrDefault(span => span is not null),
        Pattern.LitInt or Pattern.LitString => null,
        _ => throw new InvalidOperationException($"Unhandled pattern: {pattern.GetType().Name}"),
    };
}
