using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// MOD-03 / RES-09 (constitution audit C-2): one <c>open</c> provides one set of names to every layer.
/// A transparent reference <c>A = Lib.Sub</c> is an ordinary dot reference, so its own path selects DECLARED
/// members in its lexical owner, and <c>open A</c> then provides the PUBLIC members of the target, never
/// its private ones. A WRITTEN open path (<c>open Lib.Sub</c>) still selects public members only. The
/// namespace certificate, which may prove an opened name absent while Q2 is pending, must walk a reference
/// path as exactly that: a certificate that read it as a written open path "proved" a provided name absent,
/// so the name silently became an implicit parameter. Lean: <c>openNavigateWith</c>, <c>openStructure</c>; the
/// executable counterpart is the <c>open-reference-private-*</c> spec cases.
/// </summary>
public class OpenReferenceProviderAdmissionTests
{
    private const string PrivateSub = "Lib = { Sub = { public Q(x) = x + 1 } }\n";

    private static string Outcome(RunResult result) => result switch
    {
        RunResult.Success success => "ok " + success.ToDisplayString(),
        RunResult.EvalFailure failure => "err " + string.Join(", ", failure.Errors.Select(static error => error.Code)),
        RunResult.ParseFailure failure => "front " + string.Join(", ", failure.Errors.Select(static error => error.Code)),
        _ => result.GetType().Name,
    };

    [Theory]
    // The written use agrees with the audit's parameter-receiver route, which already reached the provider.
    [InlineData("open A\n" + PrivateSub + "A = Lib.Sub\nQ(5)")]
    [InlineData("open A\n" + PrivateSub + "A = Lib.Sub\nG(p) = p.Q\nG(5)")]
    [InlineData("open A\nLib = { public Sub = { public Q(x) = x + 1 } }\nA = Lib.Sub\nQ(5)")]
    // Every receiver on the path may be private, or itself a reference.
    [InlineData("open A\nLib = { Sub = { Deep = { public Q(x) = x + 1 } } }\nA = Lib.Sub.Deep\nQ(5)")]
    [InlineData("open A\n" + PrivateSub + "L = Lib\nA = L.Sub\nQ(5)")]
    [InlineData("open A\n" + PrivateSub + "B = Lib.Sub\nA = B\nQ(5)")]
    // One provider through two references; a nested opener.
    [InlineData("open A, B\n" + PrivateSub + "A = Lib.Sub\nB = Lib.Sub\nQ(5)")]
    [InlineData("Outer = { open A\n" + PrivateSub + "A = Lib.Sub\npublic R = Q(5) }\nOuter.R")]
    public async Task ProvidedName_IsAdmittedByEveryLayer(string source)
    {
        Assert.Equal("ok 6", Outcome(KatLangEngine.Run(source)));
        var demands = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("later", async (arguments, _) =>
            {
                await Task.Yield();
                demands++;
                return arguments[0];
            }, "x")),
        };
        var suspendedSource = source.Replace("(5)", "(later(5))", StringComparison.Ordinal);
        Assert.Equal("ok 6", Outcome(await KatLangEngine.RunAsync(suspendedSource, options)));
        Assert.Equal(1, demands);
    }

    [Theory]
    // A private member of the target is never opened: the name stays unresolved.
    [InlineData("open A\nLib = { Sub = { Q(x) = x + 1 } }\nA = Lib.Sub\nQ(5)", "err UnresolvedImplicitParams")]
    // An open of the container provides its public members only.
    [InlineData("open Lib\n" + PrivateSub + "Q(5)", "err UnresolvedImplicitParams")]
    // A carrier opens its own public declarations, never its target's.
    [InlineData("open A\n" + PrivateSub + "A = { Lib.Sub }\nQ(5)", "err UnresolvedImplicitParams")]
    // A WRITTEN open path selects public members, through a reference head too.
    [InlineData("open Lib.Sub\n" + PrivateSub + "Q(5)", "front UnresolvedOpenTarget")]
    [InlineData("open A.Sub\n" + PrivateSub + "A = Lib\nQ(5)", "front UnresolvedOpenTarget")]
    // Two different providers stay ambiguous.
    [InlineData("open A, C\n" + PrivateSub + "A = Lib.Sub\nC = { public Q(x) = x + 2 }\nQ(5)", "front AmbiguousOpen")]
    public void InaccessibleOrAmbiguousName_StaysRefused(string source, string expected)
        => Assert.Equal(expected, Outcome(KatLangEngine.Run(source)));

    [Fact]
    public void MemberWhoseOwnerActivationIsUnavailable_StaysLocalOnly()
    {
        const string source = "open A\nF(v) = { Sub = { public Q = v\n0 }\n1 }\nA = F.Sub\nQ";
        Assert.Equal("err LocalOnlyProperty", Outcome(KatLangEngine.Run(source)));
    }

    [Fact]
    public void ProvidedName_BindsTheTargetDeclarationInTheEditor()
    {
        const string source = "open A\n" + PrivateSub + "A = Lib.Sub\nQ(5)";
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors);
        var model = SemanticModelBuilder.Build(parsed);
        var declaration = Assert.Single(model.FindDeclarations("Q"));
        Assert.Equal(declaration, model.FindResolutionAt(new SourcePosition(4, 1))?.ResolvedDeclaration);
    }

    [Fact]
    public void LexicalPrecedence_StillBeatsTheProvider()
        => Assert.Equal("ok 105", Outcome(KatLangEngine.Run("open A\n" + PrivateSub + "A = Lib.Sub\nQ(x) = x + 100\nQ(5)")));

    [Fact]
    public void ACycleThroughTheProvider_StaysSafe()
        => Assert.Equal("ok 1", Outcome(KatLangEngine.Run("open A\nLib = { Sub = { public Q = A } }\nA = Lib.Sub\n1")));
}
