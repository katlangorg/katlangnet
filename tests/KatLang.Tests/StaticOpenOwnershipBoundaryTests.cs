using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>Completion, host-AST, module, and editor boundaries of static-open ownership.</summary>
public class StaticOpenOwnershipBoundaryTests
{
    [Theory]
    [InlineData("")]
    [InlineData("Lib = { public X = 7 }\n")]
    public void CompletedEnclosingParameter_RemovesEarlierStaticProvider(string farther)
    {
        const string body = "Need(Lib) = 0\nOuter = {\n    Inner(q) = {\n        open Lib\n        X\n    }\n    Inner(1) + Need\n}\nOuter(3)";
        var parsed = Parser.Parse(farther + body);
        Assert.Equal(
            new[] { DiagnosticCode.OpenTargetIsParameter, DiagnosticCode.UndeclaredIdentifier },
            parsed.Diagnostics.Select(d => d.Code));
        var outer = parsed.Root.Properties.Single(p => p.Name == "Outer").Value;
        Assert.Equal(["Lib"], outer.Params);
        var inner = outer.Properties.Single(p => p.Name == "Inner").Value;
        Assert.Equal("Lib", Assert.IsType<Expr.Param>(Assert.Single(inner.Opens)).Name);
        var line = farther.Length == 0 ? 4 : 5;
        var model = SemanticModelBuilder.Build(parsed);
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(line, 14));
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, resolution.Classification);
        Assert.Null(model.FindPropertyAt(line, 14));
        Assert.Null(resolution.ResolvedProperty);
    }

    [Fact]
    public void RootPhantom_DoesNotOwnNestedStaticHead_ButNestedCallableDoes()
    {
        const string source = "Q.X\nLibrary = {\n    Q = { public Y = 7 }\n    Reader = {\n        open Q\n        Y\n    }\n    Reader\n}\nLibrary";
        var parsed = SourceProvenance.ParseValid(source);
        Assert.Equal(["Q", "X"], parsed.Root.Params);
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(5, 14));
        Assert.Equal(IdentifierClassification.OpenTarget, resolution.Classification);
        Assert.Equal(new SourceSpan(3, 5, 3, 5), resolution.ResolvedDeclaration!.Span);
        Assert.Equal(KatLangErrorCode.UnresolvedImplicitParams,
            Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors).Code);

        const string callable = "Q.X\nF(Q) = {\n    open Q\n    1\n}\nF(3)";
        var invalid = Parser.Parse(callable);
        Assert.Equal(DiagnosticCode.OpenTargetIsParameter, Assert.Single(invalid.Diagnostics).Code);
        Assert.DoesNotContain(invalid.Diagnostics, d => d.Code == DiagnosticCode.ParameterPropertyCollision);
    }

    [Theory]
    [InlineData("Lib = { public X = 7 }\nF(Lib) = { open Lib\n1 }\nmap([1], F)")]
    [InlineData("F(Math) = { open Math\n1 }\nF(3)")]
    [InlineData("F(count) = { open count\n1 }\nF(3)")]
    [InlineData("F(Lib) = { a, b = { open Lib\n1, 2 }\na + b }\nF(3)")]
    [InlineData("F((Lib, *xs)) = { open Lib\n1 }\nF((1, 2))")]
    public void OtherBindingSurfaces_UseTheSameOwnershipRule(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.Equal(DiagnosticCode.OpenTargetIsParameter, Assert.Single(parsed.Diagnostics).Code);
    }

    [Fact]
    public void LongQualifiedTarget_WithCommentContinuation_KeepsEveryEditorCoordinate()
    {
        const string source = "Root = { public Sub = { public Leaf = { public X = 7 } } }\nF(Root) = {\n    open Root # continue\n        .Sub.Leaf\n    1\n}\nF(3)";
        var parsed = Parser.Parse(source);
        var error = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.OpenTargetIsParameter, error.Code);
        Assert.Equal(new SourceSpan(3, 10, 3, 13), error.Span);
        Assert.Contains("Cannot open 'Root.Sub.Leaf'", error.Message);
        var model = SemanticModelBuilder.Build(parsed);
        var head = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(3, 13));
        Assert.Equal(OccurrenceKind.OpenTargetReference, head.Occurrence.Kind);
        Assert.Equal(new SourceSpan(2, 3, 2, 6), head.ResolvedDeclaration!.Span);
        foreach (var column in new[] { 10, 14 })
        {
            var member = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(4, column));
            Assert.Equal(OccurrenceKind.OpenTargetMemberReference, member.Occurrence.Kind);
            Assert.Equal(IdentifierClassification.Unresolved, member.Classification);
            Assert.Null(member.ResolvedDeclaration);
            Assert.Null(model.FindPropertyAt(4, column));
        }
    }

    [Fact]
    public void SharedFamilyOpens_AreClassifiedInEachCapturedOwnerContext()
    {
        var head = new Expr.Resolve("Lib") { Span = new SourceSpan(2, 10, 2, 12) };
        var family = new Algorithm.Conditional(null, [head, head],
            [new CondBranch(new Pattern.Bind("n"), new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))]);
        var lib = new Algorithm.User(null, [], [], [new Property("X", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]), true)], []);
        var parent = new Algorithm.User(null, [new ParameterDeclaration("Lib")], [], [new Property("Family", family)], [new Expr.Num(1)]);
        var root = new Algorithm.User(null, [], [],
            [new Property("Lib", lib), new Property("Outer", parent), new Property("StaticFamily", family)], []);
        var detected = ParameterDetector.Detect(root);
        Assert.Equal(DiagnosticCode.OpenTargetIsParameter, Assert.Single(detected.Diagnostics).Code);
        var nested = detected.Root.Properties.Single(p => p.Name == "Outer").Value.Properties.Single().Value;
        Assert.IsType<Expr.Param>(nested.Opens[0]);
        Assert.Same(nested.Opens[0], nested.Opens[1]);
        var staticFamily = detected.Root.Properties.Single(p => p.Name == "StaticFamily").Value;
        Assert.IsType<Expr.Resolve>(staticFamily.Opens[0]);
        Assert.Same(head, family.Opens[0]);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task SuspendingModuleLoad_GatesEvaluation_AfterEagerOrDeferredElaboration(bool deferred, bool fetchFails)
    {
        var download = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var downloads = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) => { downloads++; return new ValueTask<string>(download.Task); },
            HostOperations = HostOperations.Create(HostOperation.Create("Touch", (_, _) =>
            {
                calls++;
                return new Result.Atom(1);
            })),
        };
        var source = deferred
            ? "Lib = { public X = 7 }\nF(0) = 0\nF(Lib) = {\nopen 'https://katlang.org/review.kat', Lib\nTouch()\n}\nF(3)"
            : "M = load('https://katlang.org/review.kat')\nF(M) = {\nopen M.Sub.Leaf\n1\n}\nTouch()";
        if (deferred)
        {
            Assert.Empty((await Parser.ParseAsync(source, options)).Diagnostics);
            Assert.Equal("0", Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(
                source.Replace("F(3)", "F(0)", StringComparison.Ordinal), options)).ToDisplayString());
            Assert.Equal(0, downloads);
        }
        var pending = KatLangEngine.RunAsync(source, options);
        Assert.False(pending.IsCompleted);
        Assert.Equal(1, downloads);
        Assert.Equal(0, calls);
        if (fetchFails)
            download.SetException(new IOException("review fetch failure"));
        else
            download.SetResult("public Sub = { public Leaf = { public X = 7 } }");
        var result = await pending.WaitAsync(TimeSpan.FromSeconds(10));
        var errors = deferred
            ? Assert.IsType<RunResult.EvalFailure>(result).Errors
            : Assert.IsType<RunResult.ParseFailure>(result).Errors;
        Assert.Contains(errors, e => e.Code == (deferred && fetchFails
            ? KatLangErrorCode.LoadFetchFailed : KatLangErrorCode.OpenTargetIsParameter));
        Assert.Equal(0, calls);
        Assert.Equal(1, downloads);
    }

    [Theory]
    [InlineData("Lib", true)]
    [InlineData("q", false)]
    public async Task DeferredBranch_InheritsCompletedOwnerBindings(string liftedName, bool rejected)
    {
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult("public Loaded = 1"),
            HostOperations = HostOperations.Create(HostOperation.Create("Touch", (_, _) =>
            {
                calls++;
                return new Result.Atom(1);
            })),
        };
        var source = "Lib = { public X = 7 }\nNeed(" + liftedName + ") = 0\nOuter = {\nF(0) = 0\nF(n) = {\nopen 'https://katlang.org/review.kat', Lib\nTouch() + X\n}\nF(1) + Need\n}\nOuter(3)";
        Assert.Empty((await Parser.ParseAsync(source, options)).Diagnostics);
        var result = await KatLangEngine.RunAsync(source, options);
        if (rejected)
        {
            var errors = Assert.IsType<RunResult.EvalFailure>(result).Errors;
            Assert.Equal(KatLangErrorCode.OpenTargetIsParameter, errors[0].Code);
            Assert.Single(errors, e => e.Code == KatLangErrorCode.OpenTargetIsParameter);
            Assert.Equal(0, calls);
        }
        else
        {
            Assert.Equal("8", Assert.IsType<RunResult.Success>(result).ToDisplayString());
            Assert.Equal(1, calls);
        }
    }

    [Theory]
    [InlineData("(Lib)")]
    // The comma closes the spread before the next output row (SYN-07B).
    [InlineData("Lib*, { public P = 7 }")]
    [InlineData("Lib()")]
    public void AlreadyRejectedOpenForms_DoNotAcquireOwnershipCascades(string target)
    {
        var parsed = Parser.Parse("Lib = { public X = 7 }\nF(Lib) = {\nopen " + target + "\n1\n}\nF(3)");
        Assert.Equal(DiagnosticCode.BadOpenForm, Assert.Single(parsed.Diagnostics).Code);
    }

    [Fact]
    public async Task LoadedBody_UsesItsOwnParameterBinding_AndSuppressesForeignEditorSites()
    {
        var options = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult("F(Lib) = {\n    open Lib\n    1\n}"),
        };
        const string source = "Lib = { public X = 7 }\nM = load('https://katlang.org/review.kat')\n1";
        var parsed = await Parser.ParseAsync(source, options);
        Assert.Equal(DiagnosticCode.OpenTargetIsParameter, Assert.Single(parsed.Diagnostics).Code);
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Null(model.FindResolutionAt(2, 10));
        Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options));
    }
}
