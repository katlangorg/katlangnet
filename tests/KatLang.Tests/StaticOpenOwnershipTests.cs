using KatLang.Semantics;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// Static-open ownership (SYN-03 / F2). <c>open</c> is resolved statically — there is no
/// dynamic <c>open</c> — but lexical ownership still applies to the target's HEAD name: when
/// the nearest established binding of <c>Lib</c> in <c>open Lib</c> / <c>open Lib.Sub</c> is a
/// parameter, that parameter owns the name, a parameter cannot be opened, and the front end
/// reports <see cref="DiagnosticCode.OpenTargetIsParameter"/> instead of searching farther
/// outward for a same-named property. The head elaborates to <see cref="Expr.Param"/> — not an
/// open form in either engine — so no evaluation of the elaborated tree can bypass the
/// parameter either.
///
/// <para>The regression law behind the fix: adding or removing a farther declaration of the
/// same name must not alter the ownership of a nearer parameter
/// (<see cref="FartherDeclaration_DoesNotChangeTheVerdictTheDiagnosticOrTheElaboration"/>).
/// Before the fix, <c>F(Lib) = { open Lib  X, Lib.X }</c> called with <c>Other</c> produced
/// <c>(7, 8)</c>: the open opened the farther root <c>Lib</c> while <c>Lib.X</c> read the
/// parameter.</para>
/// </summary>
public class StaticOpenOwnershipTests
{
    private const string LibSeven = "Lib = {\n    public X = 7\n}\n";
    private const string OtherEight = "Other = {\n    public X = 8\n}\n";

    // ── the rejection matrix ──────────────────────────────────────────────────

    /// <summary>
    /// Columns: label, source, head name, head line/column (the reported span), the owning
    /// parameter's declaration line/column (0 for an inferred parameter, which has no
    /// declaration site), and the editor classification of the head.
    /// </summary>
    public static TheoryData<string, string, string, int, int, int, int, IdentifierClassification> ParameterOwnedOpenHeads => new()
    {
        // A. a direct explicit parameter beside a farther root declaration of the same name
        { "explicit", LibSeven + OtherEight + "F(Lib) = {\n    open Lib\n    X, Lib.X\n}\nF(Other)", "Lib", 8, 10, 7, 3, IdentifierClassification.ExplicitParameterReference },
        // B. the same program without any farther declaration
        { "explicit-without-farther-declaration", OtherEight + "F(Lib) = {\n    open Lib\n    X\n}\nF(Other)", "Lib", 5, 10, 4, 3, IdentifierClassification.ExplicitParameterReference },
        // E. an enclosing owner's parameter, referenced from a nested body
        { "enclosing", LibSeven + "Outer(Lib) = {\n    Inner = {\n        open Lib\n        X\n    }\n    Inner\n}\nOuter(3)", "Lib", 6, 14, 4, 7, IdentifierClassification.ExplicitParameterReference },
        // with several enclosing parameters of one name, the NEAREST owns the head
        { "nearest-enclosing", LibSeven + "Outer(Lib) = {\n    Mid(Lib) = {\n        open Lib\n        X\n    }\n    Mid(2)\n}\nOuter(3)", "Lib", 6, 14, 5, 9, IdentifierClassification.ExplicitParameterReference },
        // F. a qualified target whose first segment is parameter-owned
        { "qualified", "Root = {\n    public Sub = {\n        public X = 7\n    }\n}\nF(Root) = {\n    open Root.Sub\n    X\n}\nF(Root)", "Root", 7, 10, 6, 3, IdentifierClassification.ExplicitParameterReference },
        // H. parameter varieties: collecting, grouped, clause binder, inferred, lifted
        { "collecting", LibSeven + "F(*Lib) = {\n    open Lib\n    X\n}\nF(1, 2)", "Lib", 5, 10, 4, 4, IdentifierClassification.ExplicitParameterReference },
        { "grouped", LibSeven + "F((Lib, w)) = {\n    open Lib\n    X\n}\nF((1, 2))", "Lib", 5, 10, 4, 4, IdentifierClassification.ExplicitParameterReference },
        { "branch-binder", LibSeven + "F(0) = 0\nF(Lib) = {\n    open Lib\n    X\n}\nF(5)", "Lib", 6, 10, 5, 3, IdentifierClassification.ConditionalBinderReference },
        { "inferred", "F = {\n    open Lib\n    Lib.X\n}\nF(3)", "Lib", 2, 10, 0, 0, IdentifierClassification.ImplicitParameterReference },
        { "lifted", "G = Lib.X\nF = {\n    open Lib\n    G\n}\nF(3)", "Lib", 3, 10, 0, 0, IdentifierClassification.ImplicitParameterReference },
        // G. farther same-named declarations of other kinds: an OPENED member, an ENCLOSING property
        { "opened-farther-declaration", "Libs = {\n    public Lib = {\n        public X = 7\n    }\n}\nF(Lib) = {\n    open Libs, Lib\n    X\n}\nF(3)", "Lib", 7, 16, 6, 3, IdentifierClassification.ExplicitParameterReference },
        { "enclosing-farther-property", "Outer = {\n    Lib = {\n        public X = 7\n    }\n    F(Lib) = {\n        open Lib\n        X\n    }\n    F(3)\n}\nOuter", "Lib", 6, 14, 5, 7, IdentifierClassification.ExplicitParameterReference },
    };

    [Theory]
    [MemberData(nameof(ParameterOwnedOpenHeads))]
    public async Task ParameterOwnedOpenHead_IsRejectedStaticallyAtTheHead_AndNeverBypassed(
        string label,
        string source,
        string head,
        int line,
        int column,
        int declarationLine,
        int declarationColumn,
        IdentifierClassification classification)
    {
        _ = label;
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostics = parsed.Diagnostics;

        // K. exactly one dedicated diagnostic, reported FIRST, at the head's own span, stating both facts.
        var rejection = Assert.Single(diagnostics, d => d.Code == DiagnosticCode.OpenTargetIsParameter);
        Assert.Same(rejection, diagnostics[0]);
        Assert.Equal(DiagnosticSeverity.Error, rejection.Severity);
        Assert.Equal(new SourceSpan(line, column, line, column + head.Length - 1), rejection.Span);
        Assert.Contains($"'{head}' refers to a parameter", rejection.Message);
        Assert.Contains("a parameter cannot be used as an open target", rejection.Message);
        Assert.DoesNotContain("lookup", rejection.Message, StringComparison.OrdinalIgnoreCase);

        // No misleading secondary verdict: nothing collides, nothing resolves to the farther
        // declaration, and the only other report possible is the closed-list consequence of a
        // target that provides nothing (the same recovery rule as a rejected capture target).
        Assert.All(diagnostics, d => Assert.Contains(
            d.Code, new[] { DiagnosticCode.OpenTargetIsParameter, DiagnosticCode.UndeclaredIdentifier }));

        // The elaborated head IS the parameter binding — Expr.Param at the reported span — and
        // it is the only rewritten head in the whole program.
        var heads = OpenLists(parsed.Root).SelectMany(entry => entry.Opens).Select(OpenHead).ToList();
        var parameterHead = Assert.IsType<Expr.Param>(Assert.Single(heads, h => h is Expr.Param));
        Assert.Equal(head, parameterHead.Name);
        Assert.Equal(rejection.Span, parameterHead.Span);

        // K. the front-end gate stops evaluation in both engines, and no evaluation-phase code
        // (unknown name/property, bad open form, arity, unresolved implicit parameters) leaks.
        foreach (var result in new[] { KatLangEngine.Run(source), await KatLangEngine.RunAsync(source) })
        {
            var failure = Assert.IsType<RunResult.ParseFailure>(result);
            Assert.Equal(KatLangErrorCode.OpenTargetIsParameter, failure.Errors[0].Code);
            Assert.All(failure.Errors, e => Assert.Contains(
                e.Code, new[] { KatLangErrorCode.OpenTargetIsParameter, KatLangErrorCode.UndeclaredIdentifier }));
        }

        // J. the editor agrees: the open head resolves to the PARAMETER — never to a farther
        // property — classified as the parameter reference it is, and it provides no property.
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(line, column));
        Assert.Equal(head, resolution.Occurrence.Name);
        Assert.Equal(OccurrenceKind.OpenTargetReference, resolution.Occurrence.Kind);
        Assert.Equal(classification, resolution.Classification);
        Assert.Null(resolution.ResolvedProperty);
        if (declarationLine == 0)
        {
            Assert.Null(resolution.ResolvedDeclaration);
        }
        else
        {
            var declaration = Assert.IsType<DeclarationOccurrence>(resolution.ResolvedDeclaration);
            Assert.Equal((declarationLine, declarationColumn), (declaration.Span.StartLineNumber, declaration.Span.StartColumn));
            Assert.NotEqual(OccurrenceKind.PropertyDefinition, declaration.Kind);
        }

        // Completion at the site already listed the head as that parameter; resolution now agrees.
        var visible = Assert.Single(model.GetVisibleSymbolsAt(line, column), symbol => symbol.Name == head);
        Assert.Equal(classification, visible.Classification);
        Assert.Null(visible.Property);
        Assert.Equal(resolution.ResolvedDeclaration?.Span, visible.Declaration?.Span);
    }

    // ── the law: farther declarations are irrelevant ─────────────────────────

    /// <summary>Columns: a program whose open head a parameter owns, and a farther declaration of that name to prepend.</summary>
    public static TheoryData<string, string> FartherDeclarations => new()
    {
        { OtherEight + "F(Lib) = {\n    open Lib\n    X\n}\nF(Other)", LibSeven },
        { "Outer(Lib) = {\n    Inner = {\n        open Lib\n        X\n    }\n    Inner\n}\nOuter(3)", LibSeven },
        { "F(Root) = {\n    open Root.Sub\n    X\n}\nF(3)", "Root = {\n    public Sub = {\n        public X = 7\n    }\n}\n" },
        { "F(0) = 0\nF(Lib) = {\n    open Lib\n    X\n}\nF(5)", LibSeven },
        { "F(*Lib) = {\n    open Lib\n    X\n}\nF(1, 2)", LibSeven },
        { "F((Lib, w)) = {\n    open Lib\n    X\n}\nF((1, 2))", LibSeven },
        // the farther declaration may itself be an OPENED member of the same name
        { "F(Lib) = {\n    open Libs, Lib\n    X\n}\nF(3)", "Libs = {\n    public Lib = {\n        public X = 7\n    }\n}\n" },
    };

    [Theory]
    [MemberData(nameof(FartherDeclarations))]
    public void FartherDeclaration_DoesNotChangeTheVerdictTheDiagnosticOrTheElaboration(string program, string fartherDeclaration)
    {
        var without = SourceProvenance.ParseAllowingDiagnostics(program);
        var with = SourceProvenance.ParseAllowingDiagnostics(fartherDeclaration + program);
        var shift = fartherDeclaration.Count(c => c == '\n');

        // Same diagnostics: codes, messages, and spans modulo the prepended lines; the
        // rejection first in both.
        Assert.Equal(DiagnosticCode.OpenTargetIsParameter, without.Diagnostics[0].Code);
        Assert.Equal(
            without.Diagnostics.Select(d => (d.Code, d.Message, d.Span)),
            with.Diagnostics.Select(d => (d.Code, d.Message, Shift(d.Span, -shift)!)));

        // Same elaborated open heads: the parameter head is a Param at the same (shifted) span.
        var headsWithout = OpenLists(without.Root).SelectMany(e => e.Opens).Select(OpenHead).ToList();
        var headsWith = OpenLists(with.Root).SelectMany(e => e.Opens).Select(OpenHead).ToList();
        Assert.Contains(headsWithout, h => h is Expr.Param);
        Assert.Equal(
            headsWithout.Select(h => (h.GetType(), HeadName(h), h.Span)),
            headsWith.Select(h => (h.GetType(), HeadName(h), Shift(h.Span, -shift))));

        // Same editor verdict at the head: the parameter, never the prepended declaration.
        var (line, column) = (without.Diagnostics[0].Span.StartLineNumber, without.Diagnostics[0].Span.StartColumn);
        var resolutionWithout = Assert.IsType<IdentifierResolution>(
            SemanticModelBuilder.Build(without.Parsed).FindResolutionAt(line, column));
        var resolutionWith = Assert.IsType<IdentifierResolution>(
            SemanticModelBuilder.Build(with.Parsed).FindResolutionAt(line + shift, column));
        Assert.Equal(OccurrenceKind.OpenTargetReference, resolutionWith.Occurrence.Kind);
        Assert.Equal(resolutionWithout.Classification, resolutionWith.Classification);
        Assert.Equal(resolutionWithout.ResolvedDeclaration?.Span, Shift(resolutionWith.ResolvedDeclaration?.Span, -shift));
        Assert.Null(resolutionWith.ResolvedProperty);
    }

    // ── controls: static opens are unchanged ─────────────────────────────────

    public static TheoryData<string, string> StaticOpensStillWork => new()
    {
        // C. ordinary parameter use keeps its meaning
        { OtherEight + "F(Lib) = Lib.X\nF(Other)", "8" },
        // D. a static open of a declared algorithm, from a body that binds no such name
        { LibSeven + "F = {\n    open Lib\n    X\n}\nF", "7" },
        // a static qualified target
        { "Root = {\n    public Sub = {\n        public X = 7\n    }\n}\nF = {\n    open Root.Sub\n    X\n}\nF", "7" },
        // a parameterized body may still open a declared algorithm whose name it does not bind
        { LibSeven + "F(y) = {\n    open Lib\n    X + y\n}\nF(1)", "8" },
        // an owned parameter beating an OPENED member is the other, unchanged rule
        { "Lib = {\n    public v = 99\n}\nOuter(v) = {\n    open Lib\n    v + 1\n}\nOuter(7)", "8" },
        // the head may be declared later in the same body
        { "F = {\n    open Lib\n    Lib = {\n        public X = 9\n    }\n    X\n}\nF", "9" },
        // an ancestor property head, opened from a parameterized nested body
        { "Outer = {\n    Lib = {\n        public X = 7\n    }\n    F(q) = {\n        open Lib\n        X + q\n    }\n    F(1)\n}\nOuter", "8" },
        // inline-block and builtin-namespace targets inside parameterized bodies
        { "Outer(v) = {\n    open { public v = 99 }\n    v + 1\n}\nOuter(7)", "8" },
        { "F(x) = {\n    open Math\n    Abs(x)\n}\nF(-3)", "3" },
        // a clause body may open a declared algorithm it does not bind
        { LibSeven + "F(0) = 0\nF(n) = {\n    open Lib\n    X + n\n}\nF(1)", "8" },
    };

    [Theory]
    [MemberData(nameof(StaticOpensStillWork))]
    public void StaticOpen_OfADeclaredAlgorithm_IsUnchanged(string source, string expected)
    {
        var parsed = SourceProvenance.ParseValid(source);
        Assert.DoesNotContain(OpenLists(parsed.Root).SelectMany(e => e.Opens).Select(OpenHead), h => h is Expr.Param);
        Assert.Equal(expected, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    // ── I. root phantom contrast (F1) ─────────────────────────────────────────

    /// <summary>
    /// The program root is never called, so a name the root could not resolve — or a name
    /// forwarding lifted into it — is a phantom input, not a callable parameter. It must keep
    /// its <c>UnresolvedImplicitParams</c> evaluation report and never become a "parameter that
    /// cannot be opened", whether the <c>open</c> sits in a nested body or in the root itself.
    /// </summary>
    public static TheoryData<string, string> RootPhantomOpens => new()
    {
        { "Q.X\nM = {\n    open Q\n    1\n}\nM", "Q" },
        { "open Q\nQ.X", "Q" },
        // the F1 shape itself — a nested property of the phantom's name — plus a nested open
        { "Lib = {\n    public Q = 1\n}\nQ + 1\nM = {\n    open Q\n    1\n}\nM", "Q" },
        // a name forwarding lifted into the root
        { "Need(v) = v\nM = {\n    open v\n    1\n}\nNeed + M", "v" },
    };

    [Theory]
    [MemberData(nameof(RootPhantomOpens))]
    public void RootPhantomParameter_IsNotACallableOwnerOfAnOpenHead(string source, string name)
    {
        var parsed = SourceProvenance.ParseValid(source);
        Assert.Contains(name, parsed.Root.Params);
        Assert.DoesNotContain(OpenLists(parsed.Root).SelectMany(e => e.Opens).Select(OpenHead), h => h is Expr.Param);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UnresolvedImplicitParams, error.Code);
        Assert.Contains($"'{name}'", error.Message);
    }

    // ── reporting discipline ──────────────────────────────────────────────────

    [Fact]
    public void Rejection_IsReportedExactlyOnce_WhicheverRunProducesIt()
    {
        // Discovery only (explicit list), the post-inference pass (inferred), and the
        // completion run that replaces the discovery diagnostics (lifted): one report each.
        foreach (var source in new[]
        {
            OtherEight + "F(Lib) = {\n    open Lib\n    X\n}\nF(Other)",
            "F = {\n    open Lib\n    Lib.X\n}\nF(3)",
            "G = Lib.X\nF = {\n    open Lib\n    G\n}\nF(3)",
        })
        {
            var diagnostics = SourceProvenance.ExpectFrontEndError(source);
            Assert.Equal(DiagnosticCode.OpenTargetIsParameter, diagnostics[0].Code);
            Assert.Single(diagnostics, d => d.Code == DiagnosticCode.OpenTargetIsParameter);
            Assert.Equal(diagnostics, Parser.Parse(source).Diagnostics);
        }
    }

    [Fact]
    public void QualifiedTarget_MemberSiteProvidesNothing_AndEachWrittenHeadIsReportedOnce()
    {
        const string source = "F(Root) = {\n    open Root.Sub, Root\n    1\n}\nF(3)";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.Equal(
            [(2, 10), (2, 20)],
            parsed.Diagnostics.Select(d => (d.Span.StartLineNumber, d.Span.StartColumn)));
        Assert.All(parsed.Diagnostics, d => Assert.Equal(DiagnosticCode.OpenTargetIsParameter, d.Code));
        Assert.Contains("Cannot open 'Root.Sub': its first name 'Root' refers to a parameter", parsed.Diagnostics[0].Message);
        Assert.Contains("Cannot open 'Root': 'Root' refers to a parameter", parsed.Diagnostics[1].Message);

        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var member = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(2, 15));
        Assert.Equal(OccurrenceKind.OpenTargetMemberReference, member.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Unresolved, member.Classification);
        Assert.Null(member.ResolvedDeclaration);
        Assert.Null(member.ResolvedProperty);
    }

    [Fact]
    public async Task Rejection_PreventsEvaluationInSyncAndAsyncEngines()
    {
        var calls = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Touch", (_, _) =>
            {
                calls++;
                return new Result.Atom(1);
            })),
        };
        const string source = LibSeven + "F(Lib) = {\n    open Lib\n    X\n}\nTouch()\nF({ public X = 8 })";
        foreach (var result in new[] { KatLangEngine.Run(source, options), await KatLangEngine.RunAsync(source, options) })
        {
            var failure = Assert.IsType<RunResult.ParseFailure>(result);
            Assert.Equal(KatLangErrorCode.OpenTargetIsParameter, failure.Errors[0].Code);
        }

        Assert.Equal(0, calls);
    }

    /// <summary>
    /// B2c: a branch body owning a module open is elaborated provisionally (diagnostics
    /// withheld) and for real only when the branch is selected. The rejection then surfaces
    /// through materialization, with the same code, and the farther candidate is never opened.
    /// </summary>
    [Fact]
    public async Task DeferredBranch_ReportsTheRejectionWhenTheBranchIsSelected()
    {
        var downloads = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                downloads++;
                return ValueTask.FromResult("public Loaded = 1");
            },
        };
        const string source = LibSeven + "F(0) = 0\nF(Lib) = {\n    open 'https://katlang.org/lib.kat', Lib\n    Loaded\n}\nF(5)";

        var parsed = await Parser.ParseAsync(source, options);
        Assert.Empty(parsed.Diagnostics);
        Assert.Equal(0, downloads);

        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source, options));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.OpenTargetIsParameter, error.Code);
        Assert.Contains("Cannot open 'Lib': 'Lib' refers to a parameter", error.Message);
        Assert.Equal(1, downloads);
    }

    /// <summary>
    /// G. a loaded-module alias is one more kind of farther declaration: once a nearer
    /// parameter owns the name, the alias is never the open target; without the parameter,
    /// the static alias open is unchanged.
    /// </summary>
    [Fact]
    public async Task LoadedModuleAlias_IsNeverOpenedThroughAParameterOwnedHead_AndStaysOpenableStatically()
    {
        var options = new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("public Total = 7") };

        const string rejected = "M = load('https://katlang.org/lib.kat')\nF(M) = {\n    open M\n    Total\n}\nF(3)";
        var parsed = await Parser.ParseAsync(rejected, options);
        var rejection = Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.OpenTargetIsParameter);
        Assert.Equal(new SourceSpan(3, 10, 3, 10), rejection.Span);
        Assert.All(parsed.Diagnostics, d => Assert.Contains(
            d.Code, new[] { DiagnosticCode.OpenTargetIsParameter, DiagnosticCode.UndeclaredIdentifier }));
        var failure = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(rejected, options));
        Assert.Equal(KatLangErrorCode.OpenTargetIsParameter, failure.Errors[0].Code);

        const string accepted = "M = load('https://katlang.org/lib.kat')\nF(q) = {\n    open M\n    Total + q\n}\nF(1)";
        _ = await SourceProvenance.ParseValidAsync(accepted, options);
        Assert.Equal("8", Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(accepted, options)).ToDisplayString());
    }

    // ── the evaluator half: a Param head is not an open form, in both engines ─

    /// <summary>
    /// The elaborated shape of <c>Lib = { public X = 7 }</c> / <c>Other = { public X = 8 }</c> /
    /// <c>F(Lib) = { open Lib  X }</c> / <c>F(Other)</c>, built by hand with the
    /// <see cref="Expr.Param"/> head the front end produces: neither engine opens the farther
    /// root <c>Lib</c> (7) nor the argument (8) — the head is rejected as a bad open form, so
    /// a recovery tree or a host-built AST cannot bypass the parameter either. Bare and
    /// qualified heads alike.
    /// </summary>
    [Fact]
    public async Task Evaluator_RejectsAParameterHead_EvenBesideAFartherSameNamedProperty()
    {
        static Algorithm.User Value(decimal n) => new(null, [], [], [], [new Expr.Num(n)]);
        static Algorithm.User Library(string member, Algorithm value)
            => new(null, [], [], [new Property(member, value, IsPublic: true)], []);

        var bare = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [
                new Property("Lib", Library("X", Value(7))),
                new Property("Other", Library("X", Value(8))),
                new Property("F", new Algorithm.User(
                    null, [new ParameterDeclaration("Lib")], [new Expr.Param("Lib")], [], [new Expr.Resolve("X")])),
            ],
            [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Resolve("Other")]))]));

        var qualified = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [
                new Property("Root", Library("Sub", Library("X", Value(7)))),
                new Property("F", new Algorithm.User(
                    null, [new ParameterDeclaration("Root")],
                    [new Expr.DotCall(new Expr.Param("Root"), "Sub")], [], [new Expr.Resolve("X")])),
            ],
            [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Resolve("Root")]))]));

        foreach (var program in new[] { bare, qualified })
        {
            Assert.Equal("err badOpenForm", AsyncEvaluationHarness.NeutralOf(Evaluator.RunCounted(program)));
            Assert.Equal("err badOpenForm", AsyncEvaluationHarness.NeutralOf(
                await AsyncEvaluationHarness.Complete(
                    Evaluator.RunCountedAsync(program, new PassThroughAsyncZeroArgPropertyResultCache()))));
        }
    }

    // ── helpers ───────────────────────────────────────────────────────────────

    private static Expr OpenHead(Expr open)
    {
        while (open is Expr.DotCall { Args: null } dotCall)
            open = dotCall.Target;
        return open;
    }

    private static string? HeadName(Expr head) => head switch
    {
        Expr.Resolve resolve => resolve.Name,
        Expr.Param parameter => parameter.Name,
        _ => null,
    };

    private static IEnumerable<(Algorithm Owner, IReadOnlyList<Expr> Opens)> OpenLists(Algorithm algorithm)
    {
        if (algorithm.Opens.Count > 0)
            yield return (algorithm, algorithm.Opens);

        foreach (var property in algorithm.Properties)
        {
            foreach (var entry in OpenLists(property.Value))
                yield return entry;
        }

        foreach (var branch in algorithm.Branches)
        {
            foreach (var entry in OpenLists(branch.Body))
                yield return entry;
        }
    }

    private static SourceSpan? Shift(SourceSpan? span, int lines)
        => span is null
            ? null
            : span with
            {
                StartLineNumber = span.StartLineNumber + lines,
                EndLineNumber = span.EndLineNumber + lines,
            };
}
