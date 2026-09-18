using System.Reflection;
using System.Runtime.CompilerServices;

namespace KatLang.Tests;

/// <summary>
/// Invalid-state representation §3.4 — how an inferred parameter's diagnostic
/// provenance is ATTACHED to the records that stand for it.
///
/// <para>ONE <see cref="ImplicitParameterProvenance"/> note is ONE promotion
/// event (an unresolved name first promoted in one body, in one front-end
/// context). Every record view of that promotion — the inferred capture, the
/// declarations flattened from it, every caller signature the capture is lifted
/// into, the dot edge whose fallback occurrence caused the promotion, and the
/// error snapshots the evaluator takes — references the SAME note object through
/// an equality-transparent slot, so a <c>with</c> copy is one more view with no
/// registration or hand-written copy constructor, while record equality,
/// hashing, and printing never see the note. The post-exposure finalizer mutates
/// the note in place exactly because it is shared: its verdict must reach every
/// lifted caller without rewriting an executable node. Nothing forks a note; a
/// body elaborated again in another context is a new promotion with a new note.</para>
///
/// <para>These tests pin that model directly: automatic propagation through
/// every carrier's <c>with</c>, the shared update reaching lifted callers and
/// the errors built from them, independence of separate promotions, identity
/// transparency, module positioning, lifetime, and the absence of any table.</para>
/// </summary>
public class ImplicitParameterProvenanceAttachmentTests
{
    /// <summary>The root demands <c>Use</c> as a value: an arity mismatch carrying Use's note.</summary>
    private const string LibraryTypo = "Lib = { public Double(x) = x * 2 }\nUse = Lib.Dubel(4)\nUse";

    /// <summary>The root lifts <c>Dubel</c> from <c>Use</c>: an unresolved-parameter report at the root.</summary>
    private const string LibraryTypoLifted = "Lib = { public Double(x) = x * 2 }\nUse = Lib.Dubel(4)\nUse + 1";

    private static Algorithm PropertyValue(Algorithm owner, string name)
        => Assert.Single(owner.Properties, property => property.Name == name).Value;

    private static ParameterDeclaration Parameter(Algorithm owner, string name)
        => Assert.Single(owner.Parameters, parameter => parameter.Name == name);

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    private static EvalError Fail(Algorithm root)
    {
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.True(result.IsError, "expected an evaluation failure");
        return result.Error;
    }

    private static IReadOnlyList<ImplicitParameterProvenance> Notes(EvalError error)
    {
        var notes = Innermost(error) switch
        {
            EvalError.UnresolvedImplicitParams unresolved => unresolved.InferredImplicitParameters,
            EvalError.ArityMismatch arity => arity.InferredImplicitParameters,
            var other => throw new Xunit.Sdk.XunitException($"expected an arity/unresolved error, got {other.GetType().Name}"),
        };
        Assert.NotNull(notes);
        return notes;
    }

    /// <summary>Every dot edge in the tree that carries a promotion note, modules included.</summary>
    private sealed class NotedEdgeCollector : AstWalker
    {
        public List<Expr.DotCall> Edges { get; } = [];

        protected override bool VisitsExplicitParameterDeclarations => false;

        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.DotCall { InferredFallbackProvenance: not null } edge)
                Edges.Add(edge);
            base.VisitExpr(expr);
        }
    }

    private static Expr.DotCall SingleNotedEdge(Algorithm root)
    {
        var collector = new NotedEdgeCollector();
        collector.VisitAlgorithm(root);
        return Assert.Single(collector.Edges);
    }

    // ── A. One promotion, one note, every carrier a view of it ──────────────

    [Fact]
    public void EveryCarrier_ReferencesTheOneNoteOfThePromotion_AndEveryWithCopyKeepsIt()
    {
        var root = SourceProvenance.ParseValid(LibraryTypo).Root;
        var use = PropertyValue(root, "Use");
        var pattern = Assert.IsType<CaptureParameterPattern>(Assert.Single(use.ParameterPatterns));
        var declaration = Assert.Single(use.Parameters);
        var edge = Assert.IsType<Expr.DotCall>(Assert.Single(use.Output));
        var note = pattern.InferredProvenance;
        Assert.NotNull(note);
        Assert.Equal("Dubel", note.Name);
        Assert.Equal(new SourceSpan(2, 11, 2, 16), note.Span);
        Assert.Equal("Lib", note.DotMemberOrigin?.ReceiverDescription);

        // The declaration flattened from the capture and the edge that caused the
        // promotion are views of the same note, not copies of its content.
        Assert.Same(note, declaration.InferredProvenance);
        Assert.Same(note, edge.InferredFallbackProvenance);
        Assert.Same(note, declaration.ToPattern().InferredProvenance);
        Assert.Same(note, Assert.Single(pattern.Captures).InferredProvenance);

        // Ordinary `with` on every carrier keeps the reference, whatever else changes.
        Assert.Same(note, (pattern with { Parameter = pattern.Parameter with { Span = null } }).InferredProvenance);
        Assert.Same(note, (declaration with { Kind = ParameterKind.Collecting }).InferredProvenance);
        Assert.Same(note, (edge with { Args = OutputBundle.Empty, MemberSpan = null }).InferredFallbackProvenance);

        // The error built from the callee snapshots the very same note object, and the
        // span-attaching copy on the way out keeps the snapshot.
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(Fail(root)));
        Assert.Same(note, Assert.Single(arity.InferredImplicitParameters!));
        Assert.Same(arity.InferredImplicitParameters, (arity with { Span = new SourceSpan(9, 9, 9, 10) }).InferredImplicitParameters);
    }

    [Fact]
    public void ALiftedCaller_IsAViewOfTheCalleesNote_AndItsReportSnapshotsIt()
    {
        var root = SourceProvenance.ParseValid(LibraryTypoLifted).Root;
        var note = Parameter(PropertyValue(root, "Use"), "Dubel").InferredProvenance;
        Assert.NotNull(note);

        // The resolver lifts the capture OBJECT into the root's signature, so the
        // root's declaration is one more view of Use's promotion.
        Assert.Same(note, Parameter(root, "Dubel").InferredProvenance);

        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(Fail(root)));
        Assert.Same(note, Assert.Single(unresolved.InferredImplicitParameters!));
        Assert.Same(unresolved.InferredImplicitParameters, (unresolved with { Span = null }).InferredImplicitParameters);
    }

    [Theory]
    [InlineData(typeof(ParameterDeclaration))]
    [InlineData(typeof(CaptureParameterPattern))]
    [InlineData(typeof(Expr.DotCall))]
    [InlineData(typeof(EvalError.ArityMismatch))]
    [InlineData(typeof(EvalError.UnresolvedImplicitParams))]
    public void NoteCarriers_UseTheCompilerGeneratedCopyConstructor(Type carrier)
    {
        // The slot is an ordinary field, so the synthesized copy constructor copies it
        // with everything else; a hand-written one would be a place to forget a field.
        var copyConstructor = carrier.GetConstructor(
            BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
            [carrier]);
        Assert.NotNull(copyConstructor);
        Assert.True(
            copyConstructor.IsDefined(typeof(CompilerGeneratedAttribute), inherit: false),
            $"{carrier.Name} declares a hand-written copy constructor; the provenance slot needs none.");
    }

    // ── B. The shared update reaches every view, lifted callers included ─────

    [Fact]
    public void OwnershipCompletionForget_ReachesTheLiftedCallersAndTheirErrors()
    {
        // `Lib.Dubel(4)` is promoted inside Inner with the receiver known through the
        // open; ownership completion then binds Inner's `Lib` to Outer's captured
        // parameter, and the finalizer forgets the receiver claim on the ONE note that
        // Inner, Outer (which lifted Dubel), and the root (which lifted it again) share.
        const string source = "Providers = { public Lib = { public Double(x) = x * 2 } }\n"
            + "Outer = { Inner = { open Providers\nLib.Dubel(4) }\nNeed = Lib\nInner + Need }\nOuter + 1";
        var root = SourceProvenance.ParseValid(source).Root;
        var outer = PropertyValue(root, "Outer");
        var inner = PropertyValue(outer, "Inner");
        var edge = Assert.IsType<Expr.DotCall>(Assert.Single(inner.Output));
        Assert.IsType<Expr.Param>(edge.Target);

        var note = Parameter(inner, "Dubel").InferredProvenance;
        Assert.NotNull(note);
        Assert.Same(note, edge.InferredFallbackProvenance);
        Assert.Same(note, Parameter(outer, "Dubel").InferredProvenance);
        Assert.Same(note, Parameter(root, "Dubel").InferredProvenance);
        Assert.Null(note.DotMemberOrigin);
        Assert.Null(note.SuggestedName);

        // The root's own report — built from the ROOT's declarations, two lifts away
        // from the edge — observes the forgotten claim.
        var error = Fail(root);
        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(error));
        Assert.Contains("Dubel", unresolved.ParamNames);
        Assert.Contains(Notes(error), reported => ReferenceEquals(reported, note));
        Assert.All(Notes(error), reported => Assert.Null(reported.DotMemberOrigin));
        Assert.DoesNotContain("was not found on", KatLangError.FromEvalError(error).Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task ModuleOriginPositioning_HasNoModuleSpanOnTheSharedNote_SoTheLocalDemandKeepsItsSpan()
    {
        // The edge lies inside the imported module, which is its locationless import view:
        // the promotion's shared note records NO occurrence span (never the module-relative
        // 1:19-1:25 of the member token), so the importing document's report — built from
        // the module property's declarations at the local demand — keeps the demand span,
        // while the receiver-aware wording and suggestion survive on the same object and no
        // module coordinate is rendered into the message.
        var parsed = await SourceProvenance.ParseValidAsync(
            "open 'https://katlang.org/g24.kat'\nUse + 1",
            new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("public Use = Math.Ceiling(2.1)") });
        var edge = SingleNotedEdge(parsed.Root);
        var note = edge.InferredFallbackProvenance!;
        Assert.Null(note.Span);
        Assert.Null(edge.MemberSpan);
        Assert.Equal("Math", note.DotMemberOrigin?.ReceiverDescription);
        Assert.Equal("Math.Ceil", note.SuggestedName);

        var error = Fail(parsed.Root);
        Assert.Same(note, Assert.Single(Notes(error)));
        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        Assert.Equal(2, error.Span?.Start.Line);
        Assert.Equal(1, error.Span?.Start.Column);
        var message = KatLangError.FromEvalError(error).Message;
        Assert.Contains("Did you mean 'Math.Ceil'?", message, StringComparison.Ordinal);
        Assert.DoesNotContain("[1:19]", message, StringComparison.Ordinal);
        Assert.Contains("was inferred from an unresolved name", message, StringComparison.Ordinal);
    }

    // ── C. Separate promotions never share a note ───────────────────────────

    [Fact]
    public void TheSameNamePromotedInTwoBodies_HasTwoIndependentNotes()
    {
        var root = SourceProvenance.ParseValid(
            "Lib = { public Double(x) = x * 2 }\nA = Lib.Dubel(1)\nB = Lib.Dubel(2)\nA + B").Root;
        var noteA = Parameter(PropertyValue(root, "A"), "Dubel").InferredProvenance!;
        var noteB = Parameter(PropertyValue(root, "B"), "Dubel").InferredProvenance!;
        Assert.NotSame(noteA, noteB);
        Assert.Equal(new SourceSpan(2, 9, 2, 14), noteA.Span);
        Assert.Equal(new SourceSpan(3, 9, 3, 14), noteB.Span);

        // The root lifts Dubel once, from the first dependency: its declaration is a
        // view of A's promotion and of nothing else.
        Assert.Same(noteA, Parameter(root, "Dubel").InferredProvenance);

        // A verdict on one promotion is invisible to the other.
        noteA.ForgetDotMemberOrigin();
        Assert.Null(noteA.DotMemberOrigin);
        Assert.Equal("Lib", noteB.DotMemberOrigin?.ReceiverDescription);
        Assert.Equal("Lib.Double", noteB.SuggestedName);
    }

    [Fact]
    public void TwoParsesOfOneSource_MintTheirOwnNotes()
    {
        var first = Parameter(PropertyValue(SourceProvenance.ParseValid(LibraryTypo).Root, "Use"), "Dubel").InferredProvenance;
        var second = Parameter(PropertyValue(SourceProvenance.ParseValid(LibraryTypo).Root, "Use"), "Dubel").InferredProvenance;
        Assert.NotNull(first);
        Assert.NotNull(second);
        Assert.NotSame(first, second);
        Assert.Equal(first.Span, second.Span);
        Assert.Equal(first.SuggestedName, second.SuggestedName);
    }

    [Fact]
    public void OneSharedRawBody_GetsOneNotePerFrontEndContext()
    {
        // A host DAG: the same raw property-value algorithm under two owners. Each
        // owner is its own front-end context and elaborates the body separately, so
        // each output view is a separate promotion with a separate note — while the
        // two references under ONE owner share one elaboration and one note.
        var syntax = SourceProvenance.ParseSyntaxValidRoot(LibraryTypo);
        var shared = PropertyValue(syntax, "Use");
        var lib = Assert.Single(syntax.Properties, property => property.Name == "Lib");
        var nested = new Algorithm.User(null, [], [], [new Property("Q", shared)], [new Expr.Resolve("Q")]);
        var host = new Algorithm.User(
            null,
            [],
            [],
            [lib, new Property("P", shared), new Property("P2", shared), new Property("Outer", nested)],
            [new Expr.Resolve("P")]);

        var (detected, diagnostics) = ParameterDetector.Detect(host);
        Assert.Empty(diagnostics);
        var noteP = Parameter(PropertyValue(detected, "P"), "Dubel").InferredProvenance;
        var noteP2 = Parameter(PropertyValue(detected, "P2"), "Dubel").InferredProvenance;
        var noteQ = Parameter(PropertyValue(PropertyValue(detected, "Outer"), "Q"), "Dubel").InferredProvenance;
        Assert.NotNull(noteP);
        Assert.NotNull(noteQ);
        Assert.Same(noteP, noteP2);
        Assert.NotSame(noteP, noteQ);
        Assert.Same(PropertyValue(detected, "P"), PropertyValue(detected, "P2"));
        Assert.NotSame(PropertyValue(detected, "P"), PropertyValue(PropertyValue(detected, "Outer"), "Q"));

        // The raw input carries nothing: elaboration stamps its OUTPUT views only.
        Assert.Null(Assert.IsType<Expr.DotCall>(Assert.Single(shared.Output)).InferredFallbackProvenance);
        Assert.Empty(shared.Parameters);
    }

    // ── D. The slot is invisible to structural identity ─────────────────────

    [Fact]
    public void Notes_AreTransparentToEqualityHashingAndPrinting_OnEveryCarrier()
    {
        var root = SourceProvenance.ParseValid(LibraryTypo).Root;
        var use = PropertyValue(root, "Use");
        var pattern = Assert.IsType<CaptureParameterPattern>(Assert.Single(use.ParameterPatterns));
        var declaration = Assert.Single(use.Parameters);
        var edge = Assert.IsType<Expr.DotCall>(Assert.Single(use.Output));
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(Fail(root)));
        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(
            Innermost(Fail(SourceProvenance.ParseValid(LibraryTypoLifted).Root)));

        AssertTransparent(pattern, new CaptureParameterPattern("Dubel"), pattern.InferredProvenance);
        AssertTransparent(declaration, new ParameterDeclaration("Dubel"), declaration.InferredProvenance);
        AssertTransparent(edge, edge with { InferredFallbackProvenance = null }, edge.InferredFallbackProvenance);
        AssertTransparent(
            arity,
            new EvalError.ArityMismatch(1, 0) { Span = arity.Span, Signature = arity.Signature },
            arity.InferredImplicitParameters);
        AssertTransparent(
            unresolved,
            new EvalError.UnresolvedImplicitParams(unresolved.ParamNames) { Span = unresolved.Span },
            unresolved.InferredImplicitParameters);

        static void AssertTransparent<T>(T carrying, T bare, object? carried) where T : class
        {
            Assert.NotNull(carried);
            Assert.Equal(bare, carrying);
            Assert.Equal(carrying, bare);
            Assert.Equal(bare.GetHashCode(), carrying.GetHashCode());
            Assert.Equal(bare.ToString(), carrying.ToString());
            Assert.DoesNotContain("Provenance", carrying.ToString(), StringComparison.Ordinal);
            Assert.DoesNotContain("InferredImplicitParameters", carrying.ToString(), StringComparison.Ordinal);
            Assert.Single(new HashSet<T> { bare, carrying });
        }
    }

    [Fact]
    public void NoteCarriers_ExposeNothingPublic_AndTheAssemblyKeepsNoProvenanceTable()
    {
        var assembly = typeof(ParameterDeclaration).Assembly;
        Assert.Null(assembly.GetType("KatLang.DiagnosticRecordMetadata`1", throwOnError: false));
        Assert.False(assembly.GetType("KatLang.RuntimeStateSlot`1", throwOnError: true)!.IsPublic);
        Assert.DoesNotContain(
            typeof(Expr.DotCall).GetProperties(BindingFlags.Instance | BindingFlags.Public),
            property => property.Name == "InferredFallbackProvenance");

        // The only weak table left in the assembly belongs to the dependency graph's
        // owner keys (its own audit item); no provenance is attached by reference anywhere.
        var weakTables = assembly.GetTypes()
            .SelectMany(type => type.GetFields(BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic))
            .Where(field => field.FieldType.IsGenericType
                && field.FieldType.GetGenericTypeDefinition() == typeof(ConditionalWeakTable<,>))
            .Select(field => $"{field.DeclaringType!.Name}.{field.Name}")
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();
        Assert.Equal(["OwnerQualifiedParameter.Identities"], weakTables);
    }

    // ── E. Lifetime: the tree owns its notes and nothing else roots them ─────

    [Fact]
    public void DroppedTree_AndItsNotes_AreCollectible()
    {
        var references = ParseAndForget();
        for (var attempt = 0; attempt < 5 && references.Any(reference => reference.Reference.IsAlive); attempt++)
        {
            GC.Collect();
            GC.WaitForPendingFinalizers();
            GC.Collect();
        }

        foreach (var (kind, reference) in references)
            Assert.False(reference.IsAlive, $"the {kind} stayed reachable after the tree was dropped");
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static List<(string Kind, WeakReference Reference)> ParseAndForget()
    {
        var root = SourceProvenance.ParseValid(LibraryTypo).Root;
        var use = PropertyValue(root, "Use");
        var edge = Assert.IsType<Expr.DotCall>(Assert.Single(use.Output));
        var error = Fail(root);
        var note = Assert.Single(Notes(error));
        Assert.Same(note, edge.InferredFallbackProvenance);
        return
        [
            ("root", new WeakReference(root)),
            ("edge", new WeakReference(edge)),
            ("note", new WeakReference(note)),
            ("error", new WeakReference(error)),
        ];
    }
}
