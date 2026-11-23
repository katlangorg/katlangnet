using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// FE-3 MEETING NAMES (finding lifting-signatures-fe3-sharing-breaks-on-meeting-names of the 2026-11-21 adversarial
/// performance audit). K owners that lift one L-wide callee share ONE signature template — unless the owner's names MEET
/// the lifted ones: an own capture of the same name (<c>A = G + v0</c> with <c>G</c> over <c>v0 … v(L-1)</c>) or an
/// enclosing parameter binding the owner's forwarding reuses (Q-04, <c>{ H = G + 1 ⏎ H + v0 }</c>). Such an owner's
/// order is its own, and until this repair each one re-ran the whole L-wide merge: its HashSet of bound names, seeded by
/// its own and reused names, and its visited-group set were per-owner state, so the K owners built K templates of L
/// patterns, K argument bundles of L slots (the shared bundle key was the owner's whole signature), and the exposure pass
/// folded the shared bundle's L names once per forwarding owner. An L = K = 1,024 program allocated 873 MB to parse and
/// handed the evaluator's preflight 2.1 million edges.
///
/// <para>Only the collisions are owner state. The signature is now the owner's own head over the shared tail WITHOUT the
/// colliding names, the exclusion keyed by (tail, collision set) and shared; the bundle key carries the one input a
/// bundle reads from its owner (the re-spread decision of each collecting callee name); and the exposure pass replaces a
/// partly owned shared seed by its residual, read once per (seed, template). These tests pin the representation, the
/// owners' identity, the exact per-owner merge order against an independent oracle, diagnostics, runtime behaviour, and
/// that every work counter is a sum of an owner term and a width term — never their product.</para>
/// </summary>
public sealed class Fe3MeetingNameSharingTests
{
    private static string Names(string prefix, int count, string separator = ", ")
        => string.Join(separator, Enumerable.Range(0, count).Select(i => $"{prefix}{i}"));

    /// <summary><c>G = v0 + … + v(L-1)</c> and K owners <c>A(i) = G + v0</c>: every owner's own <c>v0</c> meets the tail.</summary>
    private static string OwnMeeting(int owners, int width)
        => $"G = {Names("v", width, " + ")}\n" + string.Concat(Enumerable.Range(0, owners).Select(i => $"A{i} = G + v0\n")) + "1";

    /// <summary>Like <see cref="OwnMeeting"/>, owner i meeting the tail at <c>v(i mod L)</c>: distinct collisions.</summary>
    private static string DistinctMeeting(int owners, int width)
        => $"G = {Names("v", width, " + ")}\n" + string.Concat(Enumerable.Range(0, owners).Select(i => $"A{i} = G + v{i % width}\n")) + "1";

    /// <summary>K owners whose nested <c>H</c> lifts <c>G</c> while the owner's own <c>v0</c> is the binding H's forwarding reuses (Q-04).</summary>
    private static string EnclosingMeeting(int owners, int width)
        => $"G = {Names("v", width, " + ")}\n"
            + string.Concat(Enumerable.Range(0, owners).Select(i => $"A{i} = {{\n    H = G + 1\n    H + v0\n}}\n")) + "1";

    /// <summary>The control: each owner's own name <c>w(i)</c> misses the tail (FE-3's composed head).</summary>
    private static string NoMeeting(int owners, int width)
        => $"G = {Names("v", width, " + ")}\n" + string.Concat(Enumerable.Range(0, owners).Select(i => $"A{i} = G + w{i}\n")) + "1";

    // One collector per list pattern is legal. The shared callee therefore has L independent
    // re-spread decisions, including the L ordinary sources supplied by the enclosing declaration.
    private static string CollectorMeeting(int owners, int width, bool reuseEnclosing)
    {
        var groups = string.Join(", ", Enumerable.Range(0, width).Select(i => $"[*v{i}]"));
        var callee = $"G({groups}, extra) = 1\n";
        return reuseEnclosing
            ? callee + $"P({Names("v", width)}) = {{\n"
                + string.Concat(Enumerable.Range(0, owners).Select(i => $"H{i} = G + 1\n")) + "1\n}\n1"
            : callee + string.Concat(Enumerable.Range(0, owners).Select(i => $"A{i} = G + v0\n")) + "1";
    }

    private static Algorithm.User Owner(Algorithm root, string name)
        => Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, p => p.Name == name).Value);

    private static IEnumerable<Expr.Call> CallsTo(Algorithm algorithm, string callee)
    {
        var pending = new Stack<object>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        pending.Push(algorithm);
        while (pending.TryPop(out var node))
        {
            if (!seen.Add(node))
                continue;
            switch (node)
            {
                case Algorithm.User user:
                    foreach (var property in user.Properties) pending.Push(property.Value);
                    foreach (var row in user.Output) pending.Push(row);
                    break;
                case Expr.Call call:
                    if (call.Function is Expr.Resolve(var name) && name == callee)
                        yield return call;
                    pending.Push(call.Function);
                    foreach (var argument in call.Args) pending.Push(argument);
                    break;
                case Expr.Binary binary:
                    pending.Push(binary.Left);
                    pending.Push(binary.Right);
                    break;
                case Expr.AlgorithmExpr block:
                    pending.Push(block.Algorithm);
                    break;
            }
        }
    }

    /// <summary>A parameter list's structure: names, collecting marks and group kinds — the content the merge decides.</summary>
    private static string Shape(IEnumerable<ParameterPattern> patterns) => string.Join(", ", patterns.Select(Shape));

    private static string Shape(ParameterPattern pattern) => pattern switch
    {
        CaptureParameterPattern { Kind: ParameterKind.Collecting } collecting => "*" + collecting.Name,
        CaptureParameterPattern { Kind: ParameterKind.Meta } meta => "meta " + meta.Name,
        CaptureParameterPattern capture => capture.Name,
        SequenceValueParameterPattern sequence => "(" + Shape(sequence.Items) + ")",
        ListValueParameterPattern list => "[" + Shape(list.Items) + "]",
        UnpackingParameterPattern unpacking => "unpack[" + Shape(unpacking.Items) + "]",
    };

    // ── Passes, observed one by one ──────────────────────────────────────────────────────────────

    private sealed record Observed(
        Algorithm Resolved,
        FrontEndTraversalObservations Resolve,
        FrontEndTraversalObservations Exposure,
        FrontEndTraversalObservations Preflight,
        FrontEndTraversalObservations Admission);

    private static Observed ObservePasses(string source)
    {
        var detected = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(detected.Diagnostics);
        var observed = new Observed(null!, new(), new(), new(), new());
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observed.Resolve, diagnostics);
        Assert.Empty(diagnostics);
        var exposed = PropertyExposureResolver.Resolve(resolved, observed.Exposure);
        var program = new Expr.AlgorithmExpr(exposed);
        Assert.Null(AstStructuralPreflight.Check(
            program, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines, observed.Preflight));
        var (result, _) = Evaluator.RunCountedObserved(program,
            observations: new EvaluationObservations { PreEvaluationTraversal = observed.Admission });
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        return observed with { Resolved = resolved };
    }

    // ── Representation ───────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// Owners whose own <c>v0</c> meets the lifted tail keep their own capture first, as the per-owner merge did, but
    /// that is now a one-capture HEAD over ONE shared tail — the callee's capture records <c>v1 … v(L-1)</c> — and the
    /// K lifted calls share one argument bundle.
    /// </summary>
    [Theory]
    [InlineData(12, 40)]
    [InlineData(40, 12)]
    [InlineData(24, 24)]
    public void OwnNamesMeetingTheTail_ComposeTheirHead_OverOneExcludedTail_AndShareOneBundle(int owners, int width)
    {
        var root = SourceProvenance.ParseValid(OwnMeeting(owners, width)).Root;
        var callee = Owner(root, "G");
        var signatures = Enumerable.Range(0, owners).Select(i => Assert.IsType<ImplicitSignatureTemplate>(Owner(root, $"A{i}").ParameterPatterns)).ToList();
        var tail = Assert.IsType<ImplicitSignatureTemplate>(signatures[0].Tail);
        Assert.False(tail.IsComposed);
        Assert.Equal(width - 1, tail.Count);
        for (var j = 1; j < width; j++)
            Assert.Same(callee.ParameterPatterns[j], tail[j - 1]);

        string[] expected = [.. Enumerable.Range(0, width).Select(i => $"v{i}")];
        for (var i = 0; i < owners; i++)
        {
            var owner = Owner(root, $"A{i}");
            Assert.True(signatures[i].IsComposed);
            Assert.Same(tail, signatures[i].Tail);
            var head = Assert.IsType<CaptureParameterPattern>(Assert.Single(signatures[i].Head));
            Assert.Equal("v0", head.Name);
            // The owner's own capture, never the callee's v0.
            Assert.NotSame(callee.ParameterPatterns[0], head);
            Assert.Equal(expected, owner.Params);
            Assert.Equal(1, owner.ForwardingParameterStart);
        }

        // Every owner keeps a head record of its own: K owners are K declarations.
        Assert.Equal(owners, signatures.Select(signature => signature.Head[0]).Distinct(ReferenceEqualityComparer.Instance).Count());
        var calls = Enumerable.Range(0, owners).SelectMany(i => CallsTo(Owner(root, $"A{i}"), "G")).ToList();
        Assert.Equal(owners, calls.Count);
        Assert.All(calls, call => Assert.Same(calls[0].Args, call.Args));
        Assert.Equal(owners, calls.Select(call => call.Span).Distinct().Count());
    }

    /// <summary>
    /// Q-04: a nested owner whose enclosing binding meets the tail reuses that binding, and every such owner holds the
    /// SAME template — the tail without the reused name — however many enclosing owners there are.
    /// </summary>
    [Theory]
    [InlineData(12, 40)]
    [InlineData(40, 12)]
    public void EnclosingBindingsMeetingTheTail_ShareOneExcludedTemplate(int owners, int width)
    {
        var root = SourceProvenance.ParseValid(EnclosingMeeting(owners, width)).Root;
        var callee = Owner(root, "G");
        var nested = Enumerable.Range(0, owners).Select(i => Owner(Owner(root, $"A{i}"), "H")).ToList();
        var shared = Assert.IsType<ImplicitSignatureTemplate>(nested[0].ParameterPatterns);
        Assert.False(shared.IsComposed);
        Assert.Equal(width - 1, shared.Count);
        for (var j = 1; j < width; j++)
            Assert.Same(callee.ParameterPatterns[j], shared[j - 1]);
        Assert.All(nested, h => Assert.Same(shared, h.ParameterPatterns));
        Assert.All(nested, h => Assert.Equal(0, h.ForwardingParameterStart));

        for (var i = 0; i < owners; i++)
        {
            var owner = Assert.IsType<ImplicitSignatureTemplate>(Owner(root, $"A{i}").ParameterPatterns);
            Assert.Equal("v0", Assert.IsType<CaptureParameterPattern>(Assert.Single(owner.Head)).Name);
            Assert.Same(shared, owner.Tail);
        }
    }

    /// <summary>
    /// Real collisions are kept apart: owners meeting the tail at different names get different parts, owners meeting it
    /// at the same names share one, and the owner's own order is kept (its capture first, the lifted one filtered).
    /// </summary>
    [Fact]
    public void DistinctCollisions_KeepDistinctParts_AndEqualCollisionsShareThem()
    {
        const int width = 10;
        const int owners = 30;
        var root = SourceProvenance.ParseValid(DistinctMeeting(owners, width)).Root;
        var parts = new Dictionary<int, ImplicitSignatureTemplate>();
        for (var i = 0; i < owners; i++)
        {
            var owner = Owner(root, $"A{i}");
            var signature = Assert.IsType<ImplicitSignatureTemplate>(owner.ParameterPatterns);
            var meeting = i % width;
            Assert.Equal([$"v{meeting}", .. Enumerable.Range(0, width).Where(j => j != meeting).Select(j => $"v{j}")], owner.Params);
            var tail = Assert.IsType<ImplicitSignatureTemplate>(signature.Tail);
            if (parts.TryGetValue(meeting, out var earlier))
                Assert.Same(earlier, tail);
            else
                parts.Add(meeting, tail);
        }

        Assert.Equal(width, parts.Values.Distinct(ReferenceEqualityComparer.Instance).Count());
        var observed = ObservePasses(DistinctMeeting(owners, width)).Resolve;
        Assert.Equal(owners, observed.OwnerSignatureCollisions);
        Assert.Equal(width, observed.SignatureCollisionPartsBuilt);
        Assert.Equal(width, observed.SignatureCollisionNamesExcluded);
        // All owners read from the same bundle.
        Assert.Equal(1, observed.ImplicitArgumentBundlesBuilt);
        Assert.Equal(width, observed.ImplicitArgumentSlotsBuilt);
    }

    /// <summary>
    /// Structural shapes keep, filter and collapse exactly as the owner's merge shapes them: a sequence group left with one
    /// item is that item, a list group keeps its brackets, an own collecting name keeps its own kind and the bundle then
    /// forwards it as one argument, a META capture lifts as an ordinary one, and own and reused names exclude together.
    /// </summary>
    [Theory]
    // b = 1, a = 2, c = 3, d = 4, e = 5: G((2, 1), 3, [4, 5]) + 1.
    [InlineData("G((a, b), c, [d, e]) = a + b + c + d + e\nA = G + b\nA(1, 2, 3, [4, 5])", "A", "b, a, c, [d, e]", "16")]
    // y = 1, x = 2, z = 3: G(2, [1, 3]) + 1.
    [InlineData("G(x, [y, z]) = x + y + z\nA = G + y\nA(1, 2, [3])", "A", "y, x, [z]", "7")]
    // c = 1, a = 2, b = 3, d = 4: G((2, (3, 1)), 4) + 1.
    [InlineData("G((a, (b, c)), d) = a + b + c + d\nA = G + c\nA(1, (2, 3), 4)", "A", "c, (a, b), d", "11")]
    // r = 5 (A's own, ordinary: forwarded as one argument), a = 7: G(7, 5) + 5 = 7 + 1 + 5.
    [InlineData("G(a, *r) = a + r.count\nA = G + r\nA(5, 7)", "A", "r, a", "13")]
    [InlineData("G(meta m, a) = a\nA = G + a\n0", "A", "a, m", "0")]
    // c = 1, a = 2, b = 3, d = 4: G(2, 3, 1) + G2(1, 4) + 1.
    [InlineData("G = a + b + c\nG2 = c + d\nA = G + G2 + c\nA(1, 2, 3, 4)", "A", "c, a, b, d", "12")]
    // A reuses O's a and owns b: O(1, 2, 3) = A(2, 3) + 1 = (G(1, 2, 3) + 2) + 1.
    [InlineData("G = a + b + c\nO = {\n    A = G + b\n    A + a\n}\nO(1, 2, 3)", "O.A", "b, c", "9")]
    public void StructuralShapes_FilterLikeTheOwnersMerge(string source, string owner, string shape, string display)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var path = owner.Split('.');
        Algorithm algorithm = root;
        foreach (var name in path)
            algorithm = Owner(algorithm, name);
        Assert.Equal(shape, Shape(algorithm.ParameterPatterns));
        Assert.Equal(display, KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>
    /// The written equivalents evaluate alike: meeting owners bind in their own activations, the reused enclosing binding
    /// reaches the callee, and seeded draws through the shared tail equal the written form's.
    /// </summary>
    [Theory]
    [InlineData("G = v0 + v1 + v2\nA = G + v0\nB = G * v0\nA(1, 2, 3), B(4, 5, 6)",
        "G(v0, v1, v2) = v0 + v1 + v2\nA(v0, v1, v2) = G(v0, v1, v2) + v0\nB(v0, v1, v2) = G(v0, v1, v2) * v0\nA(1, 2, 3), B(4, 5, 6)")]
    [InlineData("G = v0 + v1 + v2\nA = {\n    H = G + 1\n    H + v0\n}\nA(1, 2, 3), A(10, 20, 30)",
        "G(v0, v1, v2) = v0 + v1 + v2\nA(v0, v1, v2) = {\n    H(v1, v2) = G(v0, v1, v2) + 1\n    H(v1, v2) + v0\n}\nA(1, 2, 3), A(10, 20, 30)")]
    [InlineData("G = random(0, 100) + v0 + v1\nA = G + v0\nB = G + v0\nA(1, 2), B(1, 2), A(1, 2)",
        "G(v0, v1) = random(0, 100) + v0 + v1\nA(v0, v1) = G(v0, v1) + v0\nB(v0, v1) = G(v0, v1) + v0\nA(1, 2), B(1, 2), A(1, 2)")]
    public void MeetingOwners_EvaluateLikeTheirWrittenForm(string lifted, string written)
    {
        var options = new RunOptions { RandomSeed = 20261123 };
        var liftedResult = Assert.IsType<RunResult.Success>(KatLangEngine.Run(lifted, options));
        var writtenResult = Assert.IsType<RunResult.Success>(KatLangEngine.Run(written, options));
        Assert.Equal(writtenResult.ToDisplayString(), liftedResult.ToDisplayString());
    }

    // ── Identity and diagnostics ─────────────────────────────────────────────────────────────────

    /// <summary>
    /// The editor sees each meeting owner's own parameter first and the forwarded one from the shared tail, and each
    /// owner's written <c>v0</c> reads that owner's own implicit parameter; in the tree the two owners keep distinct head
    /// records over one shared tail.
    /// </summary>
    [Fact]
    public void TheSemanticModel_KeepsEachOwnersOwnBinding()
    {
        const string source = "G = v0 + v1\nA = G + v0\nB = G + v0\nA(1, 2) + B(3, 4)";
        var parsed = SourceProvenance.ParseValid(source).Root;
        var model = SemanticModelBuilder.Build(parsed);
        foreach (var name in new[] { "A", "B" })
        {
            var info = Assert.Single(model.PropertyInfos, p => p.Name == name);
            Assert.Equal(["v0", "v1"], info.Parameters.Select(p => p.Name));
            Assert.All(info.Parameters, parameter => Assert.Equal(PropertyParameterKind.Implicit, parameter.Kind));
        }

        // `A = G + v0` and `B = G + v0`: the written v0 (column 9) is each owner's own implicit parameter.
        foreach (var line in new[] { 2, 3 })
        {
            var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(line, 9)));
            Assert.Equal("v0", resolution.Occurrence.Name);
            Assert.Equal(IdentifierClassification.ImplicitParameterReference, resolution.Classification);
        }

        var a = Assert.IsType<ImplicitSignatureTemplate>(Owner(parsed, "A").ParameterPatterns);
        var b = Assert.IsType<ImplicitSignatureTemplate>(Owner(parsed, "B").ParameterPatterns);
        Assert.NotSame(a.Head[0], b.Head[0]);
        Assert.Same(a.Tail, b.Tail);
        // A(1, 2) + B(3, 4) = (3 + 1) + (7 + 3).
        Assert.Equal("14", KatLangEngine.Run(source).ToDisplayString());
    }

    [Fact]
    public void ReusedCollectors_ShareByRespreadDecision_AndReadTheirOwnActivation()
    {
        const string source = "G([*r], x) = count(r) + x\n"
            + "P(r) = { A = G + 0\n A(7) }\nQ(*r) = { A = G + 0\n A(7) }\n"
            + "T(r) = { A = G + 0\n A(7) }\nP([1, 2]), Q(1, 2), T(3)";
        var root = SourceProvenance.ParseValid(source).Root;
        OutputBundle Args(string owner) => Assert.Single(CallsTo(Owner(Owner(root, owner), "A"), "G")).Args;
        Assert.Same(Args("P"), Args("T"));
        Assert.NotSame(Args("P"), Args("Q"));
        Assert.Equal("8\n9\n8", KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>
    /// Diagnostics of meeting owners are the merge's: an inferred signature with two collecting parameters at one level is
    /// reported at the reference that completes it, a lifted name that meets a property collides with it — directly or
    /// through a reused enclosing binding — and a closed list cannot bare-forward a name only the owner binds.
    /// </summary>
    [Theory]
    [InlineData("C1(a, *p) = a\nC2(b, *q) = b\nK = C1 + C2 + a\nK(1, 2, 3)", DiagnosticCode.InvalidCollectingBinding, 3, 10, 3, 12)]
    [InlineData("C1(a, *p) = a\nC2(b, *q) = b\nK = C1 + C2 + z\nK(1, 2, 3, 4)", DiagnosticCode.InvalidCollectingBinding, 3, 10, 3, 12)]
    [InlineData("G = v0 + v1\nA = {\n    v1 = 5\n    G + v0\n}\nA(1)", DiagnosticCode.ParameterPropertyCollision, 3, 5, 3, 7)]
    [InlineData("G = v0 + v1\nO = {\n    v1 = 5\n    A = G + 1\n    A + v0\n}\nO(1, 2)", DiagnosticCode.ParameterPropertyCollision, 3, 5, 3, 7)]
    [InlineData("G = v0 + v1\nO(v1) = {\n    A = G + v0\n    A\n}\nO(1)", DiagnosticCode.UnforwardableParameter, 4, 5, 4, 6)]
    public void MeetingOwnerDiagnostics_AreTheMergesDiagnostics(string source, DiagnosticCode code, int line, int column, int endLine, int endColumn)
    {
        var diagnostic = Assert.Single(Parser.Parse(source).Diagnostics);
        Assert.Equal(code, diagnostic.Code);
        Assert.Equal(new SourceSpan(new SourcePosition(line, column), new SourcePosition(endLine, endColumn)), diagnostic.Span);
        if (code == DiagnosticCode.InvalidCollectingBinding)
        {
            Assert.Equal(
                "Formula lifting cannot complete this definition's signature: it would need the collecting parameters '*p' (needed by 'C1') "
                    + "and '*q' (needed by 'C2') at the same pattern level, but a signature may declare at most one collecting parameter per pattern level."
                    + "\nCall 'C2' with explicit arguments, or declare this definition's parameters explicitly.",
                diagnostic.Message.ReplaceLineEndings("\n"));
        }
    }

    // ── The per-owner merge, as an independent oracle ────────────────────────────────────────────

    /// <summary>
    /// The pre-repair per-owner merge, written out independently: the owner's own patterns, then every dependency capture
    /// whose name neither the owner nor a reused enclosing binding binds, first occurrence winning; a group keeps its kind
    /// for its new names, a sequence group left with one non-collecting item is that item, and a group with no new name
    /// contributes nothing. META captures lift as ordinary ones.
    /// </summary>
    private static string OracleSignature(
        IReadOnlyList<ParameterPattern> own, IEnumerable<IReadOnlyList<ParameterPattern>> dependencies, IEnumerable<string> reused)
    {
        var bound = new HashSet<string>(reused, StringComparer.Ordinal);
        foreach (var name in OwnNames(own))
            bound.Add(name);
        var parts = own.Select(Shape).ToList();
        foreach (var dependency in dependencies)
            foreach (var pattern in dependency)
                if (Missing(pattern, bound) is { } kept)
                    parts.Add(kept.Text);
        return string.Join(", ", parts);
    }

    private static IEnumerable<string> OwnNames(IEnumerable<ParameterPattern> patterns)
        => patterns.SelectMany(pattern => pattern switch
        {
            CaptureParameterPattern capture => [capture.Name],
            SequenceValueParameterPattern sequence => OwnNames(sequence.Items),
            ListValueParameterPattern list => OwnNames(list.Items),
            UnpackingParameterPattern unpacking => OwnNames(unpacking.Items),
        });

    private static (string Text, bool Collecting)? Missing(ParameterPattern pattern, HashSet<string> bound) => pattern switch
    {
        CaptureParameterPattern capture => bound.Add(capture.Name)
            ? (capture.Kind == ParameterKind.Collecting ? "*" + capture.Name : capture.Name, capture.Kind == ParameterKind.Collecting)
            : null,
        SequenceValueParameterPattern sequence => MissingGroup("(", ")", sequence.Items, bound, isSequence: true),
        ListValueParameterPattern list => MissingGroup("[", "]", list.Items, bound, isSequence: false),
        UnpackingParameterPattern unpacking => MissingGroup("unpack[", "]", unpacking.Items, bound, isSequence: false),
    };

    private static (string Text, bool Collecting)? MissingGroup(
        string open, string close, IReadOnlyList<ParameterPattern> items, HashSet<string> bound, bool isSequence)
    {
        var kept = new List<(string Text, bool Collecting)>();
        foreach (var item in items)
            if (Missing(item, bound) is { } one)
                kept.Add(one);
        if (kept.Count == 0)
            return null;
        if (isSequence && kept is [{ Collecting: false } only])
            return only;
        return (open + string.Join(", ", kept.Select(static k => k.Text)) + close, false);
    }

    private static readonly string[] Alphabet = ["a", "b", "c", "d", "e"];

    /// <summary>A random callee head over distinct names: captures, at most one collector per level, groups of two or more.</summary>
    private static string Head(Random random, Queue<string> names, int depth)
    {
        var count = random.Next(1, depth == 0 ? 4 : 3);
        var items = new List<string>();
        var collecting = false;
        for (var i = 0; i < count && names.Count > 0; i++)
        {
            var roll = random.Next(10);
            if (depth == 0 && roll < 3 && names.Count >= 2)
            {
                var group = Head(random, names, depth + 1);
                if (group.Contains(','))
                    items.Add(roll == 0 ? $"[{group}]" : $"({group})");
                else if (group.Length > 0)
                    items.Add(group.StartsWith('*') ? $"[{group}]" : group);
                continue;
            }

            var name = names.Dequeue();
            if (!collecting && roll == 9 && depth > 0)
            {
                collecting = true;
                items.Add("*" + name);
            }
            else
            {
                items.Add(roll == 8 && depth == 0 ? "meta " + name : name);
            }
        }

        if (depth > 0 && items.Count == 1 && names.Count > 0)
            items.Add(names.Dequeue());
        return string.Join(", ", items);
    }

    private static string Callee(Random random, string name)
    {
        var names = new Queue<string>(Alphabet.OrderBy(_ => random.Next()));
        var head = Head(random, names, depth: 0);
        return $"{name}({head}) = 0";
    }

    /// <summary>
    /// Generated owners whose own and reused names meet one or two callees' heads (and owners lifting a composed signature)
    /// take exactly the per-owner merge's signature, shape for shape: the oracle reads the owner's own patterns from the
    /// detected tree, its reused bindings from its enclosing owner, and the callees' final signatures in lift order.
    /// </summary>
    [Fact]
    public void GeneratedMeetingOwners_TakeTheMergeOraclesSignature()
    {
        var random = new Random(20261123);
        var compared = 0;
        var meeting = 0;
        var reusing = 0;
        for (var round = 0; round < 400; round++)
        {
            var callees = new List<string> { Callee(random, "G1"), Callee(random, "G2") };
            var chained = random.Next(3) == 0;
            if (chained)
                callees.Add("G3 = G1 + " + Alphabet[random.Next(Alphabet.Length)]);
            var first = chained ? "G3" : "G1";
            var lifted = random.Next(2) == 0 ? $"{first} + G2" : first;
            var own = string.Concat(Enumerable.Range(0, random.Next(1, 3)).Select(_ => " + " + (random.Next(6) == 0 ? "z" : Alphabet[random.Next(Alphabet.Length)])));
            var nested = random.Next(2) == 0;
            var enclosing = string.Concat(Enumerable.Range(0, random.Next(1, 3)).Select(_ => " + " + Alphabet[random.Next(Alphabet.Length)]));
            var owner = nested ? $"O = {{\n    A = {lifted}{own}\n    A{enclosing}\n}}" : $"A = {lifted}{own}";
            var source = string.Join("\n", callees) + "\n" + owner + "\n1";
            if (Parser.Parse(source).HasErrors)
                continue;

            var detected = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
            Assert.Empty(detected.Diagnostics);
            var detectedOwner = nested ? Owner(Owner(detected.Root, "O"), "A") : Owner(detected.Root, "A");
            IEnumerable<string> reused = nested
                ? ParameterPattern.CapturesExpandingSharedNodesOnce(Owner(detected.Root, "O").NameResolutionParameterPatterns).Select(c => c.Name)
                : [];
            var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected);
            var resolvedOwner = nested ? Owner(Owner(resolved, "O"), "A") : Owner(resolved, "A");
            IReadOnlyList<ParameterPattern>[] dependencies = lifted.Contains('+')
                ? [Owner(resolved, first).ParameterPatterns, Owner(resolved, "G2").ParameterPatterns]
                : [Owner(resolved, first).ParameterPatterns];
            var expected = OracleSignature(detectedOwner.ParameterPatterns, dependencies, reused);
            Assert.True(expected == Shape(resolvedOwner.ParameterPatterns), $"{source}\nexpected {expected}\nactual   {Shape(resolvedOwner.ParameterPatterns)}");

            compared++;
            var dependencyNames = dependencies.SelectMany(OwnNames).ToHashSet(StringComparer.Ordinal);
            if (OwnNames(detectedOwner.ParameterPatterns).Any(dependencyNames.Contains))
                meeting++;
            if (reused.Any(dependencyNames.Contains))
                reusing++;
        }

        // The generator must keep exercising both kinds of meeting and plenty of valid programs.
        Assert.InRange(compared, 200, 400);
        Assert.InRange(meeting, 50, 400);
        Assert.InRange(reusing, 25, 400);
    }

    // ── Work: an owner term plus a width term, never their product ────────────────────────────────

    /// <summary>The counters FE-3 meeting names once multiplied by owners and width, for one shape at one size.</summary>
    private static IReadOnlyDictionary<string, long> Work(Func<int, int, string> shape, int owners, int width)
    {
        var observed = ObservePasses(shape(owners, width));
        return new Dictionary<string, long>(StringComparer.Ordinal)
        {
            ["SignatureTemplateSlotsBuilt"] = observed.Resolve.SignatureTemplateSlotsBuilt,
            ["OwnerSignatureHeadSlots"] = observed.Resolve.OwnerSignatureHeadSlots,
            ["OwnerSignatureMaterializedSlots"] = observed.Resolve.OwnerSignatureMaterializedSlots,
            ["ImplicitArgumentSlotsBuilt"] = observed.Resolve.ImplicitArgumentSlotsBuilt,
            ["LiftingStorageUnitsCharged"] = observed.Resolve.LiftingStorageUnitsCharged,
            ["SummaryQualificationProbes"] = observed.Exposure.SummaryQualificationProbes,
            ["SummaryResidualNameProbes"] = observed.Exposure.SummaryResidualNameProbes,
            ["StructuralPreflightEdges"] = observed.Preflight.StructuralPreflightEdges,
            ["AdmissionPreflightEdges"] = observed.Admission.StructuralPreflightEdges,
            ["AdmissionWalkerSteps"] = observed.Admission.WalkerSteps,
            ["AdmissionMetaPlacementSlots"] = observed.Admission.PreEvaluationMetaPlacementSlots,
        };
    }

    public static TheoryData<string> MeetingShapes => ["own", "enclosing", "none"];

    private static Func<int, int, string> ShapeOf(string name) => name switch
    {
        "own" => OwnMeeting,
        "enclosing" => EnclosingMeeting,
        _ => NoMeeting,
    };

    /// <summary>
    /// Every counter is f(K, L) = a·K + b·L + c: adding owners costs the same at two widths, and widening costs the same
    /// at two owner counts — so no counter has a K × L term, in the resolver, the exposure pass, the structural preflight
    /// or the evaluator's admission. (Sizes stay above the eight-entry copy threshold of completed summary seeds.)
    /// </summary>
    [Theory]
    [MemberData(nameof(MeetingShapes))]
    public void EveryCounter_IsAnOwnerTermPlusAWidthTerm(string shape)
    {
        const int fewOwners = 10, manyOwners = 26, narrow = 12, wide = 28;
        var build = ShapeOf(shape);
        var w11 = Work(build, fewOwners, narrow);
        var w21 = Work(build, manyOwners, narrow);
        var w12 = Work(build, fewOwners, wide);
        var w22 = Work(build, manyOwners, wide);
        var products = new List<string>();
        foreach (var counter in w11.Keys)
        {
            var ownersAtNarrow = w21[counter] - w11[counter];
            var ownersAtWide = w22[counter] - w12[counter];
            if (ownersAtNarrow != ownersAtWide)
                products.Add($"{counter} grows by {ownersAtNarrow} per {manyOwners - fewOwners} owners at width {narrow} but by {ownersAtWide} at width {wide}");
            var widthAtFew = w12[counter] - w11[counter];
            var widthAtMany = w22[counter] - w21[counter];
            if (widthAtFew != widthAtMany)
                products.Add($"{counter} grows by {widthAtFew} per {wide - narrow} names with {fewOwners} owners but by {widthAtMany} with {manyOwners}");
        }

        Assert.True(products.Count == 0, $"{shape}: " + string.Join("; ", products));
    }

    /// <summary>
    /// The exact physical representation of K own-meeting owners: G's tail and ONE excluded part, a one-slot head per owner,
    /// ONE bundle; the lifting charge is exactly those allocations (4 per pattern, 2 per argument).
    /// </summary>
    [Theory]
    [InlineData(16, 24)]
    [InlineData(48, 16)]
    public void OwnMeetingOwners_BuildOneExcludedPart_AndOneBundle(int owners, int width)
    {
        var passes = ObservePasses(OwnMeeting(owners, width));
        // G's plain signature, the shared tail, then one own head slot for each A.
        Assert.Equal(2L * width - 1 + owners, passes.Admission.PreEvaluationMetaPlacementSlots);
        var observed = passes.Resolve;
        Assert.Equal(2, observed.SignatureTemplatesBuilt);
        Assert.Equal(2L * width - 1, observed.SignatureTemplateSlotsBuilt);
        Assert.Equal(owners, observed.OwnerSignatureCollisions);
        Assert.Equal(owners, observed.OwnerSignatureInstances);
        Assert.Equal(owners, observed.OwnerSignatureHeadSlots);
        Assert.Equal(0, observed.OwnerSignaturesMaterialized);
        Assert.Equal(1, observed.SignatureCollisionPartsBuilt);
        Assert.Equal(1, observed.SignatureCollisionNamesExcluded);
        Assert.Equal(owners, observed.ImplicitCallsSynthesized);
        Assert.Equal(1, observed.ImplicitArgumentBundlesBuilt);
        Assert.Equal(width, observed.ImplicitArgumentSlotsBuilt);
        Assert.Equal(4L * (2 * width - 1) + 4L * owners + 2L * width, observed.LiftingStorageUnitsCharged);

        // Non-meeting owners still record no collision.
        var control = ObservePasses(NoMeeting(owners, width)).Resolve;
        Assert.Equal(0, control.OwnerSignatureCollisions);
        Assert.Equal(0, control.SignatureCollisionPartsBuilt);
        Assert.Equal(1, control.SignatureTemplatesBuilt);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void WideCollectorAndEnclosingSets_IndexOnlyTheSharedPartsAndOwnerHeads(bool enclosing)
    {
        FrontEndTraversalObservations Counters(int owners, int width)
        {
            var counters = ObservePasses(CollectorMeeting(owners, width, enclosing)).Resolve;
            Assert.Equal(1, counters.SignatureCollisionPartsBuilt);
            Assert.Equal(1, counters.ImplicitArgumentBundlesBuilt);
            Assert.Equal(width + 1, counters.ImplicitArgumentSlotsBuilt);
            return counters;
        }

        var narrow = Counters(8, 12).SignatureNameIndexSlots;
        var wide = Counters(8, 24).SignatureNameIndexSlots;
        Assert.True(wide > narrow);
        Assert.Equal(Counters(20, 12).SignatureNameIndexSlots - narrow,
            Counters(20, 24).SignatureNameIndexSlots - wide);
    }

    /// <summary>
    /// An owner left with none of the shared tail — every lifted name is its own — stores its own flat list (it lifts
    /// nothing new), and an owner whose collisions cover the tail's shared part but not a composed tail's local head keeps
    /// that head's remainder.
    /// </summary>
    [Fact]
    public void FullyCoveredTails_LiftNothing_OrKeepTheLocalHeadsRemainder()
    {
        var root = SourceProvenance.ParseValid("G = a + b\nA = G + a + b\nB = G + w\nC = B + a + b\nA(1, 2), C(3, 4, 5)").Root;
        // A binds every name G lifts: nothing is lifted, and its signature is its own written-order list.
        Assert.Equal("a, b", Shape(Owner(root, "A").ParameterPatterns));
        Assert.Null(Owner(root, "A").ForwardingParameterStart);
        // B is composed (w over G's tail); C meets the tail entirely, so only B's local head is left to lift.
        Assert.Equal("w, a, b", Shape(Owner(root, "B").ParameterPatterns));
        Assert.Equal("a, b, w", Shape(Owner(root, "C").ParameterPatterns));
        // A(1, 2) = G(1, 2) + 1 + 2; C(3, 4, 5) = B(5, 3, 4) + 3 + 4 = (G(3, 4) + 5) + 7.
        Assert.Equal("6\n19", KatLangEngine.Run("G = a + b\nA = G + a + b\nB = G + w\nC = B + a + b\nA(1, 2)\nC(3, 4, 5)").ToDisplayString().ReplaceLineEndings("\n"));
    }
}
