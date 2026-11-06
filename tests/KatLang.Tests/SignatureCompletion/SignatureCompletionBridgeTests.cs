using System.Text;
using KatLang.TestInfrastructure;

namespace KatLang.Tests;

/// <summary>
/// SC-1, THE BRIDGE between the Lean signature-completion reference kernel (<c>lean/KatLangArityLaws/SignatureCompletion.lean</c>)
/// and the REAL native selector. Every case is a program run through the real front end; the observer
/// (<see cref="FrontEndTraversalObservations.OnSignatureSelection"/>) reads the equations the real analysis gave the real
/// <see cref="SignatureSelector"/> and what it decided.
///
/// <para><b>Who computes what.</b> The inputs are generated from here into <c>lean/KatLangArityLaws/SignatureCompletionBridgeCases.lean</c>.
/// The expected outcomes (<c>SignatureCompletion/lean-model-outcomes.txt</c>) are written ONLY by the Lean model
/// (<c>lean/SignatureCompletionBridgeEmit.lean</c>) and never by this assembly, so no native answer reaches Lean as an
/// expectation; <c>SignatureCompletionGuards.lean</c> recomputes the file in the Lean phase, and these tests compare the
/// native selector with it. The two oracles of <see cref="RecursiveOriginOracleTests"/> and
/// <see cref="SignatureSelectionReviewRegressionTests"/> stay separate and independent of this bridge.</para>
///
/// <para><b>What agreement means.</b> Equality on this finite corpus of the selector's ordered patterns, kinds, X-02 flags and
/// refusal categories. It is executable evidence about these programs, not a proof about <c>SignatureSelector</c>, and it
/// says nothing about analysis as a function of source: the analyzed equations are inputs here, and so are origins (sealed
/// after stabilization), resource limits and cancellation, which have no modeled counterpart.</para>
/// </summary>
public sealed class SignatureCompletionBridgeTests
{
    private const string ArtifactRelativePath = "lean/KatLangArityLaws/SignatureCompletionBridgeCases.lean";
    private const string OutcomesRelativePath = "tests/KatLang.Tests/SignatureCompletion/lean-model-outcomes.txt";

    private const string Fixed = """
        X0(a) = a
        X1(b) = b
        X2(a, b) = a
        X3(*r) = 0
        X4(c, *r) = c
        X5(d, *s) = d
        X6((a, e)) = a
        X7([b, f]) = b
        X8(meta g) = g
        X9(a, *z) = a
        X10(c, r) = c
        X11(*n, a) = 0
        X12(n) = n
        X13(a, *n) = 0
        Cap(meta op) = op
        Id(v) = v

        """;

    private const string Link = "Cap(meta op) = op\nId(v) = v\nC(a, *p) = a\n";

    /// <summary>The curated cases: each names the behavior it discriminates.</summary>
    private static readonly (string Id, string Source)[] Curated =
    [
        ("acyclic-chain", "H(z) = z\nC = B + z2\nB = H + 1\n0"),
        ("acyclic-order", "P(p) = p\nQ(q) = q\nR = Q + P\nS = P + Q + R\n0"),
        ("gate-self-read", "A = if(tick() < 3, A + 1, 0)\n0"),
        ("recursive-self", "F = if(tick() > 3, x, F + 1)\n0"),
        ("recursive-mutual", "A = if(tick() > 3, x, B + 1)\nB = A + 1\n0"),
        ("written-order", "A = if(tick() > 3, x + y, B + 1)\nB = A + z\n0"),
        ("several-answers", "E(e) = e * 10\nF = if(tick() > 2, 0, F + G + E)\nG = p + F + 0\n0"),
        ("written-list-authoritative", "E(e) = e * 10\nF(p, e) = if(tick() > 2, 0, F + G + E)\nG = p + F + 0\n0"),
        ("oscillation", "X(x) = x\nY(y) = y\nA = B + X\nB = A + Y\n0"),
        ("oscillation-reader", "X(x) = x\nY(y) = y\nA = B + X\nB = A + Y\nR = A + 0\n0"),
        ("grouped-sequence", "P((a, b)) = a\nA = P + B\nB = A + c\n0"),
        ("grouped-list", "P([a, b]) = a\nA = P + B\nB = A + c\n0"),
        ("grouped-duplicate-collapses", "P(a, (a, b)) = a\nA = P + 1\n0"),
        ("grouped-singleton-collapses", "P((x, x)) = x\nA = P + B\nB = A + 0\n0"),
        ("list-group-keeps-brackets", "P(x, [x, a]) = a\nA = P + B\nB = A + 0\n0"),
        ("collector-shared-name", "C(n, *xs) = n\nD(m, *xs) = m\nK = C + D\n0"),
        ("collector-only-never-lifts", "H(*xs) = 0\nA = H + B\nB = A + 0\n0"),
        ("grouped-collector-forwarded", "H((*xs)) = 0\nA = H + B\nB = A + x\n0"),
        ("meta-lifts-ordinary", "M(meta r) = 0\nA = M + B\nB = A + 0\n0"),
        ("x02-recovered", "C1(a, *p) = a\nC2(b, *q) = b\nA = if(tick() > 2, 0, B + C1 + C2)\nB = A + 0\n0"),
        ("x02-retained", "C1(a, *p) = a\nC2(b, *q) = b\nA = if(tick() > 2, 0, C1 + C2 + B)\nB = A + 0\n0"),
        ("x02-acyclic", "C1(a, *p) = a\nC2(b, *q) = b\nK = C1 + C2\n0"),
        ("q04-filter", "H(a, b) = a\nOuter(a) = {\n    public K = H + L\n    public L = K + 0\n    0\n}\n0"),
        ("q04-rootless", "P(n) = n\nQ(k, *n) = 0\nOuter(k) = {\n    public C = D + P\n    0\n}\nA = B + Outer.C\nB = A + 0\nD = E + P\nE = Q + A\n0"),
        ("alias-one-callee", "H(x) = x\nA = H\nB = A + H + 1\n0"),
        ("declaration-order-1", "C = B + z\nA = { H = B + 0\n    x + 1 }\nB = y + A\n0"),
        ("declaration-order-2", "B = y + A\nC = B + z\nA = { H = B + 0\n    x + 1 }\n0"),
        ("link-grounded", Link + "Outer(a) = {\n    K = L.abs + 0\n    L = Cap(Id(K + C + 0)).Algorithm\n    0\n}\n0"),
        ("link-runtime-reading", Link + "B(p) = p\nD(z) = z\nOuter(a) = {\n    L = Cap(Id(K + 0)).Algorithm\n    K = L.repeat(D) + 0\n    X = L.repeat(C) + B + Y\n    Y = X + 0\n    0\n}\n0"),
        ("link-undetermined-settled", Link + "B(p) = p\nD(z) = z\nOuter(a) = {\n    L = Cap(Id(K + X + 0)).Algorithm\n    K = L.repeat(D) + 0\n    X = L.repeat(C) + B + Y\n    Y = X + 0\n    0\n}\n0"),
        ("link-ungrounded", Link + "W(x, y) = x\nX1(x) = x\nY1(y) = y\nD(z) = z\nOuter(a) = {\n    L = Cap(Id(K + 0)).Algorithm\n    K = L.repeat(D) + 0\n    A = L.repeat(W) + B + X1\n    B = A + Y1\n    0\n}\n0"),
        ("link-undetermined", Link + "W(x, y) = x\nX1(x) = x\nY1(y) = y\nD(z) = z\nOuter(a) = {\n    L = Cap(Id(K + A + 0)).Algorithm\n    K = L.repeat(D) + 0\n    A = L.repeat(W) + B + X1\n    B = A + Y1\n    0\n}\n0"),
        ("link-contradiction", Link + "A0 = C + 0\nB(p) = p\nOuter(a) = {\n    L1 = Cap(Id(H1 + 0)).Algorithm\n    H1 = L1.abs.repeat(A0) + B\n    0\n}\n0"),
        ("link-w14u", Link + "A0 = C + 0\nB(p) = p\nOuter(a) = {\n    Lx1 = Cap(Id(Hx1 + 0)).Algorithm\n    Hx1 = Ln1.repeat(A0) + B\n    Ln1 = Cap(Id(Hn1 + 0)).Algorithm\n    Hn1 = Lx1.repeat(A0) + B\n    Lf1 = Cap(Id(Hf1 + 0)).Algorithm\n    Hf1 = Lf1.repeat(A0) + Lx1.repeat(A0) + B\n    0\n}\n0"),
        ("link-ambiguous-c2", RecursiveParameterInferenceTests.C2),
        ("guarded-provider-calculation", Fixed + "Outer(a) = {\n    public E0 = E2.repeat(X12) + E1 + X0\n    public E1 = E0 + X1\n    public E2 = Cap(Id(E3 + 0)).Algorithm\n    public E3 = X1 + 0\n    0\n}\n0"),
        ("guarded-provider-runtime", Fixed + "Outer(a) = {\n    public E0 = E2.repeat(X12) + E1 + X0\n    public E1 = E0 + X1\n    public E2 = Cap(Id(E3 + 0)).Algorithm\n    public E3 = 0\n    0\n}\n0"),
        ("guard-inside-group", Fixed + "Outer(a) = {\n    public E0 = E1 + E2.repeat(X13) + X12\n    public E1 = E0 + X12\n    public E2 = Cap(Id(E0 + 0)).Algorithm\n    0\n}\n0"),
        ("guard-contradiction", Fixed + "Outer(a) = {\n    public E0 = E2.repeat(X13) + E1 + X12\n    public E1 = E0 + X12\n    public E2 = Cap(Id(E0 + 0)).Algorithm\n    0\n}\n0"),
    ];

    private const int RandomCases = 260;

    /// <summary>Seeded programs over the declarations above, with rings, a Q-04 context and, in a third of them, links.</summary>
    private static (string Id, string Source) Generated(int seed)
    {
        var random = new Random(seed);
        var count = random.Next(1, 6);
        var linkCount = seed % 3 == 0 ? random.Next(1, Math.Min(count, 3) + 1) : 0;
        var isLink = Enumerable.Range(0, count).Select(i => i < linkCount).ToArray();
        var nested = random.NextDouble() < 0.4;
        string Read(int from)
        {
            var roll = random.NextDouble();
            if (linkCount > 0 && roll < 0.3)
                return $"E{random.Next(linkCount)}.repeat(X{random.Next(14)})";
            return roll < 0.65 ? $"E{random.Next(count)}" : $"X{random.Next(14)}";
        }

        var lines = new List<string>();
        for (var i = 0; i < count; i++)
        {
            if (isLink[i])
            {
                lines.Add($"E{i} = Cap(Id(E{random.Next(count)} + {(random.NextDouble() < 0.5 ? $"X{random.Next(14)}" : "0")})).Algorithm");
                continue;
            }

            var terms = new List<string>();
            if (random.NextDouble() < 0.25)
                terms.Add(random.NextDouble() < 0.5 ? "a" : "v");
            if (random.NextDouble() < 0.5)
                terms.Add($"E{(i + 1) % count}");
            for (var r = random.Next(0, 4); r > 0; r--)
                terms.Add(Read(i));
            terms.AddRange(["0", "0"]);
            lines.Add($"E{i} = {string.Join(" + ", terms)}");
        }

        var ordered = lines.OrderBy(_ => random.Next()).ToArray();
        var body = nested
            ? "Outer(a) = {\n" + string.Concat(ordered.Select(static line => "    public " + line + "\n")) + "    0\n}\n"
            : string.Concat(ordered.Select(static line => line + "\n"));
        return ($"random-{seed}", Fixed + body + "0");
    }

    private static IEnumerable<(string Id, string Source)> Corpus()
        => Curated.Concat(Enumerable.Range(1, RandomCases).Select(Generated));

    // ── observing the real front end ────────────────────────────────────────────────────────────

    private sealed record Observed(string Id, SignatureSelectionProbe Probe, string System, string Outcome);

    private static (Algorithm? Resolved, List<SignatureSelectionProbe> Probes) Run(Algorithm root, Action<SignatureSelectionProbe>? inside = null)
    {
        var probes = new List<SignatureSelectionProbe>();
        var observations = new FrontEndTraversalObservations
        {
            OnSignatureSelection = probe =>
            {
                probes.Add(probe);
                inside?.Invoke(probe);
            },
        };
        var detected = ParameterDetector.DetectPrevalidated(root);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations, new DiagnosticBag());
        return (resolved, probes);
    }

    private static List<Observed> Observe(Action<string, SignatureSelectionProbe>? inside = null)
    {
        var observed = new List<Observed>();
        foreach (var (id, source) in Corpus())
        {
            var (_, probes) = Run(SourceProvenance.ParseSyntaxValidRoot(source), inside is null ? null : probe => inside(id, probe));
            for (var i = 0; i < probes.Count; i++)
                observed.Add(new Observed(probes.Count == 1 ? id : $"{id}#{i}", probes[i], LeanSystem(probes[i]), NativeOutcome(probes[i])));
        }

        return observed;
    }

    // ── the two renderings ──────────────────────────────────────────────────────────────────────

    private static string RenderPattern(ParameterPattern pattern) => pattern switch
    {
        CaptureParameterPattern { Kind: ParameterKind.Collecting } capture => "*" + capture.Name,
        CaptureParameterPattern { Kind: ParameterKind.Meta } capture => "meta " + capture.Name,
        CaptureParameterPattern capture => capture.Name,
        SequenceValueParameterPattern group => "(" + RenderPatterns(group.Items) + ")",
        ListValueParameterPattern group => "[" + RenderPatterns(group.Items) + "]",
        UnpackingParameterPattern group => "<" + RenderPatterns(group.Items) + ">",
        _ => throw new InvalidOperationException($"Unhandled pattern {pattern.GetType().Name}."),
    };

    private static string RenderPatterns(IEnumerable<ParameterPattern> patterns) => string.Join(",", patterns.Select(RenderPattern));

    private static string RenderViolation(ParameterSignatureViolation? violation) => violation switch
    {
        null => "",
        ParameterSignatureViolation.SingletonSequencePattern => "!singleton",
        ParameterSignatureViolation.MultipleCollectingAtOneLevel => "!collectors",
        ParameterSignatureViolation.RepeatedNameIncludesCollecting => "!repeated",
        _ => throw new InvalidOperationException($"Unhandled violation {violation}."),
    };

    /// <summary>The outcome as the Lean rendering prints it. Refusals of several categories render as a word Lean never prints.</summary>
    private static string NativeOutcome(SignatureSelectionProbe probe) => NativeOutcome(probe.Selection, probe.Equations.Count);

    private static string NativeOutcome(SignatureSelector.Selection selection, int count)
    {
        if (selection.Succeeded)
        {
            return "selected " + string.Join(" ", Enumerable.Range(0, count).Select(key =>
                $"{key}:({RenderPatterns(selection.Facts[key].Patterns)}){RenderViolation(selection.Facts[key].Violation)}"));
        }

        var categories = selection.Refusals.Select(static refusal => refusal.Outcome).Distinct().ToArray();
        return "refused " + (categories.Length == 1 ? categories[0].ToString() : "Mixed");
    }

    private static string LeanPattern(ParameterPattern pattern) => pattern switch
    {
        CaptureParameterPattern { Kind: ParameterKind.Collecting } capture => $"c {Quote(capture.Name)}",
        CaptureParameterPattern { Kind: ParameterKind.Meta } capture => $"m {Quote(capture.Name)}",
        CaptureParameterPattern capture => $"p {Quote(capture.Name)}",
        SequenceValueParameterPattern group => $".sequenceValue {LeanPatterns(group.Items)}",
        ListValueParameterPattern group => $".listValue {LeanPatterns(group.Items)}",
        UnpackingParameterPattern group => $".unpacking {LeanPatterns(group.Items)}",
        _ => throw new InvalidOperationException($"Unhandled pattern {pattern.GetType().Name}."),
    };

    private static string LeanPatterns(IEnumerable<ParameterPattern> patterns)
        => "[" + string.Join(", ", patterns.Select(LeanPattern)) + "]";

    private static string Quote(string text)
    {
        Assert.DoesNotContain(text, static c => c is '"' or '\\' or '\n');
        return "\"" + text + "\"";
    }

    /// <summary>The analyzed system as a Lean term: one number per callee identity, by reference, in first-occurrence order.</summary>
    private static string LeanSystem(SignatureSelectionProbe probe)
    {
        var identities = new Dictionary<object, int>(ReferenceEqualityComparer.Instance);
        var equations = probe.Equations.Select(equation =>
        {
            var references = equation.References.Select(reference =>
            {
                if (!identities.TryGetValue(reference.Identity, out var identity))
                    identities.Add(reference.Identity, identity = identities.Count);
                var target = reference.Target >= 0
                    ? $".member {reference.Target}"
                    : $".external {LeanPatterns(reference.External!.ParameterPatterns)}";
                var guard = reference.Guard >= 0 ? $"some {reference.Guard}" : "none";
                return $"⟨{target}, {identity}, {guard}⟩";
            });
            var forwardable = "[" + string.Join(", ", equation.Forwardable.Order(StringComparer.Ordinal).Select(Quote)) + "]";
            return $"{{ own := {LeanPatterns(equation.Own)}, forwardable := {forwardable}, "
                + $"references := [{string.Join(", ", references)}], isLink := {(equation.IsLink ? "true" : "false")} }}";
        });
        return "[" + string.Join(",\n    ", equations) + "]";
    }

    private static string GenerateArtifact(IReadOnlyList<Observed> observed)
    {
        var text = new StringBuilder();
        text.Append("""
            -- GENERATED by tests/KatLang.Tests/SignatureCompletion/SignatureCompletionBridgeTests.cs. Do not edit by hand.
            -- These are the equation systems the REAL C# analysis handed the REAL selector: inputs only. No native outcome
            -- is in this file. Regenerate with KATLANG_REGENERATE_SIGNATURE_COMPLETION_BRIDGE=1, then rewrite the outcomes with
            -- lean/SignatureCompletionBridgeEmit.lean (see that file).
            import KatLangArityLaws.SignatureCompletion

            open KatLang KatLang.SignatureCompletion

            namespace KatLang.SignatureCompletion.Bridge

            private def p (name : String) : ParameterPattern := .capture { name := name }
            private def c (name : String) : ParameterPattern := .capture { name := name, kind := .collecting }
            private def m (name : String) : ParameterPattern := .capture { name := name, kind := .metaRef }


            """);
        for (var i = 0; i < observed.Count; i++)
            text.Append($"private def case{i} : List Equation :=\n    {observed[i].System}\n\n");
        text.Append("/-- Every case: its id and its analyzed system. -/\ndef bridgeCases : List (String × System) := [\n");
        text.Append(string.Join(",\n", observed.Select((item, i) => $"  ({Quote(item.Id)}, System.ofList case{i})")));
        text.Append("]\n\nend KatLang.SignatureCompletion.Bridge\n");
        return text.ToString();
    }

    private static Dictionary<string, string> LeanOutcomes()
    {
        var path = Path.Combine(RepoRoot.Find(), OutcomesRelativePath);
        Assert.True(File.Exists(path), $"{OutcomesRelativePath} is missing: run lean/SignatureCompletionBridgeEmit.lean.");
        return File.ReadAllLines(path).Where(static line => line.Length != 0).Select(static line =>
        {
            var separator = line.IndexOf('\t');
            return (Id: line[..separator], Outcome: line[(separator + 1)..]);
        }).ToDictionary(static item => item.Id, static item => item.Outcome, StringComparer.Ordinal);
    }

    // ── the tests ───────────────────────────────────────────────────────────────────────────────

    [Fact]
    public void GeneratedInputs_AreTheEquationsTheRealAnalysisProduces()
    {
        var observed = Observe();
        var expected = GenerateArtifact(observed);
        var path = Path.Combine(RepoRoot.Find(), ArtifactRelativePath);
        var flag = RegenerationFlags.SignatureCompletionBridge;
        ArtifactRegeneration.VerifyOrRegenerate(
            flag,
            ArtifactRelativePath,
            regenerate: () => expected,
            verify: () =>
            {
                Assert.True(File.Exists(path), $"{ArtifactRelativePath} is missing. Set {flag}=1 and rerun (that run fails by design).");
                var actual = File.ReadAllText(path).ReplaceLineEndings("\n");
                Assert.True(expected == actual, $"{ArtifactRelativePath} differs from the current analysis. Set {flag}=1 and rerun, then "
                    + "rewrite the outcomes with lean/SignatureCompletionBridgeEmit.lean. "
                    + SemanticExplorerLeanArtifactTests.DescribeFirstDifference(expected, actual));
            },
            afterRegenerating: "rewrite the outcomes with lean/SignatureCompletionBridgeEmit.lean, then run `lake build KatLangArityLaws`");
    }

    /// <summary>
    /// THE BRIDGE: on every corpus system the real selector and the Lean kernel agree exactly: ordered patterns, kinds, X-02
    /// flags, or the refusal category. The native selector reports each refused group by its own category and the kernel's
    /// whole-system rule gives one, so a system whose groups refuse differently would render as <c>Mixed</c> and fail here: the
    /// corpus has none, and this comparison makes no claim about one.
    /// </summary>
    [Fact]
    public void TheRealSelector_AgreesWithTheLeanKernel_OnTheWholeCorpus()
    {
        var lean = LeanOutcomes();
        var observed = Observe();
        Assert.Equal(lean.Count, observed.Count);
        var disagreements = new List<string>();
        foreach (var item in observed)
        {
            Assert.True(lean.TryGetValue(item.Id, out var expected), $"{item.Id} has no Lean outcome.");
            if (item.Outcome != expected)
                disagreements.Add($"{item.Id}\n  lean   {expected}\n  native {item.Outcome}\n  system {item.System}");
        }

        Assert.True(disagreements.Count == 0, $"{disagreements.Count} of {observed.Count}:\n{string.Join("\n", disagreements.Take(10))}");
    }

    /// <summary>The corpus reaches what the bridge claims to compare: every outcome, recursion, links and each pattern kind.</summary>
    [Fact]
    public void TheCorpus_CoversTheDiscriminatingBehaviors()
    {
        var outcomes = LeanOutcomes();
        var observed = Observe();
        foreach (var word in new[] { "selected", "refused Ambiguous", "refused Contradiction", "refused UngroundedOnly", "refused Undetermined", "refused NonSettling" })
            Assert.Contains(outcomes.Values, outcome => outcome.StartsWith(word, StringComparison.Ordinal));
        Assert.Contains(outcomes.Values, static outcome => outcome.Contains("!collectors", StringComparison.Ordinal));
        Assert.Contains(outcomes.Values, static outcome => outcome.Contains('*'));
        Assert.Contains(outcomes.Values, static outcome => outcome.Contains('['));
        Assert.Contains(outcomes.Values, static outcome => outcome.Contains(":((", StringComparison.Ordinal));
        Assert.Contains(observed, static item => item.Probe.Equations.Any(static equation => equation.IsLink));
        Assert.Contains(observed, static item => item.Probe.Equations.Any(static equation => equation.Forwardable.Count != 0));
        Assert.Contains(observed, static item => item.Probe.Equations.Any(static equation => equation.References.Any(static reference => reference.Guard >= 0)));
        Assert.Contains(observed, static item => item.Probe.Equations.Any(static equation => equation.References.Any(static reference =>
            reference.External?.ParameterPatterns.Any(static pattern => pattern is CaptureParameterPattern { Kind: ParameterKind.Meta }) ?? false)));
    }

    /// <summary>What a selected system publishes is what the selection decided, read from the resolved tree.</summary>
    [Fact]
    public void ASelectedSignature_IsWhatTheResolvedTreePublishes()
    {
        var compared = 0;
        foreach (var (_, source) in Curated)
        {
            var (resolved, probes) = Run(SourceProvenance.ParseSyntaxValidRoot(source));
            var probe = Assert.Single(probes);
            if (!probe.Selection.Succeeded || probe.Selection.Facts.Values.Any(static fact => fact.Violation is not null))
                continue;
            foreach (var property in resolved!.Properties)
            {
                var indices = Enumerable.Range(0, probe.Equations.Count).Where(i => probe.Equations[i].Name == property.Name).ToArray();
                if (indices.Length != 1 || property.Value is not Algorithm.User user)
                    continue;
                Assert.Equal(RenderPatterns(probe.Selection.Facts[indices[0]].Patterns), RenderPatterns(user.ParameterPatterns));
                compared++;
            }
        }

        Assert.True(compared > 20, $"Only {compared} published signatures were compared.");
    }

    /// <summary>
    /// ONE BODY, TWO DECLARING CONTEXTS: the integration boundary of the analysis's region aliases. A host-built shared body has
    /// one equation (D1a's region alias), and both resolved contexts publish the native selected fact. This host-built
    /// graph is an integration check, separate from the source corpus compared with Lean.
    /// </summary>
    [Fact]
    public void ASharedBody_HasOneEquation_AndBothContextsReadItsFact()
    {
        static Algorithm.User Block(IReadOnlyList<Property> properties, params Expr[] rows) => new(null, [], [], properties, new OutputBundle(rows));
        var need = new Algorithm.User(null, [new CaptureParameterPattern("p")], [], [], new OutputBundle([new Expr.Param("p")])) { HasExplicitParameterList = true };
        var shared = Block([new Property("Q", Block([], new Expr.Binary(BinaryOp.Add, new Expr.Resolve("Need"), new Expr.Num(0))), IsPublic: true)], new Expr.Num(0));
        var root = Block(
            [
                new Property("Need", need),
                new Property("Left", Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0))),
                new Property("Right", Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0))),
            ],
            new Expr.Num(0));

        SignatureSelectionProbe? probe = null;
        var observations = new FrontEndTraversalObservations { OnSignatureSelection = seen => probe = seen };
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root, observations, diagnostics);
        Assert.Equal(0, diagnostics.ReportedCount);
        Assert.NotNull(probe);
        Assert.Single(probe.Equations, static equation => equation.Name == "Q");
        var q = probe.Equations.ToList().FindIndex(static equation => equation.Name == "Q");
        Assert.Equal("p", RenderPatterns(probe.Selection.Facts[q].Patterns));
        foreach (var contextName in new[] { "Left", "Right" })
        {
            var context = Assert.IsType<Algorithm.User>(Assert.Single(resolved.Properties, property => property.Name == contextName).Value);
            var sharedView = Assert.IsType<Algorithm.User>(Assert.Single(context.Properties, static property => property.Name == "S").Value);
            var published = Assert.IsType<Algorithm.User>(Assert.Single(sharedView.Properties, static property => property.Name == "Q").Value);
            Assert.Equal(RenderPatterns(probe.Selection.Facts[q].Patterns), RenderPatterns(published.ParameterPatterns));
        }
    }

    // ── negative controls: the bridge can fail ──────────────────────────────────────────────────

    private delegate IReadOnlyList<SignatureEquationReference>[] Mutate(IReadOnlyList<SignatureEquationReference>[] references);

    /// <summary>The REAL selector and composition over a deliberately wrong input; returns its outcome text.</summary>
    private static string Mutated(SignatureSelectionProbe probe, Mutate mutate, bool[]? isLink = null)
    {
        var references = mutate([.. probe.Equations.Select(static equation => equation.References)]);
        var selection = new SignatureSelector(references, isLink ?? [.. probe.Equations.Select(static equation => equation.IsLink)],
            probe.Compose, static (_, settled, _) => settled, probe.Closed,
            new StaticQueryResourceBudget(StaticQueryLimits.Default), CancellationToken.None).Solve();
        return NativeOutcome(selection, probe.Equations.Count);
    }

    /// <summary>
    /// Each wrong rule run through the real selector disagrees with the Lean outcomes on some case, so a selector with that
    /// defect would be detected: written reference order, guard classification and link class. (A wrong ROUND order is
    /// a kernel-side control: <c>SignatureCompletionGuards.lean</c> shows in-place rounds miss the expected outcome.)
    /// </summary>
    [Theory]
    [InlineData("ReversedReferences")]
    [InlineData("GuardsIgnored")]
    [InlineData("LinksDeclassified")]
    public void AWrongRule_IsDetectedByTheBridge(string mutation)
    {
        var lean = LeanOutcomes();
        var detected = 0;
        var compared = 0;
        foreach (var (id, source) in Corpus())
        {
            Run(SourceProvenance.ParseSyntaxValidRoot(source), probe =>
            {
                if (!lean.TryGetValue(id, out var expected))
                    return;
                compared++;
                var outcome = mutation switch
                {
                    "ReversedReferences" => Mutated(probe, static all => [.. all.Select(static list => (IReadOnlyList<SignatureEquationReference>)[.. list.Reverse()])]),
                    "GuardsIgnored" => Mutated(probe, static all => [.. all.Select(static list => (IReadOnlyList<SignatureEquationReference>)[.. list.Select(static reference => reference with { Guard = -1 })])]),
                    _ => Mutated(probe, static all => all, new bool[probe.Equations.Count]),
                };
                if (outcome != expected)
                    detected++;
            });
        }

        Assert.True(compared == 299 && detected >= 5, $"{mutation}: {detected} of {compared} detected.");
    }

    /// <summary>The unchanged control run: the same harness with no mutation agrees on every compared case.</summary>
    [Fact]
    public void TheUnmutatedControl_AgreesThroughTheSameHarness()
    {
        var lean = LeanOutcomes();
        var compared = 0;
        foreach (var (id, source) in Curated)
        {
            Run(SourceProvenance.ParseSyntaxValidRoot(source), probe =>
            {
                compared++;
                Assert.Equal(lean[id], Mutated(probe, static all => all));
            });
        }

        Assert.True(compared > 20, $"Only {compared} compared.");
    }

    /// <summary>
    /// FC-AC: the program whose final Lean heap holds a stored-address two-cycle (<c>HeapEdgeAcyclicityGuards.lean</c>) is valid and
    /// agrees on every route. So acyclicity of all stored addresses is no contract of the language; a stored reference is not
    /// a demand. This is an observation of the outcome only: the C# cell graph itself is not inspected.
    /// </summary>
    [Fact]
    public async Task AStoredAddressCycle_IsAValidProgram()
    {
        const string Source = "Capture(meta op) = op\nInner(v) = v\nQ = P\nP = Capture(Inner(Q))\nP == P.Arguments[0]";
        var observation = await SixRouteAgreement.OnEveryRouteAsync(Source);
        Assert.True(observation is { Kind: "ok", Value: "true" }, observation.ToString());
    }

    /// <summary>
    /// THE RESOURCE BOUNDARY has no modeled counterpart and is compared with nothing in Lean: the same oscillation is
    /// <see cref="DiagnosticCode.StaticStructureLimitExceeded"/> under a tiny ledger and the semantic refusal under the default,
    /// so exhaustion never decides inference. The kernel's matching law is <c>exhausted_decides_nothing</c>.
    /// </summary>
    [Fact]
    public void Exhaustion_IsNeverTheSemanticRefusal()
    {
        const string Source = "X(x) = x\nY(y) = y\nA = B + X\nB = A + Y\n0";
        var tight = Parser.Parse(Source, new RunOptions { SourceProcessingLimits = new() { MaxStaticStructureBytes = 1024 } });
        Assert.Contains(tight.Diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.StaticStructureLimitExceeded);
        Assert.DoesNotContain(tight.Diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.SelfDependentInferredParameters);
        Assert.Contains(Parser.Parse(Source).Diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.SelfDependentInferredParameters);
    }
}
