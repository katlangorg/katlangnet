namespace KatLang.Tests;

/// <summary>
/// DECLARATION ORDER IS UNOBSERVABLE (B3-5★, November 2026; formerly X-04's confined fallback).
///
/// <para>Implicit-argument resolution selects every inferred signature of a resolution BEFORE it rewrites
/// anything — one equation per written body per declaring context (D1a), solved by rule G6 — and then
/// processes a level's properties in declaration order over those final signatures. No processing order,
/// sibling cycle fallback or on-demand processing remains. A helper declared inside a body is a body of
/// its own, so the programs below, whose sibling reads once closed a "cycle" through a helper
/// (<c>A = { H = B + 0 ⏎ x + 1 }</c> / <c>B = y + A</c>), have no equation cycle at all and settle the
/// same way in every declaration order — including the one where the former fallback let a member
/// processed first read another unprocessed. (A genuine lifting cycle is refused, X-04 B; see
/// <see cref="SignatureSelectionTests"/>.)</para>
///
/// <para>Pinned as a declaration-order METAMORPHIC matrix over source programs of every graph shape —
/// every permutation must agree on the consumer's inferred signature, its value, the diagnostics and the
/// host-call log, on all six execution routes — and the editor's view of the consumer.</para>
/// </summary>
public sealed class SiblingDependencyCycleTests
{
    /// <summary>Every ordering of <paramref name="items"/>.</summary>
    private static IEnumerable<T[]> Permutations<T>(IReadOnlyList<T> items)
    {
        if (items.Count <= 1)
        {
            yield return [.. items];
            yield break;
        }

        for (var index = 0; index < items.Count; index++)
        {
            var rest = items.Where((_, other) => other != index).ToArray();
            foreach (var tail in Permutations(rest))
                yield return [items[index], .. tail];
        }
    }

    // ── Source programs: declaration order is unobservable ───────────────────────────────────

    /// <summary>
    /// One graph shape as a program: its declarations (each one or more lines), the property whose
    /// signature the shape decides, and the row that calls it. Every declaration order of the program
    /// must give <paramref name="Signature"/> and the observation of <paramref name="Value"/> (traced),
    /// identically on all six routes.
    /// </summary>
    public sealed record Shape(string Name, string[] Declarations, string Focus, string Call, string Signature, string Value)
    {
        public override string ToString() => Name;
    }

    private const string CycleA = "A = { H = B + 0\n  x + 1 }";
    private const string CycleB = "B = y + A";

    public static TheoryData<Shape> Shapes() =>
    [
        // The X-04 witness: C = B + z read B's intermediate C(z, y) when declared first.
        new Shape("canonical", ["C = B + z", CycleA, CycleB], "C", "C(1, 2, 3)", "C(z, y, x)", "7"),
        // A three-member cycle A → B → C → A with an acyclic dependent.
        new Shape(
            "three-member-cycle",
            ["D = C + d", "A = { H = B + 0\n  a + 1 }", "B = { H = C + 0\n  b + 2 }", "C = c + A"],
            "D", "D(1, 2, 3)", "D(d, c, a)", "7"),
        new Shape("chain-after-cycle", ["E = D + v", "D = C + w", "C = B + z", CycleA, CycleB], "E", "E(1, 2, 3, 4, 5)", "E(v, w, z, y, x)", "16"),
        new Shape("diamond-after-cycle", ["E = C + D", "C = B + p", "D = B + q", CycleA, CycleB], "E", "E(1, 2, 3, 4)", "E(p, y, x, q)", "17"),
        new Shape(
            "two-cycles-one-consumer",
            ["C = B + Q", CycleA, CycleB, "P = { H = Q + 0\n  u + 10 }", "Q = v + P"],
            "C", "C(1, 2, 3, 4)", "C(y, x, v, u)", "21"),
        // An acyclic producer the cycle reads (processed before it).
        new Shape("upstream-producer", ["C = B + z", CycleA, "B = y + A + P", "P = p * 10"], "C", "C(1, 2, 3, 4)", "C(z, y, x, p)", "47"),
        // A dotted read of a cycle member's public member (a hard edge to the head).
        new Shape(
            "dotted-member-read",
            ["C = A.V + z", "A = { public V = B + x\n  0 }", "B = { H = A.V + 0\n  y + 1 }"],
            "C", "C(1, 2, 3)", "C(z, x, y)", "7"),
        // A read through the consumer's own `open` of a cycle member (a soft preference).
        new Shape(
            "opened-member-read",
            ["D = { open A\n  V + z }", "A = { public V = B + x\n  0 }", "B = { H = A.V + 0\n  y + 1 }"],
            "D", "D(1, 2, 3)", "D(z, x, y)", "7"),
        // A closed consumer forwards its own bindings to the cycle member's FINAL signature (the parser
        // elaborates clause groups after plain properties, so it never preceded the cycle).
        new Shape("explicit-closed-consumer", ["C(z, y, x) = B + z", CycleA, CycleB], "C", "C(1, 2, 3)", "C(z, y, x)", "7"),
        // A property reading itself is no cycle (the channel records no self-edge) and absorbs nothing.
        new Shape("self-reading-property", ["C = S + z", "S = { H = S + 0\n  s + 5 }"], "C", "C(1, 2)", "C(z, s)", "8"),
    ];

    private static string Program(IEnumerable<string> declarations, string row)
        => string.Join("\n", declarations) + "\n" + row;

    [Theory]
    [MemberData(nameof(Shapes))]
    public async Task EveryDeclarationOrder_InfersTheSameSignature_AndEvaluatesTheSame_OnEveryRoute(Shape shape)
    {
        foreach (var declared in Permutations(shape.Declarations))
        {
            var source = Program(declared, $"trace({shape.Call})");
            var parsed = SourceProvenance.ParseValid(source);
            var focus = Assert.Single(parsed.Root.Properties, property => property.Name == shape.Focus);
            Assert.Equal(shape.Signature, CallableSignature.FromAlgorithm(focus.Name, focus.Value).DisplayText);

            var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
            Assert.True(observation is { Kind: "ok" } && observation.Value == shape.Value,
                $"{shape.Name} in the order\n{source}\ngave {observation}");
            Assert.Equal([$"trace({shape.Value})"], observation.HostCalls);
        }
    }

    /// <summary>
    /// The former X-04 residue: <c>A</c>'s parameter <c>p</c> comes from lifting the producer <c>P</c>, so
    /// it is not in <c>A</c>'s input signature, and under the processing order a <c>B</c> processed before
    /// <c>A</c> read <c>A</c> without it (<c>C(z, y)</c>, an arity error at the call). The selection reads
    /// no input signature: in EVERY declaration order <c>A</c> is <c>A(p)</c>, <c>B</c> is <c>B(y, p)</c>
    /// and the consumer <c>C(z, y, p)</c> gives 34 on every route.
    /// </summary>
    [Fact]
    public async Task ALiftedParameterReachesEveryReader_InEveryDeclarationOrder()
    {
        string[] declarations = ["C = B + z", "A = { H = B + 0\n  P + 1 }", "B = y + A", "P = p * 10"];
        foreach (var declared in Permutations(declarations))
        {
            var source = Program(declared, "trace(C(1, 2, 3))");
            var root = SourceProvenance.ParseValid(source).Root;
            var consumer = Assert.Single(root.Properties, static property => property.Name == "C");
            Assert.Equal("C(z, y, p)", CallableSignature.FromAlgorithm(consumer.Name, consumer.Value).DisplayText);

            var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
            Assert.True(observation is { Kind: "ok", Value: "34" }, $"{source}\ngave {observation}");
            Assert.Equal(["trace(34)"], observation.HostCalls);
        }
    }

    /// <summary>
    /// X-04 × X-07: whether an output-less consumer of a cycle is a function — and so the front-end
    /// error an output-less function is — depends on the cycle member's SETTLED signature (<c>B</c>'s
    /// input signature has no parameter; lifting gives it <c>x</c>). Formerly the consumer declared
    /// first read the intermediate one and was a valid container (the program printed 5); declared
    /// last it reached the evaluator as an unpositioned failure. Every order is now the same
    /// positioned front-end error, and nothing runs.
    /// </summary>
    [Fact]
    public async Task AnOutputLessConsumerOfACycle_IsJudgedOnTheSettledSignature_InEveryDeclarationOrder()
    {
        foreach (var declared in Permutations(["F = { a, b = B + 0, 1 }", CycleA, "B = A + 0"]))
        {
            var source = Program(declared, "trace(5)");
            var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
            Assert.Equal("parse", observation.Kind);
            Assert.Empty(observation.HostCalls);
            var error = Assert.Single(observation.Errors);
            var line = Array.IndexOf(source.Split('\n'), "F = { a, b = B + 0, 1 }") + 1;
            Assert.StartsWith($"{nameof(KatLangErrorCode.ExplicitParametersRequireOutput)}: This algorithm takes the implicit parameter 'x' but does not define an output.", error, StringComparison.Ordinal);
            Assert.EndsWith($"@ [{line}:1, {line}:2)", error, StringComparison.Ordinal);
        }
    }

    /// <summary>
    /// The editor sees what evaluation sees: in every declaration order the consumer's reference
    /// resolves to the cycle member's declaration and the consumer's parameters are the settled ones.
    /// </summary>
    [Fact]
    public void TheEditorModel_OfAConsumerOfACycle_IsTheSameInEveryDeclarationOrder()
    {
        foreach (var declared in Permutations(["C = B + z", CycleA, CycleB]))
        {
            var source = Program(declared, "C(1, 2, 3)");
            var model = Semantics.SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
            var lines = source.Split('\n');
            var consumerLine = Array.IndexOf(lines, "C = B + z") + 1;
            var declarationLine = Array.FindIndex(lines, static line => line.StartsWith("B = ", StringComparison.Ordinal)) + 1;

            var resolution = model.FindResolutionAt(new SourcePosition(consumerLine, 5));
            Assert.NotNull(resolution);
            Assert.Equal("B", resolution.ResolvedDeclaration?.Name);
            Assert.Equal(new SourceSpan(declarationLine, 1, declarationLine, 2), resolution.ResolvedDeclaration?.Span);

            var consumer = Assert.Single(model.FindProperties("C"));
            Assert.Equal(["z", "y", "x"], consumer.Parameters.Select(static parameter => parameter.DisplayName));
        }
    }

    /// <summary>
    /// The helper inside <c>A</c> is a body of its own (D1a), so it closes no equation cycle: it reads
    /// <c>B</c>'s selected signature <c>B(y, x)</c> and forwards <c>A</c>'s own <c>x</c> in every
    /// declaration order (formerly the member processed first read the other's INPUT signature, so the
    /// helper called <c>B(y)</c> whenever <c>A</c> was declared before <c>B</c>).
    /// </summary>
    [Fact]
    public void TheHelperReadsTheSelectedSignature_InEveryDeclarationOrder()
    {
        foreach (var declared in Permutations(["C = B + z", CycleA, CycleB]))
        {
            var root = SourceProvenance.ParseValid(Program(declared, "C(1, 2, 3)")).Root;
            var a = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == "A").Value);
            var helper = Assert.IsType<Algorithm.User>(Assert.Single(a.Properties, property => property.Name == "H").Value);
            var sum = Assert.IsType<Expr.Binary>(Assert.Single(helper.Output));
            Assert.Equal(2, Assert.IsType<Expr.Call>(sum.Left).Args.Count);
        }
    }
}
