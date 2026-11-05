using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// RECURSIVE PARAMETER INFERENCE (X-04 plain A-agree, owner direction 2026-11-05; § Recursive parameter inference of
/// <c>ownership-and-lookup.md</c>). A recursive group is composed by the ordinary law, simultaneously, from the closed
/// gate, and the state the rounds reach is the answer. Every value below is stated, not compared between routes alone:
/// parity of six routes proves agreement, not correctness. A fixture with <c>tick()</c> runs on the one tick counter of
/// its own run, so effects are isolated per observation.
/// </summary>
public sealed class RecursiveParameterInferenceTests
{
    internal static IEnumerable<T[]> Permutations<T>(IReadOnlyList<T> items)
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

    private static string Program(IEnumerable<string> declarations, string row) => string.Join("\n", declarations) + "\n" + row;

    internal static string Signature(string source, string name)
        => Assert.Single(SemanticModelBuilder.Build(Parser.Parse(source)).FindProperties(name)).DisplaySignature;

    internal static async Task AssertValue(string source, string value)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation is { Kind: "ok" } && observation.Value == value, $"{source}\ngave {observation}");
    }

    private static async Task<SixRouteAgreement.Observation> Refused(string source, int errors)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "parse", $"{source}\ngave {observation}");
        Assert.Equal(errors, observation.Errors.Count);
        Assert.All(observation.Errors, error => Assert.StartsWith($"{nameof(KatLangErrorCode.SelfDependentInferredParameters)}: ", error, StringComparison.Ordinal));
        return observation;
    }

    // ── the reviewed completions, with their values ─────────────────────────────────────────────

    [Fact]
    public async Task EffectfulSelfRecursion_CompletesAsItsWrittenForm()
    {
        const string Source = "F = if(tick() > 3, x, F + 1)\nF(10)";
        Assert.Equal("F(x)", Signature(Source, "F"));
        await AssertValue(Source, "13");
        await AssertValue("F(x) = if(tick() > 3, x, F(x) + 1)\nF(10)", "13");
    }

    [Fact]
    public async Task MutualRecursion_CompletesInEveryDeclarationOrder()
    {
        foreach (var declared in Permutations(["A = if(tick() > 3, x, B + 1)", "B = A + 1"]))
        {
            var source = Program(declared, "A(10)");
            Assert.Equal("A(x)", Signature(source, "A"));
            Assert.Equal("B(x)", Signature(source, "B"));
            await AssertValue(source, "16");
        }
    }

    [Fact]
    public async Task ThreeWayRecursion_CompletesInEveryDeclarationOrder()
    {
        foreach (var declared in Permutations(["A = if(tick() > 4, x, B + 1)", "B = C + 1", "C = A + 1"]))
            await AssertValue(Program(declared, "A(10)"), "22");
    }

    [Fact]
    public async Task PureMixedRecursion_Completes()
    {
        foreach (var declared in Permutations(["A = if(x <= 0, 0, B)", "B = if(x <= 0, A, A(x - 1)) + 1"]))
            await AssertValue(Program(declared, "A(3)"), "3");
    }

    /// <summary>
    /// Written reference order stays meaningful: each member lists its own names first. <c>A(1, 2, 3)</c> is
    /// (1 + 2) + (1 + 3 × 4 tick steps): the value proves the slots, not only the display.
    /// </summary>
    [Fact]
    public async Task EachMemberListsItsOwnNamesFirst()
    {
        foreach (var declared in Permutations(["A = if(tick() > 3, x + y, B + 1)", "B = A + z"]))
        {
            var source = Program(declared, "A(1, 2, 3)");
            Assert.Equal("A(x, y, z)", Signature(source, "A"));
            Assert.Equal("B(z, x, y)", Signature(source, "B"));
            await AssertValue(source, "15");
            await AssertValue(Program(declared, "B(1, 2, 3)"), "12");
        }
    }

    // ── the reached state is authoritative ──────────────────────────────────────────────────────

    /// <summary>
    /// The schedule's choice: both <c>F(e, p)</c> and <c>F(p, e)</c> are consistent completions, the rounds reach the first,
    /// and that is the answer, not an ambiguity. The written alternative stays available and gives its own value.
    /// </summary>
    [Fact]
    public async Task SeveralFixedPoints_TheReachedOneIsTheAnswer()
    {
        foreach (var declared in Permutations(["E(e) = e * 10", "F = if(tick() > 2, 0, F + G + E)", "G = p + F + 0"]))
        {
            var source = Program(declared, "F(1, 2)");
            Assert.Equal("F(e, p)", Signature(source, "F"));
            await AssertValue(source, "24");
        }

        await AssertValue("E(e) = e * 10\nF(e, p) = if(tick() > 2, 0, F + G + E)\nG = p + F + 0\nF(1, 2)", "24");
        await AssertValue("E(e) = e * 10\nF(p, e) = if(tick() > 2, 0, F + G + E)\nG = p + F + 0\nF(1, 2)", "42");
    }

    /// <summary>The parameter <c>E</c> itself is inferred when no declaration exists (research: the brief's first printing).</summary>
    [Fact]
    public async Task WithoutTheDeclaration_TheCalleeIsItselfAParameter()
        => await AssertValue("F = if(tick() > 2, 0, F + G + E)\nG = p + F + 0\nF(1, 2)", "6");

    // ── non-settling, precisely ─────────────────────────────────────────────────────────────────

    [Fact]
    public async Task AFullPatternOscillator_IsRefusedAsNonSettling_InEveryOrder()
    {
        foreach (var declared in Permutations(["X(x) = x", "Y(y) = y", "A = B + X", "B = A + Y"]))
        {
            var refused = await Refused(Program(declared, "A(1, 2)"), errors: 2);
            Assert.All(refused.Errors, error =>
            {
                Assert.Contains("recursive inference does not settle", error, StringComparison.Ordinal);
                Assert.Contains("use one another by name in formulas", error, StringComparison.Ordinal);
            });
        }
    }

    /// <summary>A reader of a group that does not settle is not reported again.</summary>
    [Fact]
    public async Task AReaderOfANonSettlingGroup_IsNotReportedAgain()
        => await Refused("X(x) = x\nY(y) = y\nA = B + X\nB = A + Y\nC = A + 0\n0", errors: 2);

    /// <summary>
    /// Names and arity repeat here while the ORDER changes, so a names-only or arity-only stabilization would accept what
    /// the full ordered state refuses.
    /// </summary>
    [Fact]
    public void TheState_IsOrdered_NotANameSet()
    {
        var diagnostics = Parser.Parse("X(x) = x\nY(y) = y\nA = B + X\nB = A + Y\n0").Diagnostics;
        Assert.Contains(diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.SelfDependentInferredParameters);
    }

    /// <summary>
    /// Same names, order and arity, another KIND: <c>Q</c>'s collector reaches <c>A</c> first, and the plain <c>p</c> of
    /// <c>P</c> is filtered by the merge. A kind-blind state would stop a round early with the plain capture.
    /// </summary>
    [Fact]
    public void TheState_SeesKinds()
    {
        const string Source = "P(p) = p\nQ(q, *p) = q\nM = Q + 0\nA = if(tick() > 2, 0, M + B + P)\nB = A + 0\n0";
        Assert.Equal("A(q, *p)", Signature(Source, "A"));
        Assert.Equal("B(q, *p)", Signature(Source, "B"));
    }

    /// <summary>A structural group keeps its shape around a cycle; the state compares grouping, not only captures.</summary>
    [Fact]
    public void AStructuralGroup_KeepsItsShapeAroundACycle()
    {
        const string Source = "P((p, q)) = p + q\nA = if(tick() > 2, 0, B + P)\nB = A + 0\n0";
        Assert.Equal("A((p, q))", Signature(Source, "A"));
        Assert.Equal("B((p, q))", Signature(Source, "B"));
    }

    /// <summary>
    /// A group loses a name to an earlier provider and regains it a round later, so the two members exchange <c>(p, q)</c>
    /// and <c>p, q</c> for ever. The names never change: only grouping does, and it is part of the state.
    /// </summary>
    [Fact]
    public void GroupingAlone_CanFailToSettle()
    {
        var errors = Parser.Parse("P((p, q)) = p\nQ(p) = p\nA = B + P\nB = A + Q\n0").Diagnostics;
        Assert.Equal(2, errors.Count);
        Assert.All(errors, error => Assert.Contains("recursive inference does not settle", error.Message, StringComparison.Ordinal));
    }

    /// <summary>A META callee lifts as an ordinary capture around a cycle, exactly as it does off one.</summary>
    [Fact]
    public void AMetaCallee_LiftsAsAPlainCapture()
    {
        const string Source = "P(meta p) = 1\nA = if(tick() > 2, 0, B + P)\nB = A + 0\n0";
        Assert.Equal("A(p)", Signature(Source, "A"));
        Assert.Equal("B(p)", Signature(Source, "B"));
    }

    /// <summary>Q-04: a name an enclosing binding supplies is never lifted, around a cycle as anywhere.</summary>
    [Fact]
    public void AnEnclosingBinding_FiltersACycle()
    {
        const string Source = "P(p, s) = p + s\nOuter(s) = {\n    A = if(tick() > 2, 0, B + P)\n    B = A + 0\n    A\n}\n0";
        var model = SemanticModelBuilder.Build(Parser.Parse(Source));
        Assert.Equal("A(p)", Assert.Single(model.FindProperties("A")).DisplaySignature);
    }

    /// <summary>
    /// X-02 keeps holding a completed member to the rules of a written signature, at the member whose own composition breaks
    /// them, whatever the rounds do around it: the violation is reported as the collector rule, never as a recursion refusal.
    /// </summary>
    [Fact]
    public void AnX02ViolationInACycle_IsReportedAsTheCollectorRule()
    {
        var diagnostics = Parser.Parse("C1(a, *p) = a\nC2(b, *q) = b\nA = if(tick() > 2, 0, C1 + C2 + B)\nB = A + 0\n0").Diagnostics;
        Assert.Contains(diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.InvalidCollectingBinding);
        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.SelfDependentInferredParameters);
    }

    /// <summary>
    /// The X-02 flag belongs to the state but a violation of an intermediate round is no refusal: reading <c>B</c> FIRST
    /// gives <c>A</c> the recovered list, whose later collector is plain, and <c>C2</c>'s <c>*q</c> then adds nothing. The
    /// settled state has no violation, so the program is accepted with the signature the rounds reached.
    /// </summary>
    [Fact]
    public void AnIntermediateX02Violation_IsNoRefusal()
    {
        const string Source = "C1(a, *p) = a\nC2(b, *q) = b\nA = if(tick() > 2, 0, B + C1 + C2)\nB = A + 0\n0";
        Assert.Empty(Parser.Parse(Source).Diagnostics);
        Assert.Equal("A(a, *p, b, q)", Signature(Source, "A"));
    }

    /// <summary>A lone collector accepts zero arguments: a nonempty signature is not a signature that requires arguments.</summary>
    [Fact]
    public async Task ALoneCollector_IsNotALiftingRead()
    {
        // F's closed fact is `*xs`, which accepts zero arguments, so its self read lifts nothing: a non-lifting cycle.
        const string Source = "Sum(*xs) = 7\nF = if(tick() > 2, 1, F + Sum)\nF";
        Assert.Equal("F", Signature(Source, "F"));
        await AssertValue(Source, "15");
    }

    /// <summary>
    /// Completing a signature evaluates nothing, so a completion can still fail when used: a cycle through a member path
    /// completes, and reading the local member from outside fails at run time.
    /// </summary>
    [Fact]
    public async Task ACompletion_CanStillFailWhenUsed()
    {
        const string X = "X = p + Outer.Y + 0";
        const string Outer = "Outer(p) = {\n    Y = X + 0\n    Y\n}";
        foreach (var declared in Permutations([X, Outer]))
        {
            var observation = await SixRouteAgreement.OnEveryRouteAsync(Program(declared, "Outer(5)"));
            Assert.True(observation.Kind == "err", observation.ToString());
            Assert.StartsWith($"{nameof(KatLangErrorCode.LocalOnlyProperty)}: ", observation.Errors[0], StringComparison.Ordinal);
        }
    }

    /// <summary>
    /// The repair for a C2-type program decides the links: with written lists on the bodies they read, one reading is left.
    /// Writing <c>N</c>'s own list would not help, since both readings of the links stay grounded.
    /// </summary>
    [Fact]
    public void C2_IsRepairedByWrittenLists()
    {
        var repaired = C2.Replace("    K = L2.repeat(Cq) + P", "    K(p) = L2.repeat(Cq) + P", StringComparison.Ordinal)
            .Replace("    M = L1.repeat(Cq) + P", "    M(p) = L1.repeat(Cq) + P", StringComparison.Ordinal);
        Assert.NotEqual(C2, repaired);
        var parsed = Parser.Parse(repaired);
        Assert.False(parsed.HasErrors, string.Join("; ", parsed.Diagnostics.Select(static diagnostic => diagnostic.Message)));

        var unhelped = Parser.Parse(C2.Replace("    N = o + L2.repeat(N)", "    N(o) = o + L2.repeat(N)", StringComparison.Ordinal));
        Assert.Contains(unhelped.Diagnostics, static diagnostic => diagnostic.Message.Contains("can be read in more than one consistent way", StringComparison.Ordinal));
    }

    // ── what recursive inference leaves untouched ───────────────────────────────────────────────

    [Fact]
    public async Task ExplicitRecursion_AndNonLiftingSelfReads_AreUnchanged()
    {
        await AssertValue("Fact = if(n <= 1, 1, n * Fact(n - 1))\nFact(5)", "120");
        await AssertValue("A = if(tick() < 3, A + 1, 0)\nA", "2");
        await AssertValue("F = if(tick() > 3, x, F(x) + 1)\nF(10)", "13");
    }

    /// <summary>A written list is final: a read of a member with a written list is a fixed signature, never completed.</summary>
    [Fact]
    public void AWrittenList_IsAuthoritative()
    {
        const string Source = "A(y) = if(tick() > 2, y, B + 1)\nB = A + q\n0";
        Assert.Equal("A(y)", Signature(Source, "A"));
        Assert.Equal("B(q, y)", Signature(Source, "B"));
    }

    // ── classification ──────────────────────────────────────────────────────────────────────────

    private const string CG4 = """
        Cap(meta op) = op
        Id(v) = v
        C(a, *p) = a
        A0 = C + 0
        B(p) = p
        Outer(a) = {
            L1 = Cap(Id(H1 + 0)).Algorithm
            H1 = L1.abs.repeat(A0) + B
            0
        }
        0
        """;

    /// <summary>CG4 stays the reviewed contradiction, in both orders of the pair; no coinductive reading is added.</summary>
    [Fact]
    public void CG4_IsAContradiction_InBothOrders()
    {
        var swapped = CG4.Replace("    L1 = Cap(Id(H1 + 0)).Algorithm\n    H1 = L1.abs.repeat(A0) + B", "    H1 = L1.abs.repeat(A0) + B\n    L1 = Cap(Id(H1 + 0)).Algorithm", StringComparison.Ordinal);
        Assert.NotEqual(CG4, swapped);
        foreach (var source in new[] { CG4, swapped })
        {
            var errors = Parser.Parse(source).Diagnostics.Where(static diagnostic => diagnostic.Code == DiagnosticCode.SelfDependentInferredParameters).ToArray();
            Assert.NotEmpty(errors);
            Assert.All(errors, error => Assert.Contains("no consistent reading", error.Message, StringComparison.Ordinal));
        }
    }

    internal const string C2 = """
        Cap(meta op) = op
        Id(v) = v
        Cq(q, *p) = q
        P(p) = p
        Outer(q) = {
            L1 = Cap(Id(K + 0)).Algorithm
            L2 = Cap(Id(M + 0)).Algorithm
            K = L2.repeat(Cq) + P
            M = L1.repeat(Cq) + P
            N = o + L2.repeat(N)
            0
        }
        0
        """;

    /// <summary>
    /// THE DELIBERATE COMPATIBILITY CHANGE. Under the former rule <c>N</c>'s cycle had no meaning in one reading of the
    /// links, which left exactly one grounded reading, so this program was accepted. <c>N</c> now completes, both readings
    /// are grounded, and rule G6 reports the ambiguity.
    /// </summary>
    [Fact]
    public void C2_IsAmbiguousUnderRecursiveInference()
    {
        var errors = Parser.Parse(C2).Diagnostics.Where(static diagnostic => diagnostic.Code == DiagnosticCode.SelfDependentInferredParameters).ToArray();
        Assert.NotEmpty(errors);
        Assert.All(errors, error => Assert.Contains("can be read in more than one consistent way", error.Message, StringComparison.Ordinal));
    }
}
