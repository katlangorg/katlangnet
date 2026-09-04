using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// The front end diagnoses a strict value demand it can already prove impossible.
///
/// <para>Three independent guarantees meet here and must not be confused. B2a decides that a
/// bare parameterized reference inside a CLOSED explicit parameter list may not lift, and
/// never invents the parameter it would need. The evaluator, reached with such a tree,
/// demands the bound argument's value and fails honestly rather than capturing an ambient
/// caller value (<see cref="AlgorithmChannelParameterShadowingTests"/>,
/// <see cref="NativeArgumentValueDemandTests"/>). THIS layer sits in front of both: when the
/// refused forwarding was demanded by a registry-proven value-demanding consumer, the outcome
/// is already determined, so the front end says so instead of shipping a program that can
/// only fail.</para>
///
/// <para>The rule is deliberately narrow — it fires only where all of the following are
/// statically known: the consumer's argument position is registry-proven strict-value, the
/// reference resolves to a callable with implicit parameters, and the enclosing closed
/// explicit list cannot supply them. Anything less is left to run
/// (<see cref="NotDiagnosed"/>).</para>
/// </summary>
public class ClosedListStrictValueDiagnosticTests
{
    private const string MessageMarker = "is required as a value here";

    private static IReadOnlyList<Diagnostic> BlockedDiagnostics(string source)
        => Parser.Parse(source).Diagnostics
            .Where(d => d.Severity == DiagnosticSeverity.Error
                && d.Code == DiagnosticCode.UndeclaredIdentifier
                && d.Message.Contains(MessageMarker, StringComparison.Ordinal))
            .ToList();

    private static Diagnostic SingleBlocked(string source)
    {
        var parsed = Parser.Parse(source);
        var blocked = BlockedDiagnostics(source);
        Assert.True(
            blocked.Count == 1,
            $"Expected exactly one closed-list strict-value diagnostic, found {blocked.Count}."
            + Environment.NewLine + source
            + Environment.NewLine + "All diagnostics:" + Environment.NewLine
            + string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => "  - " + d.Message.Split('\n')[0])));
        return blocked[0];
    }

    private static void AssertNotDiagnosed(string source)
    {
        var blocked = BlockedDiagnostics(source);
        Assert.True(
            blocked.Count == 0,
            $"This source must NOT be diagnosed by the closed-list strict-value rule, but was:"
            + Environment.NewLine + source + Environment.NewLine
            + string.Join(Environment.NewLine, blocked.Select(d => "  - " + d.Message.Split('\n')[0])));
    }

    // ── The rule fires, and names what the programmer can act on ─────────────

    /// <summary>
    /// The motivating program. `Math.Abs` needs `A`'s value; producing it needs `A`'s
    /// inferred `q`; `F(x)` is closed and declares no `q`.
    /// </summary>
    [Fact]
    public void ClosedList_BlockingAStrictValueDemand_IsDiagnosed()
    {
        var diagnostic = SingleBlocked(
            """
            A = q + 1
            F(x) = Math.Abs(A)
            F(7)
            """);

        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Contains("'A'", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("'q'", diagnostic.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// The diagnostic blames the REFERENCE, not the consuming math member and not the
    /// member's own declared argument names. Those names (<c>x</c>, <c>value</c>,
    /// <c>digits</c>, <c>radians</c>) are the consumer's, and naming one here would repeat
    /// exactly the confusion the evaluator-side fix removed.
    /// </summary>
    [Theory]
    [InlineData("A = q + 1\nF(zz) = Math.Abs(A)\nF(7)")]
    [InlineData("A = q + 1\nF(zz) = Math.Round(A, 2)\nF(7)")]
    [InlineData("A = radians + 1\nF(zz) = Math.Sin(A)\nF(7)")]
    public void Diagnostic_NamesTheReference_NotTheConsumersParameters(string source)
    {
        var message = SingleBlocked(source).Message;

        Assert.Contains("'A'", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Math.Abs", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Math.Round", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Math.Sin", message, StringComparison.Ordinal);
        Assert.DoesNotContain("'value'", message, StringComparison.Ordinal);
        Assert.DoesNotContain("'digits'", message, StringComparison.Ordinal);
    }

    /// <summary>The span points at the reference, so an editor underlines `A`.</summary>
    [Fact]
    public void Diagnostic_SpanCoversTheReference()
    {
        const string Source = """
            A = q + 1
            F(x) = Math.Abs(A)
            F(7)
            """;
        var span = SingleBlocked(Source).Span;

        var line = Source.ReplaceLineEndings("\n").Split('\n')[span.StartLineNumber - 1];
        Assert.Equal("F(x) = Math.Abs(A)", line);
        Assert.Equal("A", line.Substring(span.StartColumn - 1, 1));
        Assert.Equal(span.StartLineNumber, span.EndLineNumber);
        Assert.Equal(span.StartColumn, span.EndColumn);
    }

    // ── Spelling parity: the rule reads metadata, never the written name ─────

    [Theory]
    // Canonical dot spelling, prelude alias, and an aliased two-argument member.
    [InlineData("A = q + 1\nF(x) = Math.Abs(A)\nF(7)")]
    [InlineData("A = q + 1\nF(x) = abs(A)\nF(7)")]
    [InlineData("A = q + 1\nF(x) = pow(A, 2)\nF(7)")]
    // Both argument positions of a multi-argument member are strict-value.
    [InlineData("A = q + 1\nF(x) = Math.Pow(A, 2)\nF(7)")]
    [InlineData("A = q + 1\nF(x) = Math.Pow(2, A)\nF(7)")]
    // A value position INSIDE the strict argument is demanded just as much.
    [InlineData("A = q + 1\nF(x) = Math.Abs(A + 1)\nF(7)")]
    [InlineData("A = q + 1\nF(x) = Math.Abs(0 - A)\nF(7)")]
    public void EverySpellingOfTheSameDemand_IsDiagnosedOnce(string source)
        => Assert.Contains("'q'", SingleBlocked(source).Message, StringComparison.Ordinal);

    /// <summary>
    /// The other two gated lift sites — a bare prelude alias and a bare canonical
    /// <c>Math.X</c> — are diagnosed the same way when they sit in a strict-value position.
    /// Here the missing name IS a math member's declared parameter, and naming it is correct:
    /// it is that member's own public signature, and declaring it is exactly the fix
    /// (<see cref="BareMathReference_WithTheRequiredNameDeclared_IsLegal"/>).
    /// </summary>
    [Theory]
    [InlineData("F(zz) = Math.Abs(abs)\nF(0 - 5)", "'abs'")]
    [InlineData("F(zz) = Math.Abs(Math.Abs)\nF(0 - 5)", "'Math.Abs'")]
    public void BareMathReferenceInStrictPosition_IsDiagnosed(string source, string expectedSubject)
    {
        var message = SingleBlocked(source).Message;
        Assert.Contains(expectedSubject, message, StringComparison.Ordinal);
        Assert.Contains("'x'", message, StringComparison.Ordinal);
    }

    [Fact]
    public void BareMathReference_WithTheRequiredNameDeclared_IsLegal()
    {
        AssertNotDiagnosed("F(x) = Math.Abs(abs)\nF(0 - 5)");
        AssertEval("F(x) = Math.Abs(abs)\nF(0 - 5)", 5);
    }

    // ── Missing-name reporting ───────────────────────────────────────────────

    /// <summary>
    /// Several missing parameters are reported together, in the referenced callable's own
    /// declaration order — never a hash order.
    /// </summary>
    [Fact]
    public void MultipleMissingParameters_AreAllNamedInDeclarationOrder()
    {
        var message = SingleBlocked(
            """
            A = p + q
            F(x) = Math.Abs(A)
            F(7)
            """).Message;

        Assert.Contains("implicit parameters 'p' and 'q'", message, StringComparison.Ordinal);
    }

    /// <summary>
    /// Partial availability: the diagnostic must blame what is still missing, not reject
    /// because SOME requirement happens to be declared.
    /// </summary>
    [Fact]
    public void PartiallyAvailableParameters_NameOnlyTheMissingOnes()
    {
        var message = SingleBlocked(
            """
            A = p + q
            F(p) = Math.Abs(A)
            F(7)
            """).Message;

        Assert.Contains("implicit parameter 'q'", message, StringComparison.Ordinal);
        Assert.DoesNotContain("'p'", message, StringComparison.Ordinal);
    }

    [Fact]
    public void ForwardingBindingKinds_UseTheResolverGateRatherThanNameOnlyHeuristics()
    {
        // fixed caller -> fixed destination
        AssertNotDiagnosed("Target(q) = q + 1\nF(q) = Math.Abs(Target)\nF(7)");
        // fixed caller -> collecting destination: one fixed value is forwarded unspread.
        AssertNotDiagnosed("Target(*items) = items.sum\nF(items) = Math.Abs(Target)\nF(7)");
        // collecting caller -> fixed destination: the collected list remains one value.
        AssertNotDiagnosed("Target(items) = items.sum\nF(*items) = Math.Abs(Target)\nF(1, 2)");
        // collecting caller -> collecting destination: the caller's stream is forwarded by
        // binding kind, even when the capture names differ.
        AssertNotDiagnosed("Target(*xs) = xs.sum\nF(*items) = Math.Abs(Target)\nF(1, 2)");

        AssertEval("Target(q) = q + 1\nF(q) = Math.Abs(Target)\nF(7)", 8);
        AssertEval("Target(*items) = items.sum\nF(items) = Math.Abs(Target)\nF(7)", 7);
        AssertEval("Target(items) = items.sum\nF(*items) = Math.Abs(Target)\nF(1, 2)", 3);
        AssertEval("Target(*xs) = xs.sum\nF(*items) = Math.Abs(Target)\nF(1, 2)", 3);

        // A differently named fixed source cannot satisfy a collecting destination, and a
        // collecting source cannot be re-spread into a differently named fixed destination.
        Assert.Contains("'xs'", SingleBlocked(
            "Target(*xs) = xs.sum\nF(items) = Math.Abs(Target)\nF(7)").Message,
            StringComparison.Ordinal);
        Assert.Contains("'xs'", SingleBlocked(
            "Target(xs) = xs.sum\nF(*items) = Math.Abs(Target)\nF(1, 2)").Message,
            StringComparison.Ordinal);
    }

    /// <summary>
    /// ONE written occurrence yields ONE diagnostic however many strict consumers enclose
    /// it: the innermost value-demanding bundle owns the refusal, and the enclosing ones see
    /// an argument that has already been through the walk.
    /// </summary>
    [Theory]
    [InlineData("A = q + 1\nF(x) = Math.Abs(Math.Abs(A))\nF(7)")]
    [InlineData("A = q + 1\nF(x) = Math.Abs(Math.Abs(Math.Abs(A)))\nF(7)")]
    [InlineData("A = q + 1\nF(x) = Math.Abs(Math.Pow(A, 2))\nF(7)")]
    public void NestedStrictConsumers_ReportOncePerWrittenOccurrence(string source)
        => SingleBlocked(source);

    /// <summary>
    /// Two SEPARATE written occurrences are two separate places to fix, so both are
    /// reported — with distinct spans. Deduplicating them would hide one of them.
    /// </summary>
    [Fact]
    public void SeparateOccurrences_AreReportedSeparately()
    {
        var blocked = BlockedDiagnostics(
            """
            A = q + 1
            F(x) = Math.Pow(Math.Abs(A), Math.Abs(A))
            F(7)
            """);

        Assert.Equal(2, blocked.Count);
        Assert.Equal(2, blocked.Select(d => d.Span.StartColumn).Distinct().Count());
    }

    // ── Not diagnosed: everything the rule cannot prove ──────────────────────

    /// <summary>
    /// The controls that keep this refinement from becoming a general "parameterized
    /// reference" ban. Each of these either evaluates successfully or fails only at runtime,
    /// and in both cases the front end must stay quiet.
    /// </summary>
    public static TheoryData<string, string> NotDiagnosed() => new()
    {
        // Required parameter explicitly declared: ordinary legal forwarding.
        { "explicit name present", "A = q + 1\nF(q) = Math.Abs(A)\nF(7)" },
        // Open parameter list: ordinary legal inference.
        { "implicit caller", "A = q + 1\nF = Math.Abs(A)\nF(7)" },
        // Every requirement declared, several at once.
        { "all names present", "A = p + q\nF(p, q) = Math.Abs(A)\nF(3, 4)" },
        // A bare reference is not a value demand (deliberately out of scope).
        { "bare reference row", "A = q + 1\nF(x) = A\nF(7)" },
        // An ordinary call's arguments stay higher-order; no strictness is inferred for
        // arbitrary user callees.
        { "arbitrary user call", "A = q + 1\nG(x) = x + 1\nF(x) = G(A)\nF(7)" },
        { "higher-order argument", "A = q + 1\nApply(f) = f(10)\nF(x) = Apply(A)\nF(7)" },
        // Callback positions: a callable argument is not an immediate value demand.
        { "alias callback", "F(x) = [0 - 1, 0 - 2].map(abs).sum\nF(9)" },
        { "canonical callback", "F(x) = [0 - 1, 0 - 2].map(Math.Abs).sum\nF(9)" },
        { "predicate callback", "P(n) = n > 1\nF(x) = [1, 2, 3].filter(P).count\nF(9)" },
        // Non-value-demanding builtins keep their runtime behavior: only registry-proven
        // strict-value metadata drives this rule.
        { "strict builtin without metadata", "A = q + 1\nF(x) = sum(A)\nF(7)" },
        // No closed list at all.
        { "root position", "A = q + 1\nMath.Abs(A)" },
    };

    [Theory]
    [MemberData(nameof(NotDiagnosed))]
    public void ProgramsTheRuleCannotProve_AreLeftToRuntime(string description, string source)
    {
        _ = description;
        AssertNotDiagnosed(source);
    }

    /// <summary>
    /// Positions the resolver never lifts in ANY caller are OUT of scope: they are not
    /// blocked by the closed list, so the closed list is not what to blame. Both spellings
    /// fail identically with an open list and with the required name declared, which is the
    /// evidence that they are a different (caller-independent) matter and belong to the
    /// runtime.
    /// </summary>
    [Theory]
    [InlineData("A = q + 1\nF(CALLER) = Math.Abs((A))\nF(7)")]
    [InlineData("A = q + 1\nF(CALLER) = Id(Math.Abs(A))\nId(v) = v\nF(7)")]
    public void PositionsThatNeverLift_AreNotAttributedToTheClosedList(string template)
    {
        foreach (var caller in new[] { "x", "q" })
            AssertNotDiagnosed(template.Replace("CALLER", caller, StringComparison.Ordinal));

        // ... and with no explicit list at all the reference is not lifted either, so the
        // caller's interface was never the reason.
        AssertNotDiagnosed(template.Replace("F(CALLER)", "F", StringComparison.Ordinal));
    }

    /// <summary>
    /// A dot-call RECEIVER is resolved in algorithm position, so it is not a lifting site in
    /// any caller either — `A.abs` fails the same way with `F(x)` and with `F(q)`.
    /// </summary>
    [Fact]
    public void DotCallReceiver_IsNotAttributedToTheClosedList()
    {
        AssertNotDiagnosed("A = q + 1\nF(x) = A.abs\nF(7)");
        AssertNotDiagnosed("A = q + 1\nF(q) = A.abs\nF(7)");
    }

    // ── The rewrite the diagnostic sits on top of ────────────────────────────

    /// <summary>
    /// The diagnostic must never be a cover for a bad rewrite: on refusing to lift, the
    /// resolver still leaves the reference bare and synthesizes no parameter. This is the
    /// B2a invariant, re-asserted from the rejected tree.
    /// </summary>
    [Fact]
    public void RejectedProgram_StillCarriesTheSafeUnliftedTree()
    {
        // Rejected source IS the subject: the tree behind the rejection is what is asserted.
        var root = SourceProvenance.ParseAllowingDiagnostics(
            """
            A = q + 1
            F(x) = Math.Abs(A)
            F(7)
            """).Root;

        var f = root.Properties.Single(p => p.Name == "F").Value;
        Assert.Equal(["x"], f.Params);
        Assert.DoesNotContain("q", f.Params);

        var dotCall = Assert.IsType<Expr.DotCall>(Assert.Single(f.Output));
        var argument = Assert.Single(dotCall.Args!);
        var resolve = Assert.IsType<Expr.Resolve>(argument);
        Assert.Equal("A", resolve.Name);

        // No synthesized parameter reference anywhere inside F.
        Assert.Empty(ParamNames(f));
    }

    private sealed class ParamCollector : AstWalker
    {
        public readonly List<string> Names = [];

        protected override void VisitParameterIdentifier(Expr.Param expr) => Names.Add(expr.Name);
    }

    private static IReadOnlyList<string> ParamNames(Algorithm algorithm)
    {
        var collector = new ParamCollector();
        collector.VisitAlgorithm(algorithm);
        return collector.Names;
    }

    /// <summary>
    /// The refinement only moves an inevitable failure earlier: EVERY source it rejects must
    /// also fail when the elaborated tree is evaluated directly, as a host bypassing
    /// front-end checking would. A diagnosed program that would in fact have run is a false
    /// positive, and this is the systematic guard against one.
    /// </summary>
    public static TheoryData<string, KatLangErrorCode> DiagnosedExecutableSources() => new()
    {
        { "A = q + 1\nF(x) = Math.Abs(A)\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = q + 1\nF(zz) = Math.Abs(A)\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = q + 1\nF(x) = abs(A)\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = q + 1\nF(x) = Math.Pow(A, 2)\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = q + 1\nF(x) = Math.Pow(2, A)\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = q + 1\nF(x) = Math.Abs(A + 1)\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = q + 1\nF(x) = Math.Abs(Math.Abs(A))\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = q + 1\nF(x) = Math.Abs(A*)\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = q + 1\nF(x) = Math.Abs(A:0)\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = q + 1\nF(x) = Math.Abs(~A)\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = q + 1\nF(x) = {Math.Abs(A)}\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = p + q\nF(x) = Math.Abs(A)\nF(7)", KatLangErrorCode.ArityMismatch },
        { "A = p + q\nF(p) = Math.Abs(A)\nF(7)", KatLangErrorCode.ArityMismatch },
        { "F(zz) = Math.Abs(abs)\nF(0 - 5)", KatLangErrorCode.ArityMismatch },
        { "F(zz) = Math.Abs(Math.Abs)\nF(0 - 5)", KatLangErrorCode.ArityMismatch },
    };

    [Theory]
    [MemberData(nameof(DiagnosedExecutableSources))]
    public void EveryExecutedDiagnosedSource_FailsWithTheExpectedCodeWhenCheckingIsBypassed(
        string source,
        KatLangErrorCode expectedCode)
    {
        Assert.NotEmpty(BlockedDiagnostics(source));

        // Rejected source IS the subject here: state that at the call site rather than
        // demanding a clean front end (SourceProvenanceEnforcementTests).
        var root = SourceProvenance.ParseAllowingDiagnostics(source).Root;
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));

        if (!result.IsError)
        {
            Assert.Fail(
                "A rejected source evaluated successfully, so the diagnostic is a false positive:"
                + Environment.NewLine + source + Environment.NewLine + result.Value);
        }

        Assert.Equal(expectedCode, KatLangError.FromEvalError(result.Error).Code);
    }

    [Fact]
    public void UncalledInvalidClosedInterface_IsDiagnosedReachabilityIndependently()
    {
        const string Source = "A = q + 1\nF(x) = Math.Abs(A)\n1";
        Assert.NotEmpty(BlockedDiagnostics(Source));

        // Like a directly written undeclared name in F's closed interface, this is a static
        // well-formedness error even though evaluating another root row never calls F.
        var root = SourceProvenance.ParseAllowingDiagnostics(Source).Root;
        var bypassed = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.True(bypassed.IsOk);
    }

    /// <summary>
    /// Mirror of the above for the callers the rule must NOT reject: each of these keeps its
    /// established outcome, and the ones that are supposed to compute a value still do.
    /// </summary>
    [Theory]
    [InlineData("A = q + 1\nF(q) = Math.Abs(A)\nF(7)", 8)]
    [InlineData("A = q + 1\nF = Math.Abs(A)\nF(7)", 8)]
    [InlineData("A = p + q\nF(p, q) = Math.Abs(A)\nF(3, 4)", 7)]
    [InlineData("A = q + 1\nF(q) = Math.Pow(A, 2)\nF(7)", 64)]
    [InlineData("A = q + 1\nF(q) = {Math.Abs(A)}\nF(7)", 8)]
    [InlineData("A = q + 1\nApply(f) = f(10)\nF(x) = Apply(A)\nF(7)", 11)]
    [InlineData("F(x) = [0 - 1, 0 - 2].map(abs).sum\nF(9)", 3)]
    public void LegalPrograms_KeepEvaluating(string source, int expected)
    {
        AssertNotDiagnosed(source);
        AssertEval(source, expected);
    }

    // ── Memo / caller-context separation ─────────────────────────────────────

    /// <summary>
    /// The rewrite memo is keyed by node and call position within one caller context, and the
    /// strict-value flag is deliberately NOT a key (it changes no rewrite). This pins that
    /// legal and illegal callers still cannot contaminate each other in either declaration
    /// order: the open-list property keeps its lift and stays undiagnosed, and the closed-list
    /// property is diagnosed exactly once.
    /// </summary>
    [Theory]
    [InlineData("Helper(n) = n + 1\nOpenList = Math.Abs(Helper)\nClosedList(other) = Math.Abs(Helper)")]
    [InlineData("Helper(n) = n + 1\nClosedList(other) = Math.Abs(Helper)\nOpenList = Math.Abs(Helper)")]
    public void LegalAndIllegalCallers_DoNotContaminateEachOther(string source)
    {
        var diagnostic = SingleBlocked(source);
        Assert.Contains("'Helper'", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("'n'", diagnostic.Message, StringComparison.Ordinal);

        // Rejected source IS the subject here: state that at the call site rather than
        // demanding a clean front end (SourceProvenanceEnforcementTests).
        var root = SourceProvenance.ParseAllowingDiagnostics(source).Root;

        // The legal caller still lifted, and gained the inferred parameter.
        var openList = root.Properties.Single(p => p.Name == "OpenList").Value;
        Assert.Equal(["n"], openList.Params);
        Assert.IsType<Expr.Call>(Assert.Single(Assert.IsType<Expr.DotCall>(Assert.Single(openList.Output)).Args!));

        // The illegal caller kept its own list and its bare reference.
        var closedList = root.Properties.Single(p => p.Name == "ClosedList").Value;
        Assert.Equal(["other"], closedList.Params);
        Assert.IsType<Expr.Resolve>(Assert.Single(Assert.IsType<Expr.DotCall>(Assert.Single(closedList.Output)).Args!));
    }

    /// <summary>
    /// Three callers of the SAME shape in one program — open, explicit-with-the-name, and
    /// explicit-without — produce exactly one diagnostic, for the third.
    /// </summary>
    [Fact]
    public void ThreeCallerContexts_ProduceExactlyOneDiagnostic()
    {
        var diagnostic = SingleBlocked(
            """
            A = q + 1
            Open = Math.Abs(A)
            Declared(q) = Math.Abs(A)
            Blocked(x) = Math.Abs(A)
            Open(1) + Declared(2) + Blocked(3)
            """);

        Assert.Contains("'q'", diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(4, diagnostic.Span.StartLineNumber);
    }

    // ── Host-built shared nodes ──────────────────────────────────────────────

    /// <summary>
    /// A host may hand the resolver a SHARED <see cref="Expr.Resolve"/> node reached twice in
    /// ONE algorithm's output — once as an ordinary row (a legal higher-order reference) and
    /// once inside a strict-value argument. The rewrite memo is keyed by node and call
    /// position, so whichever reach happens first serves the other. Strict diagnostic
    /// observation is tracked independently because it changes no rewrite but still must run
    /// once when a shared node is first reached strictly.
    ///
    /// <para>Both reaches leave the reference bare and preserve the input's sharing. The
    /// diagnostic must nevertheless be independent of row order: shared acyclic host ASTs are
    /// supported and resolve like equivalent duplicated trees, including front-end errors.</para>
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void HostSharedNode_ReachedNeutrallyAndStrictly_ReportsIndependentlyOfOrder(
        bool strictRowFirst)
    {
        var sharedReference = new Expr.Resolve("A");
        var strictRow = new Expr.DotCall(new Expr.Resolve("Math"), "Abs", new OutputBundle([sharedReference]));
        Expr neutralRow = sharedReference;

        var parameterized = new Algorithm.User(
            null, Algorithm.NormalParameters(["q"]), [], [], [new Expr.Param("q")]);
        var closedCaller = new Algorithm.User(
            null,
            Algorithm.NormalParameters(["x"]),
            [],
            [],
            strictRowFirst ? [strictRow, neutralRow] : [neutralRow, strictRow])
        {
            ExplicitParameterPatterns = [new CaptureParameterPattern("x")],
        };
        var root = new Algorithm.User(
            null,
            [],
            [],
            [new Property("A", parameterized), new Property("F", closedCaller)],
            []);

        var diagnostics = new List<Diagnostic>();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(root, observations: null, diagnostics);

        Assert.Single(diagnostics);

        // Whatever the order, the rewrite is the safe one in BOTH positions and the sharing
        // survives: no invented call, no invented parameter.
        var f = resolved.Properties.Single(p => p.Name == "F").Value;
        Assert.Equal(["x"], f.Params);
        var rewrittenRows = f.Output.ToList();
        var rewrittenStrictArgument = Assert.Single(
            Assert.IsType<Expr.DotCall>(rewrittenRows[strictRowFirst ? 0 : 1]).Args!);
        var rewrittenNeutralRow = rewrittenRows[strictRowFirst ? 1 : 0];
        Assert.IsType<Expr.Resolve>(rewrittenStrictArgument);
        Assert.IsType<Expr.Resolve>(rewrittenNeutralRow);
        Assert.Same(rewrittenStrictArgument, rewrittenNeutralRow);
    }

    /// <summary>
    /// A neutral memo hit for a shared COMPOSITE must replay strict observation through its
    /// children, not merely inspect a shared reference when that reference is the memo key.
    /// </summary>
    [Fact]
    public void HostSharedComposite_ReachedNeutrallyBeforeStrictly_ReportsItsBlockedChild()
    {
        var sharedReference = new Expr.Resolve("A");
        Expr sharedValue = new Expr.Unary(UnaryOp.Minus, sharedReference);
        var strictRow = new Expr.DotCall(new Expr.Resolve("Math"), "Abs", new OutputBundle([sharedValue]));

        var parameterized = new Algorithm.User(
            null, Algorithm.NormalParameters(["q"]), [], [], [new Expr.Param("q")]);
        var closedCaller = new Algorithm.User(
            null,
            Algorithm.NormalParameters(["x"]),
            [],
            [],
            [sharedValue, strictRow])
        {
            ExplicitParameterPatterns = [new CaptureParameterPattern("x")],
        };
        var root = new Algorithm.User(
            null,
            [],
            [],
            [new Property("A", parameterized), new Property("F", closedCaller)],
            []);

        var diagnostics = new List<Diagnostic>();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(root, observations: null, diagnostics);

        Assert.Single(diagnostics);
        var f = resolved.Properties.Single(p => p.Name == "F").Value;
        var rewrittenRows = f.Output.ToList();
        var rewrittenStrictArgument = Assert.Single(Assert.IsType<Expr.DotCall>(rewrittenRows[1]).Args!);
        Assert.Same(rewrittenRows[0], rewrittenStrictArgument);
        Assert.Same(
            Assert.IsType<Expr.Unary>(rewrittenRows[0]).Operand,
            Assert.IsType<Expr.Unary>(rewrittenStrictArgument).Operand);
    }

    // ── Front-end surface integration ────────────────────────────────────────

    /// <summary>
    /// The diagnostic travels the ordinary front-end channel: the public parse result, the
    /// engine's run entry (which must not evaluate), and the semantic model built over the
    /// same <see cref="ParseResult"/>.
    /// </summary>
    [Fact]
    public void Diagnostic_IsVisibleOnEveryFrontEndSurface()
    {
        const string Source = """
            A = q + 1
            F(x) = Math.Abs(A)
            F(7)
            """;

        var parsed = Parser.Parse(Source);
        Assert.True(parsed.HasErrors);
        Assert.Single(BlockedDiagnostics(Source));

        var run = KatLangEngine.Run(Source);
        var failure = Assert.IsType<RunResult.ParseFailure>(run);
        Assert.Contains(failure.Errors, e => e.Message.Contains(MessageMarker, StringComparison.Ordinal));

        // The semantic model is built over the same ParseResult, so it carries the same
        // diagnostics and still models the (unlifted) tree rather than failing on it.
        Assert.NotNull(KatLang.Semantics.SemanticModelBuilder.Build(parsed));
    }
}
