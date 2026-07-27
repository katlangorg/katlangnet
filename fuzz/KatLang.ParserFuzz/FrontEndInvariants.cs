using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>The stage of the frontend pipeline the harness was executing.</summary>
internal enum FrontEndPhase
{
    RawParse,
    RawInvariants,
    FrontendProcess,
    FrontendTraversal,
    DiagnosticPrefix,
    Determinism,
    WrapperParity,
}

/// <summary>Thrown when a frontend invariant is violated. Escapes the fuzz callback as a
/// recorded crash; the phase is recovered separately by the replay driver.</summary>
internal sealed class FrontEndInvariantException(string message) : Exception(message);

/// <summary>
/// Coverage-guided invariants for the default elaborated frontend
/// (<see cref="FrontEndPipeline.Process(string)"/>, the no-download overload). Every
/// unexpected managed exception escapes so the fuzzing engine records it as a crash.
///
/// Stages:
///   1. raw parse (reference)      — <c>Parser.ParseSyntax</c>
///   2. raw invariants             — existing raw-parser invariants + raw AST spans
///   3. frontend process           — <c>FrontEndPipeline.Process</c> (no downloader)
///   4. frontend traversal         — total, cycle-safe walk + spans + no SequenceConstruct
///   5. diagnostic-prefix          — raw diagnostics are an unchanged prefix of frontend's
///   6. determinism                — same source ⇒ identical structural fingerprint
///   7. public-wrapper parity      — Parser.Parse == Process().ToParseResult() (sampled)
///
/// The frontend passes (load guard, parameter detection, implicit-argument resolution,
/// property exposure, clause-family classification) are exercised through the real
/// pipeline; none of them is reimplemented here.
/// </summary>
internal static class FrontEndInvariants
{
    // Sampling for the expensive extra-parse checks (deterministic per input). Documented
    // in fuzz/README.md.
    private const uint WrapperParitySampleModulus = 8;        // ~1 in 8 inputs
    private const uint InputIndependenceSampleModulus = 32;   // ~1 in 32 inputs

    // A fixed, unrelated program processed *between* two runs of the same source to detect
    // leaked static / cross-parse frontend state. Uses deconstruction (synthetic shared-
    // source properties) + an implicit parameter to stress the most stateful passes.
    private const string ProbeSourceB = "p, q, r = (1, 2, 3)\nHelper(x) = x + p\nOutput = Helper(q) + r";

    /// <summary>Fuzz-callback entry: runs all stages and lets any violation escape.</summary>
    public static void Check(string source)
    {
        var phase = FrontEndPhase.RawParse;
        Run(source, ref phase);
    }

    /// <summary>Runs the stages, advancing <paramref name="phase"/> to the stage in
    /// progress before each one so a thrown exception leaves it pointing at the culprit.</summary>
    public static void Run(string source, ref FrontEndPhase phase)
    {
        var lineWidths = SourceSpanValidator.LineWidths(source);

        phase = FrontEndPhase.RawParse;
        var syntax = Parser.ParseSyntax(source);

        phase = FrontEndPhase.RawInvariants;
        FuzzInvariants.Check(source, syntax);
        new AstSpanWalker(lineWidths, "raw").VisitAlgorithm(syntax.Root);

        phase = FrontEndPhase.FrontendProcess;
        var frontend = FrontEndPipeline.Process(source);

        phase = FrontEndPhase.FrontendTraversal;
        new AstSpanWalker(lineWidths, "frontend").VisitAlgorithm(frontend.ElaboratedRoot);
        CheckDiagnosticSpans(frontend.Diagnostics, lineWidths);

        phase = FrontEndPhase.DiagnosticPrefix;
        CheckDiagnosticPrefix(syntax.Diagnostics, frontend.Diagnostics);

        phase = FrontEndPhase.Determinism;
        var fp1 = FrontEndFingerprint.Compute(frontend.ElaboratedRoot, frontend.Diagnostics, frontend.CanEvaluateAfterLoadErrors);
        var frontendAgain = FrontEndPipeline.Process(source);
        var fp2 = FrontEndFingerprint.Compute(frontendAgain.ElaboratedRoot, frontendAgain.Diagnostics, frontendAgain.CanEvaluateAfterLoadErrors);
        if (!string.Equals(fp1, fp2, StringComparison.Ordinal))
            throw new FrontEndInvariantException("Non-deterministic frontend result across two Process() calls on the same source.");

        // Input independence (sampled): A, B, A — an unrelated program between two runs of
        // the same source must not change the source's result (leaked static state).
        if (StableHash(source) % InputIndependenceSampleModulus == 0)
        {
            _ = FrontEndPipeline.Process(ProbeSourceB);
            var frontendAfterB = FrontEndPipeline.Process(source);
            var fp3 = FrontEndFingerprint.Compute(frontendAfterB.ElaboratedRoot, frontendAfterB.Diagnostics, frontendAfterB.CanEvaluateAfterLoadErrors);
            if (!string.Equals(fp1, fp3, StringComparison.Ordinal))
                throw new FrontEndInvariantException("Frontend result for a source changed after processing an unrelated source (leaked cross-parse state).");
        }

        phase = FrontEndPhase.WrapperParity;
        if (StableHash(source) % WrapperParitySampleModulus == 0)
        {
            var wrapper = Parser.Parse(source);
            var wrapperFp = FrontEndFingerprint.ComputeParseResult(wrapper.Root, wrapper.Diagnostics);
            var frontendParseFp = FrontEndFingerprint.ComputeParseResult(frontend.ElaboratedRoot, frontend.Diagnostics);
            if (!string.Equals(wrapperFp, frontendParseFp, StringComparison.Ordinal))
                throw new FrontEndInvariantException("Parser.Parse(source) differs from FrontEndPipeline.Process(source).ToParseResult().");
        }
    }

    private static void CheckDiagnosticSpans(IReadOnlyList<Diagnostic> diagnostics, int[] lineWidths)
    {
        foreach (var d in diagnostics)
        {
            if (d.Span is null) continue;   // synthetic diagnostics may be spanless
            var reason = SourceSpanValidator.Validate(d.Span, lineWidths);
            if (reason is not null)
                throw new FrontEndInvariantException(
                    $"Invalid frontend diagnostic span [{reason}]: span={SourceSpanValidator.Describe(d.Span)} message='{d.Message}'");
        }
    }

    private static void CheckDiagnosticPrefix(IReadOnlyList<Diagnostic> syntax, IReadOnlyList<Diagnostic> frontend)
    {
        if (frontend.Count < syntax.Count)
            throw new FrontEndInvariantException(
                $"Frontend dropped raw diagnostics: raw has {syntax.Count}, frontend has {frontend.Count}.");

        for (int i = 0; i < syntax.Count; i++)
        {
            var a = syntax[i];
            var b = frontend[i];
            if (a.Severity != b.Severity
                || !string.Equals(a.Message, b.Message, StringComparison.Ordinal)
                || !SpanEquals(a.Span, b.Span))
            {
                throw new FrontEndInvariantException(
                    $"Raw syntax diagnostic #{i} not preserved as a frontend prefix: " +
                    $"raw=[{a.Severity}|{a.Message}|{SourceSpanValidator.Describe(a.Span)}] " +
                    $"frontend=[{b.Severity}|{b.Message}|{SourceSpanValidator.Describe(b.Span)}]");
            }
        }
    }

    private static bool SpanEquals(SourceSpan? a, SourceSpan? b)
    {
        if (a is null || b is null) return a is null && b is null;
        return a.StartLineNumber == b.StartLineNumber && a.StartColumn == b.StartColumn
            && a.EndLineNumber == b.EndLineNumber && a.EndColumn == b.EndColumn;
    }

    /// <summary>FNV-1a over UTF-16 code units — stable across processes (unlike
    /// <c>string.GetHashCode</c>) so sampling decisions are reproducible.</summary>
    private static uint StableHash(string s)
    {
        uint h = 2166136261;
        foreach (char c in s) { h ^= c; h *= 16777619; }
        return h;
    }

    /// <summary>
    /// Total, cycle-safe walk of an AST that validates every non-null source-backed span
    /// (expression, member, declaration, and output spans) and forbids
    /// <see cref="Expr.SequenceConstruct"/>. Reuses <see cref="AstWalker"/>, which visits
    /// children only and never follows the parent/back-reference field.
    /// </summary>
    private sealed class AstSpanWalker(int[] lineWidths, string which) : AstWalker
    {
        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.SequenceConstruct)
                throw new FrontEndInvariantException(
                    $"{which} AST contains Expr.SequenceConstruct — an internal-only node with no legal origin.");
            Check(expr.Span, "expression");
            base.VisitExpr(expr);
        }

        protected override void VisitPropertyDeclaration(Property property, SourceSpan span) => Check(span, "property-declaration");
        protected override void VisitExplicitParameterDeclaration(Algorithm algorithm, ParameterDeclaration declaration) => Check(declaration.Span, "parameter-declaration");
        protected override void VisitReservedOutputDeclaration(Algorithm algorithm, SourceSpan span) => Check(span, "output-declaration");
        protected override void VisitConditionalBinderDeclaration(Pattern.Bind pattern, SourceSpan span) => Check(span, "conditional-binder");
        protected override void VisitCollectingBindingMarker(SourceSpan span) => Check(span, "collecting-marker");
        protected override void VisitDotMemberIdentifier(Expr.DotCall expr, SourceSpan span) => Check(span, "dot-member");

        private void Check(SourceSpan? span, string kind)
        {
            if (span is null) return;   // synthetic / spanless nodes are allowed
            var reason = SourceSpanValidator.Validate(span, lineWidths);
            if (reason is not null)
                throw new FrontEndInvariantException(
                    $"Invalid {which} {kind} span [{reason}]: span={SourceSpanValidator.Describe(span)}");
        }
    }
}
