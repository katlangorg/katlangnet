using System.Globalization;
using System.Text;
using KatLang;
using KatLang.Evaluation.Caching;

namespace KatLang.ParserFuzz;

internal enum EvaluatorPhase
{
    FrontendParse, Eligibility, PlainEval, CountedEval, PlainCountCompare,
    ResultInvariants, EngineEval, EngineParity, Determinism, InputIndependence,
}

internal sealed class EvaluatorInvariantException(string message) : Exception(message);

/// <summary>
/// Source-level evaluator robustness invariants for the TERMINATING subset selected by
/// <see cref="EvaluatorEligibility"/>. Uses only the real evaluator entry points
/// (<c>Evaluator.Run</c>, <c>Evaluator.RunCounted</c>, <c>KatLangEngine.Run</c>) and never
/// reimplements evaluator semantics. Ordinary <see cref="EvalError"/> values are expected
/// outcomes, not crashes; unexpected CLR exceptions escape to the fuzzing engine.
///
/// Invariant 7 (loop / sequence-pipeline / cache-vs-uncached optimization parity) is
/// intentionally OMITTED: the repository exposes no internal entry point to force generic
/// evaluation, and the task forbids reflection or duplicating optimizer code. Engine
/// parity below does compare the cached engine path against the uncached RunCounted path,
/// which covers the "cache must not change observable results" half of that invariant.
/// </summary>
internal static class EvaluatorInvariants
{
    /// <summary>
    /// Deterministic resource limits used by every evaluation in this harness.
    ///
    /// <para>KatLang now stops runaway recursion and unbounded work itself, so the
    /// campaign no longer depends on libFuzzer's process timeout to survive a
    /// non-terminating program: an over-budget program returns an ordinary structured
    /// <see cref="EvalError"/> like any other failure, and is replayed deterministically.
    /// The values are small enough that an infinite loop stops in milliseconds and large
    /// enough that ordinary generated programs finish normally.</para>
    /// </summary>
    internal static readonly EvaluationLimits CampaignLimits = new()
    {
        MaxDepth = 64,
        MaxSteps = 200_000,
        MaxCollectionItems = 5_000,
        MaxMaterializedItems = 200_000,
    };

    /// <summary>Engine-facing form of <see cref="CampaignLimits"/>; no downloader, no network.</summary>
    internal static readonly RunOptions CampaignOptions = new() { EvaluationLimits = CampaignLimits };

    private const uint EngineParitySampleModulus = 4;
    private const uint DeterminismSampleModulus = 16;
    private const uint InputIndependenceSampleModulus = 64;

    // Exercises the zero-argument property cache, nested properties, and a call.
    private const string ProbeSourceB = "A = 1 + 1\nB = (C = A + 2)\nD(x) = x + A\nOutput = D(B.C) + A";

    public static void Check(string source)
    {
        var phase = EvaluatorPhase.FrontendParse;
        Run(source, ref phase);
    }

    public static void Run(string source, ref EvaluatorPhase phase)
    {
        phase = EvaluatorPhase.FrontendParse;
        var parse = Parser.Parse(source);
        if (parse.HasErrors) return;                       // frontend errors: no evaluation

        phase = EvaluatorPhase.Eligibility;
        var verdict = EvaluatorEligibility.Classify(source, parse.Root);
        if (!verdict.Eligible) return;                     // resource-sensitive: probes cover it

        var block = new Expr.Block(parse.Root);

        phase = EvaluatorPhase.PlainEval;
        var plain = Evaluator.Run(block, CampaignLimits);

        phase = EvaluatorPhase.CountedEval;
        var counted = Evaluator.RunCounted(block, new RunScopedZeroArgPropertyResultCache(), CampaignLimits);

        phase = EvaluatorPhase.PlainCountCompare;
        if (plain.IsOk != counted.IsOk)
            throw new EvaluatorInvariantException(
                $"Plain/counted outcome mismatch: plain={(plain.IsOk ? "ok" : "err")} counted={(counted.IsOk ? "ok" : "err")}.");

        if (plain.IsOk)
        {
            if (!Result.ValueComparer.Equals(plain.Value, counted.Value.Value))
                throw new EvaluatorInvariantException(
                    $"Plain/counted value mismatch: plain={Shape(plain.Value)} counted={Shape(counted.Value.Value)}.");
        }
        else
        {
            var a = Innermost(plain.Error);
            var b = Innermost(counted.Error);
            if (a.GetType() != b.GetType())
                throw new EvaluatorInvariantException(
                    $"Plain/counted innermost error kind mismatch: plain={a.GetType().Name} counted={b.GetType().Name}.");
        }

        phase = EvaluatorPhase.ResultInvariants;
        if (counted.IsOk)
            CheckResultValue(counted.Value.Value, counted.Value.EmittedCount);
        CheckErrorSpans(source, plain, counted);

        uint h = StableHash(source);

        if (h % EngineParitySampleModulus == 0)
        {
            phase = EvaluatorPhase.EngineEval;
            var engine = KatLangEngine.Run(source, CampaignOptions);

            phase = EvaluatorPhase.EngineParity;
            CheckEngineParity(source, parse.Root, counted, engine);
        }

        if (h % DeterminismSampleModulus == 0)
        {
            phase = EvaluatorPhase.Determinism;
            var f1 = Observe(source);
            var f2 = Observe(source);
            if (!string.Equals(f1, f2, StringComparison.Ordinal))
                throw new EvaluatorInvariantException("Non-deterministic evaluator observation across two runs of the same source.");

            if (h % InputIndependenceSampleModulus == 0)
            {
                phase = EvaluatorPhase.InputIndependence;
                _ = Observe(ProbeSourceB);
                var f3 = Observe(source);
                if (!string.Equals(f1, f3, StringComparison.Ordinal))
                    throw new EvaluatorInvariantException("Evaluator observation changed after evaluating an unrelated program (leaked state).");
            }
        }
    }

    // ── Result structural validity ───────────────────────────────────────────
    private static void CheckResultValue(Result value, int emittedCount)
    {
        if (emittedCount < 0)
            throw new EvaluatorInvariantException($"Negative emitted count: {emittedCount}.");

        int hashBefore = value.GetHashCode();      // stability probe only; never persisted
        int nodes = 0;
        Walk(value, 0);
        if (value.GetHashCode() != hashBefore)
            throw new EvaluatorInvariantException("Result hash code changed across traversal (mutable value).");
        if (!Result.ValueComparer.Equals(value, value))
            throw new EvaluatorInvariantException("Result is not equal to itself under ValueComparer.");

        void Walk(Result r, int depth)
        {
            if (++nodes > 2_000_000)
                throw new EvaluatorInvariantException("Result traversal exceeded a sane node bound (possible cycle).");
            if (depth > 100_000)
                throw new EvaluatorInvariantException("Result nesting exceeded a sane depth bound (possible cycle).");

            switch (r)
            {
                case Result.SequenceValue sv:
                    // Singleton sequence structure is canonicalized away during ordinary
                    // value construction ([x] => x), so it must never be observable.
                    if (sv.Items.Count == 1)
                        throw new EvaluatorInvariantException("Sequence value with exactly one child (singleton sequences are canonicalized away).");
                    foreach (var it in sv.Items)
                    {
                        if (it is null) throw new EvaluatorInvariantException("Null child inside a sequence value.");
                        Walk(it, depth + 1);
                    }
                    break;

                case Result.ListValue lv:      // exact singleton lists ARE legal
                    foreach (var it in lv.Items)
                    {
                        if (it is null) throw new EvaluatorInvariantException("Null child inside an exact list value.");
                        Walk(it, depth + 1);
                    }
                    break;
            }
        }
    }

    private static void CheckErrorSpans(string source, EvalResult<Result> plain, EvalResult<Evaluator.CountedResult> counted)
    {
        var widths = SourceSpanValidator.LineWidths(source);
        if (plain.IsError) CheckSpans(plain.Error, widths);
        if (counted.IsError) CheckSpans(counted.Error, widths);
    }

    private static void CheckSpans(EvalError error, int[] widths)
    {
        // Walk the WithContext chain; synthetic errors may be spanless.
        for (EvalError? e = error; e is not null; e = (e as EvalError.WithContext)?.Inner)
        {
            if (e.Span is not { } span) continue;
            var reason = SourceSpanValidator.Validate(span, widths);
            if (reason is not null)
                throw new EvaluatorInvariantException(
                    $"Invalid evaluator error span [{reason}]: {SourceSpanValidator.Describe(span)} on {e.GetType().Name}.");
        }
    }

    // ── Public engine parity ─────────────────────────────────────────────────
    private static void CheckEngineParity(string source, Algorithm root, EvalResult<Evaluator.CountedResult> counted, RunResult engine)
    {
        bool hasDisplayDecimals = root.Properties.Any(p => p.Name == "DisplayDecimals");

        if (counted.IsError)
        {
            bool isNoOutput = counted.Error is EvalError.WithContext { Inner: EvalError.MissingOutput };
            if (isNoOutput && engine is not RunResult.NoProgramOutput)
                throw new EvaluatorInvariantException($"Expected NoProgramOutput from engine, got {engine.GetType().Name}.");
            if (!isNoOutput && engine is not RunResult.EvalFailure)
                throw new EvaluatorInvariantException($"Expected EvalFailure from engine, got {engine.GetType().Name}.");
            return;
        }

        // counted succeeded: the engine must succeed too, unless DisplayDecimals itself is
        // invalid (a documented production rule that turns success into EvalFailure).
        if (engine is not RunResult.Success success)
        {
            if (hasDisplayDecimals && engine is RunResult.EvalFailure) return;
            throw new EvaluatorInvariantException(
                $"Counted evaluation succeeded but engine returned {engine.GetType().Name}.");
        }

        if (!Result.ValueComparer.Equals(success.Value, counted.Value.Value))
            throw new EvaluatorInvariantException(
                $"Engine value differs from counted value: engine={Shape(success.Value)} counted={Shape(counted.Value.Value)}.");

        if (success.EmittedCount != counted.Value.EmittedCount)
            throw new EvaluatorInvariantException(
                $"Engine emitted count {success.EmittedCount} != counted {counted.Value.EmittedCount}.");

        var expectedAtoms = counted.Value.Value.ToHostAtoms();
        if (!success.Atoms.SequenceEqual(expectedAtoms))
            throw new EvaluatorInvariantException("Engine host atoms differ from the counted value's host atoms.");
    }

    // ── Stable observation / fingerprint ─────────────────────────────────────
    public static string Observe(string source)
    {
        var sb = new StringBuilder(256);
        var parse = Parser.Parse(source);
        sb.Append("parse:").Append(parse.HasErrors ? "err" : "ok");
        if (parse.HasErrors) return sb.ToString();

        var verdict = EvaluatorEligibility.Classify(source, parse.Root);
        sb.Append("|elig:").Append(verdict.Eligible ? "y" : "n").Append(':').Append(verdict.ReasonText);
        if (!verdict.Eligible) return sb.ToString();

        var block = new Expr.Block(parse.Root);
        var plain = Evaluator.Run(block, CampaignLimits);
        sb.Append("|plain:").Append(plain.IsOk ? Shape(plain.Value) : ErrorKey(plain.Error));

        var counted = Evaluator.RunCounted(block, new RunScopedZeroArgPropertyResultCache(), CampaignLimits);
        sb.Append("|counted:");
        if (counted.IsOk) sb.Append(Shape(counted.Value.Value)).Append("|n=").Append(counted.Value.EmittedCount);
        else sb.Append(ErrorKey(counted.Error));

        var engine = KatLangEngine.Run(source, CampaignOptions);
        sb.Append("|engine:").Append(EngineKey(engine));
        return sb.ToString();
    }

    private static string EngineKey(RunResult r) => r switch
    {
        RunResult.Success s =>
            "S:" + Shape(s.Value) + "|n=" + s.EmittedCount.ToString(CultureInfo.InvariantCulture) +
            "|atoms=" + string.Join(",", s.Atoms.Select(a => a.ToString(CultureInfo.InvariantCulture))) +
            "|disp=" + r.ToDisplayString(),
        RunResult.NoProgramOutput => "N",
        RunResult.ParseFailure p => "P:" + p.Errors.Count.ToString(CultureInfo.InvariantCulture),
        RunResult.EvalFailure e => "E:" + e.Errors.Count.ToString(CultureInfo.InvariantCulture),
        _ => "?",
    };

    /// <summary>Neutral recursive value shape (invariant-culture numerics, no identity).</summary>
    private static string Shape(Result r)
    {
        var sb = new StringBuilder();
        Append(r);
        return sb.ToString();

        void Append(Result v)
        {
            switch (v)
            {
                case Result.Atom a: sb.Append('A').Append(a.Value.ToString(CultureInfo.InvariantCulture)); break;
                case Result.Str s: sb.Append("S{").Append(s.Value).Append('}'); break;
                case Result.SequenceValue sv:
                    sb.Append('(');
                    for (int i = 0; i < sv.Items.Count; i++) { if (i > 0) sb.Append(','); Append(sv.Items[i]); }
                    sb.Append(')');
                    break;
                case Result.ListValue lv:
                    sb.Append('[');
                    for (int i = 0; i < lv.Items.Count; i++) { if (i > 0) sb.Append(','); Append(lv.Items[i]); }
                    sb.Append(']');
                    break;
                default: sb.Append('?').Append(v.GetType().Name); break;
            }
        }
    }

    /// <summary>Innermost structured error kind plus its stable record payload.</summary>
    private static string ErrorKey(EvalError e)
    {
        var inner = Innermost(e);
        return inner.GetType().Name + "{" + inner + "}";
    }

    internal static EvalError Innermost(EvalError e)
    {
        while (e is EvalError.WithContext wc) e = wc.Inner;
        return e;
    }

    private static uint StableHash(string s)
    {
        uint h = 2166136261;
        foreach (char c in s) { h ^= c; h *= 16777619; }
        return h;
    }
}
