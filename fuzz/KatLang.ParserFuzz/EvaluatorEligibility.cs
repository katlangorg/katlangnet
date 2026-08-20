using System.Numerics;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// HARNESS-ONLY conservative classifier deciding whether an elaborated program may be
/// evaluated inside the coverage-guided campaign.
///
/// This is NOT a KatLang language rule and never modifies the production AST. Its only
/// purpose is to keep the fuzzing campaign concentrated on evaluator logic that should
/// COMPLETE, while genuinely resource-sensitive behaviour (unbounded recursion, infinite
/// loops, explosive allocation) is characterized separately by the process-isolated
/// resource probes. It deliberately over-excludes: conservative false positives are fine
/// and are reported per reason; it never attempts a termination proof.
/// </summary>
internal static class EvaluatorEligibility
{
    // Bounds for the terminating campaign. Literal bounds are Decimal128 because
    // they cap KatLang numeric literal values (Expr.Num carries Decimal128).
    private const int MaxSourceLength = 8192;
    private const int MaxAstNodes = 5000;
    private static readonly Decimal128 MaxRepeatLiteral = 100;
    private static readonly Decimal128 MaxRangeLiteral = 1000;
    private static readonly Decimal128 MaxPowLiteral = 1000;

    private static readonly HashSet<string> NonDeterministicNames =
        new(StringComparer.Ordinal) { "Random", "RandomInt" };

    internal sealed record Verdict(bool Eligible, IReadOnlyList<string> Reasons, int NodeCount, IReadOnlyList<string> Cycles)
    {
        /// <summary>Shapes that are detected but NO LONGER excluded, because KatLang's own
        /// deterministic limits now bound them. Reported so triage keeps the information.</summary>
        public IReadOnlyList<string> Notes { get; init; } = [];

        public string ReasonText => Reasons.Count == 0 ? "eligible" : string.Join("+", Reasons);

        public string NoteText => Notes.Count == 0 ? "-" : string.Join("+", Notes);
    }

    public static Verdict Classify(string source, Algorithm root)
    {
        var reasons = new List<string>();
        var notes = new List<string>();
        if (source.Length > MaxSourceLength) reasons.Add("source-too-large");

        var scan = new Scan();
        scan.Alg(root);

        if (scan.Nodes > MaxAstNodes) reasons.Add("ast-too-large");

        // Non-termination through recursion or looping is now BOUNDED by the campaign's
        // configured EvaluationLimits (depth + step budget), so these shapes stay in the
        // deterministic campaign and in replay instead of being excluded. Excluding them
        // would drop exactly the over-budget regression seeds this phase added.
        if (scan.HasWhile) notes.Add("while-call");
        if (scan.HasUnboundedRepeat) notes.Add("repeat-unbounded");

        // Large or unbounded ranges are now bounded by the campaign's configured
        // MaxCollectionItems: an oversized range is rejected BEFORE it allocates, so these
        // seeds belong in the deterministic campaign rather than only in the probes.
        if (scan.HasLargeRange) notes.Add("range-large-or-unbounded");

        // Still excluded: no collection is involved, so no materialization limit applies —
        // a huge exponent is pure arithmetic work the probes keep covering.
        if (scan.HasLargePow) reasons.Add("pow-large");
        if (scan.HasNativeOrRandom) reasons.Add("native-or-nondeterministic");

        var cycles = FindCycles(scan.PropertyRefs);
        if (cycles.Count > 0) notes.Add("recursion-cycle");

        return new Verdict(reasons.Count == 0, reasons, scan.Nodes, cycles) { Notes = notes };
    }

    /// <summary>Name-based property dependency cycles (self-recursion and mutual
    /// recursion). Intentionally coarse: names are compared without scope resolution, so
    /// shadowing yields a conservative exclusion.</summary>
    private static List<string> FindCycles(Dictionary<string, HashSet<string>> graph)
    {
        var cycles = new List<string>();
        var state = new Dictionary<string, int>(StringComparer.Ordinal); // 0 new, 1 in-stack, 2 done
        var stack = new List<string>();

        foreach (var node in graph.Keys)
            if (!state.ContainsKey(node))
                Visit(node);

        return cycles;

        void Visit(string node)
        {
            state[node] = 1;
            stack.Add(node);
            if (graph.TryGetValue(node, out var next))
            {
                foreach (var m in next)
                {
                    if (!graph.ContainsKey(m)) continue;
                    if (!state.TryGetValue(m, out var st) || st == 0) Visit(m);
                    else if (st == 1 && cycles.Count < 8)
                        cycles.Add(string.Join("->", stack.SkipWhile(n => n != m)) + "->" + m);
                }
            }
            stack.RemoveAt(stack.Count - 1);
            state[node] = 2;
        }
    }

    /// <summary>Single recursive pass collecting node count, risky builtin usage, and the
    /// property-name reference graph. Walks children only (never parent links).</summary>
    private sealed class Scan
    {
        public int Nodes;
        public bool HasWhile, HasUnboundedRepeat, HasLargeRange, HasLargePow, HasNativeOrRandom;
        public readonly Dictionary<string, HashSet<string>> PropertyRefs = new(StringComparer.Ordinal);

        private HashSet<string>? _current;

        public void Alg(Algorithm a)
        {
            if (++Nodes > 1_000_000) return;   // hard stop; ast-too-large will fire anyway

            foreach (var p in a.Properties)
            {
                var saved = _current;
                if (!PropertyRefs.TryGetValue(p.Name, out var refs))
                    PropertyRefs[p.Name] = refs = new HashSet<string>(StringComparer.Ordinal);
                _current = refs;
                Alg(p.Value);
                _current = saved;
            }

            foreach (var e in a.Opens) Ex(e);
            foreach (var e in a.Output) Ex(e);
            foreach (var b in a.Branches) Alg(b.Body);
        }

        private void Ex(Expr e)
        {
            if (++Nodes > 1_000_000) return;

            switch (e)
            {
                case Expr.Resolve r: Note(r.Name); break;
                case Expr.Param p: Note(p.Name); break;
                case Expr.NativeCall: HasNativeOrRandom = true; break;
                case Expr.Unary(_, var o): Ex(o); break;
                case Expr.Binary(var op, var l, var r):
                    if (op == BinaryOp.Pow && r is Expr.Num pn && Decimal128.Abs(pn.Value) > MaxPowLiteral) HasLargePow = true;
                    Ex(l); Ex(r); break;
                case Expr.Index(var t, var s): Ex(t); Ex(s); break;
                case Expr.SequenceSpread(var o): Ex(o); break;
                case Expr.SequenceConstruct(var l, var r): Ex(l); Ex(r); break;
                case Expr.Grace(var i, _): Ex(i); break;
                case Expr.ListLiteral(var items): foreach (var it in items) Ex(it); break;
                case Expr.AlgorithmExpr(var alg): Alg(alg); break;
                case Expr.Capture(var captureBody): foreach (var row in captureBody) Ex(row); break;
                case Expr.Call(var fn, var args):
                    CheckRiskyCall(NameOf(fn), args);
                    Ex(fn); foreach (var a in args) Ex(a); break;
                case Expr.DotCall dc:
                    if (NonDeterministicNames.Contains(dc.Name)) HasNativeOrRandom = true;
                    if (dc.Args is { } dargs) { CheckRiskyCall(dc.Name, dargs); foreach (var a in dargs) Ex(a); }
                    if (dc.LexicalFallback is { } fallback) Ex(fallback); else Note(dc.Name);
                    Ex(dc.Target); break;
            }
        }

        private static string? NameOf(Expr fn) => fn switch
        {
            Expr.Resolve r => r.Name,
            Expr.Param p => p.Name,
            Expr.Grace(Expr.Resolve r, _) => r.Name,
            _ => null,
        };

        private void Note(string name)
        {
            if (NonDeterministicNames.Contains(name)) HasNativeOrRandom = true;
            _current?.Add(name);
        }

        /// <summary>Flags loop/allocation builtins whose bound this harness cannot cheaply
        /// prove small. `while` is always excluded; `repeat`/`range` require every numeric
        /// literal in the argument list to be small and at least one to be present.</summary>
        private void CheckRiskyCall(string? name, OutputBundle args)
        {
            if (name is null) return;
            switch (name)
            {
                case "while": HasWhile = true; break;
                case "repeat": if (!BoundedLiterals(args, MaxRepeatLiteral)) HasUnboundedRepeat = true; break;
                case "range": if (!BoundedLiterals(args, MaxRangeLiteral)) HasLargeRange = true; break;
            }
        }

        private static bool BoundedLiterals(OutputBundle args, Decimal128 max)
        {
            bool sawLiteral = true_(args, max, out bool tooBig);
            return sawLiteral && !tooBig;
        }

        private static bool true_(OutputBundle args, Decimal128 max, out bool tooBig)
        {
            bool saw = false;
            bool big = false;
            foreach (var e in args) Walk(e);
            tooBig = big;
            return saw;

            void Walk(Expr e)
            {
                switch (e)
                {
                    case Expr.Num n:
                        saw = true;
                        if (Decimal128.Abs(n.Value) > max) big = true;
                        break;
                    case Expr.Unary(_, var o): Walk(o); break;
                    case Expr.Binary(_, var l, var r): Walk(l); Walk(r); break;
                    case Expr.SequenceSpread(var o): Walk(o); break;
                    case Expr.ListLiteral(var items): foreach (var it in items) Walk(it); break;
                    case Expr.AlgorithmExpr(var alg): foreach (var o2 in alg.Output) Walk(o2); break;
                    case Expr.Capture(var captureBody): foreach (var o2 in captureBody) Walk(o2); break;
                    default:
                        // A non-literal bound cannot be proven small here.
                        big = true;
                        break;
                }
            }
        }
    }
}
