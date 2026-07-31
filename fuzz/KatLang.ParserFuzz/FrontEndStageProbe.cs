using System.Diagnostics;
using System.Globalization;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Staged frontend performance probe. Runs each production frontend stage independently
/// against one source and reports elapsed time, AST size, and diagnostics per stage, so a
/// pathological pass can be isolated without a profiler.
///
///   stage-probe FILE [FILE...]   one line per source with per-stage timings
///
/// Each invocation is a fresh process; every stage is warmed with a small unrelated input
/// first so JIT cost is not attributed to the measured run.
/// </summary>
internal static class FrontEndStageProbe
{
    private const string WarmUp = "A = 1 + 1\nF(x) = x * 2\nF(A)";

    public static int Run(string[] args)
    {
        // Warm every stage so the first measured source is not paying JIT.
        for (int i = 0; i < 3; i++) Measure(WarmUp, out _);

        Console.WriteLine("source                bytes  tokens  rawNodes  lex    parse   guard   paramDet  implicit  exposure  pipeline  publicParse  postNodes diags");
        foreach (var path in args.Skip(1))
        {
            string source;
            try { source = Program.DecodeSource(File.ReadAllBytes(path)); }
            catch (Exception ex) { Console.Error.WriteLine($"skip {path}: {ex.Message}"); continue; }

            var m = Measure(source, out var note);
            Console.WriteLine(
                $"{Path.GetFileName(path),-20} {source.Length,6} {m.Tokens,7} {m.RawNodes,9} " +
                $"{F(m.Lex)} {F(m.Parse)} {F(m.Guard)} {F(m.ParamDetect)} {F(m.Implicit)} {F(m.Exposure)} {F(m.Pipeline)} {F(m.PublicParse)} " +
                $"{m.PostNodes,9} {m.Diagnostics,5} {note}");
        }
        return 0;
    }

    /// <summary>`run FILE...` — evaluate each source through the public engine and print
    /// the observable outcome. Used to establish the open-ownership semantic matrix.</summary>
    public static int RunSources(string[] args)
    {
        foreach (var path in args.Skip(1))
        {
            string source;
            try { source = Program.DecodeSource(File.ReadAllBytes(path)); }
            catch (Exception ex) { Console.Error.WriteLine($"skip {path}: {ex.Message}"); continue; }

            string outcome;
            try
            {
                var r = KatLangEngine.Run(source);
                outcome = $"{r.GetType().Name}: {r.ToDisplayString().Replace("\r", "").Replace("\n", " / ")}";
            }
            catch (Exception ex) { outcome = $"EXCEPTION {ex.GetType().Name}: {ex.Message}"; }

            Console.WriteLine($"{Path.GetFileName(path),-24} {outcome}");
        }
        return 0;
    }

    private static string F(double ms) => ms.ToString("F1", CultureInfo.InvariantCulture).PadLeft(8);

    private sealed record M(int Tokens, int RawNodes, int PostNodes, int Diagnostics,
        double Lex, double Parse, double Guard, double ParamDetect, double Implicit, double Exposure,
        double Pipeline, double PublicParse);

    private static M Measure(string source, out string note)
    {
        note = "";
        var sw = new Stopwatch();

        sw.Restart();
        var (tokens, _) = Lexer.Tokenize(source);
        double lex = sw.Elapsed.TotalMilliseconds;

        sw.Restart();
        var syntax = Parser.ParseSyntax(source);
        double parse = sw.Elapsed.TotalMilliseconds;
        int rawNodes = CountNodes(syntax.Root);
        int rawDistinct = CountDistinct(syntax.Root);

        sw.Restart();
        var loadDiags = LoadElaborationGuard.CreateUnavailableDiagnostics(syntax.Root);
        double guard = sw.Elapsed.TotalMilliseconds;

        double paramDetect = 0, implicitMs = 0, exposure = 0;
        int postNodes = rawNodes;
        int postDistinct = rawDistinct;
        Algorithm current = syntax.Root;

        if (loadDiags.Count == 0)
        {
            sw.Restart();
            var (parameterized, _) = ParameterDetector.Detect(current);
            paramDetect = sw.Elapsed.TotalMilliseconds;

            sw.Restart();
            var resolved = ImplicitArgumentResolver.Resolve(parameterized);
            implicitMs = sw.Elapsed.TotalMilliseconds;

            sw.Restart();
            var exposed = PropertyExposureResolver.Resolve(resolved);
            exposure = sw.Elapsed.TotalMilliseconds;

            current = exposed;
            postNodes = CountNodes(current);
            postDistinct = CountDistinct(current);
        }
        else note = "(load-guard short-circuit)";

        sw.Restart();
        var pipeline = FrontEndPipeline.Process(source);
        double pipelineMs = sw.Elapsed.TotalMilliseconds;

        sw.Restart();
        var pub = Parser.Parse(source);
        double publicMs = sw.Elapsed.TotalMilliseconds;

        note += $" | distinct raw={rawDistinct} post={postDistinct}";

        return new M(tokens.Count, rawNodes, postNodes, pipeline.Diagnostics.Count,
            lex, parse, guard, paramDetect, implicitMs, exposure, pipelineMs, publicMs);
    }

    /// <summary>
    /// Distinct AST node objects by REFERENCE identity. Compared against the tree-walk
    /// count this reveals whether the parser emits a shared-subtree DAG (distinct ≪ tree)
    /// that later passes expand into an actual tree.
    /// </summary>
    internal static int CountDistinct(Algorithm root)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var algs = new Stack<Algorithm>();
        var exprs = new Stack<Expr>();
        algs.Push(root);

        while (algs.Count > 0 || exprs.Count > 0)
        {
            while (algs.Count > 0)
            {
                var a = algs.Pop();
                if (!seen.Add(a)) continue;
                foreach (var p in a.Properties) { if (seen.Add(p)) algs.Push(p.Value); }
                foreach (var e in a.Opens) exprs.Push(e);
                foreach (var e in a.Output) exprs.Push(e);
                foreach (var b in a.Branches) { if (seen.Add(b)) algs.Push(b.Body); }
            }

            while (exprs.Count > 0)
            {
                var e = exprs.Pop();
                if (!seen.Add(e)) continue;
                switch (e)
                {
                    case Expr.Unary(_, var o): exprs.Push(o); break;
                    case Expr.Binary(_, var l, var r): exprs.Push(l); exprs.Push(r); break;
                    case Expr.Index(var t, var s): exprs.Push(t); exprs.Push(s); break;
                    case Expr.SequenceSpread(var o): exprs.Push(o); break;
                    case Expr.SequenceConstruct(var l, var r): exprs.Push(l); exprs.Push(r); break;
                    case Expr.Grace(var i, _): exprs.Push(i); break;
                    case Expr.ListLiteral(var items): foreach (var it in items) exprs.Push(it); break;
                    case Expr.Block(var alg): algs.Push(alg); break;
                    case Expr.Call(var fn, var args): exprs.Push(fn); algs.Push(args); break;
                    case Expr.DotCall dc: exprs.Push(dc.Target); if (dc.Args is { } a2) algs.Push(a2); break;
                }
            }
        }
        return seen.Count;
    }

    /// <summary>Recursive AST node count; walks children only (never parent links).</summary>
    internal static int CountNodes(Algorithm root)
    {
        int n = 0;
        Alg(root);
        return n;

        void Alg(Algorithm a)
        {
            if (++n > 50_000_000) return;
            foreach (var p in a.Properties) { n++; Alg(p.Value); }
            foreach (var e in a.Opens) Ex(e);
            foreach (var e in a.Output) Ex(e);
            foreach (var b in a.Branches) { n++; Alg(b.Body); }
        }

        void Ex(Expr e)
        {
            if (++n > 50_000_000) return;
            switch (e)
            {
                case Expr.Unary(_, var o): Ex(o); break;
                case Expr.Binary(_, var l, var r): Ex(l); Ex(r); break;
                case Expr.Index(var t, var s): Ex(t); Ex(s); break;
                case Expr.SequenceSpread(var o): Ex(o); break;
                case Expr.SequenceConstruct(var l, var r): Ex(l); Ex(r); break;
                case Expr.Grace(var i, _): Ex(i); break;
                case Expr.ListLiteral(var items): foreach (var it in items) Ex(it); break;
                case Expr.Block(var alg): Alg(alg); break;
                case Expr.Call(var fn, var args): Ex(fn); Alg(args); break;
                case Expr.DotCall dc: Ex(dc.Target); if (dc.Args is { } a2) Alg(a2); break;
            }
        }
    }
}
