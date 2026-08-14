using System.Globalization;
using System.Text;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Builds a stable, cycle-safe structural fingerprint of an elaborated (or raw) program
/// plus its diagnostics. Used for the determinism and public-wrapper-parity invariants.
///
/// It walks DOWN the AST only (output, properties, opens, branch bodies, call-argument
/// bundles, operands, list elements, ...) and never follows the parent/back-reference
/// (<c>ScopeCtx Parent</c>) or any runtime object identity, so it terminates on the
/// finite AST tree and is identical for structurally-identical results.
/// </summary>
internal static class FrontEndFingerprint
{
    /// <summary>Full fingerprint including the frontend-only flag.</summary>
    public static string Compute(Algorithm root, IReadOnlyList<Diagnostic> diagnostics, bool canEvaluateAfterLoadErrors)
    {
        var sb = new StringBuilder(1024);
        sb.Append("flag:").Append(canEvaluateAfterLoadErrors ? '1' : '0').Append('\n');
        AppendDiagnostics(sb, diagnostics);
        sb.Append("root:");
        Alg(sb, root);
        return sb.ToString();
    }

    /// <summary>Parse-result fingerprint (root + diagnostics only) — the projection that
    /// <c>FrontEndResult.ToParseResult()</c> and <c>Parser.Parse</c> expose, so it drops
    /// the frontend-only flag.</summary>
    public static string ComputeParseResult(Algorithm root, IReadOnlyList<Diagnostic> diagnostics)
    {
        var sb = new StringBuilder(1024);
        AppendDiagnostics(sb, diagnostics);
        sb.Append("root:");
        Alg(sb, root);
        return sb.ToString();
    }

    private static void AppendDiagnostics(StringBuilder sb, IReadOnlyList<Diagnostic> diagnostics)
    {
        sb.Append("diags(").Append(diagnostics.Count).Append("):");
        foreach (var d in diagnostics)
            sb.Append('[').Append(d.Severity).Append('|').Append(d.Message).Append('|').Append(Span(d.Span)).Append(']');
        sb.Append('\n');
    }

    private static string Span(SourceSpan? s)
        => s is null ? "-" : $"{s.StartLineNumber},{s.StartColumn},{s.EndLineNumber},{s.EndColumn}";

    private static void Alg(StringBuilder sb, Algorithm a)
    {
        switch (a)
        {
            case Algorithm.Builtin b:
                sb.Append("Builtin{").Append(b.Id).Append('}');
                break;

            case Algorithm.User u:
                sb.Append("User{decon:").Append(u.IsAssignmentDeconstructionHelper ? '1' : '0')
                  .Append("}(");
                sb.Append("params[");
                foreach (var p in u.Parameters) ParamDecl(sb, p);
                sb.Append("]patterns[");
                foreach (var pp in u.ParameterPatterns) sb.Append(pp.DisplayName).Append(';');
                sb.Append("]opens[");
                foreach (var o in u.Opens) Expr(sb, o);
                sb.Append("]props[");
                foreach (var prop in u.Properties) Prop(sb, prop);
                sb.Append("]output[");
                foreach (var e in u.Output) Expr(sb, e);
                sb.Append("])");
                break;

            case Algorithm.Conditional c:
                sb.Append("Cond(opens[");
                foreach (var o in c.Opens) Expr(sb, o);
                sb.Append("]branches[");
                foreach (var br in c.Branches)
                {
                    Pattern(sb, br.Pattern);
                    sb.Append("=>");
                    Alg(sb, br.Body);
                    sb.Append(';');
                }
                sb.Append("])");
                break;

            default:
                sb.Append("Alg?").Append(a.GetType().Name);
                break;
        }
    }

    private static void ParamDecl(StringBuilder sb, ParameterDeclaration p)
        => sb.Append(p.Name).Append(':').Append(p.Kind).Append('@').Append(Span(p.Span))
            .Append("#collecting@").Append(Span(p.CollectMarkerSpan)).Append(';');

    private static void Prop(StringBuilder sb, Property p)
    {
        sb.Append('{').Append(p.Name).Append(",pub:").Append(p.IsPublic ? '1' : '0')
          .Append(",exp:").Append(p.Exposure).Append(",decl[");
        foreach (var s in p.DeclarationSpans) sb.Append(Span(s)).Append(';');
        sb.Append("]=");
        Alg(sb, p.Value);
        sb.Append('}');
    }

    private static void Pattern(StringBuilder sb, Pattern p)
    {
        switch (p)
        {
            case Pattern.Bind b:
                sb.Append("Bind{").Append(b.Name).Append(':').Append(b.ParameterKind).Append('@').Append(Span(b.NameSpan))
                    .Append("#collecting@").Append(Span(b.CollectMarkerSpan)).Append('}');
                break;
            case Pattern.LitInt i:
                sb.Append("LInt{").Append(i.Value.ToString(CultureInfo.InvariantCulture)).Append('}');
                break;
            case Pattern.LitString s:
                sb.Append("LStr{").Append(s.Value).Append('}');
                break;
            case Pattern.SequenceValue sv:
                sb.Append("PSeq[");
                foreach (var it in sv.Items) Pattern(sb, it);
                sb.Append(']');
                break;
            default:
                sb.Append("Pat?").Append(p.GetType().Name);
                break;
        }
    }

    private static void Expr(StringBuilder sb, Expr e)
    {
        sb.Append('@').Append(Span(e.Span)).Append(':');
        switch (e)
        {
            case Expr.Param p: sb.Append("Param{").Append(p.Name).Append('}'); break;
            case Expr.Num n: sb.Append("Num{").Append(n.Value.ToString(CultureInfo.InvariantCulture)).Append('}'); break;
            case Expr.StringLiteral s: sb.Append("Str{").Append(s.Value).Append('}'); break;
            case Expr.Resolve r: sb.Append("Res{").Append(r.Name).Append('}'); break;
            case Expr.Unary(var op, var o): sb.Append("Un{").Append(op).Append("}("); Expr(sb, o); sb.Append(')'); break;
            case Expr.Binary(var op, var l, var r): sb.Append("Bin{").Append(op).Append("}("); Expr(sb, l); sb.Append(','); Expr(sb, r); sb.Append(')'); break;
            case Expr.Index(var t, var sel): sb.Append("Idx("); Expr(sb, t); sb.Append(','); Expr(sb, sel); sb.Append(')'); break;
            case Expr.SequenceConstruct(var l, var r): sb.Append("SeqC("); Expr(sb, l); sb.Append(','); Expr(sb, r); sb.Append(')'); break;
            case Expr.EmptySequence es: sb.Append("Empty{").Append(es.Depth).Append('}'); break;
            case Expr.SequenceSpread(var o): sb.Append("Spread("); Expr(sb, o); sb.Append(')'); break;
            case Expr.ListLiteral(var items): sb.Append("List["); foreach (var it in items) Expr(sb, it); sb.Append(']'); break;
            case Expr.Grace(var inner, var w): sb.Append("Grace{").Append(w).Append("}("); Expr(sb, inner); sb.Append(')'); break;
            case Expr.AlgorithmExpr(var alg): sb.Append("ABlk("); Alg(sb, alg); sb.Append(')'); break;
            case Expr.Capture(var captureBody): sb.Append("Cap["); foreach (var row in captureBody) Expr(sb, row); sb.Append(']'); break;
            case Expr.Call(var fn, var args):
                sb.Append("Call("); Expr(sb, fn); sb.Append(',');
                sb.Append("Args[");
                for (int i = 0; i < args.Count; i++) { if (i > 0) sb.Append(','); Expr(sb, args[i]); }
                sb.Append(']');
                sb.Append(')'); break;
            case Expr.NativeCall nc: sb.Append("Native{").Append(nc.FnName).Append('(').Append(string.Join(",", nc.ArgNames)).Append(")}"); break;
            case Expr.DotCall dc:
                sb.Append("Dot{").Append(dc.Name)
                    .Append(",mode:").Append(dc.ResolutionMode)
                    .Append(",member@").Append(Span(dc.MemberSpan))
                    .Append(",extension@").Append(Span(dc.ExtensionMarkerSpan))
                    .Append(",fallback:");
                if (dc.LexicalFallback is { } fallback)
                    Expr(sb, fallback);
                else
                    sb.Append("null");
                sb.Append("}(");
                Expr(sb, dc.Target);
                if (dc.Args is { } dargs)
                {
                    sb.Append(",args=");
                    sb.Append("Args[");
                    for (int i = 0; i < dargs.Count; i++) { if (i > 0) sb.Append(','); Expr(sb, dargs[i]); }
                    sb.Append(']');
                }
                sb.Append(')');
                break;
            default:
                sb.Append("Expr?").Append(e.GetType().Name);
                break;
        }
    }
}
