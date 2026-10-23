using System.Text;
using System.Numerics;

namespace KatLang.Tests.StructuralFuzz;

/// <summary>
/// Stable generator-side symbol identity, deliberately separate from rendered
/// names: transforms rename TEXT while the binding graph (who references whom)
/// stays fixed, which is what makes alpha-renaming/shadowing/isomorphism
/// metamorphisms provable rather than hopeful.
/// </summary>
public readonly record struct Sym(int Id)
{
    public override string ToString() => $"#{Id}";
}

/// <summary>
/// Model expressions — a deliberately tiny, closed vocabulary (task: structural
/// diversity over data diversity). Atom values are drawn from disjoint pools
/// (<see cref="StructuralProgram.NormalAtoms"/>, branch/clause sentinels
/// 101–149, tripwires 666–699) so token-level presence/absence of a sentinel in
/// the neutral raw observation is an unambiguous absolute oracle.
/// </summary>
public abstract record MExpr
{
    public sealed record Atom(Decimal128 Value) : MExpr;

    /// <summary>The Boolean literal <c>true</c> / <c>false</c>: the only condition kind
    /// an <see cref="If"/> accepts (numbers have no truth value).</summary>
    public sealed record Bool(bool Value) : MExpr;

    /// <summary>Reference to a declaration/binder by SYMBOL, not by name.</summary>
    public sealed record Ref(Sym Target) : MExpr;

    public sealed record Add(MExpr Left, MExpr Right) : MExpr;

    /// <summary>Parenthesized sequence group. NEVER rendered with exactly one
    /// plain item (single-expression parens unwrap at parse); a one-item group
    /// is legal only when the item is a <see cref="Spread"/> (spreads are a
    /// retained form, and <c>(P*)</c> is the canonical capture-of-supply).</summary>
    public sealed record Group(IReadOnlyList<MExpr> Items) : MExpr;

    /// <summary>Postfix spread <c>operand*</c>. Operand restricted to
    /// Ref/Group/Call so rendering never needs precedence parentheses.</summary>
    public sealed record Spread(MExpr Operand) : MExpr;

    public sealed record Call(Sym Callee, IReadOnlyList<MExpr> Args) : MExpr;

    /// <summary>Builtin <c>if(cond, then, else)</c>. Conditions are Boolean
    /// literals (<see cref="Bool"/>) in generated programs, so truth is known by
    /// construction — a number is never a condition — and the unselected branch
    /// is provably dead (Lean evaluates only the selected branch argument —
    /// <c>applyBuiltinCounted .ifBuiltin</c>).</summary>
    public sealed record If(MExpr Cond, MExpr Then, MExpr Else) : MExpr;

    /// <summary>Brace algorithm <c>{ decls… rows… }</c> — the sole nested
    /// lexical scope form.</summary>
    public sealed record Brace(MScope Scope) : MExpr;

    /// <summary>Front-end-valid runtime tripwire: <c>(1, 2)[9]</c> (err index).</summary>
    public sealed record IndexErr : MExpr;

    // ── SEM-2B grammar-aware extension ──────────────────────────────────────
    // The original StructuralCorpus never builds these nodes, so its rendered
    // sources (and therefore every existing case identity) are unchanged.

    /// <summary>Dot edge <c>receiver.Member</c> or, with <paramref name="Args"/>,
    /// <c>receiver.Member(args)</c>. <paramref name="Member"/> is a FIXED spelling
    /// — a call-reference intrinsic (<c>Arguments</c>, <c>Algorithm</c>,
    /// <c>Invoke</c>) or a builtin used through dot syntax (<c>count</c>,
    /// <c>repeat</c>, <c>while</c>) — never a generated symbol, so renaming
    /// can neither capture nor be captured by it.</summary>
    public sealed record Dot(MExpr Receiver, string Member, IReadOnlyList<MExpr>? Args) : MExpr;

    /// <summary>Variadic postfix selection <c>receiver[s1, …, sn]</c> (zero
    /// selectors render <c>receiver[]</c>).</summary>
    public sealed record Select(MExpr Receiver, IReadOnlyList<MExpr> Selectors) : MExpr;

    /// <summary>Exact list literal <c>[items]</c>.</summary>
    public sealed record ListLit(IReadOnlyList<MExpr> Items) : MExpr;

    /// <summary>Call of a FIXED-name operation: a builtin (<c>count</c>) or a
    /// deterministic host-fixture operation (<c>trace</c>, <c>wait</c>). The name
    /// lies outside every generated name pool, so it is not a symbol.</summary>
    public sealed record Prim(string Name, IReadOnlyList<MExpr> Args) : MExpr;

    /// <summary>Binary operator other than <c>+</c> (<c>*</c>, <c>/</c>, <c>-</c>,
    /// <c>&lt;</c>). Compound operands render inside redundant parentheses,
    /// which the parser erases, so no precedence reasoning is needed.</summary>
    public sealed record Binary(string Operator, MExpr Left, MExpr Right) : MExpr;
}

/// <summary>A flat parameter: fixed, collecting (<c>*name</c>), or META
/// (<c>meta name</c>, SEM-2B; a META parameter is always fixed).</summary>
public sealed record MParam(Sym Symbol, bool Collecting, bool Meta = false);

/// <summary>Deconstruction/sequence-pattern binder (<c>name</c> or <c>*name</c>).</summary>
public sealed record MBinder(Sym Symbol, bool Collecting);

public abstract record MPattern
{
    /// <summary>Literal clause pattern, e.g. <c>C(7)</c>. Two distinct literals
    /// are disjoint by construction — the precondition for clause permutation.</summary>
    public sealed record Literal(Decimal128 Value) : MPattern;

    /// <summary>Catch-all binder clause pattern, e.g. <c>C(x)</c>.</summary>
    public sealed record Binder(Sym Symbol) : MPattern;

    /// <summary>A collecting name inside a structural pattern.</summary>
    public sealed record Collecting(Sym Symbol) : MPattern;

    /// <summary>A sequence or exact-list pattern, preserving its nested delimiter structure.</summary>
    public sealed record Structure(bool IsList, IReadOnlyList<MPattern> Items) : MPattern;

    /// <summary>Top-level arity-2 literal pattern, e.g. <c>C(0, 0)</c>. Used
    /// ONLY by the IntroduceInvalidFamilyShape transform to violate the
    /// uniform-family-arity front-end rule on purpose.</summary>
    public sealed record LiteralPair(Decimal128 First, Decimal128 Second) : MPattern;
}

public sealed record MClause(MPattern Pattern, MExpr Body);

public abstract record MDecl
{
    /// <summary>Property definition; multi-row bodies (<c>P = 10, 20</c>) are
    /// the multi-output producers whose supply count the generator knows.</summary>
    public sealed record Value(Sym Symbol, IReadOnlyList<MExpr> Rows) : MDecl;

    /// <summary>Flat function <c>F(a, *b) = body</c>.</summary>
    public sealed record Func(Sym Symbol, IReadOnlyList<MParam> Params, MExpr Body) : MDecl;

    /// <summary>Named heads of top-level arity 1: literal/catch-all clause families,
    /// or one structural head for an ordinary pattern function. Only literal/catch-all
    /// heads admit the clause-family transformations.</summary>
    public sealed record Family(Sym Symbol, IReadOnlyList<MClause> Clauses) : MDecl;

    /// <summary>Single-clause sequence-value pattern function
    /// <c>H((a, *b, c)) = body</c> — opens the one received structure. With
    /// <paramref name="ListPattern"/> (SEM-2B) it is the exact-list pattern
    /// <c>H([a, *b, c]) = body</c>, which opens only a list.</summary>
    public sealed record SeqPatternFunc(Sym Symbol, IReadOnlyList<MBinder> Binders, MExpr Body, bool ListPattern = false) : MDecl;

    /// <summary>Assignment deconstruction <c>x, *y, z = RHS</c>.</summary>
    public sealed record Deconstruction(IReadOnlyList<MBinder> Binders, MExpr Rhs) : MDecl;
}

/// <summary>One lexical scope: declarations then output rows.</summary>
public sealed record MScope(IReadOnlyList<MDecl> Decls, IReadOnlyList<MExpr> Rows);

/// <summary>
/// A complete generated program: the semantic model (scopes, symbols, binding
/// graph) plus the rendered-name map and the model-derived absolute
/// expectations. Renaming transforms change ONLY <see cref="Names"/>;
/// structural transforms change the model; both revalidate through
/// <see cref="StructuralProgram.ValidateNaming"/> so a transform can never
/// silently change binding identity.
/// </summary>
public sealed record StructuralProgram(
    MScope Root,
    IReadOnlyDictionary<Sym, string> Names,
    IReadOnlyList<Decimal128> MustContainAtoms,
    IReadOnlyList<Decimal128> MustNotContainAtoms)
{
    public static readonly Decimal128[] NormalAtoms = [0m, 1m, 2m, 7m];

    public static readonly Decimal128 FirstSentinel = 101m;
    public static readonly Decimal128 FirstTripwire = 666m;

    // Every generated root ends with this real output row. It closes a
    // preceding spread explicitly (the generator never relies on an attached
    // line-final star ending a row, issue #183, although that is valid too) and
    // participates in all full-result oracles.
    // It lies outside the ordinary, branch-sentinel and tripwire atom pools.
    public static readonly Decimal128 RootControl = 997m;

    public string Render() => StructuralRenderer.Render(this);

    /// <summary>All symbols declared anywhere, with their declaration scope path.</summary>
    public IReadOnlyList<(Sym Symbol, ScopeInfo Scope, string Kind)> AllDeclarations()
        => ScopeGraph.Build(Root).Declarations;

    /// <summary>Throws with a diagnostic when the naming map would change the
    /// binding graph: every reference's nearest visible declaration of its
    /// rendered name must be exactly the reference's target symbol, and no two
    /// declarations in ONE scope may share a rendered name (duplicateProperty).</summary>
    public void ValidateNaming()
    {
        if (Root.Rows.Count == 0 || Root.Rows[^1] is not MExpr.Atom control || control.Value != RootControl)
            throw new InvalidOperationException("A structural fixture must retain its explicit final root control row.");
        ScopeGraph.Build(Root).ValidateNaming(Names);
    }

    /// <summary>The scope-model dump printed in failure reports.</summary>
    public string DescribeScopes() => ScopeGraph.Build(Root).Describe(Names);
}

/// <summary>Info about one scope in the generator-side graph.</summary>
public sealed record ScopeInfo(int Id, int? ParentId, string Label);

/// <summary>
/// The generator-side scope graph: which symbols each scope declares, in
/// which order, and which references live where. Built once from the model
/// and used to (a) validate naming maps, (b) select rename/shadow targets,
/// (c) describe failures. This is the "know the scope graph before source is
/// rendered" requirement made executable.
/// </summary>
public sealed class ScopeGraph
{
    private sealed record ScopeNode(ScopeInfo Info, ScopeNode? Parent, List<Sym> Declared);

    private sealed record Reference(Sym Target, ScopeNode InScope);

    private readonly List<ScopeNode> _scopes = [];
    private readonly List<Reference> _references = [];
    private readonly List<(Sym Symbol, ScopeInfo Scope, string Kind)> _declarations = [];

    public IReadOnlyList<(Sym Symbol, ScopeInfo Scope, string Kind)> Declarations => _declarations;

    /// <summary>Every scope, including declaration-free ones — ancestor-chain
    /// walks must not break on an intermediate scope with no declarations.</summary>
    public IReadOnlyList<ScopeInfo> AllScopes => _scopes.Select(s => s.Info).ToList();

    /// <summary>Symbols visible from the scope that declares <paramref name="target"/>'s
    /// references — used by transforms to prove freshness/no-capture.</summary>
    public IReadOnlyList<Sym> AllSymbols => _declarations.Select(d => d.Symbol).ToList();

    public static ScopeGraph Build(MScope root)
    {
        var graph = new ScopeGraph();
        var rootNode = graph.NewScope(null, "root");
        graph.WalkScope(root, rootNode);
        return graph;
    }

    private ScopeNode NewScope(ScopeNode? parent, string label)
    {
        var node = new ScopeNode(new ScopeInfo(_scopes.Count, parent?.Info.Id, label), parent, []);
        _scopes.Add(node);
        return node;
    }

    private void Declare(ScopeNode scope, Sym symbol, string kind)
    {
        scope.Declared.Add(symbol);
        _declarations.Add((symbol, scope.Info, kind));
    }

    private void WalkScope(MScope scope, ScopeNode node)
    {
        // Declarations first: KatLang properties in one algorithm are mutually
        // visible regardless of row order, so visibility is per-scope, not
        // positional.
        foreach (var decl in scope.Decls)
        {
            switch (decl)
            {
                case MDecl.Value v:
                    Declare(node, v.Symbol, "value");
                    break;
                case MDecl.Func f:
                    Declare(node, f.Symbol, "func");
                    break;
                case MDecl.Family fam:
                    Declare(node, fam.Symbol, "family");
                    break;
                case MDecl.SeqPatternFunc sp:
                    Declare(node, sp.Symbol, "seqPatternFunc");
                    break;
                case MDecl.Deconstruction d:
                    foreach (var binder in d.Binders)
                        Declare(node, binder.Symbol, binder.Collecting ? "deconstructCollecting" : "deconstructBinder");
                    break;
                default:
                    throw new InvalidOperationException($"Unhandled decl kind {decl.GetType().Name}");
            }
        }

        foreach (var decl in scope.Decls)
        {
            switch (decl)
            {
                case MDecl.Value v:
                    foreach (var row in v.Rows)
                        WalkExpr(row, node);
                    break;
                case MDecl.Func f:
                {
                    var body = NewScope(node, $"func {f.Symbol}");
                    foreach (var p in f.Params)
                        Declare(body, p.Symbol, p.Meta ? "metaParam" : p.Collecting ? "collectingParam" : "param");
                    WalkExpr(f.Body, body);
                    break;
                }

                case MDecl.Family fam:
                    foreach (var clause in fam.Clauses)
                    {
                        var body = NewScope(node, $"clause of {fam.Symbol}");
                        DeclarePattern(body, clause.Pattern);
                        WalkExpr(clause.Body, body);
                    }

                    break;
                case MDecl.SeqPatternFunc sp:
                {
                    var body = NewScope(node, $"seqPattern {sp.Symbol}");
                    foreach (var binder in sp.Binders)
                        Declare(body, binder.Symbol, binder.Collecting ? "seqCollectingBinder" : "seqBinder");
                    WalkExpr(sp.Body, body);
                    break;
                }

                case MDecl.Deconstruction d:
                    WalkExpr(d.Rhs, node);
                    break;
            }
        }

        foreach (var row in scope.Rows)
            WalkExpr(row, node);
    }

    private void DeclarePattern(ScopeNode scope, MPattern pattern)
    {
        switch (pattern)
        {
            case MPattern.Binder binder:
                Declare(scope, binder.Symbol, "clauseBinder");
                break;
            case MPattern.Collecting collecting:
                Declare(scope, collecting.Symbol, "clauseCollecting");
                break;
            case MPattern.Structure structure:
                foreach (var item in structure.Items) DeclarePattern(scope, item);
                break;
        }
    }

    private void WalkExpr(MExpr expr, ScopeNode scope)
    {
        switch (expr)
        {
            case MExpr.Atom:
            case MExpr.Bool:
            case MExpr.IndexErr:
                return;
            case MExpr.Ref r:
                _references.Add(new Reference(r.Target, scope));
                return;
            case MExpr.Add a:
                WalkExpr(a.Left, scope);
                WalkExpr(a.Right, scope);
                return;
            case MExpr.Group g:
                foreach (var item in g.Items)
                    WalkExpr(item, scope);
                return;
            case MExpr.Spread s:
                WalkExpr(s.Operand, scope);
                return;
            case MExpr.Call c:
                _references.Add(new Reference(c.Callee, scope));
                foreach (var arg in c.Args)
                    WalkExpr(arg, scope);
                return;
            case MExpr.If i:
                WalkExpr(i.Cond, scope);
                WalkExpr(i.Then, scope);
                WalkExpr(i.Else, scope);
                return;
            case MExpr.Brace b:
            {
                var inner = NewScope(scope, "brace");
                WalkScope(b.Scope, inner);
                return;
            }

            case MExpr.Dot d:
                WalkExpr(d.Receiver, scope);
                foreach (var arg in d.Args ?? [])
                    WalkExpr(arg, scope);
                return;
            case MExpr.Select s:
                WalkExpr(s.Receiver, scope);
                foreach (var selector in s.Selectors)
                    WalkExpr(selector, scope);
                return;
            case MExpr.ListLit l:
                foreach (var item in l.Items)
                    WalkExpr(item, scope);
                return;
            case MExpr.Prim p:
                foreach (var arg in p.Args)
                    WalkExpr(arg, scope);
                return;
            case MExpr.Binary bin:
                WalkExpr(bin.Left, scope);
                WalkExpr(bin.Right, scope);
                return;

            default:
                throw new InvalidOperationException($"Unhandled expr kind {expr.GetType().Name}");
        }
    }

    /// <summary>Nearest-declaration resolution of a NAME from a scope, mirroring
    /// lexical ownership-first lookup over the generated subset (no opens, no
    /// dot access, no prelude collisions — generated names never collide with
    /// prelude/builtin names by the naming pool's construction).</summary>
    private static Sym? ResolveName(string name, ScopeNode from, IReadOnlyDictionary<Sym, string> names)
    {
        for (var scope = from; scope is not null; scope = scope.Parent)
        {
            foreach (var declared in scope.Declared)
            {
                if (names[declared] == name)
                    return declared;
            }
        }

        return null;
    }

    public void ValidateNaming(IReadOnlyDictionary<Sym, string> names)
    {
        foreach (var scope in _scopes)
        {
            var seen = new Dictionary<string, Sym>(StringComparer.Ordinal);
            foreach (var declared in scope.Declared)
            {
                var name = names[declared];
                if (seen.TryGetValue(name, out var other))
                {
                    throw new InvalidOperationException(
                        $"Naming map invalid: {other} and {declared} both render as '{name}' in scope {scope.Info.Id} ({scope.Info.Label}).");
                }

                seen[name] = declared;
            }
        }

        foreach (var reference in _references)
        {
            var name = names[reference.Target];
            var resolved = ResolveName(name, reference.InScope, names);
            if (resolved != reference.Target)
            {
                throw new InvalidOperationException(
                    $"Naming map invalid: a reference to {reference.Target} ('{name}') from scope "
                    + $"{reference.InScope.Info.Id} ({reference.InScope.Info.Label}) would resolve to "
                    + $"{(resolved is null ? "nothing" : resolved.ToString())} — rendering would change the binding graph.");
            }
        }
    }

    /// <summary>True when renaming <paramref name="target"/> to
    /// <paramref name="newName"/> keeps the whole binding graph intact.</summary>
    public bool RenameKeepsBindings(Sym target, string newName, IReadOnlyDictionary<Sym, string> names)
    {
        var candidate = new Dictionary<Sym, string>(names) { [target] = newName };
        try
        {
            ValidateNaming(candidate);
            return true;
        }
        catch (InvalidOperationException)
        {
            return false;
        }
    }

    public string Describe(IReadOnlyDictionary<Sym, string> names)
    {
        var sb = new StringBuilder();
        foreach (var scope in _scopes)
        {
            sb.Append("  S").Append(scope.Info.Id);
            if (scope.Info.ParentId is { } parent)
                sb.Append("(parent S").Append(parent).Append(')');
            sb.Append(" [").Append(scope.Info.Label).Append("]:");
            if (scope.Declared.Count == 0)
                sb.Append(" (no decls)");
            foreach (var declared in scope.Declared)
                sb.Append(' ').Append(declared).Append("→'").Append(names[declared]).Append('\'');
            sb.AppendLine();
        }

        foreach (var reference in _references)
        {
            sb.Append("  ref ").Append(reference.Target)
                .Append(" ('").Append(names[reference.Target])
                .Append("') from S").Append(reference.InScope.Info.Id).AppendLine();
        }

        return sb.ToString();
    }
}

/// <summary>
/// Renders a model program to KatLang source. Rendering respects the surface
/// rules the deterministic campaigns pinned: definition bodies are line-bounded
/// (single-line unless the body is a brace, whose delimiter keeps it open);
/// one-item plain parens are never emitted (parse-time unwrap) — only
/// <c>(spread*)</c> groups keep a one-item form; declarations render before
/// rows in every scope so references never depend on declaration order.
/// The generator closes every spread explicitly rather than relying on the
/// end of a line (issue #183: an attached line-final <c>*</c> also ends its
/// row, a detached one multiplies). A spread ROW followed by another row is
/// closed with a trailing comma
/// (<c>X*,</c> newline <c>Y</c> — the same two slots); every root has a real
/// following control row. Every spread-ending declaration closes explicitly:
/// a brace body for definitions
/// (<c>F(x) = { x* }</c>, merged into the definition exactly like the bare
/// body) and capture parentheses for a deconstruction right-hand side
/// (<c>x, y = (V*)</c>, the capture the deconstruction performs anyway).
/// </summary>
public static class StructuralRenderer
{
    public static string Render(StructuralProgram program)
    {
        var sb = new StringBuilder();
        RenderScopeItems(program.Root, program.Names, sb, indent: 0);
        return sb.ToString();
    }

    private static void RenderScopeItems(
        MScope scope, IReadOnlyDictionary<Sym, string> names, StringBuilder sb, int indent)
    {
        var first = true;
        for (var d = 0; d < scope.Decls.Count; d++)
        {
            NewLine(sb, indent, ref first);
            // A later declaration and EOF never close a spread. The same-line
            // brace or capture closer does, without changing the body value.
            RenderDecl(scope.Decls[d], names, sb, indent, closeTrailingSpread: true);
        }

        for (var r = 0; r < scope.Rows.Count; r++)
        {
            NewLine(sb, indent, ref first);
            RenderExpr(scope.Rows[r], names, sb, indent);
            if (scope.Rows[r] is MExpr.Spread && r < scope.Rows.Count - 1)
                sb.Append(',');
        }
    }

    /// <summary>
    /// Renders one definition body: bare on its line, or as a brace body when
    /// <paramref name="closeTrailingSpread"/> is set and the body's last row is
    /// a spread (the brace algorithm is merged into the definition at parse
    /// time, so the tree is the same as the bare body's).
    /// </summary>
    private static void RenderBodyRows(
        IReadOnlyList<MExpr> rows, IReadOnlyDictionary<Sym, string> names, StringBuilder sb, int indent, bool closeTrailingSpread)
    {
        var brace = closeTrailingSpread && rows[^1] is MExpr.Spread;
        if (brace) sb.Append("{ ");
        for (var i = 0; i < rows.Count; i++)
        {
            if (i > 0) sb.Append(", ");
            RenderExpr(rows[i], names, sb, indent);
        }

        if (brace) sb.Append(" }");
    }

    private static void NewLine(StringBuilder sb, int indent, ref bool first)
    {
        if (!first)
            sb.Append('\n');
        sb.Append(new string(' ', indent * 2));
        first = false;
    }

    private static void RenderDecl(
        MDecl decl, IReadOnlyDictionary<Sym, string> names, StringBuilder sb, int indent, bool closeTrailingSpread)
    {
        switch (decl)
        {
            case MDecl.Value v:
                sb.Append(names[v.Symbol]).Append(" = ");
                RenderBodyRows(v.Rows, names, sb, indent, closeTrailingSpread);
                return;
            case MDecl.Func f:
                sb.Append(names[f.Symbol]).Append('(');
                for (var i = 0; i < f.Params.Count; i++)
                {
                    if (i > 0) sb.Append(", ");
                    if (f.Params[i].Meta) sb.Append("meta ");
                    if (f.Params[i].Collecting) sb.Append('*');
                    sb.Append(names[f.Params[i].Symbol]);
                }

                sb.Append(") = ");
                RenderBodyRows([f.Body], names, sb, indent, closeTrailingSpread);
                return;
            case MDecl.Family fam:
            {
                var firstClause = true;
                for (var c = 0; c < fam.Clauses.Count; c++)
                {
                    var clause = fam.Clauses[c];
                    if (!firstClause)
                    {
                        sb.Append('\n').Append(new string(' ', indent * 2));
                    }

                    firstClause = false;
                    sb.Append(names[fam.Symbol]).Append('(');
                    RenderPattern(clause.Pattern, names, sb);

                    sb.Append(") = ");
                    RenderBodyRows([clause.Body], names, sb, indent, closeTrailingSpread);
                }

                return;
            }

            case MDecl.SeqPatternFunc sp:
                sb.Append(names[sp.Symbol]).Append(sp.ListPattern ? "([" : "((");
                for (var i = 0; i < sp.Binders.Count; i++)
                {
                    if (i > 0) sb.Append(", ");
                    if (sp.Binders[i].Collecting) sb.Append('*');
                    sb.Append(names[sp.Binders[i].Symbol]);
                }

                sb.Append(sp.ListPattern ? "]) = " : ")) = ");
                RenderBodyRows([sp.Body], names, sb, indent, closeTrailingSpread);
                return;
            case MDecl.Deconstruction d:
                for (var i = 0; i < d.Binders.Count; i++)
                {
                    if (i > 0) sb.Append(", ");
                    if (d.Binders[i].Collecting) sb.Append('*');
                    sb.Append(names[d.Binders[i].Symbol]);
                }

                sb.Append(" = ");
                // A deconstruction right-hand side is captured into one shared
                // value anyway, so explicit capture parentheses close a
                // spread-ending right-hand side without changing what is bound.
                var captureRhs = closeTrailingSpread && d.Rhs is MExpr.Spread;
                if (captureRhs) sb.Append('(');
                RenderExpr(d.Rhs, names, sb, indent);
                if (captureRhs) sb.Append(')');
                return;
            default:
                throw new InvalidOperationException($"Unhandled decl kind {decl.GetType().Name}");
        }
    }

    private static void RenderPattern(MPattern pattern, IReadOnlyDictionary<Sym, string> names, StringBuilder sb)
    {
        switch (pattern)
        {
            case MPattern.Literal literal:
                sb.Append(FormatAtom(literal.Value));
                break;
            case MPattern.Binder binder:
                sb.Append(names[binder.Symbol]);
                break;
            case MPattern.Collecting collecting:
                sb.Append('*').Append(names[collecting.Symbol]);
                break;
            case MPattern.LiteralPair pair:
                sb.Append(FormatAtom(pair.First)).Append(", ").Append(FormatAtom(pair.Second));
                break;
            case MPattern.Structure structure:
                sb.Append(structure.IsList ? '[' : '(');
                for (var i = 0; i < structure.Items.Count; i++)
                {
                    if (i > 0) sb.Append(", ");
                    RenderPattern(structure.Items[i], names, sb);
                }
                sb.Append(structure.IsList ? ']' : ')');
                break;
            default:
                throw new InvalidOperationException($"Unhandled pattern {pattern.GetType().Name}");
        }
    }

    private static void RenderExpr(MExpr expr, IReadOnlyDictionary<Sym, string> names, StringBuilder sb, int indent)
    {
        switch (expr)
        {
            case MExpr.Atom a:
                sb.Append(FormatAtom(a.Value));
                return;
            case MExpr.Bool flag:
                sb.Append(flag.Value ? "true" : "false");
                return;
            case MExpr.Ref r:
                sb.Append(names[r.Target]);
                return;
            case MExpr.Add add:
                // Only a SEM-2B Binary operand needs grouping; the original corpus never
                // builds one, so its rendering is unchanged.
                RenderOperand(add.Left, add.Left is MExpr.Binary, names, sb, indent);
                sb.Append(" + ");
                RenderOperand(add.Right, add.Right is MExpr.Binary, names, sb, indent);
                return;
            case MExpr.Binary bin:
                RenderOperand(bin.Left, bin.Left is MExpr.Add or MExpr.Binary, names, sb, indent);
                sb.Append(' ').Append(bin.Operator).Append(' ');
                RenderOperand(bin.Right, bin.Right is MExpr.Add or MExpr.Binary, names, sb, indent);
                return;
            case MExpr.Dot d:
                RenderOperand(d.Receiver, d.Receiver is MExpr.Add or MExpr.Binary or MExpr.Spread, names, sb, indent);
                sb.Append('.').Append(d.Member);
                if (d.Args is { } dotArgs)
                    RenderArgs(dotArgs, names, sb, indent);
                return;
            case MExpr.Select sel:
                RenderOperand(sel.Receiver, sel.Receiver is MExpr.Add or MExpr.Binary or MExpr.Spread, names, sb, indent);
                sb.Append('[');
                for (var i = 0; i < sel.Selectors.Count; i++)
                {
                    if (i > 0) sb.Append(", ");
                    RenderExpr(sel.Selectors[i], names, sb, indent);
                }

                sb.Append(']');
                return;
            case MExpr.ListLit list:
                sb.Append('[');
                for (var i = 0; i < list.Items.Count; i++)
                {
                    if (i > 0) sb.Append(", ");
                    RenderExpr(list.Items[i], names, sb, indent);
                }

                sb.Append(']');
                return;
            case MExpr.Prim prim:
                sb.Append(prim.Name);
                RenderArgs(prim.Args, names, sb, indent);
                return;
            case MExpr.Group g:
                if (g.Items.Count == 1 && g.Items[0] is not MExpr.Spread)
                {
                    throw new InvalidOperationException(
                        "Model invalid: a one-item plain group would unwrap at parse; only (spread*) groups may have one item.");
                }

                sb.Append('(');
                for (var i = 0; i < g.Items.Count; i++)
                {
                    if (i > 0) sb.Append(", ");
                    RenderExpr(g.Items[i], names, sb, indent);
                }

                sb.Append(')');
                return;
            case MExpr.Spread s:
                if (s.Operand is MExpr.Binary)
                {
                    // SEM-2B: `(1 / 0)*` — redundant grouping makes an operator operand attachable.
                    RenderOperand(s.Operand, group: true, names, sb, indent);
                    sb.Append('*');
                    return;
                }

                if (s.Operand is not (MExpr.Ref or MExpr.Group or MExpr.Call or MExpr.Dot or MExpr.Select))
                {
                    throw new InvalidOperationException(
                        $"Model invalid: spread operand {s.Operand.GetType().Name} is not a marker-attachable form.");
                }

                RenderExpr(s.Operand, names, sb, indent);
                sb.Append('*');
                return;
            case MExpr.Call c:
                sb.Append(names[c.Callee]).Append('(');
                for (var i = 0; i < c.Args.Count; i++)
                {
                    if (i > 0) sb.Append(", ");
                    RenderExpr(c.Args[i], names, sb, indent);
                }

                sb.Append(')');
                return;
            case MExpr.If i:
                sb.Append("if(");
                RenderExpr(i.Cond, names, sb, indent);
                sb.Append(", ");
                RenderExpr(i.Then, names, sb, indent);
                sb.Append(", ");
                RenderExpr(i.Else, names, sb, indent);
                sb.Append(')');
                return;
            case MExpr.Brace b:
                sb.Append("{\n");
                RenderScopeItems(b.Scope, names, sb, indent + 1);
                if (b.Scope.Rows.Count > 0 && b.Scope.Rows[^1] is MExpr.Spread)
                    sb.Append(" }");
                else
                    sb.Append('\n').Append(new string(' ', indent * 2)).Append('}');
                return;
            case MExpr.IndexErr:
                sb.Append("(1, 2)[9]");
                return;
            default:
                throw new InvalidOperationException($"Unhandled expr kind {expr.GetType().Name}");
        }
    }

    /// <summary>An operand, inside REDUNDANT parentheses when <paramref name="group"/> is set
    /// (a one-expression group the parser erases, so the tree is the bare operand's).</summary>
    private static void RenderOperand(
        MExpr operand, bool group, IReadOnlyDictionary<Sym, string> names, StringBuilder sb, int indent)
    {
        if (group) sb.Append('(');
        RenderExpr(operand, names, sb, indent);
        if (group) sb.Append(')');
    }

    private static void RenderArgs(
        IReadOnlyList<MExpr> args, IReadOnlyDictionary<Sym, string> names, StringBuilder sb, int indent)
    {
        sb.Append('(');
        for (var i = 0; i < args.Count; i++)
        {
            if (i > 0) sb.Append(", ");
            RenderExpr(args[i], names, sb, indent);
        }

        sb.Append(')');
    }

    private static string FormatAtom(Decimal128 value)
        => value.ToString(System.Globalization.CultureInfo.InvariantCulture);
}
