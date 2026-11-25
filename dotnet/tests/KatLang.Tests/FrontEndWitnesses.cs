using System.Text;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>One member of a front-end witness: the base program or one of its two transformations.</summary>
internal sealed record FrontEndWitnessMember(string Id, string Role, string Source);

/// <summary>
/// One FRONT-END WITNESS of <see cref="FrontEndDecisionCorpus"/>: a small program written to show decisions the four
/// differential corpora leave unshown or show under one spelling only — the role formula lifting gives a slot of each
/// callee kind, a refused forward that names one binding, the by-shape supply.
///
/// <para>A witness is written as its root declarations and its root rows, so that it has the member relation of the
/// SEM-2B generated corpus (<c>SemanticCorpus</c>): the BASE program, its ALPHA-RENAME (every name the program declares
/// or infers, renamed by name to a fresh pool <c>w1, w2, …</c> in order of first appearance) and its
/// DECLARATION-REORDER (the root declarations reversed). A front-end decision is a decision about bindings, so both
/// transformations must leave every one of them standing: <c>FrontEndDecisionLeanArtifactTests</c> requires the three
/// members to show the same decisions, name for name, and the generated artifact guards each member on its own.</para>
///
/// <para>The SEM-2B tick callbacks expose callable slots. The witnesses also expose value slots,
/// lifted references and refused forwards. The front-end decision census in the formal correspondence
/// ledger records the coverage of both corpora.</para>
/// </summary>
internal sealed record FrontEndWitness(string Id, string Shows, IReadOnlyList<string> Declarations, string Rows)
{
    /// <summary>The base program: the declarations in written order, then the rows.</summary>
    public string Source => Render(Declarations);

    /// <summary>The base member, then its alpha-rename and its declaration-reorder.</summary>
    public IReadOnlyList<FrontEndWitnessMember> Members =>
    [
        new(Id, SemanticMember.BaseRole, Source),
        new($"{Id}/{SemanticMember.AlphaRenameRole}", SemanticMember.AlphaRenameRole, AlphaRename(Source, RenameMap)),
        new($"{Id}/{SemanticMember.DeclarationReorderRole}", SemanticMember.DeclarationReorderRole, Render(Declarations.Reverse())),
    ];

    /// <summary>
    /// The alpha-rename's name map: every name the base program binds — a property, a written parameter, a clause
    /// binder, an inferred parameter — to <c>w1, w2, …</c> in order of its first appearance in the source.
    /// </summary>
    public IReadOnlyDictionary<string, string> RenameMap
    {
        get
        {
            var parsed = Parser.ParseSyntax(Source);
            if (parsed.HasErrors)
                throw new InvalidOperationException($"the witness '{Id}' does not parse.");
            var bound = new BoundNames();
            bound.VisitAlgorithm(ParameterDetector.DetectPrevalidated(parsed.Root).Root);

            var map = new Dictionary<string, string>(StringComparer.Ordinal);
            foreach (var name in IdentifierTokens(Source).Select(token => Source.Substring(token.Position, token.Length)))
            {
                if (bound.Names.Contains(name) && !map.ContainsKey(name))
                    map.Add(name, $"w{map.Count + 1}");
            }

            if (map.Count != bound.Names.Count)
                throw new InvalidOperationException($"the witness '{Id}' binds a name its source never writes.");
            return map;
        }
    }

    private string Render(IEnumerable<string> declarations) => string.Join("\n", [.. declarations, Rows]);

    /// <summary>Every identifier token that spells a mapped name, replaced: a name is renamed wherever it is written.</summary>
    internal static string AlphaRename(string source, IReadOnlyDictionary<string, string> map)
    {
        var renamed = new StringBuilder(source);
        foreach (var token in IdentifierTokens(source).Reverse())
        {
            if (map.TryGetValue(source.Substring(token.Position, token.Length), out var fresh))
                renamed.Remove(token.Position, token.Length).Insert(token.Position, fresh);
        }

        return renamed.ToString();
    }

    private static IEnumerable<Token> IdentifierTokens(string source)
        => Lexer.Tokenize(source).Tokens.Where(static token => token.Kind == TokenKind.Identifier);

    private sealed class BoundNames : AstWalker
    {
        public HashSet<string> Names { get; } = new(StringComparer.Ordinal);

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            foreach (var property in algorithm.Properties)
            {
                if (property.Name is { } name)
                    Names.Add(name);
            }

            switch (algorithm)
            {
                case Algorithm.User user:
                    Names.UnionWith(user.Parameters.Select(static parameter => parameter.Name));
                    break;

                case Algorithm.Conditional family:
                    foreach (var branch in family.Branches)
                        Names.UnionWith(branch.Pattern.BoundNamesExpandingSharedNodesOnce());
                    break;
            }

            base.VisitAlgorithm(algorithm);
        }
    }
}

/// <summary>The front-end witnesses, in the order the artifact holds them.</summary>
internal static class FrontEndWitnesses
{
    public static IReadOnlyList<FrontEndWitness> All { get; } =
    [
        // ── Slot roles by callee kind ────────────────────────────────────────────────────────────────────────────────
        new("family-argument-is-a-value",
            "a clause family gives every argument the VALUE role: `Inc` is lifted at its position 1",
            ["Inc(x) = x + 1", "Pick(0, v) = 0\nPick(n, v) = v", "Use = Pick(1, Inc)"],
            "Use(4)"),

        new("user-argument-keeps-the-callable",
            "a user callable leaves an argument its CALLABLE identity: `Inc` stays bare in an inferring body",
            ["Inc(x) = x + 1", "Apply(f, v) = f(v)", "Use = Apply(Inc, 4)",
                "ViaOpen = {\n    open { public Keep(f) = f(1) }\n    Keep(Inc)\n}"],
            "Use"),

        new("dynamic-callee-keeps-the-callable",
            "a callee known only at run time (a parameter) leaves an argument CALLABLE: `Inc` stays bare in a closed body "
            + "whose own list binds the one name it requests, so nothing but the role keeps it",
            ["Inc(x) = x + 1", "Run(g) = g(5)", "Twice(f, x) = f(Inc)"],
            "Twice(Run, 3)"),

        new("strict-value-argument-is-a-value",
            "a Math argument takes a value role, shown by a lift of Inc and by the resolver's diagnostic on an unnameable family",
            ["Inc(x) = x + 1", "Lit(0) = 0\nLit(1) = 1", "Use = abs(Inc)", "Rejected = abs(Lit)"],
            "Use(-5)"),

        new("alias-takes-its-targets-kind",
            "a callable alias has no kind of its own (X-45): through `Abs = abs` the argument is a value and is lifted, "
            + "through `Held = Keep` it keeps its callable identity",
            ["Inc(x) = x + 1", "Keep(f) = f(1)", "Abs = abs", "Held = Keep", "Lifted = Abs(Inc)", "Kept = Held(Inc)"],
            "Lifted(-9), Kept"),

        new("spread-ends-known-positions",
            "after a written spread a position is unknown: `reduce`'s initial value is lifted at its known position 2 and "
            + "kept after a spread, while `take`, every position of which is a value, lifts after a spread too",
            ["Add(a, b) = a + b", "Inc(x) = x + 1", "Items = 1, 2, 3", "Late = reduce(Items*, Add, Inc)",
                "Wide = take(Items*, Inc)", "Early = reduce(Items, Add, Inc)"],
            "Early(0)"),

        new("fallback-receiver-is-slot-zero",
            "a selected fallback `R.F(args)` is the call `F(R, args)`: the receiver `Inc` keeps its callable identity under "
            + "the user callable `Apply` and is lifted under the family `Pick`",
            ["Inc(x) = x + 1", "Apply(f, v) = f(v)", "Pick(f, 0) = 0\nPick(f, n) = f + n", "Kept = Inc.Apply(4)", "Lifted = Inc.Pick(2)"],
            "Kept, Lifted(1)"),

        new("runtime-receiver-decides-nothing",
            "an edge whose receiver is a parameter is decided at run time: its argument is a dynamic callee's and `Inc` "
            + "stays bare, in a closed body that binds the name it requests",
            ["Inc(x) = x + 1", "Go(r, f) = f(r)", "Use(p, x) = p.Go(Inc)"],
            "Use(5, 0)"),

        // ── Refused forwards ─────────────────────────────────────────────────────────────────────────────────────────
        new("one-unbound-name-among-several",
            "a closed body's operand stays bare, and of the two names its callee requests the body binds `x`: the refusal "
            + "is `k`'s alone",
            ["Scale(x, k) = x * k", "Use(x) = Scale + 0"],
            "Use(3)"),

        new("two-unbound-names-share-one-refusal",
            "the same operand in a body that binds neither name: one bare reference, two unbound names, and nothing in "
            + "the output divides the refusal between them",
            ["Scale(x, k) = x * k", "Use(p) = Scale + 0"],
            "Use(3)"),

        new("bare-forwarding-reports-each-parameter",
            "a closed lone row forwards by name and reports each parameter it cannot supply on its own: `q` and `r`",
            ["Mix(p, q, r) = p + q + r", "Use(p) = Mix"],
            "Use(1)"),

        new("member-calls-and-bare-forwarding",
            "a selected member determines the argument role in either call spelling; a bare member row can report both a missing name and a pattern mismatch",
            ["Inc(x) = x + 1", "Lib = { public Mix(p, [pair], q) = p }", "Kept = Lib.Mix(Inc, [0], 1)",
                "AlsoKept = (Lib.Mix)(Inc, [0], 1)", "Lifted = Math.Abs(Inc)", "Use(p) = Lib.Mix"],
            "Use(1)"),

        // ── The by-shape supply (FD-F1) ──────────────────────────────────────────────────────────────────────────────
        new("by-shape-supply-under-two-names",
            "FD-F1: a caller whose whole list is one collector re-supplies a callee whose whole list is one list group "
            + "holding a lone collector, whatever the two are named",
            ["Get([*xs]) = xs.count", "Use(*items) = [Get][0]"],
            "Use(3, 4)"),

        new("by-shape-supply-of-a-sequence-group",
            "FD-F1 for the other group kind: `Sum((*xs))` is re-supplied as `Sum((items*))`",
            ["Sum((*xs)) = xs.sum", "Use(*items) = Sum + 0"],
            "Use(3, 4)"),

        new("by-shape-supply-under-one-name",
            "the same supply where caller and callee spell the collector alike: by name and by shape give one answer",
            ["Get([*xs]) = xs.count", "Use(*xs) = [Get][0]"],
            "Use(3, 4)"),

        new("by-shape-supply-beside-an-enclosing-binding",
            "FD-F2: an enclosing parameter binds the callee's name, so forwarding by name would read it, and the caller's "
            + "own collector is supplied by shape instead",
            ["Get([*xs]) = xs.count", "Outer(*xs) = {\n    Use(*items) = [Get][0]\n    Use(3, 4)\n}"],
            "Outer(1, 2, 3)"),
    ];
}
