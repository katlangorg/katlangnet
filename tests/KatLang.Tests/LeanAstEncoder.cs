using System.Globalization;
using System.Numerics;
using System.Text;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Prints an elaborated C# AST in the Lean constructor syntax used by the
/// generated differential artifacts <c>lean/SemanticExplorerCases.lean</c> and
/// <c>lean/LanguageSpecCases.lean</c>.
///
/// <para>
/// Track 9 found a corpus-fidelity defect where a hand-written Lean program
/// declared <c>publicProp "X"</c> for source that actually elaborates <c>X</c>
/// as PRIVATE, so 109 differential cases compared structurally different
/// programs. This encoder exists so a differential case's Lean program can be
/// PRODUCED from the source's real elaborated AST instead of transcribed by
/// eye: both corpora now derive every Lean-representable case's program
/// through <see cref="EncodeProgram"/> (see <c>SemanticExplorerCorpus</c> and
/// <c>LanguageSpecCorpus</c>), and <c>OpenVisibilityCorpusFidelityTests</c> +
/// <c>LeanAstEncoderTests</c> pin the encoding itself against manually
/// reviewed golden text.
/// </para>
///
/// <para>
/// Coverage is deliberately bounded to the Lean-modeled elaborated surface:
/// anything else throws rather than printing something plausible but wrong —
/// an encoder that silently approximated would reintroduce the very defect it
/// guards against. The deliberate exclusions are <see cref="Expr.Grace"/>
/// (front-end elaboration consumes and strips it, so no elaborated tree
/// contains one), <see cref="Expr.NativeCall"/> (it exists only inside
/// prelude/host wrapper bodies, never inside a source program's AST; the Lean
/// core deliberately does not model natives), and
/// <see cref="Algorithm.Builtin"/> (a prelude member, likewise never part of
/// a source program). Numbers must be integer-valued AND render as plain integers
/// (the Lean core is <c>Int</c>; the runtime keeps Decimal128 quantum, so
/// <c>1.0</c> is refused) and strings must be control-character-free; both are
/// validated fail-loud.
/// </para>
///
/// <para>
/// HOST-DIFF-1: a host-built AST may carry PRE-WIRED parent scopes
/// (<see cref="Algorithm.User.Parent"/>, <see cref="Algorithm.Conditional.Parent"/>,
/// <see cref="Algorithm.Alias.Parent"/>, each a finite <see cref="ScopeCtx"/> chain). Such an
/// algorithm encodes as <c>Algorithm.withParent (some scope) …</c> over its ordinary encoding, the
/// scope as the ownerless <c>ScopeCtx.mk</c> level it is (see <c>EncodeScope</c>), inner to outer;
/// an unwired algorithm keeps its exact former text. The sharing pre-pass walks parent scopes too,
/// and a property declared in a host level gets its shared identity per SCOPE OBJECT, so one
/// object reached twice is one Lean declaring scope and two record-equal objects are two. The
/// deliberate boundaries: evaluator-created scopes (internal owner/activation state) are refused,
/// a cyclic or over-deep graph is refused by the evaluator's own structural preflight, and the
/// residual HOST-LEAN-O6 shapes Lean cannot represent with per-object property identities alone
/// (empty host levels as open-provider identity, O6-18; the C# pass-through inconsistency
/// O6-11x awaiting owner decision OD-1) are pinned as machine-checked divergence fixtures in
/// <c>HostParentDifferentialCorpus</c>, never as green comparisons.
/// </para>
/// </summary>
public static class LeanAstEncoder
{
    public static string EncodeProgram(Algorithm root)
    {
        var encoding = new LeanAstEncoding(root);
        return encoding.Complete(encoding.EncodeProgram(root));
    }
    public static string EncodeAlgorithm(Algorithm algorithm)
    {
        var encoding = new LeanAstEncoding(algorithm);
        return encoding.Complete(encoding.EncodeAlgorithm(algorithm));
    }
    public static string EncodeExpr(Expr expression)
    {
        var encoding = new LeanAstEncoding(expression);
        return encoding.Complete(encoding.EncodeExpr(expression));
    }
    public static string EncodeProperty(Property property)
    {
        var encoding = new LeanAstEncoding(property.Value);
        return encoding.Complete(encoding.EncodeProperty(property));
    }
    public static string EncodePattern(Pattern pattern) => LeanAstEncoding.EncodePattern(pattern);

    /// <summary>
    /// A Lean string literal with exactly <paramref name="value"/>'s text (the encoder's own
    /// spelling): how a generated <c>#guard</c> embeds an expected neutral observation, so a
    /// string result holding a quote, a backslash, a line feed or a tab stays faithful.
    /// </summary>
    public static string QuoteString(string value) => LeanAstEncoding.Quote(value);
}

internal sealed class LeanAstEncoding
{
    private readonly SharedDeclarations _sharing = new();
    // Keyed by the C# owner identity, so an ownerless host ANCESTOR of the owner counts by object
    // reference (HOST-NESTED-1): owned declarations under two distinct host objects get distinct ids.
    // Empty or opens-only host levels still carry no Lean token of their own (O6-18, HP-14b).
    private readonly Dictionary<StructuralOwnerIdentity, Dictionary<Property, int>> _identities = new();
    // HOST-DIFF-1: a property declared directly in a host-built (ownerless) ScopeCtx level is one
    // C# binding PER SCOPE OBJECT (CACHE-OWNER-D3 / HOST-ALIAS-R14 key that level by reference), so
    // its shared Lean identity is allocated per (scope object, property object), never per
    // record-equal scope content.
    private readonly Dictionary<ScopeCtx, Dictionary<Property, int>> _hostScopeIdentities =
        new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<DeclarationIdentity, int> _algorithmIdentities = new();
    private int _nextIdentity;
    private ScopeCtx? _scope;
    private readonly bool _compact;
    private readonly object _globalContext = new();
    private readonly Dictionary<object, Dictionary<object, string>> _terms = new(ReferenceEqualityComparer.Instance);
    private readonly List<string> _definitions = [];

    public LeanAstEncoding(Algorithm root)
    {
        RequireAdmissibleGraph(root);
        _compact = NeedsCompactTerms(root);
        _sharing.VisitAlgorithm(root);
    }

    public LeanAstEncoding(Expr root)
    {
        RequireAdmissibleGraph(root);
        _compact = NeedsCompactTerms(root);
        _sharing.VisitExpr(root);
    }

    // Keep existing small and source-derived goldens byte-identical. Large host graphs use Lean
    // let terms: expanding a diamond into a tree costs exponentially more than its input graph.
    // This bottom-up estimate saturates, visits each graph node once, and never prints the tree.
    private static bool NeedsCompactTerms(object root)
    {
        const int InlineWorkLimit = 4096;
        var sizes = new Dictionary<object, int>(ReferenceEqualityComparer.Instance);
        var frames = new Stack<(object Node, int Next, int Size)>();
        frames.Push((root, 0, 1));
        var hasHost = false;
        var joins = 0;
        while (frames.TryPop(out var frame))
        {
            if (!AstStructuralPreflight.TryGetChild(frame.Node, frame.Next, out var child))
            {
                sizes[frame.Node] = frame.Size;
                hasHost |= frame.Node is ScopeCtx;
                if (frame.Node is Expr.SequenceConstruct or Expr.SequenceSpread) joins++;
                continue;
            }
            if (!sizes.TryGetValue(child, out var size))
            {
                frames.Push(frame);
                frames.Push((child, 0, 1));
            }
            else frames.Push((frame.Node, frame.Next + 1, Math.Min(InlineWorkLimit + 1, frame.Size + size)));
        }
        // Join spines have zero evaluator depth and may be arbitrarily long, even without hosts.
        return (hasHost && sizes[root] > InlineWorkLimit) || joins > EvaluationLimits.MaxSupportedAstDepth;
    }

    public string Complete(string body) => _definitions.Count == 0 ? body : $"({string.Concat(_definitions)}{body})";

    private object CurrentContext => (object?)_scope ?? _globalContext;

    private string Term(object node, object context, string type, Func<string> encode)
    {
        if (!_compact) return encode();
        if (!_terms.TryGetValue(node, out var contexts))
            _terms[node] = contexts = new(ReferenceEqualityComparer.Instance);
        if (contexts.TryGetValue(context, out var known)) return known;
        var value = encode();
        var name = $"hd{_definitions.Count}";
        _definitions.Add($"let {name} : {type} := {value}; ");
        contexts[context] = name;
        return name;
    }

    // AstWalker is recursive through internal join nodes. Match the evaluator's accepted domain
    // with an explicit stack here too; every non-join subtree still uses the ordinary visitor.
    private static void WalkJoinSpine(Expr root, HashSet<Expr> visited, Action<Expr> visitLeaf, Action<Expr> visitRepeated)
    {
        var pending = new Stack<Expr>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (node is not (Expr.SequenceConstruct or Expr.SequenceSpread)) { visitLeaf(node); continue; }
            if (!visited.Add(node)) { visitRepeated(node); continue; }
            if (node is Expr.SequenceConstruct join) { pending.Push(join.Right); pending.Push(join.Left); }
            else pending.Push(((Expr.SequenceSpread)node).Operand);
        }
    }

    /// <summary>
    /// The encoder walks the graph recursively (the sharing pre-pass, then the printer), parent
    /// scopes included, so it first runs the evaluator's own iterative structural preflight over
    /// the same graph: a reference cycle (possible through caller-owned collections, for instance
    /// a host scope whose property is pre-wired back to that scope) or an over-deep graph is
    /// refused with a bounded, precise error instead of overflowing the stack. Zero-weight join
    /// spines use explicit stacks in both sharing walks and the printer; large host DAGs use
    /// context-qualified Lean let terms. Unsupported semantic payloads are still refused below.
    /// </summary>
    private static void RequireAdmissibleGraph(object root)
    {
        if (AstStructuralPreflight.Check(root, EvaluationLimits.MaxSupportedAstDepth,
                AstConsumerProfile.EvaluatorIterativeJoinSpines) is { } rejection)
        {
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} cannot encode a graph the evaluator's structural preflight refuses " +
                $"({rejection.Kind}); a cyclic or over-deep host graph has no finite Lean term.");
        }
    }

    private int DeclarationIdentity(Property property, Algorithm owner)
    {
        // Lean withParent: the owner as wired under the current scope, narrowed to the variant
        // that has a parent (a builtin never owns a property, but the switch stays total).
        Algorithm rewiredOwner = owner switch
        {
            Algorithm.User user => user with { Parent = _scope?.Parent },
            Algorithm.Conditional family => family with { Parent = _scope?.Parent },
            Algorithm.Alias alias => alias with { Parent = _scope?.Parent },
            Algorithm.Builtin => owner,
        };
        var scopeIdentity = StructuralOwnerIdentity.FromOwner(rewiredOwner);
        if (!_identities.TryGetValue(scopeIdentity, out var byProperty))
            _identities[scopeIdentity] = byProperty = new(ReferenceEqualityComparer.Instance);
        if (!byProperty.TryGetValue(property, out var identity))
            byProperty[property] = identity = _nextIdentity++;
        return identity;
    }

    /// <summary>
    /// The shared Lean identity of <paramref name="property"/> as declared in the host-built level
    /// <paramref name="scope"/>: one per (scope OBJECT, property OBJECT). The same scope reached
    /// twice gives its properties equal ids (C#: one host object is one declaring owner), while two
    /// distinct scope objects that share a property, a property list, or are record <c>with</c>
    /// copies get distinct ids (C#: two objects are two owners), so Lean's structural owner key
    /// separates exactly what C# separates (HOST-LEAN-O6 option C: O6-02..O6-09, O6-16, O6-17).
    /// </summary>
    private int HostDeclarationIdentity(Property property, ScopeCtx scope)
    {
        if (!_hostScopeIdentities.TryGetValue(scope, out var byProperty))
            _hostScopeIdentities[scope] = byProperty = new(ReferenceEqualityComparer.Instance);
        if (!byProperty.TryGetValue(property, out var identity))
            byProperty[property] = identity = _nextIdentity++;
        return identity;
    }

    // Two graph-bounded walks preserve host sharing without confusing equal
    // bodies with one declaration. A repeated subtree marks all its properties.
    // The base AstWalker visits an algorithm's executable children only, never its
    // pre-wired Parent scope chain, so both walks visit parent scopes explicitly
    // (HOST-DIFF-1): a scope's open targets, its properties and its own parent, each
    // scope OBJECT once (reference identity, never record equality: two equal scope
    // objects are two scopes); a scope reached again marks everything under it.
    private sealed class SharedDeclarations : AstWalker
    {
        private readonly HashSet<Algorithm> _algorithms = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<DeclarationIdentity> _declarations = new();
        private readonly HashSet<DeclarationIdentity> _sharedDeclarations = new();
        private readonly HashSet<Expr> _expressions = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<Property> _properties = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<ScopeCtx> _scopes = new(ReferenceEqualityComparer.Instance);
        private readonly SharedMarker _marker = new();
        public bool Contains(Property property) => _marker.Properties.Contains(property);
        public bool Contains(Algorithm algorithm) => _marker.Algorithms.Contains(algorithm)
            || (algorithm.Declaration is { } declaration && _sharedDeclarations.Contains(declaration));
        protected override bool VisitsExplicitParameterDeclarations => false;
        public override void VisitAlgorithm(Algorithm algorithm)
        {
            // A host `with` copy is another object representing the SAME declaration.
            // Visit distinct object graphs normally (copies may have different children),
            // but give every view of a repeated declaration the same Lean shared id.
            if (algorithm.Declaration is { } declaration && !_declarations.Add(declaration))
                _sharedDeclarations.Add(declaration);
            if (_algorithms.Add(algorithm))
            {
                base.VisitAlgorithm(algorithm);
                VisitScope(algorithm.Parent);
            }
            else _marker.VisitAlgorithm(algorithm);
        }
        public override void VisitExpr(Expr expression)
        {
            if (expression is Expr.SequenceConstruct or Expr.SequenceSpread)
            {
                WalkJoinSpine(expression, _expressions, VisitExpr, _marker.VisitExpr);
                return;
            }
            if (_expressions.Add(expression)) base.VisitExpr(expression);
            else _marker.VisitExpr(expression);
        }
        protected override void VisitProperty(Property property)
        {
            if (!_properties.Add(property)) _marker.Properties.Add(property);
            base.VisitProperty(property);
        }
        private void VisitScope(ScopeCtx? scope)
        {
            if (scope is null) return;
            if (!_scopes.Add(scope))
            {
                _marker.VisitScope(scope);
                return;
            }

            foreach (var open in scope.Opens)
                VisitOpenExpression(open);
            foreach (var property in scope.Properties)
                VisitProperty(property);
            VisitScope(scope.Parent);
        }
    }

    private sealed class SharedMarker : AstWalker
    {
        public readonly HashSet<Algorithm> Algorithms = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<Expr> _expressions = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<ScopeCtx> _scopes = new(ReferenceEqualityComparer.Instance);
        public readonly HashSet<Property> Properties = new(ReferenceEqualityComparer.Instance);
        protected override bool VisitsExplicitParameterDeclarations => false;
        public override void VisitAlgorithm(Algorithm algorithm)
        {
            if (Algorithms.Add(algorithm))
            {
                base.VisitAlgorithm(algorithm);
                VisitScope(algorithm.Parent);
            }
        }
        public override void VisitExpr(Expr expression)
        {
            if (expression is Expr.SequenceConstruct or Expr.SequenceSpread)
            {
                WalkJoinSpine(expression, _expressions, VisitExpr, static _ => { });
                return;
            }
            if (_expressions.Add(expression)) base.VisitExpr(expression);
        }
        protected override void VisitProperty(Property property)
        {
            Properties.Add(property);
            base.VisitProperty(property);
        }
        public void VisitScope(ScopeCtx? scope)
        {
            if (scope is null || !_scopes.Add(scope)) return;
            foreach (var open in scope.Opens)
                VisitOpenExpression(open);
            foreach (var property in scope.Properties)
                VisitProperty(property);
            VisitScope(scope.Parent);
        }
    }

    /// <summary>Encodes a parsed root algorithm as a Lean <c>.algorithmExpr (alg ...)</c> program.</summary>
    public string EncodeProgram(Algorithm root) => $".algorithmExpr {EncodeAlgorithm(root)}";

    /// <summary>
    /// Bare encoding, suitable where a delimiter already separates terms (list
    /// elements). Use <see cref="Arg"/> for anything in Lean application
    /// position, which needs parentheses around multi-token terms.
    /// </summary>
    public string EncodeExpr(Expr expr)
        => expr is Expr.SequenceConstruct or Expr.SequenceSpread
            ? EncodeJoinSpine(expr)
            : Term(expr, CurrentContext, "Expr", () => EncodeExprCore(expr));

    private string EncodeJoinSpine(Expr root)
    {
        var context = CurrentContext;
        var encoded = new Dictionary<Expr, string>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<(Expr Node, bool Complete)>();
        pending.Push((root, false));
        while (pending.TryPop(out var frame))
        {
            if (encoded.ContainsKey(frame.Node)) continue;
            if (_compact && _terms.TryGetValue(frame.Node, out var contexts) && contexts.TryGetValue(context, out var known))
            {
                encoded[frame.Node] = known;
                continue;
            }
            if (frame.Node is not (Expr.SequenceConstruct or Expr.SequenceSpread))
            {
                encoded[frame.Node] = EncodeExpr(frame.Node);
                continue;
            }
            if (!frame.Complete)
            {
                pending.Push((frame.Node, true));
                if (frame.Node is Expr.SequenceConstruct join) { pending.Push((join.Right, false)); pending.Push((join.Left, false)); }
                else pending.Push((((Expr.SequenceSpread)frame.Node).Operand, false));
                continue;
            }
            static string Argument(string value) => value.StartsWith('(') ? value : $"({value})";
            var body = frame.Node is Expr.SequenceConstruct construct
                ? $"(.sequenceConstruct {Argument(encoded[construct.Left])} {Argument(encoded[construct.Right])})"
                : $"(.sequenceSpread {Argument(encoded[((Expr.SequenceSpread)frame.Node).Operand])})";
            encoded[frame.Node] = Term(frame.Node, context, "Expr", () => body);
        }
        return encoded[root];
    }

    private string EncodeExprCore(Expr expr) => expr switch
    {
        Expr.Num(var value) => $".num {EncodeNumber(value)}",
        Expr.StringLiteral(var value) => $".stringLiteral {Quote(value)}",
        Expr.BoolLiteral(var value) => $".boolLiteral {EncodeBool(value)}",
        Expr.EmptySequence(var depth) => EncodeEmptySequence(depth),
        Expr.Resolve(var name) => $".resolve {Quote(name)}",
        Expr.Param(var name) => $".param {Quote(name)}",
        Expr.AlgorithmExpr(var algorithm) => $"(.algorithmExpr {EncodeAlgorithm(algorithm)})",
        Expr.Capture(var captureBody) => $"(.capture [{EncodeList(captureBody, EncodeExpr)}])",
        Expr.ListLiteral(var items) => $"(.listLiteral [{EncodeList(items, EncodeExpr)}])",
        Expr.SequenceSpread(var operand) => $"(.sequenceSpread {Arg(operand)})",
        Expr.Unary(var op, var operand) => $"(.unary .{EncodeUnaryOp(op)} {Arg(operand)})",
        Expr.Binary(var op, var left, var right) =>
            $"(.binary .{EncodeBinaryOp(op)} {Arg(left)} {Arg(right)})",
        // A comparison chain encodes as the flat chain it is: the first operand and one
        // `{ op, operand }` link per written comparison, never nested binaries.
        Expr.Comparison(var first, var links) =>
            $"(.comparison {Arg(first)} [{EncodeList(links, EncodeComparisonLink)}])",
        // An interpolated string encodes as the alternating form it is: the decoded head text
        // and one `{ hole, text }` link per hole, in written order.
        Expr.InterpolatedString(var head, var links) =>
            $"(.interpolatedString {Quote(head)} [{EncodeList(links, EncodeInterpolationLink)}])",
        Expr.Index(var target, var selectors) => $"(.index {Arg(target)} [{EncodeList(selectors, EncodeExpr)}])",
        // INTERNAL node: the parser never produces it, but the internal-node
        // differential cases hand-construct it, and their Lean text is derived
        // from the same constructed AST the C# side observes.
        Expr.SequenceConstruct(var left, var right) =>
            $"(.sequenceConstruct {Arg(left)} {Arg(right)})",
        Expr.DotCall dotCall => EncodeDotCall(dotCall),
        Expr.Call(var callee, var args) => $"(.call {Arg(callee)} {EncodeBundle(args)})",
        // DELIBERATELY refused: elaboration consumes and strips Grace, and the Lean core
        // does not model natives (NativeCall exists only inside prelude/host wrapper
        // bodies). The switch is compiler-exhaustive over the closed Expr hierarchy, so a
        // new variant must be encoded or refused here explicitly — never approximated.
        Expr.Grace or Expr.NativeCall => throw new NotSupportedException(
            $"{nameof(LeanAstEncoder)} does not cover {expr.GetType().Name}. " +
            "Add it deliberately rather than letting the encoder approximate."),
    };

    /// <summary>Encoding for Lean application position: parenthesized unless already delimited.</summary>
    private string Arg(Expr expr)
    {
        var encoded = EncodeExpr(expr);
        return encoded.StartsWith('(') ? encoded : $"({encoded})";
    }

    /// <summary>
    /// Serializes the ELABORATED dot-edge decision: an edge whose fallback is
    /// the default <c>Resolve(Name)</c> uses the `Expr.dotCall` smart
    /// constructor (definitionally the same node), while a Param-bound
    /// fallback is spelled with the full <c>.dotMember</c> constructor so the
    /// Lean guard evaluates the same front-end decision the C# runtime
    /// consumes. (A graced dot source encodes identically to its ungraced
    /// twin: Grace is consumed before encoding.)
    /// </summary>
    private string EncodeDotCall(Expr.DotCall dotCall)
    {
        var argsEncoding = dotCall.Args is null ? "none" : $"(some {EncodeBundle(dotCall.Args)})";
        var fallback = dotCall.EffectiveLexicalFallback;
        if (fallback is Expr.Resolve(var fallbackName)
            && string.Equals(fallbackName, dotCall.Name, StringComparison.Ordinal))
        {
            return $"(.dotCall {Arg(dotCall.Target)} {Quote(dotCall.Name)} {argsEncoding})";
        }

        return $"(.dotMember {Arg(dotCall.Target)} {Quote(dotCall.Name)} {Arg(fallback)} {argsEncoding})";
    }

    /// <summary>Call/dot-call argument bundle: a plain Lean list of the slot expressions.</summary>
    private string EncodeBundle(OutputBundle args) => $"[{EncodeList(args, EncodeExpr)}]";

    public string EncodeAlgorithm(Algorithm algorithm)
        => Term(algorithm, CurrentContext, "Algorithm", () => EncodeAlgorithmInContext(algorithm));

    private string EncodeAlgorithmInContext(Algorithm algorithm)
    {
        var parent = _scope;
        // A loaded module is a source unit rooted at the prelude (Q-31 H-P): it has no enclosing
        // scope wherever it is held, and its ONE declaration (Q-32 I-U) is marked so Lean wires it
        // at the chain's root level (`PropertyIdentity.module`, `Algorithm.withParent`).
        var isModule = algorithm.IsModuleRoot;
        // A PRE-WIRED parent (a host-built `Algorithm.Parent`, HOST-DIFF-1) is the algorithm's own
        // lexical parent and is encoded with it; only an unwired algorithm takes the encoder's
        // enclosing scope, which both evaluators wire it under.
        // The scope stands for the EVALUATOR-OWNED level of `algorithm`, so it carries that owner:
        // an ownerless level would count as a host object by reference (HOST-NESTED-1), and this
        // per-traversal record would split one declaration reached twice.
        _scope = new ScopeCtx(algorithm.Parent ?? (isModule ? null : parent), algorithm.Opens, algorithm.Properties)
        {
            Owner = algorithm,
        };
        try
        {
            var encoded = EncodeAlgorithmCore(algorithm);
            if (algorithm.Parent is { } wired)
                encoded = $"(Algorithm.withParent (some {EncodeScope(wired)}) {encoded})";
            if (isModule)
            {
                var module = algorithm.Declaration
                    ?? throw new NotSupportedException("A loaded module must have a declaration identity.");
                if (!_algorithmIdentities.TryGetValue(module, out var moduleIdentity))
                    _algorithmIdentities[module] = moduleIdentity = _algorithmIdentities.Count;
                return $"(Algorithm.withDeclarationId (some (.module {moduleIdentity})) {encoded})";
            }

            if (!_sharing.Contains(algorithm)) return encoded;
            var declaration = algorithm.Declaration
                ?? throw new NotSupportedException("A shared algorithm must have a declaration identity.");
            if (!_algorithmIdentities.TryGetValue(declaration, out var identity))
                _algorithmIdentities[declaration] = identity = _algorithmIdentities.Count;
            return $"(Algorithm.withDeclarationId (some (.shared {identity})) {encoded})";
        }
        finally { _scope = parent; }
    }

    private string EncodeOpens(IReadOnlyList<Expr> opens)
    {
        // Inline open providers are wired to the global prelude, not the opener.
        // Its common outer scope adds no distinguishing identity within a run.
        var opener = _scope;
        _scope = null;
        try { return EncodeList(opens, EncodeExpr); }
        finally { _scope = opener; }
    }

    /// <summary>
    /// A host-built <see cref="ScopeCtx"/> level as the Lean <c>ScopeCtx.mk</c> it is, with its own
    /// parent chain inner to outer: <c>ScopeCtx.mk parent params opens props output branches
    /// activation declarationId</c>. A host level is OWNERLESS — no owner body (its Lean
    /// <c>output</c>/<c>branches</c>, which retain an owner's body for scope reconstruction, are
    /// empty: Lean reconstructs only evaluator-owned scopes, and the host level reaches lookup only
    /// through its opens and properties), no activation and no declaration identity, exactly
    /// <c>CoreTests/HostScopePropertyCache.lean</c>'s <c>hostLevel</c>. Its properties are declared
    /// IN this level (their values resolve names under it, Lean <c>lookupInParentsStructuralProperty</c>),
    /// and a property shared across encodings carries its per-scope-object identity
    /// (<see cref="HostDeclarationIdentity"/>). An evaluator-created scope (internal
    /// <see cref="ScopeCtx.Owner"/> / <see cref="ScopeCtx.Activation"/>) is runtime state no input AST
    /// carries, so it is refused rather than encoded as an ownerless level.
    /// </summary>
    private string EncodeScope(ScopeCtx scope)
        => Term(scope, _globalContext, "ScopeCtx", () => EncodeScopeCore(scope));

    private string EncodeScopeCore(ScopeCtx scope)
    {
        if (scope.Owner is not null || scope.Activation is not null)
        {
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} cannot encode an evaluator-created ScopeCtx (owner " +
                $"{(scope.Owner is null ? "none" : scope.Owner.GetType().Name)}, activation " +
                $"{(scope.Activation is null ? "none" : "present")}); owner bodies and activations are runtime state " +
                "with no stable input-AST encoding, and dropping them would encode a different (ownerless) level.");
        }

        var outer = scope.Parent is { } parent ? $"(some {EncodeScope(parent)})" : "none";
        var enclosing = _scope;
        _scope = scope;
        try
        {
            var parameters = EncodeList(scope.Parameters, Quote);
            var opens = EncodeOpens(scope.Opens);
            var properties = EncodeList(scope.Properties, property => EncodePropertyCore(property,
                _sharing.Contains(property) ? HostDeclarationIdentity(property, scope) : null));
            return $"(ScopeCtx.mk {outer} [{parameters}] [{opens}] [{properties}] [] [] none none)";
        }
        finally { _scope = enclosing; }
    }

    private string EncodeAlgorithmCore(Algorithm algorithm)
    {
        if (algorithm is Algorithm.Conditional conditional)
        {
            var conditionalOpens = EncodeOpens(conditional.Opens);
            var branches = EncodeList(
                conditional.Branches,
                branch => $"⟨{EncodePattern(branch.Pattern)}, {EncodeAlgorithm(branch.Body)}⟩");
            return $"(.conditional none [{conditionalOpens}] [{branches}])";
        }

        if (algorithm is Algorithm.Alias alias)
        {
            // Lean `Algorithm.alias parent opens properties target`: the binding's own scope and
            // its written target, resolved by the Lean evaluator in the alias's own scope.
            var aliasOpens = EncodeOpens(alias.Opens);
            var aliasProperties = EncodeList(alias.Properties, property => EncodeProperty(property, alias));
            return $"(.alias none [{aliasOpens}] [{aliasProperties}] ({EncodeExpr(alias.Target)}))";
        }

        if (algorithm is not Algorithm.User user)
        {
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} covers Algorithm.User, Algorithm.Conditional and Algorithm.Alias, " +
                $"not {algorithm.GetType().Name}.");
        }

        var opens = EncodeOpens(user.Opens);
        var properties = EncodeList(user.Properties, property => EncodeProperty(property, user));
        var output = EncodeList(user.Output, EncodeExpr);
        var (constructor, parameters) = EncodeParameterChannel(user);
        return $"({constructor} [{parameters}] [{opens}] [{properties}] [{output}])";
    }

    /// <summary>
    /// Encodes the parameter channel through the least-powerful faithful Lean
    /// constructor, mirroring how the corpora spell the three shapes:
    /// <c>alg [names]</c> for all-normal flat captures,
    /// <c>algWithParameters [{ name, kind }]</c> once a collecting capture
    /// appears, and <c>algWithParameterPatterns [...]</c> once any structural
    /// (sequence or list) pattern appears. The Lean helpers derive the flattened
    /// parameter list from the patterns exactly as the C# tree does: a user
    /// algorithm stores ONE channel (<see cref="Algorithm.User.ParameterPatterns"/>)
    /// and <see cref="Algorithm.User.Parameters"/> is its projection, so the two
    /// can no longer disagree and the encoder reads the stored patterns alone.
    /// </summary>
    private static (string Constructor, string Parameters) EncodeParameterChannel(Algorithm.User user)
    {
        var patterns = user.ParameterPatterns;
        if (patterns.Any(static pattern => pattern is not CaptureParameterPattern))
        {
            return ("algWithParameterPatterns", EncodeList(patterns, EncodeParameterPattern));
        }

        var captures = patterns.Cast<CaptureParameterPattern>().ToList();
        if (captures.Any(static capture => capture.Kind != ParameterKind.Normal))
        {
            return ("algWithParameters", EncodeList(captures, EncodeCallableParameter));
        }

        return ("alg", EncodeList(captures, capture => Quote(capture.Name)));
    }

    /// <summary>Lean <c>CallableParameter</c> anonymous-structure spelling.</summary>
    private static string EncodeCallableParameter(CaptureParameterPattern capture) => capture.Kind switch
    {
        ParameterKind.Normal => $"{{ name := {Quote(capture.Name)} }}",
        ParameterKind.Collecting => $"{{ name := {Quote(capture.Name)}, kind := .collecting }}",
        ParameterKind.Meta => $"{{ name := {Quote(capture.Name)}, kind := .metaRef }}",
        _ => throw new NotSupportedException($"Unhandled parameter kind '{capture.Kind}'."),
    };

    /// <summary>
    /// Lean <c>ParameterPattern</c> constructor spelling. Pattern SHAPE and KIND are
    /// load-bearing: <c>F((x, y))</c>, <c>F([x, y])</c> and the flat <c>F(x, y)</c> are
    /// three different programs, and the flattened <see cref="Algorithm.User.Parameters"/>
    /// list cannot distinguish them — the original Track 9 failure mode. Encoding the
    /// pattern tree keeps the distinction. Compiler-exhaustive over the closed
    /// ParameterPattern hierarchy: a new variant fails this build until the encoder covers it.
    /// </summary>
    private static string EncodeParameterPattern(ParameterPattern pattern) => pattern switch
    {
        CaptureParameterPattern capture => $".capture {EncodeCallableParameter(capture)}",
        SequenceValueParameterPattern(var items) =>
            $".sequenceValue [{EncodeList(items, EncodeParameterPattern)}]",
        ListValueParameterPattern(var items) =>
            $".listValue [{EncodeList(items, EncodeParameterPattern)}]",
        UnpackingParameterPattern(var items) =>
            $".unpacking [{EncodeList(items, EncodeParameterPattern)}]",
    };

    /// <summary>
    /// Encodes visibility AND exposure. Both matter: <c>open</c> selects a member only
    /// when it is public, structural dot access ignores visibility entirely, and a
    /// local-only member's required ancestor parameter names decide from which sites
    /// either channel may use it (Lean <c>memberAccessible?</c>).
    /// </summary>
    public string EncodeProperty(Property property, Algorithm? owner = null)
        => EncodePropertyCore(property,
            owner is not null && _sharing.Contains(property) ? DeclarationIdentity(property, owner) : null);

    private string EncodePropertyCore(Property property, int? sharedIdentity)
    {
        var value = EncodeAlgorithm(property.Value);
        var encoded = (property.IsPublic, property.Exposure) switch
        {
            (false, PropertyExposure.Exported) => $"privateProp {Quote(property.Name)} {value}",
            (true, PropertyExposure.Exported) => $"publicProp {Quote(property.Name)} {value}",
            (false, var exposure) => $"privateLocalProp {Quote(property.Name)} {EncodeExposure(exposure, property.RequiredAncestorParameters)} {value}",
            (true, var exposure) => $"publicLocalProp {Quote(property.Name)} {EncodeExposure(exposure, property.RequiredAncestorParameters)} {value}",
        };
        if (property.CaptureRequirements is { Count: > 0 } requirements)
        {
            var owners = string.Join(", ", requirements.Select(r =>
                $"({Quote(r.Name)}, {(r.OwnerDepth < 0 ? "none" : $"some {r.OwnerDepth}")})"));
            encoded = $"{{ ({encoded}) with requiredOwnerDepths := some [{owners}] }}";
        }
        return sharedIdentity is { } identity
            ? $"{{ ({encoded}) with identity := some (.shared {identity}) }}"
            : encoded;
    }

    /// <summary>
    /// Conditional clause head. Pattern SHAPE and KIND are load-bearing: a nested
    /// <c>sequenceValue</c> (written <c>F((x, y))</c>) matches sequences only, a
    /// <c>listValue</c> (written <c>F([x, y])</c>) lists only, and a bare <c>bind</c>
    /// head (written <c>F(x)</c>) any value. Compiler-exhaustive over the closed
    /// Pattern hierarchy: a new variant fails this build until the encoder covers it.
    /// </summary>
    public static string EncodePattern(Pattern pattern) => pattern switch
    {
        Pattern.Bind { ParameterKind: ParameterKind.Collecting } =>
            throw new NotSupportedException("Lean clause binders cannot represent collecting bindings."),
        Pattern.Bind { ParameterKind: ParameterKind.Meta } =>
            throw new NotSupportedException("Lean clause binders cannot represent META bindings."),
        Pattern.Bind(var name) => $".bind {Quote(name)}",
        Pattern.LitInt(var value) => $".litInt {EncodeNumber(value)}",
        Pattern.LitString(var value) => $".litString {Quote(value)}",
        Pattern.LitBool(var value) => $".litBool {EncodeBool(value)}",
        Pattern.SequenceValue(var items) => $".sequenceValue [{EncodeList(items, EncodePattern)}]",
        Pattern.ListValue(var items) => $".listValue [{EncodeList(items, EncodePattern)}]",
    };

    /// <summary>Lean's `Bool` literals are spelled exactly like KatLang's.</summary>
    private static string EncodeBool(bool value) => value ? "true" : "false";

    private static string EncodeExposure(PropertyExposure exposure, IReadOnlyList<string> requiredAncestorParameters) => exposure switch
    {
        PropertyExposure.LocalOnlyCapturedAncestorParameters =>
            $"(.localCapturedAncestorParams [{EncodeList(requiredAncestorParameters, Quote)}])",
        PropertyExposure.LocalOnlyConditionalAlgorithm => ".localConditional",
        _ => throw new NotSupportedException($"Unhandled exposure '{exposure}'."),
    };

    /// <summary>One chain link as the Lean structure literal <c>{ op := .lt, operand := … }</c>.</summary>
    private string EncodeComparisonLink(ComparisonLink link)
        => $"{{ op := .{EncodeComparisonOp(link.Op)}, operand := {Arg(link.Operand)} }}";

    private string EncodeInterpolationLink(InterpolationLink link)
        => $"{{ hole := {Arg(link.Hole)}, text := {Quote(link.Text)} }}";

    private static string EncodeComparisonOp(ComparisonOp op) => op switch
    {
        ComparisonOp.Lt => "lt",
        ComparisonOp.Gt => "gt",
        ComparisonOp.Le => "le",
        ComparisonOp.Ge => "ge",
        ComparisonOp.Eq => "eq",
        ComparisonOp.Ne => "ne",
        _ => throw new NotSupportedException($"Unhandled comparison operator '{op}'."),
    };

    private static string EncodeBinaryOp(BinaryOp op) => op switch
    {
        BinaryOp.Add => "add",
        BinaryOp.Sub => "sub",
        BinaryOp.Mul => "mul",
        BinaryOp.Div => "div",
        BinaryOp.IDiv => "idiv",
        BinaryOp.Mod => "mod",
        BinaryOp.Pow => "pow",
        BinaryOp.And => "and",
        BinaryOp.Or => "or",
        BinaryOp.Xor => "xor",
        _ => throw new NotSupportedException($"Unhandled binary operator '{op}'."),
    };

    private static string EncodeUnaryOp(UnaryOp op) => op switch
    {
        UnaryOp.Minus => "minus",
        UnaryOp.Not => "not",
        _ => throw new NotSupportedException($"Unhandled unary operator '{op}'."),
    };

    /// <summary>
    /// Lean <c>.num</c> takes an <c>Int</c>: a finite, exactly integral
    /// Decimal128 value is encoded by value in fixed-point form when that is
    /// also how the runtime renders it — an exponent spelling such as
    /// <c>1e3</c> renders and encodes as <c>1000</c>. Fractions, non-finite
    /// values, and negative zero are outside the Lean Int model and are refused
    /// rather than normalized to a different value; so is an integral value
    /// whose invariant rendering keeps a Decimal128 quantum (<c>1.0</c>,
    /// <c>10.0</c>, <c>100e-2</c>): <c>Decimal128.IsInteger</c> ignores the
    /// quantum, but the runtime displays it (<c>1.0 + 2.0</c> is <c>3.0</c>)
    /// where a Lean Int program observes <c>3</c>, so <c>.num 1</c> would
    /// fabricate a Lean/C# divergence out of the encoder itself. Quantum is the
    /// Decimal128-only numeric tier (the numeric row in
    /// <c>src/KatLang/SEMANTIC-ALIGNMENT.md</c>); a case that needs it is
    /// excluded with a <c>LeanExclusionReason</c>, never given a Lean encoding.
    /// </summary>
    private static string EncodeNumber(Decimal128 value)
    {
        var display = KatLang.Rendering.ValueTextRenderer.FormatNumberInvariant(value);
        if (!Decimal128.IsFinite(value) || !Decimal128.IsInteger(value))
        {
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} cannot encode the non-integer or non-finite number '{display}'; " +
                "the Lean core models Int, so a case with fractional or non-finite " +
                "literals must be excluded explicitly (decimal semantics are a documented model divergence).");
        }

        if (value == Decimal128.Zero && Decimal128.IsNegative(value))
        {
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} cannot encode Decimal128 negative zero; " +
                "Lean Int has no signed-zero value, so normalizing it to 0 would change the modeled program.");
        }

        var text = value.ToString("F0", CultureInfo.InvariantCulture);
        if (text != display)
        {
            // The invariant rendering is the observation channel the differential
            // corpora compare (SemanticExplorerHarness.Neutral), so it — not a
            // quantum probe — decides encodability: `1e100` renders as its plain
            // digits and encodes, `1.0` renders its quantum and is refused.
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} cannot encode the quantum-bearing integral number '{display}'; " +
                $"the Lean core models Int and would observe '{text}', while the Decimal128 runtime keeps the " +
                "quantum in its output. Quantum is Decimal128-only numeric-tier behavior (never given a " +
                "fabricated Lean encoding), so the case must be excluded explicitly with a LeanExclusionReason.");
        }

        return text.StartsWith('-') ? $"({text})" : text;
    }

    private static string EncodeEmptySequence(int depth)
    {
        if (depth < 0)
        {
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} cannot encode EmptySequence depth {depth}; " +
                "the Lean field is Nat, so a negative host-built value has no faithful constructor spelling.");
        }

        return $"(.emptySequence {depth})";
    }

    /// <summary>
    /// Lean string-literal spelling for names and string values. Backslash and
    /// quote are escaped, and a line feed and a tab take Lean's <c>\n</c> / <c>\t</c>
    /// (a double-quoted KatLang string can hold them through its escapes); every other
    /// control character has no reviewed spelling here and is refused. Also the
    /// spelling of the expected neutral text embedded in a generated <c>#guard</c>.
    /// </summary>
    internal static string Quote(string value)
    {
        var builder = new StringBuilder(value.Length + 2);
        builder.Append('"');
        for (var i = 0; i < value.Length; i++)
        {
            var ch = value[i];
            if (ch == '\n')
            {
                builder.Append("\\n");
                continue;
            }

            if (ch == '\t')
            {
                builder.Append("\\t");
                continue;
            }

            if (char.IsControl(ch))
            {
                throw new NotSupportedException(
                    $"{nameof(LeanAstEncoder)} cannot encode the control character U+{(int)ch:X4} " +
                    "inside a Lean string literal; add an explicit escape deliberately if a case needs it.");
            }

            if (char.IsHighSurrogate(ch))
            {
                if (i + 1 >= value.Length || !char.IsLowSurrogate(value[i + 1]))
                {
                    throw new NotSupportedException(
                        $"{nameof(LeanAstEncoder)} cannot encode the unpaired high surrogate U+{(int)ch:X4}; " +
                        "Lean strings contain Unicode scalar values, so invalid UTF-16 cannot be preserved.");
                }

                builder.Append(ch);
                builder.Append(value[++i]);
                continue;
            }

            if (char.IsLowSurrogate(ch))
            {
                throw new NotSupportedException(
                    $"{nameof(LeanAstEncoder)} cannot encode the unpaired low surrogate U+{(int)ch:X4}; " +
                    "Lean strings contain Unicode scalar values, so invalid UTF-16 cannot be preserved.");
            }

            if (ch is '"' or '\\')
                builder.Append('\\');
            builder.Append(ch);
        }

        builder.Append('"');
        return builder.ToString();
    }

    private static string EncodeList<T>(IReadOnlyList<T> items, Func<T, string> encode)
    {
        if (items.Count == 0)
            return string.Empty;

        var builder = new StringBuilder();
        for (var i = 0; i < items.Count; i++)
        {
            if (i > 0)
                builder.Append(", ");
            builder.Append(encode(items[i]));
        }

        return builder.ToString();
    }
}
