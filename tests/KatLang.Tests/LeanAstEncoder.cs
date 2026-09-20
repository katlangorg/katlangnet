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
/// </summary>
public static class LeanAstEncoder
{
    public static string EncodeProgram(Algorithm root) => new LeanAstEncoding(root).EncodeProgram(root);
    public static string EncodeAlgorithm(Algorithm algorithm) => new LeanAstEncoding(algorithm).EncodeAlgorithm(algorithm);
    public static string EncodeExpr(Expr expression) => new LeanAstEncoding(expression).EncodeExpr(expression);
    public static string EncodeProperty(Property property) => new LeanAstEncoding(property.Value).EncodeProperty(property);
    public static string EncodePattern(Pattern pattern) => LeanAstEncoding.EncodePattern(pattern);
}

internal sealed class LeanAstEncoding
{
    private readonly SharedDeclarations _sharing = new();
    private readonly Dictionary<StructuralOwnerIdentity, Dictionary<Property, int>> _identities = new();
    private readonly Dictionary<DeclarationIdentity, int> _algorithmIdentities = new();
    private int _nextIdentity;
    private ScopeCtx? _scope;

    public LeanAstEncoding(Algorithm root) => _sharing.VisitAlgorithm(root);
    public LeanAstEncoding(Expr root) => _sharing.VisitExpr(root);

    private int DeclarationIdentity(Property property, Algorithm owner)
    {
        // Lean withParent: the owner as wired under the current scope, narrowed to the variant
        // that has a parent (a builtin never owns a property, but the switch stays total).
        Algorithm rewiredOwner = owner switch
        {
            Algorithm.User user => user with { Parent = _scope?.Parent },
            Algorithm.Conditional family => family with { Parent = _scope?.Parent },
            Algorithm.Builtin => owner,
        };
        var scopeIdentity = StructuralOwnerIdentity.FromOwner(rewiredOwner);
        if (!_identities.TryGetValue(scopeIdentity, out var byProperty))
            _identities[scopeIdentity] = byProperty = new(ReferenceEqualityComparer.Instance);
        if (!byProperty.TryGetValue(property, out var identity))
            byProperty[property] = identity = _nextIdentity++;
        return identity;
    }

    // Two graph-bounded walks preserve host sharing without confusing equal
    // bodies with one declaration. A repeated subtree marks all its properties.
    private sealed class SharedDeclarations : AstWalker
    {
        private readonly HashSet<Algorithm> _algorithms = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<DeclarationIdentity> _declarations = new();
        private readonly HashSet<DeclarationIdentity> _sharedDeclarations = new();
        private readonly HashSet<Expr> _expressions = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<Property> _properties = new(ReferenceEqualityComparer.Instance);
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
            if (_algorithms.Add(algorithm)) base.VisitAlgorithm(algorithm);
            else _marker.VisitAlgorithm(algorithm);
        }
        public override void VisitExpr(Expr expression)
        {
            if (_expressions.Add(expression)) base.VisitExpr(expression);
            else _marker.VisitExpr(expression);
        }
        protected override void VisitProperty(Property property)
        {
            if (!_properties.Add(property)) _marker.Properties.Add(property);
            base.VisitProperty(property);
        }
    }

    private sealed class SharedMarker : AstWalker
    {
        public readonly HashSet<Algorithm> Algorithms = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<Expr> _expressions = new(ReferenceEqualityComparer.Instance);
        public readonly HashSet<Property> Properties = new(ReferenceEqualityComparer.Instance);
        protected override bool VisitsExplicitParameterDeclarations => false;
        public override void VisitAlgorithm(Algorithm algorithm)
        {
            if (Algorithms.Add(algorithm)) base.VisitAlgorithm(algorithm);
        }
        public override void VisitExpr(Expr expression)
        {
            if (_expressions.Add(expression)) base.VisitExpr(expression);
        }
        protected override void VisitProperty(Property property)
        {
            Properties.Add(property);
            base.VisitProperty(property);
        }
    }

    /// <summary>Encodes a parsed root algorithm as a Lean <c>.algorithmExpr (alg ...)</c> program.</summary>
    public string EncodeProgram(Algorithm root) => $".algorithmExpr {EncodeAlgorithm(root)}";

    /// <summary>
    /// Bare encoding, suitable where a delimiter already separates terms (list
    /// elements). Use <see cref="Arg"/> for anything in Lean application
    /// position, which needs parentheses around multi-token terms.
    /// </summary>
    public string EncodeExpr(Expr expr) => expr switch
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
        Expr.Index(var target, var selector) => $"(.index {Arg(target)} {Arg(selector)})",
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
    {
        var parent = _scope;
        _scope = new ScopeCtx(parent, algorithm.Opens, algorithm.Properties);
        try
        {
            var encoded = EncodeAlgorithmCore(algorithm);
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

    private string EncodeAlgorithmCore(Algorithm algorithm)
    {
        if (algorithm.Parent is not null)
        {
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} cannot encode an algorithm with a pre-wired Parent scope; " +
                "corpus/source algorithms must be unwired (Parent = null) so both evaluators wire them to their caller.");
        }

        if (algorithm is Algorithm.Conditional conditional)
        {
            var conditionalOpens = EncodeOpens(conditional.Opens);
            var branches = EncodeList(
                conditional.Branches,
                branch => $"⟨{EncodePattern(branch.Pattern)}, {EncodeAlgorithm(branch.Body)}⟩");
            return $"(.conditional none [{conditionalOpens}] [{branches}])";
        }

        if (algorithm is not Algorithm.User user)
        {
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} covers Algorithm.User and Algorithm.Conditional, " +
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
    /// appears, and <c>algWithParameterPatterns [...]</c> once any
    /// sequence-value pattern appears. The Lean helpers derive the flattened
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
        _ => throw new NotSupportedException($"Unhandled parameter kind '{capture.Kind}'."),
    };

    /// <summary>
    /// Lean <c>ParameterPattern</c> constructor spelling. Pattern SHAPE is
    /// load-bearing: <c>F((x))</c> is a singleton sequence-value pattern, a
    /// different program from the flat <c>F(x)</c>, and the flattened
    /// <see cref="Algorithm.User.Parameters"/> list cannot distinguish them — the
    /// original Track 9 failure mode. Encoding the pattern tree keeps the
    /// distinction. Compiler-exhaustive over the closed ParameterPattern hierarchy:
    /// a new variant fails this build until the encoder covers it.
    /// </summary>
    private static string EncodeParameterPattern(ParameterPattern pattern) => pattern switch
    {
        CaptureParameterPattern capture => $".capture {EncodeCallableParameter(capture)}",
        SequenceValueParameterPattern(var items) =>
            $".sequenceValue [{EncodeList(items, EncodeParameterPattern)}]",
    };

    /// <summary>
    /// Encodes visibility AND exposure. Both matter: <c>open</c> selects a member only
    /// when it is public, structural dot access ignores visibility entirely, and a
    /// local-only member's required ancestor parameter names decide from which sites
    /// either channel may use it (Lean <c>memberAccessible?</c>).
    /// </summary>
    public string EncodeProperty(Property property, Algorithm? owner = null)
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
        return owner is not null && _sharing.Contains(property)
            ? $"{{ ({encoded}) with identity := some (.shared {DeclarationIdentity(property, owner)}) }}"
            : encoded;
    }

    /// <summary>
    /// Conditional clause head. Pattern SHAPE is load-bearing: a singleton
    /// <c>sequenceValue [bind]</c> head (written <c>F((x))</c>) is a different
    /// clause from a bare <c>bind</c> head (written <c>F(x)</c>), and only the
    /// former exercises the documented whole-argument singleton rule.
    /// Compiler-exhaustive over the closed Pattern hierarchy: a new variant fails
    /// this build until the encoder covers it.
    /// </summary>
    public static string EncodePattern(Pattern pattern) => pattern switch
    {
        Pattern.Bind(var name) => $".bind {Quote(name)}",
        Pattern.LitInt(var value) => $".litInt {EncodeNumber(value)}",
        Pattern.LitString(var value) => $".litString {Quote(value)}",
        Pattern.LitBool(var value) => $".litBool {EncodeBool(value)}",
        Pattern.SequenceValue(var items) => $".sequenceValue [{EncodeList(items, EncodePattern)}]",
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
    /// quote are escaped; a control character has no reviewed spelling here and
    /// is refused (no corpus name or literal contains one).
    /// </summary>
    private static string Quote(string value)
    {
        var builder = new StringBuilder(value.Length + 2);
        builder.Append('"');
        for (var i = 0; i < value.Length; i++)
        {
            var ch = value[i];
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
