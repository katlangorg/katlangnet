using System.Globalization;
using System.Numerics;
using System.Text;

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
/// a source program). Numbers must be integer-valued (the Lean core is
/// <c>Int</c>) and strings must be control-character-free; both are validated
/// fail-loud.
/// </para>
/// </summary>
public static class LeanAstEncoder
{
    /// <summary>Encodes a parsed root algorithm as a Lean <c>.algorithmExpr (alg ...)</c> program.</summary>
    public static string EncodeProgram(Algorithm root) => $".algorithmExpr {EncodeAlgorithm(root)}";

    /// <summary>
    /// Bare encoding, suitable where a delimiter already separates terms (list
    /// elements). Use <see cref="Arg"/> for anything in Lean application
    /// position, which needs parentheses around multi-token terms.
    /// </summary>
    public static string EncodeExpr(Expr expr) => expr switch
    {
        Expr.Num(var value) => $".num {EncodeNumber(value)}",
        Expr.StringLiteral(var value) => $".stringLiteral {Quote(value)}",
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
        Expr.Index(var target, var selector) => $"(.index {Arg(target)} {Arg(selector)})",
        // INTERNAL node: the parser never produces it, but the internal-node
        // differential cases hand-construct it, and their Lean text is derived
        // from the same constructed AST the C# side observes.
        Expr.SequenceConstruct(var left, var right) =>
            $"(.sequenceConstruct {Arg(left)} {Arg(right)})",
        Expr.DotCall dotCall => EncodeDotCall(dotCall),
        Expr.Call(var callee, var args) => $"(.call {Arg(callee)} {EncodeBundle(args)})",
        _ => throw new NotSupportedException(
            $"{nameof(LeanAstEncoder)} does not cover {expr.GetType().Name}. " +
            "Add it deliberately rather than letting the encoder approximate."),
    };

    /// <summary>Encoding for Lean application position: parenthesized unless already delimited.</summary>
    private static string Arg(Expr expr)
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
    private static string EncodeDotCall(Expr.DotCall dotCall)
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
    private static string EncodeBundle(OutputBundle args) => $"[{EncodeList(args, EncodeExpr)}]";

    public static string EncodeAlgorithm(Algorithm algorithm)
    {
        if (algorithm.Parent is not null)
        {
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} cannot encode an algorithm with a pre-wired Parent scope; " +
                "corpus/source algorithms must be unwired (Parent = null) so both evaluators wire them to their caller.");
        }

        if (algorithm is Algorithm.Conditional conditional)
        {
            var conditionalOpens = EncodeList(conditional.Opens, EncodeExpr);
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

        var opens = EncodeList(user.Opens, EncodeExpr);
        var properties = EncodeList(user.Properties, EncodeProperty);
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
    /// parameter list from the patterns, so the C# tree's two channels
    /// (<see cref="Algorithm.Parameters"/> and
    /// <see cref="Algorithm.ParameterPatterns"/>) must agree — a host tree
    /// whose channels diverge has no single faithful Lean spelling and is
    /// refused rather than approximated.
    /// </summary>
    private static (string Constructor, string Parameters) EncodeParameterChannel(Algorithm.User user)
    {
        var patterns = user.ParameterPatterns;
        var flattened = ParameterPattern.FlattenCaptures(patterns);
        if (flattened.Count != user.Parameters.Count
            || flattened.Where((capture, i) =>
                    !string.Equals(capture.Name, user.Parameters[i].Name, StringComparison.Ordinal)
                    || capture.Kind != user.Parameters[i].Kind)
                .Any())
        {
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} cannot encode an algorithm whose Parameters " +
                $"([{string.Join(", ", user.Parameters.Select(p => p.DisplayName))}]) disagree with the flatten of its " +
                $"ParameterPatterns ([{string.Join(", ", patterns.Select(p => p.DisplayName))}]); the Lean model derives " +
                "one from the other, so a divergent host tree has no faithful spelling.");
        }

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
    /// <see cref="Algorithm.Parameters"/> list cannot distinguish them — the
    /// original Track 9 failure mode. Encoding the pattern tree keeps the
    /// distinction.
    /// </summary>
    private static string EncodeParameterPattern(ParameterPattern pattern) => pattern switch
    {
        CaptureParameterPattern capture => $".capture {EncodeCallableParameter(capture)}",
        SequenceValueParameterPattern(var items) =>
            $".sequenceValue [{EncodeList(items, EncodeParameterPattern)}]",
        _ => throw new NotSupportedException(
            $"{nameof(LeanAstEncoder)} does not cover parameter pattern {pattern.GetType().Name}."),
    };

    /// <summary>
    /// Encodes visibility AND exposure. Both matter: <c>open</c> exposes a member
    /// only when it is public AND exported, while structural dot access ignores
    /// visibility entirely.
    /// </summary>
    public static string EncodeProperty(Property property)
    {
        var value = EncodeAlgorithm(property.Value);
        return (property.IsPublic, property.Exposure) switch
        {
            (false, PropertyExposure.Exported) => $"privateProp {Quote(property.Name)} {value}",
            (true, PropertyExposure.Exported) => $"publicProp {Quote(property.Name)} {value}",
            (false, var exposure) => $"privateLocalProp {Quote(property.Name)} .{EncodeExposure(exposure)} {value}",
            (true, var exposure) => $"publicLocalProp {Quote(property.Name)} .{EncodeExposure(exposure)} {value}",
        };
    }

    /// <summary>
    /// Conditional clause head. Pattern SHAPE is load-bearing: a singleton
    /// <c>sequenceValue [bind]</c> head (written <c>F((x))</c>) is a different
    /// clause from a bare <c>bind</c> head (written <c>F(x)</c>), and only the
    /// former exercises the documented whole-argument singleton rule.
    /// </summary>
    public static string EncodePattern(Pattern pattern) => pattern switch
    {
        Pattern.Bind(var name) => $".bind {Quote(name)}",
        Pattern.LitInt(var value) => $".litInt {EncodeNumber(value)}",
        Pattern.LitString(var value) => $".litString {Quote(value)}",
        Pattern.SequenceValue(var items) => $".sequenceValue [{EncodeList(items, EncodePattern)}]",
        _ => throw new NotSupportedException(
            $"{nameof(LeanAstEncoder)} does not cover pattern {pattern.GetType().Name}."),
    };

    private static string EncodeExposure(PropertyExposure exposure) => exposure switch
    {
        PropertyExposure.LocalOnlyCapturedAncestorParameters => "localCapturedAncestorParams",
        PropertyExposure.LocalOnlyConditionalAlgorithm => "localConditional",
        _ => throw new NotSupportedException($"Unhandled exposure '{exposure}'."),
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
        BinaryOp.Lt => "lt",
        BinaryOp.Gt => "gt",
        BinaryOp.Le => "le",
        BinaryOp.Ge => "ge",
        BinaryOp.Eq => "eq",
        BinaryOp.Ne => "ne",
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
    /// Lean <c>.num</c> takes an <c>Int</c>: every finite, exactly integral
    /// Decimal128 value is rendered in fixed-point form, independent of how the
    /// source literal was spelled or how the value's general formatter chooses
    /// exponent notation. Fractions, non-finite values, and negative zero are
    /// outside the Lean Int model and are refused rather than normalized to a
    /// different value.
    /// </summary>
    private static string EncodeNumber(Decimal128 value)
    {
        var display = value.ToString(CultureInfo.InvariantCulture);
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
