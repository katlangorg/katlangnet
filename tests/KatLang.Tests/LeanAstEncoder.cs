using System.Globalization;
using System.Text;

namespace KatLang.Tests;

/// <summary>
/// Prints an elaborated C# AST in the Lean constructor syntax used by
/// <c>lean/SemanticExplorerCases.lean</c>.
///
/// <para>
/// Track 9 found a corpus-fidelity defect where a hand-written Lean program
/// declared <c>publicProp "X"</c> for source that actually elaborates <c>X</c>
/// as PRIVATE, so 109 differential cases compared structurally different
/// programs. This encoder exists so the <c>open</c>/visibility family — where
/// exposure metadata IS the semantics under test — can be checked mechanically
/// instead of by eye (see <c>OpenVisibilityCorpusFidelityTests</c>).
/// </para>
///
/// <para>
/// Coverage is deliberately narrow: exactly the node kinds the
/// <c>open</c>/visibility family uses. Anything else throws rather than
/// printing something plausible but wrong — an encoder that silently
/// approximated would reintroduce the very defect it guards against.
/// </para>
/// </summary>
public static class LeanAstEncoder
{
    /// <summary>Encodes a parsed root algorithm as a Lean <c>.block (alg ...)</c> program.</summary>
    public static string EncodeProgram(Algorithm root) => $".block {EncodeAlgorithm(root)}";

    /// <summary>
    /// Bare encoding, suitable where a delimiter already separates terms (list
    /// elements). Use <see cref="Arg"/> for anything in Lean application
    /// position, which needs parentheses around multi-token terms.
    /// </summary>
    public static string EncodeExpr(Expr expr) => expr switch
    {
        Expr.Num(var value) => $".num {EncodeNumber(value)}",
        Expr.StringLiteral(var value) => $".stringLiteral \"{value}\"",
        Expr.EmptySequence(var depth) => $"(.emptySequence {depth})",
        Expr.Resolve(var name) => $".resolve \"{name}\"",
        Expr.Param(var name) => $".param \"{name}\"",
        Expr.Block(var algorithm) => $"(.block {EncodeAlgorithm(algorithm)})",
        Expr.ListLiteral(var items) => $"(.listLiteral [{EncodeList(items, EncodeExpr)}])",
        Expr.SequenceSpread(var operand) => $"(.sequenceSpread {Arg(operand)})",
        Expr.Unary(var op, var operand) => $"(.unary .{EncodeUnaryOp(op)} {Arg(operand)})",
        Expr.Binary(var op, var left, var right) =>
            $"(.binary .{EncodeBinaryOp(op)} {Arg(left)} {Arg(right)})",
        Expr.DotCall(var target, var name, var args) =>
            $"(.dotCall {Arg(target)} \"{name}\" {(args is null ? "none" : $"(some {EncodeAlgorithm(args)})")})",
        Expr.Call(var callee, var args) => $"(.call {Arg(callee)} {EncodeAlgorithm(args)})",
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

    public static string EncodeAlgorithm(Algorithm algorithm)
    {
        if (algorithm is not Algorithm.User user)
        {
            throw new NotSupportedException(
                $"{nameof(LeanAstEncoder)} covers Algorithm.User only, not {algorithm.GetType().Name}.");
        }

        foreach (var parameter in user.Parameters)
        {
            if (parameter.Kind != ParameterKind.Normal)
            {
                throw new NotSupportedException(
                    $"{nameof(LeanAstEncoder)} covers normal parameters only ('{parameter.Name}' is {parameter.Kind}); " +
                    "a collecting or patterned parameter needs algWithParameters/algWithParameterPatterns.");
            }
        }

        var parameters = EncodeList(user.Parameters, static p => $"\"{p.Name}\"");
        var opens = EncodeList(user.Opens, EncodeExpr);
        var properties = EncodeList(user.Properties, EncodeProperty);
        var output = EncodeList(user.Output, EncodeExpr);
        return $"(alg [{parameters}] [{opens}] [{properties}] [{output}])";
    }

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
            (false, PropertyExposure.Exported) => $"privateProp \"{property.Name}\" {value}",
            (true, PropertyExposure.Exported) => $"publicProp \"{property.Name}\" {value}",
            (false, var exposure) => $"privateLocalProp \"{property.Name}\" .{EncodeExposure(exposure)} {value}",
            (true, var exposure) => $"publicLocalProp \"{property.Name}\" .{EncodeExposure(exposure)} {value}",
        };
    }

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
        _ => throw new NotSupportedException($"Unhandled binary operator '{op}'."),
    };

    private static string EncodeUnaryOp(UnaryOp op) => op switch
    {
        UnaryOp.Minus => "minus",
        UnaryOp.Not => "not",
        _ => throw new NotSupportedException($"Unhandled unary operator '{op}'."),
    };

    private static string EncodeNumber(decimal value)
        => value < 0
            ? $"({value.ToString(CultureInfo.InvariantCulture)})"
            : value.ToString(CultureInfo.InvariantCulture);

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
