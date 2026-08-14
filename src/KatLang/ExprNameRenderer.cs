namespace KatLang;

/// <summary>
/// The rendering mode for one expression position inside a diagnostic name.
/// Modes reproduce the established context-sensitive parenthesization rules:
/// <see cref="Open"/> is the base spelling; the operand/target/selector modes wrap
/// forms whose bare rendering would rebind in source syntax; and
/// <see cref="DiagnosticName"/> is the operand-shape spelling used by binary
/// operand-shape contexts (bare top-level binary chains, zero-shape blocks and the
/// internal sequence joins rendered as one sequence value).
/// </summary>
internal enum ExprNameMode
{
    /// <summary>Base diagnostic spelling (Lean: openExprName).</summary>
    Open,

    /// <summary>
    /// Operand-shape spelling: a bare top-level binary chain, a zero-shape block as
    /// <c>(out1, out2, ...)</c>, and the internal sequence join as one sequence
    /// value; everything else falls back to <see cref="Open"/>.
    /// </summary>
    DiagnosticName,

    /// <summary>
    /// Unary operand position: parenthesized unless the operand is a leaf or a
    /// postfix form that binds tighter than unary.
    /// </summary>
    UnaryOperand,

    /// <summary>
    /// Postfix spread operand position. Spread binds to the completed operand, so a
    /// unary operand needs parentheses: <c>-A*</c> parses as unary minus applied to
    /// a spread, while <c>(-A)*</c> is the spread of the unary expression. Binary
    /// names already include their own parentheses.
    /// </summary>
    SpreadOperand,

    /// <summary>
    /// Index target position. Indexing is postfix and binds tighter than unary, so
    /// <c>-A:0</c> reads as <c>-(A:0)</c> and a unary target needs <c>(-A):0</c>.
    /// Postfix targets (<c>A:0:1</c>, <c>A.B:0</c>, <c>f(...):0</c>) are
    /// left-associative and render faithfully bare. Lean: indexTargetNeedsParens.
    /// </summary>
    IndexTarget,

    /// <summary>
    /// Index selector position. The selector is a primary in source syntax, so any
    /// form that would continue the postfix chain rebinds to the target instead
    /// (<c>A:B.C</c> reads as <c>(A:B).C</c>), and a bare negative literal
    /// (<c>A:-1</c>) is not selector syntax at all. Lean: indexSelectorNeedsParens.
    /// </summary>
    IndexSelector,
}

/// <summary>
/// Stack-safe, output-bounded renderer for expression names in diagnostics.
///
/// <para><b>Why this exists.</b> The former per-mode recursive renderers consumed
/// CLR stack proportional to the expression tree's depth. The evaluator's structural
/// preflight deliberately accepts arbitrarily long chains of the internal
/// sequence-join kinds (<see cref="Expr.SequenceConstruct"/>,
/// <see cref="Expr.SequenceSpread"/>) because every evaluation-path consumer walks
/// them iteratively — so a diagnostic renderer reached through a binary
/// operand-shape error, a call/dot-call context, an open-form error, or an optimizer
/// reason string had to stop being the one recursive consumer behind that gate.
/// This renderer walks with an explicit work stack, never recursing on the CLR
/// stack for ANY node kind, and never using record structural equality, recursive
/// hashing, or <c>ToString()</c> on the tree it renders.</para>
///
/// <para><b>Truncation contract.</b> Output is deterministic and bounded: at most
/// <see cref="MaxRenderedNameLength"/> UTF-16 units of rendered name, followed by
/// the repository's established <c>…</c> truncation marker when anything was
/// elided. Work is bounded by <see cref="MaxWorkItems"/> processed pieces (suffix-
/// positioned node kinds can be popped before contributing visible characters, so
/// an item cap — not only the character cap — keeps hostile trees from costing more
/// than the bounded output justifies); hitting either bound appends the same marker
/// once and stops. Names at or under the bounds render byte-identically to the
/// former recursive renderers.</para>
/// </summary>
internal static class ExprNameRenderer
{
    /// <summary>Maximum rendered name length in UTF-16 units, excluding the truncation marker.</summary>
    internal const int MaxRenderedNameLength = 512;

    /// <summary>
    /// Maximum work items processed for one rendered name. Suffix-heavy shapes
    /// (index/dot-call/call/spread chains) contribute at least one visible unit per
    /// node, so any tree that legitimately renders within
    /// <see cref="MaxRenderedNameLength"/> stays far below this; only trees that
    /// would also exceed the character bound can reach it.
    /// </summary>
    private const int MaxWorkItems = MaxRenderedNameLength * 8;

    /// <summary>The repository's established elision marker (see <c>KatLangEngine</c> display bounding).</summary>
    internal const string TruncationMarker = "…";

    /// <summary>
    /// One pending unit of rendering work: literal text, a node in a mode, or an
    /// indexed collection cursor. Collection cursors are important for the work
    /// bound: eagerly pushing every item of a hostile wide list/block would allocate
    /// proportional storage before <see cref="MaxWorkItems"/> could stop the render.
    /// A cursor schedules one item at a time, so auxiliary storage stays proportional
    /// to nesting depth and the work cap is effective for breadth as well as depth.
    /// </summary>
    private readonly struct Piece
    {
        public readonly string? Text;
        public readonly Expr? Node;
        public readonly IReadOnlyList<Expr>? Items;
        public readonly int ItemIndex;
        public readonly ExprNameMode Mode;

        public Piece(string text)
        {
            Text = text;
            Node = null;
            Items = null;
            ItemIndex = 0;
            Mode = default;
        }

        public Piece(Expr node, ExprNameMode mode)
        {
            Text = null;
            Node = node;
            Items = null;
            ItemIndex = 0;
            Mode = mode;
        }

        public Piece(IReadOnlyList<Expr> items, int itemIndex, ExprNameMode mode)
        {
            Text = null;
            Node = null;
            Items = items;
            ItemIndex = itemIndex;
            Mode = mode;
        }
    }

    /// <summary>Renders one expression name in the given mode.</summary>
    internal static string Render(Expr root, ExprNameMode mode)
    {
        // Leaf fast paths: identifier leaves render bare in EVERY mode, and they are
        // the overwhelmingly common case on the call paths that render names
        // eagerly, so they must not pay for the engine's stack and builder.
        if (root is Expr.Resolve(var resolveName))
            return CapLeafName(resolveName);
        if (root is Expr.Param(var paramName))
            return CapLeafName(paramName);

        var pending = new Stack<Piece>();
        pending.Push(new Piece(root, mode));
        return Drain(pending);
    }

    /// <summary>
    /// Renders the binary operand-shape name <c>left op right</c> (both operands in
    /// <see cref="ExprNameMode.DiagnosticName"/>, no outer parentheses).
    /// </summary>
    internal static string RenderBinaryDiagnosticName(BinaryOp op, Expr left, Expr right)
    {
        var pending = new Stack<Piece>();
        pending.Push(new Piece(right, ExprNameMode.DiagnosticName));
        pending.Push(new Piece(SpacedBinaryOpText(op)));
        pending.Push(new Piece(left, ExprNameMode.DiagnosticName));
        return Drain(pending);
    }

    private static string CapLeafName(string name)
    {
        if (name.Length <= MaxRenderedNameLength)
            return name;

        var prefixLength = SafePrefixLength(name, MaxRenderedNameLength);
        return name[..prefixLength] + TruncationMarker;
    }

    private static string Drain(Stack<Piece> pending)
    {
        var builder = new System.Text.StringBuilder();
        var itemsProcessed = 0;
        while (pending.Count > 0)
        {
            if (++itemsProcessed > MaxWorkItems)
                return Truncated(builder);

            var piece = pending.Pop();
            if (piece.Text is { } text)
            {
                if (!Append(builder, text))
                    return Truncated(builder);
                continue;
            }

            if (piece.Items is { } items)
            {
                // Schedule exactly one collection item. This preserves the former
                // left-to-right spelling while preventing a wide host-owned list from
                // filling the pending stack before either renderer bound is checked.
                if (piece.ItemIndex >= items.Count)
                    continue;

                pending.Push(new Piece(items, piece.ItemIndex + 1, piece.Mode));
                pending.Push(new Piece(items[piece.ItemIndex], piece.Mode));
                if (piece.ItemIndex > 0)
                    pending.Push(new Piece(", "));
                continue;
            }

            if (!Expand(builder, pending, piece.Node!, piece.Mode))
                return Truncated(builder);
        }

        return builder.ToString();
    }

    private static string Truncated(System.Text.StringBuilder builder)
        => builder.Append(TruncationMarker).ToString();

    /// <summary>Appends within the length bound; false once the bound is reached.</summary>
    private static bool Append(System.Text.StringBuilder builder, string text)
    {
        var room = MaxRenderedNameLength - builder.Length;
        if (text.Length <= room)
        {
            builder.Append(text);
            return true;
        }

        builder.Append(text, 0, SafePrefixLength(text, room));
        return false;
    }

    /// <summary>
    /// Returns a prefix length no greater than <paramref name="maximumLength"/> that
    /// does not split a well-formed UTF-16 surrogate pair at the truncation boundary.
    /// Ill-formed caller text is otherwise preserved; the renderer never creates a
    /// new unpaired surrogate from a valid payload.
    /// </summary>
    private static int SafePrefixLength(string text, int maximumLength)
    {
        var length = Math.Min(text.Length, maximumLength);
        if (length > 0
            && length < text.Length
            && char.IsHighSurrogate(text[length - 1])
            && char.IsLowSurrogate(text[length]))
        {
            length--;
        }

        return length;
    }

    /// <summary>
    /// Appends a repeated character within the length bound without materializing
    /// the full run (the count is host-controlled via <see cref="Expr.EmptySequence"/>
    /// and may be enormous or negative; negative counts append nothing).
    /// </summary>
    private static bool AppendRepeated(System.Text.StringBuilder builder, char ch, long count)
    {
        var room = MaxRenderedNameLength - builder.Length;
        if (count <= room)
        {
            for (var i = 0L; i < count; i++)
                builder.Append(ch);
            return true;
        }

        for (var i = 0; i < room; i++)
            builder.Append(ch);
        return false;
    }

    /// <summary>
    /// Renders one node in one mode: either appends its leaf text directly or pushes
    /// its child pieces (in reverse, so they pop in reading order). Returns false
    /// only when the output bound was reached.
    /// </summary>
    private static bool Expand(System.Text.StringBuilder builder, Stack<Piece> pending, Expr node, ExprNameMode mode)
    {
        // Mode-specific wrapping decisions first; every mode then shares the base
        // Open spelling below for whatever it did not wrap or special-case.
        switch (mode)
        {
            case ExprNameMode.DiagnosticName:
                switch (node)
                {
                    // A capture renders as one written sequence value over its
                    // body slots.
                    case Expr.Capture(var captureBody):
                    {
                        pending.Push(new Piece(")"));
                        pending.Push(new Piece(
                            captureBody, 0, ExprNameMode.DiagnosticName));
                        pending.Push(new Piece("("));
                        return true;
                    }

                    // A zero-shape scoped block renders the same way over its
                    // output slots. Parameters.Count equals the derived Params.Count by
                    // construction, without materializing the name list.
                    case Expr.AlgorithmExpr(var algorithm) when algorithm.Parameters.Count == 0
                        && algorithm.Opens.Count == 0
                        && algorithm.Properties.Count == 0:
                    {
                        pending.Push(new Piece(")"));
                        pending.Push(new Piece(
                            algorithm.Output, 0, ExprNameMode.DiagnosticName));
                        pending.Push(new Piece("("));
                        return true;
                    }

                    // A top-level binary chain renders bare, without the outer
                    // parentheses the Open spelling adds.
                    case Expr.Binary(var op, var left, var right):
                        pending.Push(new Piece(right, ExprNameMode.DiagnosticName));
                        pending.Push(new Piece(SpacedBinaryOpText(op)));
                        pending.Push(new Piece(left, ExprNameMode.DiagnosticName));
                        return true;

                    // The internal SequenceConstruct join renders as one sequence
                    // value; ';' is not surface syntax.
                    case Expr.SequenceConstruct(var left, var right):
                        pending.Push(new Piece(")"));
                        pending.Push(new Piece(right, ExprNameMode.DiagnosticName));
                        pending.Push(new Piece(", "));
                        pending.Push(new Piece(left, ExprNameMode.DiagnosticName));
                        pending.Push(new Piece("("));
                        return true;
                }

                break;

            case ExprNameMode.UnaryOperand:
                if (node is not (Expr.Param or Expr.Resolve or Expr.Num or Expr.StringLiteral
                    or Expr.DotCall or Expr.Index))
                {
                    return PushParenthesized(pending, node);
                }

                break;

            case ExprNameMode.SpreadOperand:
            case ExprNameMode.IndexTarget:
                if (node is Expr.Unary)
                    return PushParenthesized(pending, node);
                break;

            case ExprNameMode.IndexSelector:
                if (node is Expr.Unary or Expr.Call or Expr.DotCall or Expr.Index
                    or Expr.SequenceSpread or Expr.Num { Value: < 0 })
                {
                    return PushParenthesized(pending, node);
                }

                break;
        }

        // Base Open spelling (Lean: openExprName).
        switch (node)
        {
            case Expr.Resolve(var name):
                return Append(builder, name);
            case Expr.Param(var name):
                return Append(builder, name);
            case Expr.Num(var value):
                return Append(builder, value.ToString(System.Globalization.CultureInfo.InvariantCulture));
            case Expr.StringLiteral(var value):
                return Append(builder, "'") && Append(builder, value) && Append(builder, "'");

            case Expr.Unary(var op, var operand):
                switch (op)
                {
                    case UnaryOp.Minus:
                        pending.Push(new Piece(operand, ExprNameMode.UnaryOperand));
                        pending.Push(new Piece("-"));
                        return true;
                    case UnaryOp.Not:
                        pending.Push(new Piece(operand, ExprNameMode.UnaryOperand));
                        pending.Push(new Piece("not "));
                        return true;
                    default:
                        return Append(builder, $"({Evaluator.ExprKind(node)})");
                }

            case Expr.Binary(var op, var left, var right):
                pending.Push(new Piece(")"));
                pending.Push(new Piece(right, ExprNameMode.Open));
                pending.Push(new Piece(SpacedBinaryOpText(op)));
                pending.Push(new Piece(left, ExprNameMode.Open));
                pending.Push(new Piece("("));
                return true;

            // Diagnostic expression names use KatLang source syntax: indexing is
            // postfix `target:selector`, never `target[selector]` (`[...]` is exact
            // list literal syntax, so bracket text would read back as adjacency).
            case Expr.Index(var target, var selector):
                pending.Push(new Piece(selector, ExprNameMode.IndexSelector));
                pending.Push(new Piece(":"));
                pending.Push(new Piece(target, ExprNameMode.IndexTarget));
                return true;

            case Expr.DotCall(var target, var name, var argsOpt):
                if (argsOpt is not null)
                    pending.Push(new Piece("(...)"));
                pending.Push(new Piece(name));
                pending.Push(new Piece("."));
                pending.Push(new Piece(target, ExprNameMode.Open));
                return true;

            case Expr.Call(var function, _):
                pending.Push(new Piece("(...)"));
                pending.Push(new Piece(function, ExprNameMode.Open));
                return true;

            case Expr.Grace(var inner, var weight):
                if (weight < 0)
                {
                    pending.Push(new Piece(inner, ExprNameMode.Open));
                    pending.Push(new Piece("~"));
                }
                else
                {
                    pending.Push(new Piece("~"));
                    pending.Push(new Piece(inner, ExprNameMode.Open));
                }

                return true;

            case Expr.AlgorithmExpr or Expr.Capture:
                return Append(builder, "(inline library)");

            // SequenceConstruct is an internal value node; ';' is not surface
            // syntax, so render it as one sequence value, never with ';'.
            case Expr.SequenceConstruct(var left, var right):
                pending.Push(new Piece(")"));
                pending.Push(new Piece(right, ExprNameMode.Open));
                pending.Push(new Piece(", "));
                pending.Push(new Piece(left, ExprNameMode.Open));
                pending.Push(new Piece("("));
                return true;

            // A spread expression renders in the canonical postfix-marker form.
            case Expr.SequenceSpread(var operand):
                pending.Push(new Piece("*"));
                pending.Push(new Piece(operand, ExprNameMode.SpreadOperand));
                return true;

            // Exact list literal `[a, b, c]`.
            case Expr.ListLiteral(var items):
            {
                pending.Push(new Piece("]"));
                pending.Push(new Piece(items, 0, ExprNameMode.Open));
                pending.Push(new Piece("["));
                return true;
            }

            // Empty sequence core nodes render by depth for diagnostics; evaluation
            // canonicalizes repeated ordinary parentheses back to `()`.
            case Expr.EmptySequence(var depth):
                return AppendRepeated(builder, '(', (long)depth + 1)
                    && AppendRepeated(builder, ')', (long)depth + 1);

            default:
                return Append(builder, $"({Evaluator.ExprKind(node)})");
        }
    }

    private static bool PushParenthesized(Stack<Piece> pending, Expr node)
    {
        pending.Push(new Piece(")"));
        pending.Push(new Piece(node, ExprNameMode.Open));
        pending.Push(new Piece("("));
        return true;
    }

    /// <summary>Bare source spelling of a binary operator for diagnostics.</summary>
    internal static string BinaryOpText(BinaryOp op) => op switch
    {
        BinaryOp.Add => "+",
        BinaryOp.Sub => "-",
        BinaryOp.Mul => "*",
        BinaryOp.Div => "/",
        BinaryOp.IDiv => "div",
        BinaryOp.Mod => "mod",
        BinaryOp.Pow => "^",
        BinaryOp.Lt => "<",
        BinaryOp.Gt => ">",
        BinaryOp.Le => "<=",
        BinaryOp.Ge => ">=",
        BinaryOp.Eq => "==",
        BinaryOp.Ne => "!=",
        BinaryOp.And => "and",
        BinaryOp.Or => "or",
        BinaryOp.Xor => "xor",
        _ => "?",
    };

    private static string SpacedBinaryOpText(BinaryOp op) => op switch
    {
        BinaryOp.Add => " + ",
        BinaryOp.Sub => " - ",
        BinaryOp.Mul => " * ",
        BinaryOp.Div => " / ",
        BinaryOp.IDiv => " div ",
        BinaryOp.Mod => " mod ",
        BinaryOp.Pow => " ^ ",
        BinaryOp.Lt => " < ",
        BinaryOp.Gt => " > ",
        BinaryOp.Le => " <= ",
        BinaryOp.Ge => " >= ",
        BinaryOp.Eq => " == ",
        BinaryOp.Ne => " != ",
        BinaryOp.And => " and ",
        BinaryOp.Or => " or ",
        BinaryOp.Xor => " xor ",
        _ => " ? ",
    };
}
