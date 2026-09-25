namespace KatLang;

/// <summary>
/// The rendering mode for one expression position inside a diagnostic name.
/// Modes reproduce the established context-sensitive parenthesization rules:
/// <see cref="Open"/> is the base spelling (every binary and comparison-chain name
/// self-parenthesizes); the operand/target/selector modes wrap forms whose bare
/// rendering would rebind in source syntax; and <see cref="DiagnosticName"/> is the
/// operand-shape spelling used by operand-shape contexts (the "while evaluating
/// `…`" frames): operators render bare and every operand keeps exactly the
/// parentheses the precedence ladder needs.
/// </summary>
internal enum ExprNameMode
{
    /// <summary>Base diagnostic spelling (Lean: openExprName).</summary>
    Open,

    /// <summary>
    /// Operand-shape spelling (Lean: <c>exprDiagnosticName</c>): a binary node, a
    /// comparison chain, and a prefix operator render bare at the top with their
    /// operands parenthesized by the precedence-tier rule (<c>(a + b) * c</c>,
    /// <c>a &lt; b &lt;= c</c>, <c>(a &lt; b) == c</c>, <c>-(a + b)</c>), a zero-shape
    /// block renders as <c>(out1, out2, ...)</c>, and the internal sequence join as one
    /// sequence value; everything else falls back to <see cref="Open"/>.
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
        public readonly IReadOnlyList<ComparisonLink>? Links;
        public readonly int ItemIndex;
        public readonly ExprNameMode Mode;

        public Piece(string text)
        {
            Text = text;
            Node = null;
            Items = null;
            Links = null;
            ItemIndex = 0;
            Mode = default;
        }

        public Piece(Expr node, ExprNameMode mode)
        {
            Text = null;
            Node = node;
            Items = null;
            Links = null;
            ItemIndex = 0;
            Mode = mode;
        }

        public Piece(IReadOnlyList<Expr> items, int itemIndex, ExprNameMode mode)
        {
            Text = null;
            Node = null;
            Items = items;
            Links = null;
            ItemIndex = itemIndex;
            Mode = mode;
        }

        /// <summary>A comparison-chain link cursor: the link at <paramref name="linkIndex"/> is rendered next.</summary>
        public Piece(IReadOnlyList<ComparisonLink> links, int linkIndex, ExprNameMode mode)
        {
            Text = null;
            Node = null;
            Items = null;
            Links = links;
            ItemIndex = linkIndex;
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
        PushBinaryRightOperand(pending, op, right, ExprNameMode.DiagnosticName);
        pending.Push(new Piece(SpacedBinaryOpText(op)));
        PushBinaryLeftOperand(pending, op, left, ExprNameMode.DiagnosticName);
        return Drain(pending);
    }

    /// <summary>
    /// Renders ONE link of a comparison chain in operand shape — <c>left op right</c>,
    /// the two ADJACENT operands the link compares, in
    /// <see cref="ExprNameMode.DiagnosticName"/> with no outer parentheses — so the
    /// failing link of <c>1 &lt; 2 &lt; true</c> reads <c>2 &lt; true</c>, never a
    /// nested spelling of the whole chain. Lean: <c>comparisonLinkDiagnosticName</c>.
    /// </summary>
    internal static string RenderComparisonLinkDiagnosticName(ComparisonOp op, Expr left, Expr right)
    {
        var pending = new Stack<Piece>();
        PushComparisonOperand(pending, right, ExprNameMode.DiagnosticName);
        pending.Push(new Piece(SpacedComparisonOpText(op)));
        PushComparisonOperand(pending, left, ExprNameMode.DiagnosticName);
        return Drain(pending);
    }

    // ── Precedence tiers (the ONE parenthesization rule) ─────────────────────
    //
    // A rendered name must read back as the AST it was rendered from, so an
    // operand is parenthesized exactly when it binds LOOSER than the position it
    // is written in. The tiers mirror the parser's ladder (Parser.cs, "Precedence
    // levels"); Lean: `bindingTier` and the slot tiers of `exprDiagnosticName`.

    private const int OrTier = 1;
    private const int XorTier = 2;
    private const int AndTier = 3;
    private const int NotTier = 4;
    private const int ComparisonTier = 5;
    private const int AdditiveTier = 6;
    private const int MultiplicativeTier = 7;
    private const int UnaryMinusTier = 8;
    private const int PowerTier = 9;
    private const int PostfixTier = 10;
    private const int AtomTier = 11;

    private static int BinaryOperatorTier(BinaryOp op) => op switch
    {
        BinaryOp.Or => OrTier,
        BinaryOp.Xor => XorTier,
        BinaryOp.And => AndTier,
        BinaryOp.Add or BinaryOp.Sub => AdditiveTier,
        BinaryOp.Mul or BinaryOp.Div or BinaryOp.IDiv or BinaryOp.Mod => MultiplicativeTier,
        BinaryOp.Pow => PowerTier,
        _ => AtomTier,
    };

    /// <summary>
    /// How tightly <paramref name="expr"/> binds when rendered bare. Prefix forms
    /// take their operator's tier (a literal whose text begins with a minus —
    /// including -0 and -Infinity, never NaN — reads back as a prefix minus);
    /// postfix forms and the self-delimiting spellings (leaves, captures, lists,
    /// blocks, the parenthesized internal join) never rebind. Lean: <c>bindingTier</c>.
    /// </summary>
    private static int BindingTier(Expr expr) => expr switch
    {
        Expr.Binary binary => BinaryOperatorTier(binary.Op),
        Expr.Comparison { Links.Count: 0 } => AtomTier,
        Expr.Comparison => ComparisonTier,
        Expr.Unary { Op: UnaryOp.Not } => NotTier,
        Expr.Unary => UnaryMinusTier,
        Expr.Num numLiteral when NumericLiteralRendersWithLeadingMinus(numLiteral.Value) => UnaryMinusTier,
        Expr.Index or Expr.DotCall or Expr.Call or Expr.SequenceSpread or Expr.Grace => PostfixTier,
        _ => AtomTier,
    };

    /// <summary>
    /// The binding tier of <paramref name="expr"/> as rendered in <paramref name="mode"/>:
    /// in <see cref="ExprNameMode.Open"/> a binary or comparison node prints inside its
    /// own parentheses, so it is self-delimiting there and only the prefix forms can
    /// rebind; in <see cref="ExprNameMode.DiagnosticName"/> every operand prints bare
    /// and is judged by its real tier.
    /// </summary>
    private static int BindingTier(Expr expr, ExprNameMode mode)
        => mode == ExprNameMode.Open && expr is Expr.Binary or Expr.Comparison
            ? AtomTier
            : BindingTier(expr);

    /// <summary>
    /// The tier a binary operator's LEFT operand is written at: the operator's own
    /// tier for the left-associative operators (an equal-tier left operand reads back
    /// unchanged), the postfix tier for `^`, whose base is postfix-level — a unary base
    /// or a leading-minus literal must keep its parentheses, or `-a ^ b` would read back
    /// as `-(a ^ b)`, and `(a ^ b) ^ c` would read back right-associated.
    /// </summary>
    private static int LeftOperandTier(BinaryOp op)
        => op == BinaryOp.Pow ? PostfixTier : BinaryOperatorTier(op);

    /// <summary>
    /// The tier a binary operator's RIGHT operand is written at: one above the operator
    /// for the left-associative operators (`a - (b - c)` keeps its parentheses), the
    /// unary tier for `^`, whose exponent re-enters the unary level (`a ^ -b` and
    /// `a ^ b ^ c` read back with the same AST).
    /// </summary>
    private static int RightOperandTier(BinaryOp op)
        => op == BinaryOp.Pow ? UnaryMinusTier : BinaryOperatorTier(op) + 1;

    /// <summary>
    /// True exactly when Decimal128's invariant diagnostic text begins with a
    /// minus. <see cref="System.Numerics.Decimal128.IsNegative(System.Numerics.Decimal128)"/>
    /// also observes the sign bit of NaN, but Decimal128 renders every NaN as
    /// unsigned <c>NaN</c>, so sign-bit testing alone would add parentheses for
    /// text that cannot rebind as unary minus.
    /// </summary>
    private static bool NumericLiteralRendersWithLeadingMinus(System.Numerics.Decimal128 value)
        => !System.Numerics.Decimal128.IsNaN(value)
            && System.Numerics.Decimal128.IsNegative(value);

    /// <summary>Pushes <paramref name="operand"/> in <paramref name="mode"/>, parenthesized iff it binds looser than <paramref name="slotTier"/>.</summary>
    private static void PushOperand(Stack<Piece> pending, Expr operand, int slotTier, ExprNameMode mode)
    {
        if (BindingTier(operand, mode) < slotTier)
        {
            pending.Push(new Piece(")"));
            pending.Push(new Piece(operand, mode));
            pending.Push(new Piece("("));
            return;
        }

        pending.Push(new Piece(operand, mode));
    }

    /// <summary>
    /// Pushes a binary node's LEFT operand in <paramref name="mode"/>, parenthesized
    /// when it binds looser than <see cref="LeftOperandTier"/> — a rebinding power
    /// base, a `not` under a tighter operator, a looser binary or a comparison chain
    /// under an arithmetic operator. The child keeps its surrounding mode so
    /// capture/block spellings are unchanged inside the added parentheses.
    /// </summary>
    private static void PushBinaryLeftOperand(Stack<Piece> pending, BinaryOp op, Expr left, ExprNameMode mode)
        => PushOperand(pending, left, LeftOperandTier(op), mode);

    /// <summary>
    /// Pushes a binary node's RIGHT operand in <paramref name="mode"/>, parenthesized
    /// when it binds looser than <see cref="RightOperandTier"/>; a unary minus
    /// exponent or operand stays bare, as its tier allows.
    /// </summary>
    private static void PushBinaryRightOperand(Stack<Piece> pending, BinaryOp op, Expr right, ExprNameMode mode)
        => PushOperand(pending, right, RightOperandTier(op), mode);

    /// <summary>
    /// Pushes one operand of a comparison chain in <paramref name="mode"/>. A chain
    /// operand is written at the additive tier: a nested chain (`(a &lt; b) == c` is
    /// not the chain `a &lt; b == c`), a `not`, and the logical operators keep their
    /// parentheses; arithmetic, powers, prefix minus, and postfix forms read back bare.
    /// </summary>
    private static void PushComparisonOperand(Stack<Piece> pending, Expr operand, ExprNameMode mode)
        => PushOperand(pending, operand, AdditiveTier, mode);

    /// <summary>
    /// Pushes a whole comparison chain — <c>first op1 x1 op2 x2 …</c> — with every
    /// operand in <paramref name="mode"/> under the comparison-operand rule. The links
    /// are scheduled through a CURSOR (one link at a time, like a wide list's items),
    /// so a host-built chain with an enormous link list never fills the pending stack
    /// before the renderer's bounds are checked.
    /// </summary>
    private static void PushComparisonChain(Stack<Piece> pending, Expr first, IReadOnlyList<ComparisonLink> links, ExprNameMode mode)
    {
        pending.Push(new Piece(links, 0, mode));
        PushComparisonOperand(pending, first, mode);
    }

    /// <summary>Schedules the link at <paramref name="index"/>: its operator text, then its operand, then the cursor for the next link.</summary>
    private static void PushComparisonLink(Stack<Piece> pending, IReadOnlyList<ComparisonLink> links, int index, ExprNameMode mode)
    {
        pending.Push(new Piece(links, index + 1, mode));
        PushComparisonOperand(pending, links[index].Operand, mode);
        pending.Push(new Piece(SpacedComparisonOpText(links[index].Op)));
    }

    /// <summary>
    /// Pushes a prefix operator's operand in <see cref="ExprNameMode.DiagnosticName"/>:
    /// a `not` operand keeps its parentheses only when it binds looser than `not` (a
    /// logical binary: `not (a and b)`; a comparison chain reads back bare, `not a &lt; b`
    /// IS `not (a &lt; b)`), a minus operand when it binds no tighter than the prefix
    /// tier itself (`-(a + b)`, `-(a &lt; b)`, `-(not a)`, `-(-a)`; a power reads back
    /// bare, `-a ^ b` IS `-(a ^ b)`).
    /// </summary>
    private static void PushDiagnosticUnaryOperand(Stack<Piece> pending, UnaryOp op, Expr operand)
        => PushOperand(
            pending,
            operand,
            op == UnaryOp.Not ? NotTier : UnaryMinusTier + 1,
            ExprNameMode.DiagnosticName);

    private static string CapLeafName(string name)
    {
        if (name.Length <= MaxRenderedNameLength)
            return name;

        var prefixLength = SafePrefixLength(name, MaxRenderedNameLength);
        return name[..prefixLength] + TruncationMarker;
    }

    /// <summary>
    /// Bounds ONE source-derived name a front-end diagnostic echoes to the rendered-name bound,
    /// with the same marker as a rendered name. A declaration's name echoed by every diagnostic
    /// about its references (a clause family's name, say) would otherwise repeat the whole
    /// identifier per reference — text quadratic in the source.
    /// </summary>
    internal static string BoundName(string name) => CapLeafName(name);

    /// <summary>
    /// Joins source-derived names for a front-end diagnostic within the rendered-name bound,
    /// reading only the names it shows — so a parameter list echoed once per reference costs a
    /// bounded amount per diagnostic, however long the list. Output that fits is byte-identical to
    /// <c>string.Join(separator, names)</c>; longer output keeps its surrogate-safe prefix and the
    /// marker.
    /// </summary>
    internal static string BoundedJoin(IEnumerable<string> names, string separator)
    {
        var sink = new Rendering.BoundedDiagnosticSink(MaxRenderedNameLength);
        var first = true;
        foreach (var name in names)
        {
            if (!first && !sink.Append(separator))
                break;
            first = false;
            if (!sink.Append(name))
                break;
        }

        return sink.Finish();
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

            if (piece.Links is { } links)
            {
                // Schedule exactly one chain link, for the same reason as one list item.
                if (piece.ItemIndex >= links.Count)
                    continue;

                PushComparisonLink(pending, links, piece.ItemIndex, piece.Mode);
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
    /// Returns a prefix length no greater than a non-negative
    /// <paramref name="maximumLength"/> that does not split a well-formed UTF-16
    /// surrogate pair at the truncation boundary. A non-positive maximum returns zero.
    /// Ill-formed caller text is otherwise preserved; the renderer never creates a
    /// new unpaired surrogate from a valid payload.
    ///
    /// <para>Shared with <see cref="Rendering.BoundedDiagnosticSink"/> so both bounded
    /// diagnostic fragments cut text at the same boundary.</para>
    /// </summary>
    internal static int SafePrefixLength(string text, int maximumLength)
    {
        var length = Math.Clamp(maximumLength, 0, text.Length);
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
        // A host-only vacuous chain evaluates its operand but returns true. It
        // has no source spelling: printing just its operand would name a
        // different expression (e.g. 7 instead of a Boolean-producing chain).
        if (node is Expr.Comparison { Links.Count: 0 })
            return Append(builder, "<comparison with no links>");

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
                    case Expr.AlgorithmExpr(var algorithm) when algorithm.ParameterCount == 0
                        && algorithm.Opens.Count == 0
                        && algorithm.Properties.Count == 0:
                    {
                        pending.Push(new Piece(")"));
                        pending.Push(new Piece(
                            algorithm.Output, 0, ExprNameMode.DiagnosticName));
                        pending.Push(new Piece("("));
                        return true;
                    }

                    // A top-level binary renders bare, without the outer
                    // parentheses the Open spelling adds; its operands render
                    // bare too and keep parentheses exactly where the precedence
                    // ladder needs them (PushBinaryLeftOperand /
                    // PushBinaryRightOperand), so the text reads back as this tree.
                    case Expr.Binary(var op, var left, var right):
                        PushBinaryRightOperand(pending, op, right, ExprNameMode.DiagnosticName);
                        pending.Push(new Piece(SpacedBinaryOpText(op)));
                        PushBinaryLeftOperand(pending, op, left, ExprNameMode.DiagnosticName);
                        return true;

                    // A comparison chain renders as the flat chain it is —
                    // `a < b <= c == d` — never as nested binary comparisons; a
                    // parenthesized nested chain keeps its parentheses.
                    case Expr.Comparison(var first, var links):
                        PushComparisonChain(pending, first, links, ExprNameMode.DiagnosticName);
                        return true;

                    // A prefix operator renders its operand bare unless the
                    // operand binds looser than the operator (PushDiagnosticUnaryOperand).
                    case Expr.Unary(var unaryOp, var unaryOperand):
                        PushDiagnosticUnaryOperand(pending, unaryOp, unaryOperand);
                        pending.Push(new Piece(unaryOp == UnaryOp.Minus ? "-" : "not "));
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
                if (node is not (Expr.Param or Expr.Resolve or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral
                    or Expr.DotCall or Expr.Index))
                {
                    return PushParenthesized(pending, node);
                }

                break;

            case ExprNameMode.SpreadOperand:
            case ExprNameMode.IndexTarget:
                if (BindingTier(node, ExprNameMode.Open) < PostfixTier)
                    return PushParenthesized(pending, node);
                break;

            case ExprNameMode.IndexSelector:
                // The shared rendered-sign predicate matches exactly the literals whose
                // text begins with a minus (including -0 and -Infinity), which is what
                // needs parenthesizing in selector position; NaN renders unsigned.
                if (node is Expr.Unary or Expr.Call or Expr.DotCall or Expr.Index
                    or Expr.SequenceSpread
                    || (node is Expr.Num negativeLiteral
                        && NumericLiteralRendersWithLeadingMinus(negativeLiteral.Value)))
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
                return Append(builder, Rendering.ValueTextRenderer.FormatNumberInvariant(value));
            case Expr.StringLiteral(var value):
                return Append(builder, "'") && Append(builder, value) && Append(builder, "'");
            case Expr.BoolLiteral(var value):
                return Append(builder, Rendering.ValueTextRenderer.FormatBool(value));

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

            // Binary open names self-parenthesize; a rebinding power base or a
            // `not` operand under a tighter operator additionally keeps its own
            // parentheses (PushBinaryLeftOperand / PushBinaryRightOperand).
            case Expr.Binary(var op, var left, var right):
                pending.Push(new Piece(")"));
                PushBinaryRightOperand(pending, op, right, ExprNameMode.Open);
                pending.Push(new Piece(SpacedBinaryOpText(op)));
                PushBinaryLeftOperand(pending, op, left, ExprNameMode.Open);
                pending.Push(new Piece("("));
                return true;

            // Comparison-chain open names self-parenthesize like binary names,
            // rendering the whole chain flat (`(a < b == c)`); a `not` operand
            // keeps its own parentheses (PushComparisonOperand).
            case Expr.Comparison(var first, var links):
                pending.Push(new Piece(")"));
                PushComparisonChain(pending, first, links, ExprNameMode.Open);
                pending.Push(new Piece("("));
                return true;

            // Diagnostic expression names use KatLang source syntax: indexing is
            // postfix `target:selector`, never `target[selector]` (`[...]` is exact
            // list literal syntax, so bracket text would read back as a list
            // literal after the target, not as an index).
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
                PushOperand(pending, target, PostfixTier, ExprNameMode.Open);
                return true;

            case Expr.Call(var function, _):
                pending.Push(new Piece("(...)"));
                PushOperand(pending, function, PostfixTier, ExprNameMode.Open);
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

            // A brace block is an opaque algorithm literal; a capture is the written
            // parenthesized group and renders as such (its rows, bounded like every
            // other composite), never as a "library" — a capture is a value boundary,
            // not algorithm identity.
            case Expr.AlgorithmExpr:
                return Append(builder, "{...}");

            case Expr.Capture(var slots):
            {
                pending.Push(new Piece(")"));
                pending.Push(new Piece(slots, 0, ExprNameMode.Open));
                pending.Push(new Piece("("));
                return true;
            }

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
            // normalizes repeated ordinary parentheses back to `()`.
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
        BinaryOp.And => "and",
        BinaryOp.Or => "or",
        BinaryOp.Xor => "xor",
        _ => "?",
    };

    /// <summary>Bare source spelling of a comparison operator for diagnostics. Lean: <c>ComparisonOp.symbol</c>.</summary>
    internal static string ComparisonOpText(ComparisonOp op) => op switch
    {
        ComparisonOp.Lt => "<",
        ComparisonOp.Gt => ">",
        ComparisonOp.Le => "<=",
        ComparisonOp.Ge => ">=",
        ComparisonOp.Eq => "==",
        ComparisonOp.Ne => "!=",
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
        BinaryOp.And => " and ",
        BinaryOp.Or => " or ",
        BinaryOp.Xor => " xor ",
        _ => " ? ",
    };

    private static string SpacedComparisonOpText(ComparisonOp op) => op switch
    {
        ComparisonOp.Lt => " < ",
        ComparisonOp.Gt => " > ",
        ComparisonOp.Le => " <= ",
        ComparisonOp.Ge => " >= ",
        ComparisonOp.Eq => " == ",
        ComparisonOp.Ne => " != ",
        _ => " ? ",
    };
}
