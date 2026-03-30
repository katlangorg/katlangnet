namespace KatLang;

/// <summary>
/// Recursive-descent parser with precedence climbing for KatLang 0.7.
/// Produces a raw AST where all identifiers are <see cref="Expr.Resolve"/> nodes.
/// Use <see cref="ParameterDetector"/> afterwards to classify parameters.
/// </summary>
public sealed class Parser
{
    private readonly IReadOnlyList<Token> _tokens;
    private readonly List<Diagnostic> _diagnostics;
    private int _pos;

    private Parser(IReadOnlyList<Token> tokens, List<Diagnostic> diagnostics)
    {
        _tokens = tokens;
        _diagnostics = diagnostics;
    }

    // ── Entry points ─────────────────────────────────────────────────────────

    internal static ParseResult ParseSyntax(string source)
    {
        var (tokens, lexDiags) = Lexer.Tokenize(source);
        var diagnostics = new List<Diagnostic>(lexDiags);
        var parser = new Parser(tokens, diagnostics);
        var root = parser.ParseAlgorithm(isParametrized: true);
        if (parser.Current.Kind != TokenKind.EndOfFile)
        {
            parser.ReportError($"Expected end of input, got '{parser.Current.Kind}'.");
        }
        return new ParseResult(root, diagnostics);
    }

    /// <summary>
    /// Full pipeline: parse, elaborate loads, detect parameters, and resolve implicit arguments.
    /// Returns the final processed AST along with any diagnostics.
    /// </summary>
    public static ParseResult Parse(string source)
    {
        var result = ParseSyntax(source);
        var detected = ParameterDetector.Detect(result.Root);
        var resolved = ImplicitArgumentResolver.Resolve(detected);
        return result with { Root = resolved };
    }

    /// <summary>
    /// Full pipeline with load elaboration: parse, elaborate load directives,
    /// detect parameters, and resolve implicit arguments.
    /// </summary>
    /// <param name="source">KatLang source code.</param>
    /// <param name="downloadCode">
    /// Injected code fetcher: URL → source text. In WASM, pass a JS interop downloader.
    /// If null, a default HttpClient-based fetcher is used.
    /// </param>
    /// <param name="allowedHosts">
    /// Optional set of allowed hostnames for load directives. Defaults to katlang.org only.
    /// </param>
    public static ParseResult Parse(
        string source,
        Func<string, string>? downloadCode,
        IEnumerable<string>? allowedHosts = null)
    {
        var result = ParseSyntax(source);
        var diagnostics = new List<Diagnostic>(result.Diagnostics);

        // load elaboration: resolve load("url") directives before parameter detection
        var loader = new ModuleLoader(diagnostics, downloadCode, allowedHosts);
        var elaborated = loader.Elaborate(result.Root);

        var detected = ParameterDetector.Detect(elaborated);
        var resolved = ImplicitArgumentResolver.Resolve(detected);
        return new ParseResult(resolved, diagnostics);
    }

    // ── Token access helpers ────────────────────────────────────────────────

    // Comment tokens are kept in the stream for consumers such as colorizers.
    // The parser skips them transparently so grammar rules never see them.

    private Token Current
    {
        get
        {
            while (_pos < _tokens.Count - 1 && _tokens[_pos].Kind == TokenKind.Comment)
                _pos++;
            return _tokens[_pos];
        }
    }

    private Token Advance()
    {
        var token = Current; // normalises _pos past any leading comments
        if (_pos < _tokens.Count - 1) _pos++;
        // skip any comment tokens so the next Current call lands on a real token
        while (_pos < _tokens.Count - 1 && _tokens[_pos].Kind == TokenKind.Comment)
            _pos++;
        return token;
    }

    private Token Expect(TokenKind kind)
    {
        if (Current.Kind == kind)
            return Advance();

        ReportError($"Expected '{kind}', got '{Current.Kind}'.");
        return Token.Bad(Current.Position, 0, Current.Line, Current.Column);
    }

    private void ReportError(string message)
    {
        _diagnostics.Add(new Diagnostic(
            message,
            DiagnosticSeverity.Error,
            new SourceSpan(
                Current.Line,
                Current.Column,
                Current.Line,
                Current.Column + Math.Max(Current.Length, 1) - 1)));
    }

    private Token Previous
    {
        get
        {
            var idx = Math.Max(0, _pos - 1);
            while (idx > 0 && _tokens[idx].Kind == TokenKind.Comment)
                idx--;
            return _tokens[idx];
        }
    }

    private SourceSpan MakeSpan(Token start) => new(
        start.Line, start.Column,
        Previous.Line, Previous.Column + Math.Max(Previous.Length, 1) - 1);

    private static SourceSpan TokenSpan(Token t) => new(
        t.Line, t.Column, t.Line, t.Column + Math.Max(t.Length, 1) - 1);

    private SourceSpan SpanFrom(Expr start) => new(
        start.Span?.StartLineNumber ?? Previous.Line,
        start.Span?.StartColumn ?? Previous.Column,
        Previous.Line,
        Previous.Column + Math.Max(Previous.Length, 1) - 1);

    // ── Algorithm parsing ───────────────────────────────────────────────────
    // Corresponds to 0.6's ReadSecondOrderAlgorithm.
    // Reads property definitions (Name = ...) and output expression lines.
    // Explicit output syntax: `Output = expr` is special output-definition syntax,
    // NOT a property assignment. It lowers to the algorithm's Output list.

    private Algorithm ParseAlgorithm(bool isParametrized)
    {
        var opens = new List<Expr>();
        var hasOpenDeclaration = false;
        var properties = new List<Property>();
        var output = new List<Expr>();
        var hasExplicitOutput = false;
        var hasImplicitOutput = false;

        while (Current.Kind != TokenKind.EndOfFile
            && Current.Kind != TokenKind.RParen
            && Current.Kind != TokenKind.RBrace)
        {
            // Skip bad tokens for error recovery
            if (Current.Kind == TokenKind.Bad)
            {
                Advance();
                continue;
            }

            // Check for invalid grace on property name: ~Name = ... or ~public Name = ...
            if (Current.Kind == TokenKind.Tilde && LookaheadThroughTildesToPropertyDef())
            {
                ReportError("Grace operator cannot be applied to property names.");
                while (Current.Kind == TokenKind.Tilde) Advance();
                // Fall through to normal property definition handling
            }

            // Open declaration: open target1, target2, ...
            if (Current.Kind == TokenKind.KeywordOpen)
            {
                if (hasOpenDeclaration)
                {
                    ReportError("Only one 'open' declaration is allowed per algorithm.");
                }
                if (properties.Count > 0 || output.Count > 0)
                {
                    ReportError("'open' declaration must appear before any properties or output expressions.");
                }
                hasOpenDeclaration = true;
                Advance(); // consume 'open'
                var openExprs = ParseOpenTargetList();
                NormalizeAndValidateOpenForms(openExprs);
                opens.AddRange(openExprs);
            }
            // public open ... → reject
            else if (Current.Kind == TokenKind.KeywordPublic && LookaheadIsPublicOpen())
            {
                ReportError("'public' cannot be applied to open declarations.");
                Advance(); // consume 'public'
                // Fall through: next iteration will parse the open declaration normally
            }
            // public Output = ... → reject (output cannot be public)
            else if (Current.Kind == TokenKind.KeywordPublic && LookaheadIsPublicOutputDef())
            {
                ReportError("'public' cannot be applied to output definitions. Use 'Output = expr' without 'public'.");
                Advance(); // consume 'public'
                // Fall through: next iteration will parse as explicit output
            }
            // Check for public property definition: public Name = ...
            else if (Current.Kind == TokenKind.KeywordPublic && LookaheadIsPublicPropertyDef())
            {
                Advance(); // consume 'public'
                var name = Current.StringValue!;

                Advance(); // consume identifier
                Advance(); // consume '='
                var body = ParseOutputLine();
                properties.Add(new Property(name, body, IsPublic: true));
            }
            // Explicit output definition: Output = expr
            else if (Current.Kind == TokenKind.Identifier && Current.StringValue == "Output" && LookaheadIsEquals())
            {
                if (hasExplicitOutput)
                {
                    ReportError("Algorithm output may be defined only once.");
                }
                if (hasImplicitOutput)
                {
                    ReportError("Cannot use both explicit 'Output = ...' and implicit trailing output in the same algorithm.");
                }

                hasExplicitOutput = true;
                Advance(); // consume 'Output'
                Advance(); // consume '='
                var exprs = ParseOutputLineExprs();
                output.AddRange(exprs);
            }
            // Check for property definition: Identifier '='
            else if (Current.Kind == TokenKind.Identifier && LookaheadIsEquals())
            {
                var name = Current.StringValue!;

                Advance(); // consume identifier
                Advance(); // consume '='
                var body = ParseOutputLine();
                properties.Add(new Property(name, body));
            }
            else
            {
                // Implicit output expression line
                if (hasExplicitOutput)
                {
                    ReportError("Cannot use both explicit 'Output = ...' and implicit trailing output in the same algorithm.");
                }
                hasImplicitOutput = true;
                var exprs = ParseOutputLineExprs();
                output.AddRange(exprs);
            }
        }

        return new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: opens,
            Properties: properties,
            Output: output)
        {
            IsParametrized = isParametrized
        };
    }

    /// <summary>
    /// Parses the comma-separated target list after the <c>open</c> keyword.
    /// Each target is a combine item (expression with optional semicolons).
    /// String literal targets are desugared to <c>load('url')</c> calls.
    /// </summary>
    private List<Expr> ParseOpenTargetList()
    {
        var targets = new List<Expr>();
        targets.Add(ParseOpenTarget());

        while (Current.Kind == TokenKind.Comma)
        {
            Advance(); // consume ','
            targets.Add(ParseOpenTarget());
        }

        return targets;
    }

    /// <summary>
    /// Parses a single open target (which may include semicolons for combine).
    /// If the target is a string literal, desugars it to <c>load('url')</c>.
    /// </summary>
    private Expr ParseOpenTarget()
    {
        // String literal sugar: open 'url' → open load('url')
        if (Current.Kind == TokenKind.StringLiteral)
        {
            var token = Advance();
            var url = token.StringValue ?? "";
            var urlExpr = new Expr.StringLiteral(url) { Span = TokenSpan(token) };
            var loadArgs = new Algorithm.User(
                Parent: null, Params: [], Opens: [],
                Properties: [], Output: [urlExpr])
            { IsParametrized = false };
            var loadResolve = new Expr.Resolve("load") { Span = TokenSpan(token) };
            return new Expr.Call(loadResolve, loadArgs) { Span = TokenSpan(token) };
        }

        return ParseCombineItem();
    }

    /// <summary>
    /// Checks if the token after the current identifier is '='.
    /// Used to distinguish property definitions from output expressions.
    /// </summary>
    private bool LookaheadIsEquals()
    {
        var next = _pos + 1;
        return next < _tokens.Count && _tokens[next].Kind == TokenKind.Equals;
    }

    /// <summary>
    /// Checks if the current tilde sequence is followed by Identifier '=' or 'public Identifier ='.
    /// Used to detect invalid grace on property definitions.
    /// </summary>
    private bool LookaheadThroughTildesToPropertyDef()
    {
        var next = _pos;
        while (next < _tokens.Count && _tokens[next].Kind == TokenKind.Tilde)
            next++;
        // ~Name = ...
        if (next + 1 < _tokens.Count
            && _tokens[next].Kind == TokenKind.Identifier
            && _tokens[next + 1].Kind == TokenKind.Equals)
            return true;
        // ~public Name = ...
        if (next + 2 < _tokens.Count
            && _tokens[next].Kind == TokenKind.KeywordPublic
            && _tokens[next + 1].Kind == TokenKind.Identifier
            && _tokens[next + 2].Kind == TokenKind.Equals)
            return true;
        return false;
    }

    /// <summary>
    /// Checks if 'public' keyword is followed by 'open' keyword.
    /// Used to detect and reject public open declarations.
    /// </summary>
    private bool LookaheadIsPublicOpen()
    {
        var next = _pos + 1; // skip 'public'
        return next < _tokens.Count && _tokens[next].Kind == TokenKind.KeywordOpen;
    }

    /// <summary>
    /// Checks if 'public' keyword is followed by 'Output' '='.
    /// Used to detect and reject public output definitions.
    /// </summary>
    private bool LookaheadIsPublicOutputDef()
    {
        var next = _pos + 1; // skip 'public'
        return next + 1 < _tokens.Count
            && _tokens[next].Kind == TokenKind.Identifier
            && _tokens[next].StringValue == "Output"
            && _tokens[next + 1].Kind == TokenKind.Equals;
    }

    /// <summary>
    /// Checks if 'public' keyword is followed by Identifier '='.
    /// Used to detect public property definitions.
    /// </summary>
    private bool LookaheadIsPublicPropertyDef()
    {
        var next = _pos + 1; // skip 'public'
        return next + 1 < _tokens.Count
            && _tokens[next].Kind == TokenKind.Identifier
            && _tokens[next + 1].Kind == TokenKind.Equals;
    }

    // ── Output line parsing ─────────────────────────────────────────────────
    // Corresponds to 0.6's ReadFirstOrderAlgorithm.
    // Reads comma-separated expressions (with semicolons for combine).

    /// <summary>
    /// Parses a property body as an algorithm: the comma-separated expressions
    /// become the algorithm's output list.
    /// If the body is a single block expression, return its algorithm directly
    /// (enables nested property access like X.Y where X = (Y = ...)).
    /// </summary>
    private Algorithm ParseOutputLine()
    {
        var exprs = ParseOutputLineExprs();

        // Unwrap single Block to allow nested property access
        if (exprs.Count == 1 && exprs[0] is Expr.Block(var innerAlg))
            return innerAlg with { IsParametrized = true };

        return new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: [],
            Properties: [],
            Output: exprs)
        {
            IsParametrized = true
        };
    }

    /// <summary>
    /// Normalizes and validates open expressions.
    /// DotCall(obj, name, null) is the canonical form for dotted paths in opens.
    /// Rejects DotCall with args as invalid.
    /// Lean: Expr.openForm? — only Resolve, DotCall(none), Combine, Block are open forms.
    /// </summary>
    private void NormalizeAndValidateOpenForms(List<Expr> exprs)
    {
        for (var i = 0; i < exprs.Count; i++)
            exprs[i] = NormalizeOpenExpr(exprs[i]);

        foreach (var expr in exprs)
        {
            if (!IsOpenForm(expr))
            {
                var kind = OpenExprKind(expr);
                ReportError($"Invalid open form: '{kind}' is not allowed in open declarations.");
            }
        }
    }

    /// <summary>
    /// Recursively normalizes an open expression:
    /// - DotCall(obj, name, null) is the canonical no-arg form (kept as-is)
    /// - DotCall(obj, name, args) → report error (call-like syntax not allowed in opens)
    /// - Recurse through Combine, DotCall target, Block.
    /// </summary>
    private Expr NormalizeOpenExpr(Expr expr)
    {
        switch (expr)
        {
            case Expr.DotCall(var target, var name, null):
                return new Expr.DotCall(NormalizeOpenExpr(target), name) { Span = expr.Span };

            case Expr.DotCall(var target, var name, _):
                ReportError($"Invalid open form: call-like dotCall '.{name}(...)' is not allowed in open declarations.");
                // Return as-is; validation will also flag it
                return expr;

            case Expr.Combine(var left, var right):
                return new Expr.Combine(NormalizeOpenExpr(left), NormalizeOpenExpr(right)) { Span = expr.Span };

            case Expr.Block(var alg):
                // Block in open position: normalize opens within the block's own opens
                return expr;

            default:
                return expr;
        }
    }

    /// <summary>
    /// Predicate for valid open forms at parse time.
    /// Lean: Expr.openForm? — only Resolve, DotCall(none), Combine, Block post-elaboration.
    /// DotCall with args is NOT a valid open form.
    /// load calls (Call(Resolve("load"), _)) are allowed as *surface* open forms because
    /// the load elaboration pass will rewrite them to Block nodes before open resolution.
    /// After elaboration, no load calls or StringLiteral nodes remain —
    /// see Lean postElabInvariant (rejects both structurally).
    /// load is NOT a core Expr constructor; it is surface syntax only.
    /// </summary>
    private static bool IsOpenForm(Expr e) => e is
        Expr.Resolve or Expr.DotCall(_, _, null) or Expr.Combine or Expr.Block
        || e is Expr.Call(Expr.Resolve("load"), _);

    /// <summary>
    /// Human-readable kind string for open-form validation errors.
    /// </summary>
    private static string OpenExprKind(Expr e) => e switch
    {
        Expr.Num => "num",
        Expr.StringLiteral => "stringLiteral",
        Expr.Param => "param",
        Expr.Unary => "unary",
        Expr.Binary => "binary",
        Expr.Index => "index",
        Expr.Call => "call",
        Expr.DotCall => "dotCall",
        Expr.Grace => "grace",
        Expr.NativeCall => "nativeCall",
        _ => "unknown",
    };

    /// <summary>
    /// Parses comma-separated expressions for an output line.
    /// Semicolons create <see cref="Expr.Combine"/> nodes.
    /// Returns the list of expressions (each comma-separated item is one entry).
    /// </summary>
    private List<Expr> ParseOutputLineExprs()
    {
        var exprs = new List<Expr>();
        exprs.Add(ParseCombineItem());

        while (Current.Kind == TokenKind.Comma)
        {
            Advance(); // consume ','
            exprs.Add(ParseCombineItem());
        }

        return exprs;
    }

    /// <summary>
    /// Parses a single item that may contain semicolons for combine.
    /// <c>expr ; expr</c> → <see cref="Expr.Combine"/>.
    /// </summary>
    private Expr ParseCombineItem()
    {
        var left = ParseExpression();

        while (Current.Kind == TokenKind.Semicolon)
        {
            Advance(); // consume ';'
            var right = ParseExpression();
            left = new Expr.Combine(left, right) { Span = SpanFrom(left) };
        }

        return left;
    }

    // ── Expression parsing (precedence climbing) ────────────────────────────
    //
    // Precedence levels:
    //   1: or            (logical or, left-associative)
    //   2: xor           (logical xor, left-associative)
    //   3: and           (logical and, left-associative)
    //   4: == !=         (equality, left-associative)
    //   5: < > <= >=     (comparison, left-associative)
    //   6: + -           (additive, left-associative)
    //   7: * / div mod   (multiplicative, left-associative)
    //   8: ^             (power, right-associative)
    //   9: - not         (unary prefix)
    //  10: . : call      (postfix)

    private Expr ParseExpression(int minPrecedence = 0)
    {
        var lhs = minPrecedence <= 9 ? ParseUnary() : ParsePostfix();

        while (true)
        {
            var (prec, op) = GetBinaryOpInfo(Current.Kind);
            if (prec < minPrecedence) break;

            Advance(); // consume operator token

            // Right-associative: ^ uses prec (not prec+1) so 2^3^4 = 2^(3^4)
            var nextMin = op is BinaryOp.Pow ? prec : prec + 1;
            var rhs = ParseExpression(nextMin);
            lhs = new Expr.Binary(op, lhs, rhs) { Span = SpanFrom(lhs) };
        }

        return lhs;
    }

    private static (int Precedence, BinaryOp Op) GetBinaryOpInfo(TokenKind kind) => kind switch
    {
        TokenKind.KeywordOr => (1, BinaryOp.Or),
        TokenKind.KeywordXor => (2, BinaryOp.Xor),
        TokenKind.KeywordAnd => (3, BinaryOp.And),
        TokenKind.EqualEqual => (4, BinaryOp.Eq),
        TokenKind.BangEqual => (4, BinaryOp.Ne),
        TokenKind.LessThan => (5, BinaryOp.Lt),
        TokenKind.GreaterThan => (5, BinaryOp.Gt),
        TokenKind.LessEqual => (5, BinaryOp.Le),
        TokenKind.GreaterEqual => (5, BinaryOp.Ge),
        TokenKind.Plus => (6, BinaryOp.Add),
        TokenKind.Minus => (6, BinaryOp.Sub),
        TokenKind.Star => (7, BinaryOp.Mul),
        TokenKind.Slash => (7, BinaryOp.Div),
        TokenKind.KeywordDiv => (7, BinaryOp.IDiv),
        TokenKind.KeywordMod => (7, BinaryOp.Mod),
        TokenKind.Caret => (8, BinaryOp.Pow),
        _ => (-1, default),
    };

    // ── Unary ───────────────────────────────────────────────────────────────

    private Expr ParseUnary()
    {
        if (Current.Kind == TokenKind.Minus)
        {
            var start = Advance(); // consume '-'
            var operand = ParseUnary();
            return new Expr.Unary(UnaryOp.Minus, operand) { Span = MakeSpan(start) };
        }
        if (Current.Kind is TokenKind.KeywordNot)
        {
            var start = Advance(); // consume 'not'
            var operand = ParseUnary();
            return new Expr.Unary(UnaryOp.Not, operand) { Span = MakeSpan(start) };
        }
        return ParsePostfix();
    }

    // ── Postfix (dot, colon, call) ──────────────────────────────────────────

    private Expr ParsePostfix()
    {
        var lhs = ParsePrimary();

        while (true)
        {
            switch (Current.Kind)
            {
                case TokenKind.Colon:
                    // Index: expr : selector
                    Advance(); // consume ':'
                    var selector = ParsePrimary();
                    lhs = new Expr.Index(lhs, selector) { Span = SpanFrom(lhs) };
                    break;

                case TokenKind.Dot:
                    // Dot-call syntax: expr.Name or expr.Name(args)
                    Advance(); // consume '.'
                    if (Current.Kind != TokenKind.Identifier)
                    {
                        ReportError("Expected property name after '.'.");
                        break;
                    }
                    var propName = Current.StringValue!;
                    Advance(); // consume identifier

                    if (Current.Kind is TokenKind.LParen or TokenKind.LBrace)
                    {
                        // expr.Name(args) → DotCall(expr, Name, args)
                        // Lean: dotCall : Expr → Ident → Option Algorithm → Expr
                        var args = ParseCallArgs();
                        lhs = new Expr.DotCall(lhs, propName, args) { Span = SpanFrom(lhs) };
                    }
                    else
                    {
                        // expr.Name → DotCall(expr, Name, null)
                        lhs = new Expr.DotCall(lhs, propName) { Span = SpanFrom(lhs) };
                    }
                    break;

                case TokenKind.LParen or TokenKind.LBrace when lhs is Expr.Resolve or Expr.DotCall:
                    // Direct call: Name(args) or expr.Name(args) already handled above
                    // This handles: Name(args) → Call(Resolve(Name), args)
                    var callArgs = ParseCallArgs();
                    // Direct-call lowering for while/repeat: package multi-item init
                    // into a block so that while(step, s1, s2) → while(step, block([s1,s2]))
                    // and repeat(step, n, s1, s2) → repeat(step, n, block([s1,s2])).
                    // This is safe to do in the parser for lexical calls because the callee
                    // is a known name; dotCall lowering must wait until the evaluator confirms
                    // no structural property shadows the name.
                    callArgs = MaybeLowerBuiltinInitArgs(lhs, callArgs);
                    // Validate if arity (2 or 3 args).
                    ValidateIfArity(lhs, callArgs);
                    lhs = new Expr.Call(lhs, callArgs) { Span = SpanFrom(lhs) };
                    break;

                default:
                    return lhs;
            }
        }
    }

    /// <summary>
    /// Parses call arguments: <c>(algorithm)</c> or <c>{algorithm}</c>.
    /// Ordinary parentheses always mean ordinary grouping — <c>((expr))</c> is
    /// just nested grouping, never special block construction.
    /// </summary>
    private Algorithm ParseCallArgs()
    {
        if (Current.Kind == TokenKind.LParen)
        {
            Advance(); // consume '('
            var alg = ParseAlgorithm(isParametrized: false);
            Expect(TokenKind.RParen);
            return alg;
        }
        else
        {
            // Trailing brace-block: Algo{e} → Algo({e})
            // The brace content is a parametrized algorithm that becomes a single
            // Expr.Block argument inside a non-parametrized wrapper, so the block
            // is resolvable as an algorithm by ResolveAlg(.block ...).
            var start = Current;
            Advance(); // consume '{'
            var innerAlg = ParseAlgorithm(isParametrized: true);
            Expect(TokenKind.RBrace);
            var blockExpr = new Expr.Block(innerAlg) { Span = MakeSpan(start) };
            return new Algorithm.User(
                Parent: null, Params: [], Opens: [],
                Properties: [], Output: [blockExpr]);
        }
    }

    // ── Primary expressions ─────────────────────────────────────────────────

    private Expr ParsePrimary()
    {
        switch (Current.Kind)
        {
            case TokenKind.Number:
            {
                var token = Advance();
                return new Expr.Num(token.NumValue) { Span = TokenSpan(token) };
            }

            case TokenKind.StringLiteral:
            {
                var token = Advance();
                return new Expr.StringLiteral(token.StringValue ?? "") { Span = TokenSpan(token) };
            }

            case TokenKind.Identifier:
            {
                var token = Advance();
                if (Current.Kind == TokenKind.Tilde)
                {
                    var weight = 0;
                    while (Current.Kind == TokenKind.Tilde)
                    {
                        Advance();
                        weight++;
                    }
                    return new Expr.Grace(
                        new Expr.Resolve(token.StringValue!) { Span = TokenSpan(token) },
                        weight) { Span = MakeSpan(token) };
                }
                return new Expr.Resolve(token.StringValue!) { Span = TokenSpan(token) };
            }

            case TokenKind.Tilde:
            {
                // Prefix grace: each ~ decrements weight
                var startToken = Current;
                var weight = 0;
                while (Current.Kind == TokenKind.Tilde)
                {
                    Advance();
                    weight--;
                }
                if (Current.Kind != TokenKind.Identifier)
                {
                    ReportError("Expected identifier after '~'.");
                    Advance(); // skip for recovery
                    return new Expr.Num(0) { Span = MakeSpan(startToken) };
                }
                var graceToken = Advance();
                // Postfix grace: each ~ after identifier increments weight
                while (Current.Kind == TokenKind.Tilde)
                {
                    Advance();
                    weight++;
                }
                var resolve = new Expr.Resolve(graceToken.StringValue!) { Span = TokenSpan(graceToken) };
                return weight == 0 ? resolve : new Expr.Grace(resolve, weight) { Span = MakeSpan(startToken) };
            }

            case TokenKind.LParen:
            {
                var start = Current;
                Advance(); // consume '('
                var alg = ParseAlgorithm(isParametrized: false);
                Expect(TokenKind.RParen);

                // Unwrap single expression without properties (grouping parens)
                if (alg.Properties.Count == 0 && alg.Output.Count == 1)
                    return alg.Output[0];

                return new Expr.Block(alg) { Span = MakeSpan(start) };
            }

            case TokenKind.LBrace:
            {
                var start = Current;
                Advance(); // consume '{'
                var alg = ParseAlgorithm(isParametrized: true);
                Expect(TokenKind.RBrace);
                return new Expr.Block(alg) { Span = MakeSpan(start) };
            }

            case TokenKind.KeywordOpen:
            {
                var token = Current;
                ReportError("'open' is a declaration and cannot be used in expression position.");
                Advance(); // skip for recovery
                return new Expr.Num(0) { Span = TokenSpan(token) }; // error placeholder
            }

            default:
            {
                var token = Current;
                ReportError($"Unexpected token: '{Current.Kind}'.");
                Advance(); // skip for recovery
                return new Expr.Num(0) { Span = TokenSpan(token) }; // error placeholder
            }
        }
    }

    // ── Direct-call lowering for while/repeat ─────────────────────────────
    // When the parser sees a lexical call to "while" or "repeat" with more args
    // than the builtin arity, it packages the trailing init-state arguments into
    // a single Expr.Block argument. This allows:
    //   while(Step, x, 0)       → while(Step, block([x, 0]))
    //   repeat(Step, n, x, 0)   → repeat(Step, n, block([x, 0]))
    // This rewriting is safe here because the callee is a known resolve name.
    // For dotCall (e.g. Step.while(x, 0)) the packaging must happen later in
    // the evaluator, after structural property lookup confirms no shadowing.

    /// <summary>
    /// Creates a zero-parameter block algorithm wrapping the given expressions.
    /// Used to package multi-item init state for while/repeat lowering.
    /// </summary>
    private static Expr.Block MakeInitBlock(IReadOnlyList<Expr> exprs) =>
        new(new Algorithm.User(
            Parent: null, Params: [], Opens: [],
            Properties: [], Output: exprs));

    /// <summary>
    /// If <paramref name="callee"/> is <c>resolve("while")</c> or <c>resolve("repeat")</c>
    /// and <paramref name="args"/> has more outputs than the builtin arity, rewrite the
    /// trailing init-state outputs into a single <see cref="Expr.Block"/> argument.
    /// Otherwise returns <paramref name="args"/> unchanged.
    /// </summary>
    private static Algorithm MaybeLowerBuiltinInitArgs(Expr callee, Algorithm args)
    {
        if (callee is not Expr.Resolve(var name)) return args;
        var count = args.Output.Count;

        if (name == "while" && count >= 3)
        {
            // while(step, s1, s2, ..., sk) → while(step, block([s1..sk]))
            var initExprs = args.Output.Skip(1).ToList();
            var newOutput = new List<Expr> { args.Output[0], MakeInitBlock(initExprs) };
            return args with { Output = newOutput };
        }

        if (name == "repeat" && count >= 4)
        {
            // repeat(step, count, s1, s2, ..., sk) → repeat(step, count, block([s1..sk]))
            var initExprs = args.Output.Skip(2).ToList();
            var newOutput = new List<Expr> { args.Output[0], args.Output[1], MakeInitBlock(initExprs) };
            return args with { Output = newOutput };
        }

        return args;
    }

    /// <summary>
    /// Validates that <c>if(...)</c> has exactly 2 or 3 arguments.
    /// For non-<c>if</c> callees, does nothing.
    /// </summary>
    private void ValidateIfArity(Expr callee, Algorithm args)
    {
        if (callee is Expr.Resolve("if"))
        {
            var argCount = args.Output.Count;
            if (argCount != 2 && argCount != 3)
            {
                ReportError($"'if' requires 2 or 3 arguments, got {argCount}.");
            }
        }
    }

    // ── Tuple desugaring ────────────────────────────────────────────────────
    // Converts surface-level Tuple nodes into Lean-core Block(Algorithm(params:[],...)).
    // Must run AFTER ParameterDetector and ImplicitArgumentResolver.

}
