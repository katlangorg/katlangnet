namespace KatLang;

/// <summary>
/// Stable machine-readable identity of a front-end <see cref="Diagnostic"/> family:
/// which lexical, parse, elaboration, module-loading, or source-processing condition
/// the diagnostic reports. One code covers one semantic family, not one reporting
/// call site — several distinct messages may deliberately share a code when they
/// describe the same condition, and the human-readable <see cref="Diagnostic.Message"/>
/// remains the presentation channel only, never the classification API.
///
/// <para><b>Stability.</b> Names and numeric values are stable public contract:
/// existing members are never renumbered, renamed, or removed; new families are
/// appended with new values. Hosts may persist the numeric values.</para>
///
/// <para><b>Coverage.</b> Every diagnostic produced by KatLang itself carries a
/// deliberate non-default code. Only externally constructed diagnostics (the
/// positional <see cref="Diagnostic"/> constructor leaves the code unset) use
/// <see cref="Unspecified"/>.</para>
/// </summary>
public enum DiagnosticCode
{
    /// <summary>
    /// No structured identity. This is the default for externally constructed
    /// <see cref="Diagnostic"/> values and the explicit compatibility state for
    /// legacy host-created diagnostics; KatLang-produced diagnostics never use it.
    /// </summary>
    Unspecified = 0,

    // ── Lexical ─────────────────────────────────────────────────────────────

    /// <summary>A character that no KatLang token can begin with.</summary>
    UnexpectedCharacter = 1,

    /// <summary>A string literal is missing its closing quote before the end of the line.</summary>
    UnterminatedStringLiteral = 2,

    /// <summary>A number literal does not fit the finite Decimal128 numeric domain.</summary>
    NumberLiteralTooLarge = 3,

    // ── General syntax ──────────────────────────────────────────────────────

    /// <summary>
    /// A token appears where the grammar requires something else: an expected
    /// closing delimiter or keyword is missing, or a token cannot start or
    /// continue the construct being parsed.
    /// </summary>
    UnexpectedToken = 4,

    /// <summary>
    /// Semicolon used as an expression separator, which KatLang does not support
    /// (use comma or adjacency for separate expressions, parentheses for one
    /// sequence value).
    /// </summary>
    UnsupportedSemicolon = 5,

    /// <summary>
    /// The parser's cumulative weighted recursion budget was exceeded: the source
    /// nests parentheses, brackets, braces, calls, operators, or patterns too
    /// deeply to parse safely (for a loaded module this budget also carries the
    /// module loader's live stack debt).
    /// </summary>
    NestingTooDeep = 6,

    /// <summary>
    /// A single flat operator/postfix chain is too deep for the front end's
    /// recursive visitors to process safely (per-chain limit, distinct from the
    /// cumulative <see cref="NestingTooDeep"/> budget).
    /// </summary>
    ExpressionChainTooDeep = 7,

    // ── Declarations and structure ──────────────────────────────────────────

    /// <summary>The same property name is defined more than once in one algorithm.</summary>
    DuplicateProperty = 8,

    /// <summary>
    /// An algorithm-level declaration (property/clause definition, deconstruction
    /// binding, or <c>open</c>) written inside parentheses; only <c>{ ... }</c>
    /// blocks and the root create declaration scopes.
    /// </summary>
    DeclarationInParentheses = 9,

    /// <summary>
    /// An <c>open</c> declaration used illegally as a declaration: more than one
    /// per algorithm, placed after properties or output, marked <c>public</c>,
    /// or written in expression position.
    /// </summary>
    InvalidOpenDeclaration = 10,

    /// <summary>
    /// The comma-separated <c>open</c> target list is malformed: a missing
    /// same-line first target, a dangling comma, a semicolon separator, or two
    /// targets without a comma between them.
    /// </summary>
    InvalidOpenTargetList = 11,

    /// <summary>
    /// An individual <c>open</c> target is not an open form (for example a
    /// parenthesized capture, a call-like dot-call, a grace-marked target, or
    /// another non-algorithm expression). This is the front-end counterpart of
    /// <see cref="EvalError.BadOpenForm"/> and maps to the same host-facing family.
    /// </summary>
    BadOpenForm = 12,

    /// <summary>Two clauses of one conditional algorithm have match-equivalent patterns.</summary>
    DuplicateBranchPattern = 13,

    /// <summary>Conditional algorithm branches disagree on top-level pattern arity.</summary>
    BranchArityMismatch = 14,

    /// <summary>Conditional algorithm branches disagree on top-level output arity.</summary>
    BranchOutputArityMismatch = 15,

    /// <summary>Clauses of one conditional algorithm mix <c>public</c> and non-public modifiers.</summary>
    ClauseVisibilityMismatch = 16,

    /// <summary>
    /// The grace marker <c>~</c> used where it is not defined: on a property
    /// name, on a compound (non-name) occurrence, on a collecting binding, or
    /// inside clause-head patterns and conditional branch bodies.
    /// </summary>
    InvalidGraceMarker = 17,

    /// <summary>
    /// A malformed star marker in or around a binding position: a detached or
    /// repeated collect marker, a collect marker without a binding name, a
    /// postfix spread marker inside a binding pattern, or a prefix collect
    /// marker in expression position.
    /// </summary>
    InvalidCollectMarker = 18,

    /// <summary>
    /// A collecting binding placed where the language does not allow one:
    /// outside ordinary explicit parameter lists, more than one per pattern
    /// level or deconstruction pattern, or combined with repeated parameter
    /// names.
    /// </summary>
    InvalidCollectingBinding = 19,

    /// <summary>
    /// A spread expression used as a scalar operand (unary/binary operand,
    /// indexing target or selector) instead of a whole expression-list slot.
    /// </summary>
    MisplacedSpread = 20,

    /// <summary>
    /// A parse-time arity gate rejected a call (the <c>if</c> builtin's
    /// three-argument requirement). Runtime arity failures surface as
    /// <see cref="EvalError.ArityMismatch"/> instead.
    /// </summary>
    ArityMismatch = 21,

    /// <summary>An algorithm declares explicit parameters but defines no output.</summary>
    ExplicitParametersRequireOutput = 22,

    /// <summary>
    /// A name required inside a conditional branch or explicitly parameterized
    /// algorithm is not declared by the applicable closed parameter list or
    /// pattern. This includes both a directly written unresolved identifier and
    /// an implicit parameter required to produce a visible callable's value.
    /// </summary>
    UndeclaredIdentifier = 23,

    // ── Structural preflight ────────────────────────────────────────────────

    /// <summary>
    /// The program tree's weighted structural depth exceeds the safe processing
    /// limit (the front-end counterpart of <see cref="EvalError.AstDepthLimitExceeded"/>).
    /// </summary>
    AstDepthLimitExceeded = 24,

    /// <summary>
    /// The program tree contains a reference cycle, so it is not a valid KatLang
    /// program structure (the front-end counterpart of <see cref="EvalError.AstCycleDetected"/>).
    /// </summary>
    AstCycleDetected = 25,

    // ── Source-processing limits ────────────────────────────────────────────

    /// <summary>One source text (program or loaded module) exceeds the per-source length limit.</summary>
    SourceLengthExceeded = 26,

    /// <summary>The cumulative source length across the program and its modules exceeds the aggregate limit.</summary>
    AggregateSourceLengthExceeded = 27,

    /// <summary>A module import chain exceeds the nested module-import depth limit.</summary>
    ModuleImportDepthExceeded = 28,

    /// <summary>Loading another distinct module would exceed the module-count limit.</summary>
    ModuleCountExceeded = 29,

    /// <summary>
    /// Module content at this load position would nest deeper than the
    /// cumulative structural budget across the module chain allows.
    /// </summary>
    ModuleNestingTooDeep = 30,

    /// <summary>
    /// Module elaboration stopped because the host thread's remaining stack
    /// cannot safely walk the composition, although it is within the structural
    /// depth limit.
    /// </summary>
    ModuleElaborationStackExhausted = 31,

    // ── Module loading ──────────────────────────────────────────────────────

    /// <summary>
    /// A <c>load</c> directive is malformed or misplaced: used in a runtime
    /// expression, not given exactly one argument, or given a non-literal URL.
    /// </summary>
    InvalidLoadDirective = 32,

    /// <summary>
    /// A <c>load</c> URL is rejected by URL validation policy: not a valid
    /// absolute URL, not HTTPS, or not on the configured domain allowlist.
    /// </summary>
    InvalidLoadUrl = 33,

    /// <summary>A module load cycle was detected: a module (transitively) loads itself.</summary>
    LoadCycle = 34,

    /// <summary>Fetching a module's source failed or returned no source text.</summary>
    LoadFetchFailed = 35,

    /// <summary>
    /// Downloaded module content is not valid KatLang source (for example the
    /// URL returned an HTML page).
    /// </summary>
    InvalidLoadedSource = 36,

    /// <summary>
    /// The program uses <c>load</c>, but module elaboration is unavailable in
    /// the current parser/run configuration (no downloader/module loader).
    /// </summary>
    LoadElaborationUnavailable = 37,

    /// <summary>
    /// An internal front-end invariant was violated (for example module
    /// elaboration left an unresolved load directive in the AST). Indicates a
    /// KatLang defect, not a problem with the source program.
    /// </summary>
    InternalError = 38,
}
