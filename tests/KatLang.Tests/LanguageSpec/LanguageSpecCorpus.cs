namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// The canonical executable language-specification corpus.
///
/// Every case pins hand-written canonical expectations for observable KatLang
/// semantics (see <see cref="SpecCase"/>). Four layers consume it:
/// the C# runner (<c>LanguageSpecRunnerTests</c>) executes every case through
/// the production front end and evaluator; the generated Lean artifact
/// (<c>lean/LanguageSpecCases.lean</c>) pins the same canonical neutral
/// observations as <c>#guard</c>s over the Lean model for the
/// Lean-representable partition; tutorial examples reference cases by stable
/// ID via <c>&lt;!-- spec:id --&gt;</c> markers (<c>TutorialSpecTests</c>); and
/// the katlang-generator prompt files embed a generated verified-examples
/// block (<c>GeneratorSpecTests</c>).
///
/// This corpus is complementary to <see cref="SemanticExplorerCorpus"/>: the
/// explorer is a generated cross-product that re-pins observed behavior for
/// bounded differential validation, while this corpus is the human-governed
/// canonical layer — changing an expectation here is always a reviewed edit.
/// </summary>
public static class LanguageSpecCorpus
{
    /// <summary>Allowed case categories (schema-validated).</summary>
    public static readonly IReadOnlyList<string> Categories =
    [
        "arithmetic",
        "empty-and-singleton",
        "item-supply-vs-value",
        "empty-visible-vs-spread",
        "deconstruction",
        "variadic-calls",
        "sequence-construction",
        "access-boundaries",
        "collection-builtins",
        "equality-and-indexing",
        "parser-layout",
        "errors",
        "strings",
    ];

    // ----- Lean program text helpers (same encoding as SemanticExplorerCorpus:
    // parenthesized lists are zero-parameter blocks, `()` is the empty-sequence
    // node; the parser never produces .sequenceConstruct) -------------------

    private static string LProg(IEnumerable<string> props, IEnumerable<string> outputs)
        => $".block (alg [] [] [{string.Join(", ", props)}] [{string.Join(", ", outputs)}])";

    private static string LProp(string name, params string[] outputs)
        => $"privateProp \"{name}\" (alg [] [] [] [{string.Join(", ", outputs)}])";

    private static string LFn(string name, string[] parameters, params string[] outputs)
        => $"privateProp \"{name}\" (alg [{string.Join(", ", parameters.Select(p => $"\"{p}\""))}] [] [] [{string.Join(", ", outputs)}])";

    private static string LFnP(string name, string[] parameterSpecs, params string[] outputs)
        => $"privateProp \"{name}\" (algWithParameters [{string.Join(", ", parameterSpecs)}] [] [] [{string.Join(", ", outputs)}])";

    private static string LFnPat(string name, string[] patterns, params string[] outputs)
        => $"privateProp \"{name}\" (algWithParameterPatterns [{string.Join(", ", patterns)}] [] [] [{string.Join(", ", outputs)}])";

    private static string LCall(string callee, params string[] args)
        => $".call (.resolve \"{callee}\") (alg [] [] [] [{string.Join(", ", args)}])";

    private static string LBlock(params string[] outputs)
        => $"(.block (alg [] [] [] [{string.Join(", ", outputs)}]))";

    private static string LNums(params int[] ns) => string.Join(", ", ns.Select(n => $".num {n}"));

    private const string LEmpty = "(.emptySequence 0)";

    private static string LVar(string name) => $"{{ name := \"{name}\", kind := .variadic }}";

    private static string LFix(string name) => $"{{ name := \"{name}\" }}";

    /// <summary>
    /// Parser-elaborated assignment deconstruction (same encoding as
    /// SemanticExplorerCorpus.LDecon): the RHS is evaluated once into a shared
    /// property and each observed target binds through an inline
    /// sequence-value parameter pattern that opens that shared value.
    /// </summary>
    private static string LDecon(string sharedProp, string[] rhsOutputs, string[] targets, int variadicIndex, string observed)
    {
        var captures = targets.Select((t, i) => i == variadicIndex
            ? $".capture {{ name := \"{t}\", kind := .variadic }}"
            : $".capture {{ name := \"{t}\" }}");
        var pattern = $".sequenceValue [{string.Join(", ", captures)}]";
        var helper = $".block (algWithParameterPatterns [{pattern}] [] [] [.param \"{observed}\"])";
        return $"privateProp \"{observed}\" (alg [] [] [] [.call ({helper}) (alg [] [] [] [.resolve \"{sharedProp}\"])])";
    }

    private const string PairOfPairs =
        "(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))";

    // ----- The corpus -------------------------------------------------------

    public static IReadOnlyList<SpecCase> AllCases() =>
    [
        // ==================== arithmetic ====================
        new()
        {
            Id = "first-program",
            Category = "arithmetic",
            Source = "2 + 3 * 4",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "14",
            ExpectedRaw = "14",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [".binary .add (.num 2) (.binary .mul (.num 3) (.num 4))"]),
            Explanation = "Multiplication binds tighter than addition; a bare expression is the program's output.",
        },
        new()
        {
            Id = "property-access-and-call",
            Category = "arithmetic",
            Source = "// Define a property:\nAnswer = 42\n\n// Property-style access:\nAnswer\n\n// Explicit zero-parameter call:\nAnswer()",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "42\n42",
            ExpectedRaw = "S[42, 42]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("Answer", ".num 42")],
                [".resolve \"Answer\"", ".call (.resolve \"Answer\") (alg [] [] [] [])"]),
            Explanation = "Property-style access `Answer` and the explicit call `Answer()` observe the same value; the call shape only controls the zero-argument cache.",
        },

        // ==================== empty-and-singleton ====================
        new()
        {
            Id = "empty-literal",
            Category = "empty-and-singleton",
            Source = "()",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()",
            ExpectedRaw = "S[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LEmpty]),
            IncludeInGeneratorPrompt = true,
            Explanation = "`()` is the empty sequence value — a real value occupying one visible output slot that contains zero items.",
        },
        new()
        {
            Id = "empty-wrapped",
            Category = "empty-and-singleton",
            Source = "(())",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()",
            ExpectedRaw = "S[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LBlock(LEmpty)]),
            Probes =
            [
                new SpecProbe("count((()))", "ok raw=0 n=1"),
                new SpecProbe("() == (())", "ok raw=1 n=1"),
            ],
            Explanation = "Redundant parentheses around `()` are one written grouping level that canonicalizes away: `(())` is the same value as `()`.",
        },
        new()
        {
            Id = "empty-wrapped-twice",
            Category = "empty-and-singleton",
            Source = "((()))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()",
            ExpectedRaw = "S[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LBlock(LBlock(LEmpty))]),
            Explanation = "Canonicalization is not depth-limited: `((()))` is still `()`.",
        },
        new()
        {
            Id = "singleton-paren",
            Category = "empty-and-singleton",
            Source = "(7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7",
            ExpectedRaw = "7",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LBlock(".num 7")]),
            Probes =
            [
                new SpecProbe("(7) == 7", "ok raw=1 n=1"),
                new SpecProbe("count((7))", "ok raw=1 n=1"),
            ],
            Explanation = "Parentheses around one value are transparent grouping, not a one-item sequence: `(7)` is the atom `7`.",
        },
        new()
        {
            Id = "singleton-paren-deep",
            Category = "empty-and-singleton",
            Source = "(((7)))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7",
            ExpectedRaw = "7",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LBlock(LBlock(LBlock(".num 7")))]),
            Explanation = "Singleton sequence boundaries normalize away at every depth; `(((7)))` is the atom `7`.",
        },
        new()
        {
            Id = "empty-eq-family",
            Category = "empty-and-singleton",
            Source = "() == ()      // 1\n() == (())    // 1\n() != (())    // 0\ncount(())     // 0\ncount((()))   // 0",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n1\n0\n0\n0",
            ExpectedRaw = "S[1, 1, 0, 0, 0]",
            ExpectedEmittedCount = 5,
            LeanProgram = LProg([],
            [
                $".binary .eq {LEmpty} {LEmpty}",
                $".binary .eq {LEmpty} {LBlock(LEmpty)}",
                $".binary .ne {LEmpty} {LBlock(LEmpty)}",
                LCall("count", LEmpty),
                LCall("count", LBlock(LEmpty)),
            ]),
            Explanation = "Equality is structural on canonical values, so `()` and `(())` are the same value, and both count zero items.",
        },
        new()
        {
            Id = "empty-capture",
            Category = "empty-and-singleton",
            Source = "A = ()\nA",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()",
            ExpectedRaw = "S[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([LProp("A", LEmpty)], [".resolve \"A\""]),
            Probes =
            [
                new SpecProbe("A = ()\nA.count", "ok raw=0 n=1"),
                new SpecProbe("A = ()\nA == ()", "ok raw=1 n=1"),
                new SpecProbe("A = ()\nA:0", "err index"),
            ],
            Explanation = "`()` stores and reloads like any value: it displays as `()`, counts zero items, equals `()`, and has no item to index.",
        },

        // ==================== item-supply-vs-value ====================
        new()
        {
            Id = "supply-three-rows",
            Category = "item-supply-vs-value",
            Source = "10, 20, 30",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "10\n20\n30",
            ExpectedRaw = "S[10, 20, 30]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg([], [LNums(10, 20, 30)]),
            IncludeInGeneratorPrompt = true,
            Explanation = "A comma expression list at root output creates three top-level output slots — an item supply, not one sequence value.",
        },
        new()
        {
            Id = "value-three-items",
            Category = "item-supply-vs-value",
            Source = "(1 + 1, 2 + 2, 3 + 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(2, 4, 6)",
            ExpectedRaw = "S[2, 4, 6]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LBlock(
                ".binary .add (.num 1) (.num 1)",
                ".binary .add (.num 2) (.num 2)",
                ".binary .add (.num 3) (.num 3)")]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Parentheses materialize an expression list as one sequence value occupying one output slot.",
        },
        new()
        {
            Id = "adjacency-is-comma",
            Category = "item-supply-vs-value",
            Source = "1 2 3",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n3",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg([], [LNums(1, 2, 3)]),
            Notes = "Adjacency is a parser-level implicit comma; the elaborated AST is identical to `1, 2, 3`.",
            Explanation = "Same-line adjacency is an implicit expression-list separator: `1 2 3` is exactly `1, 2, 3`.",
        },
        new()
        {
            Id = "capture-supply",
            Category = "item-supply-vs-value",
            Source = "A = 1, 2, 3\nA",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3)",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([LProp("A", LNums(1, 2, 3))], [".resolve \"A\""]),
            Probes =
            [
                new SpecProbe("A = 1, 2, 3\ncount(A)", "ok raw=3 n=1"),
                new SpecProbe("A = 1, 2, 3\nA.count", "ok raw=3 n=1"),
                new SpecProbe("A = 1, 2, 3\nA == (1, 2, 3)", "ok raw=1 n=1"),
                new SpecProbe("A = 1, 2, 3\nA:0", "ok raw=1 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Property access is a value boundary: a multi-item body is observed by the caller as one canonical sequence value.",
        },
        new()
        {
            Id = "capture-supply-spread",
            Category = "item-supply-vs-value",
            Source = "A = 1, 2, 3\nA...",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n3",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg([LProp("A", LNums(1, 2, 3))], [".sequenceSpread (.resolve \"A\")"]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Postfix `...` reopens one sequence-value layer into the surrounding item supply — here back into three root output rows.",
        },
        new()
        {
            Id = "call-reentry-identity",
            Category = "item-supply-vs-value",
            Source = "I(a) = a\nA = 1, 2, 3\nI(I(A))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3)",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("I", ["a"], ".param \"a\""), LProp("A", LNums(1, 2, 3))],
                [LCall("I", LCall("I", ".resolve \"A\""))]),
            Explanation = "Re-entry through another receiver preserves the canonical value: passing a sequence value through identity functions changes nothing.",
        },
        new()
        {
            Id = "call-value-boundary",
            Category = "item-supply-vs-value",
            Source = "F(a...) = a\nF(5, 9)\nF(5, 9)...",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(5, 9)\n5\n9",
            ExpectedRaw = "S[S[5, 9], 5, 9]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LFnP("F", [LVar("a")], ".param \"a\"")],
                [LCall("F", ".num 5", ".num 9"), $".sequenceSpread ({LCall("F", ".num 5", ".num 9")})"]),
            IncludeInGeneratorPrompt = true,
            Explanation = "A call returns exactly one value; only explicit caller-site `...` reopens it into the surrounding item supply.",
        },
        new()
        {
            Id = "property-value-boundary",
            Category = "item-supply-vs-value",
            Source = "Coordinates = 10, 20\nCoordinates\nCoordinates...",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(10, 20)\n10\n20",
            ExpectedRaw = "S[S[10, 20], 10, 20]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("Coordinates", LNums(10, 20))],
                [".resolve \"Coordinates\"", ".sequenceSpread (.resolve \"Coordinates\")"]),
            Explanation = "Property-style access observes a multi-item body as one sequence value; caller-site spread re-opens it into separate output rows.",
        },
        new()
        {
            Id = "fixed-call-preserves-boundaries",
            Category = "item-supply-vs-value",
            Source = "Pair = 10, 20\nAdd(x, y) = x + y\n\nAdd(Pair)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            LeanProgram = LProg(
                [LProp("Pair", LNums(10, 20)), LFn("Add", ["x", "y"], ".binary .add (.param \"x\") (.param \"y\")")],
                [LCall("Add", ".resolve \"Pair\"")]),
            Probes =
            [
                new SpecProbe("Pair = 10, 20\nAdd(x, y) = x + y\nAdd(Pair...)", "ok raw=30 n=1"),
                new SpecProbe("Pair = 10, 20\nAdd(x, y) = x + y\nAdd(Pair:0, Pair:1)", "ok raw=30 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A property reference is one argument expression even when it evaluates to several items: `Add(Pair)` is an arity error. Open it explicitly with `Add(Pair...)` or index with `Add(Pair:0, Pair:1)`.",
        },
        new()
        {
            Id = "spread-fills-remaining-slots",
            Category = "item-supply-vs-value",
            Source = "Tail = 2, 3\nUse(a, b, c) = a + b + c\n\nUse(1, Tail...)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "6",
            ExpectedRaw = "6",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("Tail", LNums(2, 3)), LFn("Use", ["a", "b", "c"], ".binary .add (.binary .add (.param \"a\") (.param \"b\")) (.param \"c\")")],
                [LCall("Use", ".num 1", ".sequenceSpread (.resolve \"Tail\")")]),
            Probes =
            [
                new SpecProbe("Tail = 2, 3\nUse(a, b, c) = a + b + c\nUse(1, Tail)", "err arity"),
                new SpecProbe("Tail = 2, 3\nUse(a, b, c) = a + b + c\nUse(1...Tail)", "err arity"),
            ],
            Explanation = "`Tail...` spreads its items into the remaining argument slots; the unspread `Use(1, Tail)` supplies only two argument boundaries, and `Use(1...Tail)` spreads the scalar `1` (one item) so only two slots are supplied.",
        },

        // ==================== empty-visible-vs-spread ====================
        new()
        {
            Id = "empty-count-one-arg",
            Category = "empty-visible-vs-spread",
            Source = "count(())",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0",
            ExpectedRaw = "0",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("count", LEmpty)]),
            Explanation = "One supplied `()` is a single grouped value; the builtin collection binding opens it and finds zero items.",
        },
        new()
        {
            Id = "empty-count-two-args",
            Category = "empty-visible-vs-spread",
            Source = "count((), ())",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2",
            ExpectedRaw = "2",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("count", LEmpty, LEmpty)]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Two supplied `()` values are two visible items: singleton-boundary normalization applies only to a single grouped value, and sibling `()` items are preserved.",
        },
        new()
        {
            Id = "fixed-empty-arg-visible",
            Category = "empty-visible-vs-spread",
            Source = "F(a) = a\nF(())",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()",
            ExpectedRaw = "S[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([LFn("F", ["a"], ".param \"a\"")], [LCall("F", LEmpty)]),
            Explanation = "A non-spread `()` occupies one visible supplied slot: `F(())` binds `a = ()`.",
        },
        new()
        {
            Id = "fixed-empty-spread-zero-items",
            Category = "empty-visible-vs-spread",
            Source = "F(a) = a\nF(()...)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            LeanProgram = LProg([LFn("F", ["a"], ".param \"a\"")], [LCall("F", $".sequenceSpread {LEmpty}")]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Spreading `()` contributes zero items, so `F(()...)` supplies no arguments and the one-parameter call fails.",
        },
        new()
        {
            Id = "variadic-empty-arg-vs-spread",
            Category = "empty-visible-vs-spread",
            Source = "F(a...) = a.count\nF(())",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0",
            ExpectedRaw = "0",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("F", [LVar("a")], ".dotCall (.param \"a\") \"count\" none")],
                [LCall("F", LEmpty)]),
            Probes =
            [
                new SpecProbe("F(a...) = a.count\nF((), ())", "ok raw=2 n=1"),
                new SpecProbe("F(a...) = a.count\nF()", "ok raw=0 n=1"),
            ],
            Explanation = "A lone grouped `()` argument to a rest-only function opens to zero items, while two sibling `()` arguments stay two items, and the empty call binds the empty stream.",
        },
        new()
        {
            Id = "spread-empty-in-sequence",
            Category = "empty-visible-vs-spread",
            Source = "(()..., 99)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "99",
            ExpectedRaw = "99",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LBlock($".sequenceSpread {LEmpty}", ".num 99")]),
            Explanation = "Inside a written sequence value, `()...` contributes zero items, leaving one item — and a one-item construction is the item itself, not a wrapper.",
        },
        new()
        {
            Id = "empty-visible-in-sequence",
            Category = "empty-visible-vs-spread",
            Source = "((), 99)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "((), 99)",
            ExpectedRaw = "S[S[], 99]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LBlock(LEmpty, ".num 99")]),
            Explanation = "A written non-spread `()` stays a visible sequence item: `((), 99)` keeps two items.",
        },
        new()
        {
            Id = "empty-visible-at-root",
            Category = "empty-visible-vs-spread",
            Source = "(), 99",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()\n99",
            ExpectedRaw = "S[S[], 99]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg([], [LEmpty, ".num 99"]),
            Explanation = "At root output, a non-spread `()` slot is one visible row.",
        },

        // ==================== deconstruction ====================
        new()
        {
            Id = "decon-pair",
            Category = "deconstruction",
            Source = "x, y = 1, 2\nx\ny",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("d", LNums(1, 2)),
                 LDecon("d", [], ["x", "y"], -1, "x"),
                 LDecon("d", [], ["x", "y"], -1, "y")],
                [".resolve \"x\"", ".resolve \"y\""]),
            Explanation = "Assignment deconstruction matches fixed targets to the supplied items element-by-element.",
        },
        new()
        {
            Id = "decon-rest-tail",
            Category = "deconstruction",
            Source = "x, rest... = 1, 2, 3\nrest",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(2, 3)",
            ExpectedRaw = "S[2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("d", LNums(1, 2, 3)), LDecon("d", [], ["x", "rest"], 1, "rest")],
                [".resolve \"rest\""]),
            Explanation = "The rest target captures the remaining items as one grouped sequence value.",
        },
        new()
        {
            Id = "decon-rest-head",
            Category = "deconstruction",
            Source = "head..., last = 1, 2, 3\nhead\nlast",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2)\n3",
            ExpectedRaw = "S[S[1, 2], 3]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("d", LNums(1, 2, 3)),
                 LDecon("d", [], ["head", "last"], 0, "head"),
                 LDecon("d", [], ["head", "last"], 0, "last")],
                [".resolve \"head\"", ".resolve \"last\""]),
            Explanation = "The single movable rest may lead: fixed targets after it bind from the back.",
        },
        new()
        {
            Id = "decon-rest-middle",
            Category = "deconstruction",
            Source = "x, middle..., z = 1, 2, 3, 4\nmiddle",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(2, 3)",
            ExpectedRaw = "S[2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("d", LNums(1, 2, 3, 4)), LDecon("d", [], ["x", "middle", "z"], 1, "middle")],
                [".resolve \"middle\""]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Front and back fixed targets bind first; the middle rest captures what remains.",
        },
        new()
        {
            Id = "decon-empty-rest",
            Category = "deconstruction",
            Source = "x, rest... = 1\nrest\nx",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()\n1",
            ExpectedRaw = "S[S[], 1]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("d", ".num 1"),
                 LDecon("d", [], ["x", "rest"], 1, "rest"),
                 LDecon("d", [], ["x", "rest"], 1, "x")],
                [".resolve \"rest\"", ".resolve \"x\""]),
            Probes =
            [
                new SpecProbe("x, rest... = 1\nrest.count", "ok raw=0 n=1"),
                new SpecProbe("x, rest... = 1\nrest...\nx", "ok raw=1 n=1"),
            ],
            Explanation = "A rest that captures zero items binds `()`, which stays one visible output slot; only spreading it contributes zero items.",
        },
        new()
        {
            Id = "decon-arity-under",
            Category = "deconstruction",
            Source = "x, y = 1\nx",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            LeanProgram = LProg(
                [LProp("d", ".num 1"), LDecon("d", [], ["x", "y"], -1, "x")],
                [".resolve \"x\""]),
            Explanation = "Without a rest target the item count must match exactly: one supplied item cannot bind two targets.",
        },
        new()
        {
            Id = "decon-arity-over",
            Category = "deconstruction",
            Source = "x, y = 1, 2, 3\nx",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            LeanProgram = LProg(
                [LProp("d", LNums(1, 2, 3)), LDecon("d", [], ["x", "y"], -1, "x")],
                [".resolve \"x\""]),
            Explanation = "Three supplied items cannot bind two fixed targets.",
        },
        new()
        {
            Id = "decon-unpacks-stored-value",
            Category = "deconstruction",
            Source = "A = 1, 2, 3\nx, y, z = A\ny",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2",
            ExpectedRaw = "2",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("A", LNums(1, 2, 3)),
                 LProp("d", ".resolve \"A\""),
                 LDecon("d", [], ["x", "y", "z"], -1, "y")],
                [".resolve \"y\""]),
            Probes =
            [
                new SpecProbe("A = 1, 2, 3\nx, y, z = A...\ny", "ok raw=2 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Assignment deconstruction is an unpacking receiver: a single stored sequence value is opened and matched element-by-element, so `= A` and `= A...` bind identically. Function calls do NOT unpack this way — `F(A)` still passes one argument.",
        },
        new()
        {
            Id = "decon-tutorial-full",
            Category = "deconstruction",
            Source = "A = 1, 2, 3, 4, 5\n\nx, y..., z = A\nx\ny\nz",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n(2, 3, 4)\n5",
            ExpectedRaw = "S[1, S[2, 3, 4], 5]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("A", LNums(1, 2, 3, 4, 5)),
                 LProp("d", ".resolve \"A\""),
                 LDecon("d", [], ["x", "y", "z"], 1, "x"),
                 LDecon("d", [], ["x", "y", "z"], 1, "y"),
                 LDecon("d", [], ["x", "y", "z"], 1, "z")],
                [".resolve \"x\"", ".resolve \"y\"", ".resolve \"z\""]),
            Explanation = "Deconstruction with a middle rest over a stored sequence value: fixed targets take the ends, the rest keeps the middle as one grouped value.",
        },
        new()
        {
            Id = "decon-two-rests-rejected",
            Category = "deconstruction",
            Source = "a..., b... = 1, 2, 3\na",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "at most one rest binding",
            Explanation = "A deconstruction pattern allows at most one rest binding.",
        },
        new()
        {
            Id = "decon-lone-rest-rejected",
            Category = "deconstruction",
            Source = "all... = 1, 2, 3\nall",
            Outcome = SpecOutcome.ParseError,
            Explanation = "A deconstruction pattern needs at least two targets; rest-only item-supply binding belongs to function parameters, not assignment.",
        },

        // ==================== variadic-calls ====================
        new()
        {
            Id = "variadic-grouped-and-spread",
            Category = "variadic-calls",
            Source = "A = 1, 2, 3, 4, 5\n\nG(x...) = x.sum\n\nG(A)\nG(A...)\nG(1, 2, 3, 4, 5)\nG((1, 2, 3, 4, 5))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "15\n15\n15\n15",
            ExpectedRaw = "S[15, 15, 15, 15]",
            ExpectedEmittedCount = 4,
            LeanProgram = LProg(
                [LProp("A", LNums(1, 2, 3, 4, 5)),
                 LFnP("G", [LVar("x")], ".dotCall (.param \"x\") \"sum\" none")],
                [LCall("G", ".resolve \"A\""),
                 LCall("G", ".sequenceSpread (.resolve \"A\")"),
                 LCall("G", LNums(1, 2, 3, 4, 5)),
                 LCall("G", LBlock(LNums(1, 2, 3, 4, 5)))]),
            IncludeInGeneratorPrompt = true,
            Explanation = "A lone rest parameter captures the supplied argument stream as one canonical value; for rest-only shapes the grouped and opened supply display the same value, though they supply different argument streams.",
        },
        new()
        {
            Id = "variadic-siblings-preserved",
            Category = "variadic-calls",
            Source = "A = 1, 2\nB = 3, 4\n\nG(x...) = x.count\n\nG(A, B)\nG(A..., B...)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2\n4",
            ExpectedRaw = "S[2, 4]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("A", LNums(1, 2)), LProp("B", LNums(3, 4)),
                 LFnP("G", [LVar("x")], ".dotCall (.param \"x\") \"count\" none")],
                [LCall("G", ".resolve \"A\"", ".resolve \"B\""),
                 LCall("G", ".sequenceSpread (.resolve \"A\")", ".sequenceSpread (.resolve \"B\")")]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Sibling grouped values are preserved as two items unless each is explicitly opened with `...`.",
        },
        new()
        {
            Id = "variadic-capture-canonical",
            Category = "variadic-calls",
            Source = "F(x...) = x\nF(1, 2, 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3)",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("F", [LVar("x")], ".param \"x\"")],
                [LCall("F", LNums(1, 2, 3))]),
            Probes =
            [
                new SpecProbe("F(x...) = x\ncount(F(1, 2, 3))", "ok raw=3 n=1"),
                new SpecProbe("F(x...) = x\nF(1, 2, 3) == (1, 2, 3)", "ok raw=1 n=1"),
            ],
            Explanation = "Capture converts an item supply into one canonical sequence value.",
        },
        new()
        {
            Id = "mixed-rest-binding",
            Category = "variadic-calls",
            Source = "F(x, y..., z) = x + y.sum + z\nF(1, 2, 3, 4, 5)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "15",
            ExpectedRaw = "15",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("F", [LFix("x"), LVar("y"), LFix("z")],
                    ".binary .add (.binary .add (.param \"x\") (.dotCall (.param \"y\") \"sum\" none)) (.param \"z\")")],
                [LCall("F", LNums(1, 2, 3, 4, 5))]),
            Probes =
            [
                new SpecProbe("F(x, y..., z) = x + y.sum + z\nF(1, 2)", "ok raw=3 n=1"),
                new SpecProbe("F(x, y..., z) = x + y.sum + z\nA = 1, 2, 3, 4, 5\nF(A)", "err arity"),
                new SpecProbe("F(x, y..., z) = y\nF(1, 2, 3, 4, 5)", "ok raw=S[2, 3, 4] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Mixed fixed/rest parameter lists bind the call's argument stream: fixed captures take the front and back, the rest keeps the middle (possibly zero items). A plain call does not implicitly open a single sequence argument, so `F(A)` fails.",
        },
        new()
        {
            Id = "mixed-front-back-family",
            Category = "variadic-calls",
            Source = "Arg = 1, 2, 3\n\nHead(first, rest...) = first\nTail(first, rest...) = rest\nInit(init..., last) = init\nLast(init..., last) = last\n\nHead(1, (2, 3))\nTail(1, (2, 3))\nInit((1, 2), 3)\nLast(Arg, 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n(2, 3)\n(1, 2)\n3",
            ExpectedRaw = "S[1, S[2, 3], S[1, 2], 3]",
            ExpectedEmittedCount = 4,
            LeanProgram = LProg(
                [LProp("Arg", LNums(1, 2, 3)),
                 LFnP("Head", [LFix("first"), LVar("rest")], ".param \"first\""),
                 LFnP("Tail", [LFix("first"), LVar("rest")], ".param \"rest\""),
                 LFnP("Init", [LVar("init"), LFix("last")], ".param \"init\""),
                 LFnP("Last", [LVar("init"), LFix("last")], ".param \"last\"")],
                [LCall("Head", ".num 1", LBlock(LNums(2, 3))),
                 LCall("Tail", ".num 1", LBlock(LNums(2, 3))),
                 LCall("Init", LBlock(LNums(1, 2)), ".num 3"),
                 LCall("Last", ".resolve \"Arg\"", ".num 3")]),
            Explanation = "Grouped arguments are single slots: a rest of one grouped value collapses to that value, and fixed captures bind whole argument boundaries.",
        },
        new()
        {
            Id = "rest-grouped-vs-opened",
            Category = "variadic-calls",
            Source = "H(h, t...) = t\nH((1, 2))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()",
            ExpectedRaw = "S[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("H", [LFix("h"), LVar("t")], ".param \"t\"")],
                [LCall("H", LBlock(LNums(1, 2)))]),
            Probes =
            [
                new SpecProbe("H(h, t...) = t\nH((1, 2)...)", "ok raw=2 n=1"),
            ],
            Explanation = "Mixed shapes make the supply boundary observable: `H((1, 2))` binds `h` to the whole pair leaving an empty rest, while `H((1, 2)...)` opens the pair first so `h = 1` and `t` collapses to `2`.",
        },
        new()
        {
            Id = "variadic-nested-not-flattened",
            Category = "variadic-calls",
            Source = "Arg = (1, 2), (3, 4)\n\nMany(values...) = values.count\nFlattened = atoms(Arg).count\n\nMany(Arg)\nFlattened",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2\n4",
            ExpectedRaw = "S[2, 4]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("Arg", $"{LBlock(LNums(1, 2))}, {LBlock(LNums(3, 4))}"),
                 LFnP("Many", [LVar("values")], ".dotCall (.param \"values\") \"count\" none"),
                 LProp("Flattened", $".dotCall ({LCall("atoms", ".resolve \"Arg\"")}) \"count\" none")],
                [LCall("Many", ".resolve \"Arg\""), ".resolve \"Flattened\""]),
            Explanation = "Variadic capture is not recursive flattening: nested sequence values stay top-level items; `atoms` is the explicit recursive projection.",
        },
        new()
        {
            Id = "supply-vs-value-patterns",
            Category = "variadic-calls",
            Source = "CountValues(values...) = values.count\nCountSequenceValue((values...)) = values.count\n\nCountValues()\nCountValues(1, 2, 3)\nCountValues((1, 2, 3))\nCountSequenceValue((1, 2, 3))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0\n3\n3\n3",
            ExpectedRaw = "S[0, 3, 3, 3]",
            ExpectedEmittedCount = 4,
            LeanProgram = LProg(
                [LFnP("CountValues", [LVar("values")], ".dotCall (.param \"values\") \"count\" none"),
                 LFnPat("CountSequenceValue", [".sequenceValue [.capture { name := \"values\", kind := .variadic }]"],
                     ".dotCall (.param \"values\") \"count\" none")],
                [".call (.resolve \"CountValues\") (alg [] [] [] [])",
                 LCall("CountValues", LNums(1, 2, 3)),
                 LCall("CountValues", LBlock(LNums(1, 2, 3))),
                 LCall("CountSequenceValue", LBlock(LNums(1, 2, 3)))]),
            Explanation = "Top-level `values...` consumes the call's item supply, while the sequence-value pattern `(values...)` consumes exactly one grouped argument and opens it during binding.",
        },
        new()
        {
            Id = "redundant-call-parens-canonical",
            Category = "variadic-calls",
            Source = "Inner = (1, 2, 3)\nCountSequenceValue((values...)) = values.count\nNestedCount(((values...))) = values.count\n\nCountSequenceValue(Inner)\nCountSequenceValue((Inner))\nCountSequenceValue(((1, 2, 3)))\nNestedCount(((1, 2, 3)))\nNestedCount((((1, 2, 3))))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3\n3\n3\n3\n3",
            ExpectedRaw = "S[3, 3, 3, 3, 3]",
            ExpectedEmittedCount = 5,
            LeanProgram = LProg(
                [LProp("Inner", LBlock(LNums(1, 2, 3))),
                 LFnPat("CountSequenceValue", [".sequenceValue [.capture { name := \"values\", kind := .variadic }]"],
                     ".dotCall (.param \"values\") \"count\" none"),
                 LFnPat("NestedCount", [".sequenceValue [.sequenceValue [.capture { name := \"values\", kind := .variadic }]]"],
                     ".dotCall (.param \"values\") \"count\" none")],
                [LCall("CountSequenceValue", ".resolve \"Inner\""),
                 LCall("CountSequenceValue", LBlock(".resolve \"Inner\"")),
                 LCall("CountSequenceValue", LBlock(LBlock(LNums(1, 2, 3)))),
                 LCall("NestedCount", LBlock(LBlock(LNums(1, 2, 3)))),
                 LCall("NestedCount", LBlock(LBlock(LBlock(LNums(1, 2, 3)))))]),
            Probes =
            [
                new SpecProbe("NestedCount(((values...))) = values.count\nNestedCount((1, 2, 3))", "err arity"),
                new SpecProbe("CountSequenceValue((values...)) = values.count\nCountSequenceValue(((1, 2), 3))", "ok raw=2 n=1"),
            ],
            Explanation = "Redundant unary parentheses canonicalize during value construction and never add an observable sequence level; the explicit nested pattern level and non-unary structure remain observable.",
        },

        // ==================== sequence-construction ====================
        new()
        {
            Id = "wrapped-pair-collapses",
            Category = "sequence-construction",
            Source = "((1, 2))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2)",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LBlock(LBlock(LNums(1, 2)))]),
            Probes =
            [
                new SpecProbe("((1, 2)) == (1, 2)", "ok raw=1 n=1"),
                new SpecProbe("count(((1, 2)))", "ok raw=2 n=1"),
            ],
            Explanation = "`((1, 2))` is not a one-item wrapper around a pair — redundant unary sequence structure canonicalizes to the pair itself. Orphan wrappers are not writable KatLang values.",
        },
        new()
        {
            Id = "pair-of-pairs-preserved",
            Category = "sequence-construction",
            Source = "((1, 2), (3, 4))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "((1, 2), (3, 4))",
            ExpectedRaw = "S[S[1, 2], S[3, 4]]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [PairOfPairs]),
            Probes =
            [
                new SpecProbe("count(((1, 2), (3, 4)))", "ok raw=2 n=1"),
                new SpecProbe("x = ((1, 2), (3, 4))\nx:0", "ok raw=S[1, 2] n=2"),
                new SpecProbe("x = ((1, 2), (3, 4))\nx == ((1, 2), (3, 4))", "ok raw=1 n=1"),
            ],
            Explanation = "Non-unary nested structure is never flattened: a pair of pairs keeps both boundaries.",
        },
        new()
        {
            Id = "pair-then-empty-preserved",
            Category = "sequence-construction",
            Source = "((1, 2), ())",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "((1, 2), ())",
            ExpectedRaw = "S[S[1, 2], S[]]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LBlock(LBlock(LNums(1, 2)), LEmpty)]),
            Explanation = "A written `()` item inside a sequence value stays visible.",
        },
        new()
        {
            Id = "spread-splices-into-sequence",
            Category = "sequence-construction",
            Source = "x = (1, 2)\n(x..., 99)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 99)",
            ExpectedRaw = "S[1, 2, 99]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("x", LBlock(LNums(1, 2)))],
                [LBlock(".sequenceSpread (.resolve \"x\")", ".num 99")]),
            Explanation = "Spread inside a written sequence value splices exactly one layer of items beside the sibling slots.",
        },
        new()
        {
            Id = "spread-empty-between-siblings",
            Category = "sequence-construction",
            Source = "(1..., (), 2...)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, (), 2)",
            ExpectedRaw = "S[1, S[], 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LBlock(".sequenceSpread (.num 1)", LEmpty, ".sequenceSpread (.num 2)")]),
            Explanation = "Spreading a scalar contributes the scalar itself; the written `()` slot between the spreads stays a visible item.",
        },
        new()
        {
            Id = "root-spread-beside-slot",
            Category = "sequence-construction",
            Source = "A = (1, 2)\nA..., 99",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n99",
            ExpectedRaw = "S[1, 2, 99]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("A", LBlock(LNums(1, 2)))],
                [".sequenceSpread (.resolve \"A\")", ".num 99"]),
            Explanation = "At root output a spread slot contributes its opened items as rows beside the other slots.",
        },
        new()
        {
            Id = "root-spread-then-value-slot",
            Category = "sequence-construction",
            Source = "First = 1, 2\nSecond = 3, 4\n\nFirst...Second",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n(3, 4)",
            ExpectedRaw = "S[1, 2, S[3, 4]]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("First", LNums(1, 2)), LProp("Second", LNums(3, 4))],
                [".sequenceSpread (.resolve \"First\")", ".resolve \"Second\""]),
            Explanation = "`First...Second` is the expression list `First..., Second` (postfix `...` never takes a right operand): the spread opens `First` into two rows and `Second` stays one sequence-valued row.",
        },
        new()
        {
            Id = "spread-slots-capture",
            Category = "sequence-construction",
            Source = "A = 1, 2\nB = 1...2\n\nA.count\nB.count",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2\n2",
            ExpectedRaw = "S[2, 2]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("A", LNums(1, 2)),
                 LProp("B", ".sequenceSpread (.num 1), .num 2")],
                [".dotCall (.resolve \"A\") \"count\" none", ".dotCall (.resolve \"B\") \"count\" none"]),
            Explanation = "`B = 1...2` is the two-slot body `1..., 2`, so `B` captures the same two items as `A = 1, 2`.",
        },
        new()
        {
            Id = "spread-one-level-only",
            Category = "sequence-construction",
            Source = "(1, (2, 3))...4",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n(2, 3)\n4",
            ExpectedRaw = "S[1, S[2, 3], 4]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg([], [$".sequenceSpread {LBlock(".num 1", LBlock(LNums(2, 3)))}", ".num 4"]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Spread opens exactly one level: the inner `(2, 3)` stays intact, and `4` is a separate expression-list slot.",
        },

        // ==================== access-boundaries ====================
        new()
        {
            Id = "dot-access-value-boundary",
            Category = "access-boundaries",
            Source = "A = {\n    X = 1, 2, 3\n}\nA.X",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3)",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                ["privateProp \"A\" (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 1, .num 2, .num 3])] [])"],
                [".dotCall (.resolve \"A\") \"X\" none"]),
            Probes =
            [
                new SpecProbe("A = {\n    X = 1, 2, 3\n}\nA.X()", "ok raw=S[1, 2, 3] n=1"),
                new SpecProbe("A = {\n    X = 1, 2, 3\n}\ncount(A.X)", "ok raw=3 n=1"),
            ],
            Explanation = "Structural dot access observes the same value boundary as lexical access: one canonical sequence value.",
        },
        new()
        {
            Id = "property-call-boundary",
            Category = "access-boundaries",
            Source = "P = 1, 2, 3\nP()",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3)",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("P", LNums(1, 2, 3))],
                [".call (.resolve \"P\") (alg [] [] [] [])"]),
            Probes =
            [
                new SpecProbe("P = 1, 2, 3\nP.count", "ok raw=3 n=1"),
            ],
            Explanation = "Explicit zero-parameter call `P()` observes the same value as property-style access `P`; the difference is only cache usage.",
        },
        new()
        {
            Id = "builtin-result-reentry",
            Category = "access-boundaries",
            Source = "x = take((1, 2, 3), 2)\nx",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2)",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("x", LCall("take", LBlock(LNums(1, 2, 3)), ".num 2"))],
                [".resolve \"x\""]),
            Probes =
            [
                new SpecProbe("I(a) = a\nI(take((1, 2, 3), 2))", "ok raw=S[1, 2] n=1"),
                new SpecProbe("G(a...) = a\nG(take((1, 2, 3), 2))", "ok raw=S[1, 2] n=1"),
                new SpecProbe("take((1, 2, 3), 2) == (1, 2)", "ok raw=1 n=1"),
                new SpecProbe("count(take((1, 2, 3), 2))", "ok raw=2 n=1"),
            ],
            Explanation = "A collection builtin's result re-enters every receiver unchanged: capture, identity calls, variadic binding, equality, and count all observe the same canonical value.",
        },
        new()
        {
            Id = "zero-arg-access-of-parametrized",
            Category = "access-boundaries",
            Source = "Add(a, b) = a + b\n\nAdd\n(1, 2)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            LeanProgram = LProg(
                [LFn("Add", ["a", "b"], ".binary .add (.param \"a\") (.param \"b\")")],
                [".resolve \"Add\"", LBlock(LNums(1, 2))]),
            Explanation = "A physical newline never continues a closed expression into a call: `Add` alone is a zero-argument access of a two-parameter callable (an arity error), and `(1, 2)` is a separate row.",
        },

        // ==================== collection-builtins ====================
        new()
        {
            Id = "take-prefix",
            Category = "collection-builtins",
            Source = "take((1, 2, 3, 4, 5), 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3)",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("take", LBlock(LNums(1, 2, 3, 4, 5)), ".num 3")]),
            Explanation = "`take` keeps the first `count` items and returns them as one sequence value.",
        },
        new()
        {
            Id = "take-single-survivor",
            Category = "collection-builtins",
            Source = "take(((1, 2), (3, 4)), 1)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2)",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("take", PairOfPairs, ".num 1")]),
            Probes =
            [
                new SpecProbe("count(take(((1, 2), (3, 4)), 1))", "ok raw=2 n=1"),
                new SpecProbe("take(((1, 2), (3, 4)), 1) == (1, 2)", "ok raw=1 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A single kept item IS the result: `take(((1, 2), (3, 4)), 1)` is the pair `(1, 2)` itself, never the unwritable one-item wrapper `((1, 2))`; its count is therefore 2.",
        },
        new()
        {
            Id = "take-zero-empty",
            Category = "collection-builtins",
            Source = "take((1, 2, 3), 0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()",
            ExpectedRaw = "S[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("take", LBlock(LNums(1, 2, 3)), ".num 0")]),
            Explanation = "Zero kept items form the empty sequence value `()`.",
        },
        new()
        {
            Id = "skip-prefix",
            Category = "collection-builtins",
            Source = "skip((1, 2, 3, 4, 5), 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(4, 5)",
            ExpectedRaw = "S[4, 5]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("skip", LBlock(LNums(1, 2, 3, 4, 5)), ".num 3")]),
            Probes =
            [
                new SpecProbe("skip(((1, 2), (3, 4)), 1)", "ok raw=S[3, 4] n=1"),
                new SpecProbe("skip((1, 2), 5)", "ok raw=S[] n=1"),
            ],
            Explanation = "`skip` drops the first `count` items; a single remaining item is that item itself, and skipping everything leaves `()`.",
        },
        new()
        {
            Id = "filter-keeps-matching",
            Category = "collection-builtins",
            Source = "IsEven = x mod 2 == 0\nfilter((1, 2, 3, 4, 5, 6), IsEven)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(2, 4, 6)",
            ExpectedRaw = "S[2, 4, 6]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("IsEven", ["x"], ".binary .eq (.binary .mod (.param \"x\") (.num 2)) (.num 0)")],
                [LCall("filter", LBlock(LNums(1, 2, 3, 4, 5, 6)), ".resolve \"IsEven\"")]),
            Explanation = "`filter` keeps items whose predicate result is one nonzero atomic value, returning one sequence value.",
        },
        new()
        {
            Id = "filter-single-survivor",
            Category = "collection-builtins",
            Source = "Big(a) = a > 2\nfilter((1, 2, 3), Big)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("Big", ["a"], ".binary .gt (.param \"a\") (.num 2)")],
                [LCall("filter", LBlock(LNums(1, 2, 3)), ".resolve \"Big\"")]),
            Explanation = "The multi-item-to-singleton transition: one surviving item is returned as that item itself.",
        },
        new()
        {
            Id = "filter-none-empty",
            Category = "collection-builtins",
            Source = "No(a) = 0\nfilter((1, 2, 3), No)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()",
            ExpectedRaw = "S[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("No", ["a"], ".num 0")],
                [LCall("filter", LBlock(LNums(1, 2, 3)), ".resolve \"No\"")]),
            Probes =
            [
                new SpecProbe("No(a) = 0\nfilter((1, 2, 3), No) == ()", "ok raw=1 n=1"),
            ],
            Explanation = "Zero survivors form the empty sequence value, which equals `()` structurally.",
        },
        new()
        {
            Id = "map-transforms-items",
            Category = "collection-builtins",
            Source = "Double = x * 2\nmap((1, 2, 3), Double)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(2, 4, 6)",
            ExpectedRaw = "S[2, 4, 6]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("Double", ["x"], ".binary .mul (.param \"x\") (.num 2)")],
                [LCall("map", LBlock(LNums(1, 2, 3)), ".resolve \"Double\"")]),
            Explanation = "`map` replaces each top-level item with the callback result, preserving order and count.",
        },
        new()
        {
            Id = "map-single-item",
            Category = "collection-builtins",
            Source = "M(a) = a\nmap((7), M)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7",
            ExpectedRaw = "7",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("M", ["a"], ".param \"a\"")],
                [LCall("map", LBlock(".num 7"), ".resolve \"M\"")]),
            Explanation = "`(7)` is the atom 7 (singleton parens are transparent), so mapping over it yields the single mapped item itself.",
        },
        new()
        {
            Id = "map-pair-callback",
            Category = "collection-builtins",
            Source = "Swap(a, b) = (b, a)\nmap(((1, 2), (3, 4)), Swap)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "((2, 1), (4, 3))",
            ExpectedRaw = "S[S[2, 1], S[4, 3]]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("Swap", ["a", "b"], LBlock(".param \"b\", .param \"a\""))],
                [LCall("map", PairOfPairs, ".resolve \"Swap\"")]),
            Explanation = "Sequence-value callback items are projected one level to the callback's parameters; the callback must return exactly one value per item.",
        },
        new()
        {
            Id = "distinct-preserves-first",
            Category = "collection-builtins",
            Source = "distinct((3, 1, 3, 2, 1, 2))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(3, 1, 2)",
            ExpectedRaw = "S[3, 1, 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("distinct", LBlock(LNums(3, 1, 3, 2, 1, 2)))]),
            Explanation = "`distinct` keeps the first occurrence of each structurally-equal item.",
        },
        new()
        {
            Id = "distinct-structural-pairs",
            Category = "collection-builtins",
            Source = "distinct(((1, 2), (1, 2), (3, 4)))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "((1, 2), (3, 4))",
            ExpectedRaw = "S[S[1, 2], S[3, 4]]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("distinct",
                LBlock(LBlock(LNums(1, 2)), LBlock(LNums(1, 2)), LBlock(LNums(3, 4))))]),
            Explanation = "Deduplication uses structural equality on whole sequence-value items.",
        },
        new()
        {
            Id = "take-family-tutorial",
            Category = "collection-builtins",
            Source = "take((1, 2, 3, 4, 5), 3)\n\ntake(((1, 2), (3, 4)), 1)\n\nrange(1, 5).take(2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3)\n(1, 2)\n(1, 2)",
            ExpectedRaw = "S[S[1, 2, 3], S[1, 2], S[1, 2]]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg([],
                [LCall("take", LBlock(LNums(1, 2, 3, 4, 5)), ".num 3"),
                 LCall("take", PairOfPairs, ".num 1"),
                 $".dotCall ({LCall("range", ".num 1", ".num 5")}) \"take\" (some (alg [] [] [] [.num 2]))"]),
            Explanation = "The tutorial's `take` examples: a plain prefix, the single-survivor case (the kept pair itself, no wrapper), and the dot-call form.",
        },
        new()
        {
            Id = "distinct-family-tutorial",
            Category = "collection-builtins",
            Source = "distinct((3, 1, 3, 2, 1, 2))\n\ndistinct(((1, 2), (1, 2), (3, 4)))\n\nValues = 3, 1, 3, 2, 1, 2\nValues.distinct",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(3, 1, 2)\n((1, 2), (3, 4))\n(3, 1, 2)",
            ExpectedRaw = "S[S[3, 1, 2], S[S[1, 2], S[3, 4]], S[3, 1, 2]]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("Values", LNums(3, 1, 3, 2, 1, 2))],
                [LCall("distinct", LBlock(LNums(3, 1, 3, 2, 1, 2))),
                 LCall("distinct", LBlock(LBlock(LNums(1, 2)), LBlock(LNums(1, 2)), LBlock(LNums(3, 4)))),
                 ".dotCall (.resolve \"Values\") \"distinct\" none"]),
            Explanation = "The tutorial's `distinct` examples: atom dedup, structural pair dedup, and the dot-call form over a captured multi-item body.",
        },
        new()
        {
            Id = "spread-one-level-family",
            Category = "sequence-construction",
            Source = "(1, 2)...3\n1...(2, 3)\n(1, (2, 3))...4",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n3\n1\n(2, 3)\n1\n(2, 3)\n4",
            ExpectedRaw = "S[1, 2, 3, 1, S[2, 3], 1, S[2, 3], 4]",
            ExpectedEmittedCount = 8,
            LeanProgram = LProg([],
                [$".sequenceSpread {LBlock(LNums(1, 2))}", ".num 3",
                 ".sequenceSpread (.num 1)", LBlock(LNums(2, 3)),
                 $".sequenceSpread {LBlock(".num 1", LBlock(LNums(2, 3)))}", ".num 4"]),
            Explanation = "Spread projects exactly one immediate level and the following expression is always a separate slot: each line contributes its opened items plus the trailing slot as root rows.",
        },
        new()
        {
            Id = "distinct-empties-collapse",
            Category = "collection-builtins",
            Source = "distinct((), ())",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()",
            ExpectedRaw = "S[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("distinct", LEmpty, LEmpty)]),
            Explanation = "Two supplied `()` items deduplicate to one kept `()`, and a single kept item is the result itself: `()`.",
        },
        new()
        {
            Id = "order-sorts-atoms",
            Category = "collection-builtins",
            Source = "order((3, 4, 2, 1, 3, 3))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3, 3, 3, 4)",
            ExpectedRaw = "S[1, 2, 3, 3, 3, 4]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("order", LBlock(LNums(3, 4, 2, 1, 3, 3)))]),
            Probes =
            [
                new SpecProbe("order(5)", "ok raw=5 n=1"),
                new SpecProbe("order(())", "ok raw=S[] n=1"),
            ],
            Explanation = "`order` sorts numeric items ascending; a single item or empty input passes through canonically.",
        },
        new()
        {
            Id = "range-inclusive",
            Category = "collection-builtins",
            Source = "range(1, 5)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3, 4, 5)",
            ExpectedRaw = "S[1, 2, 3, 4, 5]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("range", ".num 1", ".num 5")]),
            Probes =
            [
                new SpecProbe("count(range(1, 5))", "ok raw=5 n=1"),
                new SpecProbe("range(1, 3):0", "ok raw=1 n=1"),
            ],
            Explanation = "`range` returns every integer from start to stop inclusive as one sequence value.",
        },
        new()
        {
            Id = "range-single-value",
            Category = "collection-builtins",
            Source = "range(3, 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("range", ".num 3", ".num 3")]),
            IncludeInGeneratorPrompt = true,
            Explanation = "A one-integer range is that integer itself — collection builtins never mint one-item wrappers.",
        },
        new()
        {
            Id = "atoms-recursive-flatten",
            Category = "collection-builtins",
            Source = "atoms(((1, 2), (3, 4)))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3, 4)",
            ExpectedRaw = "S[1, 2, 3, 4]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("atoms", PairOfPairs)]),
            Explanation = "`atoms` recursively erases all sequence-value structure — the explicit contrast to one-level spread.",
        },
        new()
        {
            Id = "sum-of-opened-range",
            Category = "collection-builtins",
            Source = "sum(range(1, 3)...)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "6",
            ExpectedRaw = "6",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("sum", $".sequenceSpread ({LCall("range", ".num 1", ".num 3")})")]),
            Explanation = "Caller-site spread opens a builtin result into the consuming builtin's item supply.",
        },
        new()
        {
            Id = "count-family",
            Category = "collection-builtins",
            Source = "count(())\ncount((()))\n\ncount(range(1, 5))\n\ncount((10, 20, 30))\n\ncount((3, 4, range(1, 5)..., 7))\n\ncount((range(1, 5)..., 7))\n\ncount(((1, 2), (3, 4)))\n\nData = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)\n(Data:0).count",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0\n0\n5\n3\n8\n6\n2\n5",
            ExpectedRaw = "S[0, 0, 5, 3, 8, 6, 2, 5]",
            ExpectedEmittedCount = 8,
            LeanProgram = LProg(
                [LProp("Data", $"{LBlock(LNums(7, 6, 4, 2, 1))}, {LBlock(LNums(1, 2, 3, 4, 5))}")],
                [LCall("count", LEmpty),
                 LCall("count", LBlock(LEmpty)),
                 LCall("count", LCall("range", ".num 1", ".num 5")),
                 LCall("count", LBlock(LNums(10, 20, 30))),
                 LCall("count", LBlock(".num 3", ".num 4", $".sequenceSpread ({LCall("range", ".num 1", ".num 5")})", ".num 7")),
                 LCall("count", LBlock($".sequenceSpread ({LCall("range", ".num 1", ".num 5")})", ".num 7")),
                 LCall("count", PairOfPairs),
                 ".dotCall (.index (.resolve \"Data\") (.num 0)) \"count\" none"]),
            Explanation = "`count` counts top-level items after the builtin collection binding opens a single grouped value: `()` counts 0, spreads splice before counting, nested pairs count as whole items, and a projected item counts its own contents.",
        },
        new()
        {
            Id = "count-scalar-and-string",
            Category = "collection-builtins",
            Source = "count(5)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1",
            ExpectedRaw = "1",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("count", ".num 5")]),
            Probes =
            [
                new SpecProbe("count('hello')", "ok raw=1 n=1"),
            ],
            Explanation = "An atomic value is a one-element collection for `count`.",
        },
        new()
        {
            Id = "count-dotcount-agree",
            Category = "collection-builtins",
            Source = "T = (1, 2, 3)\nT.count\n\nA = 1, 2, 3\nA.count\n\ncount(A)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3\n3\n3",
            ExpectedRaw = "S[3, 3, 3]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("T", LBlock(LNums(1, 2, 3))), LProp("A", LNums(1, 2, 3))],
                [".dotCall (.resolve \"T\") \"count\" none",
                 ".dotCall (.resolve \"A\") \"count\" none",
                 LCall("count", ".resolve \"A\"")]),
            Explanation = "`.count` and `count(...)` agree through both a written sequence value and a captured multi-item body.",
        },
        new()
        {
            Id = "if-value-boundary",
            Category = "collection-builtins",
            Source = "X = 1, 2, 3\nif(1, X, X)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3)",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("X", LNums(1, 2, 3))],
                [LCall("if", ".num 1", ".resolve \"X\"", ".resolve \"X\"")]),
            Probes =
            [
                new SpecProbe("X = 1, 2, 3\nif(1, X, X)...", "ok raw=S[1, 2, 3] n=3"),
            ],
            Explanation = "`if` is a value boundary like every builtin: the selected branch is one value, reopened only by caller-site spread.",
        },
        new()
        {
            Id = "reduce-accumulates-value",
            Category = "collection-builtins",
            Source = "Append(item, history...) = (history..., item)\nreduce((2, 3, 4), Append, 1)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3, 4)",
            ExpectedRaw = "S[1, 2, 3, 4]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("Append", [LFix("item"), LVar("history")],
                    LBlock(".sequenceSpread (.param \"history\")", ".param \"item\""))],
                [LCall("reduce", LBlock(LNums(2, 3, 4)), ".resolve \"Append\"", ".num 1")]),
            Probes =
            [
                new SpecProbe("Append(item, history...) = (history..., item)\nreduce(2, 3, 4, Append, 1)", "ok raw=S[1, 2, 3, 4] n=1"),
                new SpecProbe("Add(a, b) = a + b\nreduce((1, 2, 3, 4), Add, 0)", "ok raw=10 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`reduce` threads one accumulator value; the grouped-collection and open-supply call shapes bind the same items, and the result displays as ONE sequence value `(1, 2, 3, 4)` — not as separate rows.",
        },

        // ==================== equality-and-indexing ====================
        new()
        {
            Id = "eq-structural-nested",
            Category = "equality-and-indexing",
            Source = "A = 1, (2, 3)\nB = 1, (2, 3)\nA == B",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1",
            ExpectedRaw = "1",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("A", $".num 1, {LBlock(LNums(2, 3))}"),
                 LProp("B", $".num 1, {LBlock(LNums(2, 3))}")],
                [".binary .eq (.resolve \"A\") (.resolve \"B\")"]),
            Probes =
            [
                new SpecProbe("A = 1, (2, 3)\nC = 1, (2, 4)\nA == C", "ok raw=0 n=1"),
                new SpecProbe("1 == (1, 2)", "ok raw=0 n=1"),
            ],
            Explanation = "Equality is structural over the whole canonical value, including nested sequence boundaries.",
        },
        new()
        {
            Id = "index-selects-atom",
            Category = "equality-and-indexing",
            Source = "Nums = 10, 20, 30, 40, 50\n\n// Select the third value (index 2):\nNums:2",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "30",
            ExpectedRaw = "30",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("Nums", LNums(10, 20, 30, 40, 50))],
                [".index (.resolve \"Nums\") (.num 2)"]),
            Explanation = "`:` selects one top-level item by zero-based index; an atomic item is the result itself.",
        },
        new()
        {
            Id = "index-projects-one-level",
            Category = "equality-and-indexing",
            Source = "Pairs = (1, 2), (3, 4)\nPairs:0",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("Pairs", $"{LBlock(LNums(1, 2))}, {LBlock(LNums(3, 4))}")],
                [".index (.resolve \"Pairs\") (.num 0)"]),
            Probes =
            [
                new SpecProbe("Pairs = (1, 2), (3, 4)\n(Pairs:0).count", "ok raw=2 n=1"),
                new SpecProbe("G(a) = a\nPairs = (1, 2), (3, 4)\nG(Pairs:0)", "ok raw=S[1, 2] n=1"),
            ],
            Explanation = "Selection projects the selected item's content one level: a selected sequence value emits its immediate members (two root rows here), while any other receiver re-materializes them as one value.",
        },
        new()
        {
            Id = "index-nested-stays-intact",
            Category = "equality-and-indexing",
            Source = "Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8))\nBags:0\nBags:0:1",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "((1, 2), (3, 4))\n(3, 4)",
            ExpectedRaw = "S[S[S[1, 2], S[3, 4]], S[3, 4]]",
            ExpectedEmittedCount = 4,
            LeanProgram = LProg(
                [LProp("Bags",
                    $"{LBlock(LBlock(LNums(1, 2)), LBlock(LNums(3, 4)))}, {LBlock(LBlock(LNums(5, 6)), LBlock(LNums(7, 8)))}")],
                [".index (.resolve \"Bags\") (.num 0)",
                 ".index (.index (.resolve \"Bags\") (.num 0)) (.num 1)"]),
            Notes = "Root emitted count is 4 (each projection emits 2) while the accumulated root value has two items — display rows follow the value items; the projection supply is observable only for a lone root row.",
            Explanation = "Projection is one-level only and does not recursively flatten: nested pairs stay intact, and chaining `:` repeats the one-level step.",
        },
        new()
        {
            Id = "index-empty-item-visible",
            Category = "equality-and-indexing",
            Source = "x = ((), ())\nx:0",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "()",
            ExpectedRaw = "S[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("x", LBlock(LEmpty, LEmpty))],
                [".index (.resolve \"x\") (.num 0)"]),
            Explanation = "Selecting a `()` item shows one `()` row: the empty value is a real selectable item.",
        },
        new()
        {
            Id = "index-out-of-range",
            Category = "equality-and-indexing",
            Source = "x = (1, 2)\nx:9",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "index",
            LeanProgram = LProg(
                [LProp("x", LBlock(LNums(1, 2)))],
                [".index (.resolve \"x\") (.num 9)"]),
            Explanation = "Indexing past the last item is an index error, not an empty result.",
        },
        new()
        {
            Id = "index-captured-requality",
            Category = "equality-and-indexing",
            Source = "x = ((1, 2), (3, 4))\ny = x:0\ny == (1, 2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1",
            ExpectedRaw = "1",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("x", PairOfPairs),
                 LProp("y", ".index (.resolve \"x\") (.num 0)"),
                 ],
                [".binary .eq (.resolve \"y\") " + LBlock(LNums(1, 2))]),
            Explanation = "A captured projection re-materializes as the canonical selected value and compares structurally equal to the written literal.",
        },

        // ==================== parser-layout ====================
        new()
        {
            Id = "semicolon-not-expression-syntax",
            Category = "parser-layout",
            Source = "1 ; 2",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Semicolon is not supported as an expression separator",
            IncludeInGeneratorPrompt = true,
            Explanation = "Semicolon is not expression syntax: use comma or adjacency for separate slots, or parentheses for one sequence value.",
        },
        new()
        {
            Id = "trailing-comma-in-parens-rejected",
            Category = "parser-layout",
            Source = "(3,)",
            Outcome = SpecOutcome.ParseError,
            Explanation = "A trailing comma inside parentheses is not a one-item sequence constructor.",
        },
        new()
        {
            Id = "trailing-comma-continues-line",
            Category = "parser-layout",
            Source = "1,\n2",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg([], [LNums(1, 2)]),
            Explanation = "A trailing comma keeps the expression list open across the newline: two root output slots.",
        },
        new()
        {
            Id = "spread-not-binary-operand",
            Category = "parser-layout",
            Source = "A = (1, 2)\nA... == A...",
            Outcome = SpecOutcome.ParseError,
            Explanation = "A spread expression is not a binary operand; `...` results feed slots, not operators.",
        },
        new()
        {
            Id = "negative-index-literal-rejected",
            Category = "parser-layout",
            Source = "x = (1, 2)\nx:-1",
            Outcome = SpecOutcome.ParseError,
            Explanation = "A negative index selector never forms at parse time.",
        },
        new()
        {
            Id = "adjacency-call-across-space",
            Category = "parser-layout",
            Source = "Add(a, b) = a + b\n\nAdd(1, 2)    // 3\nAdd (1, 2)   // the same call, 3",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3\n3",
            ExpectedRaw = "S[3, 3]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LFn("Add", ["a", "b"], ".binary .add (.param \"a\") (.param \"b\")")],
                [LCall("Add", LNums(1, 2)), LCall("Add", LNums(1, 2))]),
            Explanation = "Postfix continuations win over adjacency on the same physical line: `Add (1, 2)` is still the call.",
        },
        new()
        {
            Id = "multiline-call-open-delimiter",
            Category = "parser-layout",
            Source = "Add(a, b) = a + b\n\nAdd(\n  1, 2\n)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("Add", ["a", "b"], ".binary .add (.param \"a\") (.param \"b\")")],
                [LCall("Add", LNums(1, 2))]),
            Notes = "Parse-level: an already-open argument list spans lines; the elaborated AST equals the single-line call.",
            Explanation = "For a multiline call, open the delimiter before the newline — an open argument list spans lines normally.",
        },
        new()
        {
            Id = "newline-ends-property-body",
            Category = "parser-layout",
            Source = "P = 1\n2",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2",
            ExpectedRaw = "2",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([LProp("P", ".num 1")], [".num 2"]),
            Explanation = "A simple one-line property body ends at the newline; the next line is a separate root output row.",
        },
        new()
        {
            Id = "comment-does-not-change-parse",
            Category = "parser-layout",
            Source = "// comment\n1 + 1",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2",
            ExpectedRaw = "2",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [".binary .add (.num 1) (.num 1)"]),
            Explanation = "Comments never change parse decisions.",
        },
        new()
        {
            Id = "spread-binds-before-list",
            Category = "parser-layout",
            Source = "X(vals...) = vals.count\nb = (1, 2)\nX(7 b...)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("X", [LVar("vals")], ".dotCall (.param \"vals\") \"count\" none"),
                 LProp("b", LBlock(LNums(1, 2)))],
                [LCall("X", ".num 7", ".sequenceSpread (.resolve \"b\")")]),
            Explanation = "Postfix `...` binds to its immediate operand before expression-list handling: `X(7 b...)` is `X(7, b...)`.",
        },
        new()
        {
            Id = "dot-chain-continuation",
            Category = "parser-layout",
            Source = "(1, 2, 3)\n.map { n * 2 }\n.sum",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "12",
            ExpectedRaw = "12",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([],
                [$".dotCall (.dotCall {LBlock(LNums(1, 2, 3))} \"map\" (some (alg [] [] [] [.block (alg [\"n\"] [] [] [.binary .mul (.param \"n\") (.num 2)])]))) \"sum\" none"]),
            Explanation = "A leading `.` is the supported method-chain continuation across lines.",
        },

        // ==================== errors ====================
        new()
        {
            Id = "arity-too-many-arguments",
            Category = "errors",
            Source = "KeepFirst(a, b) = a\nKeepFirst(42, 999, 1)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            LeanProgram = LProg(
                [LFn("KeepFirst", ["a", "b"], ".param \"a\"")],
                [LCall("KeepFirst", LNums(42, 999, 1))]),
            Explanation = "Supplying more arguments than fixed parameters is an arity error.",
        },
        new()
        {
            Id = "missing-output-not-a-value",
            Category = "errors",
            Source = "A = {\n}\nA",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "missingOutput",
            LeanProgram = LProg(
                ["privateProp \"A\" (alg [] [] [] [])"],
                [".resolve \"A\""]),
            Probes =
            [
                new SpecProbe("A = {\n}\nA == ()", "err missingOutput"),
                new SpecProbe("A = {\n}\nA...", "err spreadMissingOutput"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A no-output body is not a value: accessing it, comparing it with `()`, or spreading it are errors — `()` is a value, `{}` is not.",
        },
        new()
        {
            Id = "missing-output-as-builtin-arg",
            Category = "errors",
            Source = "count({})",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "missingOutput",
            LeanProgram = LProg([], [LCall("count", "(.block (alg [] [] [] []))")]),
            Explanation = "`{}` where a value is required is a missing-output error, not `0`.",
        },
        new()
        {
            Id = "scalar-op-rejects-sequence",
            Category = "errors",
            Source = "(1, 2) + 1",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            LeanProgram = LProg([], [$".binary .add {LBlock(LNums(1, 2))} (.num 1)"]),
            Probes =
            [
                new SpecProbe("() > 1", "ok raw=1 n=1"),
                new SpecProbe("() + 1", "ok raw=1 n=1"),
            ],
            Notes = "The probes pin the documented `()` operator transparency: for non-comparison operators `()` is a transparent passthrough, not a comparison result.",
            Explanation = "Scalar operators require numeric scalar operands; a multi-item sequence value is a type error. `()` alone is transparent for non-equality operators.",
        },
        new()
        {
            Id = "order-rejects-non-numeric",
            Category = "errors",
            Source = "order((1, 'hello'))",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            LeanProgram = LProg([], [LCall("order", LBlock(".num 1", "(.stringLiteral \"hello\")"))]),
            Probes =
            [
                new SpecProbe("order(((1, 2), (3, 4)))", "err arity"),
            ],
            Explanation = "`order` requires each item to be a single numeric value; strings and sequence-value items are rejected.",
        },
        new()
        {
            Id = "division-by-zero",
            Category = "errors",
            Source = "1 / 0",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "div0",
            LeanProgram = LProg([], [".binary .div (.num 1) (.num 0)"]),
            Explanation = "Division by zero is a runtime error.",
        },
        new()
        {
            Id = "unresolved-implicit-parameter",
            Category = "errors",
            Source = "Nope",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "unresolvedImplicitParams",
            LeanProgram = ".block (alg [\"Nope\"] [] [] [.param \"Nope\"])",
            Explanation = "An undefined name becomes an implicit parameter; running a program whose root still needs parameters is an error.",
        },

        // ==================== strings ====================
        new()
        {
            Id = "string-equality-exact",
            Category = "strings",
            Source = "'ab' == 'ab'",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1",
            ExpectedRaw = "1",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [".binary .eq (.stringLiteral \"ab\") (.stringLiteral \"ab\")"]),
            Probes =
            [
                new SpecProbe("count('ab')", "ok raw=1 n=1"),
            ],
            Explanation = "Strings compare by exact value and count as one item.",
        },
        new()
        {
            Id = "string-displays-unquoted",
            Category = "strings",
            Source = "x = 'ab'\nx",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "ab",
            ExpectedRaw = "'ab'",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([LProp("x", "(.stringLiteral \"ab\")")], [".resolve \"x\""]),
            Notes = "String display intentionally drops quotes (documented display non-roundtrip).",
            Explanation = "String values display without quotes.",
        },

        // ==================== implementation-only (C# decimal runtime) ====================
        new()
        {
            Id = "avg-decimal-mean",
            Category = "collection-builtins",
            Source = "avg((1, 2))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1.5",
            ExpectedRaw = "1.5",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Decimal mean: the C# runtime uses decimal numerics; the Lean Int core truncates (documented model limitation, tutorial 'Average' section).",
            Explanation = "`avg` returns the decimal mean in the runtime; the Lean Int-core model truncates and is documented as a model limitation, not the runtime contract.",
        },
    ];
}
