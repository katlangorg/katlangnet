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
        "lists",
        "conditionals",
    ];

    // ----- Lean program text helpers (same encoding as SemanticExplorerCorpus:
    // surviving parenthesized lists are `.capture` bundles, braces and roots
    // are `.algorithmExpr`, `()` is the empty-sequence node; the parser never
    // produces .sequenceConstruct) ------------------------------------------

    private static string LProg(IEnumerable<string> props, IEnumerable<string> outputs)
        => $".algorithmExpr (alg [] [] [{string.Join(", ", props)}] [{string.Join(", ", outputs)}])";

    private static string LProp(string name, params string[] outputs)
        => $"privateProp \"{name}\" (alg [] [] [] [{string.Join(", ", outputs)}])";

    private static string LFn(string name, string[] parameters, params string[] outputs)
        => $"privateProp \"{name}\" (alg [{string.Join(", ", parameters.Select(p => $"\"{p}\""))}] [] [] [{string.Join(", ", outputs)}])";

    private static string LFnP(string name, string[] parameterSpecs, params string[] outputs)
        => $"privateProp \"{name}\" (algWithParameters [{string.Join(", ", parameterSpecs)}] [] [] [{string.Join(", ", outputs)}])";

    private static string LFnPat(string name, string[] patterns, params string[] outputs)
        => $"privateProp \"{name}\" (algWithParameterPatterns [{string.Join(", ", patterns)}] [] [] [{string.Join(", ", outputs)}])";

    private static string LCall(string callee, params string[] args)
        => $".call (.resolve \"{callee}\") [{string.Join(", ", args)}]";

    private static string LCapture(params string[] outputs)
        => $"(.capture [{string.Join(", ", outputs)}])";

    private static string LNums(params int[] ns) => string.Join(", ", ns.Select(n => $".num {n}"));

    private const string LEmpty = "(.emptySequence 0)";

    private static string LVar(string name) => $"{{ name := \"{name}\", kind := .collecting }}";

    private static string LFix(string name) => $"{{ name := \"{name}\" }}";

    /// <summary>
    /// Parser-elaborated assignment deconstruction (same encoding as
    /// SemanticExplorerCorpus.LDecon): the RHS is evaluated once into a shared
    /// property and each observed target binds through an inline
    /// sequence-value parameter pattern that opens that shared value.
    /// </summary>
    private static string LDecon(string sharedProp, string[] rhsOutputs, string[] targets, int collectingIndex, string observed)
    {
        var captures = targets.Select((t, i) => i == collectingIndex
            ? $".capture {{ name := \"{t}\", kind := .collecting }}"
            : $".capture {{ name := \"{t}\" }}");
        var pattern = $".sequenceValue [{string.Join(", ", captures)}]";
        var helper = $".algorithmExpr (algWithParameterPatterns [{pattern}] [] [] [.param \"{observed}\"])";
        return $"privateProp \"{observed}\" (alg [] [] [] [.call ({helper}) [.resolve \"{sharedProp}\"]])";
    }

    private const string PairOfPairs =
        "(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])";

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
            Source = "# Define a property:\nAnswer = 42\n\n# Property-style access:\nAnswer\n\n# Explicit zero-parameter call:\nAnswer()",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "42\n42",
            ExpectedRaw = "S[42, 42]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("Answer", ".num 42")],
                [".resolve \"Answer\"", ".call (.resolve \"Answer\") []"]),
            Explanation = "Property-style access `Answer` and the explicit call `Answer()` observe the same value; the call shape only controls the zero-argument cache.",
        },
        new()
        {
            Id = "output-is-ordinary-property",
            Category = "arithmetic",
            Source = "Output = 5\nOutput",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5",
            ExpectedRaw = "5",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("Output", ".num 5")],
                [".resolve \"Output\""]),
            Probes =
            [
                new SpecProbe("A = 3\nOutput = A + 2", "err missingOutput"),
                new SpecProbe("A = 3\nOutput = A + 2\nOutput", "ok raw=5 n=1"),
                new SpecProbe("output = 6\noutput", "ok raw=6 n=1"),
                new SpecProbe("Output(x) = x * 2\nOutput(4)", "ok raw=8 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`Output` and `output` are ordinary identifiers: `Output = 5` defines a regular property named `Output`, and only bare expression rows contribute to algorithm output — a program whose rows are all definitions has no output.",
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
            LeanProgram = LProg([], [LEmpty]),
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
            LeanProgram = LProg([], [LEmpty]),
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
            LeanProgram = LProg([], [".num 7"]),
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
            LeanProgram = LProg([], [".num 7"]),
            Explanation = "Singleton sequence boundaries normalize away at every depth; `(((7)))` is the atom `7`.",
        },
        new()
        {
            Id = "empty-eq-family",
            Category = "empty-and-singleton",
            Source = "() == ()      # 1\n() == (())    # 1\n() != (())    # 0\ncount(())     # 0\ncount((()))   # 0",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n1\n0\n0\n0",
            ExpectedRaw = "S[1, 1, 0, 0, 0]",
            ExpectedEmittedCount = 5,
            LeanProgram = LProg([],
            [
                $".binary .eq {LEmpty} {LEmpty}",
                $".binary .eq {LEmpty} {LEmpty}",
                $".binary .ne {LEmpty} {LEmpty}",
                LCall("count", LEmpty),
                LCall("count", LEmpty),
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
            LeanProgram = LProg([], [LCapture(
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
            Source = "A = 1, 2, 3\nA*",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n3",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg([LProp("A", LNums(1, 2, 3))], [".sequenceSpread (.resolve \"A\")"]),
            IncludeInGeneratorPrompt = true,
            Explanation = "A spread expression spreads one sequence-value layer back into the surrounding item supply — here back into three root output rows.",
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
            Source = "F(*a) = a\nF(5, 9)\nF(5, 9)*",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[5, 9]\n5\n9",
            ExpectedRaw = "S[L[5, 9], 5, 9]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LFnP("F", [LVar("a")], ".param \"a\"")],
                [LCall("F", ".num 5", ".num 9"), $".sequenceSpread ({LCall("F", ".num 5", ".num 9")})"]),
            IncludeInGeneratorPrompt = true,
            Explanation = "A call returns exactly one value — here the collected list `[5, 9]` — and only the explicit caller-site spread `value*` opens it back into the surrounding item supply.",
        },
        new()
        {
            Id = "property-value-boundary",
            Category = "item-supply-vs-value",
            Source = "Coordinates = 10, 20\nCoordinates\nCoordinates*",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(10, 20)\n10\n20",
            ExpectedRaw = "S[S[10, 20], 10, 20]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("Coordinates", LNums(10, 20))],
                [".resolve \"Coordinates\"", ".sequenceSpread (.resolve \"Coordinates\")"]),
            Explanation = "Property-style access observes a multi-item body as one sequence value; caller-site spread turns it back into separate output rows.",
        },
        new()
        {
            Id = "spread-capture-count",
            Category = "item-supply-vs-value",
            Source = "A = [1, 2, 3]\n\n(A*).count",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("A", "(.listLiteral [.num 1, .num 2, .num 3])")],
                [$".dotCall {LCapture(".sequenceSpread (.resolve \"A\")")} \"count\" none"]),
            Probes =
            [
                new SpecProbe("A = [1, 2, 3]\nA*.count", "err arity"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Parentheses around a supply-producing expression perform CAPTURE — they are not always redundant grouping: `(A*).count` counts one captured sequence value (3), while the fluent `A*.count` is the call `count(A*)` whose three argument slots do not fit the fixed `count(collection)` signature (an arity error).",
        },
        new()
        {
            Id = "repeated-spread-fixed-point",
            Category = "item-supply-vs-value",
            Source = "Collect(*items) = items\nA = [[1, 2], [3, 4]]\n\nCollect(A*)\nCollect(A**)\nCollect((A*)*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[[1, 2], [3, 4]]\n[[1, 2], [3, 4]]\n[[1, 2], [3, 4]]",
            ExpectedRaw = "S[L[L[1, 2], L[3, 4]], L[L[1, 2], L[3, 4]], L[L[1, 2], L[3, 4]]]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LFnP("Collect", [LVar("items")], ".param \"items\""),
                 LProp("A", "(.listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]])")],
                [LCall("Collect", ".sequenceSpread (.resolve \"A\")"),
                 LCall("Collect", ".sequenceSpread (.sequenceSpread (.resolve \"A\"))"),
                 LCall("Collect", $".sequenceSpread {LCapture(".sequenceSpread (.resolve \"A\")")}")]),
            Probes =
            [
                new SpecProbe("Collect(*items) = items\nCollect([[1, 2], 3]*)", "ok raw=L[L[1, 2], 3] n=1"),
                new SpecProbe("Collect(*items) = items\nCollect([[1, 2], 3]**)", "ok raw=L[L[1, 2], 3] n=1"),
                new SpecProbe("A = [[1, 2], [3, 4]]\nA**", "ok raw=S[L[1, 2], L[3, 4]] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Repeated spread is ordinary composition, not recursive flattening: `A**` means `(A*)*`. The first star supplies A's two inner lists; the ordinary expression boundary CAPTURES that two-item supply back into one sequence value; the second star re-spreads the same two items — a fixed point. The inner lists are never opened.",
        },
        new()
        {
            Id = "repeated-spread-singleton-opens",
            Category = "item-supply-vs-value",
            Source = "Collect(*items) = items\n\nCollect([[7]]*)\nCollect([[7]]**)\nCollect([7]*)\nCollect([7]**)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[[7]]\n[7]\n[7]\n[7]",
            ExpectedRaw = "S[L[L[7]], L[7], L[7], L[7]]",
            ExpectedEmittedCount = 4,
            LeanProgram = LProg(
                [LFnP("Collect", [LVar("items")], ".param \"items\"")],
                [LCall("Collect", ".sequenceSpread (.listLiteral [.listLiteral [.num 7]])"),
                 LCall("Collect", ".sequenceSpread (.sequenceSpread (.listLiteral [.listLiteral [.num 7]]))"),
                 LCall("Collect", ".sequenceSpread (.listLiteral [.num 7])"),
                 LCall("Collect", ".sequenceSpread (.sequenceSpread (.listLiteral [.num 7]))")]),
            Probes =
            [
                new SpecProbe("Collect(*items) = items\nCollect([]*)", "ok raw=L[] n=1"),
                new SpecProbe("Collect(*items) = items\nCollect([]**)", "ok raw=L[] n=1"),
                new SpecProbe("Collect(*items) = items\nCollect(5*)", "ok raw=L[5] n=1"),
            ],
            Explanation = "A second star changes the observable supply only when the first spread contributes exactly ONE structured value: singleton capture collapses to that item, so the second star can open its boundary (`[[7]]**` supplies `7`). A scalar singleton is neutral (`[7]**` equals `[7]*` — spread is total), and a zero-item supply stays zero (`[]**` captures `()` in between).",
        },
        new()
        {
            Id = "scalar-spread-neutral",
            Category = "item-supply-vs-value",
            Source = "Collect(*items) = items\n\nCollect(5)\nCollect(5*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[5]\n[5]",
            ExpectedRaw = "S[L[5], L[5]]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LFnP("Collect", [LVar("items")], ".param \"items\"")],
                [LCall("Collect", ".num 5"),
                 LCall("Collect", ".sequenceSpread (.num 5)")]),
            Explanation = "The item view is total: an atom contributes itself as a one-item supply, so spreading an atom is observationally neutral in this collecting context. This is a fact about the item view, not a claim that atoms and collection values are the same kind of value.",
        },
        new()
        {
            Id = "select-spread-vs-capture-select",
            Category = "item-supply-vs-value",
            Source = "A = [[1, 2], [3, 4]]\n\n(A:0)*\n(A*):0",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n[1, 2]",
            ExpectedRaw = "S[1, 2, L[1, 2]]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("A", "(.listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]])")],
                [$".sequenceSpread {LCapture(".index (.resolve \"A\") (.num 0)")}",
                 $".index {LCapture(".sequenceSpread (.resolve \"A\")")} (.num 0)"]),
            Probes =
            [
                new SpecProbe("A = [[1, 2], [3, 4]]\nA:0*", "ok raw=S[1, 2] n=2"),
            ],
            Explanation = "Select-then-spread and capture-then-select are different operations: `(A:0)*` selects the stored list `[1, 2]` and spreads its elements into two rows, while `(A*):0` captures the two-item spread supply as one sequence value and selects its first item — the intact list `[1, 2]`. (`A:0*` is the same select-then-spread: the star attaches to the completed index. `A*:0` is a targeted parse error — selection cannot be applied directly to an item supply.)",
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
                new SpecProbe("Pair = 10, 20\nAdd(x, y) = x + y\nAdd(Pair*)", "ok raw=30 n=1"),
                new SpecProbe("Pair = 10, 20\nAdd(x, y) = x + y\nAdd(Pair:0, Pair:1)", "ok raw=30 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A property reference is one argument expression even when it evaluates to several items: `Add(Pair)` is an arity error. Open it explicitly with `Add(Pair*)` or index with `Add(Pair:0, Pair:1)`.",
        },
        new()
        {
            Id = "spread-fills-remaining-slots",
            Category = "item-supply-vs-value",
            Source = "Tail = 2, 3\nUse(a, b, c) = a + b + c\n\nUse(1, Tail*)",
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
                new SpecProbe("Tail = 2, 3\nUse(a, b, c) = a + b + c\nUse(1*, Tail)", "err arity"),
            ],
            Explanation = "`Tail*` spreads its items into the remaining argument slots; the unspread `Use(1, Tail)` supplies only two argument boundaries, and `Use(1*, Tail)` spreads the scalar `1` (one item) so only two slots are supplied. The comma after a spread is required before another same-line item — `1* Tail` would be the multiplication `1 * Tail`.",
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
            Source = "count(((), ()))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2",
            ExpectedRaw = "2",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("count", LCapture(LEmpty, LEmpty))]),
            Probes =
            [
                new SpecProbe("count((), ())", "err arity"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`count(collection)` takes exactly one collection argument. The grouped `((), ())` collection holds two visible `()` items, so its count is 2; the bare two-argument form `count((), ())` is an ordinary arity error.",
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
            Source = "F(a) = a\nF(()*)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            LeanProgram = LProg([LFn("F", ["a"], ".param \"a\"")], [LCall("F", $".sequenceSpread {LEmpty}")]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Spreading `()` contributes zero items, so `F(()*)` supplies no arguments and the one-parameter call fails.",
        },
        new()
        {
            Id = "variadic-empty-arg-vs-spread",
            Category = "empty-visible-vs-spread",
            Source = "F(*a) = a.count\nF(())",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1",
            ExpectedRaw = "1",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("F", [LVar("a")], ".dotCall (.param \"a\") \"count\" none")],
                [LCall("F", LEmpty)]),
            Probes =
            [
                new SpecProbe("F(*a) = a.count\nF((), ())", "ok raw=2 n=1"),
                new SpecProbe("F(*a) = a.count\nF()", "ok raw=0 n=1"),
                new SpecProbe("F(*a) = a.count\nF(()*)", "ok raw=0 n=1"),
            ],
            Explanation = "A non-spread `()` is one visible argument slot, so the collecting parameter collects `[()]` (count 1); the empty call collects `[]` (count 0), and only spreading `()` contributes zero slots.",
        },
        new()
        {
            Id = "spread-empty-in-sequence",
            Category = "empty-visible-vs-spread",
            Source = "(()*, 99)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "99",
            ExpectedRaw = "99",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCapture($".sequenceSpread {LEmpty}", ".num 99")]),
            Explanation = "Inside a written sequence value, `()*` contributes zero items, leaving one item — and a one-item construction is the item itself, not a wrapper.",
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
            LeanProgram = LProg([], [LCapture(LEmpty, ".num 99")]),
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
            Id = "decon-collecting-tail",
            Category = "deconstruction",
            Source = "x, *rest = 1, 2, 3\nrest",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[2, 3]",
            ExpectedRaw = "L[2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("d", LNums(1, 2, 3)), LDecon("d", [], ["x", "rest"], 1, "rest")],
                [".resolve \"rest\""]),
            Explanation = "The collecting target collects the remaining items as one exact immutable list.",
        },
        new()
        {
            Id = "decon-collecting-head",
            Category = "deconstruction",
            Source = "*head, last = 1, 2, 3\nhead\nlast",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2]\n3",
            ExpectedRaw = "S[L[1, 2], 3]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("d", LNums(1, 2, 3)),
                 LDecon("d", [], ["head", "last"], 0, "head"),
                 LDecon("d", [], ["head", "last"], 0, "last")],
                [".resolve \"head\"", ".resolve \"last\""]),
            Explanation = "The single movable collecting binding may lead: fixed targets after it bind from the back.",
        },
        new()
        {
            Id = "decon-collecting-middle",
            Category = "deconstruction",
            Source = "x, *middle, z = 1, 2, 3, 4\nmiddle",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[2, 3]",
            ExpectedRaw = "L[2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("d", LNums(1, 2, 3, 4)), LDecon("d", [], ["x", "middle", "z"], 1, "middle")],
                [".resolve \"middle\""]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Front and back fixed targets bind first; the middle collecting binding collects its matched segment as one exact immutable list.",
        },
        new()
        {
            Id = "decon-empty-collecting",
            Category = "deconstruction",
            Source = "x, *rest = 1\nrest\nx",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[]\n1",
            ExpectedRaw = "S[L[], 1]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("d", ".num 1"),
                 LDecon("d", [], ["x", "rest"], 1, "rest"),
                 LDecon("d", [], ["x", "rest"], 1, "x")],
                [".resolve \"rest\"", ".resolve \"x\""]),
            Probes =
            [
                new SpecProbe("x, *rest = 1\nrest.count", "ok raw=0 n=1"),
                new SpecProbe("x, *rest = 1\nrest*\nx", "ok raw=1 n=1"),
                new SpecProbe("x, *rest = 1\nrest == []", "ok raw=1 n=1"),
            ],
            Explanation = "A collecting binding that collects zero items binds the exact empty list `[]`, one visible output slot; spreading it contributes zero items.",
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
            Explanation = "Without a collecting target the item count must match exactly: one supplied item cannot bind two targets.",
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
                new SpecProbe("A = 1, 2, 3\nx, y, z = A*\ny", "ok raw=2 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Assignment deconstruction is an unpacking receiver: a single stored sequence value is opened and matched element-by-element, so `= A` and `= A*` bind identically. Function calls do NOT unpack this way — `F(A)` still passes one argument.",
        },
        new()
        {
            Id = "decon-tutorial-full",
            Category = "deconstruction",
            Source = "A = 1, 2, 3, 4, 5\n\nx, *y, z = A\nx\ny\nz",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n[2, 3, 4]\n5",
            ExpectedRaw = "S[1, L[2, 3, 4], 5]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("A", LNums(1, 2, 3, 4, 5)),
                 LProp("d", ".resolve \"A\""),
                 LDecon("d", [], ["x", "y", "z"], 1, "x"),
                 LDecon("d", [], ["x", "y", "z"], 1, "y"),
                 LDecon("d", [], ["x", "y", "z"], 1, "z")],
                [".resolve \"x\"", ".resolve \"y\"", ".resolve \"z\""]),
            Explanation = "Deconstruction with a middle collecting binding over a stored sequence value: fixed targets take the ends, the collecting binding collects the middle as one exact immutable list.",
        },
        new()
        {
            Id = "decon-two-collecting-rejected",
            Category = "deconstruction",
            Source = "*a, *b = 1, 2, 3\na",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "at most one collecting binding",
            Explanation = "A deconstruction pattern allows at most one collecting binding.",
        },
        new()
        {
            Id = "decon-lone-collecting",
            Category = "deconstruction",
            Source = "*all = 1, 2, 3\nall",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3]",
            ExpectedRaw = "L[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("d", LNums(1, 2, 3)), LDecon("d", [], ["all"], 0, "all")],
                [".resolve \"all\""]),
            Probes =
            [
                new SpecProbe("*all = ()\nall", "ok raw=L[] n=1"),
                new SpecProbe("*all = 7\nall", "ok raw=L[7] n=1"),
            ],
            Explanation = "A lone collecting binding is valid and collects the complete supplied item stream as one exact list, including exact empty and singleton lists.",
        },

        // ==================== variadic-calls ====================
        new()
        {
            Id = "variadic-grouped-and-spread",
            Category = "variadic-calls",
            Source = "A = 1, 2, 3, 4, 5\n\nG(*x) = x.sum\n\nG(A*)\nG(1, 2, 3, 4, 5)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "15\n15",
            ExpectedRaw = "S[15, 15]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("A", LNums(1, 2, 3, 4, 5)),
                 LFnP("G", [LVar("x")], ".dotCall (.param \"x\") \"sum\" none")],
                [LCall("G", ".sequenceSpread (.resolve \"A\")"),
                 LCall("G", LNums(1, 2, 3, 4, 5))]),
            Probes =
            [
                new SpecProbe("A = 1, 2, 3, 4, 5\nG(*x) = x.sum\nG(A)", "err arity"),
                new SpecProbe("G(*x) = x.sum\nG((1, 2, 3, 4, 5))", "err arity"),
                new SpecProbe("A = 1, 2, 3, 4, 5\nG(*x) = x.count\nG(A)", "ok raw=1 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A collecting parameter collects the supplied argument slots as one exact list. `G(A*)` and `G(1, 2, 3, 4, 5)` supply five numeric slots (sum 15), while the grouped calls `G(A)` and `G((1, 2, 3, 4, 5))` supply ONE sequence-valued slot — `x = [A]` — so the numeric `sum` element constraint rejects it. Supplying items is always explicit spread.",
        },
        new()
        {
            Id = "variadic-siblings-preserved",
            Category = "variadic-calls",
            Source = "A = 1, 2\nB = 3, 4\n\nG(*x) = x.count\n\nG(A, B)\nG(A*, B*)",
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
            Explanation = "Sibling grouped values are preserved as two items unless each is explicitly opened with a spread marker.",
        },
        new()
        {
            Id = "variadic-capture-collects-list",
            Category = "variadic-calls",
            Source = "F(*x) = x\nF(1, 2, 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3]",
            ExpectedRaw = "L[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("F", [LVar("x")], ".param \"x\"")],
                [LCall("F", LNums(1, 2, 3))]),
            Probes =
            [
                new SpecProbe("F(*x) = x\ncount(F(1, 2, 3))", "ok raw=3 n=1"),
                new SpecProbe("F(*x) = x\nF(1, 2, 3) == [1, 2, 3]", "ok raw=1 n=1"),
                new SpecProbe("F(*x) = x\nF(1, 2, 3) == (1, 2, 3)", "ok raw=0 n=1"),
                new SpecProbe("F(*x) = x\nF()", "ok raw=L[] n=1"),
                new SpecProbe("F(*x) = x\nF(7)", "ok raw=L[7] n=1"),
                new SpecProbe("F(*x) = x\nF(F(1, 2))", "ok raw=L[L[1, 2]] n=1"),
            ],
            Explanation = "Collecting binding COLLECTS the supplied argument slots into one exact immutable list: zero slots form `[]`, one slot forms `[item]` (never erased), many form `[a, b, ...]`. The collected list never equals the sequence value with the same items.",
        },
        new()
        {
            Id = "variadic-forwarding-list-spread",
            Category = "variadic-calls",
            Source = "Target(*items) = items\nForward(*items) = Target(items*)\n\nForward(1, 2)\nForward([1, 2])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2]\n[[1, 2]]",
            ExpectedRaw = "S[L[1, 2], L[L[1, 2]]]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LFnP("Target", [LVar("items")], ".param \"items\""),
                 LFnP("Forward", [LVar("items")],
                     LCall("Target", ".sequenceSpread (.param \"items\")"))],
                [LCall("Forward", ".num 1", ".num 2"),
                 LCall("Forward", "(.listLiteral [.num 1, .num 2])")]),
            Probes =
            [
                new SpecProbe("Target(*items) = items\nForward(*items) = Target(items*)\nForward()", "ok raw=L[] n=1"),
                new SpecProbe("Target(*items) = items\nForward(*items) = Target(items*)\nForward(7)", "ok raw=L[7] n=1"),
                new SpecProbe("Target(*items) = items\nForward(*items) = Target(items*)\nForward([1, 2]*)", "ok raw=L[1, 2] n=1"),
                new SpecProbe("TargetOne(item) = item\nForwardAsOne(*items) = TargetOne(items)\nForwardAsOne(1, 2)", "ok raw=L[1, 2] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Variadic forwarding is ordinary list spread: spreading a collected list re-supplies exactly its items (`Target(items*)` re-collects the caller's slots, including the empty and singleton cases), while passing the collected list without spread passes ONE list argument (`TargetOne(items)` receives `[1, 2]`). There is no hidden raw-supply forwarding.",
        },
        new()
        {
            Id = "implicit-forwarding-source-kind",
            Category = "variadic-calls",
            Source = "Target(*items) = items\nUse(items) = Target\nUseVariadic(*items) = Target\n\nUse([1, 2])\nUse((1, 2))\nUseVariadic(1, 2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[[1, 2]]\n[(1, 2)]\n[1, 2]",
            ExpectedRaw = "S[L[L[1, 2]], L[S[1, 2]], L[1, 2]]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LFnP("Target", [LVar("items")], ".param \"items\""),
                 LFn("Use", ["items"], LCall("Target", ".param \"items\"")),
                 LFnP("UseVariadic", [LVar("items")],
                     LCall("Target", ".sequenceSpread (.param \"items\")"))],
                [LCall("Use", "(.listLiteral [.num 1, .num 2])"),
                 LCall("Use", LCapture(LNums(1, 2))),
                 LCall("UseVariadic", ".num 1", ".num 2")]),
            Probes =
            [
                new SpecProbe("Target(*items) = items\nUse(items) = Target\nUse(7)", "ok raw=L[7] n=1"),
                new SpecProbe("Target(*items) = items\nUse(items) = Target(items)\nUse([1, 2])", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("Target(*items) = items\nUseVariadic(*items) = Target\nUseVariadic([1, 2])", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("Target(first, *middle, last) = middle\nUse(first, *middle, last) = Target\nUse(1, 2, 3, 4)", "ok raw=L[2, 3] n=1"),
                new SpecProbe("Target(*a) = a\nUse((a, b)) = Target\nUse(([1, 2], 5))", "ok raw=L[L[1, 2]] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Implicit forwarding decides spread from the SOURCE binding kind, never from the destination parameter kind: an ordinary caller parameter is passed as ONE argument even into a collecting destination (`Use(items) = Target` elaborates to `Target(items)`, so the list stays one collected slot), while a caller collecting parameter legitimately forwards as spread (`UseVariadic(*items) = Target` elaborates to `Target(items*)`).",
        },
        new()
        {
            Id = "variadic-receiver-distinction",
            Category = "variadic-calls",
            Source = "Inspect(*items) = items\nA = [1, 2, 3]\n\nInspect(A)\nInspect(A*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[[1, 2, 3]]\n[1, 2, 3]",
            ExpectedRaw = "S[L[L[1, 2, 3]], L[1, 2, 3]]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LFnP("Inspect", [LVar("items")], ".param \"items\""),
                 LProp("A", "(.listLiteral [.num 1, .num 2, .num 3])")],
                [LCall("Inspect", ".resolve \"A\""),
                 LCall("Inspect", ".sequenceSpread (.resolve \"A\")")]),
            Probes =
            [
                new SpecProbe("Inspect(*items) = items\nB = (1, 2, 3)\nInspect(B)", "ok raw=L[S[1, 2, 3]] n=1"),
                new SpecProbe("Inspect(*items) = items\nB = (1, 2, 3)\nInspect(B*)", "ok raw=L[1, 2, 3] n=1"),
                new SpecProbe("Inspect(*items) = items\nA = [1, 2]\nA.Inspect", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("CountArgs(*items) = items.count\nCountArgs([10, 20])", "ok raw=1 n=1"),
                new SpecProbe("CountArgs(*items) = items.count\nCountArgs([10, 20]*)", "ok raw=2 n=1"),
                new SpecProbe("CountArgs(*items) = items.count\nCountArgs((10, 20))", "ok raw=1 n=1"),
                new SpecProbe("CountArgs(*items) = items.count\nCountArgs((10, 20)*)", "ok raw=2 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "An unspread structure is one argument slot — `Inspect(A)` collects `[A]` (count 1) for lists and sequence values alike, and a NAMED dotted receiver `A.Inspect` supplies the same one item (a stored property receiver's segment supply is its value-boundary count) — while explicit spread supplies the immediate items (`Inspect(A*)` collects `[1, 2, 3]`, count 3). A WRITTEN group receiver is different: see `dot-receiver-segment-supply`.",
        },
        new()
        {
            Id = "dot-receiver-segment-supply",
            Category = "variadic-calls",
            Source = "Mean(*Vector) = Vector.sum / Vector.count\n\nMean(1, 2, 3)\n(1, 2, 3).Mean",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2\n2",
            ExpectedRaw = "S[2, 2]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LFnP("Mean", [LVar("Vector")],
                    ".binary .div (.dotCall (.param \"Vector\") \"sum\" none) (.dotCall (.param \"Vector\") \"count\" none)")],
                [LCall("Mean", LNums(1, 2, 3)),
                 ".dotCall (.capture [.num 1, .num 2, .num 3]) \"Mean\" none"]),
            Probes =
            [
                new SpecProbe("Mean(*Vector) = Vector.sum / Vector.count\nMean(1, 2, 2.718)", "ok raw=1.906 n=1"),
                new SpecProbe("Mean(*Vector) = Vector.sum / Vector.count\n(1, 2, 2.718).Mean", "ok raw=1.906 n=1"),
                new SpecProbe("Collect(*items) = items\n(1, 2).Collect", "ok raw=L[1, 2] n=1"),
                new SpecProbe("Collect(*items) = items\n((1, 2)).Collect", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("Collect(*items) = items\n().Collect", "ok raw=L[] n=1"),
                new SpecProbe("Collect(*items) = items\n[1, 2].Collect", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("Scale(*values, factor) = values, factor\n(1, 2, 3).Scale(10)", "ok raw=S[L[1, 2, 3], 10] n=1"),
                new SpecProbe("F(first, *middle, last) = first\n(1, 2).F", "err arity"),
                new SpecProbe("F(*middle, last) = middle, last\n(1, 2).F", "ok raw=S[L[], S[1, 2]] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A lexical dot-call receiver is ONE leading segment for arity checking and fixed prefix/suffix allocation — its item count never satisfies arity, and a fixed parameter binds the receiver as one value. A flat top-level collecting parameter that is allocated the segment consumes the segment's evaluated top-level supply: a WRITTEN group receiver supplies its raw rows (`(1, 2, 3).Mean` averages the three items; `((1, 2)).Collect` keeps the extra written boundary; `().Collect` supplies zero items), while exact lists stay opaque. Direct calls are unchanged: `Mean((1, 2, 3))` still collects one grouped argument.",
        },
        new()
        {
            Id = "mixed-collecting-parameter",
            Category = "variadic-calls",
            Source = "F(x, *y, z) = x + y.sum + z\nF(1, 2, 3, 4, 5)",
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
                new SpecProbe("F(x, *y, z) = x + y.sum + z\nF(1, 2)", "ok raw=3 n=1"),
                new SpecProbe("F(x, *y, z) = x + y.sum + z\nA = 1, 2, 3, 4, 5\nF(A)", "err arity"),
                new SpecProbe("F(x, *y, z) = y\nF(1, 2, 3, 4, 5)", "ok raw=L[2, 3, 4] n=1"),
                new SpecProbe("F(x, *y, z) = y\nF(1, 2)", "ok raw=L[] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Mixed fixed/collecting parameter lists bind the call's argument stream: fixed captures take the front and back, and the collecting parameter collects the middle as one exact immutable list (possibly `[]`). A plain call does not implicitly open a single sequence argument, so `F(A)` fails.",
        },
        new()
        {
            Id = "mixed-front-back-family",
            Category = "variadic-calls",
            Source = "Arg = 1, 2, 3\n\nHead(first, *rest) = first\nTail(first, *rest) = rest\nInit(*init, last) = init\nLast(*init, last) = last\n\nHead(1, (2, 3))\nTail(1, (2, 3))\nInit((1, 2), 3)\nLast(Arg, 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n[(2, 3)]\n[(1, 2)]\n3",
            ExpectedRaw = "S[1, L[S[2, 3]], L[S[1, 2]], 3]",
            ExpectedEmittedCount = 4,
            LeanProgram = LProg(
                [LProp("Arg", LNums(1, 2, 3)),
                 LFnP("Head", [LFix("first"), LVar("rest")], ".param \"first\""),
                 LFnP("Tail", [LFix("first"), LVar("rest")], ".param \"rest\""),
                 LFnP("Init", [LVar("init"), LFix("last")], ".param \"init\""),
                 LFnP("Last", [LVar("init"), LFix("last")], ".param \"last\"")],
                [LCall("Head", ".num 1", LCapture(LNums(2, 3))),
                 LCall("Tail", ".num 1", LCapture(LNums(2, 3))),
                 LCall("Init", LCapture(LNums(1, 2)), ".num 3"),
                 LCall("Last", ".resolve \"Arg\"", ".num 3")]),
            Explanation = "Grouped arguments are single slots: a collected segment of one grouped value is the one-element list holding it (never the value itself), and fixed captures bind whole argument boundaries.",
        },
        new()
        {
            Id = "collecting-minimum-arity",
            Category = "variadic-calls",
            Source = "F(first, *middle, last) = middle\n\nF(1, 2)\nF(1, 2, 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[]\n[2]",
            ExpectedRaw = "S[L[], L[2]]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LFnP("F", [LFix("first"), LVar("middle"), LFix("last")], ".param \"middle\"")],
                [LCall("F", ".num 1", ".num 2"),
                 LCall("F", LNums(1, 2, 3))]),
            Probes =
            [
                new SpecProbe("F(first, *middle, last) = middle\nF(1)", "err arity"),
            ],
            Explanation = "The fixed bindings set a minimum: `F(first, *middle, last)` requires at least two supplied items because `first` and `last` each bind one, while the movable collecting parameter collects the (possibly empty) middle as an exact list. `F(1)` reports the targeted minimum-arity error.",
        },
        new()
        {
            Id = "variadic-grouped-vs-spread",
            Category = "variadic-calls",
            Source = "H(h, *t) = t\nH((1, 2))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[]",
            ExpectedRaw = "L[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("H", [LFix("h"), LVar("t")], ".param \"t\"")],
                [LCall("H", LCapture(LNums(1, 2)))]),
            Probes =
            [
                new SpecProbe("H(h, *t) = t\nH((1, 2)*)", "ok raw=L[2] n=1"),
            ],
            Explanation = "Mixed shapes make the supply boundary observable: `H((1, 2))` binds `h` to the whole pair leaving the empty collected list `[]`, while `H((1, 2)*)` spreads the pair first so `h = 1` and `t` collects `[2]`.",
        },
        new()
        {
            Id = "variadic-nested-not-flattened",
            Category = "variadic-calls",
            Source = "Arg = (1, 2), (3, 4)\n\nMany(*values) = values.count\nFlattened = atoms(Arg).count\n\nMany(Arg*)\nFlattened",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2\n4",
            ExpectedRaw = "S[2, 4]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("Arg", $"{LCapture(LNums(1, 2))}, {LCapture(LNums(3, 4))}"),
                 LFnP("Many", [LVar("values")], ".dotCall (.param \"values\") \"count\" none"),
                 LProp("Flattened", $".dotCall ({LCall("atoms", ".resolve \"Arg\"")}) \"count\" none")],
                [LCall("Many", ".sequenceSpread (.resolve \"Arg\")"), ".resolve \"Flattened\""]),
            Probes =
            [
                new SpecProbe("Arg = (1, 2), (3, 4)\nMany(*values) = values.count\nMany(Arg)", "ok raw=1 n=1"),
            ],
            Explanation = "Segment collection is not recursive flattening: `Many(Arg*)` supplies the two nested pairs as two collected elements, the unspread `Many(Arg)` is one collected element, and `atoms` is the explicit recursive projection.",
        },
        new()
        {
            Id = "supply-vs-value-patterns",
            Category = "variadic-calls",
            Source = "CountValues(*values) = values.count\nCountSequenceValue((*values)) = values.count\n\nCountValues()\nCountValues(1, 2, 3)\nCountValues((1, 2, 3))\nCountSequenceValue((1, 2, 3))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0\n3\n1\n3",
            ExpectedRaw = "S[0, 3, 1, 3]",
            ExpectedEmittedCount = 4,
            LeanProgram = LProg(
                [LFnP("CountValues", [LVar("values")], ".dotCall (.param \"values\") \"count\" none"),
                 LFnPat("CountSequenceValue", [".sequenceValue [.capture { name := \"values\", kind := .collecting }]"],
                     ".dotCall (.param \"values\") \"count\" none")],
                [".call (.resolve \"CountValues\") []",
                 LCall("CountValues", LNums(1, 2, 3)),
                 LCall("CountValues", LCapture(LNums(1, 2, 3))),
                 LCall("CountSequenceValue", LCapture(LNums(1, 2, 3)))]),
            Explanation = "Top-level `*values` collects the call's argument slots — a grouped `(1, 2, 3)` is ONE collected element — while the sequence-value pattern `(*values)` consumes exactly one grouped argument and opens it during binding, collecting its three items.",
        },
        new()
        {
            Id = "redundant-call-parens-canonical",
            Category = "variadic-calls",
            Source = "Inner = (1, 2, 3)\nCountSequenceValue((*values)) = values.count\nNestedCount(((*values))) = values.count\n\nCountSequenceValue(Inner)\nCountSequenceValue((Inner))\nCountSequenceValue(((1, 2, 3)))\nNestedCount(((1, 2, 3)))\nNestedCount((((1, 2, 3))))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3\n1\n1\n3\n3",
            ExpectedRaw = "S[3, 1, 1, 3, 3]",
            ExpectedEmittedCount = 5,
            LeanProgram = LProg(
                [LProp("Inner", LCapture(LNums(1, 2, 3))),
                 LFnPat("CountSequenceValue", [".sequenceValue [.capture { name := \"values\", kind := .collecting }]"],
                     ".dotCall (.param \"values\") \"count\" none"),
                 LFnPat("NestedCount", [".sequenceValue [.sequenceValue [.capture { name := \"values\", kind := .collecting }]]"],
                     ".dotCall (.param \"values\") \"count\" none")],
                [LCall("CountSequenceValue", ".resolve \"Inner\""),
                 LCall("CountSequenceValue", LCapture(".resolve \"Inner\"")),
                 LCall("CountSequenceValue", LCapture(LCapture(LNums(1, 2, 3)))),
                 LCall("NestedCount", LCapture(LCapture(LNums(1, 2, 3)))),
                 LCall("NestedCount", LCapture(LCapture(LCapture(LNums(1, 2, 3)))))]),
            Probes =
            [
                new SpecProbe("NestedCount(((*values))) = values.count\nNestedCount((1, 2, 3))", "err arity"),
                new SpecProbe("CountSequenceValue((*values)) = values.count\nCountSequenceValue(((1, 2), 3))", "ok raw=2 n=1"),
            ],
            Explanation = "A pattern-shaped callee consumes written grouping levels: a bare reference opens to its three items, while ONE extra written level around the argument leaves a single grouped item, which the collecting parameter collects exactly (`[Inner]`, count 1). Levels beyond the first stay redundant (unary sequence structure canonicalizes during value construction), and the declared nested pattern depth consumes matching written depth.",
        },
        new()
        {
            Id = "call-spread-into-conditional-clauses",
            Category = "variadic-calls",
            Source = "F(0, 0) = 100\nF(x, y) = x + y\nA = (1, 2)\nF(A*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                ["privateProp \"F\" (.conditional none [] [" +
                     "⟨.sequenceValue [.litInt 0, .litInt 0], alg [] [] [] [.num 100]⟩, " +
                     "⟨.sequenceValue [.bind \"x\", .bind \"y\"], alg [] [] [] [.binary .add (.param \"x\") (.param \"y\")]⟩])",
                 LProp("A", LCapture(LNums(1, 2)))],
                [LCall("F", ".sequenceSpread (.resolve \"A\")")]),
            Probes =
            [
                new SpecProbe("F(0, 0) = 100\nF(x, y) = x + y\nA = (1, 2)\nF(A)", "err branch"),
            ],
            Explanation = "Explicit call-site spread has identical meaning for every callable shape: `F(A*)` supplies A's spread items as ordinary argument slots BEFORE clause selection, so the two-binder clause binds x = 1, y = 2. The unspread `F(A)` supplies ONE closed argument, which no two-argument clause can match.",
            IncludeInGeneratorPrompt = true,
        },
        new()
        {
            Id = "patterned-user-call-is-one-value-boundary",
            Category = "item-supply-vs-value",
            Source = "F((x)) = 1, 2\nF((7))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2)",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnPat("F", [".sequenceValue [.capture { name := \"x\" }]"], LNums(1, 2))],
                [LCall("F", ".num 7")]),
            Probes =
            [
                new SpecProbe("F((x)) = x, x\nF((7))", "ok raw=S[7, 7] n=1"),
                new SpecProbe("F((x, y)) = x, y\nF((1, 2))", "ok raw=S[1, 2] n=1"),
                // The flat-parameter spelling must reach the same boundary.
                new SpecProbe("F(x) = 1, 2\nF(7)", "ok raw=S[1, 2] n=1"),
            ],
            Explanation = "A user call is a VALUE boundary on every callee shape, including a sequence-value-patterned one: the body's multi-slot output is combined into one value and the emitted count is re-counted to that value's own count (1). Body/root output accumulation is not a value boundary, so without the re-count the call would leak its body's two-slot supply into the caller and emit two rows instead of one.",
        },
        new()
        {
            Id = "conditional-singleton-head-binds-its-argument-whole",
            Category = "conditionals",
            Source = "F((x)) = x\nF(n) = 0\nF([1, 2])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2]",
            ExpectedRaw = "L[1, 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                ["privateProp \"F\" (.conditional none [] [" +
                     "⟨.sequenceValue [.sequenceValue [.bind \"x\"]], (alg [] [] [] [.param \"x\"])⟩, " +
                     "⟨.bind \"n\", (alg [] [] [] [.num 0])⟩])"],
                ["(.call (.resolve \"F\") [(.listLiteral [.num 1, .num 2])])"]),
            Probes =
            [
                // A SINGLETON list is not opened either: `x` binds `[7]`, not 7.
                new SpecProbe("F((x)) = x\nF(n) = 0\nF([7])", "ok raw=L[7] n=1"),
                // Control: a two-item SEQUENCE value has arity 2 against a
                // one-element pattern, so it falls through to the next clause.
                new SpecProbe("F((x)) = x\nF(n) = 0\nF((1, 2))", "ok raw=0 n=1"),
                new SpecProbe("F((x)) = x\nF(n) = 0\nF(7)", "ok raw=7 n=1"),
            ],
            Explanation = "A singleton sequence-value clause head `(x)` matches ANY one argument whole via the scalar one-item rule: singleton sequence structure canonicalizes away during construction, so the pattern must also accept a non-sequence result as if it were a one-element sequence. It never opens the argument — an exact list binds entire, including a singleton list. Only a sequence value of a different arity fails the head.",
        },
        new()
        {
            Id = "conditional-clause-head-rejects-extra-arguments",
            Category = "conditionals",
            Source = "F(0) = 1\nF(n) = 2\nF(1, 2)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "branch",
            LeanProgram = LProg(
                ["privateProp \"F\" (.conditional none [] [" +
                     "⟨.litInt 0, (alg [] [] [] [.num 1])⟩, " +
                     "⟨.bind \"n\", (alg [] [] [] [.num 2])⟩])"],
                ["(.call (.resolve \"F\") [.num 1, .num 2])"]),
            Probes =
            [
                // A literal head must not match on the first argument alone.
                new SpecProbe("F(0) = 1\nF(n) = 2\nF(0, 9)", "err branch"),
                new SpecProbe("F(0) = 1\nF(n) = 2\nF()", "err branch"),
                new SpecProbe("F(0) = 1\nF(n) = 2\nF(1)", "ok raw=2 n=1"),
            ],
            Explanation = "A non-sequence clause head consumes exactly ONE explicit argument slot. Surplus arguments are never dropped: no clause of a one-argument family matches a two-argument call, so the family reports no matching branch rather than silently binding the first argument and discarding the rest.",
        },
        new()
        {
            Id = "call-spread-dispatches-before-clause-selection",
            Category = "variadic-calls",
            Source = "F(0, 0) = 100\nF(x, y) = x + y\nA = (0, 0)\nF(A*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "100",
            ExpectedRaw = "100",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                ["privateProp \"F\" (.conditional none [] [" +
                     "⟨.sequenceValue [.litInt 0, .litInt 0], alg [] [] [] [.num 100]⟩, " +
                     "⟨.sequenceValue [.bind \"x\", .bind \"y\"], alg [] [] [] [.binary .add (.param \"x\") (.param \"y\")]⟩])",
                 LProp("A", LCapture(LNums(0, 0)))],
                [LCall("F", ".sequenceSpread (.resolve \"A\")")]),
            Explanation = "Clause selection happens strictly AFTER spread expansion: `F(A*)` with A = (0, 0) supplies the two literal-matching slots, so the literal clause wins. A catch-all clause can never absorb a spread argument as one closed value.",
        },
        new()
        {
            Id = "call-spread-into-patterned-callee",
            Category = "variadic-calls",
            Source = "F(x, x) = x + 1\nA = (7, 7)\nF(A*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8",
            ExpectedRaw = "8",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("F", [LFix("x"), LFix("x")], ".binary .add (.param \"x\") (.num 1)"),
                 LProp("A", LCapture(LNums(7, 7)))],
                [LCall("F", ".sequenceSpread (.resolve \"A\")")]),
            Probes =
            [
                new SpecProbe("F(x, x) = x + 1\nA = (7, 7)\nF(A)", "err arity"),
                new SpecProbe("F(x, x) = x + 1\nA = (7, 8)\nF(A*)", "err arity"),
            ],
            Explanation = "The repeated-name (patterned) callee shape does not change caller-side spread: `F(A*)` supplies two argument slots that must satisfy the repeated-bind equality, exactly like the flat callee `G(x, y)` would receive them. The unspread `F(A)` is one argument against two parameters.",
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
            LeanProgram = LProg([], [LCapture(LCapture(LNums(1, 2)))]),
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
            LeanProgram = LProg([], [LCapture(LCapture(LNums(1, 2)), LEmpty)]),
            Explanation = "A written `()` item inside a sequence value stays visible.",
        },
        new()
        {
            Id = "spread-splices-into-sequence",
            Category = "sequence-construction",
            Source = "x = (1, 2)\n(x*, 99)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 99)",
            ExpectedRaw = "S[1, 2, 99]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("x", LCapture(LNums(1, 2)))],
                [LCapture(".sequenceSpread (.resolve \"x\")", ".num 99")]),
            Explanation = "Spread inside a written sequence value splices exactly one layer of items beside the sibling slots.",
        },
        new()
        {
            Id = "spread-empty-between-siblings",
            Category = "sequence-construction",
            Source = "(1*, (), 2*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, (), 2)",
            ExpectedRaw = "S[1, S[], 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCapture(".sequenceSpread (.num 1)", LEmpty, ".sequenceSpread (.num 2)")]),
            Explanation = "Spreading a scalar contributes the scalar itself; the written `()` slot between the spreads stays a visible item.",
        },
        new()
        {
            Id = "root-spread-beside-slot",
            Category = "sequence-construction",
            Source = "A = (1, 2)\nA*, 99",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n99",
            ExpectedRaw = "S[1, 2, 99]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("A", LCapture(LNums(1, 2)))],
                [".sequenceSpread (.resolve \"A\")", ".num 99"]),
            Explanation = "At root output a spread slot contributes its spread items as rows beside the other slots.",
        },
        new()
        {
            Id = "root-spread-then-value-slot",
            Category = "sequence-construction",
            Source = "First = 1, 2\nSecond = 3, 4\n\nFirst*, Second",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n(3, 4)",
            ExpectedRaw = "S[1, 2, S[3, 4]]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("First", LNums(1, 2)), LProp("Second", LNums(3, 4))],
                [".sequenceSpread (.resolve \"First\")", ".resolve \"Second\""]),
            Explanation = "A comma is required after a spread expression when another supplied item follows on the same line, because `First* Second` is the multiplication `First * Second`. `First*, Second` spreads `First` into two rows and `Second` stays one sequence-valued row.",
        },
        new()
        {
            Id = "spread-slots-capture",
            Category = "sequence-construction",
            Source = "A = 1, 2\nB = 1*, 2\n\nA.count\nB.count",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2\n2",
            ExpectedRaw = "S[2, 2]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("A", LNums(1, 2)),
                 LProp("B", ".sequenceSpread (.num 1), .num 2")],
                [".dotCall (.resolve \"A\") \"count\" none", ".dotCall (.resolve \"B\") \"count\" none"]),
            Explanation = "`B = 1*, 2` is a two-slot body: the spread of the scalar `1` supplies one item and `2` is a separate slot, so `B` captures the same two items as `A = 1, 2`. Without the comma, `1* 2` is the multiplication `1 * 2`.",
        },
        new()
        {
            Id = "spread-one-level-only",
            Category = "sequence-construction",
            Source = "(1, (2, 3))*, 4",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n(2, 3)\n4",
            ExpectedRaw = "S[1, S[2, 3], 4]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg([], [$".sequenceSpread {LCapture(".num 1", LCapture(LNums(2, 3)))}", ".num 4"]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Spread opens exactly one level: the inner `(2, 3)` stays intact, and `4` is a separate expression-list slot (the comma after the spread is required — `(1, (2, 3))* 4` would be multiplication).",
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
            Id = "zero-param-block-higher-order",
            Category = "access-boundaries",
            Source = "Call0 = f()\nCall0({42})",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "42",
            ExpectedRaw = "42",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("Call0", ["f"], ".call (.param \"f\") []")],
                [LCall("Call0", ".algorithmExpr (alg [] [] [] [.num 42])")]),
            Probes =
            [
                new SpecProbe("Const = 42\nCall0 = f()\nCall0(Const)", "ok raw=42 n=1"),
                new SpecProbe("Call0 = f()\nCall0(({42}))", "ok raw=42 n=1"),
                new SpecProbe("Call0 = f()\nCall0({1, 2})", "ok raw=S[1, 2] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "An algorithm block always provides its contained algorithm on the higher-order channel, regardless of parameter or output count: `Call0({42})` invokes the brace algorithm exactly like the named zero-parameter `Call0(Const)`, redundant parentheses around braces normalize away, and a multi-output block's call emits its outputs as one captured sequence value.",
        },
        new()
        {
            Id = "dot-member-higher-order-parameter",
            Category = "access-boundaries",
            Source = "K(a, t) = t(a)\nD(a, t) = a.t\n\nK(7, {a+1})\nD(7, {a+1})",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8\n8",
            ExpectedRaw = "S[8, 8]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LFn("K", ["a", "t"], ".call (.param \"t\") [.param \"a\"]"),
                 LFn("D", ["a", "t"], ".dotMember (.param \"a\") \"t\" (.param \"t\") .ordinary none")],
                [LCall("K", ".num 7", ".algorithmExpr (alg [\"a\"] [] [] [.binary .add (.param \"a\") (.num 1)])"),
                 LCall("D", ".num 7", ".algorithmExpr (alg [\"a\"] [] [] [.binary .add (.param \"a\") (.num 1)])")]),
            Probes =
            [
                new SpecProbe("t = 5\nK(a, t) = a.t\nK(7, {a+1})", "ok raw=8 n=1"),
                new SpecProbe("t = 5\nG(x) = x.t\nK(a, t) = G(a)\nK(7, {a+1})", "err arity"),
                new SpecProbe("Obj = {public V = 42}\nK(a, V) = a.V\nK(Obj, {a+1})", "ok raw=42 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "After structural member lookup fails, a dot member name that is a parameter of the calling context resolves exactly like the plain callee: `a.t` and `t(a)` agree, including algorithm-valued parameters. A parameter of the current algorithm wins over a same-name visible property, a captured ancestor parameter yields to a visible non-builtin declaration, and structural members of the resolved receiver always take precedence first.",
        },
        new()
        {
            Id = "extension-dot-higher-order-implicit",
            Category = "access-boundaries",
            Source = "K = a~.t\nK(7, {a+1})",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8",
            ExpectedRaw = "8",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("K", ["a", "t"], ".dotMember (.param \"a\") \"t\" (.param \"t\") .extensionOnly none")],
                [LCall("K", ".num 7", ".algorithmExpr (alg [\"a\"] [] [] [.binary .add (.param \"a\") (.num 1)])")]),
            Probes =
            [
                new SpecProbe("K = a.~t\nK(7, {a+1})", "ok raw=8 n=1"),
                new SpecProbe("K(a, t) = a~.t\nK(7, {a+1})", "ok raw=8 n=1"),
                new SpecProbe("K(a, t) = a.~t\nK(7, {a+1})", "ok raw=8 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`~.` (equivalently `.~`) selects extension-call resolution: the member is a callable-name occurrence that participates in ordinary parameter/name resolution, so `K = a~.t` infers the parameters `(a, t)` exactly like `K = t(a)` and calls the bound algorithm with the receiver injected first. Ordinary `.` never infers member names as parameters.",
        },
        new()
        {
            Id = "extension-dot-bypasses-structural-member",
            Category = "access-boundaries",
            Source = "V(x) = 99\nObj = {\n    public V = 42\n    0\n}\n\nObj.V\nObj~.V",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "42\n99",
            ExpectedRaw = "S[42, 99]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LFn("V", ["x"], ".num 99"),
                 "privateProp \"Obj\" (alg [] [] [publicProp \"V\" (alg [] [] [] [.num 42])] [.num 0])"],
                [".dotCall (.resolve \"Obj\") \"V\" none",
                 ".dotMember (.resolve \"Obj\") \"V\" (.resolve \"V\") .extensionOnly none"]),
            Probes =
            [
                new SpecProbe("V(x) = 99\nObj = {\n    public V = 42\n    0\n}\nObj.~V", "ok raw=99 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Ordinary `.` performs structural member lookup first, so `Obj.V` reads Obj's own property even when a lexical `V` exists; `Obj~.V` (equivalently `Obj.~V`) explicitly selects extension-call resolution, bypasses structural lookup, and calls the lexical `V` with `Obj` as the injected first argument.",
        },
        new()
        {
            Id = "ordinary-dot-member-is-not-implicit-param",
            Category = "access-boundaries",
            Source = "K(x) = x.V\nObj = {public V = 42}\n\nK(Obj)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "42",
            ExpectedRaw = "42",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("K", ["x"], ".dotCall (.param \"x\") \"V\" none"),
                 "privateProp \"Obj\" (alg [] [] [publicProp \"V\" (alg [] [] [] [.num 42])] [])"],
                [LCall("K", ".resolve \"Obj\"")]),
            Explanation = "An ordinary dot member is never inferred as an implicit parameter merely because a lexical fallback path exists: `K(x) = x.V` keeps arity 1, and `V` resolves structurally on the runtime receiver. Use the extension marker (`x~.V`) when the member is meant as a callable-name occurrence.",
        },
        new()
        {
            Id = "open-capture-target-rejected",
            Category = "access-boundaries",
            Source = "M = {\n    public C = 5\n}\nR = {\n    open (M)\n    C\n}\nR",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "a parenthesized group is a captured value, not an algorithm",
            Probes =
            [
                new SpecProbe("M = {\n    public C = 5\n}\nR = {\n    open M\n    C\n}\nR", "ok raw=5 n=1"),
                new SpecProbe("R = {\n    open ({public C = 6})\n    C\n}\nR", "ok raw=6 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`open` consumes algorithm identity, and a capture is a value boundary that never exposes the identity of what it encloses: `open (M)` is rejected at parse time. Open the algorithm directly (`open M`), or use a brace block — parentheses around a brace block normalize away, so `open ({ ... })` still opens the block.",
        },
        new()
        {
            Id = "capture-suppresses-higher-order-identity",
            Category = "access-boundaries",
            Source = "Apply = f(9)\nIncrement(x) = x + 1\nApply((Increment))",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            LeanProgram = LProg(
                [LFn("Apply", ["f"], ".call (.param \"f\") [.num 9]"),
                 LFn("Increment", ["x"], ".binary .add (.param \"x\") (.num 1)")],
                [LCall("Apply", LCapture(".resolve \"Increment\""))]),
            Probes =
            [
                new SpecProbe("Apply = f(9)\nIncrement(x) = x + 1\nApply(Increment)", "ok raw=10 n=1"),
                new SpecProbe("Apply = f(9)\nIncrement(x) = x + 1\nApply(((Increment)))", "err arity"),
            ],
            Explanation = "A capture supplies only a zero-parameter value thunk on the algorithm channel. Grouping a named callable therefore suppresses its callable identity instead of forwarding it to the higher-order parameter.",
        },
        new()
        {
            Id = "capture-suppresses-structural-members",
            Category = "access-boundaries",
            Source = "Obj = {public V = 7}\n(Obj).V",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "unknownName",
            LeanProgram = LProg(
                ["privateProp \"Obj\" (alg [] [] [publicProp \"V\" (alg [] [] [] [.num 7])] [])"],
                [$".dotCall {LCapture(".resolve \"Obj\"")} \"V\" none"]),
            Probes =
            [
                new SpecProbe("Obj = {public V = 7}\nObj.V", "ok raw=7 n=1"),
                new SpecProbe("F2(x, y) = x + y\nX = 3\n(X).F2(4)", "ok raw=7 n=1"),
            ],
            Explanation = "A capture receiver has no structural members. Dot access therefore falls back lexically and injects the captured receiver as the leading argument; without a lexical member name, lookup fails.",
        },
        new()
        {
            Id = "output-dotted-access-ordinary",
            Category = "access-boundaries",
            Source = "A = {\n    Output = 9\n}\n\nA.Output",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "9",
            ExpectedRaw = "9",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                ["privateProp \"A\" (alg [] [] [privateProp \"Output\" (alg [] [] [] [.num 9])] [])"],
                [".dotCall (.resolve \"A\") \"Output\" none"]),
            Explanation = "A property named `Output` follows ordinary dotted property access rules — there is no reserved output member.",
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
                [".call (.resolve \"P\") []"]),
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
            ExpectedDisplay = "[1, 2]",
            ExpectedRaw = "L[1, 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("x", LCall("take", LCapture(LNums(1, 2, 3)), ".num 2"))],
                [".resolve \"x\""]),
            Probes =
            [
                new SpecProbe("I(a) = a\nI(take((1, 2, 3), 2))", "ok raw=L[1, 2] n=1"),
                new SpecProbe("G(*a) = a\nG(take((1, 2, 3), 2))", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("G(*a) = a\nG(take((1, 2, 3), 2)*)", "ok raw=L[1, 2] n=1"),
                new SpecProbe("take((1, 2, 3), 2) == (1, 2)", "ok raw=0 n=1"),
                new SpecProbe("take((1, 2, 3), 2) == [1, 2]", "ok raw=1 n=1"),
                new SpecProbe("count(take((1, 2, 3), 2))", "ok raw=2 n=1"),
            ],
            Explanation = "A collection builtin's exact list result re-enters receivers by the ordinary rules: capture and fixed parameters observe the same list value, a collecting binding collects it as one element (`[[1, 2]]`) unless the caller spreads it, count opens its one list boundary, and the list never equals a sequence value.",
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
                [".resolve \"Add\"", LCapture(LNums(1, 2))]),
            Explanation = "A physical newline never continues a closed expression into a call: `Add` alone is a zero-argument access of a two-parameter callable (an arity error), and `(1, 2)` is a separate row.",
        },

        // ==================== collection-builtins ====================
        new()
        {
            Id = "take-prefix",
            Category = "collection-builtins",
            Source = "take((1, 2, 3, 4, 5), 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3]",
            ExpectedRaw = "L[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("take", LCapture(LNums(1, 2, 3, 4, 5)), ".num 3")]),
            Explanation = "`take` keeps the first `count` items and materializes them as one exact immutable list value.",
        },
        new()
        {
            Id = "take-single-survivor",
            Category = "collection-builtins",
            Source = "take(((1, 2), (3, 4)), 1)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[(1, 2)]",
            ExpectedRaw = "L[S[1, 2]]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("take", PairOfPairs, ".num 1")]),
            Probes =
            [
                new SpecProbe("count(take(((1, 2), (3, 4)), 1))", "ok raw=1 n=1"),
                new SpecProbe("take(((1, 2), (3, 4)), 1) == (1, 2)", "ok raw=0 n=1"),
                new SpecProbe("take(((1, 2), (3, 4)), 1)*", "ok raw=S[1, 2] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Collection builtins materialize exact lists: one kept item forms the one-element list `[(1, 2)]` (never erased to the item), so its count is 1 and an explicit `value*` re-spreads the list to the kept pair.",
        },
        new()
        {
            Id = "take-zero-empty",
            Category = "collection-builtins",
            Source = "take((1, 2, 3), 0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[]",
            ExpectedRaw = "L[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("take", LCapture(LNums(1, 2, 3)), ".num 0")]),
            Explanation = "Zero kept items form the empty list `[]` — one visible value, distinct from the empty sequence value `()`.",
        },
        new()
        {
            Id = "skip-prefix",
            Category = "collection-builtins",
            Source = "skip((1, 2, 3, 4, 5), 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[4, 5]",
            ExpectedRaw = "L[4, 5]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("skip", LCapture(LNums(1, 2, 3, 4, 5)), ".num 3")]),
            Probes =
            [
                new SpecProbe("skip(((1, 2), (3, 4)), 1)", "ok raw=L[S[3, 4]] n=1"),
                new SpecProbe("skip((1, 2), 5)", "ok raw=L[] n=1"),
            ],
            Explanation = "`skip` drops the first `count` items and materializes the rest as one exact list: a single remaining item stays a one-element list, and skipping everything leaves the empty list `[]`.",
        },
        new()
        {
            Id = "filter-keeps-matching",
            Category = "collection-builtins",
            Source = "IsEven = x mod 2 == 0\nfilter((1, 2, 3, 4, 5, 6), IsEven)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[2, 4, 6]",
            ExpectedRaw = "L[2, 4, 6]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("IsEven", ["x"], ".binary .eq (.binary .mod (.param \"x\") (.num 2)) (.num 0)")],
                [LCall("filter", LCapture(LNums(1, 2, 3, 4, 5, 6)), ".resolve \"IsEven\"")]),
            Explanation = "`filter` keeps items whose predicate result is one nonzero atomic value, returning one exact list value.",
        },
        new()
        {
            Id = "filter-single-survivor",
            Category = "collection-builtins",
            Source = "Big(a) = a > 2\nfilter((1, 2, 3), Big)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[3]",
            ExpectedRaw = "L[3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("Big", ["a"], ".binary .gt (.param \"a\") (.num 2)")],
                [LCall("filter", LCapture(LNums(1, 2, 3)), ".resolve \"Big\"")]),
            Explanation = "One surviving item forms the exact one-element list `[3]` — list results never erase the one-item boundary.",
        },
        new()
        {
            Id = "filter-none-empty",
            Category = "collection-builtins",
            Source = "No(a) = 0\nfilter((1, 2, 3), No)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[]",
            ExpectedRaw = "L[]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("No", ["a"], ".num 0")],
                [LCall("filter", LCapture(LNums(1, 2, 3)), ".resolve \"No\"")]),
            Probes =
            [
                new SpecProbe("No(a) = 0\nfilter((1, 2, 3), No) == ()", "ok raw=0 n=1"),
                new SpecProbe("No(a) = 0\nfilter((1, 2, 3), No) == []", "ok raw=1 n=1"),
            ],
            Explanation = "Zero survivors form the empty list `[]`, which is one visible value and never equals the empty sequence value `()`.",
        },
        new()
        {
            Id = "map-transforms-items",
            Category = "collection-builtins",
            Source = "Double = x * 2\nmap((1, 2, 3), Double)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[2, 4, 6]",
            ExpectedRaw = "L[2, 4, 6]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("Double", ["x"], ".binary .mul (.param \"x\") (.num 2)")],
                [LCall("map", LCapture(LNums(1, 2, 3)), ".resolve \"Double\"")]),
            Explanation = "`map` replaces each top-level item with the callback result, preserving order and count, and materializes the mapped items as one exact list.",
        },
        new()
        {
            Id = "map-single-item",
            Category = "collection-builtins",
            Source = "M(a) = a\nmap((7), M)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[7]",
            ExpectedRaw = "L[7]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("M", ["a"], ".param \"a\"")],
                [LCall("map", ".num 7", ".resolve \"M\"")]),
            Explanation = "`(7)` is the atom 7 (singleton parens are transparent), so the supply has one item — and the exact list result keeps it as the one-element list `[7]`.",
        },
        new()
        {
            Id = "map-pair-callback",
            Category = "collection-builtins",
            Source = "Swap(a, b) = (b, a)\nmap(((1, 2), (3, 4)), Swap)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[(2, 1), (4, 3)]",
            ExpectedRaw = "L[S[2, 1], S[4, 3]]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("Swap", ["a", "b"], LCapture(".param \"b\", .param \"a\""))],
                [LCall("map", PairOfPairs, ".resolve \"Swap\"")]),
            Explanation = "Sequence-value callback items are projected one level to the callback's parameters; the callback must return exactly one value per item, and each captured result stays one exact list element (never flattened).",
        },
        new()
        {
            Id = "callback-variadic-collects",
            Category = "collection-builtins",
            Source = "Collect(*items) = items\n\n[7].map(Collect)\n[(1, 2)].map(Collect)\n[[1, 2]].map(Collect)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[[7]]\n[[(1, 2)]]\n[[[1, 2]]]",
            ExpectedRaw = "S[L[L[7]], L[L[S[1, 2]]], L[L[L[1, 2]]]]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LFnP("Collect", [LVar("items")], ".param \"items\"")],
                [".dotCall (.listLiteral [.num 7]) \"map\" (some [.resolve \"Collect\"])",
                 ".dotCall (.listLiteral [.capture [.num 1, .num 2]]) \"map\" (some [.resolve \"Collect\"])",
                 ".dotCall (.listLiteral [.listLiteral [.num 1, .num 2]]) \"map\" (some [.resolve \"Collect\"])"]),
            Probes =
            [
                new SpecProbe("Collect(*items) = items\n[[]].map(Collect)", "ok raw=L[L[L[]]] n=1"),
                new SpecProbe("Collect(*items) = items\n[()].map(Collect)", "ok raw=L[L[S[]]] n=1"),
                new SpecProbe("Collect(*items) = items\nmap((7, 8), Collect)", "ok raw=L[L[7], L[8]] n=1"),
                new SpecProbe("IsSingleSeven(*items) = items == [7]\n[7, 8].filter(IsSingleSeven)", "ok raw=L[7] n=1"),
                new SpecProbe("R(*items, acc) = items == [10]\nreduce([10], R, 99)", "ok raw=1 n=1"),
                new SpecProbe("R(*items) = items\nreduce([10], R, 99)", "ok raw=L[10, 99] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A single-collecting map/filter callback receives each iterated element as ONE collected slot: `items` is the exact list `[element]`, preserving the element's kind (scalar, sequence value, or nested list). Reducers supply element and accumulator slots, so a genuine single-collecting reducer collects both as `[element, accumulator]`; an element-side collecting parameter before a fixed accumulator still observes `[element]`.",
        },
        new()
        {
            Id = "callback-mixed-variadic-rows",
            Category = "collection-builtins",
            Source = "F(first, *middle, last) = middle\nRows = [(1, 2, 3, 4)]\n\nRows.map(F)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[[2, 3]]",
            ExpectedRaw = "L[L[2, 3]]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("F", [LFix("first"), LVar("middle"), LFix("last")], ".param \"middle\""),
                 LProp("Rows", "(.listLiteral [.capture [.num 1, .num 2, .num 3, .num 4]])")],
                [".dotCall (.resolve \"Rows\") \"map\" (some [.resolve \"F\"])"]),
            Probes =
            [
                new SpecProbe("F((first, *middle, last)) = middle\nRows = [(1, 2, 3, 4)]\nRows.map(F)", "ok raw=L[L[2, 3]] n=1"),
                new SpecProbe("F(first, *rest) = rest\n[(1, 2, 3)].map(F)", "ok raw=L[L[2, 3]] n=1"),
                new SpecProbe("F(first, *rest) = rest\n[7].map(F)", "ok raw=L[L[]] n=1"),
                new SpecProbe("F(*init, last) = init\n[(1, 2, 3)].map(F)", "ok raw=L[L[1, 2]] n=1"),
            ],
            Explanation = "A multi-parameter flat callback opens the lone sequence element into row slots (the established flat-callback row convention), then the shared prefix/collecting/suffix binder allocates fixed front/back slots and COLLECTS the middle as an exact list — agreeing with the nested sequence-value pattern form `F((first, *middle, last))`.",
        },
        new()
        {
            Id = "distinct-preserves-first",
            Category = "collection-builtins",
            Source = "distinct((3, 1, 3, 2, 1, 2))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[3, 1, 2]",
            ExpectedRaw = "L[3, 1, 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("distinct", LCapture(LNums(3, 1, 3, 2, 1, 2)))]),
            Explanation = "`distinct` keeps the first occurrence of each structurally-equal item.",
        },
        new()
        {
            Id = "distinct-structural-pairs",
            Category = "collection-builtins",
            Source = "distinct(((1, 2), (1, 2), (3, 4)))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[(1, 2), (3, 4)]",
            ExpectedRaw = "L[S[1, 2], S[3, 4]]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("distinct",
                LCapture(LCapture(LNums(1, 2)), LCapture(LNums(1, 2)), LCapture(LNums(3, 4))))]),
            Explanation = "Deduplication uses structural equality on whole sequence-value items.",
        },
        new()
        {
            Id = "take-family-tutorial",
            Category = "collection-builtins",
            Source = "take((1, 2, 3, 4, 5), 3)\n\ntake(((1, 2), (3, 4)), 1)\n\nrange(1, 5).take(2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3]\n[(1, 2)]\n[1, 2]",
            ExpectedRaw = "S[L[1, 2, 3], L[S[1, 2]], L[1, 2]]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg([],
                [LCall("take", LCapture(LNums(1, 2, 3, 4, 5)), ".num 3"),
                 LCall("take", PairOfPairs, ".num 1"),
                 $".dotCall ({LCall("range", ".num 1", ".num 5")}) \"take\" (some [.num 2])"]),
            Explanation = "The tutorial's `take` examples: a plain prefix list, the single-survivor case (the exact one-element list `[(1, 2)]`), and the dot-call form over a `range` list receiver.",
        },
        new()
        {
            Id = "distinct-family-tutorial",
            Category = "collection-builtins",
            Source = "distinct((3, 1, 3, 2, 1, 2))\n\ndistinct(((1, 2), (1, 2), (3, 4)))\n\nValues = 3, 1, 3, 2, 1, 2\nValues.distinct",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[3, 1, 2]\n[(1, 2), (3, 4)]\n[3, 1, 2]",
            ExpectedRaw = "S[L[3, 1, 2], L[S[1, 2], S[3, 4]], L[3, 1, 2]]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("Values", LNums(3, 1, 3, 2, 1, 2))],
                [LCall("distinct", LCapture(LNums(3, 1, 3, 2, 1, 2))),
                 LCall("distinct", LCapture(LCapture(LNums(1, 2)), LCapture(LNums(1, 2)), LCapture(LNums(3, 4)))),
                 ".dotCall (.resolve \"Values\") \"distinct\" none"]),
            Explanation = "The tutorial's `distinct` examples: atom dedup, structural pair dedup, and the dot-call form over a captured multi-item body.",
        },
        new()
        {
            Id = "spread-one-level-family",
            Category = "sequence-construction",
            Source = "(1, 2)*, 3\n1*, (2, 3)\n(1, (2, 3))*, 4",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n3\n1\n(2, 3)\n1\n(2, 3)\n4",
            ExpectedRaw = "S[1, 2, 3, 1, S[2, 3], 1, S[2, 3], 4]",
            ExpectedEmittedCount = 8,
            LeanProgram = LProg([],
                [$".sequenceSpread {LCapture(LNums(1, 2))}", ".num 3",
                 ".sequenceSpread (.num 1)", LCapture(LNums(2, 3)),
                 $".sequenceSpread {LCapture(".num 1", LCapture(LNums(2, 3)))}", ".num 4"]),
            Explanation = "Spread projects exactly one immediate level, and a comma is required between a spread and a following same-line slot (a star with a right operand is multiplication): each line contributes its spread items plus the trailing slot as root rows.",
        },
        new()
        {
            Id = "distinct-empties-collapse",
            Category = "collection-builtins",
            Source = "distinct(((), ()))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[()]",
            ExpectedRaw = "L[S[]]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("distinct", LCapture(LEmpty, LEmpty))]),
            Probes =
            [
                new SpecProbe("distinct((), ())", "err arity"),
            ],
            Explanation = "The grouped collection's two `()` items deduplicate to one kept `()`, and the exact list result keeps it as the one-element list `[()]` — list results never erase the one-item boundary. `distinct(collection)` takes exactly one argument, so the bare two-argument form is an arity error.",
        },
        new()
        {
            Id = "order-sorts-atoms",
            Category = "collection-builtins",
            Source = "order((3, 4, 2, 1, 3, 3))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3, 3, 3, 4]",
            ExpectedRaw = "L[1, 2, 3, 3, 3, 4]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("order", LCapture(LNums(3, 4, 2, 1, 3, 3)))]),
            Probes =
            [
                new SpecProbe("order(5)", "ok raw=L[5] n=1"),
                new SpecProbe("order(())", "ok raw=L[] n=1"),
            ],
            Explanation = "`order` sorts numeric items ascending into one exact list; a single item forms `[5]` and empty input forms `[]`.",
        },
        new()
        {
            Id = "range-inclusive",
            Category = "collection-builtins",
            Source = "range(1, 5)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3, 4, 5]",
            ExpectedRaw = "L[1, 2, 3, 4, 5]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("range", ".num 1", ".num 5")]),
            Probes =
            [
                new SpecProbe("count(range(1, 5))", "ok raw=5 n=1"),
                new SpecProbe("range(1, 3):0", "ok raw=1 n=1"),
                new SpecProbe("x = range(1, 3)*\nx:0", "ok raw=1 n=1"),
            ],
            Explanation = "`range` returns every integer from start to stop inclusive as one exact list value; `:` selects one element directly from the list result.",
        },
        new()
        {
            Id = "range-single-value",
            Category = "collection-builtins",
            Source = "range(3, 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[3]",
            ExpectedRaw = "L[3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("range", ".num 3", ".num 3")]),
            IncludeInGeneratorPrompt = true,
            Explanation = "A one-integer range is the exact one-element list `[3]` — collection-producing builtins always materialize a list, and the one-item boundary is never erased.",
        },
        new()
        {
            Id = "spread-arguments-keep-written-order",
            Category = "collection-builtins",
            Source = "Lo = 2\nHi = 4\nrange(Lo*, Hi*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[2, 3, 4]",
            ExpectedRaw = "L[2, 3, 4]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("Lo", ".num 2"), LProp("Hi", ".num 4")],
                [LCall("range", ".sequenceSpread (.resolve \"Lo\")", ".sequenceSpread (.resolve \"Hi\")")]),
            Probes =
            [
                // Swapping the written slots swaps the supplied arguments, so the
                // expanded argument order really is the written order.
                new SpecProbe("Lo = 2\nHi = 4\nrange(Hi*, Lo*)", "ok raw=L[4, 3, 2] n=1"),
                // One spread slot supplying both bounds keeps its items in order too.
                new SpecProbe("Bounds = 2, 4\nrange(Bounds*)", "ok raw=L[2, 3, 4] n=1"),
                new SpecProbe("Bounds = 4, 2\nrange(Bounds*)", "ok raw=L[4, 3, 2] n=1"),
            ],
            Notes = "The order companion of `spread-arguments-fail-left-to-right`: correcting the evaluation ORDER of spread argument slots must not reorder the expanded argument VALUES.",
            Explanation = "Expanding spread argument slots preserves written order: each slot contributes its items in place, so `range(Lo*, Hi*)` supplies `Lo`'s item before `Hi`'s.",
        },
        new()
        {
            Id = "atoms-recursive-flatten",
            Category = "collection-builtins",
            Source = "atoms(((1, 2), (3, 4)))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3, 4]",
            ExpectedRaw = "L[1, 2, 3, 4]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("atoms", PairOfPairs)]),
            Explanation = "`atoms` recursively erases all sequence-value structure and materializes the collected atoms as one exact immutable list — the explicit contrast to one-level spread.",
        },
        new()
        {
            Id = "atoms-exact-list-result",
            Category = "collection-builtins",
            Source = "atoms(7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[7]",
            ExpectedRaw = "L[7]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("atoms", ".num 7")]),
            IncludeInGeneratorPrompt = true,
            Probes =
            [
                new SpecProbe("atoms(7) == [7]", "ok raw=1 n=1"),
                new SpecProbe("atoms(7) == 7", "ok raw=0 n=1"),
                new SpecProbe("atoms((1, 2)) == [1, 2]", "ok raw=1 n=1"),
                new SpecProbe("atoms((1, 2)) == (1, 2)", "ok raw=0 n=1"),
                new SpecProbe("atoms(()) == []", "ok raw=1 n=1"),
                new SpecProbe("atoms(()) == ()", "ok raw=0 n=1"),
                new SpecProbe("atoms('text')", "ok raw=L[] n=1"),
            ],
            Explanation = "`atoms` always returns one exact immutable list, whatever the input kind or atom count: a lone number yields the singleton list `[7]` (never the bare `7`), a no-atom input yields `[]`, and the result is list-exact, never a sequence.",
        },
        new()
        {
            Id = "atoms-list-traversal",
            Category = "collection-builtins",
            Source = "atoms([1, 2])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2]",
            ExpectedRaw = "L[1, 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("atoms", ".listLiteral [.num 1, .num 2]")]),
            IncludeInGeneratorPrompt = true,
            Probes =
            [
                new SpecProbe("atoms(1, 2)", "err arity"),
                new SpecProbe("atoms([1, 2]*)", "err arity"),
                new SpecProbe("atoms(([1, 2]*))", "ok raw=L[1, 2] n=1"),
                new SpecProbe("[1, [2, 3]].atoms == atoms([1, [2, 3]])", "ok raw=1 n=1"),
            ],
            Explanation = "`atoms` traverses exact list boundaries just like sequence boundaries. The call boundary is unchanged: `atoms(value)` takes exactly one argument, an unspread list is one argument, and spreading a multi-element list into the call is an ordinary arity error.",
        },
        new()
        {
            Id = "atoms-mixed-traversal",
            Category = "collection-builtins",
            Source = "atoms([(1, 2), [3, [4]]])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3, 4]",
            ExpectedRaw = "L[1, 2, 3, 4]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall(
                "atoms",
                $".listLiteral [{LCapture(".num 1", ".num 2")}, .listLiteral [.num 3, .listLiteral [.num 4]]]")]),
            Probes =
            [
                new SpecProbe("atoms([3, (1, [4, 2])])", "ok raw=L[3, 1, 4, 2] n=1"),
                new SpecProbe("atoms([[], (), [1]])", "ok raw=L[1] n=1"),
                new SpecProbe("atoms([10, [20, 30]]):2", "ok raw=30 n=1"),
            ],
            Explanation = "Mixed sequence/list nesting flattens depth-first, left to right, into one flat exact list: container boundaries are opened, never preserved, and structural order is kept without sorting or deduplication.",
        },
        new()
        {
            Id = "atoms-list-composition",
            Category = "collection-builtins",
            Source = "[1, 2, 3].skip(1).atoms",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[2, 3]",
            ExpectedRaw = "L[2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [".dotCall (.dotCall (.listLiteral [.num 1, .num 2, .num 3]) \"skip\" (some [.num 1])) \"atoms\" none"]),
            Probes =
            [
                new SpecProbe("range(1, 3).atoms", "ok raw=L[1, 2, 3] n=1"),
                new SpecProbe("atoms((3, 1, 2)).order", "ok raw=L[1, 2, 3] n=1"),
                new SpecProbe("atoms((1, 2, 3)).count", "ok raw=3 n=1"),
            ],
            Explanation = "List-producing builtins compose directly with `atoms` — no spread-and-recapture workaround is needed — and the exact-list result of `atoms` composes directly with every collection consumer.",
        },
        new()
        {
            Id = "atoms-no-truthiness",
            Category = "collection-builtins",
            Source = "if((1, [2]), 10, 20)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "10",
            ExpectedRaw = "10",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall(
                "if",
                LCapture(".num 1", ".listLiteral [.num 2]"),
                ".num 10",
                ".num 20")]),
            Probes =
            [
                new SpecProbe("if([1], 10, 20)", "err arity"),
                new SpecProbe("if([], 10, 20)", "err arity"),
                new SpecProbe("if(atoms((1, 2)), 10, 20)", "err arity"),
                new SpecProbe("if(([1], 0), 10, 20)", "ok raw=20 n=1"),
            ],
            Explanation = "`atoms` does not define truthiness: truth testing still flattens through sequence boundaries only, so list values contribute no atoms — a list condition (including an `atoms` result) stays invalid, and list elements inside a sequence condition are skipped.",
        },
        new()
        {
            Id = "sum-of-range-collection",
            Category = "collection-builtins",
            Source = "sum(range(1, 3))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "6",
            ExpectedRaw = "6",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("sum", LCall("range", ".num 1", ".num 3"))]),
            Probes =
            [
                new SpecProbe("sum(range(1, 3)*)", "err arity"),
                new SpecProbe("sum((range(1, 3)*))", "ok raw=6 n=1"),
            ],
            Explanation = "A collection builtin's list result is one collection argument for the next builtin: `sum` opens the bound list one level and sums its items. Spreading the result instead supplies its items as separate arguments — an arity error for the one-parameter `sum(collection)` — unless the spread is re-grouped into one collection value.",
        },
        new()
        {
            Id = "count-family",
            Category = "collection-builtins",
            Source = "count(())\ncount((()))\n\ncount(range(1, 5))\n\ncount((10, 20, 30))\n\ncount((3, 4, range(1, 5)*, 7))\n\ncount((range(1, 5)*, 7))\n\ncount(((1, 2), (3, 4)))\n\nData = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)\n(Data:0).count",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0\n0\n5\n3\n8\n6\n2\n5",
            ExpectedRaw = "S[0, 0, 5, 3, 8, 6, 2, 5]",
            ExpectedEmittedCount = 8,
            LeanProgram = LProg(
                [LProp("Data", $"{LCapture(LNums(7, 6, 4, 2, 1))}, {LCapture(LNums(1, 2, 3, 4, 5))}")],
                [LCall("count", LEmpty),
                 LCall("count", LEmpty),
                 LCall("count", LCall("range", ".num 1", ".num 5")),
                 LCall("count", LCapture(LNums(10, 20, 30))),
                 LCall("count", LCapture(".num 3", ".num 4", $".sequenceSpread ({LCall("range", ".num 1", ".num 5")})", ".num 7")),
                 LCall("count", LCapture($".sequenceSpread ({LCall("range", ".num 1", ".num 5")})", ".num 7")),
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
                [LProp("T", LCapture(LNums(1, 2, 3))), LProp("A", LNums(1, 2, 3))],
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
                new SpecProbe("X = 1, 2, 3\nif(1, X, X)*", "ok raw=S[1, 2, 3] n=3"),
            ],
            Explanation = "`if` is a value boundary like every builtin: the selected branch is one value, turned back into an item supply only by caller-site spread.",
        },
        new()
        {
            Id = "builtin-fixed-collection-arity",
            Category = "collection-builtins",
            Source = "count((1, 2, 3))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("count", LCapture(LNums(1, 2, 3)))]),
            Probes =
            [
                new SpecProbe("count(1, 2, 3)", "err arity"),
                new SpecProbe("count()", "err arity"),
                new SpecProbe("count(3)", "ok raw=1 n=1"),
                new SpecProbe("take((1, 2, 3), 2)", "ok raw=L[1, 2] n=1"),
                new SpecProbe("take([1, 2, 3], 2)", "ok raw=L[1, 2] n=1"),
                new SpecProbe("take((1, 2, 3))", "err arity"),
                new SpecProbe("take([1, 2, 3])", "err arity"),
                new SpecProbe("take([1, 2, 3]*, 2)", "err arity"),
                new SpecProbe("Inspect(*items) = items\nInspect(1, 2, 3)", "ok raw=L[1, 2, 3] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A collection builtin receives exactly ONE fixed collection argument plus its fixed control arguments: `count(collection)` and `take(collection, count)` are ordinary fixed-arity callables, so inline items (`count(1, 2, 3)`), a missing control (`take((1, 2, 3))`), a missing collection (`count()`), and spread items (`take([1, 2, 3]*, 2)`) are ordinary arity errors. A scalar is a one-element collection. USER-DEFINED variadic functions remain a separate general arity mechanism: `Inspect(1, 2, 3)` collects the three argument slots as the exact list `[1, 2, 3]`.",
        },
        new()
        {
            Id = "reduce-accumulates-value",
            Category = "collection-builtins",
            Source = "Append(item, *history) = (history*, item)\nreduce((2, 3, 4), Append, 1)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3, 4)",
            ExpectedRaw = "S[1, 2, 3, 4]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("Append", [LFix("item"), LVar("history")],
                    LCapture(".sequenceSpread (.param \"history\")", ".param \"item\""))],
                [LCall("reduce", LCapture(LNums(2, 3, 4)), ".resolve \"Append\"", ".num 1")]),
            Probes =
            [
                new SpecProbe("Append(item, *history) = (history*, item)\nreduce(2, 3, 4, Append, 1)", "err arity"),
                new SpecProbe("Add(a, b) = a + b\nreduce((1, 2, 3, 4), Add, 0)", "ok raw=10 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`reduce(collection, reducer, initial)` takes exactly three arguments and threads one accumulator value; the result displays as ONE sequence value `(1, 2, 3, 4)` — not as separate rows. Supplying the items inline (`reduce(2, 3, 4, Append, 1)`) is an ordinary five-argument arity error.",
        },
        new()
        {
            Id = "reduce-empty-initial-is-one-value",
            Category = "collection-builtins",
            Source = "R(x, acc) = acc + x\nInit = 1, 2\nreduce((), R, Init)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2)",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFn("R", ["x", "acc"], ".binary .add (.param \"acc\") (.param \"x\")"),
                 LProp("Init", LNums(1, 2))],
                [LCall("reduce", LEmpty, ".resolve \"R\"", ".resolve \"Init\"")]),
            Probes =
            [
                new SpecProbe("R(x, acc) = acc + x\nreduce([], R, [5])", "ok raw=L[5] n=1"),
                new SpecProbe("Add(a, b) = a + b\nreduce((), Add, 5)", "ok raw=5 n=1"),
            ],
            Explanation = "The initial accumulator expression occupies ONE written accumulator slot: its result is reified as one value before reduction begins, so an empty reduction returns the initial accumulator as ONE value (`(1, 2)`, count 1) — never as an unbounded multi-item supply — exactly like the non-empty case threads it.",
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
                [LProp("A", $".num 1, {LCapture(LNums(2, 3))}"),
                 LProp("B", $".num 1, {LCapture(LNums(2, 3))}")],
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
            Source = "Nums = 10, 20, 30, 40, 50\n\n# Select the third value (index 2):\nNums:2",
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
                [LProp("Pairs", $"{LCapture(LNums(1, 2))}, {LCapture(LNums(3, 4))}")],
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
                    $"{LCapture(LCapture(LNums(1, 2)), LCapture(LNums(3, 4)))}, {LCapture(LCapture(LNums(5, 6)), LCapture(LNums(7, 8)))}")],
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
                [LProp("x", LCapture(LEmpty, LEmpty))],
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
                [LProp("x", LCapture(LNums(1, 2)))],
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
                [".binary .eq (.resolve \"y\") " + LCapture(LNums(1, 2))]),
            Explanation = "A captured projection re-materializes as the canonical selected value and compares structurally equal to the written literal.",
        },

        // ==================== parser-layout ====================
        new()
        {
            Id = "output-rows-interleave-definitions",
            Category = "parser-layout",
            Source = "A = 3\nA + B\nB = 2",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5",
            ExpectedRaw = "5",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("A", ".num 3"), LProp("B", ".num 2")],
                [".binary .add (.resolve \"A\") (.resolve \"B\")"]),
            Probes =
            [
                new SpecProbe("A = 3\nA\nA + 1", "ok raw=S[3, 4] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Output rows may be interleaved with property definitions: property resolution uses the complete property set of the algorithm, not textual order.",
        },
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
            Source = "A = (1, 2)\nA* == A*",
            Outcome = SpecOutcome.ParseError,
            Explanation = "A spread expression is not a binary operand; spread results feed slots, not operators.",
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
            Source = "Add(a, b) = a + b\n\nAdd(1, 2)    # 3\nAdd (1, 2)   # the same call, 3",
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
            Source = "# comment\n1 + 1",
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
            Source = "X(*vals) = vals.count\nb = (1, 2)\nX(7 b*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LFnP("X", [LVar("vals")], ".dotCall (.param \"vals\") \"count\" none"),
                 LProp("b", LCapture(LNums(1, 2)))],
                [LCall("X", ".num 7", ".sequenceSpread (.resolve \"b\")")]),
            Explanation = "A spread expression is one whole expression-list slot: `X(7 b*)` is `X(7, b*)`.",
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
                [$".dotCall (.dotCall {LCapture(LNums(1, 2, 3))} \"map\" (some [.algorithmExpr (alg [\"n\"] [] [] [.binary .mul (.param \"n\") (.num 2)])])) \"sum\" none"]),
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
                new SpecProbe("A = {\n}\nA*", "err spreadMissingOutput"),
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
            LeanProgram = LProg([], [LCall("count", "(.algorithmExpr (alg [] [] [] []))")]),
            Explanation = "`{}` where a value is required is a missing-output error, not `0`.",
        },
        new()
        {
            Id = "scalar-op-rejects-sequence",
            Category = "errors",
            Source = "(1, 2) + 1",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            LeanProgram = LProg([], [$".binary .add {LCapture(LNums(1, 2))} (.num 1)"]),
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
            LeanProgram = LProg([], [LCall("order", LCapture(".num 1", "(.stringLiteral \"hello\")"))]),
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
            Id = "spread-arguments-fail-left-to-right",
            Category = "errors",
            Source = "P = 1 / 0\nQ = 'x' + 1\nrange(P*, Q*)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "div0",
            LeanProgram = LProg(
                [LProp("P", ".binary .div (.num 1) (.num 0)"),
                 LProp("Q", ".binary .add (.stringLiteral \"x\") (.num 1)")],
                [LCall("range", ".sequenceSpread (.resolve \"P\")", ".sequenceSpread (.resolve \"Q\")")]),
            Probes =
            [
                // The mirrored spelling: whichever spread slot is written FIRST is the
                // one whose failure is reported.
                new SpecProbe("P = 1 / 0\nQ = 'x' + 1\nrange(Q*, P*)", "err type"),
                // The same rule at other builtins that expand spread arguments.
                new SpecProbe("P = 1 / 0\nQ = 'x' + 1\nif(P*, Q*, 0)", "err div0"),
                new SpecProbe("P = 1 / 0\nQ = 'x' + 1\nif(Q*, P*, 0)", "err type"),
                new SpecProbe("P = 1 / 0\nQ = 'x' + 1\nrepeat(P*, Q*, 1)", "err div0"),
                new SpecProbe("P = 1 / 0\nQ = 'x' + 1\nrepeat(Q*, P*, 1)", "err type"),
            ],
            Notes = "Pins the forced-spread evaluation ORDER, not just the reported category: each spread-marked slot is forced exactly once, left to right, and expanding a spread slot is part of evaluating that slot. Non-spread slots remain builtin-lazy algorithms at this stage (SpreadArgumentEvaluationOrderTests pins the mixed spread/non-spread interaction).",
            Explanation = "Spread-marked argument slots are forced exactly once in left-to-right written order, so the leftmost failing spread slot's error is the one reported; non-spread argument slots remain builtin-lazy and are evaluated or skipped by the builtin's own semantics.",
        },
        new()
        {
            Id = "unresolved-implicit-parameter",
            Category = "errors",
            Source = "Nope",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "unresolvedImplicitParams",
            LeanProgram = ".algorithmExpr (alg [\"Nope\"] [] [] [.param \"Nope\"])",
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

        // ==================== lists ====================
        new()
        {
            Id = "list-literal",
            Category = "lists",
            Source = "[1, 2, 3]",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3]",
            ExpectedRaw = "L[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [".listLiteral [.num 1, .num 2, .num 3]"]),
            Probes =
            [
                new SpecProbe("[[1, 2], [3, 4]]", "ok raw=L[L[1, 2], L[3, 4]] n=1"),
                new SpecProbe("[()]", "ok raw=L[S[]] n=1"),
                new SpecProbe("[(1, 2)]", "ok raw=L[S[1, 2]] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`[1, 2, 3]` is an exact immutable list value: one value whose elements are stored exactly, displayed with brackets.",
        },
        new()
        {
            Id = "list-exactness",
            Category = "lists",
            Source = "[7] == 7\n[[1, 2]] == [1, 2]\n[[]] == []",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0\n0\n0",
            ExpectedRaw = "S[0, 0, 0]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [],
                [".binary .eq (.listLiteral [.num 7]) (.num 7)",
                 ".binary .eq (.listLiteral [.listLiteral [.num 1, .num 2]]) (.listLiteral [.num 1, .num 2])",
                 ".binary .eq (.listLiteral [.listLiteral []]) (.listLiteral [])"]),
            Probes =
            [
                new SpecProbe("[1, 2] == [1, 2]", "ok raw=1 n=1"),
                new SpecProbe("[[1], [2, 3]] == [[1], [2, 3]]", "ok raw=1 n=1"),
                new SpecProbe("[1, [2]] == [1, 2]", "ok raw=0 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Lists preserve exact cardinality and nesting: `[7]` is not `7`, `[[1, 2]]` is not `[1, 2]`, `[[]]` is not `[]`; equality is structural and recursive.",
        },
        new()
        {
            Id = "list-vs-sequence-kind",
            Category = "lists",
            Source = "[] == ()\n[1, 2] == (1, 2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0\n0",
            ExpectedRaw = "S[0, 0]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [],
                [".binary .eq (.listLiteral []) (.emptySequence 0)",
                 ".binary .eq (.listLiteral [.num 1, .num 2]) (.capture [.num 1, .num 2])"]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Lists and sequence values are different value kinds: equal elements never make a list equal a sequence, and `[]` is not `()`.",
        },
        new()
        {
            Id = "list-index-selects-element",
            Category = "lists",
            Source = "[1, 2, 3]:0",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1",
            ExpectedRaw = "1",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [".index (.listLiteral [.num 1, .num 2, .num 3]) (.num 0)"]),
            Probes =
            [
                new SpecProbe("[1, 2, 3]:2", "ok raw=3 n=1"),
                new SpecProbe("[7]:0", "ok raw=7 n=1"),
                new SpecProbe("((1, 2, 3):1) == ([1, 2, 3]:1)", "ok raw=1 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`:` selects one immediate element from an exact list by zero-based position, exactly like sequence selection.",
        },
        new()
        {
            Id = "list-index-nested-element-stays-exact",
            Category = "lists",
            Source = "Rows = [[1, 2], [3, 4]]\nRows:0\nRows:0:1",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2]\n2",
            ExpectedRaw = "S[L[1, 2], 2]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("Rows", ".listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]")],
                [".index (.resolve \"Rows\") (.num 0)",
                 ".index (.index (.resolve \"Rows\") (.num 0)) (.num 1)"]),
            Probes =
            [
                new SpecProbe("[[1, 2]]:0 == [1, 2]", "ok raw=1 n=1"),
                new SpecProbe("[[1, 2]]:0 == (1, 2)", "ok raw=0 n=1"),
                new SpecProbe("[(1, 2), (3, 4)]:0", "ok raw=S[1, 2] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A selected list element is returned exactly as stored — one opaque list, never flattened or converted — while a selected sequence element projects one level as usual; chaining `:` selects one level at a time.",
        },
        new()
        {
            Id = "list-index-out-of-range",
            Category = "lists",
            Source = "[]:0",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "index",
            LeanProgram = LProg([], [".index (.listLiteral []) (.num 0)"]),
            Probes =
            [
                new SpecProbe("[1, 2]:2", "err index"),
                new SpecProbe("[1, 2]:100", "err index"),
                new SpecProbe("A = []\nA:0", "err index"),
            ],
            Explanation = "Empty and past-the-end list positions report the same out-of-range index error as sequence selection.",
        },
        new()
        {
            Id = "list-index-builtin-results",
            Category = "lists",
            Source = "range(1, 3):2",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [$".index ({LCall("range", ".num 1", ".num 3")}) (.num 2)"]),
            Probes =
            [
                new SpecProbe("take([1, 2, 3], 1):0", "ok raw=1 n=1"),
                new SpecProbe("[3, 1, 2].order:0", "ok raw=1 n=1"),
                new SpecProbe("A = range(1, 3)\nA:0", "ok raw=1 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Collection-producing builtin results are exact lists and can be indexed directly — no spread-and-recapture step is needed.",
        },
        new()
        {
            Id = "list-redundant-parens-canonicalize",
            Category = "lists",
            Source = "([1, 2]) == [1, 2]",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1",
            ExpectedRaw = "1",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [],
                [".binary .eq (.listLiteral [.num 1, .num 2]) (.listLiteral [.num 1, .num 2])"]),
            Probes =
            [
                new SpecProbe("(([1]))", "ok raw=L[1] n=1"),
            ],
            Explanation = "Ordinary parentheses stay a redundant sequence grouping even around lists: `([1, 2])` canonicalizes to the exact list itself.",
        },
        new()
        {
            Id = "list-spread-capture",
            Category = "lists",
            Source = "A = [1, 2, 3]\n\nx = A\ny = A*\n\nx\ny",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3]\n(1, 2, 3)",
            ExpectedRaw = "S[L[1, 2, 3], S[1, 2, 3]]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("A", "(.listLiteral [.num 1, .num 2, .num 3])"),
                 LProp("x", ".resolve \"A\""),
                 LProp("y", ".sequenceSpread (.resolve \"A\")")],
                [".resolve \"x\"", ".resolve \"y\""]),
            IncludeInGeneratorPrompt = true,
            Explanation = "Single-name capture preserves the list; the spread marker opens exactly one list boundary into the item supply, so capturing the spread yields the canonical sequence of the elements.",
        },
        new()
        {
            Id = "list-spread-edges",
            Category = "lists",
            Source = "A = []\nB = [7]\nC = [[7]]\n\nA*\nB*\nC*",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7\n[7]",
            ExpectedRaw = "S[7, L[7]]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("A", "(.listLiteral [])"),
                 LProp("B", "(.listLiteral [.num 7])"),
                 LProp("C", "(.listLiteral [.listLiteral [.num 7]])")],
                [".sequenceSpread (.resolve \"A\")",
                 ".sequenceSpread (.resolve \"B\")",
                 ".sequenceSpread (.resolve \"C\")"]),
            Probes =
            [
                new SpecProbe("A = []\nx = A*\nx", "ok raw=S[] n=1"),
            ],
            Explanation = "Spread opens ONE boundary: `[]*` supplies zero items (the row vanishes), `[7]*` supplies `7`, and `[[7]]*` supplies the inner list `[7]` intact.",
        },
        new()
        {
            Id = "list-literal-spread-elements",
            Category = "lists",
            Source = "A = 1, 2, 3\n\n[A*]\n[0, A*, 4]",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3]\n[0, 1, 2, 3, 4]",
            ExpectedRaw = "S[L[1, 2, 3], L[0, 1, 2, 3, 4]]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("A", LNums(1, 2, 3))],
                [".listLiteral [.sequenceSpread (.resolve \"A\")]",
                 ".listLiteral [.num 0, .sequenceSpread (.resolve \"A\"), .num 4]"]),
            IncludeInGeneratorPrompt = true,
            Explanation = "List-literal elements use the ordinary expression-list model: a spread element inserts its item supply into the list being constructed.",
        },
        new()
        {
            Id = "list-elements-preserve-boundaries",
            Category = "lists",
            Source = "A = [1, 2]\nB = [3, 4]\n\n[A, B]\n[A*, B*]\n[A, B*]",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[[1, 2], [3, 4]]\n[1, 2, 3, 4]\n[[1, 2], 3, 4]",
            ExpectedRaw = "S[L[L[1, 2], L[3, 4]], L[1, 2, 3, 4], L[L[1, 2], 3, 4]]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("A", "(.listLiteral [.num 1, .num 2])"),
                 LProp("B", "(.listLiteral [.num 3, .num 4])")],
                [".listLiteral [.resolve \"A\", .resolve \"B\"]",
                 ".listLiteral [.sequenceSpread (.resolve \"A\"), .sequenceSpread (.resolve \"B\")]",
                 ".listLiteral [.resolve \"A\", .sequenceSpread (.resolve \"B\")]"]),
            Explanation = "Non-spread list values stay single elements; only an explicit `value*` slot opens a list into the surrounding list literal.",
        },
        new()
        {
            Id = "list-written-slot-reifies-projection",
            Category = "lists",
            Source = "S = ((1, 2), (3, 4))\n\n[S:0, 5]\n[S:0*, 5]",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[(1, 2), 5]\n[1, 2, 5]",
            ExpectedRaw = "S[L[S[1, 2], 5], L[1, 2, 5]]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("S", LCapture(LCapture(LNums(1, 2)), LCapture(LNums(3, 4))))],
                [".listLiteral [.index (.resolve \"S\") (.num 0), .num 5]",
                 ".listLiteral [.sequenceSpread (.index (.resolve \"S\") (.num 0)), .num 5]"]),
            Probes =
            [
                new SpecProbe("S = ((1, 2), (3, 4))\nz = (S:0, 5)\nz", "ok raw=S[S[1, 2], 5] n=1"),
                new SpecProbe("S = ((1, 2), (3, 4))\nF((x, y)) = (x == (1, 2)) + y\nF((S:0, 5))", "ok raw=6 n=1"),
                new SpecProbe("S = ((1, 2), (3, 4))\nF((x, y, z)) = x + y + z\nF((S:0*, 5))", "ok raw=8 n=1"),
            ],
            Explanation = "A non-spread expression occupying one written slot contributes exactly ONE persistent value: `S:0` is a two-item projection, but as a list element it is the pair `(1, 2)` — matching capture, call arguments, and every other written-slot receiver. Only an explicit spread `(S:0)*` opens the projected value into the surrounding slots.",
            IncludeInGeneratorPrompt = true,
        },
        new()
        {
            Id = "list-empty-spread-neutral",
            Category = "lists",
            Source = "[1, []*, 2]\n[1, ()*, 2]",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2]\n[1, 2]",
            ExpectedRaw = "S[L[1, 2], L[1, 2]]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [],
                [".listLiteral [.num 1, .sequenceSpread (.listLiteral []), .num 2]",
                 ".listLiteral [.num 1, .sequenceSpread (.emptySequence 0), .num 2]"]),
            Probes =
            [
                new SpecProbe("F(a, b) = a + b\nF(1, []*, 2)", "ok raw=3 n=1"),
                new SpecProbe("[1, [], 2]", "ok raw=L[1, L[], 2] n=1"),
            ],
            Explanation = "Spreading an empty list contributes zero elements, exactly like `()*`; a NON-spread `[]` element stays one visible list element.",
        },
        new()
        {
            Id = "list-call-boundary",
            Category = "lists",
            Source = "F(a, b, c) = a + b + c\nOne(x) = 7\n\nA = [1, 2, 3]\n\nOne(A)\nF(A*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7\n6",
            ExpectedRaw = "S[7, 6]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LFn("F", ["a", "b", "c"], ".binary .add (.binary .add (.param \"a\") (.param \"b\")) (.param \"c\")"),
                 LFn("One", ["x"], ".num 7"),
                 LProp("A", "(.listLiteral [.num 1, .num 2, .num 3])")],
                [LCall("One", ".resolve \"A\""),
                 LCall("F", ".sequenceSpread (.resolve \"A\")")]),
            Probes =
            [
                new SpecProbe("F(a) = a\nF([]*)", "err arity"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Calls never open lists implicitly: `One(A)` passes one list-valued argument, `F(A*)` explicitly supplies its three elements, and `F([]*)` supplies zero arguments.",
        },
        new()
        {
            Id = "list-lone-deconstruction",
            Category = "lists",
            Source = "x, y, z = [1, 2, 3]\n\nx\ny\nz",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n3",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 3,
            LeanProgram = LProg(
                [LProp("d", "(.listLiteral [.num 1, .num 2, .num 3])"),
                 LDecon("d", [], ["x", "y", "z"], -1, "x"),
                 LDecon("d", [], ["x", "y", "z"], -1, "y"),
                 LDecon("d", [], ["x", "y", "z"], -1, "z")],
                [".resolve \"x\"", ".resolve \"y\"", ".resolve \"z\""]),
            Probes =
            [
                new SpecProbe("x, y, z = [1, 2, 3]*\nx, y, z", "ok raw=S[1, 2, 3] n=3"),
                new SpecProbe("A = [1, 2, 3]\nx, y, z = A\nx, y, z", "ok raw=S[1, 2, 3] n=3"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A multi-target deconstruction whose right-hand side is exactly one list value opens the list, binding identically to the explicit spread.",
        },
        new()
        {
            Id = "list-deconstruction-not-recursive",
            Category = "lists",
            Source = "x, y = [[1, 2], 3]\n\nx\ny",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2]\n3",
            ExpectedRaw = "S[L[1, 2], 3]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("d", "(.listLiteral [.listLiteral [.num 1, .num 2], .num 3])"),
                 LDecon("d", [], ["x", "y"], -1, "x"),
                 LDecon("d", [], ["x", "y"], -1, "y")],
                [".resolve \"x\"", ".resolve \"y\""]),
            Probes =
            [
                new SpecProbe("x, y = [1, 2], 3\nx, y", "ok raw=S[L[1, 2], 3] n=2"),
            ],
            Explanation = "Only the outer lone structure opens: nested lists stay intact, and a list that is one item of an already multi-item supply stays one value.",
        },
        new()
        {
            Id = "collecting-binding-exact-list",
            Category = "lists",
            Source = "x, *rest = [1, 2, 3]\n\nx\nrest",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n[2, 3]",
            ExpectedRaw = "S[1, L[2, 3]]",
            ExpectedEmittedCount = 2,
            LeanProgram = LProg(
                [LProp("d", "(.listLiteral [.num 1, .num 2, .num 3])"),
                 LDecon("d", [], ["x", "rest"], 1, "x"),
                 LDecon("d", [], ["x", "rest"], 1, "rest")],
                [".resolve \"x\"", ".resolve \"rest\""]),
            Probes =
            [
                new SpecProbe("x, *rest = [1]\nrest == []", "ok raw=1 n=1"),
                new SpecProbe("x, *rest = [1]\nrest == ()", "ok raw=0 n=1"),
                new SpecProbe("x, *rest = [1, 2]\nrest", "ok raw=L[2] n=1"),
                new SpecProbe("x, *rest = [[1, 2, 3]]\nx", "ok raw=L[1, 2, 3] n=1"),
                new SpecProbe("x, *rest = 1, [2, 3], 4\nrest", "ok raw=L[L[2, 3], 4] n=1"),
                new SpecProbe("x, *rest = 1, [2, 3]*, (4, 5)*\nrest", "ok raw=L[2, 3, 4, 5] n=1"),
                new SpecProbe("Rows = [[1, 2], [3, 4]]\nfirst, *rest = Rows\nrest", "ok raw=L[L[3, 4]] n=1"),
                new SpecProbe("Rows = [[1, 2], [3, 4]]\nfirst, *rest = Rows\nrest.count", "ok raw=1 n=1"),
                new SpecProbe("skip([1, 2, 3], 1)", "ok raw=L[2, 3] n=1"),
                new SpecProbe("x, *rest = [1, 2, 3]\nrest == skip([1, 2, 3], 1)", "ok raw=1 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A collecting binding COLLECTS the item slots assigned to it into one exact immutable list: `rest` from `x, *rest = [1, 2, 3]` is `[2, 3]`, the empty segment is `[]`, a singleton segment is `[item]` (a one-row segment of `[[1, 2], [3, 4]]` stays `[[3, 4]]`, count 1), and the result agrees with collection builtins — `rest == skip([1, 2, 3], 1)`.",
        },
        new()
        {
            Id = "list-lone-collecting-assignment",
            Category = "lists",
            Source = "*items = [1, 2, 3]\nitems",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3]",
            ExpectedRaw = "L[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg(
                [LProp("d", "(.listLiteral [.num 1, .num 2, .num 3])"),
                 LDecon("d", [], ["items"], 0, "items")],
                [".resolve \"items\""]),
            Probes =
            [
                new SpecProbe("*items = []\nitems", "ok raw=L[] n=1"),
                new SpecProbe("*items = [7]\nitems", "ok raw=L[7] n=1"),
            ],
            Explanation = "A lone collecting binding opens one right-hand-side structure boundary and collects its items as one exact immutable list; empty and singleton lists remain exact.",
        },
        new()
        {
            Id = "list-builtin-collection",
            Category = "lists",
            Source = "count([1, 2, 3])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            LeanProgram = LProg([], [LCall("count", "(.listLiteral [.num 1, .num 2, .num 3])")]),
            Probes =
            [
                new SpecProbe("count([1, 2, 3]*)", "err arity"),
                new SpecProbe("sum([1, 2, 3])", "ok raw=6 n=1"),
                new SpecProbe("sum(([1, 2, 3]*))", "ok raw=6 n=1"),
                new SpecProbe("A = [1, 2]\nA.count", "ok raw=2 n=1"),
                new SpecProbe("count([], [])", "err arity"),
                new SpecProbe("count(([], []))", "ok raw=2 n=1"),
                new SpecProbe("count([1, [2], 3])", "ok raw=3 n=1"),
                new SpecProbe("take([1, 2, 3], 1)", "ok raw=L[1] n=1"),
                new SpecProbe("contains([1, 2, 3], 2)", "ok raw=1 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A list is ONE collection argument: `count([1, 2, 3])` and `A.count` count three items through the post-binding one-level collection view. The view is never recursive — a grouped pair of lists counts its two opaque list items (`count(([], []))` is 2), and a nested list stays one item. Spread supplies ordinary argument slots, so `count([1, 2, 3]*)` and the bare two-argument `count([], [])` are arity errors; re-group a spread (`sum(([1, 2, 3]*))`) to pass its items as one collection.",
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
