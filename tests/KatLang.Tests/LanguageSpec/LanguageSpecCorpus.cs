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

    /// <summary>
    /// All canonical cases, with each Lean-guarded case's Lean program DERIVED
    /// from the source's real elaborated AST through <see cref="LeanAstEncoder"/>
    /// (see <see cref="SpecCase.LeanProgram"/>). Derivation is fail-loud: a
    /// non-parse-error case must either derive cleanly, carry an explicit
    /// <see cref="SpecCase.LeanExclusionReason"/>, or carry an explicit
    /// <see cref="SpecCase.LeanProgramOverride"/> with a reason — so an encoder
    /// or parser regression fails corpus construction naming the case instead
    /// of silently shrinking the Lean-guarded partition. The corpus is
    /// deterministic and immutable, so it is built once per process.
    /// </summary>
    public static IReadOnlyList<SpecCase> AllCases() => LazyCases.Value;

    private static readonly Lazy<IReadOnlyList<SpecCase>> LazyCases =
        new(() => RawCases().Select(DeriveLeanProgram).ToList().AsReadOnly());

    private static SpecCase DeriveLeanProgram(SpecCase specCase)
    {
        // The corpus is cached process-wide. Freeze every nested collection too,
        // so a caller cannot mutate a probe list and make later tests depend on
        // which test first touched AllCases().
        specCase = specCase with { Probes = specCase.Probes.ToList().AsReadOnly() };

        if (specCase.Outcome == SpecOutcome.ParseError
            || specCase.LeanExclusionReason is not null
            || specCase.LeanProgramOverride is not null)
        {
            return specCase;
        }

        var parsed = Parser.Parse(specCase.Source);
        if (parsed.HasErrors)
        {
            throw new InvalidOperationException(
                $"Language-spec case '{specCase.Id}' is not a ParseError case but its source does not parse cleanly: "
                + string.Join(" | ", parsed.Diagnostics.Select(d => d.Message.Split('\n')[0]))
                + $"\nSource:\n{specCase.Source}");
        }

        try
        {
            return specCase with { DerivedLeanProgram = LeanAstEncoder.EncodeProgram(parsed.Root) };
        }
        catch (NotSupportedException ex)
        {
            throw new InvalidOperationException(
                $"Language-spec case '{specCase.Id}' cannot be Lean-encoded; either extend LeanAstEncoder "
                + "deliberately, exclude the case with a reviewed LeanExclusionReason, or (exceptionally) supply a "
                + $"LeanProgramOverride with a reason. Encoder said: {ex.Message}"
                + $"\nSource:\n{specCase.Source}", ex);
        }
    }

    // ----- The corpus -------------------------------------------------------

    private static IReadOnlyList<SpecCase> RawCases() =>
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
            Explanation = "Multiplication binds tighter than addition; a bare expression is the program's output.",
        },
        new()
        {
            Id = "power-unary-precedence",
            Category = "arithmetic",
            Source = "-2 ^ 2\n(-2) ^ 2\n2 ^ 3 ^ 2",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "-4\n4\n512",
            ExpectedRaw = "S[-4, 4, 512]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // The exponent side re-enters the unary level, so a negated
                // exponent needs no parentheses (Decimal128-only results).
                new SpecProbe("2 ^ -2", "ok raw=0.25 n=1"),
                new SpecProbe("-2 ^ -2", "ok raw=-0.25 n=1"),
                // The unary tier sits between the multiplicative tier and `^`.
                new SpecProbe("1 + -2 ^ 2", "ok raw=-3 n=1"),
                new SpecProbe("2 * -3 ^ 2", "ok raw=-18 n=1"),
                // Combined associativity: a unary base negates the whole
                // right-associative chain; a unary exponent applies to the
                // whole tail it introduces.
                new SpecProbe("-2 ^ 3 ^ 2", "ok raw=-512 n=1"),
                new SpecProbe("2 ^ -2 ^ 2", "ok raw=0.0625 n=1"),
                // `not` shares the prefix-unary tier.
                new SpecProbe("not 0 ^ 0", "ok raw=0 n=1"),
                new SpecProbe("2 ^ not 0", "ok raw=2 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`^` binds tighter than prefix `-`/`not` on the left, so `-2 ^ 2` negates the power: `-(2 ^ 2)`. Parenthesize the base to raise a negative value: `(-2) ^ 2`. The exponent side accepts a unary value directly (`2 ^ -2` is `0.25`), and `^` chains group from the right.",
        },
        new()
        {
            Id = "integer-division-truncates",
            Category = "arithmetic",
            Source = "-7 div 2\n-7 mod 2\n7 div 2",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "-3\n-1\n3",
            ExpectedRaw = "S[-3, -1, 3]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // An exact `/` quotient is the same value in both engines.
                new SpecProbe("8 / 2", "ok raw=4 n=1"),
                // Zero to a negative integer power is the specified error in
                // BOTH numeric models (Lean `negativeIntPow`, C# `EvalPow`).
                new SpecProbe("0 ^ -1", "err illegalInEval"),
            ],
            Notes = "Shared Lean-modeled law on these common exact integer operands: `div`/`mod` truncate toward zero (Lean `Int.tdiv`/`Int.tmod`; C# `Decimal128.Truncate(x / y)`/`%`). This is not a blanket claim about every integral Decimal128 input: a sufficiently large C# `div` quotient can round before truncation. Contrast the C#-only `division-decimal-quotient` case, where a non-exact `/` result diverges from the Int core by design.",
            Explanation = "Integer division `div` and remainder `mod` truncate toward zero: `-7 div 2` is `-3` and `-7 mod 2` is `-1`. These representative exact integer operations are cross-engine semantics shared with the Lean core model; Decimal128 precision/range remains a separate boundary for large operands.",
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
            Explanation = "A non-spread `()` occupies one visible supplied slot: `F(())` binds `a = ()`.",
        },
        new()
        {
            Id = "fixed-empty-spread-zero-items",
            Category = "empty-visible-vs-spread",
            Source = "F(a) = a\nF(()*)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
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
            Explanation = "Without a collecting target the item count must match exactly: one supplied item cannot bind two targets.",
        },
        new()
        {
            Id = "decon-arity-over",
            Category = "deconstruction",
            Source = "x, y = 1, 2, 3\nx",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
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
            Explanation = "Deconstruction with a middle collecting binding over a stored sequence value: fixed targets take the ends, the collecting binding collects the middle as one exact immutable list.",
        },
        new()
        {
            Id = "decon-two-collecting-rejected",
            Category = "deconstruction",
            Source = "*a, *b = 1, 2, 3\na",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "at most one collecting binding",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidCollectingBinding,
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
            Id = "dot-member-fallback-implicit-signature",
            Category = "access-boundaries",
            Source = "K = a.t\nK(7, {a+1})",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8",
            ExpectedRaw = "8",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("K(a, t) = a.t\nK(7, {a+1})", "ok raw=8 n=1"),
                new SpecProbe("K = a.t(b)\nK(1, {x + y * 10}, 2)", "ok raw=21 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "An opaque receiver may not carry the member structurally, so the dot edge's lexical fallback may be selected at runtime and its callable name participates in implicit parameter inference at the member's semantic source occurrence. DotCall order is receiver, participating member/fallback, then written arguments: `K = a.t` corresponds to `K(a, t) = a.t`, while runtime fallback still invokes `t(a)` and the direct source `t(a)` independently infers callee first.",
        },
        new()
        {
            Id = "grace-dot-higher-order-implicit",
            Category = "access-boundaries",
            Source = "K = a~.t\nK({a+1}, 7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8",
            ExpectedRaw = "8",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("K = a.~t\nK({a+1}, 7)", "ok raw=8 n=1"),
                new SpecProbe("K(t, a) = a~.t\nK({a+1}, 7)", "ok raw=8 n=1"),
                new SpecProbe("K(t, a) = a.~t\nK({a+1}, 7)", "ok raw=8 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Grace composes with ordinary DotCall. Base occurrence order for `a.t` is receiver then participating fallback: `(a, t)`. In `a~.t`, ordinary postfix Grace moves `a` one place later; in `a.~t`, ordinary prefix Grace moves `t` one place earlier. Both infer `(t, a)`, while all three sources elaborate to the same ordinary `a.t` body.",
        },
        new()
        {
            Id = "grace-dot-keeps-structural-precedence",
            Category = "access-boundaries",
            Source = "V(x) = 99\nObj = {\n    public V = 42\n    0\n}\n\nObj.V\nObj~.V",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "42\n42",
            ExpectedRaw = "S[42, 42]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                new SpecProbe("V(x) = 99\nObj = {\n    public V = 42\n    0\n}\nObj.~V", "ok raw=42 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`~` changes inferred parameter ORDER only — never member selection. `Obj.V`, `Obj~.V`, and `Obj.~V` all perform ordinary structural-first DotCall lookup, so each reads Obj's own property even though a lexical `V` exists. To call the lexical `V` with Obj's value, write the call `V(Obj)`.",
        },
        new()
        {
            Id = "dot-member-fallback-in-closed-parameter-list",
            Category = "access-boundaries",
            Source = "K(x) = x.V\nObj = {public V = 42}\n\nK(Obj)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "42",
            ExpectedRaw = "42",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("Get(obj) = obj.size\nsize(v) = 77\nGet(3)", "ok raw=77 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "An explicit parameter list is CLOSED, and it asks the definite question: a member name whose fallback merely MAY be selected is not required to be declared. `K(x) = x.V` keeps arity 1, resolving `V` structurally on the runtime receiver and reaching the lexical fallback only when the receiver has no such member.",
        },
        new()
        {
            Id = "open-capture-target-rejected",
            Category = "access-boundaries",
            Source = "M = {\n    public C = 5\n}\nR = {\n    open (M)\n    C\n}\nR",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "a parenthesized group is a captured value, not an algorithm",
            ExpectedDiagnosticCode = DiagnosticCode.BadOpenForm,
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
            Source = "V(x) = 99\nObj = {\n    public V = 7\n    0\n}\n\nObj.V\n(Obj).V",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7\n99",
            ExpectedRaw = "S[7, 99]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                new SpecProbe("F2(x, y) = x + y\nX = 3\n(X).F2(4)", "ok raw=7 n=1"),
                new SpecProbe("Obj = {public V = 7}\nQ(z) = (Obj).V\nQ(0)", "err unknownName"),
            ],
            Explanation = "A capture receiver has no structural members: `Obj.V` reads Obj's own property, while `(Obj).V` falls back lexically and injects the captured receiver as the leading argument. With no lexical member name in sight the fallback has nowhere to go — inside a closed parameter list that is an unknown-name error, and in an implicitly parameterized body the member becomes an inferred parameter instead.",
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
            Explanation = "Selecting a `()` item shows one `()` row: the empty value is a real selectable item.",
        },
        new()
        {
            Id = "index-out-of-range",
            Category = "equality-and-indexing",
            Source = "x = (1, 2)\nx:9",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "index",
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
            ExpectedDiagnosticCode = DiagnosticCode.UnsupportedSemicolon,
            IncludeInGeneratorPrompt = true,
            Explanation = "Semicolon is not expression syntax: use comma or adjacency for separate slots, or parentheses for one sequence value.",
        },
        new()
        {
            Id = "trailing-comma-in-parens-rejected",
            Category = "parser-layout",
            Source = "(3,)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.UnexpectedToken,
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
            Explanation = "A trailing comma keeps the expression list open across the newline: two root output slots.",
        },
        new()
        {
            Id = "spread-not-binary-operand",
            Category = "parser-layout",
            Source = "A = (1, 2)\nA* == A*",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.MisplacedSpread,
            Explanation = "A spread expression is not a binary operand; spread results feed slots, not operators.",
        },
        new()
        {
            Id = "negative-index-literal-rejected",
            Category = "parser-layout",
            Source = "x = (1, 2)\nx:-1",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.UnexpectedToken,
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
            Explanation = "Supplying more arguments than fixed parameters is an arity error.",
        },
        new()
        {
            Id = "missing-output-not-a-value",
            Category = "errors",
            Source = "A = {\n}\nA",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "missingOutput",
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
            Explanation = "`{}` where a value is required is a missing-output error, not `0`.",
        },
        new()
        {
            Id = "scalar-op-rejects-sequence",
            Category = "errors",
            Source = "(1, 2) + 1",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
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
            Explanation = "Division by zero is a runtime error.",
        },
        new()
        {
            Id = "spread-arguments-fail-left-to-right",
            Category = "errors",
            Source = "P = 1 / 0\nQ = 'x' + 1\nrange(P*, Q*)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "div0",
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

        // ==================== C#-only model divergences ====================
        // The canonical numeric family for the Decimal128-vs-Lean-Int model
        // boundary (plus the unmodeled Math-native surface at the end). Each
        // case pins runtime-contract behavior the Lean Int core cannot
        // represent and carries the reviewed LeanExclusionReason that keeps it
        // out of the Lean-guarded partition; the shared integer tier stays
        // Lean-comparable (see `integer-division-truncates`,
        // `division-by-zero`). Routing rule: the numeric-semantics row in
        // src/KatLang/SEMANTIC-ALIGNMENT.md.
        new()
        {
            Id = "avg-decimal-mean",
            Category = "collection-builtins",
            Source = "avg((1, 2))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1.5",
            ExpectedRaw = "1.5",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Decimal mean: the C# runtime performs Decimal128 division and returns `1.5`; the Lean Int core uses `Int.tdiv` and returns `1` (documented model limitation, tutorial 'Average' section).",
            Explanation = "`avg` returns the decimal mean in the runtime; the Lean Int-core model truncates and is documented as a model limitation, not the runtime contract.",
        },
        new()
        {
            Id = "decimal-fraction-arithmetic",
            Category = "arithmetic",
            Source = "0.5 + 0.5",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1.0",
            ExpectedRaw = "1.0",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Fractional Decimal128 literals and values are outside the Lean Int numeric model; LeanAstEncoder refuses fractional numbers by design rather than approximating them, so the program itself has no faithful Lean form.",
            Probes =
            [
                // The classic binary-floating-point failure is exact in decimal
                // arithmetic.
                new SpecProbe("0.1 + 0.2 == 0.3", "ok raw=1 n=1"),
                // Ordinary arithmetic keeps its IEEE quantum; literals keep the
                // quantum they were written with.
                new SpecProbe("2.50 * 4", "ok raw=10.00 n=1"),
                new SpecProbe("1.50", "ok raw=1.50 n=1"),
            ],
            Explanation = "Numbers are IEEE 754 Decimal128, so decimal fractions are exact (`0.1 + 0.2 == 0.3` is `1`) and ordinary arithmetic exposes the Decimal128-selected result quantum without canonicalizing it: `0.5 + 0.5` displays `1.0`, not `1`. Quantum affects display, not structural numeric equality; formatting never re-rounds the computed value.",
        },
        new()
        {
            Id = "division-decimal-quotient",
            Category = "arithmetic",
            Source = "1 / 3",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0.3333333333333333333333333333333333",
            ExpectedRaw = "0.3333333333333333333333333333333333",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Non-exact `/` quotients are correctly rounded 34-digit Decimal128 values; the Lean Int core truncates the quotient (`1 / 3 = 0` there) — the documented Int-core limitation in the lean/KatLang.lean numeric-model header, not the runtime contract.",
            Probes =
            [
                new SpecProbe("7 / 2", "ok raw=3.5 n=1"),
            ],
            Notes = "The truncating spellings stay cross-engine: see the Lean-comparable `integer-division-truncates` case for `div`/`mod`.",
            Explanation = "`/` returns the exact decimal quotient, correctly rounded to KatLang's 34 significant digits: `1 / 3` is `0.3333333333333333333333333333333333` and `7 / 2` is `3.5`. Use `div` for the truncated integer quotient.",
        },
        new()
        {
            Id = "nan-equality-vs-ordering",
            Category = "arithmetic",
            Source = "N = (-2) ^ 0.5\nN == (-3) ^ 0.5\nN < 1\nN <= 1\nN > 1\nN >= 1",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n0\n0\n0\n0",
            ExpectedRaw = "S[1, 0, 0, 0, 0]",
            ExpectedEmittedCount = 5,
            LeanExclusionReason = "NaN is a Decimal128 runtime value with no counterpart in the Lean Int numeric model; the equality-vs-ordering split (structural `==` treats NaN as one value, ordering comparisons follow IEEE and are false) is Decimal128-specific by construction.",
            Probes =
            [
                // Structural side: two INDEPENDENTLY computed NaN atoms are one
                // value (a same-property spelling like `N == N` would compare
                // the cached result against itself and never reach the atom
                // rule), so != is 0 and the collection consumers agree with ==.
                new SpecProbe("N = (-2) ^ 0.5\nN != (-3) ^ 0.5", "ok raw=0 n=1"),
                new SpecProbe("N = (-2) ^ 0.5\ncontains((1, N), (-3) ^ 0.5)", "ok raw=1 n=1"),
                new SpecProbe("N = (-2) ^ 0.5\ndistinct((N, (-3) ^ 0.5))", "ok raw=L[NaN] n=1"),
                // `order`/`orderDesc` use Decimal128's TOTAL order (NaN sorts
                // before every other value ascending), a third, deliberate
                // surface distinct from both `==` and the IEEE comparisons.
                new SpecProbe("N = (-2) ^ 0.5\norder((1, N, -1))", "ok raw=L[NaN, -1, 1] n=1"),
                new SpecProbe("N = (-2) ^ 0.5\norderDesc((1, N, -1))", "ok raw=L[1, -1, NaN] n=1"),
                // `min` canonically represents the NaN-propagating min/max
                // family; Decimal128NumericsTests pins `max` independently.
                new SpecProbe("N = (-2) ^ 0.5\nmin((3, N, 1))", "ok raw=NaN n=1"),
                // Truth testing: zero is false, every other atom — NaN
                // included — is true.
                new SpecProbe("N = (-2) ^ 0.5\nif(N, 1, 2)", "ok raw=1 n=1"),
            ],
            Notes = "`(-2) ^ 0.5` produces NaN through the operator surface alone (a fractional power of a negative base), keeping this case independent of the separately excluded Math-native surface. The equality, `contains`, and `distinct` rows deliberately compare SEPARATELY computed NaN values so each consumer reaches the structural atom rule instead of succeeding through the zero-arg property cache's reference identity.",
            Explanation = "NaN splits by operation: structural `==`/`!=` (also `contains`/`distinct`) treat NaN as ONE value, so two independently computed NaN results compare equal; the ordering operators follow IEEE, so every `<`/`>`/`<=`/`>=` involving NaN is `0`; and `order`/`orderDesc` sort by the total order, where NaN comes before every other value ascending. `min`/`max` propagate NaN, and NaN is truthy like every non-zero number.",
        },
        new()
        {
            Id = "overflow-produces-infinity",
            Category = "arithmetic",
            Source = "9e6144 * 10",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "Infinity",
            ExpectedRaw = "Infinity",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Lean's unbounded Int has no finite range and no Infinity value (`9e6144 * 10` is an ordinary integer there); Decimal128 overflow producing a signed infinity is runtime-only range behavior.",
            Probes =
            [
                new SpecProbe("(0 - 9e6144) * 10", "ok raw=-Infinity n=1"),
                // Non-finite operands then propagate by IEEE arithmetic:
                // Infinity - Infinity is NaN, never an error.
                new SpecProbe("9e6144 * 10 - 9e6144 * 10", "ok raw=NaN n=1"),
                // An infinity participates in IEEE ordering as the extreme.
                new SpecProbe("9e6144 * 10 > 9e6144", "ok raw=1 n=1"),
            ],
            Explanation = "Arithmetic past Decimal128's finite range (about ±1e6145) produces `Infinity`/`-Infinity` instead of erroring or clamping to a finite boundary, and the infinities then behave by IEEE rules: `Infinity - Infinity` is `NaN`, and an infinity compares beyond every finite value.",
        },
        new()
        {
            Id = "negative-zero-display",
            Category = "arithmetic",
            Source = "-0",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "-0",
            ExpectedRaw = "-0",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Decimal128 signed zero is outside the Lean Int numeric model: Int negation of zero is zero, so the Lean form of this program observes `0` where the runtime observes the sign-preserving `-0`.",
            Probes =
            [
                // One structural value: the sign never separates the zeros for
                // == or the hashed consumers, and IEEE ordering agrees.
                new SpecProbe("-0 == 0", "ok raw=1 n=1"),
                new SpecProbe("distinct((-0, 0))", "ok raw=L[-0] n=1"),
                // Zero-VALUED divisors keep the Lean-modeled error: signed zero
                // does NOT adopt the IEEE 1/-0 = -Infinity convention.
                new SpecProbe("1 / -0", "err div0"),
            ],
            Notes = "The canonical case keeps the representative signed-zero boundary: construction/display, structural equality (including the hashed `distinct` consumer), and the shared zero-divisor rule. Decimal128NumericsTests retains the denser relational, arithmetic-sign, and truthiness matrix.",
            Explanation = "`-0` (unary minus on zero — literals are unsigned) is an observable Decimal128 value: it displays with its sign while comparing structurally equal to `0`, and it remains a zero-valued divisor (`1 / -0` is the ordinary division-by-zero error, not `-Infinity`).",
        },
        new()
        {
            Id = "native-flat-callback-binding",
            Category = "collection-builtins",
            Source = "F(x) = [1, -2].map(abs)\nF(5)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2]",
            ExpectedRaw = "L[1, 2]",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Math natives (Expr.NativeCall) are a documented unmodeled gap in the Lean core; the counted-first native-argument lookup matches the modeled Expr.Param dual-view order.",
            Probes =
            [
                new SpecProbe("[1, -2].map(abs)", "ok raw=L[1, 2] n=1"),
                new SpecProbe("[1, -2].map(Math.Abs)", "ok raw=L[1, 2] n=1"),
                new SpecProbe("G(radians) = [0, 1].map(sin)\nG(0.5) == [sin(0), sin(1)]", "ok raw=1 n=1"),
                new SpecProbe("abs(-2)", "ok raw=2 n=1"),
                new SpecProbe("F(x, y) = reduce([2, 3], pow, 1)\nF(100, 200)", "ok raw=9 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A math function is an ordinary callable, so its lowercase alias, opened canonical name, and qualified `Math.X` spelling work directly as callbacks: the callback binds its own arguments and never captures same-named values from the surrounding algorithm — the ambient `x = 5` does not leak into `abs`. Direct calls such as `abs(-2)` are unchanged.",
        },
        new()
        {
            Id = "callable-argument-parameter-shadowing",
            Category = "access-boundaries",
            Source = "A = q + 1\nAdd1(x) = x + 1\nF(x) = Add1(A)\n\nF(7)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // The caller's parameter name is the ONLY difference, and it changes nothing.
                new SpecProbe("A = q + 1\nAdd1(x) = x + 1\nF(zz) = Add1(A)\nF(7)", "err arity"),
                // Patterned and item-supply callees take the same rule.
                new SpecProbe("A = q + 1\nP(x, (a, b)) = x + a\nF(x) = P(A, (1, 2))\nF(7)", "err arity"),
                new SpecProbe("A = q + 1\nC(x, *rest) = x + 1\nF(x) = C(A, 5)\nF(7)", "err arity"),
                // The callable argument is still invocable by name inside the callee.
                new SpecProbe("A = q + 1\nApply(x) = x(10)\nF(x) = Apply(A)\nF(7)", "ok raw=11 n=1"),
                // A nested property still reads its ancestor's parameter: shadowing removes
                // only the callee's OWN parameter names from the inherited environment.
                new SpecProbe("Outer(v) = Inner\n  Inner = v + 1\nOuter(7)", "ok raw=8 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Passing a callable binds the receiving parameter on the callable channel, not the value channel, so reading that parameter as a value asks the callable for a zero-argument value — an arity error here, because `A` still needs its implicit `q`. The callee never sees the caller's own `x`: a parameter always means the argument bound at this call, whatever the surrounding algorithm happens to name its parameters. Call the parameter (`x(10)`) to use it, or pass a value.",
        },
        new()
        {
            Id = "native-argument-value-demand",
            Category = "errors",
            Source = "Z = 1 / 0\n\nMath.Abs(Z)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "div0",
            LeanExclusionReason = "Math natives (Expr.NativeCall) are a documented unmodeled gap in the Lean core; the wrapper's declared-argument read is the modeled Expr.Param value read applied to a native body Lean does not represent.",
            Probes =
            [
                // A clause family has no value with zero arguments, so the ordinary
                // conditional value-access failure surfaces.
                new SpecProbe("C(0) = 1\nC(n) = 2\nMath.Abs(C)", "err branch"),
                // A builtin argument reports the builtin's own arity failure.
                new SpecProbe("Math.Abs(count)", "err arity"),
                // Where the reference's parameters CAN be inferred, the math argument is an
                // ordinary value position and the program simply works.
                new SpecProbe("A = q + 1\nF(q) = Math.Abs(A)\nF(7)", "ok raw=8 n=1"),
                // Ordinary value arguments are unchanged.
                new SpecProbe("F(x) = Math.Abs(x)\nF(0 - 9)", "ok raw=9 n=1"),
            ],
            Explanation = "A math function needs a VALUE, so its argument is read exactly like any other parameter: the value bound at this call, and otherwise whatever the bound callable yields with no arguments — here `Z`'s own division by zero. The failure is always about the argument, never about the math function's declared parameter name (`x`, `value`, `digits`, ...), which the program never binds.",
        },
        new()
        {
            Id = "closed-list-strict-value-forwarding",
            Category = "errors",
            Source = "A = q + 1\nF(x) = Math.Abs(A)\n\nF(7)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.UndeclaredIdentifier,
            ExpectedParseDiagnosticFragment = "producing that value needs the implicit parameter 'q'",
            // Probes observe values, so the REJECTED spellings of this rule (the alias
            // `abs(A)`, either argument position of `Math.Pow`) are pinned by
            // ClosedListStrictValueDiagnosticTests instead; what belongs here are the
            // controls proving the rule does not over-reject.
            Probes =
            [
                // Declaring the required parameter, or leaving the list open so it is
                // inferred, keeps the program legal.
                new SpecProbe("A = q + 1\nF(q) = Math.Abs(A)\nF(7)", "ok raw=8 n=1"),
                new SpecProbe("A = q + 1\nF = Math.Abs(A)\nF(7)", "ok raw=8 n=1"),
                // A bare reference is not a value demand, and an ordinary call's arguments
                // stay higher-order: neither is diagnosed.
                new SpecProbe("A = q + 1\nApply(f) = f(10)\nF(x) = Apply(A)\nF(7)", "ok raw=11 n=1"),
                new SpecProbe("F(x) = [0 - 1, 0 - 2].map(abs).sum\nF(9)", "ok raw=3 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "An explicit parameter list is closed, and that applies to what a value position needs indirectly as well as directly. `Math.Abs` needs `A`'s value, producing it needs `A`'s inferred `q`, and `F(x)` declares no `q` — so the program is rejected before it runs, naming `A` and `q` rather than the math function. Declare `q` in the list, call `A` with explicit arguments, or leave the list off so `q` is inferred. Passing `A` where a callable is wanted is unaffected: only a proven value demand is checked this way.",
        },
        new()
        {
            Id = "clause-family-nested-in-branch-body-binds-its-own-binders",
            Category = "conditionals",
            Source = "n = 99\nF(0) = {\n  G(0) = 'zero'\n  G(n) = n\n  G(5)\n}\nF(k) = k\n\nF(0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5",
            ExpectedRaw = "5",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // The identical family inside an ordinary brace block, and at the root.
                new SpecProbe("n = 99\nK = {\n  G(0) = 'zero'\n  G(n) = n\n  G(5)\n}\nK", "ok raw=5 n=1"),
                new SpecProbe("n = 99\nG(0) = 'zero'\nG(n) = n\nG(5)", "ok raw=5 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A clause family declared inside a conditional branch body is elaborated exactly like one declared in a brace block or at the root: `G(n) = n` binds its own pattern binder `n`, so `G(5)` is 5. The outer sibling `n = 99` is never consulted — a branch body is a scope-owning body under the same rules as every other body, not a weaker one.",
        },
        new()
        {
            Id = "conditional-branch-pattern-is-a-closed-input-specification",
            Category = "conditionals",
            Source = "A = x + 1\nF(0) = A\nF(n) = n\n\nF(0)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // A binder the pattern DOES bind supplies the referenced callable's implicit
                // parameter, without the body acquiring a parameter of its own.
                new SpecProbe("A = n + 1\nF(0) = 0\nF(n) = A\nF(4)", "ok raw=5 n=1"),
                // The same reference behind a closed explicit list fails the same way.
                new SpecProbe("A = x + 1\nF(k) = A\nF(0)", "err arity"),
            ],
            Explanation = "A conditional branch pattern is a closed input specification, like a written explicit parameter list: the branch body's only inputs are its pattern binders, and the front end never invents a body parameter to feed a referenced callable. `F(0) = A` therefore keeps `A` as a bare reference whose zero-argument value demand fails with the ordinary arity error, exactly as `F(k) = A` does — never with an `Unknown name` for a parameter nothing binds.",
        },
        new()
        {
            Id = "expression-position-block-closed-list-is-diagnosed",
            Category = "errors",
            Source = "{\n  F(x) = y\n  F(1)\n}",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.UndeclaredIdentifier,
            ExpectedParseDiagnosticFragment = "Identifier 'y' is used in an explicitly parameterized algorithm",
            Probes =
            [
                new SpecProbe("{\n  F(x) = x\n  F(1)\n}", "ok raw=1 n=1"),
            ],
            Explanation = "Brace blocks work in any expression position and are scope-owning bodies under the same rules as the root, so a closed explicit parameter list inside an output-position block reports its undeclared identifier at the front end exactly as the same declaration would at the root — it does not fall through to a runtime `Unknown name`.",
        },
        new()
        {
            Id = "conditional-branch-inline-open-exposes-members-to-the-branch",
            Category = "conditionals",
            Source = "F(0) = {\n  open {\n    public Helper = 5\n  }\n  Helper\n}\nF(n) = n\n\nF(0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5",
            ExpectedRaw = "5",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // The equivalent named open of an outer library makes the same decision.
                new SpecProbe("Helpers = {\n  public Helper = 5\n}\nF(0) = {\n  open Helpers\n  Helper\n}\nF(n) = n\nF(0)", "ok raw=5 n=1"),
                // A parameterized helper, and a branch binder handed to it as an explicit argument.
                new SpecProbe("F(0) = {\n  open {\n    public Helper(x) = x\n  }\n  Helper(5)\n}\nF(n) = n\nF(0)", "ok raw=5 n=1"),
                new SpecProbe("F(0) = 0\nF(n) = {\n  open {\n    public Helper(x) = x\n  }\n  Helper(n)\n}\nF(5)", "ok raw=5 n=1"),
                // The block is isolated from the opener like every open target: a bare name inside
                // it is the helper's own implicit parameter, so a bare reference to the helper is
                // the ordinary zero-argument arity failure — exactly as through the named open.
                new SpecProbe("F(0) = 0\nF(n) = {\n  open {\n    public Helper = n\n  }\n  Helper\n}\nF(5)", "err arity"),
                new SpecProbe("Helpers = {\n  public Helper = n\n}\nF(0) = 0\nF(n) = {\n  open Helpers\n  Helper\n}\nF(5)", "err arity"),
                // Outside the branch the name resolves to nothing: the enclosing algorithm treats
                // it as its own implicit parameter.
                new SpecProbe("Outer = {\n  F(0) = {\n    open { public Helper = 5 }\n    Helper\n  }\n  F(n) = n\n  F(0), Helper\n}\nOuter(7)", "ok raw=S[5, 7] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "An `open` target is a provider for the body that opens it, not a definition of that body. An inline block opened by a conditional branch therefore exposes its self-contained public members to that branch exactly as an equivalent named open of an outer library would — `Helper` is 5 inside `F(0)` — while the block lives only for that branch: sibling branches, the enclosing algorithm, and callers never see `Helper`. Properties DECLARED in the branch stay branch-local as before, and the branch pattern stays closed — a binder reaches an opened helper as an explicit argument, never as a captured name inside the block.",
        },
        new()
        {
            Id = "conditional-branch-inline-open-does-not-leak-to-sibling-branches",
            Category = "errors",
            Source = "F(0) = {\n  open {\n    public Helper = 5\n  }\n  Helper\n}\nF(1) = Helper\nF(n) = n\n\nF(1)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.UndeclaredIdentifier,
            ExpectedParseDiagnosticFragment = "Identifier 'Helper' is used in conditional branch 'F'",
            Probes =
            [
                // A sibling branch that declares the name itself is unaffected.
                new SpecProbe("F(0) = {\n  open {\n    public Helper = 5\n  }\n  Helper\n}\nF(1) = {\n  Helper = 6\n  Helper\n}\nF(n) = n\nF(1)", "ok raw=6 n=1"),
            ],
            Explanation = "Exposure through an inline open ends at the branch that wrote it: `F(1)` resolves through its own lookup chain, which never contains the first branch's open list, so its `Helper` is an undeclared identifier under the closed branch-pattern rule — the same diagnostic any other unbound name in a branch body receives.",
        },
        new()
        {
            Id = "conditional-branch-local-library-is-openable-within-the-branch",
            Category = "conditionals",
            Source = "F(0) = {\n  Lib = {\n    public X = 1\n  }\n  G = {\n    open Lib\n    X\n  }\n  G\n}\nF(n) = n\n\nF(0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1",
            ExpectedRaw = "1",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // A parameterized member, structural dot access inside the branch, a consumer two
                // bodies down, and an inner clause family's branch as the consumer.
                new SpecProbe("F(0) = {\n  Lib = {\n    public X(n) = n\n  }\n  G = {\n    open Lib\n    X(5)\n  }\n  G\n}\nF(n) = n\nF(0)", "ok raw=5 n=1"),
                new SpecProbe("F(0) = {\n  Lib = { public X = 1 }\n  Lib.X\n}\nF(n) = n\nF(0)", "ok raw=1 n=1"),
                new SpecProbe("F(0) = {\n  Lib = { public X = 1 }\n  G = {\n    H = {\n      open Lib\n      X\n    }\n    H\n  }\n  G\n}\nF(n) = n\nF(0)", "ok raw=1 n=1"),
                new SpecProbe("F(0) = {\n  Lib = { public X = 1 }\n  G(0) = {\n    open Lib\n    X\n  }\n  G(k) = k\n  G(0)\n}\nF(n) = n\nF(0)", "ok raw=1 n=1"),
                // A member capturing the branch binder is local-only exactly like a
                // parameter-capturing member, so `open Lib` hides it.
                new SpecProbe("F(0) = 0\nF(n) = {\n  Lib = { public X = n }\n  G = {\n    open Lib\n    X\n  }\n  G\n}\nF(5)", "err unknownName"),
                // By name, nothing declared in a branch is reachable from outside the family.
                new SpecProbe("F(0) = {\n  Lib = { public X = 1 }\n  Lib.X\n}\nF(n) = n\nF.Lib", "err localOnlyProperty"),
                new SpecProbe("Outer = {\n  F(0) = {\n    Lib = { public X = 1 }\n    G = {\n      open Lib\n      X\n    }\n    G\n  }\n  F(n) = n\n  F(0), X\n}\nOuter(7)", "ok raw=S[1, 7] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A library declared inside a conditional branch classifies exactly like one declared in a parameterized body: its self-contained public members are exported, so any body nested in that branch may `open` it (or reach its members with dot access) — `X` is 1 inside `G`. What stays branch-local is the declaration's reach by name: a conditional exposes no members of its branches, so `F.Lib` and `open F.Lib` are refused at the family, and a sibling branch or the enclosing algorithm never sees `Lib` or `X`. A member that captures the branch's pattern binder is local-only for the same reason a parameter-capturing member is.",
        },
        new()
        {
            Id = "conditional-branch-local-library-does-not-leak-to-sibling-branches",
            Category = "errors",
            Source = "F(0) = {\n  Lib = {\n    public X = 1\n  }\n  G = {\n    open Lib\n    X\n  }\n  G\n}\nF(1) = X\nF(n) = n\n\nF(1)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.UndeclaredIdentifier,
            ExpectedParseDiagnosticFragment = "Identifier 'X' is used in conditional branch 'F'",
            Probes =
            [
                // The sibling may declare and open a library of its own, and a branch body may
                // open its own declaration directly.
                new SpecProbe("F(0) = {\n  Lib = { public X = 1 }\n  G = {\n    open Lib\n    X\n  }\n  G\n}\nF(1) = {\n  open Lib\n  Lib = { public X = 2 }\n  X\n}\nF(n) = n\nF(1)", "ok raw=2 n=1"),
            ],
            Explanation = "A branch-local library is visible only inside the branch that declares it: the sibling branch `F(1)` resolves through its own lookup chain, which never contains the first branch's declarations, so its `X` is an undeclared identifier under the closed branch-pattern rule.",
        },
    ];
}
