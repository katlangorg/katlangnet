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
        "name-resolution",
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
            Id = "need-closed-core-demand-is-runtime",
            Category = "errors",
            Source = "A(q) = q + 1\nF(x) = A + 0\nF(7)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Explanation = "A closed body gains no q. Its resolved callable reference is legal, but an actual value demand rejects the ordinary zero-argument call to A(q).",
        },
        new()
        {
            Id = "need-unused-ordinary-argument",
            Category = "variadic-calls",
            Source = "F(x) = 10\nF(1 / 0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "10",
            ExpectedRaw = "10",
            ExpectedEmittedCount = 1,
            Explanation = "An ordinary non-spread argument is a suspended cell. The unused plain binder x never demands its value.",
        },
        new()
        {
            Id = "need-unused-collector-slice",
            Category = "variadic-calls",
            Source = "F(*xs) = 10\nF(1, 1 / 0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "10",
            ExpectedRaw = "10",
            ExpectedEmittedCount = 1,
            Explanation = "A collector stores a lazy slice. An unused slice does not demand its members.",
        },
        new()
        {
            Id = "need-forwarding-preserves-unused-cell",
            Category = "variadic-calls",
            Source = "G(x) = 10\nF(x) = G\nF(1 / 0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "10",
            ExpectedRaw = "10",
            ExpectedEmittedCount = 1,
            Explanation = "Bare forwarding transports the same parameter cell without forcing it.",
        },
        new()
        {
            Id = "need-collector-forwarding-preserves-unused-slice",
            Category = "variadic-calls",
            Source = "G(*xs) = 10\nF(*xs) = G\nF(1, 1 / 0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "10",
            ExpectedRaw = "10",
            ExpectedEmittedCount = 1,
            Explanation = "Re-spreading an existing collector transfers its member cells without materializing the slice.",
        },
        new()
        {
            Id = "need-ordinary-conditional-selects-one-cell",
            Category = "variadic-calls",
            Source = "Choose(true, yes, no) = yes\nChoose(false, yes, no) = no\nChoose(true, 7, 1 / 0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7",
            ExpectedRaw = "7",
            ExpectedEmittedCount = 1,
            Explanation = "An ordinary clause family forces its literal condition and then only the selected branch's value cell.",
        },
        new()
        {
            Id = "need-family-shares-failed-attempt-value",
            Category = "variadic-calls",
            Source = "F(0, x) = 7\nF(n, 0) = n\nF(3, 0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            Explanation = "Clause attempts reuse supplied cells. The first literal mismatch does not force its later binder.",
        },
        new()
        {
            Id = "need-first-loop-step-can-ignore-initial",
            Category = "variadic-calls",
            Source = "Step(x) = 7\nrepeat(Step, 1, 1 / 0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7",
            ExpectedRaw = "7",
            ExpectedEmittedCount = 1,
            Explanation = "The first loop step receives the suspended initial cell. A step that ignores it can produce the final state.",
        },
        new()
        {
            Id = "need-closed-demand-can-remain-unused",
            Category = "variadic-calls",
            Source = "A(q) = q + 1\nKeep(x) = 7\nF(x) = Keep(count(A))\nF(0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7",
            ExpectedRaw = "7",
            ExpectedEmittedCount = 1,
            Explanation = "A closed body gains no q, but an unused argument containing a zero-argument demand does not fail.",
        },
        new()
        {
            Id = "need-wrong-arity-precedes-cell-demand",
            Category = "variadic-calls",
            Source = "F(x) = x\nF(1 / 0, 2)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Explanation = "After explicit spread formation, wrong cardinality rejects before ordinary argument cells are demanded.",
        },
        new()
        {
            Id = "need-explicit-spread-precedes-arity",
            Category = "variadic-calls",
            Source = "F(x) = 7\nF(9, (1 / 0)*)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "div0",
            Explanation = "An arbitrary explicit spread must demand its operand to form supply, even when the resulting call would have wrong arity.",
        },
        new()
        {
            Id = "need-collector-demand-materializes-whole-slice",
            Category = "variadic-calls",
            Source = "F(*xs) = xs.first\nF(1, 1 / 0)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "div0",
            Explanation = "Demanding any value from a collector first materializes the full collected list left to right.",
        },
        new()
        {
            Id = "need-callable-projection-does-not-force-value",
            Category = "variadic-calls",
            Source = "Inc(x) = x + 1\nApply(f) = f(4)\nApply(Inc)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5",
            ExpectedRaw = "5",
            ExpectedEmittedCount = 1,
            Explanation = "A callable consumer projects Inc's identity without making a zero-argument value demand.",
        },
        new()
        {
            Id = "need-demand-order-decides-the-first-failure",
            Category = "errors",
            Source = "F(x, y) = y + x\nF(1 / 0, 'a' + 1)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Explanation = "Supplied arguments run in the order they are first demanded, not in written order. The body demands y first, so its type error is the failure the call reports, and the division by zero is never evaluated.",
        },
        new()
        {
            Id = "need-wrapper-keeps-builtin-if-selection",
            Category = "conditionals",
            Source = "MyIf(c, t, e) = if(c, t, e)\nApply3(f, a, b, c) = f(a, b, c)\nMyIf(true, 1, 1 / 0)\nApply3(if, false, 1 / 0, 2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 2,
            Explanation = "A wrapper's parameters are suspended computations that it passes on unevaluated, so builtin `if` reached through a user wrapper or a higher-order parameter still demands only its condition and the selected branch: the unselected `1 / 0` never runs.",
        },
        new()
        {
            Id = "need-container-call-checks-cardinality-first",
            Category = "errors",
            Source = "A = {\n    public X = 1\n}\nA(6)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Explanation = "A container has no parameters, so a call that supplies an argument fails its cardinality check before the body runs: the error is the arity mismatch, not the container's missing output.",
        },
        new()
        {
            Id = "need-collection-builtin-demands-its-collection-first",
            Category = "collection-builtins",
            Source = "take(1 / 0, 'a' + 1)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "div0",
            Explanation = "A collection builtin demands its collection first and then its controls, each validated before the next is demanded, so the collection's division by zero is the failure the call reports and the count `'a' + 1` is never evaluated.",
        },
        new()
        {
            Id = "need-dot-receiver-is-a-supplied-computation",
            Category = "variadic-calls",
            Source = "Second(a, b) = b\n(1 / 0).Second(2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2",
            ExpectedRaw = "2",
            ExpectedEmittedCount = 1,
            Explanation = "A dot call's receiver is the call's first argument, supplied like every argument: it runs only if the callee demands it. `Second` reads only `b`, so the receiver's division by zero never runs, exactly as in the written call `Second(1 / 0, 2)`.",
        },
        new()
        {
            Id = "need-dot-receiver-follows-callee-demand-order",
            Category = "variadic-calls",
            Source = "Flip(a, b) = b + a\n(1 / 0).Flip('a' + 1)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Explanation = "The receiver is not evaluated before the written arguments: the callee demands its cells in its own order. `Flip` demands `b` first, so the type error of `'a' + 1` is the failure reported and the receiver's division by zero never runs, as in the written call `Flip(1 / 0, 'a' + 1)`.",
        },
        new()
        {
            Id = "need-family-binder-keeps-the-callable",
            Category = "conditionals",
            Source = "Inc(x) = x + 1\nApp(f, 0) = 0\nApp(f, n) = f(n)\nR(z) = App(Inc, 5)\nR(0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "6",
            ExpectedRaw = "6",
            ExpectedEmittedCount = 1,
            Explanation = "A clause family demands only what its patterns inspect, and a binder keeps its argument's callable identity, so the selected clause can invoke `f` as `Inc`. The closed parameter list of `R` keeps `Inc` a callable argument; in a formula that infers its parameters a family argument is a value position, and a bare callable there would be lifted instead.",
        },
        new()
        {
            Id = "need-deconstruction-runs-on-first-target-demand",
            Category = "deconstruction",
            Source = "p, q = 1 / 0, 2\nI(f) = 0\nI(p), I(q)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0\n0",
            ExpectedRaw = "S[0, 0]",
            ExpectedEmittedCount = 2,
            Explanation = "A deconstruction's right-hand side runs on the first demand of one of its targets. Passing a target to a callee that never reads it is no demand, so the division by zero never runs and the program succeeds.",
        },
        new()
        {
            Id = "collected-callable-survives-explicit-respread",
            Category = "variadic-calls",
            Source = "Inc(x) = x + 1\nApply(f) = f(9)\nFwd(*fs) = Apply(fs*)\nFwd(Inc)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "10",
            ExpectedRaw = "10",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // The re-spread argument keeps its callable channel in a builtin callback slot too.
                new SpecProbe("Inc(x) = x + 1\nApplyFirst(*fs) = map([1, 2], fs*)\nApplyFirst(Inc)", "ok raw=L[2, 3] n=1"),
                // Collecting demands nothing: an unused collected function is never evaluated.
                new SpecProbe("Inc(x) = x + 1\nIgnore(*xs) = 1\nIgnore(Inc)", "ok raw=1 n=1"),
                // Reading the collected list evaluates every element: Inc's own zero-argument rejection.
                new SpecProbe("Inc(x) = x + 1\nCollect(*xs) = xs\nCollect(Inc)", "err arity"),
                // The unspread collector is one list value, never a function.
                new SpecProbe("Inc(x) = x + 1\nApply(f) = f(9)\nFwd(*fs) = Apply(fs)\nFwd(Inc)", "err notAnAlgorithm"),
                // An ordinary list built from the collector, then spread: building it evaluates Inc.
                new SpecProbe("Inc(x) = x + 1\nApply(f) = f(9)\nFwd(*fs) = Apply([fs*]*)\nFwd(Inc)", "err arity"),
                // A value never becomes callable by passing through a collector.
                new SpecProbe("Apply(f) = f(9)\nFwd(*fs) = Apply(fs*)\nFwd(5)", "err notAnAlgorithm"),
            ],
            Explanation = "A collecting parameter keeps the arguments it receives exactly as they were supplied, and re-spreading it with `fs*` hands those same arguments on. A function passed through `Fwd` therefore reaches `Apply` still callable: `Fwd(Inc)` means `Apply(Inc)`, which is 10. Collecting evaluates nothing, so an unused collected function or failing calculation never runs. Reading the collector as a value (`xs`) builds its list, which evaluates every element, so a function that needs an argument reports its own error there. The collected list itself is a value, not a function, and a value never becomes callable by passing through a collector.",
        },
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
            Id = "boolean-values-and-equality",
            Category = "arithmetic",
            Source = "true\nfalse\n[true, 1, false, 0]\ntrue == 1\n1 == true\nfalse != 0\n0 != false\ndistinct([true, 1, false, 0, true])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "true\nfalse\n[true, 1, false, 0]\nfalse\nfalse\ntrue\ntrue\n[true, 1, false, 0]",
            ExpectedRaw = "S[true, false, L[true, 1, false, 0], false, false, true, true, L[true, 1, false, 0]]",
            ExpectedEmittedCount = 8,
            IncludeInGeneratorPrompt = true,
            Explanation = "Booleans are a distinct scalar kind. Equality is total and symmetric across kinds, with no Boolean/number conversion; lists, sequences, and distinct preserve that distinction.",
        },
        new()
        {
            Id = "boolean-predicates-and-patterns",
            Category = "conditionals",
            Source = "F(true) = false\nF(false) = true\nF(true)\nF(false)\nrange(-2, 2).filter{x >= 0}\nrange(-2, 2).map{x >= 0}.contains(true)\nif(not 1 == 1, 10, 20)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "false\ntrue\n[0, 1, 2]\ntrue\n20",
            ExpectedRaw = "S[false, true, L[0, 1, 2], true, 20]",
            ExpectedEmittedCount = 5,
            IncludeInGeneratorPrompt = true,
            Explanation = "Comparisons and contains produce Booleans. Predicate consumers require them, and true/false in clause heads are literal patterns, never parameter names.",
        },
        new()
        {
            Id = "boolean-loop-state-transition",
            Category = "conditionals",
            Source = "S(x) = if(x == true, 0, true), x != 0\nS.while(true)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0",
            ExpectedRaw = "0",
            ExpectedEmittedCount = 1,
            Explanation = "Loop state may change value kind. The continuation is Boolean, and a false continuation returns the current state without committing the proposed next state.",
        },
        new()
        {
            Id = "boolean-predicate-rejects-visible-empty",
            Category = "conditionals",
            Source = "F(x) = true, ()\nrange(0, 2).filter(F).count",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Explanation = "A predicate must return one Boolean value. A Boolean beside a visible empty output is a sequence, and cannot be searched or flattened for a truth value.",
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
                // `not` binds below `^` as well: `not 0 ^ 0` is `not (0 ^ 0)`, and
                // the Boolean-operand rejection it reports names the exponentiation
                // result (`1`), never the base `0` a `(not 0) ^ 0` parse would reject.
                new SpecProbe("not 0 ^ 0", "err type"),
                // A parenthesized Boolean exponent is rejected by `^` itself; the bare
                // `2 ^ not false` is a parse error, because `not` — below the
                // comparisons — can never be an operand of `^` (see
                // not-binds-below-comparisons).
                new SpecProbe("2 ^ (not false)", "err type"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`^` binds tighter than prefix `-` on the left (and than `not`, which sits below the comparisons altogether), so `-2 ^ 2` negates the power: `-(2 ^ 2)`. Parenthesize the base to raise a negative value: `(-2) ^ 2`. The exponent side accepts a unary value directly (`2 ^ -2` is `0.25`), and `^` chains group from the right.",
        },
        new()
        {
            Id = "not-binds-below-comparisons",
            Category = "arithmetic",
            Source = "not 5 > 3\nnot 2 > 3\nnot 5 == 5\nnot 5 == 4\nnot true == false\nnot true == 1",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "false\ntrue\nfalse\ntrue\ntrue\ntrue",
            ExpectedRaw = "S[false, true, false, true, true, true]",
            ExpectedEmittedCount = 6,
            Probes =
            [
                // Every comparison operator is negated as a whole.
                new SpecProbe("not 5 < 3", "ok raw=true n=1"),
                new SpecProbe("not 3 <= 3", "ok raw=false n=1"),
                new SpecProbe("not 2 >= 3", "ok raw=true n=1"),
                new SpecProbe("not 5 != 4", "ok raw=false n=1"),
                // Arithmetic and powers inside the comparison bind tighter still.
                new SpecProbe("not 1 + 1 > 3", "ok raw=true n=1"),
                new SpecProbe("not 2 ^ 3 > 7", "ok raw=false n=1"),
                // `not` binds tighter than `and`/`xor`/`or`: `not A and B` is
                // `(not A) and B` (`not (A and B)` would be true here), and
                // `not A or B` is `(not A) or B` (`not (A or B)` would be false).
                new SpecProbe("A = false\nB = false\nnot A and B", "ok raw=false n=1"),
                new SpecProbe("A = true\nB = true\nnot A or B", "ok raw=true n=1"),
                new SpecProbe("not 1 > 2 and 2 > 1", "ok raw=true n=1"),
                // Nested negation.
                new SpecProbe("not not 5 > 3", "ok raw=true n=1"),
                // Explicit parentheses keep the other grouping: the negation itself is
                // compared, which is a type error against a number.
                new SpecProbe("(not true) == false", "ok raw=true n=1"),
                new SpecProbe("(not true) > 3", "err type"),
                new SpecProbe("(not 5) > 3", "err type"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Comparisons bind tighter than `not`, and `not` binds tighter than `and`, `xor`, and `or` (comparisons > not > and > xor > or), so `not x > 3` negates the whole comparison — it is `not (x > 3)` — and `not a and b` is `(not a) and b`. Parentheses override the rule: `(not x) > 3` compares the negation itself, a type error for a numeric `x`. A `not` can only begin an operand of a logical operator or a whole expression; `1 + not x` and `2 ^ not x` are parse errors, so parenthesize the negation there.",
        },
        new()
        {
            Id = "comparison-chains-compare-adjacent-pairs",
            Category = "arithmetic",
            Source = "1 < 2 < 3\n1 < 2 <= 2 == 2 != 3\n1 == 1 == 1\n1 != 2 != 1\n1 != 1 != 1\n3 < 2 < 1\n1 == 1 < 2\n1 < 2 == true",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "true\ntrue\ntrue\ntrue\nfalse\nfalse\ntrue\nfalse",
            ExpectedRaw = "S[true, true, true, true, false, false, true, false]",
            ExpectedEmittedCount = 8,
            Probes =
            [
                // Parentheses are expression boundaries: a parenthesized chain is an
                // ordinary Boolean operand and never merges into the outer chain.
                new SpecProbe("(1 < 2) == true", "ok raw=true n=1"),
                new SpecProbe("1 == (1 < 2)", "ok raw=false n=1"),
                new SpecProbe("(1 < 2) == (3 < 4)", "ok raw=true n=1"),
                new SpecProbe("(1 < 2 < 3) == true", "ok raw=true n=1"),
                new SpecProbe("1 == (2 < 3 < 4)", "ok raw=false n=1"),
                new SpecProbe("1 < (2 == 2)", "err type"),
                new SpecProbe("(1 == 1) < 2", "err type"),
                // The surrounding tiers: `not` below the chain, the logical operators below
                // `not`, arithmetic above the chain.
                new SpecProbe("not 1 < 2 < 3", "ok raw=false n=1"),
                new SpecProbe("1 < 2 < 3 and 4 < 5", "ok raw=true n=1"),
                new SpecProbe("1 + 1 < 3 * 1 <= 4 - 1", "ok raw=true n=1"),
                new SpecProbe("-2 ^ 2 < -3 < 0", "ok raw=true n=1"),
                // A middle link that is false makes the chain false; equality and ordering
                // mix freely on the same operands.
                new SpecProbe("1 < 3 < 2 < 4", "ok raw=false n=1"),
                new SpecProbe("1 <= 1 == 1", "ok raw=true n=1"),
                new SpecProbe("1 < 1 == 1", "ok raw=false n=1"),
                // Structural equality chains over strings and sequence values.
                new SpecProbe("'a' == 'a' == 'a'", "ok raw=true n=1"),
                new SpecProbe("(1, 2) == (1, 2) != (2, 1)", "ok raw=true n=1"),
                // Booleans are not ordered, in a chain exactly as alone.
                new SpecProbe("true < false", "err type"),
                new SpecProbe("1 < 2 < 3 < true", "err type"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "The six comparison operators form ONE chainable precedence tier (September 2026): consecutive unparenthesized comparisons are one `Expr.comparison` chain with adjacent-pair links, evaluated incrementally with every operand exactly once. Before this change equality bound looser than ordering, so `1 == 1 < 2` read `1 == (1 < 2)` (false) and `1 < 2 < 3` ordered a Boolean against a number (an error).",
            Explanation = "All six comparison operators share one precedence tier and CHAIN: `a < b <= c == d != e` compares the adjacent pairs `a < b`, `b <= c`, `c == d`, and `d != e`, and the whole chain is `true` only when every pair holds. Each operand is evaluated once, left to right. `1 != 2 != 1` is `true` (adjacent pairs, not \"all distinct\"), `1 == 1 < 2` is `true`, and `1 < 2 == true` compares `2` with `true` (false). Parentheses break a chain: `(1 < 2) == true` compares the Boolean result of the group.",
        },
        new()
        {
            Id = "comparison-chain-boolean-and-arithmetic-operands",
            Category = "arithmetic",
            Source = "true == true == true\ntrue != false != true\ntrue == 1 == false\ntrue == true == false\n1 + 1 < 3 == 2 + 0\n-2 ^ 2 < 0 == true",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "true\ntrue\nfalse\nfalse\nfalse\nfalse",
            ExpectedRaw = "S[true, true, false, false, false, false]",
            ExpectedEmittedCount = 6,
            Explanation = "Comparisons use adjacent operand values even across Boolean/numeric kinds; arithmetic and power bind inside operands. The Boolean result accumulated by a chain never becomes an operand of its next link.",
        },
        new()
        {
            Id = "comparison-chain-is-eager-after-false",
            Category = "errors",
            Source = "3 < 2 < true",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Probes =
            [
                // A later operand's own error still surfaces after an earlier false link...
                new SpecProbe("3 < 2 < 1 / 0", "err div0"),
                new SpecProbe("1 == 2 == 1 / 0", "err div0"),
                // ...while an EARLIER operand or link error stops the chain before any later
                // operand: the earlier failure is the outcome.
                new SpecProbe("1 / 0 < true < 1", "err div0"),
                new SpecProbe("1 < true < 1 / 0", "err type"),
                new SpecProbe("'a' < 'b' < 1 / 0", "err type"),
                // A later operand that would fail at evaluation is never reached.
                new SpecProbe("1 < true < (1 / 0)", "err type"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Eager Boolean composition, like `and`/`or`: `false` never short-circuits a chain, so `3 < 2 < true` still compares `2 < true` and reports that link's ordering rejection (`while evaluating `2 < true``). Errors do terminate: an error in an earlier operand or link is the chain's outcome and later operands are not evaluated. Lean `evalComparisonCounted` / C# `EvalExpressionSpineCounted`.",
            Explanation = "A `false` comparison never stops a chain — like `and` and `or`, comparison chains evaluate eagerly — so `3 < 2 < true` still performs `2 < true`, and that comparison is the error (Booleans are not ordered). Errors do stop a chain: once an operand or a comparison fails, the later operands are not evaluated.",
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
                // BOTH numeric models (Lean `negativeIntPow`, C# `EvalPow`). The
                // runtime rule covers EVERY negative exponent — see the C#-only
                // `pow-zero-base-negative-exponent` case for the fractional side.
                new SpecProbe("0 ^ -1", "err illegalInEval"),
            ],
            Notes = "Shared Lean-modeled law on these common exact integer operands: `div`/`mod` truncate toward zero (Lean `Int.tdiv`/`Int.tmod`; C# `Decimal128Numerics.IntegerDivide`/`%`). Since G-3 the C# `div` truncates the EXACT quotient and is exact wherever the truncated quotient is representable — see `integer-division-exact-quotient`; only a truncated quotient that needs more than 34 significant digits is a Decimal128 precision boundary (the C#-only `integer-division-beyond-consecutive-integers`). Contrast the C#-only `division-decimal-quotient` case, where a non-exact `/` result diverges from the Int core by design.",
            Explanation = "Integer division `div` and remainder `mod` truncate toward zero: `-7 div 2` is `-3` and `-7 mod 2` is `-1`. These representative exact integer operations are cross-engine semantics shared with the Lean core model; Decimal128 precision remains a boundary only when the truncated quotient itself needs more than 34 significant digits.",
        },
        new()
        {
            Id = "integer-division-exact-quotient",
            Category = "arithmetic",
            Source = "X = 8999999999999999999999999999999999\nX div 3\nX mod 3\nX == 3 * (X div 3) + (X mod 3)\nY = 3e32\n(13 * Y - 1) div Y\n(12 * Y + 1) div Y\n-X div 3\nX div -3\n-X div -3\n1e34 div 7\n1e34 mod 7\n1e40 div 1e5",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2999999999999999999999999999999999\n2\ntrue\n12\n12\n-2999999999999999999999999999999999\n-2999999999999999999999999999999999\n2999999999999999999999999999999999\n1428571428571428571428571428571428\n4\n100000000000000000000000000000000000",
            ExpectedRaw = "S[2999999999999999999999999999999999, 2, true, 12, 12, -2999999999999999999999999999999999, -2999999999999999999999999999999999, 2999999999999999999999999999999999, 1428571428571428571428571428571428, 4, 100000000000000000000000000000000000]",
            ExpectedEmittedCount = 11,
            Probes =
            [
                // The small-quotient landing: the IEEE quotient of (13·3e32 − 1) / 3e32
                // is visibly 13.000…0 while the truncated quotient is 12; the mirror
                // image ABOVE the integer lands down on 12 and must not be adjusted.
                new SpecProbe("Y = 3e32\nX = 13 * Y - 1\nX div Y", "ok raw=12 n=1"),
                new SpecProbe("Y = 3e32\nX = 12 * Y + 1\nX div Y", "ok raw=12 n=1"),
                // The rounded quotient …429 times 7 rounds back to exactly 1e34: a
                // rounded-product exactness test would be fooled.
                new SpecProbe("10000000000000000000000000000000000 div 7", "ok raw=1428571428571428571428571428571428 n=1"),
                new SpecProbe("10000000000000000000000000000000000 mod 7", "ok raw=4 n=1"),
                // Every sign combination truncates toward zero; the remainder keeps
                // the dividend's sign.
                new SpecProbe("-8999999999999999999999999999999999 div 3", "ok raw=-2999999999999999999999999999999999 n=1"),
                new SpecProbe("8999999999999999999999999999999999 div -3", "ok raw=-2999999999999999999999999999999999 n=1"),
                new SpecProbe("-8999999999999999999999999999999999 div -3", "ok raw=2999999999999999999999999999999999 n=1"),
                new SpecProbe("-8999999999999999999999999999999999 mod 3", "ok raw=-2 n=1"),
                // Digit extraction at the consecutive-integer boundary stays exact.
                new SpecProbe("9999999999999999999999999999999999 div 10\n9999999999999999999999999999999999 mod 10", "ok raw=S[999999999999999999999999999999999, 9] n=2"),
                // A sparse representable quotient beyond the boundary is exact too.
                new SpecProbe("1e40 div 1e5", "ok raw=100000000000000000000000000000000000 n=1"),
            ],
            Notes = "Shared Lean-modeled law (G-3, September 2026): `div` is the EXACT quotient truncated toward zero (Lean `Int.tdiv`; C# `Decimal128Numerics.IntegerDivide`), returned exactly whenever the truncated quotient is representable — throughout the exact consecutive-integer domain |q| <= 10^34 (every such integer is a Decimal128) — and `mod` is the exact remainder for finite operands and a nonzero divisor (`Int.tmod`; Decimal128 `%`). The mathematical identity holds for representable truncated quotients; its KatLang recomposition also requires exact intermediate arithmetic. The former C# rule `Decimal128.Truncate(x / y)` truncated a quotient ALREADY rounded to 34 significant digits and answered `3000000000000000000000000000000000` here (and `13` for the first probe), silently one integer away while Lean was right all along. Beyond the domain see the C#-only `integer-division-beyond-consecutive-integers` case.",
            Explanation = "`div` truncates the exact quotient, not a quotient that was first rounded to 34 digits: `8999999999999999999999999999999999 div 3` is `2999999999999999999999999999999999` (while `/` rounds that quotient to `3000000000000000000000000000000000`), `mod` is the exact remainder `2`, and `x == y * (x div y) + (x mod y)` holds when the truncated quotient is representable and the intermediate arithmetic is exact. Every integer with magnitude at most 10^34 is representable, as are sparse larger integers.",
        },
        new()
        {
            Id = "integer-division-beyond-consecutive-integers",
            Category = "arithmetic",
            Source = "1e40 div 7\n1e40 / 7",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1428571428571428571428571428571428000000\n1428571428571428571428571428571429000000",
            ExpectedRaw = "S[1428571428571428571428571428571428000000, 1428571428571428571428571428571429000000]",
            ExpectedEmittedCount = 2,
            LeanExclusionReason = "The truncated quotient 1428571428571428571428571428571428571428 has 40 significant digits, so it is not a Decimal128: the runtime rounds it TOWARD ZERO to its leading 34 digits (`div` stays a truncation), while the Lean Int core returns the exact 40-digit integer — Decimal128 precision is the documented model divergence (and `1e40 / 7`, correctly rounded to nearest, diverges from the Int core's truncating `/` as well).",
            Probes =
            [
                // Toward zero, never to nearest: an exact 35-digit quotient ending in
                // 5 is a round-to-nearest TIE, and 2e40 / 3 would round up to …667.
                new SpecProbe("99999999999999999999999999999999990 div 6", "ok raw=16666666666666666666666666666666660 n=1"),
                new SpecProbe("2e40 div 3", "ok raw=6666666666666666666666666666666666000000 n=1"),
                new SpecProbe("-2e40 div 3", "ok raw=-6666666666666666666666666666666666000000 n=1"),
                // The quotient rounds toward zero and the product rounds monotonically,
                // so (x div y) * y never exceeds x.
                new SpecProbe("X = 1e40\n(X div 7) * 7 <= X", "ok raw=true n=1"),
                // A representable sparse quotient beyond the boundary stays exact.
                new SpecProbe("9999999999999999999999999999999999e10 div 3", "ok raw=33333333333333333333333333333333330000000000 n=1"),
                // Beyond the finite range the quotient overflows to a signed infinity
                // like every other arithmetic overflow (never saturates to the maximum).
                new SpecProbe("5 div 1e-6176", "ok raw=Infinity n=1"),
            ],
            Notes = "Decimal128 has 34 significant decimal digits. |n| <= 10^34 is KatLang's exact CONSECUTIVE-integer domain (10^34 + 1 is the first integer that is not a Decimal128); larger sparse integers such as 1e40 or 3333…3e10 are still exactly representable, so this boundary is not the largest representable integer. A truncated `div` quotient that needs more than 34 significant digits is rounded toward zero to 34 digits — the largest-magnitude Decimal128 integer not exceeding it — never to nearest. When IEEE division remains finite, `div` stays a truncation and, for finite operands and a nonzero divisor, `(x div y) * y` never exceeds `x` in magnitude even after the product rounds; `/` stays correctly rounded to nearest. The mathematical identity requires a representable truncated quotient; its KatLang recomposition also requires exact intermediate arithmetic. `mod` is exact for finite operands and a nonzero divisor. IEEE division overflow still produces signed infinity.",
            Explanation = "Beyond 34 significant digits `div` keeps the leading 34 digits of the exact truncated quotient, rounding toward zero rather than to nearest: `1e40 div 7` is `1428571428571428571428571428571428000000`, while `1e40 / 7` correctly rounds to `…429000000`. For finite quotients, `div` therefore never exceeds the true quotient in magnitude, for either sign; an exactly representable quotient such as `1e40 div 1e5` stays exact. IEEE overflow still produces signed infinity.",
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
                new SpecProbe("() == (())", "ok raw=true n=1"),
            ],
            Explanation = "Redundant parentheses around `()` are one written grouping level that normalizes away: `(())` is the same value as `()`.",
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
            Explanation = "Sequence normalization is not depth-limited: `((()))` is still `()`.",
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
                new SpecProbe("(7) == 7", "ok raw=true n=1"),
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
            Source = "() == ()      # true\n() == (())    # true\n() != (())    # false\ncount(())     # 0\ncount((()))   # 0",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "true\ntrue\nfalse\n0\n0",
            ExpectedRaw = "S[true, true, false, 0, 0]",
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
                new SpecProbe("A = ()\nA == ()", "ok raw=true n=1"),
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
            Id = "not-cannot-be-a-tighter-operand",
            Category = "parser-layout",
            Source = "2 ^ not false",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Unexpected 'not'",
            ExpectedDiagnosticCode = DiagnosticCode.UnexpectedToken,
            IncludeInGeneratorPrompt = true,
            Notes = "Source-level precedence diagnostic (see not-binds-below-comparisons); no elaborated Lean program exists. Recovery parses the negation as if parenthesized, so later diagnostics see the tree of `2 ^ (not false)`.",
            Explanation = "`not` binds below the comparisons (comparisons > not > and > xor > or), so it can begin only a whole expression or an operand of `and`, `xor`, or `or`. Where a comparison, arithmetic, power, or prefix-minus operand is required — `2 ^ not x`, `1 + not x`, `a == not b`, `-not x` — the parser reports the `not` and asks for parentheses: `2 ^ (not x)`, `a == (not b)`.",
        },
        new()
        {
            Id = "same-line-slots-need-comma",
            Category = "parser-layout",
            Source = "1 2 3",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Unexpected item after a closed expression on the same line",
            ExpectedDiagnosticCode = DiagnosticCode.UnseparatedSameLineItem,
            IncludeInGeneratorPrompt = true,
            Notes = "SYN-07A retired the implicit same-line comma (`adjacency-is-comma` used to pin `1 2 3` as `1, 2, 3`). Source-level separator diagnostic; the recovered AST is that of `1, 2, 3`, but no elaborated Lean program exists for a rejected parse.",
            Explanation = "Whitespace never separates slots: two slots on one physical line need an explicit comma (`1, 2, 3`), while a newline separates rows where the context permits (`1` newline `2` newline `3`). `1 2 3` reports the separator diagnostic once per missing comma, at the second item.",
        },
        new()
        {
            Id = "same-line-call-arguments-need-comma",
            Category = "parser-layout",
            Source = "F(a, b) = a + b\nF(1 2)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Unexpected item after a closed expression on the same line",
            ExpectedDiagnosticCode = DiagnosticCode.UnseparatedSameLineItem,
            IncludeInGeneratorPrompt = true,
            Notes = "Source-level SYN-07A separator diagnostic; no elaborated Lean program exists. Recovery keeps the two argument slots, so later diagnostics see the call `F(1, 2)`.",
            Explanation = "Argument slots are separated by commas: `F(1, 2)` is the two-argument call, `F(1 2)` is rejected at `2`, and `F(1 -2)` is one argument (the subtraction `1 - 2`) because a same-line operator continues the expression before any slot boundary is considered.",
        },
        new()
        {
            Id = "same-line-declaration-begins-a-line",
            Category = "parser-layout",
            Source = "x = 3 y = 4\nx + y",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Unexpected item after a closed expression on the same line",
            ExpectedDiagnosticCode = DiagnosticCode.UnseparatedSameLineItem,
            IncludeInGeneratorPrompt = true,
            Notes = "Source-level SYN-07A declaration-row diagnostic; no elaborated Lean program exists. Recovery keeps `y = 4` a declaration (never swallowed into x's body), so `x + y` still resolves both names.",
            Explanation = "A declaration begins a physical line (or is the first item directly after `{`). `x = 3 y = 4` is rejected at `y`; write the two definitions on separate lines. The same rule rejects `1 P = 3` and the one-line block `{ d = 2 n * d }`, so a missing line break can never silently move a declaration or an expression into the preceding definition's body.",
        },
        new()
        {
            Id = "same-line-slot-before-spread-needs-comma",
            Category = "parser-layout",
            Source = "A = (1, 2)\nB = (3, 4)\nA B*",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Unexpected item after a closed expression on the same line",
            ExpectedDiagnosticCode = DiagnosticCode.UnseparatedSameLineItem,
            Notes = "Source-level SYN-07A separator diagnostic; no elaborated Lean program exists. SYN-07B star classification is unchanged: `B*` is still the spread marker, only the missing comma before it is rejected.",
            Explanation = "A slot before a spread needs the comma like every other same-line slot: `A, B*` supplies `A` and then B's items, while `A B*` is rejected at `B`. The comma after a spread is required for a second reason as well (`B* C` is the multiplication `B * C`).",
        },
        new()
        {
            Id = "same-line-parameter-patterns-need-comma",
            Category = "parser-layout",
            Source = "F(a b) = a + b\nF(1, 2)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Unexpected item after a parameter pattern on the same line",
            ExpectedDiagnosticCode = DiagnosticCode.UnseparatedSameLineItem,
            IncludeInGeneratorPrompt = true,
            Notes = "Source-level SYN-07A separator diagnostic for parameter-pattern lists (clause heads and nested sequence-value patterns); no elaborated Lean program exists. Recovery keeps `b` a parameter of F — the head recovers as `F(a, b)` — so `a + b` stays F's body and nothing leaks into the root as output rows or implicit parameters.",
            Explanation = "Parameter lists are comma-separated like every other same-line list: `F(a, b) = a + b` declares two parameters, while `F(a b) = a + b` is rejected once, at `b`, with the pattern-list report (inside a parameter list the comma is the only repair). The same rule covers literal, nested, and collecting patterns: `F(1 2) = 3`, `F((a b)) = a`, and `F(a, *b c) = a` are each rejected at their unseparated item.",
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
                new SpecProbe("A = 1, 2, 3\nA == (1, 2, 3)", "ok raw=true n=1"),
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
            Probes =
            [
                // A multi-row body is observed as ONE value at any call boundary.
                new SpecProbe("F = 1, 2\nG(x) = x.count\nG(F())", "ok raw=2 n=1"),
                // `()` is a value, so a body whose output is `()` returns exactly that ...
                new SpecProbe("Empty = ()\nEmpty()", "ok raw=S[] n=1"),
                // ... while a body with no output rows has nothing to return: an error, never a silent `()`.
                new SpecProbe("Nothing = {}\nNothing()", "err missingOutput"),
                // Higher-order consumers add their own contract: a map callback must return exactly one element.
                new SpecProbe("D(x) = x, x\n[1].map(D)", "err arity"),
                // A completed loop is a value boundary too (Q-26): the finished multi-slot loop is ONE value at the root ...
                new SpecProbe("Step = a + 1, b + 1\nStep.repeat(1, 0, 0)", "ok raw=S[1, 1] n=1"),
                // ... exactly as through an ordinary property boundary ...
                new SpecProbe("Step = a + 1, b + 1\nR = Step.repeat(1, 0, 0)\nR", "ok raw=S[1, 1] n=1"),
                // ... and only the explicit spread opens it into items.
                new SpecProbe("Step = a + 1, b + 1\nStep.repeat(1, 0, 0)*", "ok raw=S[1, 1] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A call returns exactly one value — here the collected list `[5, 9]` — and only the explicit caller-site spread `value*` opens it back into the surrounding item supply.",
        },
        new()
        {
            Id = "loop-result-is-one-value",
            Category = "item-supply-vs-value",
            Source = "Fibonacci(a, b) = b, a + b\nFibonacci.repeat(10, 0, 1)\nFibonacci.repeat(10, 0, 1)*,\nFibonacci.repeat(10, 0, 1), 7",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(55, 89)\n55\n89\n(55, 89)\n7",
            ExpectedRaw = "S[S[55, 89], 55, 89, S[55, 89], 7]",
            ExpectedEmittedCount = 5,
            Probes =
            [
                // The same one value through a property ...
                new SpecProbe("Fibonacci(a, b) = b, a + b\nX = Fibonacci.repeat(10, 0, 1)\nX", "ok raw=S[55, 89] n=1"),
                // ... and through `while`: the final two-slot state is one value too.
                new SpecProbe("Cd(n, acc) = n - 1, acc + n, n > 1\nwhile(Cd, 3, 0)", "ok raw=S[1, 5] n=1"),
                // A zero-slot final state is the one visible value `()`; its spread supplies nothing.
                new SpecProbe("Drop(*xs) = { ()* }\nrepeat(Drop, 1, 1), repeat(Drop, 1, 1)*", "ok raw=S[] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A completed `repeat`/`while` is ONE value, like every call result: the two final state slots come back as the one value `(55, 89)` — one row alone or beside other rows — and only the explicit spread `…*` opens it into separate items.",
        },
        new()
        {
            Id = "loop-step-patterns-only-bind",
            Category = "item-supply-vs-value",
            Source = "Dup(x, x) = { (x + 1, x + 1)* }\nSame(x, x) = { x + 1, x + 1 }\nStep((a, b)) = (b, a + b)\nDup.repeat(2, 1, 1), Same.repeat(2, 1, 1), Step.repeat(3, (0, 1))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(3, 3)\n(3, 3)\n(2, 3)",
            ExpectedRaw = "S[S[3, 3], S[3, 3], S[2, 3]]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // A structural step's spread row supplies TWO slots, which its one-pattern head cannot re-bind.
                new SpecProbe("Step2((a, b)) = { (b, a + b)* }\nStep2.repeat(3, (0, 1))", "err arity"),
                // Diverging rows of a repeated-name step fail the NEXT binding, like the direct call `Dup(2, 3)`.
                new SpecProbe("Dup(x, x) = { x + 1, x + 2 }\nDup.repeat(2, 1, 1)", "err arity"),
                // An exact list keeps a growing history as ONE slot.
                new SpecProbe("Grow([*h], n) = [h*, n], n + 1\nGrow.repeat(3, [], 0):0", "ok raw=L[0, 1, 2] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A loop step's parameter patterns only bind the incoming state; its rows — with `*` opening a value, as everywhere — are the next state. `Dup`'s spread row supplies the same two slots as `Same`'s two rows, and `Step` keeps its pair as ONE slot by writing one value.",
        },
        new()
        {
            Id = "loop-nested-step-row-is-one-slot",
            Category = "item-supply-vs-value",
            Source = "Fibonacci(a, b) = b, a + b\nTwo(a, b) = { repeat(Fibonacci, 2, a, b)* }\nTwo.repeat(3, 0, 1)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(8, 13)",
            ExpectedRaw = "S[8, 13]",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // Unspread, the inner loop is ONE next-state slot, which `Two(a, b)` cannot re-bind ...
                new SpecProbe("Fibonacci(a, b) = b, a + b\nTwo(a, b) = repeat(Fibonacci, 2, a, b)\nTwo.repeat(3, 0, 1)", "err arity"),
                // ... exactly as a helper returning the same loop.
                new SpecProbe("Fibonacci(a, b) = b, a + b\nInner(a, b) = repeat(Fibonacci, 2, a, b)\nTwo(a, b) = { Inner(a, b)* }\nTwo.repeat(3, 0, 1)", "ok raw=S[8, 13] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A nested loop written as a step row is ONE next-state slot, like any call result; spread it with `*` to supply its final items as the next state.",
        },
        new()
        {
            Id = "loop-step-clause-family",
            Category = "conditionals",
            Source = "Step(0) = 0\nStep(n) = n - 1\nrepeat(Step, 2, 3), Step.repeat(5, 3), Step(Step(3))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n0\n1",
            ExpectedRaw = "S[1, 0, 1]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // A wrong state arity is the family's own ordinary arity failure.
                new SpecProbe("Step(0) = 0\nStep(n) = n - 1\nrepeat(Step, 1, 1, 2)", "err arity"),
                // The selected clause's ROWS are the next state: two rows are two slots.
                new SpecProbe("Two(0) = 9, 9\nTwo(n) = n, n\nrepeat(Two, 2, 1)", "err arity"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A loop step is an ordinary callable: each iteration invokes a clause family exactly as the call `Step(state…)` would — ordinary clause dispatch over the current state — and the selected clause's rows become the next state, so `repeat(Step, 2, 3)` is `Step(Step(3))`.",
        },
        new()
        {
            Id = "loop-step-family-while",
            Category = "conditionals",
            Source = "Countdown(0) = 0, false\nCountdown(n) = n - 1, true\nCountdown.while(3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0",
            ExpectedRaw = "0",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // A clause that matches nothing is the ordinary NoMatchingBranch, never loop termination.
                new SpecProbe("S(2) = 1, true\nS(1) = 0, true\nwhile(S, 2)", "err branch"),
                new SpecProbe("S(2) = 1, true\nS(1) = 0, false\nwhile(S, 2)", "ok raw=1 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A clause family is a natural `while` step with a base case: the selected clause's last row is the continuation flag, as for any step.",
        },
        new()
        {
            Id = "loop-step-family-multi-slot",
            Category = "conditionals",
            Source = "Gcd(a, 0) = a, 0, false\nGcd(a, b) = b, a mod b, true\nGcd.while(48, 18):0",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "6",
            ExpectedRaw = "6",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("Gcd(a, 0) = a, 0, false\nGcd(a, b) = b, a mod b, true\nwhile(Gcd, 48, 18)", "ok raw=S[6, 0] n=1"),
                new SpecProbe("Gcd(a, 0) = a, 0, false\nGcd(a, b) = b, a mod b, true\nwhile(Gcd, 7, 0)", "ok raw=S[7, 0] n=1"),
            ],
            Explanation = "A multi-slot family step matches its literals against the current state slots through ordinary clause dispatch; the selected clause's rows are the next state and its last row is the flag.",
        },
        new()
        {
            Id = "loop-step-builtin-is-one-row-wrapper",
            Category = "collection-builtins",
            Source = "C(c) = count(c)\nrepeat(count, 1, [1, 2]) == repeat(C, 1, [1, 2]), count.repeat(1, [1, 2])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "true\n2",
            ExpectedRaw = "S[true, 2]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // A collection result is ONE state slot, never its element count ...
                new SpecProbe("repeat(take, 1, [1, 2, 3], 2)", "ok raw=L[1, 2] n=1"),
                // ... so the next `take` invocation has one argument: take's own arity failure.
                new SpecProbe("repeat(take, 2, [1, 2, 3], 2)", "err arity"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A builtin step runs through its ordinary argument roles over the current state; it has no written rows, so its one result value is one next-state slot — exactly the step its one-row wrapper `C(c) = count(c)` makes.",
        },
        new()
        {
            Id = "loop-step-builtin-empty-result-is-one-slot",
            Category = "empty-visible-vs-spread",
            Source = "while(first, [()])",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Probes =
            [
                // The one-row wrapper fails the same way: its `()` row is one slot, so it is the flag.
                new SpecProbe("Fi(c) = first(c)\nwhile(Fi, [()])", "err type"),
                new SpecProbe("repeat(first, 1, [()])", "ok raw=S[] n=1"),
            ],
            Explanation = "A builtin's `()` result is ONE state slot holding `()`, like a `()` row: as a `while` step that slot is the flag, so a Boolean is required (a zero-slot reading would instead be the empty-supply arity failure).",
        },
        new()
        {
            Id = "loop-step-alias-follows-target",
            Category = "name-resolution",
            Source = "Step(0) = 0\nStep(n) = n - 1\nA = Step\nC = count\nrepeat(A, 2, 3), repeat(C, 1, [1, 2])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                new SpecProbe("Step(0) = 0\nStep(n) = n - 1\nRun(f, *s) = repeat(f, 2, s*)\nRun(Step, 3)", "ok raw=1 n=1"),
            ],
            Explanation = "A callable alias — and a parameter forwarding a callable — is its target's callable as a loop step too: a family or builtin target is invoked exactly as when written directly.",
        },
        new()
        {
            Id = "loop-step-value-is-rejected",
            Category = "errors",
            Source = "repeat(5, 1, 0)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "notAnAlgorithm",
            Probes =
            [
                new SpecProbe("A = 1, 2\nrepeat(A:0, 1, 0)", "err notAnAlgorithm"),
                // A genuinely zero-parameter callable is eligible, but one state value fails its ordinary arity.
                new SpecProbe("Z = 5\nrepeat(Z, 1, 0)", "err arity"),
            ],
            Explanation = "Any callable is an eligible step, but a value has no callable identity: a number, list, selection or call result is still no step, and the first iteration that needs it reports NotAnAlgorithm (Q-06) — by CALLABLE projection, never by demanding the value. A real zero-parameter callable is a step whose interface cannot bind one state value: ArityMismatch.",
        },
        new()
        {
            Id = "loop-step-zero-iterations-never-projects",
            Category = "item-supply-vs-value",
            Source = "repeat(5, 0, 1), repeat(1 / 0, 0, 5)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n5",
            ExpectedRaw = "S[1, 5]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                new SpecProbe("F(0) = 1\nrepeat(F, 0, 5)", "ok raw=5 n=1"),
            ],
            Explanation = "A zero-iteration `repeat` returns its initial state without projecting, validating or evaluating its step.",
        },
        new()
        {
            Id = "loop-step-family-no-match-is-ordinary",
            Category = "conditionals",
            Source = "F(0) = 1\nF(1) = 2\nrepeat(F, 1, 5)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "branch",
            Explanation = "A family step whose clauses match none of the current state is the family's ordinary NoMatchingBranch, exactly as the call `F(5)`.",
        },
        new()
        {
            Id = "loop-step-lazy-builtin-roles",
            Category = "collection-builtins",
            Source = "repeat(if, 1, false, 1 / 0, 2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2",
            ExpectedRaw = "2",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // A callback slot of a builtin step invokes the callable the state supplies.
                new SpecProbe("repeat(map, 1, [1, 2], { x + 1 })", "ok raw=L[2, 3] n=1"),
            ],
            Explanation = "A builtin step keeps its ordinary argument roles: `if` demands its condition and the selected branch only, so the unselected failing branch is never evaluated.",
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
            Source = "A = [[1, 2], [3, 4]]\n\n(A:0)*,\n(A*):0",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n[1, 2]",
            ExpectedRaw = "S[1, 2, L[1, 2]]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                new SpecProbe("A = [[1, 2], [3, 4]]\nA:0*", "ok raw=S[1, 2] n=2"),
                new SpecProbe("A = [[1, 2], [3, 4]]\n(A:0)*\n(A*):0", "err type"),
            ],
            Explanation = "Select-then-spread and capture-then-select are different operations: `(A:0)*` selects the stored list `[1, 2]` and spreads its elements into two rows, while `(A*):0` captures the two-item spread supply as one sequence value and selects its first item — the intact list `[1, 2]`. The trailing comma closes the spread row: without it the `(` on the next line is a right operand and the star is the multiplication `(A:0) * (A*):0` (SYN-07B), which fails on the list operands. (`A:0*` is the same select-then-spread: the star follows the completed index. `A*:0` is a targeted parse error — selection cannot be applied directly to an item supply.)",
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
            Source = "F(*a) = a.count\nF((), ())",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2",
            ExpectedRaw = "2",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("F(*a) = a.count\nF(())", "ok raw=1 n=1"),
                new SpecProbe("F(*a) = a.count\nF()", "ok raw=0 n=1"),
                new SpecProbe("F(*a) = a.count\nF(()*)", "ok raw=0 n=1"),
                new SpecProbe("F(*a) = a.count\nF(()*, (), 1)", "ok raw=2 n=1"),
                new SpecProbe("F(*a) = a\nF(())", "ok raw=L[S[]] n=1"),
                new SpecProbe("One(a) = 1\nOne(())", "ok raw=1 n=1"),
                new SpecProbe("One(a) = 1\nOne(()*)", "err arity"),
            ],
            Explanation = "A non-spread `()` is one visible argument: `One(())` binds it, `F((), ())` collects two items, and `F(())` collects ONE item — the empty sequence value `[()]` — never the zero-item supply of the empty call `F()`. Only spreading `()` contributes zero items (`F(()*)` is 0, `One(()*)` is an arity error, and `F(()*, (), 1)` collects the visible `()` beside `1`): an empty value is still a value, and only explicit opening turns it into nothing.",
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
            Id = "decon-rhs-implicit-parameter",
            Category = "deconstruction",
            Source = "F = {\n    a, b = x, 10\n    a + b\n}\nF(1)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "11",
            ExpectedRaw = "11",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("F = {\n    P = y * 2\n    a, b = P, 10\n    a + b\n}\nF(4)", "ok raw=18 n=1"),
                new SpecProbe("F = {\n    a, b = P, 10\n    P = y * 2\n    a + b\n}\nF(4)", "ok raw=18 n=1"),
            ],
            Explanation = "A deconstruction right-hand side is an expression of the enclosing body: its unresolved name `x` becomes `F`'s implicit parameter (never the hoisted source's), and a parameterized sibling referenced there lifts in `F`'s context regardless of declaration order.",
        },
        new()
        {
            Id = "decon-rhs-brace-scope",
            Category = "deconstruction",
            Source = "F = {\n    Q = 100\n    a, b = { Q = 7\n        Q, 10 }\n    a + b\n}\nF",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "17",
            ExpectedRaw = "17",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("a, b = { open { public Q = 7 }\n Q, 10 }\na + b", "ok raw=17 n=1"),
                new SpecProbe("a, b = { c, d = 7, 10\n c, d }\na + b", "ok raw=17 n=1"),
            ],
            Explanation = "A whole-brace deconstruction RHS keeps its lexical scope inside the shared source: its own Q shadows the enclosing Q, and its declarations never become enclosing RHS rows.",
        },
        new()
        {
            Id = "decon-rhs-lifted-parameter-order",
            Category = "deconstruction",
            Source = "P = x * 2\nR = y * 3\nF = {\n    a, b = P, 10\n    R + a + b\n}\nF(1, 2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "18",
            ExpectedRaw = "18",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("P = x * 2\nR = y * 3\nF = {\n R + a + b\n a, b = P, 10\n}\nF(1, 2)", "ok raw=17 n=1"),
            ],
            Explanation = "Sibling-derived parameters follow written row order across RHS and output rows, exactly as ordinary output rows do: F infers x then y, not output-first y then x.",
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
            Explanation = "The collecting target collects the remaining items as one list.",
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
            Explanation = "Front and back fixed targets bind first; the middle collecting binding collects its matched segment as one list.",
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
                new SpecProbe("x, *rest = 1\nrest*, x", "ok raw=1 n=1"),
                new SpecProbe("x, *rest = 1\nrest == []", "ok raw=true n=1"),
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
                new SpecProbe("A = 1, 2, 3\nx, y, z = (A*)\ny", "ok raw=2 n=1"),
                // Observe A itself as well as its bindings: no singleton sequence wrapper survives storage.
                new SpecProbe("A = ((1, 2))\nx, y = A\nA, x, y", "ok raw=S[S[1, 2], 1, 2] n=3"),
                new SpecProbe("x, y = [(1, 2)]\nx", "err arity"),
                new SpecProbe("x, y = ([(1, 2)]*)\nx, y", "ok raw=S[1, 2] n=2"),
                new SpecProbe("A = [(1, 2)]\nx, y = A\nx", "err arity"),
                new SpecProbe("A = [(1, 2)]\nx, y = (A*)\nx, y", "ok raw=S[1, 2] n=2"),
                // Different captured values can still present the same deconstruction items.
                new SpecProbe("A = [7]\nx, *xs = A\ny, *ys = (A*)\nA, (A*), x, xs, y, ys", "ok raw=S[L[7], 7, 7, L[], 7, L[]] n=6"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Assignment deconstruction is an unpacking receiver: the whole right-hand side is captured into one shared value, then a sequence or list is opened one level and matched element-by-element; an atom or string supplies itself as one item. For deconstruction targets, `= A` and `= (A*)` present the same items unless `A` is a singleton list whose lone element is itself a sequence or list. In that case, spread supplies the lone element, singleton capture returns it, and deconstruction opens it one level further: `x, y = [(1, 2)]` fails against two targets, while `x, y = ([(1, 2)]*)` binds `x = 1`, `y = 2`. Equal binding items do NOT require equal captured values: for `A = [7]`, both `x, *rest = A` and `x, *rest = (A*)` bind `x = 7`, `rest = []`, although capture sees `[7]` versus `7`. Stored sequences have no equivalent singleton wrapper because sequence normalization erases it. An ordinary single-name definition `x = A` retains the captured value without deconstruction; ordinary calls also do NOT unpack this way — `F(A)` still passes one argument.",
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
            Explanation = "Deconstruction with a middle collecting binding over a stored sequence value: fixed targets take the ends, the collecting binding collects the middle as one list.",
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
            Explanation = "A lone collecting binding is valid and collects the complete item supply as one exact list, including exact empty and singleton lists.",
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
                new SpecProbe("A = 1, 2, 3, 4, 5\nG(*x) = x.sum\nG(A)", "err type"),
                new SpecProbe("G(*x) = x.sum\nG((1, 2, 3, 4, 5))", "err type"),
                new SpecProbe("A = 1, 2, 3, 4, 5\nG(*x) = x.count\nG(A)", "ok raw=1 n=1"),
                new SpecProbe("A = 1, 2, 3, 4, 5\nG(*x) = x.count\nG(A*)", "ok raw=5 n=1"),
                new SpecProbe("A = 1, 2, 3, 4, 5\nG(*x) = x.count\nG(A, 0)", "ok raw=2 n=1"),
                new SpecProbe("G(*x) = x.sum\nG([1, 2, 3, 4, 5])", "err type"),
                new SpecProbe("G(*x) = x.sum\nG([1, 2, 3, 4, 5]*)", "ok raw=15 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A collecting parameter collects the ARGUMENTS supplied to it, exactly as one list. `G(A*)` and `G(1, 2, 3, 4, 5)` supply five numeric items (sum 15). The grouped calls `G(A)` and `G((1, 2, 3, 4, 5))` supply ONE sequence-valued argument, collected as one element (`G(A)` counts 1) that the numeric `sum` rejects as an element of the wrong kind (TypeMismatch) — exactly like a list argument `G([1, 2, 3, 4, 5])`. Only the explicit spread turns a value into several supplied items (`G([1, 2, 3, 4, 5]*)` sums to 15).",
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
                new SpecProbe("F(*x) = x\nF(1, 2, 3) == [1, 2, 3]", "ok raw=true n=1"),
                new SpecProbe("F(*x) = x\nF(1, 2, 3) == (1, 2, 3)", "ok raw=false n=1"),
                new SpecProbe("F(*x) = x\nF()", "ok raw=L[] n=1"),
                new SpecProbe("F(*x) = x\nF(7)", "ok raw=L[7] n=1"),
                new SpecProbe("F(*x) = x\nF(F(1, 2))", "ok raw=L[L[1, 2]] n=1"),
            ],
            Explanation = "Collecting binding COLLECTS the supplied argument slots into one list: zero slots form `[]`, one slot forms `[item]` (never erased), many form `[a, b, ...]`. The collected list never equals the sequence value with the same items.",
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
            Explanation = "Forwarding a collecting parameter re-spreads the collector's own supply: `Target(items*)` re-supplies exactly the items the caller supplied — the same computations, unevaluated until something demands them — so it re-collects the caller's slots, including the empty and singleton cases, while passing the collector without spread passes ONE argument whose value is the list (`TargetOne(items)` receives `[1, 2]`). There is no hidden raw-supply metadata.",
        },
        new()
        {
            Id = "implicit-forwarding-source-kind",
            Category = "variadic-calls",
            Source = "Target(tag, *items) = items\nUse(tag, items) = Target\nUseVariadic(tag, *items) = Target\n\nUse(0, [1, 2])\nUse(0, (1, 2))\nUseVariadic(0, 1, 2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[[1, 2]]\n[(1, 2)]\n[1, 2]",
            ExpectedRaw = "S[L[L[1, 2]], L[S[1, 2]], L[1, 2]]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                new SpecProbe("Target(tag, *items) = items\nUse(tag, items) = Target\nUse(0, 7)", "ok raw=L[7] n=1"),
                new SpecProbe("Target(tag, *items) = items\nUse(tag, items) = Target(tag, items)\nUse(0, [1, 2])", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("Target(tag, *items) = items\nUseVariadic(tag, *items) = Target\nUseVariadic(0, [1, 2])", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("Target(tag, *items) = items\nUseVariadic(tag, *items) = Target\nUseVariadic(0, (1, 2))", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("Target(first, *middle, last) = middle\nUse(first, *middle, last) = Target\nUse(1, 2, 3, 4)", "ok raw=L[2, 3] n=1"),
                // A formula forwards by binding NAME: Use's nested fixed `a` reaches Target's `*a`
                // as one value.
                new SpecProbe("Target(b, *a) = a\nUse((a, b)) = [Target]:0\nUse(([1, 2], 5))", "ok raw=L[L[1, 2]] n=1"),
                // Bare forwarding is by name too, never by position: Use's `a` reaches Target's `*a`
                // and Use's `b` Target's `b`, whatever order Use declares them in.
                new SpecProbe("Target(b, *a) = a\nUse(a, b) = Target\nUse([1, 2], 5)", "ok raw=L[L[1, 2]] n=1"),
                // Bare forwarding reads the callee's DECLARED signature, so a callee that works with
                // no arguments is forwarded like any other — exactly the written forwarding.
                new SpecProbe("Target(*items) = items\nUse(items) = Target\nUse([1, 2])", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("Target(*items) = items\nUseVariadic(*items) = Target\nUseVariadic(1, 2)", "ok raw=L[1, 2] n=1"),
                new SpecProbe("Target(*items) = items\nUseVariadic(*items) = Target(items*)\nUseVariadic(1, 2)", "ok raw=L[1, 2] n=1"),
                // In a FORMULA such a callee is read as a value by its bare name (Q-03).
                new SpecProbe("Target(*items) = items\nUseVariadic(*items) = [Target]:0\nUseVariadic(1, 2)", "ok raw=L[] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Forwarding decides spread from the SOURCE binding kind, never from the destination parameter kind: an ordinary caller parameter is passed as ONE argument even into a collecting destination (`Use(tag, items) = Target` forwards Use's `tag` and `items` by name, `Target(tag, items)`, so a list and a sequence value alike stay one collected item), and a caller collecting parameter forwards as spread (`UseVariadic(tag, *items) = Target` is `Target(tag, items*)`, which re-supplies exactly the collected items: collecting a supply and then spreading it gives back that same supply). Bare forwarding reads the callee's declared signature and supplies each parameter from the caller's binding of the SAME NAME, never by position, so even `Target(*items)` alone is forwarded; a formula that USES the callee forwards by binding name as well, and there a callee that works with no arguments is read as a value (`[]`).",
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
                new SpecProbe("Inspect(*items) = items\nB = (1, 2, 3)\nInspect(B, 0)", "ok raw=L[S[1, 2, 3], 0] n=1"),
                new SpecProbe("Inspect(*items) = items\nA = [1, 2]\nA.Inspect", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("CountArgs(*items) = items.count\nCountArgs([10, 20])", "ok raw=1 n=1"),
                new SpecProbe("CountArgs(*items) = items.count\nCountArgs([10, 20]*)", "ok raw=2 n=1"),
                new SpecProbe("CountArgs(*items) = items.count\nCountArgs((10, 20))", "ok raw=1 n=1"),
                new SpecProbe("CountArgs(*items) = items.count\nCountArgs((10, 20)*)", "ok raw=2 n=1"),
                new SpecProbe("CountArgs(*items) = items.count\nCountArgs((10, 20), 30)", "ok raw=2 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "An unspread value is one argument, a sequence and a list alike: `Inspect(A)` collects `[A]` (count 1) for the list `A`, and `Inspect(B)` collects `[B]` for the sequence `B` — alone or beside another argument (`Inspect(B, 0)` is `[(1, 2, 3), 0]`). The dotted receiver `A.Inspect` is exactly that argument (dot-call passes a value: `A.Inspect` is `Inspect(A)`). Only explicit spread supplies the immediate items (`Inspect(A*)` and `Inspect(B*)` collect `[1, 2, 3]`, and the fluent `A*.Inspect` is `Inspect(A*)`). See `dot-receiver-passes-a-value` for written group receivers.",
        },
        new()
        {
            Id = "dot-receiver-passes-a-value",
            Category = "variadic-calls",
            Source = "Mean(*Vector) = Vector.sum / Vector.count\n\nMean(1, 2, 3)\n(1, 2, 3)*.Mean\n[1, 2, 3]*.Mean",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2\n2\n2",
            ExpectedRaw = "S[2, 2, 2]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                new SpecProbe("Mean(*Vector) = Vector.sum / Vector.count\nMean(1, 2, 2.718)", "ok raw=1.906 n=1"),
                new SpecProbe("Mean(*Vector) = Vector.sum / Vector.count\n(1, 2, 2.718)*.Mean", "ok raw=1.906 n=1"),
                new SpecProbe("Mean(*Vector) = Vector.sum / Vector.count\n(1, 2, 2.718).Mean", "err type"),
                new SpecProbe("Mean(*Vector) = Vector.sum / Vector.count\n[1, 2, 3].Mean", "err type"),
                new SpecProbe("Collect(*items) = items\n(1, 2).Collect", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("Collect(*items) = items\nCollect((1, 2))", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("Collect(*items) = items\n(1, 2)*.Collect", "ok raw=L[1, 2] n=1"),
                new SpecProbe("Collect(*items) = items\n((1, 2)).Collect", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("Collect(*items) = items\n(1, 2).Collect(3)", "ok raw=L[S[1, 2], 3] n=1"),
                new SpecProbe("Collect(*items) = items\n((1, 2), 3).Collect", "ok raw=L[S[S[1, 2], 3]] n=1"),
                new SpecProbe("Collect(*items) = items\n().Collect", "ok raw=L[S[]] n=1"),
                new SpecProbe("Collect(*items) = items\n().Collect(3)", "ok raw=L[S[], 3] n=1"),
                new SpecProbe("Collect(*items) = items\n()*.Collect", "ok raw=L[] n=1"),
                new SpecProbe("Collect(*items) = items\n[1, 2].Collect", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("Collect(*items) = items\n[1, 2]*.Collect", "ok raw=L[1, 2] n=1"),
                new SpecProbe("Collect(*items) = items\n[(1, 2)]*.Collect", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("Collect(*items) = items\n{1, 2}.Collect", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("Collect(*items) = items\nA = (1, 2)\n(A*).Collect", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("Scale(*values, factor) = values, factor\n(1, 2, 3).Scale(10)", "ok raw=S[L[S[1, 2, 3]], 10] n=1"),
                new SpecProbe("Scale(*values, factor) = values, factor\n(1, 2, 3)*.Scale(10)", "ok raw=S[L[1, 2, 3], 10] n=1"),
                new SpecProbe("Scale(*values, factor) = values, factor\n[1, 2, 3].Scale(10)", "ok raw=S[L[L[1, 2, 3]], 10] n=1"),
                new SpecProbe("F(first, *middle, last) = first\n(1, 2).F", "err arity"),
                new SpecProbe("F(first, *middle, last) = first\n(1, 2)*.F", "ok raw=1 n=1"),
                new SpecProbe("F(*middle, last) = middle, last\n(1, 2).F", "ok raw=S[L[], S[1, 2]] n=1"),
                new SpecProbe("F(*middle, last) = middle, last\n(1, 2)*.F", "ok raw=S[L[1], 2] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Dot-call passes a value: for extension-call fallback, `R.F(args)` is exactly `F(R, args)` — the receiver is ONE ordinary leading argument whatever it is (a written group, a brace block, a list, a property, a call result, a selection, a capture of a spread), so its item count never satisfies arity (`(1, 2).F` against two fixed parameters fails), a fixed parameter binds it whole (`F(*middle, last)` gives `last` the whole pair), and a collecting parameter collects it as one item — a sequence and a list alike (`(1, 2).Collect` is `[(1, 2)]`, `[1, 2].Collect` is `[[1, 2]]`, `().Collect` is `[()]`, so `(1, 2, 3).Mean` and `[1, 2, 3].Mean` both hand `sum` one non-numeric element). Only the spread marker opens a receiver: `R*.F(args)` is `F(R*, args)`, so `(1, 2, 3)*.Mean` and `[1, 2, 3]*.Mean` average three items, and `[(1, 2)]*.Collect` collects the pair as one item.",
        },
        new()
        {
            Id = "values-stay-values",
            Category = "variadic-calls",
            Source = "Coll(*xs) = xs\nCnt(*xs) = xs.count\nCntValue(x) = x.count\n\nColl((1, 2))\nColl([1, 2])\nColl((1, 2)*)\nCnt((10, 7))\nCntValue((10, 7))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[(1, 2)]\n[[1, 2]]\n[1, 2]\n1\n2",
            ExpectedRaw = "S[L[S[1, 2]], L[L[1, 2]], L[1, 2], 1, 2]",
            ExpectedEmittedCount = 5,
            Probes =
            [
                new SpecProbe("Coll(*xs) = xs\nColl()", "ok raw=L[] n=1"),
                new SpecProbe("Coll(*xs) = xs\nColl(1, 2)", "ok raw=L[1, 2] n=1"),
                new SpecProbe("Coll(*xs) = xs\nColl(())", "ok raw=L[S[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nColl([])", "ok raw=L[L[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nColl([1, 2]*)", "ok raw=L[1, 2] n=1"),
                new SpecProbe("Coll(*xs) = xs\nColl([(1, 2)]*)", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nColl([()]*)", "ok raw=L[S[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nColl([[1, 2]]*)", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("Cnt(*xs) = xs.count\nCnt([10, 7])", "ok raw=1 n=1"),
                new SpecProbe("Cnt(*xs) = xs.count\nCnt([10, 7]*)", "ok raw=2 n=1"),
                new SpecProbe("CntValue(x) = x.count\nCntValue([10, 7])", "ok raw=2 n=1"),
                new SpecProbe("Coll(*xs) = xs\nA = ((1, 2), 3)\nColl(A:0), Coll(first(A)), Coll((A:0)*)", "ok raw=S[L[S[1, 2]], L[S[1, 2]], L[1, 2]] n=3"),
                new SpecProbe("WithHead(x, *rest) = (x, rest)\nWithHead(0, (1, 2)), WithHead(0, (1, 2)*)", "ok raw=S[S[0, L[S[1, 2]]], S[0, L[1, 2]]] n=2"),
                new SpecProbe("Middle(x, *m, y) = (x, m, y)\nMiddle(0, [1, 2], 9), Middle(0, (1, 2), 3, 9)", "ok raw=S[S[0, L[L[1, 2]], 9], S[0, L[S[1, 2], 3], 9]] n=2"),
                new SpecProbe("Id(x) = x\nId((1, 2)), Id([1, 2])", "ok raw=S[S[1, 2], L[1, 2]] n=2"),
                new SpecProbe("Add(x, y) = x + y\nAdd((1, 2))", "err arity"),
                new SpecProbe("Add(x, y) = x + y\nAdd((1, 2)*), Add([1, 2]*)", "ok raw=S[3, 3] n=2"),
                new SpecProbe("Target(*xs) = xs\nForward(*xs) = Target(xs*)\nForward((), [], (1, 2), [()]*)", "ok raw=L[S[], L[], S[1, 2], S[]] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "VALUES STAY VALUES. A non-spread argument supplies exactly ONE item — its value, whatever it is: a scalar, a sequence, a list, `()`, or `[]`. A collecting parameter collects exactly the items supplied to it as one list (`Coll((1, 2))` is `[(1, 2)]`, `Coll([1, 2])` is `[[1, 2]]`, `Coll(())` is `[()]`), a fixed parameter binds its item unchanged (`Id((1, 2))` is the pair, `Add((1, 2))` is an arity error), and ONLY the explicit spread `v*` turns a value into several items, one level, a sequence and a list alike (`Coll((1, 2)*)` and `Coll([1, 2]*)` are `[1, 2]`; spread-produced items are never reopened, so `Coll([(1, 2)]*)` is `[(1, 2)]`). So `*xs` counts the arguments supplied (`Cnt((10, 7))` is 1) while `x.count` counts one collection value's elements (`CntValue((10, 7))` is 2). Forwarding therefore round-trips: collecting a supply and then spreading it re-supplies exactly the same items.",
        },
        new()
        {
            Id = "callback-element-is-one-argument",
            Category = "collection-builtins",
            Source = "AddPair((x, y)) = x + y\nLAddPair([x, y]) = x + y\n\nmap([(1, 2)], AddPair)\nmap([[1, 2]], LAddPair)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[3]\n[3]",
            ExpectedRaw = "S[L[3], L[3]]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                new SpecProbe("Add(x, y) = x + y\nmap([(1, 2)], Add)", "err arity"),
                new SpecProbe("Add(x, y) = x + y\nmap([[1, 2]], Add)", "err arity"),
                new SpecProbe("Cnt(*xs) = xs.count\nmap([(1, 2)], Cnt), map([[1, 2]], Cnt)", "ok raw=S[L[1], L[1]] n=2"),
                new SpecProbe("Cnt(*xs) = xs.count\nAlias(*xs) = Cnt(xs*)\nApply(f, xs) = map(xs, f)\nApply(Alias, [(10, 7), 20]), Apply(Alias, [[10, 7], 20])", "ok raw=S[L[1, 1], L[1, 1]] n=2"),
                new SpecProbe("IsPair(*xs) = xs.count == 2\nfilter([(1, 2), [1, 2]], IsPair)", "ok raw=L[] n=1"),
                new SpecProbe("Acc(x, *acc) = acc\nreduce([9], Acc, (1, 2)), reduce([9], Acc, [1, 2])", "ok raw=S[L[S[1, 2]], L[L[1, 2]]] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "THE CALLBACK LAW: a callback element is ONE ordinary argument, bound exactly as the direct call `F(element)` — `map`, `filter`, and `reduce` add no implicit opening. A two-parameter flat callee therefore rejects a pair element with the ordinary arity error (`map([(1, 2)], Add)` like `Add((1, 2))`), a sequence and a list alike, while a structural pattern of the element's kind opens it explicitly (`AddPair((x, y))` a sequence element, `LAddPair([x, y])` a list element). A collecting callback counts one argument per element (`map([(1, 2)], Cnt)` is `[1]`), through a written forwarding alias and forwarding parameters too (`Alias(*xs) = Cnt(xs*)`, `Apply(Alias, [(10, 7), 20])` is `[1, 1]`), and a reducer receives its accumulator as one argument (`Acc(x, *acc)` collects `[(1, 2)]`).",
        },
        new()
        {
            Id = "parentheses-group-syntax",
            Category = "item-supply-vs-value",
            Source = "Collect(*items) = items\nS = 1, 2\nL = [1, 2]\nE = ()\n\nCollect(S), Collect((S)), Collect(((S)))\nCollect(L), Collect((L))\nCollect(E), Collect((E))\nS.Collect, (S).Collect, ((S)).Collect\nE*.Collect, (E)*.Collect",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[(1, 2)]\n[(1, 2)]\n[(1, 2)]\n[[1, 2]]\n[[1, 2]]\n[()]\n[()]\n[(1, 2)]\n[(1, 2)]\n[(1, 2)]\n[]\n[]",
            ExpectedRaw = "S[L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[L[1, 2]], L[L[1, 2]], L[S[]], L[S[]], L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[], L[]]",
            ExpectedEmittedCount = 12,
            Probes =
            [
                // Selection, dot access, and calls: the group is the expression.
                new SpecProbe("A = (1, 2), (3, 4)\n(A):0 == A:0, ((A)):1 == A:1", "ok raw=S[true, true] n=2"),
                new SpecProbe("Obj = {\n    public V = 7\n}\n(Obj).V, ((Obj)).V", "ok raw=S[7, 7] n=2"),
                new SpecProbe("Apply(f) = f(9)\nInc(x) = x + 1\nApply((Inc))", "ok raw=10 n=1"),
                new SpecProbe("Inc(x) = x + 1\n(Inc)(1), ((Inc))(2)", "ok raw=S[2, 3] n=2"),
                // Storage and stored reads agree with the direct value.
                new SpecProbe("S = 1, 2\nX = S\nY = (S)\nX == Y, (X) == Y, count(Y), (Y).count", "ok raw=S[true, true, 2, 2] n=4"),
                // Nested sequence and list values keep exactly their structure.
                new SpecProbe("N = ((1, 2), 3)\nCollect(*items) = items\nCollect((N)), [(N)], ((N)):0", "ok raw=S[L[S[S[1, 2], 3]], L[S[S[1, 2], 3]], S[1, 2]] n=3"),
                new SpecProbe("N = [[1, 2], 3]\nCollect(*items) = items\nCollect((N)), [(N)], ((N)):0", "ok raw=S[L[L[L[1, 2], 3]], L[L[L[1, 2], 3]], L[1, 2]] n=3"),
                // A selected empty sequence stays a selected `()` however it is grouped.
                new SpecProbe("A = ((), 1)\nCollect(*items) = items\nCollect((first(A))), Collect(((A:0))), ((first(A)))*.Collect", "ok raw=S[L[S[]], L[S[]], L[]] n=3"),
                // Only the groups whose parentheses DO something are captures.
                new SpecProbe("Collect(*items) = items\nCollect((1, 2), 3), Collect(((1, 2), 3))", "ok raw=S[L[S[1, 2], 3], L[S[S[1, 2], 3]]] n=2"),
                new SpecProbe("A = [[1, 2]]\nCollect(*items) = items\nCollect((A*)), Collect(A*)", "ok raw=S[L[L[1, 2]], L[L[1, 2]]] n=2"),
                new SpecProbe("A = [(1, 2)]\nCollect(*items) = items\n(A*).Collect, A*.Collect", "ok raw=S[L[S[1, 2]], L[S[1, 2]]] n=2"),
                // Error kinds agree between the spellings.
                new SpecProbe("Two(a, b) = a + b\nTwo(((1, 2)))", "err arity"),
                new SpecProbe("Two(a, b) = a + b\nTwo((1, 2))", "err arity"),
                new SpecProbe("Inc(x) = x + 1\nProbe(u) = count((Inc))\nProbe(0)", "err arity"),
                // A grouped reference lifts exactly like the bare one.
                new SpecProbe("Inc(x) = x + 1\nG = count((Inc)), count(Inc)\nG(4)", "ok raw=S[1, 1] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Parentheses group syntax; they do not introduce a semantic boundary. A group of exactly one non-spread expression is that expression — `(S)`, `((S))`, `(L)`, `(E)`, `(A):0`, `(Obj).V`, `(Inc)(1)` mean `S`, `L`, `E`, `A:0`, `Obj.V`, `Inc(1)` — with the same value, the same emitted count, the same binding (each is ONE argument: `Collect(((S)))` is `[(1, 2)]` like `Collect(S)`), the same caching, the same selection, the same dot-call receiver, the same spread, and the same error kind. Normalization never stops at a parenthesis (`((S))` is the pair, `(())` is `()`). Only a group whose parentheses do something is a sequence-valued capture: several slots (`((1, 2), 3)` is the pair beside 3) or a lone spread (`(A*)` captures the spread items into one value). Pattern parentheses are call-shape syntax (`F((a, b))` takes one argument that opens to two items), never a runtime boundary. Selection chooses a value, dot-call passes a value, spread opens a value — and parentheses group syntax.",
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
                new SpecProbe("F(x, *y, z) = y\nF(1, (2, 3), 4)", "ok raw=L[S[2, 3]] n=1"),
                new SpecProbe("F(x, *y, z) = y\nF(1, (2, 3)*, 4)", "ok raw=L[2, 3] n=1"),
                new SpecProbe("F(x, *y, z) = y\nF(1, (2, 3), 5, 4)", "ok raw=L[S[2, 3], 5] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Mixed fixed/collecting parameter lists bind the call's argument supply: fixed captures take the front and back first, and the collecting parameter then collects the middle segment EXACTLY — every remaining argument is one item, possibly none (`F(1, (2, 3), 4)` binds `y = [(2, 3)]`, `F(1, (2, 3), 5, 4)` binds `y = [(2, 3), 5]`), and only an explicit spread supplies a value's items (`F(1, (2, 3)*, 4)` binds `y = [2, 3]`). Fixed positions never open a sequence argument: `F(A)` supplies one argument against two fixed parameters and fails.",
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
            Probes =
            [
                new SpecProbe("Tail(first, *rest) = rest\nTail(1, (2, 3), 4)", "ok raw=L[S[2, 3], 4] n=1"),
                new SpecProbe("Tail(first, *rest) = rest\nTail(1, (2, 3)*)", "ok raw=L[2, 3] n=1"),
                new SpecProbe("Init(*init, last) = init\nInit((1, 2), 3, 4)", "ok raw=L[S[1, 2], 3] n=1"),
                new SpecProbe("Init(*init, last) = init\nInit([1, 2], 3)", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("Head(first, *rest) = first\nArg = 1, 2, 3\nHead(Arg)", "ok raw=S[1, 2, 3] n=1"),
                new SpecProbe("Tail(first, *rest) = rest\nArg = 1, 2, 3\nTail(Arg)", "ok raw=L[] n=1"),
            ],
            Explanation = "Grouped arguments are single items, and fixed captures bind whole argument boundaries first (`Head(1, (2, 3))` binds `first = 1`, `Last(Arg, 3)` binds `last = 3`, `Head(Arg)` binds the whole sequence). The collecting parameter then collects the remaining arguments exactly — a lone grouped sequence is one item (`Tail(1, (2, 3))` is `[(2, 3)]`, `Init((1, 2), 3)` is `[(1, 2)]`), exactly like a list (`Init([1, 2], 3)` is `[[1, 2]]`) — and only an explicit spread supplies its items (`Tail(1, (2, 3)*)` is `[2, 3]`).",
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
                new SpecProbe("Arg = (1, 2), (3, 4)\nMany(*values) = values.count\nMany(Arg, 0)", "ok raw=2 n=1"),
            ],
            Explanation = "Segment collection is not recursive flattening: `Many(Arg*)` supplies the two nested pairs as two collected elements — the spread opens exactly one level, never the four atoms — while the unspread `Many(Arg)` is ONE argument (count 1), and `atoms` is the explicit recursive projection.",
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
            Probes =
            [
                new SpecProbe("CountValues(*values) = values.count\nCountValues((1, 2, 3), 4)", "ok raw=2 n=1"),
                new SpecProbe("CountSequenceValue((*values)) = values.count\nCountSequenceValue((1, 2, 3), 4)", "err arity"),
                new SpecProbe("CountValues(*values) = values.count\nCountValues([1, 2, 3])", "ok raw=1 n=1"),
                new SpecProbe("CountSequenceValue((*values)) = values.count\nCountSequenceValue([1, 2, 3])", "err type"),
                new SpecProbe("CountListValue([*values]) = values.count\nCountListValue([1, 2, 3])", "ok raw=3 n=1"),
            ],
            Explanation = "Top-level `*values` collects the call's ARGUMENTS: a grouped `(1, 2, 3)` is ONE argument (count 1), two arguments stay two (`CountValues((1, 2, 3), 4)` counts 2), and a list is one argument too. The sequence pattern `(*values)` is the explicit structural opener instead: it consumes exactly one argument, which must be a SEQUENCE value, and opens it during binding (`CountSequenceValue((1, 2, 3))` counts 3), so a second argument is an arity error and a list is its kind mismatch; the list pattern `[*values]` opens a list the same way.",
        },
        new()
        {
            Id = "singleton-sequence-pattern-is-invalid",
            Category = "empty-and-singleton",
            Source = "F((x)) = x\nF(7)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "no one-item sequence value",
            ExpectedDiagnosticCode = DiagnosticCode.SingletonSequencePattern,
            Probes =
            [
                // The collector-only sequence pattern, the one-element LIST pattern, and a plain
                // binder are the valid spellings; expression grouping is unaffected. (Every
                // nesting level and clause families follow the rejection too — `F(((x)))`,
                // `F(([x]))`, `F(((x, y)))`, `F(0) = 0` / `F((x)) = x`: SingletonSequencePatternTests.)
                new SpecProbe("F((*xs)) = xs\nF((1, 2))", "ok raw=L[1, 2] n=1"),
                new SpecProbe("F([x]) = x\nF([7])", "ok raw=7 n=1"),
                new SpecProbe("F(x) = (x)\nF((7))", "ok raw=7 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Source-level pattern diagnostic; no elaborated Lean program exists for a rejected parse. Lean enforces the same rule on hand-built trees: validateExplicitParamOutputInvariant rejects a singleton sequence pattern before evaluation (CoreTests singletonSequencePatternIsRejectedBeforeEvaluation).",
            Explanation = "KatLang has no one-item sequence value — `(7)` IS `7` — so a sequence pattern with exactly ONE non-collecting item describes a boundary no value has. The front end rejects it at every nesting level, in ordinary definitions and clause families alike, instead of silently reading `F((x))` as `F(x)`: bind the whole value with a plain name `x`, or use the list pattern `[x]` for a one-element list. The collector-only `(*xs)` stays valid — a collector stands for a sequence's elements, not for a sequence of one — and grouping in expressions is unaffected (`(x)` there IS `x`).",
        },
        new()
        {
            Id = "list-patterns-cover-every-cardinality",
            Category = "lists",
            Source = "L([*xs]) = xs\nOnly([x]) = x\nPair([x, y]) = x + y\nEnds([first, *middle, last]) = first, middle, last\n\nL([]), L([1]), L([1, 2])\nOnly([10])\nPair([10, 20])\nEnds([1, 2, 3, 4])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[]\n[1]\n[1, 2]\n10\n30\n(1, [2, 3], 4)",
            ExpectedRaw = "S[L[], L[1], L[1, 2], 10, 30, S[1, L[2, 3], 4]]",
            ExpectedEmittedCount = 6,
            Probes =
            [
                // A list pattern opens LIST values only, of its own length.
                new SpecProbe("Only([x]) = x\nOnly(7)", "err type"),
                new SpecProbe("Only([x]) = x\nOnly((7, 8))", "err type"),
                new SpecProbe("Only([x]) = x\nOnly([7, 8])", "err arity"),
                new SpecProbe("Only([x]) = x\nOnly([[7]])", "ok raw=L[7] n=1"),
                // The empty sequence and the empty list are different values and patterns.
                new SpecProbe("E([]) = 0\nE([])", "ok raw=0 n=1"),
                new SpecProbe("E([]) = 0\nE(())", "err type"),
                new SpecProbe("E(()) = 0\nE([])", "err type"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Lists keep every cardinality, so list patterns do too: `[]` matches the empty list, `[x]` exactly a one-element list (the one-element structural pattern), `[x, y]` a two-element list, and a collector — `[*xs]`, `[first, *rest]`, `[first, *middle, last]` — collects the remaining elements of a list of any length as an exact list. A list pattern opens LIST values only: a scalar or a sequence is its kind mismatch. The empty sequence `()` and the empty list `[]` are different values, and `()` and `[]` are different patterns.",
        },
        new()
        {
            Id = "nested-structural-patterns-keep-their-kind",
            Category = "variadic-calls",
            Source = "F(([x, y], z)) = x + y + z\nG([(x, y), z]) = x + y + z\n\nF(([10, 20], 30))\nG([(1, 2), 3])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "60\n6",
            ExpectedRaw = "S[60, 6]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // Each level checks its own kind.
                new SpecProbe("F(([x, y], z)) = x + y + z\nF(((10, 20), 30))", "err type"),
                new SpecProbe("F(([x, y], z)) = x + y + z\nF([[10, 20], 30])", "err type"),
                new SpecProbe("G([(x, y), z]) = x + y + z\nG([[1, 2], 3])", "err type"),
                // Outer call arity is not structural shape.
                new SpecProbe("F(x, y) = x + y\nF(1, 2)", "ok raw=3 n=1"),
                new SpecProbe("F((x, y)) = x + y\nF(1, 2)", "err arity"),
                new SpecProbe("F([x, y]) = x + y\nF((1, 2))", "err type"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Structural patterns compose, keeping their kind at every level: `F(([x, y], z))` takes ONE argument that must be a two-element sequence whose first element is a two-element list, and `G([(x, y), z])` is the mirror image. Outer call arity is separate from structural shape: `F(x, y)` has two parameters, `F((x, y))` one parameter whose value must be a two-element sequence, and `F([x, y])` one parameter whose value must be a two-element list.",
        },
        new()
        {
            Id = "structural-patterns-open-only-their-own-kind",
            Category = "variadic-calls",
            Source = "PairSum((x, y)) = x + y\nListSum([x, y]) = x + y\n\nPairSum((2, 3))\nListSum([2, 3])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5\n5",
            ExpectedRaw = "S[5, 5]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // The other kind, or a scalar, is the pattern's KIND mismatch; the right kind with
                // the wrong number of elements is its arity mismatch.
                new SpecProbe("PairSum((x, y)) = x + y\nPairSum([2, 3])", "err type"),
                new SpecProbe("PairSum((x, y)) = x + y\nPairSum(7)", "err type"),
                new SpecProbe("PairSum((x, y)) = x + y\nPairSum((1, 2, 3))", "err arity"),
                new SpecProbe("ListSum([x, y]) = x + y\nListSum((2, 3))", "err type"),
                // Collectors keep the kind: a sequence collector opens sequences only, a list
                // collector lists of every cardinality, one element included.
                new SpecProbe("Count((*v)) = v.count\nCount((1, 2, 3))", "ok raw=3 n=1"),
                new SpecProbe("Count((*v)) = v.count\nCount([1, 2, 3])", "err type"),
                new SpecProbe("LCount([*v]) = v.count\nLCount([7])", "ok raw=1 n=1"),
                // Callback position uses the same binder and the same law.
                new SpecProbe("PairSum((x, y)) = x + y\n[(1, 2), (3, 4)].map(PairSum)", "ok raw=L[3, 7] n=1"),
                new SpecProbe("PairSum((x, y)) = x + y\n[[1, 2], (3, 4)].map(PairSum)", "err type"),
                // A clause family follows the same law; there a mismatch only rejects the clause.
                new SpecProbe("F((x, y)) = x + y\nF(z) = 0\nF([2, 3])", "ok raw=0 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Structural pattern delimiters select the value kind they destructure. A parenthesized sequence pattern consumes one argument slot and opens a SEQUENCE value only; a bracketed list pattern opens a LIST value only. A value of the other kind — or a scalar, which is never a one-item structure — is the pattern's kind mismatch, a type error in an ordinary definition; the right kind with the wrong number of elements is an arity error. Clause families follow the same law, where a mismatch only rejects that clause.",
        },
        new()
        {
            Id = "binding-failure-outranks-repeated-name-conflict",
            Category = "variadic-calls",
            Source = "Bad = 1 / 0\nP(x, x, (a, b)) = a\n\nP(1, 2, Bad)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // The second x immediately conflicts; later structural patterns are not demanded.
                new SpecProbe("P(x, x, (a, b)) = a\nP(1, 2, 7)", "err arity"),
                new SpecProbe("P(x, x, (a, b)) = a\nP(1, 2, (7, 8, 9))", "err arity"),
                // The first conflict in written pattern order decides. A and B have equal values
                // but distinct callable identities.
                new SpecProbe("A = 5\nB = 2 + 3\nP(x, x, f, f) = 0\nP(1, 2, A, B)", "err arity"),
                new SpecProbe("A = 5\nB = 2 + 3\nP(f, f, x, x) = 0\nP(A, B, 1, 2)", "err type"),
                // A repeated name's argument without a value fails its own binding first.
                new SpecProbe("Bad = 1 / 0\nP(x, x, y, y) = 0\nP(Bad, 7, 1, 2)", "err div0"),
                // A conflict inside a nested group is part of binding that group.
                new SpecProbe("Bad = 1 / 0\nP((x, x), (a, b)) = a\nP((1, 2), Bad)", "err arity"),
                // Equal repeated values still bind.
                new SpecProbe("P(x, x, (a, b)) = b\nP(1, 1, (2, 3))", "ok raw=3 n=1"),
            ],
            Explanation = "Repeated names demand each occurrence in written pattern order and check compatibility immediately. The second unequal `x` is an arity conflict, so the later structural argument `Bad` is never demanded. A demanded failure still aborts binding, and equal values with distinct callable identities conflict at the occurrence that reveals the difference. Nested patterns follow the same order. Callbacks and loop state use this binder too.",
        },
        new()
        {
            Id = "repeated-name-binding-is-order-independent",
            Category = "variadic-calls",
            Source = "A = 5\nB = 2 + 3\nP(f, f, f) = f\n\nP(A, 5, B)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Probes =
            [
                // This contribution set fails in every permutation. Its only incompatibility
                // is callable identity; mixed VALUE/identity sets may report different categories.
                new SpecProbe("A = 5\nB = 2 + 3\nP(f, f, f) = f\nP(B, 5, A)", "err type"),
                new SpecProbe("A = 5\nB = 2 + 3\nP(f, f, f) = f\nP(5, A, B)", "err type"),
                // Every pair compatible: binds in every order.
                new SpecProbe("A = 5\nP(f, f, f) = f\nP(A, A, 5)", "ok raw=5 n=1"),
                new SpecProbe("A = 5\nP(f, f, f) = f\nP(5, A, A)", "ok raw=5 n=1"),
                // Unequal values, in every order.
                new SpecProbe("A = 5\nB = 6\nP(f, f, f) = f\nP(B, 5, A)", "err arity"),
                // An argument without a value is its own failure wherever it stands (formerly the
                // two-occurrence rule bound `P(5, Inc)` to the value 5 with Inc's algorithm).
                new SpecProbe("Bad = 1 / 0\nP(f, f, f) = f\nP(5, Bad, 5)", "err div0"),
                new SpecProbe("Bad = 1 / 0\nP(f, f, f) = f\nP(5, 5, Bad)", "err div0"),
                new SpecProbe("Inc(y) = y + 1\nP(f, f) = f\nP(5, Inc)", "err arity"),
            ],
            Explanation = "Each repeated occurrence is demanded and compared immediately with the established complete binding. Compatible values and callable identities succeed regardless of order; conflicts or demand failures stop at their first occurrence. Equal values from distinct named callables conflict, while a ready scalar has no callable channel. A failing value is never replaced by another occurrence's value or callable.",
        },
        new()
        {
            Id = "repeated-name-is-a-constraint-not-a-merge",
            Category = "variadic-calls",
            Source = "Inc(y) = y + 1\nP(x, x) = x, x(5)\n\nP(Inc, 1)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // Both orders: the value 1 never borrows Inc's algorithm (formerly `(1, 6)`).
                new SpecProbe("Inc(y) = y + 1\nP(x, x) = x, x(5)\nP(1, Inc)", "err arity"),
                // A failing argument's own error propagates; the other value never stands in
                // (formerly `7`), and two failures report the first (formerly a type error).
                new SpecProbe("Bad = 1 / 0\nQ(x, x) = x\nQ(Bad, 7)", "err div0"),
                new SpecProbe("Bad = 1 / 0\nQ(x, x) = x\nQ(7, Bad)", "err div0"),
                new SpecProbe("Bad = 1 / 0\nMissing = [1]:5\nQ(x, x) = x\nQ(Missing, Bad)", "err index"),
                // Values that each arrive on their own bind; a callable accompanies its own value.
                new SpecProbe("P(x, x) = x\nP(7, 7)", "ok raw=7 n=1"),
                new SpecProbe("A = 5\nP(f, f) = f, f()\nP(5, A)", "ok raw=S[5, 5] n=1"),
                // Clause families already required every argument's value before matching.
                new SpecProbe("Bad = 1 / 0\nE(x, x) = true\nE(x, y) = false\nE(Bad, 7)", "err div0"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A repeated parameter name is a constraint over arguments that are each supplied independently, never a way to combine them. Every occurrence must supply its own value, and the values must be equal. `Inc` passed without arguments has no value (reading it as one is an arity error), so `P(Inc, 1)` and `P(1, Inc)` both fail with that error: the value 1 is never paired with Inc's callable. An argument whose evaluation fails reports its own error, and another occurrence's value never stands in for it. When equal values arrive together with a callable, the callable accompanies its own argument's value.",
        },
        new()
        {
            Id = "repeated-equal-values-require-one-callable-identity",
            Category = "variadic-calls",
            Source = "A(*xs) = 5\nB(*xs) = 5 + xs.count\nP(f, f) = f(1)\nP(A, B)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Probes =
            [
                new SpecProbe("A(*xs) = 5\nB(*xs) = 5 + xs.count\nP(f, f) = f(1)\nP(B, A)", "err type"),
                new SpecProbe("A(*xs) = 5\nB(*xs) = 5 + xs.count\nP(f, *r, f) = f(1)\nP(A, 9, B)", "err type"),
                new SpecProbe("A = 5\nB = 5\nP(f, f) = f\nP(A, B)", "err type"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Repeated values must be equal, and repeated callable contributions must carry values and the same callable identity (declaration and captured lexical activations). Equal zero-argument values do not make A and B interchangeable: A(1) is 5 while B(1) is 6. Both argument orders therefore reject, including with just two occurrences. One callable plus an equal value remains valid.",
        },
        new()
        {
            Id = "implicit-forwarding-is-by-binding-name",
            Category = "variadic-calls",
            Source = "F(x) = x + 1\nG(x) = x * 2\nH = F + G\n\nCommon(x, x) = x\nTwice = Common * 2\n\nH(3)\nTwice(7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "10\n14",
            ExpectedRaw = "S[10, 14]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // One binding name is one caller parameter: Twice takes one argument.
                new SpecProbe("Common(x, x) = x\nTwice = Common * 2\nTwice(7, 7)", "err arity"),
                // The direct call supplies two independent arguments, which must be equal (Q-05).
                new SpecProbe("Common(x, x) = x\nCommon(7, 8)", "err arity"),
                // Three occurrences, a nested group, and a written parameter list that binds the name.
                new SpecProbe("P(x, x, x) = x\nSome = P + 0\nSome(7)", "ok raw=7 n=1"),
                new SpecProbe("P((x, a), x) = a\nSome = [P]:0\nSome((7, 8))", "ok raw=8 n=1"),
                new SpecProbe("P(x, x) = x\nQ(x) = P + 0\nQ(7)", "ok raw=7 n=1"),
                // The one binding is the caller's argument, whatever it is: a failing or
                // callable-only argument is still its own error (Q-05), never repaired or spliced.
                new SpecProbe("Bad = 1 / 0\nP(x, x) = x\nSome = P + 0\nSome(Bad)", "err div0"),
                new SpecProbe("Inc(y) = y + 1\nP(x, x) = x\nSome = P + 0\nSome(Inc)", "err arity"),
                // A body that is ONLY the callee is not a formula: a callable alias IS Common, with
                // its two arguments and their constraint, and bare forwarding reuses the caller's one
                // binding named x for both occurrences, P(x, x).
                new SpecProbe("Common(x, x) = x\nSame = Common\nSame(7, 7)", "ok raw=7 n=1"),
                new SpecProbe("Common(x, x) = x\nSame = Common\nSame(7)", "err arity"),
                new SpecProbe("P(x, x) = x\nQ(x) = P\nQ(7)", "ok raw=7 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A formula that USES another formula hands its inputs on by binding name, regardless of how many times that name occurs in the callee's parameter patterns. A caller owns one binding for a name, and every occurrence of that name in the callee receives it: `Twice = Common * 2` is `Twice(x) = Common(x, x) * 2`, exactly as `H = F + G` with `F(x)` and `G(x)` is `H(x) = F(x) + G(x)`. So `Twice(7)` is 14, and Twice takes one argument. Nothing is combined: both occurrences receive the same binding, so a failing or callable-only argument is still that argument's own error. A definition whose whole body is the callee is not a formula: `Same = Common` is a callable alias, so calling Same calls Common itself, with its two independent arguments, and bare forwarding `Q(x) = P` reuses Q's one binding named x by name, `P(x, x)`.",
        },
        new()
        {
            Id = "formula-lifting-is-one-law-for-every-callable",
            Category = "variadic-calls",
            Source = "Lib = {\n    public Inc(x) = x + 1\n}\nE(0) = 100\nE(n) = n\nTotal = count + 0\nNext = Lib.Inc + 0\nFam = E + 1\n\nTotal((1, 2, 3))\nNext(4)\nFam(0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3\n5\n101",
            ExpectedRaw = "S[3, 5, 101]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // A member reached through `open`, a loop builtin, `if`, a Math function and a host
                // operation lift from their own signatures exactly the same way.
                new SpecProbe("Lib = {\n    public Inc(x) = x + 1\n}\nG = {\n    open Lib\n    Inc + 0\n}\nG(4)", "ok raw=5 n=1"),
                new SpecProbe("Step(s) = s + 1\nG = repeat + 0\nG(Step, 2, 0)", "ok raw=2 n=1"),
                new SpecProbe("G = if + 0\nG(false, 1, 2)", "ok raw=2 n=1"),
                new SpecProbe("G = abs + 0\nG(0 - 4)", "ok raw=4 n=1"),
                new SpecProbe("G = Math.Abs * 2\nG(0 - 4)", "ok raw=8 n=1"),
                // A clause family is named by its clauses, one whole-value input per position.
                new SpecProbe("P(0, y) = y\nP(x, y) = x + y\nG = P * 10\nG(2, 5), G(0, 5)", "ok raw=S[70, 50] n=2"),
                // A closed list forwards a builtin's input by its own name, like a user formula's.
                new SpecProbe("G(collection) = count + 0\nG((1, 2, 3))", "ok raw=3 n=1"),
                new SpecProbe("G(items) = count + 0\nG((1, 2, 3))", "err arity"),
                // Not formulas: a bare top-level row is the callable's own demand, and a whole body
                // that is only a callable's name is a callable alias of it, a builtin's included.
                new SpecProbe("count", "err arity"),
                new SpecProbe("E(0) = 1\nE(n) = n\nE", "err branch"),
                new SpecProbe("C = count\nC((1, 2))", "ok raw=2 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "The unified formula-lifting law (decided September 30 2026; constitution Q-11, Q-12 and Q-13 for formulas). Formerly only document properties and the two Math spellings lifted: `count`, an opened or dotted member, a host operation and a clause family stayed bare references.",
            Explanation = "A formula that uses a callable as a value hands the callable's inputs on, whatever kind of callable it is and however its name was reached: a builtin (`Total = count + 0` is `Total(collection) = count(collection) + 0`, with the builtin's own parameter names), a member reached through a dot path or `open`, a Math function, a host operation, and a clause family, whose inputs are named by its clauses (`E(n) = n` names `E`'s one input `n`, so `Fam = E + 1` is `Fam(n) = E(n) + 1`). A bare top-level row is not a formula — writing `count` alone reports that `count` needs its argument — and neither is a definition whose whole body is only a callable's name: `C = count` makes `C` a callable alias of `count`, so `C((1, 2))` is `count((1, 2))`.",
        },
        new()
        {
            Id = "formula-lifting-follows-the-consumers-role",
            Category = "variadic-calls",
            Source = "Inc(x) = x + 1\nApply(f) = f(10)\n\nValues = [Inc, Inc * 2]\nKept = Apply(Inc)\nBranch = if(true, Inc, 0)\n\nValues(4)\nKept\nBranch(4)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[5, 10]\n11\n5",
            ExpectedRaw = "S[L[5, 10], 11, 5]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // Callbacks and loop steps are called, never lifted.
                new SpecProbe("Inc(x) = x + 1\nG = map([1, 2], Inc)\nG", "ok raw=L[2, 3] n=1"),
                new SpecProbe("Inc(x) = x + 1\nG = repeat(Inc, 2, 0)\nG", "ok raw=2 n=1"),
                // A nested expression takes its own consumer's role, whatever slot encloses it.
                new SpecProbe("Inc(x) = x + 1\nId(v) = v\nG = Id(Inc + 0)\nG(4)", "ok raw=5 n=1"),
                new SpecProbe("Inc(x) = x + 1\nG = (Inc, 0)\nG(4)", "ok raw=S[5, 0] n=1"),
                new SpecProbe("Inc(x) = x + 1\nS = Inc.string\nS(4)", "ok raw='5' n=1"),
                new SpecProbe("Inc(x) = x + 1\nG = Inc.count\nG(4)", "ok raw=1 n=1"),
                // An unselected branch still lifts, and is still evaluated only when selected.
                new SpecProbe("Bad(x) = x / 0\nG = if(c, 1, Bad)\nG(true, 5)", "ok raw=1 n=1"),
                new SpecProbe("Bad(x) = x / 0\nG = if(c, 1, Bad)\nG(false, 5)", "err div0"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "The unified formula-lifting law (decided September 30 2026): the role is the immediate consumer's, recursive, and blind to laziness. Formerly builtin value slots, capture elements, nested call arguments and the `.string` receiver never lifted.",
            Explanation = "Whether a reference lifts is decided by what its immediate consumer does with it. A consumer that needs the VALUE — an operator, a list or capture element, an `if` argument, a builtin's collection or value control, a Math or host argument, a clause family's argument, the `.string` receiver — lifts it: `Values = [Inc, Inc * 2]` is `Values(x) = [Inc(x), Inc(x) * 2]`. A consumer that CALLS it or passes it on keeps it: `Apply(Inc)` hands `Inc` itself to `Apply`, and `map([1, 2], Inc)` calls it for each element. A nested expression is judged by its own consumer, so `Id(Inc + 0)` lifts while `Id(Inc)` does not. Laziness does not change the decision: an `if` branch lifts whether or not a run selects it, and it is still evaluated only when selected.",
        },
        new()
        {
            Id = "unliftable-clause-family",
            Category = "variadic-calls",
            Source = "S(1) = 1\nS(-1) = -1\nG = S + 0\n\nG(1)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "has no formula-lifting signature",
            ExpectedDiagnosticCode = DiagnosticCode.UnliftableClauseFamily,
            Probes =
            [
                // The family stays explicitly callable, and a family its clauses name lifts.
                new SpecProbe("S(1) = 1\nS(-1) = -1\nG(v) = S(v) + 0\nG(0 - 1)", "ok raw=-1 n=1"),
                new SpecProbe("E(0) = 100\nE(n) = n\nG = E + 0\nG(0)", "ok raw=100 n=1"),
                // A closed list forwards nothing to a family that names nothing: its runtime demand.
                new SpecProbe("S(1) = 1\nS(-1) = -1\nP(u) = S + 0\nP(0)", "err branch"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "The unified formula-lifting law (decided September 30 2026): a clause family's lifting signature is derived from its clauses, and no name is ever invented. Source-level front-end diagnostic; no elaborated Lean program exists.",
            Explanation = "A formula hands its inputs on by parameter name, so lifting a clause family needs one name per argument position: the plain parameters its clauses bind there. Literal, structural and empty clause patterns name nothing, the clauses must agree on a position's name, and two positions cannot share one. `S(1) = 1` and `S(-1) = -1` name nothing, so the formula `G = S + 0` is rejected at `S`: call the family with explicit arguments (`G(v) = S(v) + 0`), or name the position with a plain parameter in a general clause.",
        },
        new()
        {
            Id = "repeated-name-wrapper-keeps-independent-arguments",
            Category = "variadic-calls",
            Source = "Common(x, x) = x\nBoth(a, b) = Common(a, b)\nTwice(v) = Common(v, v)\nSome = Common\n\nBoth(7, 7)\nTwice(8)\nSome(9, 9)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7\n8\n9",
            ExpectedRaw = "S[7, 8, 9]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // Two independently supplied arguments: unequal values are the callee's own
                // failure, and a failed argument is its own error.
                new SpecProbe("P(x, x) = x\nAlias(a, b) = P(a, b)\nAlias(7, 8)", "err arity"),
                new SpecProbe("Bad = 1 / 0\nP(x, x) = x\nAlias(a, b) = P(a, b)\nAlias(Bad, 7)", "err div0"),
                // A callable alias IS the callee, with its two independent arguments.
                new SpecProbe("P(x, x) = x\nSome = P\nSome(7, 8)", "err arity"),
                new SpecProbe("Bad = 1 / 0\nP(x, x) = x\nSome = P\nSome(Bad, 7)", "err div0"),
                // One binding supplied to both occurrences, written or forwarded by a formula.
                new SpecProbe("Bad = 1 / 0\nP(x, x) = x\nSame(x) = P(x, x)\nSame(Bad)", "err div0"),
                new SpecProbe("Bad = 1 / 0\nP(x, x) = x\nSome = [P]:0\nSome(Bad)", "err div0"),
                // A nested repetition, and an alias of a wrapper whose own names are distinct.
                new SpecProbe("P((x, a), x) = a\nW(p, q) = P(p, q)\nW((7, 8), 7)", "ok raw=8 n=1"),
                new SpecProbe("P(x, x) = x\nW(u, v) = P(u, v)\nAlias = W\nAlias(5, 5)", "ok raw=5 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Who supplies the occurrences of a repeated name decides what is checked. `Both(a, b) = Common(a, b)` passes two independently supplied arguments, so Common still checks them: `Both(7, 7)` is 7 and `Both(7, 8)` fails as `Common(7, 8)` does. `Some = Common` is a callable alias: calling Some calls Common itself, with its own two independent arguments, so `Some(9, 9)` is 9 and `Some(9, 8)` fails the same way. `Twice(v) = Common(v, v)` writes one binding into both occurrences, and a formula such as `[Common]:0` forwards one binding by name in exactly the same way, so `Twice(8)` is 8.",
        },
        new()
        {
            Id = "implicit-forwarding-preserves-structural-kind",
            Category = "variadic-calls",
            Source = "Single([x]) = x\nA = Single\nAdd((x, y)) = x + y\nB = Add\nC((*xs)) = xs.count\nCount = C\nG([x]) = Single\n\nA([7])\nA([[7]])\nB((10, 20))\nCount((1, 2, 3))\nG([7])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7\n[7]\n30\n3\n7",
            ExpectedRaw = "S[7, L[7], 30, 3, 7]",
            ExpectedEmittedCount = 5,
            Probes =
            [
                // An alias means its callee, for every argument and every structural kind.
                new SpecProbe("Single([x]) = x\nA = Single\nA([[7]]) == Single([[7]])", "ok raw=true n=1"),
                new SpecProbe("Single([x]) = x\nA = Single\nA(7)", "err type"),
                new SpecProbe("Add((x, y)) = x + y\nB = Add\nB([10, 20])", "err type"),
                new SpecProbe("C((*xs)) = xs.count\nCount = C\nCount(())", "ok raw=0 n=1"),
                // Nested groups keep their kind at every level.
                new SpecProbe("F(([x, y], z)) = x + y + z\nA = F\nA(([10, 20], 30))", "ok raw=60 n=1"),
                new SpecProbe("F([(x, y), z]) = x + y + z\nA = F\nA([(1, 2), 3])", "ok raw=6 n=1"),
                // An alias chain is its callee too, repeated names included.
                new SpecProbe("P([x, x]) = x\nSome = P\nNext = Some\nNext([(7, 8), (7, 8)])", "ok raw=S[7, 8] n=1"),
                new SpecProbe("P([x, x]) = x\nSome = P\nNext = Some\nNext([(7, 8)])", "err arity"),
                // A local alias is Single itself, so its owner forwards its own same-pattern [x]
                // to it by name.
                new SpecProbe("Single([x]) = x\nF([x]) = {\n  K = Single\n  K\n}\nF([[7]])", "ok raw=L[7] n=1"),
                // Bare forwarding rebuilds the same-named, same-pattern parameter as its own kind.
                new SpecProbe("M([first, *middle, last]) = [first, middle, last]\nW([first, *middle, last]) = M\nW([1, 2, 3])", "ok raw=L[1, L[2], 3] n=1"),
                new SpecProbe("F(([x, y], z)) = x + y + z\nW(([x, y], z)) = F\nW(([1, 2], 3))", "ok raw=6 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Forwarding hands every existing binding on unchanged and rebuilds every structural pattern it reconstructs as the SAME kind that pattern matches. A callable alias forwards nothing at all — it IS its callee: `A = Single` accepts exactly the one-element lists Single accepts, `B = Add` exactly the pairs (so, like `Add`, it rejects a list), `Count = C` exactly C's sequences, and nested groups keep their kind at every level. Bare forwarding supplies a structural parameter only from a binding with the same name AND the same pattern, rebuilt as that kind: `G([x]) = Single` is `G([x]) = Single([x])`, so `G([7])` is 7 (while `G(x) = Single` is rejected, because G's whole `x` is not Single's `[x]`). Nothing converts between sequences and lists.",
        },
        new()
        {
            Id = "alias-forwarding-and-explicit-call",
            Category = "name-resolution",
            Source = "Double(x) = x * 2\nOther(y) = y * 2\n\nAlias = Double\nForward(x) = Double\nExplicit(x) = Other(x)\nFormula = Double + 1\n\nAlias(5)\nForward(5)\nExplicit(5)\nFormula(5)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "10\n10\n10\n11",
            ExpectedRaw = "S[10, 10, 10, 11]",
            ExpectedEmittedCount = 4,
            Probes =
            [
                // Bare forwarding keeps the explicit list closed: Forward still takes one argument.
                new SpecProbe("Double(x) = x * 2\nForward(x) = Double\nForward(5, 6)", "err arity"),
                // A parameter the callee does not need stays unused, and a callee that needs nothing
                // is simply read.
                new SpecProbe("Double(x) = x * 2\nForward(x, unused) = Double\nForward(5, 999)", "ok raw=10 n=1"),
                new SpecProbe("Ten = 10\nAlways(p) = Ten\nAlways(999)", "ok raw=10 n=1"),
                // By name, never by position: G's y reaches Sub's y and G's x reaches Sub's x ...
                new SpecProbe("Sub(y, x) = y - x\nG(x, y) = Sub\nG(10, 3)", "ok raw=-7 n=1"),
                // ... while the written call passes its arguments in the written order.
                new SpecProbe("Sub(y, x) = y - x\nG(x, y) = Sub(x, y)\nG(10, 3)", "ok raw=7 n=1"),
                // Formula lifting shares one binding per name across callees.
                new SpecProbe("F(x) = x * 2\nG(x) = x + 10\nA = F + G\nA(5)", "ok raw=25 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Four ways to define a formula through another one are four different mechanisms. `Alias = Double` is a CALLABLE ALIAS: Alias names Double's callable itself — calling Alias calls Double, with Double's own parameters, and no wrapper or copied signature exists — while Alias stays its own definition. `Forward(x) = Double` is BARE FORWARDING: Forward's explicit parameter list is closed, and Double's parameter `x` is supplied from Forward's existing binding of the SAME NAME — never by position, never renamed, never added (a parameter Double does not need simply stays unused). `Explicit(x) = Other(x)` is an EXPLICIT CALL: the written arguments are passed as written, so the names need not match. `Formula = Double + 1` USES Double inside an expression, so Double's parameter is lifted into Formula by name: `Formula(x) = Double(x) + 1`. So `Forward(x) = Double` is not the same thing as `Forward(x) = Double(x)`: with `Sub(y, x) = y - x`, `G(x, y) = Sub` hands G's `y` to Sub's `y` and gives -7 for `G(10, 3)`, while `G(x, y) = Sub(x, y)` gives 7.",
        },
        new()
        {
            Id = "bare-forwarding-never-renames-a-parameter",
            Category = "name-resolution",
            Source = "Other(y) = y * 2\nBad(x) = Other\n\nBad(5)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "is forwarded by name here, but its parameter 'y'",
            ExpectedDiagnosticCode = DiagnosticCode.UnforwardableParameter,
            IncludeInGeneratorPrompt = true,
            Notes = "FWD-02 bare forwarding (decided September 30 2026): a front-end rejection, so no elaborated Lean program exists; Lean pins the same verdict with `bareForwardingRow` in CoreTests/AliasForwarding.lean.",
            Explanation = "Bare forwarding reuses an existing parameter only under its own name. `Other` needs `y`, and `Bad`'s explicit parameter list declares only `x`, so the definition is rejected: KatLang never renames `x` to `y` and never matches parameters by position. Write the call to pass `x` anyway (`Bad(x) = Other(x)`), or name the parameter `y`.",
        },
        new()
        {
            Id = "bare-forwarding-never-adds-a-parameter",
            Category = "name-resolution",
            Source = "F(p, q) = p + q\nA(p) = F\n\nA(1)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "is forwarded by name here, but its parameter 'q'",
            ExpectedDiagnosticCode = DiagnosticCode.UnforwardableParameter,
            IncludeInGeneratorPrompt = true,
            Notes = "FWD-02 bare forwarding with a closed explicit list (PAR-04): a front-end rejection, so no elaborated Lean program exists.",
            Explanation = "An explicit parameter list is closed: bare forwarding may reuse its parameters by name, but never adds one. `F` still needs `q`, which `A(p)` does not declare, so the definition is rejected instead of inferring `q`. Declare it (`A(p, q) = F`) or supply it explicitly (`A(p) = F(p, 10)`).",
        },
        new()
        {
            Id = "alias-structural-forwarding-and-written-call",
            Category = "name-resolution",
            Source = "Single([x]) = x\n\nAlias = Single\nSameShape([x]) = Single\nExplicit(x) = Single(x)\nConstruct = Single([x])\n\nAlias([7])\nSameShape([7])\nExplicit([7])\nConstruct(7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7\n7\n7\n7",
            ExpectedRaw = "S[7, 7, 7, 7]",
            ExpectedEmittedCount = 4,
            Probes =
            [
                // The alias and the same-pattern forwarding take Single's one-element list; the explicit
                // call takes one whole value and passes it as Single's list argument.
                new SpecProbe("Single([x]) = x\nAlias = Single\nAlias(7)", "err type"),
                new SpecProbe("Single([x]) = x\nSameShape([x]) = Single\nSameShape(7)", "err type"),
                new SpecProbe("Single([x]) = x\nExplicit(x) = Single(x)\nExplicit(7)", "err type"),
                new SpecProbe("Single([x]) = x\nAlias = Single\nSameShape([x]) = Single\nAlias([[7]]), SameShape([[7]])", "ok raw=S[L[7], L[7]] n=2"),
                // Construct builds the list itself, so it takes the element.
                new SpecProbe("Single([x]) = x\nConstruct = Single([x])\nConstruct([7])", "ok raw=L[7] n=1"),
                // An explicit call builds a sequence where a callee needs one.
                new SpecProbe("Add((a, b)) = a + b\nPair(a, b) = Add((a, b))\nPair(2, 3)", "ok raw=5 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "The same four forms apply to structural parameters. `Alias = Single` is a callable alias of Single: it takes exactly the arguments Single takes, its `[x]` included. `SameShape([x]) = Single` is bare forwarding: its own parameter is the same pattern `[x]` under the same name, so Single receives it rebuilt as the list it matched. `Explicit(x) = Single(x)` passes its whole argument `x` as Single's list argument, so `Explicit([7])` is `Single([7])`. `Construct = Single([x])` infers `x` from the written `[x]` and builds the list before calling Single, so it takes the element itself. A bare `Bad(x) = Single` is rejected, because a same-named leaf inside a pattern is not the same parameter.",
        },
        new()
        {
            Id = "bare-forwarding-never-reshapes-a-structural-parameter",
            Category = "name-resolution",
            Source = "Single([x]) = x\nBad(x) = Single\n\nBad([7])",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "does not declare its parameter '[x]' in that form",
            ExpectedDiagnosticCode = DiagnosticCode.UnforwardableParameter,
            IncludeInGeneratorPrompt = true,
            Notes = "FWD-02 structural compatibility is decided at the top-level parameter pattern: a front-end rejection, so no elaborated Lean program exists.",
            Explanation = "Bare forwarding matches whole parameters, not leaf names. Single's parameter is the one-element list pattern `[x]`, while `Bad`'s is a whole value that happens to be called `x`, so the definition is rejected rather than silently building `Single([x])` from it. Write `Bad(x) = Single(x)` to pass `x` whole (then `Bad([7])` is 7), or declare the same pattern: `Bad([x]) = Single`.",
        },
        new()
        {
            Id = "bare-forwarding-never-manufactures-a-sequence",
            Category = "name-resolution",
            Source = "Add((x, y)) = x + y\nG(x, y) = Add\n\nG(2, 3)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "does not declare its parameter '(x, y)' in that form",
            ExpectedDiagnosticCode = DiagnosticCode.UnforwardableParameter,
            Notes = "FWD-02 structural compatibility: a front-end rejection, so no elaborated Lean program exists.",
            Explanation = "Add takes ONE parameter, the pair pattern `(x, y)`. `G(x, y)` declares two whole values with the same names, which is a different signature, so bare forwarding is rejected instead of manufacturing the pair. `G((x, y)) = Add` forwards the same pattern, and `G(x, y) = Add((x, y))` builds the pair explicitly.",
        },
        new()
        {
            Id = "alias-preserves-the-callee-signature",
            Category = "name-resolution",
            Source = "Single([x]) = x\nP(x, x) = x\nE((), []) = 1\nA = Single\nB = A\nC = B\nAP = P\nAE = E\n\nC([7])\nC([[7]])\nAP(5, 5)\nAE((), [])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7\n[7]\n5\n1",
            ExpectedRaw = "S[7, L[7], 5, 1]",
            ExpectedEmittedCount = 4,
            Probes =
            [
                // The alias rejects exactly what the callee rejects, at every level of a chain.
                new SpecProbe("Single([x]) = x\nA = Single\nB = A\nB(7)", "err type"),
                new SpecProbe("Single([x]) = x\nA = Single\nA((1, 2))", "err type"),
                new SpecProbe("Single([x]) = x\nA = Single\nA([])", "err arity"),
                new SpecProbe("Add((x, y)) = x + y\nA = Add\nA([2, 3])", "err type"),
                // Repeated names keep their two independent arguments and their constraint.
                new SpecProbe("P(x, x) = x\nA = P\nA(5, 6)", "err arity"),
                new SpecProbe("P(x, x) = x\nA = P\nA(5)", "err arity"),
                // Binderless structural parameters keep their arity and kinds.
                new SpecProbe("E((), []) = 1\nA = E\nA()", "err arity"),
                new SpecProbe("E((), []) = 1\nA = E\nA([], ())", "err type"),
                // The three collector shapes stay distinct.
                new SpecProbe("C(*xs) = xs\nA = C\nA(1, 2)", "ok raw=L[1, 2] n=1"),
                new SpecProbe("C([*xs]) = xs\nA = C\nA([1, 2])", "ok raw=L[1, 2] n=1"),
                new SpecProbe("C((*xs)) = xs\nA = C\nA((1, 2))", "ok raw=L[1, 2] n=1"),
                new SpecProbe("C([*xs]) = xs\nA = C\nA((1, 2))", "err type"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A definition whose whole body is a bare reference to a callable that declares parameters is a CALLABLE ALIAS: `A = Single` makes A another name for Single's callable — no wrapper and no copied signature — so `A(S)` IS `Single(S)` for every argument supply: the same results, the same failures, the same effects. Nothing is derived from the callee's binder names: repeated names (`AP = P` takes `P(x, x)`'s two arguments, which must be equal), binderless groups (`AE = E` takes `E((), [])`'s two structural parameters), collectors and structural kinds are the callee's own, through every level of a chain (`C = B`, `B = A`). The alias is still its own definition: its name, its declaration and its cached bare value belong to it.",
        },
        new()
        {
            Id = "alias-of-a-builtin-is-the-builtin",
            Category = "name-resolution",
            Source = "C = count\nI = if\nM = map\nBad(x) = x / 0\n\nC([1, 2, 3])\nI(true, 1, 1 / 0)\nM([], Bad)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3\n1\n[]",
            ExpectedRaw = "S[3, 1, L[]]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // A loop keeps its own minimum arity, and a chain normalizes to the one builtin.
                new SpecProbe("R = repeat\nInc(x) = x + 1\nR(Inc)", "err arity"),
                new SpecProbe("A = count\nB = A\nC = B\nC([1, 2])", "ok raw=2 n=1"),
                new SpecProbe("T = take\nT([1, 2, 3], 2)", "ok raw=L[1, 2] n=1"),
                // An alias is the builtin wherever a callable is used: a callback ...
                new SpecProbe("Cnt = count\nmap([[1], [1, 2]], Cnt)", "ok raw=L[1, 2] n=1"),
                // ... bare forwarding by the builtin's own parameter names, and formula lifting.
                new SpecProbe("C = count\nW(collection) = C\nW([1, 2])", "ok raw=2 n=1"),
                new SpecProbe("C = count\nK = C + 1\nK([1, 2])", "ok raw=3 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Callable aliases as binding indirection (decided October 1 2026): formerly a bare row naming a non-Math builtin stayed an ordinary property, so `C([1, 2, 3])` was an arity error.",
            Explanation = "A definition whose whole body is the name of a callable that takes parameters is a CALLABLE ALIAS: the new name is a second name for the very same callable. That holds for every builtin. `C = count` makes `C([1, 2, 3])` exactly `count([1, 2, 3])`; `I = if` keeps `if`'s laziness, so `I(true, 1, 1 / 0)` is 1 and the division never runs; `M = map` keeps `map`'s rule that the callback is only called per element, so `M([], Bad)` is `[]` without calling `Bad`. An alias of an alias is the same callable again.",
        },
        new()
        {
            Id = "alias-of-a-clause-family-dispatches-as-the-family",
            Category = "name-resolution",
            Source = "Fact(0) = 1\nFact(n) = n * Fact(n - 1)\nF = Fact\n\nF(4)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "24",
            ExpectedRaw = "24",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // The family's own dispatch failure, named by the written callee.
                new SpecProbe("Fact(0) = 1\nFact(n) = n * Fact(n - 1)\nF = Fact\nF(1, 2)", "err arity"),
                // A family whose clauses name no position can be aliased too.
                new SpecProbe("S(1) = 1\nS(-1) = -1\nSA = S\nSA(-1)", "ok raw=-1 n=1"),
                new SpecProbe("S(1) = 1\nS(-1) = -1\nSA = S\nSA(0)", "err branch"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Callable aliases as binding indirection (decided October 1 2026): formerly a clause family was never an alias target (PV-14), so `F(4)` was an arity error.",
            Explanation = "A clause family is aliased like any other callable: `F = Fact` makes `F(4)` exactly `Fact(4)`, choosing the clause the way `Fact` itself does, and `F(1, 2)` fails exactly as `Fact(1, 2)` does. Aliasing needs only the callable itself, not parameter names, so even a family whose clauses name no argument position — `S(1) = 1`, `S(-1) = -1` — can be aliased.",
        },
        new()
        {
            Id = "bare-forwarding-needs-parameter-names",
            Category = "name-resolution",
            Source = "S(1) = 1\nS(-1) = -1\nSA = S\nW(x) = SA\n\nW(1)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "has no parameter names to forward by",
            ExpectedDiagnosticCode = DiagnosticCode.UnforwardableCallable,
            IncludeInGeneratorPrompt = true,
            Notes = "Narrowed Q-77 (decided October 1 2026): a closed lone row whose callable has no forwarding contract is a front-end error, never a silent zero-argument demand. A front-end rejection, so no elaborated Lean program exists; Lean pins the verdict with `bareForwardingRowOf`.",
            Explanation = "Bare forwarding hands a callable its parameters from existing parameters of the SAME NAMES, so it needs a callable whose parameters have names. `S(1) = 1` and `S(-1) = -1` name nothing — a literal clause pattern is not a parameter name — so `W(x) = SA` is rejected: `SA` is an alias of `S`, and there is no name `x` could be forwarded by. Call the family with explicit arguments instead: `W(x) = SA(x)`.",
        },
        new()
        {
            Id = "alias-arguments-take-the-targets-roles",
            Category = "variadic-calls",
            Source = "Inc(x) = x + 1\nI = if\nK = I(c, Inc, 0)\n\nK(true, 4)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5",
            ExpectedRaw = "5",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // The same for a Math function and for a builtin's collection slot.
                new SpecProbe("A = abs\nInc(x) = x + 1\nK = A(Inc)\nK(-5)", "ok raw=4 n=1"),
                new SpecProbe("C = count\nPair(x) = x, x\nK = C(Pair)\nK(1)", "ok raw=2 n=1"),
            ],
            Notes = "Callable aliases as binding indirection (decided October 1 2026; fixes X-45): formerly an alias was classified as a user callee, whose argument stays neutral, so `Inc` reached `if` as a callable and `K(true, 4)` failed.",
            Explanation = "A call through an alias treats its arguments exactly as a call of the target does. `if` needs the VALUE of each of its arguments, so in `K = I(c, Inc, 0)` the formula uses `Inc`'s value and takes its input: `K(c, x) = I(c, Inc(x), 0)`, and `K(true, 4)` is 5 — just as `K = if(c, Inc, 0)` would be.",
        },
        new()
        {
            Id = "alias-is-the-targets-callable",
            Category = "name-resolution",
            Source = "P(f, f) = f(7)\nOnly(*xs) = 0\nA = Only\n\nP(A, Only)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0",
            ExpectedRaw = "0",
            ExpectedEmittedCount = 1,
            Notes = "Callable aliases as binding indirection (decided October 1 2026): formerly the alias was a wrapper callable of its own, so the repeated `f` saw two different callables and the call failed.",
            Explanation = "An alias and its target are one callable. `P(f, f)` requires its two arguments to be the same callable, and `A = Only` makes `A` another name for `Only`'s callable, so `P(A, Only)` binds `f` once and gives `Only(7)`, which is 0. The two names are still separate definitions: each keeps its own cached value when it is read without arguments.",
        },
        new()
        {
            Id = "alias-declares-only-its-own-members",
            Category = "name-resolution",
            Source = "Lib(x) = {\n  K = 5\n  x\n}\nA = Lib\nNavigate(f) = f.K\n\nLib.K\nNavigate(A)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5\n5",
            ExpectedRaw = "S[5, 5]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // Written member access on the alias does not reach Lib's member K: `A.K` falls back to
                // a lexical `K`, which nothing declares, so the program has an unresolved input.
                new SpecProbe("Lib(x) = {\n  K = 5\n  x\n}\nA = Lib\nA.K", "err unresolvedImplicitParams"),
            ],
            Notes = "Callable aliases as binding indirection (decided October 1 2026): an alias is not a namespace alias.",
            Explanation = "An alias names a CALLABLE, not a namespace. `A = Lib` declares no members of its own, so writing `A.K` does not look inside `Lib` — the dot falls back to an ordinary function named `K`. But the callable you pass through the alias IS `Lib`: `Navigate(A)` gives `Navigate` the callable `Lib`, whose member `K` it reads exactly as `Navigate(Lib)` would.",
        },
        new()
        {
            Id = "open-of-a-callable-alias-is-refused",
            Category = "errors",
            Source = "Lib(x) = x\nA = Lib\nB = {\n  open A\n  1\n}\n\nB",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "is a callable alias, not a namespace",
            ExpectedDiagnosticCode = DiagnosticCode.IllegalInOpen,
            Notes = "Callable aliases as binding indirection (decided October 1 2026): a front-end rejection, so no elaborated Lean program exists; Lean refuses the same open with `Algorithm.requiresArguments`.",
            Explanation = "`open` imports the members of an algorithm that needs no call. An alias is a name for a callable, never a namespace, so `open A` is rejected whatever its target is.",
        },
        new()
        {
            Id = "bare-forwarding-keeps-each-parameter-kind",
            Category = "name-resolution",
            Source = "Add((a, b)) = a + b\nColl(*vs) = vs\nMid([first, *middle, last]) = [first, middle, last]\nPair((a, b)) = Add\nMany(*vs) = Coll\nSame([first, *middle, last]) = Mid\n\nPair((2, 3))\nMany(1, 2)\nSame([1, 2, 3, 4])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5\n[1, 2]\n[1, [2, 3], 4]",
            ExpectedRaw = "S[5, L[1, 2], L[1, L[2, 3], 4]]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // A collecting parameter forwards what it collected, 0, 1 or N arguments.
                new SpecProbe("Coll(*vs) = vs\nMany(*vs) = Coll\nMany()", "ok raw=L[] n=1"),
                new SpecProbe("Coll(*vs) = vs\nMany(*vs) = Coll\nMany(7)", "ok raw=L[7] n=1"),
                // The SOURCE binding's kind decides the spread: a fixed binding is one collected
                // item, and a collected list reaches a fixed parameter whole.
                new SpecProbe("Coll(*vs) = vs\nOne(vs) = Coll\nOne((1, 2))", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("One(vs) = vs\nMany(*vs) = One\nMany(1, 2)", "ok raw=L[1, 2] n=1"),
                // A binding the local list does not declare is the enclosing one a written name
                // would denote (Q-04); the local y stays unused.
                new SpecProbe("F(x) = x\nOuter(x) = {\n  Local(y) = F\n  Local(5)\n}\nOuter(100)", "ok raw=100 n=1"),
                // A local parameter of the same name is the nearer binding.
                new SpecProbe("F(x) = x\nOuter(x) = {\n  Local(x) = F\n  Local(5)\n}\nOuter(100)", "ok raw=5 n=1"),
                // A clause branch forwards the binders of its own pattern.
                new SpecProbe("F(n) = n * 10\nG(0) = 0\nG(n) = F\nG(0), G(3)", "ok raw=S[0, 30] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Bare forwarding supplies each parameter of the callee from the binding of the same name, keeping the binding as it is: a structural parameter declared with the same pattern is rebuilt as its own list or sequence (`Pair((a, b)) = Add` is `Add((a, b))`, `Same([first, *middle, last]) = Mid` is `Mid([first, middle*, last])`), and a collecting parameter re-spreads what it collected into a collecting parameter of the same name (`Many(*vs) = Coll` is `Coll(vs*)`). Only the source binding's kind decides a spread, so a fixed binding reaches a collector as one item and a collected list reaches a fixed parameter whole. A name the explicit list does not declare may still be an enclosing parameter binding — the one a written name would denote there — and is reused as it is; nothing is ever added to the list or renamed.",
        },
        new()
        {
            Id = "written-call-infers-its-written-names",
            Category = "name-resolution",
            Source = "Add((a, b)) = a + b\nSingle([a]) = a\nG = Add((x, y))\nConstruct = Single([x])\n\nG(2, 3)\nConstruct(7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5\n7",
            ExpectedRaw = "S[5, 7]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // Renaming the callee's binders changes nothing for the caller.
                new SpecProbe("Add((left, right)) = left + right\nG = Add((x, y))\nG(2, 3)", "ok raw=5 n=1"),
                // G takes the two names it writes, in first-appearance order.
                new SpecProbe("Add((a, b)) = a + b\nG = Add((x, y))\nG(2)", "err arity"),
                new SpecProbe("Sub((a, b)) = a - b\nG = Sub((y, x))\nG(2, 3)", "ok raw=-1 n=1"),
                new SpecProbe("Add((a, b)) = a + b\nG(x, y) = Add((x, y))\nG(2, 3)", "ok raw=5 n=1"),
                // A name written twice is one input.
                new SpecProbe("Two(a, b) = [a, b]\nG = Two(x, x)\nG(7)", "ok raw=L[7, 7] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A written call is authoritative: `G = Add((x, y))` takes its parameters from the free names WRITTEN in its arguments, `x` then `y`, so it is exactly `G(x, y) = Add((x, y))` — and the sequence `(x, y)` stays one argument to Add. Add's own binder names never reach G: renaming them to `left` and `right` changes nothing. `Construct = Single([x])` likewise takes one parameter `x` and builds the one-element list itself.",
        },
        new()
        {
            Id = "repeated-callable-success-preserves-both-channels",
            Category = "variadic-calls",
            Source = "B(*xs) = 5 + xs.count\nP(f, f, f, f, f) = [f, f(1), map([7], f)]\nP(B, 5, B, 5, 5)\nP(5, B, 5, 5, B)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[5, 6, [6]]\n[5, 6, [6]]",
            ExpectedRaw = "S[L[5, 6, L[6]], L[5, 6, L[6]]]",
            ExpectedEmittedCount = 2,
            Explanation = "Successful permutations retain the same value and callable channels. Repeated references to B are the same callable, so f reads its bound value 5 while f(1) and the mapper invoke B and produce 6. The rule applies uniformly to five occurrences as well as one, two, or three.",
        },
        new()
        {
            Id = "repeated-genuine-aliases-preserve-complete-binding",
            Category = "variadic-calls",
            Source = "A(*xs) = 5 + xs.count\nP(f, f) = [f, f.count, f(1), map([7], f)]\nBoth(left, right) = [P(left, right), P(right, left)]\nShare(original) = Both(original, original)\nShare(A)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[[5, 1, 6, [6]], [5, 1, 6, [6]]]",
            ExpectedRaw = "L[L[5, 1, 6, L[6]], L[5, 1, 6, L[6]]]",
            ExpectedEmittedCount = 1,
            IncludeInGeneratorPrompt = true,
            Explanation = "The parameters left and right are genuine aliases of the one callable A. Both argument orders bind successfully and preserve all channels: f reads 5, its count is 1, and both direct invocation and the callback invoke A. Successful permutations preserve channel availability, values, counts and callable identity. Forwarding transports the same demandable cells and performs no VALUE evaluation.",
        },
        new()
        {
            Id = "repeated-callable-identity-includes-captured-activation",
            Category = "variadic-calls",
            Source = "P(f, f) = f(1)\nOuter(n, previous) = {\n  Inner(*xs) = 5 + n * xs.count\n  if(n == 1, Outer(2, Inner), P(previous, Inner))\n}\nOuter(1, 0)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Explanation = "Two activations of one nested declaration are different callables even when their zero-argument values agree. The earlier Inner captures n=1 and the later Inner captures n=2; selecting either would change f(1), so the repeated binding rejects.",
        },
        new()
        {
            Id = "repeated-dot-results-have-distinct-wrapper-identities",
            Category = "variadic-calls",
            Source = "Obj = { public V = 5 }\nP(f, f) = f\nP(Obj.V, Obj.V)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5",
            ExpectedRaw = "5",
            ExpectedEmittedCount = 1,
            Explanation = "A declared structural member supplies that member's stable callable identity without a value demand. Both `Obj.V` occurrences name the same member, so their equal values and identical callable channels satisfy the repeated-name constraint. Computed values do not acquire wrapper callable identities.",
        },
        new()
        {
            Id = "repeated-forwarded-dot-wrapper-keeps-identity",
            Category = "variadic-calls",
            Source = "Obj = { public V = 5 }\nP(f, f) = f()\nPass(g) = P(g, g)\nPass(Obj.V)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5",
            ExpectedRaw = "5",
            ExpectedEmittedCount = 1,
            Explanation = "A structural member path supplies that member's own callable identity (a dot expression has one callable identity in every position; no wrapper is involved). Forwarding the parameter keeps that one identity, so both occurrences of `f` receive the same callable and the repeated-name constraint holds; `f()` is the member's ordinary fresh call, giving 5.",
        },
        new()
        {
            Id = "collecting-pattern-list-merges-after-the-collector",
            Category = "variadic-calls",
            Source = "Bad = 1 / 0\nP(x, *rest, x) = x\n\nP(1, Bad, 2)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // The prefix binds and checks its repeated names before the suffix binds.
                new SpecProbe("Bad = 1 / 0\nP(x, x, *rest, (a, b)) = a\nP(1, 2, Bad)", "err arity"),
                // The suffix x conflicts immediately, before the next structural pattern.
                new SpecProbe("Bad = 1 / 0\nP(x, *rest, x, (a, b)) = a\nP(1, 9, 2, Bad)", "err arity"),
                new SpecProbe("P(x, *rest, x) = rest\nP(1, 9, 1)", "ok raw=L[9] n=1"),
            ],
            Explanation = "A collector binds a lazy slice of supplied cells. Pattern traversal continues in written order, and the suffix `x` conflicts with the prefix immediately, before the collector or a later structural argument is demanded. A demanded collector materializes its entire slice from left to right; an unused collector performs no value evaluations.",
        },
        new()
        {
            Id = "redundant-call-parens-canonical",
            Category = "variadic-calls",
            Source = "Inner = (1, 2, 3)\nCountSequenceValue((*values)) = values.count\nNestedCount([(*values)]) = values.count\n\nCountSequenceValue(Inner)\nCountSequenceValue((Inner))\nCountSequenceValue(((1, 2, 3)))\nNestedCount([(1, 2, 3)])\nNestedCount(([(1, 2, 3)]))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3\n3\n3\n3\n3",
            ExpectedRaw = "S[3, 3, 3, 3, 3]",
            ExpectedEmittedCount = 5,
            Probes =
            [
                new SpecProbe("NestedCount([(*values)]) = values.count\nNestedCount((1, 2, 3))", "err type"),
                new SpecProbe("NestedCount([(*values)]) = values.count\nNestedCount(([[1, 2, 3]]))", "err type"),
                new SpecProbe("NestedCount([(*values)]) = values\nNestedCount(7)", "err type"),
                new SpecProbe("NestedCount([(*values)]) = values\nNestedCount([()]), NestedCount(([(1, 2)]))", "ok raw=S[L[], L[1, 2]] n=2"),
                new SpecProbe("CountSequenceValue((*values)) = values.count\nCountSequenceValue(((1, 2), 3))", "ok raw=2 n=1"),
                new SpecProbe("S = 1, 2\nF((a, b)) = a + b\nF({S})", "ok raw=3 n=1"),
                new SpecProbe("A = [[1, 2], [3]]\nP((*xs)) = xs\nP((A*))", "ok raw=L[L[1, 2], L[3]] n=1"),
            ],
            Explanation = "Parentheses group syntax; they do not introduce a semantic boundary. A pattern-shaped callee opens the argument's VALUE: `Inner`, `(Inner)`, and `((1, 2, 3))` are all the sequence value `(1, 2, 3)`, so the collecting parameter collects its three items in every spelling — a redundant group is never a written level for the pattern to consume, and a single-row block `{S}` or a captured spread `(A*)` is likewise just its value. A nested pattern `[(*values)]` opens two real boundaries, each of its own kind: a one-element LIST whose element is a SEQUENCE (unary sequence structure never survives normalization, so a one-element outer level is always a list). A sequence, a list element, or a scalar where the other kind is required is the pattern's kind mismatch. Non-unary structure is preserved: `((1, 2), 3)` counts 2.",
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
                new SpecProbe("F(0, 0) = 100\nF(x, y) = x + y\nA = (1, 2)\nF(A)", "err arity"),
            ],
            Explanation = "Explicit call-site spread has identical meaning for every callable shape: `F(A*)` supplies A's spread items as ordinary argument slots BEFORE clause selection, so the two-binder clause binds x = 1, y = 2. The unspread `F(A)` supplies ONE closed argument, which no two-argument clause can match.",
            IncludeInGeneratorPrompt = true,
        },
        new()
        {
            Id = "patterned-user-call-is-one-value-boundary",
            Category = "item-supply-vs-value",
            Source = "F([x]) = 1, 2\nF([7])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2)",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("F([x]) = x, x\nF([7])", "ok raw=S[7, 7] n=1"),
                new SpecProbe("F((x, y)) = x, y\nF((1, 2))", "ok raw=S[1, 2] n=1"),
                // The flat-parameter spelling must reach the same boundary.
                new SpecProbe("F(x) = 1, 2\nF(7)", "ok raw=S[1, 2] n=1"),
            ],
            Explanation = "A user call is a VALUE boundary on every callee shape, including a sequence-value-patterned one: the body's multi-slot output is combined into one value and the emitted count is re-counted to that value's own count (1). Body/root output accumulation is not a value boundary, so without the re-count the call would leak its body's two-slot supply into the caller and emit two rows instead of one.",
        },
        new()
        {
            Id = "conditional-one-element-list-pattern",
            Category = "conditionals",
            Source = "F([x]) = x\nF(n) = 0\n\nF([7])\nF([1, 2])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7\n0",
            ExpectedRaw = "S[7, 0]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // A scalar and a sequence are no lists: they fall through to the next clause.
                new SpecProbe("F([x]) = x\nF(n) = 0\nF(7)", "ok raw=0 n=1"),
                new SpecProbe("F([x]) = x\nF(n) = 0\nF((1, 2))", "ok raw=0 n=1"),
                // The element is bound whole, whatever it is.
                new SpecProbe("F([x]) = x\nF(n) = 0\nF([[1, 2]])", "ok raw=L[1, 2] n=1"),
                // List patterns tell every list cardinality apart.
                new SpecProbe("Kind([]) = 0\nKind([x]) = 1\nKind([x, y]) = 2\nKind(v) = 9\nKind([]), Kind([5]), Kind([5, 6]), Kind([5, 6, 7]), Kind(()), Kind(5)", "ok raw=S[0, 1, 2, 9, 9, 9] n=6"),
            ],
            Explanation = "In a clause family the one-element list pattern `[x]` matches exactly a one-element list and binds its element whole; a longer list, a sequence, or a scalar does not match that clause and falls through. List patterns distinguish every list cardinality — `[]`, `[x]`, `[x, y]`. There is no one-item sequence pattern: `(x)` is rejected by the front end, and a plain binder `F(x)` is how a clause takes any one argument whole.",
        },
        new()
        {
            Id = "conditional-sequence-pattern-matches-sequence-values-only",
            Category = "conditionals",
            Source = "F((x, y)) = x + y\nF(z) = 0\n\nF((2, 3))\nF([2, 3])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5\n0",
            ExpectedRaw = "S[5, 0]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // With no clause that accepts a list, the list argument matches nothing.
                new SpecProbe("F((x, y)) = x + y\nF((x, y, z)) = 0\n\nF([2, 3])", "err branch"),
                // The list pattern is the list twin.
                new SpecProbe("F([x, y]) = x + y\nF(z) = 0\n\nF([2, 3])", "ok raw=5 n=1"),
                // An ordinary single-clause definition follows the same kind law.
                new SpecProbe("PairSum((x, y)) = x + y\nPairSum([2, 3])", "err type"),
            ],
            Explanation = "In a clause family a sequence pattern matches sequence values only: an exact list argument does not match `(x, y)` even when its element count fits, so it falls through to a later clause, or fails with no matching branch when none accepts it. The list pattern `[x, y]` is the list twin. An ordinary single-clause definition follows the same kind law, where a wrong-kind value is the pattern's type error instead of a fall-through.",
        },
        new()
        {
            Id = "empty-structural-patterns-are-distinct-heads",
            Category = "conditionals",
            Source = "Kind(()) = 'empty sequence'\nKind([]) = 'empty list'\nKind(x) = 'other'\n\nKind(())\nKind([])\nKind(0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "empty sequence\nempty list\nother",
            ExpectedRaw = "S['empty sequence', 'empty list', 'other']",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // Each empty pattern is a valid clause head of its own.
                new SpecProbe("F(()) = 1\nF(x) = 2\nF(()), F(5)", "ok raw=S[1, 2] n=2"),
                new SpecProbe("F([]) = 1\nF(x) = 2\nF([]), F(5)", "ok raw=S[1, 2] n=2"),
                // Neither empty pattern matches the other kind's empty value.
                new SpecProbe("F(()) = 1\nF(x) = 2\nF([])", "ok raw=2 n=1"),
                new SpecProbe("G([]) = 1\nG(x) = 2\nG(())", "ok raw=2 n=1"),
                // Without a catch-all, any other value matches no clause.
                new SpecProbe("H(()) = 1\nH([]) = 2\nH(0)", "err branch"),
                // A single clause is an ordinary definition: the wrong kind is its type error.
                new SpecProbe("E(()) = 1\nE([])", "err type"),
            ],
            Explanation = "The empty sequence pattern `()` and the empty list pattern `[]` are ordinary clause heads: `()` matches only the empty sequence and `[]` only the empty list, so one family can tell them apart and send everything else to a catch-all. They are different heads, never duplicates, and neither matches the other kind's empty value. In a single-clause definition a wrong kind is the pattern's type error instead of a fall-through.",
        },
        new()
        {
            Id = "expression-is-not-a-pattern",
            Category = "conditionals",
            Source = "F(1 + 1) = 2\nF(2)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Expected ')' but found '+'",
            ExpectedDiagnosticCode = DiagnosticCode.UnexpectedToken,
            Probes =
            [
                // The literal pattern the arithmetic was meant to compute is the valid spelling.
                new SpecProbe("F(2) = 2\nF(x) = 0\nF(1 + 1), F(3)", "ok raw=S[2, 0] n=2"),
                // A negative number literal is a literal pattern, not an expression.
                new SpecProbe("F(-1) = 1\nF(x) = 0\nF(0 - 1), F(1)", "ok raw=S[1, 0] n=2"),
            ],
            Notes = "Source-level pattern-grammar diagnostic; no elaborated Lean program exists for a rejected parse, and Lean's Pattern has no expression constructor. EmptyStructuralPatternLawTests pins the other expression shapes (a binder operand, a list pattern, a call, a nested group) with their exact diagnostics.",
            Explanation = "A clause head is written in the pattern language, not as an expression: a pattern is a name, a number, string or Boolean literal (a number may carry a leading `-`), or a sequence pattern `( … )` or list pattern `[ … ]` of patterns, the empty `()` and `[]` included (an ordinary definition may also have one collecting `*name` per level). Arithmetic such as `1 + 1` is not a pattern and is rejected at the operator; write the value itself, `F(2)`, or bind the argument and compare it in the body.",
        },
        new()
        {
            Id = "conditional-clauses-share-top-level-arity",
            Category = "conditionals",
            Source = "F(0) = 1\nF(x, y) = 2\n\nF(0)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "must have the same top-level pattern arity",
            ExpectedDiagnosticCode = DiagnosticCode.BranchArityMismatch,
            Probes =
            [
                // Literal-vs-variable is what distinguishes branches of one arity.
                new SpecProbe("F(0) = 1\nF(x) = x + 1\n\nF(0)\nF(5)", "ok raw=S[1, 6] n=2"),
                // A captured pair is ONE written output slot, so it is a legal branch result beside a scalar one.
                new SpecProbe("F(0) = 1\nF(x) = (1, 2)\n\nF(5)", "ok raw=S[1, 2] n=1"),
            ],
            Explanation = "Arity never distinguishes branches: all clauses of one family share one top-level pattern arity, and the front end rejects a family whose clauses disagree before anything runs — even though `F(0)` would have matched the first clause. Branches are told apart by their pattern shape alone — literals, string patterns, sequence-value structure, repeated-name constraints, or a catch-all — tried top to bottom.",
        },
        new()
        {
            Id = "conditional-clauses-share-top-level-output-arity",
            Category = "conditionals",
            Source = "F(0) = 1\nF(x) = 1, 2\n\nF(5)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "must have the same top-level output arity",
            ExpectedDiagnosticCode = DiagnosticCode.BranchOutputArityMismatch,
            Explanation = "The clauses of one family also share one top-level output arity — the same number of written output slots. `F(x) = 1, 2` writes two slots beside the one-slot `F(0) = 1`, so the family is rejected by the front end; when one branch's result is a pair, write it as the one captured slot `(1, 2)`.",
        },
        new()
        {
            Id = "conditional-clause-head-rejects-extra-arguments",
            Category = "conditionals",
            Source = "F(0) = 1\nF(n) = 2\nF(1, 2)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // A literal head must not match on the first argument alone.
                new SpecProbe("F(0) = 1\nF(n) = 2\nF(0, 9)", "err arity"),
                new SpecProbe("F(0) = 1\nF(n) = 2\nF()", "err arity"),
                new SpecProbe("F(0) = 1\nF(n) = 2\nF(1)", "ok raw=2 n=1"),
            ],
            Explanation = "A one-argument family requires exactly one supplied slot. A call with two arguments or no arguments reports ordinary arity mismatch before evaluating ordinary argument cells or attempting a clause. Surplus arguments are never discarded; a correct-count call that fails every pattern reports no matching branch.",
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
                new SpecProbe("((1, 2)) == (1, 2)", "ok raw=true n=1"),
                new SpecProbe("count(((1, 2)))", "ok raw=2 n=1"),
            ],
            Explanation = "`((1, 2))` is not a one-item wrapper around a pair — redundant unary sequence structure normalizes to the pair itself. Orphan wrappers are not writable KatLang values.",
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
                new SpecProbe("x = ((1, 2), (3, 4))\nx:0", "ok raw=S[1, 2] n=1"),
                new SpecProbe("x = ((1, 2), (3, 4))\nx == ((1, 2), (3, 4))", "ok raw=true n=1"),
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
            Id = "open-local-only-through-capture-row",
            Category = "access-boundaries",
            Source = "Outer(p) = {\n    open Lib\n    Lib = { public G = { Q = p + 1\n    (Q) } }\n    G\n}\nOuter(1)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "2",
            ExpectedRaw = "2",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("Outer(p) = {\n    open Lib\n    Lib = { public G = { Q = p + 1\n    { Q } } }\n    G\n}\nOuter(1)", "ok raw=2 n=1"),
                new SpecProbe("Outer(p) = {\n    open Lib\n    Lib = { public G = { Q = p + 1\n    Id(Q) } }\n    Id(v) = v\n    G\n}\nOuter(1)", "ok raw=2 n=1"),
                // Outside `Outer` the same member is selected and refused at the access.
                new SpecProbe("Outer(p) = {\n    public Lib = { public G = { Q = p + 1\n    (Q) } }\n    0\n}\nA = {\n    open Outer.Lib\n    G\n}\nA", "err localOnlyProperty"),
            ],
            Explanation = "Exposure follows ownership through every layer: `G` depends on `p` (owned by `Outer`) through its own local `Q` whether the reference is written bare, in a capture row, in a nested block, or in a call argument, so it is local-only. Local-only is context-dependent, not universal: `open Lib` provides `G` to Outer's own body, which lies inside the owner of the captured `p`, and refuses it to a body outside `Outer`.",
        },
        new()
        {
            Id = "open-self-contained-beside-same-named-sibling",
            Category = "access-boundaries",
            Source = "Outer(p) = {\n    open Lib\n    Lib = {\n        public G = { Q = 7\n        (Q) }\n        Q = p + 1\n    }\n    G\n}\nOuter(1)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7",
            ExpectedRaw = "7",
            ExpectedEmittedCount = 1,
            Explanation = "`G`'s capture row names its OWN self-contained `Q = 7`, never Lib's ancestor-capturing `Q = p + 1`, so `G` stays exported through `open Lib`.",
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
            Explanation = "After structural member lookup fails, a dot member name that is a parameter of the calling context resolves exactly like the plain callee: `a.t` and `t(a)` agree, including algorithm-valued parameters. The lexical fallback uses the owner walk, so a captured parameter beats farther properties and opens. Properties matching same-owner or enclosing parameters are declaration errors. Structural members of the resolved receiver always take precedence first.",
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
                new SpecProbe("K(t, a) = a.t\nK({a+1}, 7)", "ok raw=8 n=1"),
                new SpecProbe("K = a~~.t\nK({a+1}, 7)", "ok raw=8 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Grace composes with ordinary DotCall. Base occurrence order for `a.t` is receiver then participating fallback: `(a, t)`. In `a~.t`, ordinary postfix Grace moves `a` one place later; in `a.~t`, ordinary prefix Grace moves `t` one place earlier. Both infer `(t, a)` — the order the explicit spelling `K(t, a) = a.t` declares — and all three sources elaborate to the same ordinary `a.t` body. Grace is valid only on such FREE names that the algorithm infers as its own parameters: under an explicit parameter list (`K(t, a) = a~.t`) nothing is inferred, so the marker has no parameter to weight and is a front-end error.",
        },
        new()
        {
            Id = "grace-dot-keeps-structural-precedence",
            Category = "access-boundaries",
            Source = "V(x) = 99\nObj = {\n    public V = 42\n    0\n}\nRead = o~.V\n\nObj.V\nRead(Obj)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "42\n42",
            ExpectedRaw = "S[42, 42]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                new SpecProbe("Obj = {\n    public V = 42\n    0\n}\nRead = o.~V\nRead({x}, Obj)", "ok raw=42 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`~` changes inferred parameter ORDER only — never member selection. `Read = o~.V` graces the FREE receiver name `o` (the marker is valid: `o` becomes Read's own inferred parameter — as the only one it cannot move, and that saturation is no error), and `Read(Obj)` performs ordinary structural-first DotCall lookup, reading Obj's own `V` even though a lexical `V` exists — exactly like the direct `Obj.V`. With no lexical `V` declaration, prefix member Grace behaves the same way on an opaque receiver: `Read = o.~V` infers `(V, o)`, and `Read({x}, Obj)` still reads Obj's structural `V`. To call the lexical `V` with Obj's value, write the call `V(Obj)`. A marker on the bound `Obj` itself (`Obj~.V`) has no inferred parameter to weight and is rejected instead of being ignored.",
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
            Explanation = "An explicit parameter list is CLOSED, and it asks the definite question: a member name whose fallback merely MAY be selected — the runtime receiver may declare it — is not required to be declared. `K(x) = x.V` keeps arity 1, resolving `V` structurally on the runtime receiver and reaching the lexical fallback only when the receiver has no such member. A fallback that MUST be selected is checked like the call it is (`closed-list-must-fallback-name-is-checked`).",
        },
        new()
        {
            Id = "dot-fallback-on-known-receiver-stays-valid",
            Category = "access-boundaries",
            Source = "Lib = {\n    public Double(x) = 2 * x\n}\nDubel(a, b) = b * 3\n\nLib.Dubel(4)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "12",
            ExpectedRaw = "12",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // The prelude's Math receiver is no different: a visible lexical
                // `Ceiling` makes `Math.Ceiling(2.1)` the call `Ceiling(Math, 2.1)`.
                new SpecProbe("Ceiling(a, b) = b * 2\nMath.Ceiling(2.1)", "ok raw=4.2 n=1"),
                // Without the lexical callable, the fallback name is an ordinary
                // unresolved name and is inferred as an implicit parameter — never a
                // missing-member rejection. The diagnostic is receiver-aware (it names
                // the receiver and suggests `Lib.Double` / `Math.Ceil`); the outcome is not.
                new SpecProbe("Lib = {\n    public Double(x) = 2 * x\n}\nLib.Dubel(4)", "err unresolvedImplicitParams"),
                new SpecProbe("Math.Ceiling(2.1)", "err unresolvedImplicitParams"),
                // Supplying the parameter runs the ordinary fallback call with that callable.
                new SpecProbe("P = Math.Ceiling(2.1)\nTwice(a, b) = b * 2\nP(Twice)", "ok raw=4.2 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A member name the receiver does not declare is not an error by itself, and a statically known receiver (`Math`, a block, a module) gets no special status: `Lib.Dubel(4)` has no structural `Dubel`, so it is the ordinary lexical fallback `Dubel(Lib, 4)` — `a` receives the `Lib` algorithm and `b` receives `4`. Static receiver knowledge never changes the resolution: it improves the DIAGNOSTIC when no such callable is visible (the report names the receiver, explains the fallback, and suggests a real member), and it makes the fallback statically CERTAIN — so in an implicitly parameterized body the name is inferred like a written callee name, while under a closed parameter list it is checked like one (`closed-list-must-fallback-name-is-checked`).",
        },
        // ==================== law system U: route, identity, syntax, static obligation (Q-17, Q-18, Q-75) ====================
        new()
        {
            Id = "dot-string-declared-member-wins",
            Category = "strings",
            Source = "Obj = {\n    public string = 5\n    7\n}\n\nObj.string",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5",
            ExpectedRaw = "5",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("Obj = {\n    public string(x) = x * 2\n    7\n}\nObj.string(5)", "ok raw=10 n=1"),
                new SpecProbe("Obj = {\n    public string = {\n        public Q = 3\n        4\n    }\n    7\n}\nObj.string.Q", "ok raw=3 n=1"),
                new SpecProbe("Apply(f, v) = f(v)\nObj = {\n    public string(x) = x * 2\n    7\n}\nApply(Obj.string, 5)", "ok raw=10 n=1"),
                // Selection, then accessibility: an inaccessible or branch-only member is an error, never the intrinsic.
                new SpecProbe("G(x) = {\n    public Sub = {\n        public string = x + 1\n        0\n    }\n    0\n}\nG.Sub.string", "err localOnlyProperty"),
                new SpecProbe("F(0) = {\n    string = 1\n    0\n}\nF(n) = n\nF.string", "err localOnlyProperty"),
            ],
            Explanation = "A dot edge selects a DECLARED member first, whatever its spelling: a member named `string` is selected like any member — read, called, navigated, supplied as a callable — and its accessibility is checked after selection, so a local-only or branch-only `string` member is the LocalOnlyProperty error, never a fall-through to the intrinsic. Declarations named `string` are ordinary declarations.",
        },
        new()
        {
            Id = "dot-string-intrinsic-on-structural-miss",
            Category = "strings",
            Source = "string(x) = 99\nObj = {\n    public V = 1\n    7\n}\n\n3.string\nObj.string\nstring(3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3\n7\n99",
            ExpectedRaw = "S['3', '7', 99]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // The fluent spread receiver is the lexical call `string(A*)`.
                new SpecProbe("string(x) = 99\nA = 5\nA*.string", "ok raw=99 n=1"),
                // A runtime receiver without such a member converts its value.
                new SpecProbe("Use(o) = o.string\nUse(12)", "ok raw='12' n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Only on a structural MISS is `.string` the number-to-text intrinsic, and the intrinsic takes the extension call's place: a lexical `string` is never consulted by `.string`. A receiver that declares no member named `string` — a number, a value, an algorithm without such a member — converts its numeric value (`3.string` is '3', `Obj.string` is '7'), while the written call `string(3)` uses the visible `string` callable. The fluent spread `A*.string` is that written call `string(A*)`.",
        },
        new()
        {
            Id = "grouped-structural-callee-is-the-member",
            Category = "access-boundaries",
            Source = "Box = {\n    public G(x) = x * 10\n}\nApply(f, v) = f(v)\n\nBox.G(2)\n(Box.G)(2)\nApply(Box.G, 2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "20\n20\n20",
            ExpectedRaw = "S[20, 20, 20]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                new SpecProbe("Lib = {\n    public F(0) = 0\n    public F(n) = n * 2\n}\n(Lib.F)(4)", "ok raw=8 n=1"),
                new SpecProbe("Inc(x) = x * 10\nObj = {\n    public M = Inc\n    7\n}\n(Obj.M)(5)", "ok raw=50 n=1"),
                new SpecProbe("Lib = {\n    public M(x) = {\n        public Q = 7\n        x\n    }\n}\n(Lib.M)(3)", "ok raw=3 n=1"),
                new SpecProbe("(Math.Abs)(-3)", "ok raw=3 n=1"),
                new SpecProbe("Math = {\n    public Abs(x) = 100\n}\n(Math.Abs)(-3)", "ok raw=100 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Parentheses never change callable identity. A dot expression carries ONE callable identity in every position that uses a callable, and an argumentless member reference is its member's own callable: supplied (`Apply(Box.G, 2)`) or called after grouping (`(Box.G)(2)`), it is the member `G` — with its own parameters, clauses, alias target and members — exactly as `Box.G(2)` calls it. The prelude's `Math` members are ordinary members too.",
        },
        new()
        {
            Id = "grouped-zero-arg-member-call-is-fresh",
            Category = "access-boundaries",
            Source = "Box = {\n    public V = 7\n}\n\nBox.V\nBox.V()\n(Box.V)()",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7\n7\n7",
            ExpectedRaw = "S[7, 7, 7]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                new SpecProbe("open Box\nBox = {\n    public V = 7\n}\nV, V(), (V)()", "ok raw=S[7, 7, 7] n=3"),
            ],
            Notes = "Freshness is observable only through effects, which this harness does not run: pinned by DotSemanticsDecisionTests (host operations and seeded draws on six routes) and CoreTests/DotIdentity.lean (binding contexts and cache entries).",
            Explanation = "`Box.V` is a property READ — evaluated once per run and cached — while `Box.V()` is an explicit CALL that evaluates the member afresh. Grouping does not change the call: `(Box.V)()` IS `Box.V()`, a fresh call that neither reads nor populates the cached value, exactly as `(V)()` is `V()`.",
        },
        new()
        {
            Id = "computed-dot-callee-is-not-callable",
            Category = "errors",
            Source = "Inc(x) = x + 1\n(5.Inc)()",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "notAnAlgorithm",
            Probes =
            [
                new SpecProbe("(5.string)()", "err notAnAlgorithm"),
                new SpecProbe("Other(o) = 7\nObj = {\n    public V = 1\n    5\n}\n(Obj.Other)()", "err notAnAlgorithm"),
                // The value itself is fine: only calling it fails.
                new SpecProbe("Inc(x) = x + 1\n5.Inc, Inc(5)", "ok raw=S[6, 6] n=2"),
            ],
            Explanation = "A dot expression whose receiver does not declare the member is a computed VALUE — the extension call's result (`5.Inc` is `Inc(5)`) or the `.string` intrinsic's text — and a computed value has no callable identity, so calling it is NotAnAlgorithm, never a hidden wrapper that re-evaluates the value.",
        },
        new()
        {
            Id = "call-after-argument-bearing-dot-edge-is-a-parse-error",
            Category = "parser-layout",
            Source = "X = {\n    public Mk(k) = k + 1\n}\n\nX.Mk(1)()",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "after a closed expression on the same line",
            ExpectedDiagnosticCode = DiagnosticCode.UnseparatedSameLineItem,
            IncludeInGeneratorPrompt = true,
            Notes = "Front-end rejection (SYN-09, Q-18 C-B3); Lean has no surface parser. A host-built call written after an argument-bearing dot edge reaches the runtime law as a computed callee: notAnAlgorithm (CoreTests/DotIdentity.lean).",
            Explanation = "A call may follow a callable reference — a name, a graced name, an argumentless member reference, or a redundant group of one — never an already computed call result. `X.Mk(1)` is a call, so `X.Mk(1)()` (like `X.G(1){ … }`) is the same-line-item error exactly as `Mk(1)()` is; `(X.Mk)(1)` is the member call.",
        },
        new()
        {
            Id = "closed-list-must-fallback-name-is-checked",
            Category = "access-boundaries",
            Source = "Get(obj) = 5.size\n\nGet(1)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "so `5.size` is the call `size(5)`",
            ExpectedDiagnosticCode = DiagnosticCode.UndeclaredIdentifier,
            IncludeInGeneratorPrompt = true,
            Notes = "Front-end rule (Q-75 F-A; FORMAL-02 leaves static validity to the C# front end). The checked set is exactly LexicalFallbackSelection.Always.",
            Explanation = "Under an explicit (closed) parameter list, a dot edge whose fallback is statically CERTAIN — a value receiver, or a known receiver that declares no such member — IS the call `size(5)`, so its name is checked exactly like the written callee name: `Get(obj) = 5.size` is the same UndeclaredIdentifier as `Get(obj) = size(5)`, reported at the member token whether or not `Get` is ever called.",
        },
        new()
        {
            Id = "closed-list-may-fallback-name-is-runtime",
            Category = "access-boundaries",
            Source = "Get(obj) = obj.size\nObj = {\n    public size = 11\n}\nsize(v) = 77\n\nGet(Obj)\nGet(3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "11\n77",
            ExpectedRaw = "S[11, 77]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                new SpecProbe("Get(obj) = obj.size\n7", "ok raw=7 n=1"),
            ],
            Explanation = "When only the runtime receiver decides — a parameter, an unresolved or ambiguous receiver — the fallback is merely POSSIBLE, so a closed parameter list does not require its name: `obj.size` reads the structural `size` of a receiver that declares one, and falls back to the lexical `size` only for a receiver that does not.",
        },
        new()
        {
            Id = "branch-must-fallback-name-is-checked",
            Category = "conditionals",
            Source = "F(0) = 0\nF(n) = (n + 1).G\n\nF(0)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "is the call `G(n + 1)`",
            ExpectedDiagnosticCode = DiagnosticCode.UndeclaredIdentifier,
            Probes =
            [
                new SpecProbe("F(0) = 0\nF(n) = n.G\nF(0)", "ok raw=0 n=1"),
            ],
            Notes = "Front-end rule (Q-75 F-A) shared with closed parameter lists; a load-bearing branch applies it when the branch is selected (MOD-10).",
            Explanation = "A clause-branch body obeys the closed parameter list's law: `(n + 1).G` certainly falls back, so it is the call `G(n + 1)` and `G` must be visible — reported at the member token even though `F(0)` never selects that branch. A binder receiver (`F(n) = n.G`) only MAY fall back and stays valid.",
        },
        // ==================== local-only members are local-context-dependent (K1-08) ====================
        new()
        {
            Id = "open-parameterized-provider-rejected",
            Category = "name-resolution",
            Source = "Lib(p) = {\n    public X = p + 101\n    X\n}\nA = {\n    open Lib\n    X\n}\nA",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "'Lib' cannot be opened because it requires arguments",
            ExpectedDiagnosticCode = DiagnosticCode.IllegalInOpen,
            IncludeInGeneratorPrompt = true,
            Notes = "Front-end rejection decided after signature completion (K1-08, September 2026); no elaborated Lean program exists for a rejected parse. Both evaluators refuse the same target at open resolution with `illegalInOpen` (Lean `resolveOpen`, C# `Evaluator.ResolveOpen`), and a clause family or an implicitly parameterized provider (`Lib = { public X = 1  p + 1 }`) is refused identically.",
            Explanation = "An `open` provider must need no call: `open` imports a namespace and never creates an activation, so an algorithm with parameters — explicit or inferred — has no members its inputs could be read from, and `open Lib` is refused at the open target rather than given an invented meaning (`X` is neither read through a phantom `p` nor turned into an implicit parameter). A parameterized head of a dotted target is different: `open Lib.Sub` with `Lib(p)` opens a self-contained `Sub` by identity navigation.",
        },
        new()
        {
            Id = "open-local-only-member-inside-owner",
            Category = "access-boundaries",
            Source = "Outer(n) = {\n    open Inner\n    Inner = {\n        public X = n\n    }\n    X + 0\n}\nOuter(5)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5",
            ExpectedRaw = "5",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // The same member through structural access, and from a sibling scope.
                new SpecProbe("Outer(n) = {\n    Inner = {\n        public X = n\n    }\n    Inner.X\n}\nOuter(5)", "ok raw=5 n=1"),
                new SpecProbe("Outer(n) = {\n    Left = {\n        public X = n\n    }\n    Right = {\n        open Left\n        X\n    }\n    Right\n}\nOuter(5)", "ok raw=5 n=1"),
                new SpecProbe("Outer(n) = {\n    Left = {\n        public X = n\n    }\n    Right = {\n        Left.X\n    }\n    Right\n}\nOuter(5)", "ok raw=5 n=1"),
                // A transitive capture (X reads Helper, which reads n) is the same case.
                new SpecProbe("Outer(n) = {\n    Helper = n + 1\n    Inner = {\n        public X = Helper\n    }\n    Inner.X\n}\nOuter(5)", "ok raw=6 n=1"),
                // A binder-capturing member inside its branch, through both channels.
                new SpecProbe("F(0) = 0\nF(n) = {\n    Lib = { public X = n }\n    G = {\n        open Lib\n        X\n    }\n    G + Lib.X\n}\nF(5)", "ok raw=10 n=1"),
                // Every activation reads its own binding: no run-wide reuse of a captured value.
                new SpecProbe("Outer(n) = {\n    Inner = {\n        public X = n\n    }\n    P = Inner.X\n    P\n}\nOuter(1), Outer(2)", "ok raw=S[1, 2] n=2"),
                // Capture payloads preserve owners, values, and activation identity across shadowing.
                new SpecProbe("Outer(n) = {\n Lib = { public X = 10\n n }\n P = { open Lib\n X }\n Q = Lib.X\n 0\n}\nOuter.P, Outer.Q", "ok raw=S[10, 10] n=2"),
                new SpecProbe("Outer(n) = {\n Inner = { public X = n }\n Read(n) = Inner.X\n Read(7)\n}\nOuter(5), Outer(9)", "ok raw=S[5, 9] n=2"),
                new SpecProbe("Outer(n) = {\n Inner = { public X = n }\n Read(n) = { open Inner\n X }\n Read(7)\n}\nOuter(5), Outer(9)", "ok raw=S[5, 9] n=2"),
                new SpecProbe("Outer(n) = {\n Q = n\n Mid(n) = { public X = Q\n X }\n Mid.X\n}\nOuter(5)", "ok raw=5 n=1"),
                new SpecProbe("Outer(n) = {\n Q = n\n Mid(n) = { public X = Q + n\n X }\n Mid(7)\n}\nOuter(5)", "ok raw=12 n=1"),
                new SpecProbe("Outer(n) = {\n Lib = { public X = n }\n Step(n) = Lib.X + n\n repeat(Step, 2, 0)\n}\nOuter(5), Outer(7)", "ok raw=S[10, 14] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A `public` member that captures an enclosing parameter is local-only, and local-only means local-context-dependent, not universally hidden: `Inner` is a zero-parameter provider whose `X` reads the active `Outer.n`, so inside `Outer` — the owner of that parameter — `open Inner` provides `X` and `Inner.X` reaches it, from Outer's own body and from any sibling or nested scope under the same activation. Both channels apply the ONE accessibility rule: a local-only member may be used from every lexical context inside the owner of each parameter it captures.",
        },
        new()
        {
            Id = "dot-local-only-member-outside-owner",
            Category = "access-boundaries",
            Source = "Outer(n) = {\n    Inner = {\n        public X = n\n    }\n    Inner.X\n}\nOuter.Inner.X",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "localOnlyProperty",
            Probes =
            [
                // The open channel refuses the same member from outside its owner (the open is
                // the body's preamble, so it precedes the clause definition it names).
                new SpecProbe("open Outer.Inner\nOuter(n) = {\n    public Inner = {\n        public X = n\n    }\n    Inner.X\n}\nX", "err localOnlyProperty"),
                // A live but unrelated binding of the same name never counts: the rule is lexical.
                new SpecProbe("Outer(n) = {\n    Inner = {\n        public X = n\n    }\n    G(7)\n}\nG(n) = Outer.Inner.X\nOuter(5)", "err localOnlyProperty"),
                new SpecProbe("Apply(f) = f.X\nOuter(n) = {\n    Inner = { public X = n }\n    Apply(Inner)\n}\nOuter(5)", "err localOnlyProperty"),
                // The owner is the NEAREST binder of the captured name: a site inside Outer but
                // outside Mid cannot read Mid's n through Outer's same-named parameter.
                new SpecProbe("Outer(n) = {\n    Mid(n) = {\n        Inner = {\n            public X = n\n        }\n        Inner.X\n    }\n    Mid.Inner.X\n}\nOuter(5)", "err localOnlyProperty"),
                // Inside the owner (the nested `Apply` is written inside Outer) the same access is valid.
                new SpecProbe("Outer(n) = {\n    Inner = { public X = n }\n    Apply(f) = f.X\n    Apply(Inner)\n}\nOuter(5)", "ok raw=5 n=1"),
                // Neither another activation nor another same-binder family supplies the owner.
                new SpecProbe("Outer(n) = {\n Mid(n) = { public X = n\n 0 }\n P = if(false, Mid.X, 10)\n Read = Outer.P\n Read\n}\nOuter(5)", "err localOnlyProperty"),
                new SpecProbe("Outer(m) = {\n Mid(n) = { public X = n\n 0 }\n P = if(false, Mid.X, 10)\n Read = Outer.P\n Read\n}\nOuter(5)", "err localOnlyProperty"),
                new SpecProbe("Outer(n) = {\n Mid(n) = { public X = n\n Read = Outer.Mid.X\n Read }\n Mid(7)\n}\nOuter(5)", "ok raw=7 n=1"),
                new SpecProbe("Outer(m) = {\n public Mid(n) = { public Lib = { public X = n }\n Read = { open Outer.Mid.Lib\n X }\n Read }\n Mid(7)\n}\nOuter(5)", "ok raw=7 n=1"),
                new SpecProbe("H(f, n) = if(n != 0, H({ public X = n }, 0), f.X)\nH({ public X = 0 }, 5)", "err localOnlyProperty"),
                new SpecProbe("Outer(f, k) = {\n Lib(n) = { public X = n\n f.X }\n if(k != 0, Outer(Lib, 0), Lib(7))\n}\nOuter({ public X = 0 }, 1)", "err localOnlyProperty"),
                new SpecProbe("H(f, k) = {\n F(0) = 0\n F(n) = H({ public X = n }, 0)\n G(0) = 0\n G(n) = f.X\n if(k != 0, F(k), G(7))\n}\nH({ public X = 0 }, 5)", "err localOnlyProperty"),
                new SpecProbe("Outer(n) = {\n Q = n\n Mid(n) = { public X = Q + n\n X }\n Mid.X\n}\nOuter(5)", "err localOnlyProperty"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Outside the owner of the captured parameter the same local-only member is selected and then refused: the root, an unrelated algorithm, and a callee written outside `Outer` are not inside `Outer`, so no activation of it is lexically available there — even when some same-named binding happens to be live (the rule is lexical ownership, never a dynamic lookup). Selection never depends on exposure, so the refusal is an accessibility error at the access, not a fallback or an invented meaning.",
        },
        new()
        {
            Id = "open-distinct-declarations-stay-distinct-providers",
            Category = "name-resolution",
            Source = $"open {new string('N', 520)}A, {new string('N', 520)}B\n{new string('N', 520)}A = {{ public X = 1 }}\n{new string('N', 520)}B = {{ public X = 1 }}\nX",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "is ambiguous: 2 different opened algorithms provide it at the same open level",
            ExpectedDiagnosticCode = DiagnosticCode.AmbiguousOpen,
            Probes =
            [
                new SpecProbe($"open {new string('N', 520)}A, {new string('N', 520)}A\n{new string('N', 520)}A = {{ public X = 1 }}\nX", "ok raw=1 n=1"),
            ],
            Notes = "Q-19 D-I (decided 2026-10-06) replaced the former `open-full-spelling-decides-provider-identity`, which taught that the written spelling identified a provider.",
            Explanation = "An `open` list counts the PROVIDERS its targets resolve to — each declaration once, in its declaring scope — never their spellings or their contents. Two declarations stay two providers even when their bodies are identical and their names abbreviate to the same diagnostic text, so a written `X` that both provide is ambiguous; one declaration written twice is one provider.",
        },
        new()
        {
            Id = "open-local-only-member-is-a-second-provider",
            Category = "name-resolution",
            Source = "Pub = {\n    public X = 101\n}\nOuter(p) = {\n    public Lib = {\n        public X = p + 202\n    }\n    0\n}\nA = {\n    open Pub, Outer.Lib\n    X\n}\nA",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "is ambiguous: 2 different opened algorithms provide it at the same open level",
            ExpectedDiagnosticCode = DiagnosticCode.AmbiguousOpen,
            Probes =
            [
                new SpecProbe("Pub = {\n    public X = 101\n}\nLib = {\n    X = 202\n}\nA = {\n    open Pub, Lib\n    X\n}\nA", "ok raw=101 n=1"),
                // The overlap itself is valid while nobody writes the name.
                new SpecProbe("Pub = {\n    public X = 101\n}\nOuter(p) = {\n    public Lib = {\n        public X = p + 202\n    }\n    0\n}\nA = {\n    open Pub, Outer.Lib\n    5\n}\nA", "ok raw=5 n=1"),
            ],
            Explanation = "`open` selects members by visibility alone: a public local-only member is provided by its open whatever its exposure and takes part in precedence and ambiguity like any provided name, so beside another provider of `X` it is a genuine second provider and a written `X` is ambiguous. Only a PRIVATE member is never provided. Whether the selected member may be used at the site is checked afterwards, which is what lets the front end select exactly what the evaluator selects before exposure is classified.",
        },
        new()
        {
            Id = "open-two-spellings-one-provider",
            Category = "name-resolution",
            Source = "Lib = {\n    public Sub = {\n        public X = 1\n    }\n    public R = {\n        open Sub, Lib.Sub\n        X\n    }\n}\nLib.R",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1",
            ExpectedRaw = "1",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("Lib = {\n    public Sub = {\n        public X = 1\n    }\n    public R = {\n        open Lib.Sub, Sub\n        X\n    }\n}\nLib.R", "ok raw=1 n=1"),
                new SpecProbe("open M, M\nM = {\n    public X = 1\n}\nX", "ok raw=1 n=1"),
                new SpecProbe("open M, (M)\nM = {\n    public X = 1\n}\nX", "ok raw=1 n=1"),
                new SpecProbe("open Lib.Sub, Lib.Sub\nLib = {\n    public Sub = {\n        public X = 1\n    }\n}\nX", "ok raw=1 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Q-19 D-I (decided 2026-10-06).",
            Explanation = "Opening the same provider twice still opens it once, however the paths are spelled: inside `Lib.R`, `Sub` and `Lib.Sub` name the one declaration `Sub`, so `X` has one provider in either order, exactly like `open M, M` and `open M, (M)`. Provider identity is the declaration in its declaring scope, never the written text or its position in the list.",
        },
        new()
        {
            Id = "open-identical-inline-blocks-two-providers",
            Category = "name-resolution",
            Source = "open { public X = 1 }, { public X = 1 }\nX",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "is ambiguous: 2 different opened algorithms provide it at the same open level",
            ExpectedDiagnosticCode = DiagnosticCode.AmbiguousOpen,
            Probes =
            [
                new SpecProbe("open { public X = 1 }, { public X = 1 }\n5", "ok raw=5 n=1"),
                new SpecProbe("open { public X = 1 }, { public Y = 1 }\nX", "ok raw=1 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Q-19 D-I with Q-29 A-U (decided 2026-10-06).",
            Explanation = "Two written blocks are two declarations, so they are two providers even when their text and members are identical: providers are never merged by their contents or their values. A written `X` that both provide is ambiguous, while the overlap alone, with no written `X`, is valid.",
        },
        new()
        {
            Id = "ambiguous-open-written-use-is-static",
            Category = "name-resolution",
            Source = "open A, B\nA = {\n    public X = 1\n}\nB = {\n    public X = 2\n}\nY = X\n5",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "'X' is ambiguous: 2 different opened algorithms provide it at the same open level (A, B)",
            ExpectedDiagnosticCode = DiagnosticCode.AmbiguousOpen,
            Probes =
            [
                new SpecProbe("open A, B\nA = {\n    public X = 1\n}\nB = {\n    public X = 2\n}\nA.X + B.X", "ok raw=3 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Q-29 A-U (decided 2026-10-06): before, a written ambiguous name was accepted until evaluation demanded it.",
            Explanation = "A written name is resolved statically, whether or not evaluation ever demands it: `Y` is never read, yet its `X` reaches an open level where two different providers supply `X`, so it names no declaration and the program is rejected at that `X`. Demand decides what is computed, never what a written name means. Qualify the name (`A.X`) or open only one of the providers.",
        },
        new()
        {
            Id = "ambiguous-open-unused-overlap-is-valid",
            Category = "name-resolution",
            Source = "open A, B\nA = {\n    public X = 1\n    public P = 10\n}\nB = {\n    public X = 2\n    public Q = 20\n}\nP + Q",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "30",
            ExpectedRaw = "30",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // Lexical precedence decides first: an owned X, or a nearer level that provides X once.
                new SpecProbe("open A, B\nA = {\n    public X = 1\n}\nB = {\n    public X = 2\n}\nX = 9\nX", "ok raw=9 n=1"),
                new SpecProbe("open A, B\nA = {\n    public X = 1\n}\nB = {\n    public X = 2\n}\nC = {\n    open D\n    D = {\n        public X = 3\n    }\n    X\n}\nC", "ok raw=3 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Q-29 A-U (decided 2026-10-06).",
            Explanation = "Different opened algorithms may contain the same name: the overlap itself is valid, so adding an unused member to one library never breaks a program that opens it beside another. Only a written reference that resolves to two providers at the same open level is rejected, and lexical precedence decides first — an owned `X`, or a nearer open level that provides `X` once, is selected without ambiguity.",
        },
        new()
        {
            Id = "dot-chain-structural-member-beats-extension",
            Category = "access-boundaries",
            Source = "Lib = {\n    public Sub = {\n        public Q = 1\n    }\n}\n\nQ(x) = 99\n\nLib.Sub.Q",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1",
            ExpectedRaw = "1",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("Lib = {\n    Sub = {\n        public Q = 1\n    }\n}\nQ(x) = 99\nLib.Sub.Q", "ok raw=1 n=1"),
                new SpecProbe("Lib = {\n    public Sub = {\n        public Q = 1\n    }\n}\nK(Q) = Lib.Sub.Q\nK({x + 1})", "ok raw=1 n=1"),
                new SpecProbe("Lib = {\n    public Sub = {\n        public Q(y) = y + 1\n    }\n}\nQ(x) = 99\nLib.Sub.Q(5)", "ok raw=6 n=1"),
                new SpecProbe("Lib = {\n    public Sub = {\n        public Q = 1\n    }\n}\nOuter = {\n    Q(x) = 99\n    Lib.Sub.Q\n}\nOuter", "ok raw=1 n=1"),
                new SpecProbe("Lib(p) = {\n public Mid(q) = {\n public Sub = { public X = 10 }\n q\n }\n p\n}\nLib.Mid.Sub.X", "ok raw=10 n=1"),
                new SpecProbe("open Lib.Mid.Sub\nLib(p) = {\n public Mid = {\n public Sub = { public X = 10 }\n q\n }\n p\n}\nX", "ok raw=10 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Dot syntax is property-first at EVERY level of a chain: the receiver `Lib.Sub` is navigated to `Sub`'s algorithm, and because `Sub` exposes an accessible `Q`, that member is read before the visible extension `Q(x)` is ever considered — exactly as `Lib.Q` reads `Lib`'s own `Q`. Only a receiver without the member falls back to the extension call `Q(receiver)`; a same-named extension, whether declared at the root, in the enclosing algorithm, or as a parameter of it, never pre-empts a structural member.",
        },
        new()
        {
            Id = "dot-chain-extension-fallback-composes",
            Category = "access-boundaries",
            Source = "A = x + 7\nB = x * 5\n\n3.A.B\nB(A(3))\nB(3.A)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "50\n50\n50",
            ExpectedRaw = "S[50, 50, 50]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                new SpecProbe("Q(x) = x * 10\n[1, 2, 3].count.Q", "ok raw=30 n=1"),
                new SpecProbe("Q(x) = x + 1\n3.Q", "ok raw=4 n=1"),
                new SpecProbe("Lib = {\n    public Sub = {\n        5\n    }\n}\nF(a, b) = a * 100 + b\nLib.Sub.F(2)", "ok raw=502 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "When a receiver has no such member, the dot edge falls back to the extension call with the receiver as the leading argument, and the fallbacks compose along a chain: the number `3` has no structural `A`, so `3.A` is `A(3)`; that result has no `B`, so `3.A.B` is `B(A(3))`, the same as `B(3.A)`. The free-call/dot-call law `receiver.F(a, b) = F(receiver, a, b)` is untouched wherever structural lookup does not apply.",
        },
        new()
        {
            Id = "dot-chain-nested-structural-members",
            Category = "access-boundaries",
            Source = "A = {\n    public B = {\n        public C = {\n            public D = 7\n        }\n    }\n}\nD(x) = 93\n\nA.B.C.D",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7",
            ExpectedRaw = "7",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("G(x) = {\n    public Sub = {\n        public Q = 1\n    }\n    x\n}\nQ(v) = 99\nG.Sub.Q", "ok raw=1 n=1"),
                new SpecProbe("Lib = {\n    public Sub = {\n        public Q = 1\n        5\n    }\n}\nQ(x) = x * 10\nLib.Sub().Q", "ok raw=50 n=1"),
                new SpecProbe("Lib = {\n    public Sub = {\n        public Q = 1\n        5\n    }\n}\nQ(x) = x * 10\n(Lib.Sub).Q", "ok raw=1 n=1"),
                new SpecProbe("Lib = {\n    public Sub = {\n        7\n    }\n}\nLib.Sub.string", "ok raw='7' n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A chain of argumentless dot edges navigates accessible structural members at every level without evaluating the intermediate containers, so a container that has no output, or declares parameters, still exposes its members through the chain. A written call such as `Lib.Sub()` is a VALUE, so a member after it is resolved by extension fallback on that value; parentheses around a single dot expression are ordinary redundant grouping, so `(Lib.Sub).Q` is `Lib.Sub.Q`.",
        },
        new()
        {
            Id = "dot-chain-local-only-member-is-not-a-fallback",
            Category = "access-boundaries",
            Source = "G(x) = {\n    public Sub = {\n        public Q = 1\n        x\n    }\n    0\n}\nQ(v) = 99\n\nG.Sub.Q",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "localOnlyProperty",
            Probes =
            [
                new SpecProbe("G(x) = {\n    public Sub = {\n        public Q = 1\n        x\n    }\n    0\n}\nG.Sub", "err localOnlyProperty"),
                new SpecProbe("C(0) = {\n    public Q = {\n        public R = 1\n    }\n    0\n}\nC(1) = 2\nR(v) = 99\nC.Q.R", "err localOnlyProperty"),
            ],
            Explanation = "Accessibility is the established one-level rule applied at every level: `Sub` is declared but local-only (its value reads the enclosing parameter `x`), so `G.Sub.Q` reports that structural error at `Sub` — never a fallback to the visible extension `Q(v)` — exactly as `G.Sub` itself reports it, and a member defined only inside conditional branches fails the same way. Private members remain reachable: structural access ignores `public`, not exposure.",
        },
        new()
        {
            Id = "open-capture-target-rejected",
            Category = "access-boundaries",
            Source = "M = {\n    public C = 5\n}\nR = {\n    open (M, M)\n    C\n}\nR",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "a parenthesized group is a captured value, not an algorithm",
            ExpectedDiagnosticCode = DiagnosticCode.BadOpenForm,
            Probes =
            [
                new SpecProbe("M = {\n    public C = 5\n}\nR = {\n    open M\n    C\n}\nR", "ok raw=5 n=1"),
                new SpecProbe("M = {\n    public C = 5\n}\nR = {\n    open (M)\n    C\n}\nR", "ok raw=5 n=1"),
                new SpecProbe("M = {\n    public C = 5\n}\nR = {\n    open ((M))\n    C\n}\nR", "ok raw=5 n=1"),
                new SpecProbe("R = {\n    open ({public C = 6})\n    C\n}\nR", "ok raw=6 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`open` consumes algorithm identity, and a capture is a value boundary that never exposes the identity of what it encloses: `open (M, M)` — a group of several slots — is rejected at parse time, as is `open (M*)`. Redundant parentheses are not a capture: parentheses group syntax, so `open (M)` and `open ((M))` are exactly `open M`, and parentheses around a brace block normalize away too, so `open ({ ... })` still opens the block.",
        },
        new()
        {
            Id = "open-target-head-must-name-an-algorithm",
            Category = "access-boundaries",
            Source = "open F(1).Y\nF(x) = {\n    public Y = x\n}\nY",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Invalid open form: 'call' is not allowed in open declarations.",
            ExpectedDiagnosticCode = DiagnosticCode.BadOpenForm,
            Probes =
            [
                // Every legal head, under dotted steps: a name and a `{ ... }` block.
                new SpecProbe("open Lib.S\nLib = {\n    public S = {\n        public Q = 3\n    }\n}\nQ", "ok raw=3 n=1"),
                new SpecProbe("open { public S = { public Q = 3 } }.S\nQ", "ok raw=3 n=1"),
                new SpecProbe("open { public S = { public T = { public Q = 4 } } }.S.T\nQ", "ok raw=4 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Constitution PV-11 (September 2026): the parser checked only the OUTER node of a target, so `open 5.N` or `open F(1).N` passed the front end; the evaluators refuse such a head only when some lookup consults the level (Lean `resolveAlgForOpen` recurses through the receiver), so a program failed after its effects had run, or not at all. Every static consumer now reads the one decomposition `AstHelpers.OpenTargetHead`.",
            Explanation = "An open target names an algorithm all the way down: the first part of a dotted path must itself be a name, a `{ ... }` block, or a `load` module, exactly like a bare target. `open F(1).Y`, `open 5.N`, `open (A, B).N` and `open [A].N` are rejected at that first part like `open F(1)`, `open 5`, `open (A, B)` and `open [A]`, whether or not any name is ever looked up through them. `open` never calls or evaluates anything, so open a path that starts at a declared algorithm (`open Lib.S`) or at an inline block.",
        },
        new()
        {
            Id = "inline-headed-open-paths-keep-distinct-providers",
            Category = "name-resolution",
            Source = "open { public S = { public X = 5 } }.S, { public S = { public X = 7 } }.S\nX",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "is ambiguous: 2 different opened algorithms provide it at the same open level",
            ExpectedDiagnosticCode = DiagnosticCode.AmbiguousOpen,
            Probes =
            [
                new SpecProbe("open { public S = { public X = 7 } }.S, { public S = { public X = 5 } }.S\n5", "ok raw=5 n=1"),
                new SpecProbe("open { public S = { public Y = 5 } }.S, { public S = { public X = 7 } }.S\nX", "ok raw=7 n=1"),
                new SpecProbe("open { public S = { X = 5 } }.S, { public S = { public X = 7 } }.S\nX", "ok raw=7 n=1"),
                new SpecProbe("open Lib.S, (Lib).S\nLib = { public S = { public X = 7 } }\nX", "ok raw=7 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Each written block is its own declaration, so a dotted path starting at a brace block is a separate provider from a path starting at another block, even when both paths have the same member names: a written `X` that both provide is ambiguous, while the overlap alone is valid. A diagnostic abbreviation such as `{...}.S` never identifies a provider, and two spellings of one name-headed path such as `open Lib.S, (Lib).S` are one provider.",
        },
        new()
        {
            Id = "open-inline-headed-path-must-resolve",
            Category = "name-resolution",
            Source = "A = {\n    open { public X = 1 }.Nope\n    X\n}\nA(5)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "'{...}.Nope' cannot be opened because '{...}' has no property named 'Nope'.",
            ExpectedDiagnosticCode = DiagnosticCode.UnresolvedOpenTarget,
            Probes =
            [
                new SpecProbe("A = {\n    open { public S = { public X = 1 } }.S\n    X\n}\nA", "ok raw=1 n=1"),
            ],
            Notes = "Constitution PV-11 (September 2026): the static resolution described failures of name-headed paths only, so a path starting at a `{ ... }` block or a loaded module with a missing, private, or branch-only step was dropped silently and the names only it could provide were promoted to implicit parameters — here `X` became `A`'s parameter and `A(5)` ran as 5, and `open load('url').Shwn` did the same while `Lib = load('url')` / `open Lib.Shwn` was refused.",
            Explanation = "Every written open target must resolve, whatever its first part: the dotted steps of a path that starts at a `{ ... }` block or a loaded module select public members exactly as they do after a name, so a missing, private, or branch-only step is an unresolved open target. It is never dropped, and the names it would have provided are never turned into implicit parameters.",
        },
        new()
        {
            Id = "open-after-clause-definition-rejected",
            Category = "parser-layout",
            Source = "P(a) = a\nopen Lib\nLib = {\n    public X = 4\n}\nP(X)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "'open' declaration must appear before any properties or output expressions.",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidOpenDeclaration,
            Probes =
            [
                new SpecProbe("open Lib\nP(a) = a\nLib = {\n    public X = 4\n}\nP(X)", "ok raw=4 n=1"),
                new SpecProbe("open Lib\nP(0) = 0\nP(n) = n + X\nLib = {\n    public X = 4\n}\nP(1)", "ok raw=5 n=1"),
                // A clause body is a body of its own, with its own preamble.
                new SpecProbe("P(0) = {\n    open Lib\n    X\n}\nP(n) = n\nLib = {\n    public X = 4\n}\nP(0)", "ok raw=4 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Constitution PV-25 (September 2026): clause definitions are buffered in their families until the body ends, and the placement check counted only properties and output rows, so an `open` after `P(a) = a` — or between two clauses of one family — was accepted while an `open` after `P = a` was refused.",
            Explanation = "A body's one `open` declaration is its import preamble: it comes before every declaration and output row of that body, clause definitions included — `P(a) = a` declares a property exactly as `P = a` does. Move the `open` to the top of the body; each nested `{ ... }` body, a clause body included, has its own preamble.",
        },
        new()
        {
            Id = "capture-suppresses-higher-order-identity",
            Category = "access-boundaries",
            Source = "Apply = f(9)\nIncrement(x) = x + 1\nProbe(u) = Apply((Increment, Increment))\nProbe(0)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "notAnAlgorithm",
            Probes =
            [
                new SpecProbe("Apply = f(9)\nIncrement(x) = x + 1\nApply(Increment)", "ok raw=10 n=1"),
                new SpecProbe("Apply = f(9)\nIncrement(x) = x + 1\nApply((Increment))", "ok raw=10 n=1"),
                new SpecProbe("Apply = f(9)\nIncrement(x) = x + 1\nApply(((Increment)))", "ok raw=10 n=1"),
                new SpecProbe("Apply = f(9)\nIncrement(x) = x + 1\nProbe(u) = Apply((Increment*))\nProbe(0)", "err notAnAlgorithm"),
                // A capture's elements are value positions: a formula that infers its parameters lifts them.
                new SpecProbe("Id(v) = v\nIncrement(x) = x + 1\nG = Id((Increment, Increment))\nG(4)", "ok raw=S[5, 5] n=1"),
            ],
            Explanation = "A capture such as `(Increment, Increment)` or `(Increment*)` supplies a suspended value cell with no callable identity. Calling the parameter fails as not an algorithm without evaluating the capture's contents. A value consumer instead demands the capture; its elements are formula value positions and may lift in an inferring body. Redundant parentheses disappear, so `(Increment)` and `((Increment))` retain Increment's callable identity.",
        },
        new()
        {
            Id = "capture-suppresses-structural-members",
            Category = "access-boundaries",
            Source = "V(x) = 99\nObj = {\n    public V = 7\n    0\n}\n\nObj.V\n(Obj).V\n(Obj*).V",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7\n7\n99",
            ExpectedRaw = "S[7, 7, 99]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                new SpecProbe("F2(x, y) = x + y\nX = 3\n(X).F2(4)", "ok raw=7 n=1"),
                new SpecProbe("Obj = {public V = 7}\nQ(z) = (Obj).V\nQ(0)", "ok raw=7 n=1"),
                new SpecProbe("Obj = {public V = 7\n0}\nV(x) = 99\nQ(z) = (Obj*).V\nQ(0)", "ok raw=99 n=1"),
            ],
            Explanation = "Parentheses group syntax: `(Obj).V` IS `Obj.V`, so both read Obj's own property. A genuine capture receiver — a lone spread `(Obj*)` or a group of several slots — has no structural members, so `(Obj*).V` falls back lexically and injects the captured value as the leading argument. That fallback is statically certain, so its name must be visible: inside a closed parameter list an undeclared one is the front-end UndeclaredIdentifier (`closed-list-must-fallback-name-is-checked`), and in an implicitly parameterized body the member becomes an inferred parameter instead.",
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
            Id = "dot-call-structural-member-is-not-a-lexical-rewrite",
            Category = "access-boundaries",
            Source = "B(a, c) = a * 100 + c\nObj = {\n    public B(c) = c + 1\n}\n\nObj.B(5)\n3.B(5)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "6\n305",
            ExpectedRaw = "S[6, 305]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // Structural selection ignores `public`: a private member is still the receiver's own.
                new SpecProbe("B(a, c) = a * 100 + c\nObj = {\n    B(c) = c + 1\n}\nObj.B(5)", "ok raw=6 n=1"),
                // A receiver without the member takes the fallback, injecting its VALUE as the leading argument.
                new SpecProbe("B(a, c) = a * 100 + c\nObj = {\n    public Q = 1\n    3\n}\nObj.B(5)", "ok raw=305 n=1"),
                // The fallback allocates like B(A, C): the receiver is one ordinary argument, never spread across fixed parameters.
                new SpecProbe("B(a, c) = a * 100 + c\n(3, 4).B(5)", "err type"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Dot syntax is property-first. `Obj` declares its own `B`, so `Obj.B(5)` calls that member with the one argument `5` and injects no receiver; the visible two-parameter `B(a, c)` is never considered, although `B(Obj, 5)` is a well-formed two-argument call. Only a receiver WITHOUT the member takes the lexical fallback, where `A.B(C)` allocates arguments like `B(A, C)` with the receiver as one ordinary leading argument — `3.B(5)` is `B(3, 5)`.",
        },
        new()
        {
            Id = "visibility-private-member-is-structural-not-exported",
            Category = "access-boundaries",
            Source = "Lib = {\n    public Area = 4\n    Helper = Area / 2\n}\n\nLib.Area\nLib.Helper",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "4\n2",
            ExpectedRaw = "S[4, 2]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // `open` provides only public members: Area arrives, Helper does not (it would be a root parameter).
                new SpecProbe("open Lib\nLib = {\n    public Area = 4\n    Helper = Area / 2\n}\n\nArea", "ok raw=4 n=1"),
                new SpecProbe("open Lib\nLib = {\n    public Area = 4\n    Helper = Area / 2\n}\n\nHelper", "err unresolvedImplicitParams"),
                // Opening the library does not take structural access away.
                new SpecProbe("open Lib\nLib = {\n    public Area = 4\n    Helper = Area / 2\n}\n\nLib.Helper", "ok raw=2 n=1"),
                // Structural access reaches a capturing member by declaration and then refuses it
                // here: the root is not inside `Lib`, the owner of the `r` that `Area` captures.
                // (A parameterized algorithm cannot be opened at all; that front-end rejection is
                // the `open-parameterized-provider-rejected` case.)
                new SpecProbe("Lib(r) = {\n    public Area = r * r\n    Area\n}\n\nLib.Area", "err localOnlyProperty"),
                // Inside the owner the same capturing member is provided and reachable.
                new SpecProbe("Outer(r) = {\n    open Lib\n    Lib = {\n        public Area = r * r\n    }\n    Area\n}\n\nOuter(3)", "ok raw=9 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Private means not provided by `open`, not unreachable: `open` (an opened module included) brings only `public` members into scope, while structural dot access ignores `public`, so `Lib.Helper` reaches the private, self-contained `Helper`. Exposure never removes a member from selection: a `public` member that depends on an enclosing parameter is selected as usual and then refused at any access written outside the owner of that parameter. A parameterized algorithm is refused as an `open` target outright, because `open` imports a namespace and never creates the activation its members would read.",
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
                new SpecProbe("take((1, 2, 3), 2) == (1, 2)", "ok raw=false n=1"),
                new SpecProbe("take((1, 2, 3), 2) == [1, 2]", "ok raw=true n=1"),
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
            Explanation = "`take` keeps the first `count` items and materializes them as one list value.",
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
                new SpecProbe("take(((1, 2), (3, 4)), 1) == (1, 2)", "ok raw=false n=1"),
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
            Explanation = "`filter` requires one Boolean predicate result and keeps items for which it is `true`, returning one exact list value.",
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
            Source = "No(a) = false\nfilter((1, 2, 3), No)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[]",
            ExpectedRaw = "L[]",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("No(a) = false\nfilter((1, 2, 3), No) == ()", "ok raw=false n=1"),
                new SpecProbe("No(a) = false\nfilter((1, 2, 3), No) == []", "ok raw=true n=1"),
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
            Source = "Swap((a, b)) = (b, a)\nmap(((1, 2), (3, 4)), Swap)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[(2, 1), (4, 3)]",
            ExpectedRaw = "L[S[2, 1], S[4, 3]]",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("Swap(a, b) = (b, a)\nmap(((1, 2), (3, 4)), Swap)", "err arity"),
                new SpecProbe("Swap((a, b)) = (b, a)\nmap([[1, 2]], Swap)", "err type"),
                new SpecProbe("LSwap([a, b]) = [b, a]\nmap([[1, 2]], LSwap)", "ok raw=L[L[2, 1]] n=1"),
            ],
            Explanation = "Each callback item is one selected value, passed to the callback as ONE ordinary argument — exactly as the direct call `Swap(item)`. A pair-shaped callback therefore opens the row with an explicit structural pattern of the row's kind — `Swap((a, b))` for a sequence row, `LSwap([a, b])` for a list row; the flat two-parameter `Swap(a, b)` is the ordinary arity error for a one-argument call. Each callback must return exactly one value, preserved as one exact list element.",
        },
        new()
        {
            Id = "clause-family-multirow-callback-rejected",
            Category = "collection-builtins",
            Source = "F(0) = 1, 2\nF(n) = n, n\nmap([0, 3], F)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // A lone literal clause is a one-branch family: the same contract.
                new SpecProbe("F(0) = 1, 2\nmap([0], F)", "err arity"),
                // Every route to the family is the family: an alias, a forwarded parameter, a dot call.
                new SpecProbe("F(0) = 1, 2\nF(n) = n, n\nG = F\nmap([3], G)", "err arity"),
                new SpecProbe("F(0) = 1, 2\nF(n) = n, n\nApply(f, xs) = map(xs, f)\nApply(F, [0])", "err arity"),
                new SpecProbe("F(0) = 1, 2\nF(n) = n, n\n[0, 3].map(F)", "err arity"),
                // The ordinary call is one value, and so is the η-block that makes it.
                new SpecProbe("F(0) = 1, 2\nF(n) = n, n\nF(0)", "ok raw=S[1, 2] n=1"),
                new SpecProbe("F(0) = 1, 2\nF(n) = n, n\nmap([0, 3], { F(x) })", "ok raw=L[S[1, 2], S[3, 3]] n=1"),
                // `filter` reads its predicate's value: two rows are one sequence, not a Boolean.
                new SpecProbe("P(0) = true, true\nP(n) = false, false\nfilter([0, 3], P)", "err type"),
            ],
            Explanation = "A clause family is an ordinary callable, so as a `map` transform it is judged like every callback: the selected clause must EMIT exactly one value, and `1, 2` emits two rows — the map contract's arity error, exactly as for `D(x) = x, x`. The same family's ordinary call `F(0)` is the one value `(1, 2)`; write `F(0) = (1, 2)`, or the η-block `{ F(x) }`, to map to pairs.",
        },
        new()
        {
            Id = "clause-family-multirow-reduce-step-rejected",
            Category = "collection-builtins",
            Source = "R(e, 0) = e, 0\nR(e, acc) = e, acc\nreduce([1], R, 0)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                new SpecProbe("R(e, 0) = e, 0\nreduce([1], R, 0)", "err arity"),
                new SpecProbe("R(e, 0) = e, 0\nR(e, acc) = e, acc\n[1].reduce(R, 0)", "err arity"),
                new SpecProbe("R(e, 0) = e, 0\nR(e, acc) = e, acc\nR(1, 0)", "ok raw=S[1, 0] n=1"),
                new SpecProbe("R(e, 0) = (e, 0)\nR(e, acc) = (e, acc)\nreduce([1], R, 0)", "ok raw=S[1, 0] n=1"),
                new SpecProbe("R(e, 0) = e, 0\nR(e, acc) = e, acc\nreduce([], R, 7)", "ok raw=7 n=1"),
            ],
            Explanation = "A `reduce` step must emit exactly one accumulator value. A family step is judged by its selected clause's own rows, so `e, 0` is the reduce contract's arity error, while the ordinary call `R(1, 0)` is the one value `(1, 0)` and `R(e, 0) = (e, 0)` is a valid step.",
        },
        new()
        {
            Id = "clause-family-callback-single-value-accepted",
            Category = "collection-builtins",
            Source = "F(0) = 1, 2\nP(0) = (1, 2)\nP(n) = (n, n)\nL(0) = []\nL(n) = [n]\nmap([0, 3], P), map([0, 3], L), F(0) == P(0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[(1, 2), (3, 3)]\n[[], [3]]\ntrue",
            ExpectedRaw = "S[L[S[1, 2], S[3, 3]], L[L[], L[3]], true]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                new SpecProbe("P(0) = (1, 2)\nmap([0], P)", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("D(x) = x, x\nF(0) = D(0)\nF(n) = D(n)\nmap([0, 3], F)", "ok raw=L[S[0, 0], S[3, 3]] n=1"),
                new SpecProbe("IsZero(0) = true\nIsZero(n) = false\nfilter([0, 1, 0], IsZero)", "ok raw=L[0, 0] n=1"),
                // A loop step is no callback: the selected clause's two rows are the next state.
                new SpecProbe("S(0) = 1, 2\nS(n) = n, n\nrepeat(S, 1, 0)", "ok raw=S[1, 2] n=1"),
            ],
            Explanation = "A callback result is judged by its EMITTED rows, not by its elements: a family clause that emits ONE value — a sequence `(1, 2)`, a list, `[]`, or an inner call's one value — is one mapped element, and an ordinary family call is one value too (`F(0) == P(0)`); only a callback whose selected clause writes several rows is rejected. A loop step is no callback: its rows are the next state.",
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
                new SpecProbe("Collect(*items) = items\n[((1, 2), 3)].map(Collect)", "ok raw=L[L[S[S[1, 2], 3]]] n=1"),
                new SpecProbe("Collect(*items) = items\nmap((7, 8), Collect)", "ok raw=L[L[7], L[8]] n=1"),
                new SpecProbe("IsSingleSeven(*items) = items == [7]\n[7, 8].filter(IsSingleSeven)", "ok raw=L[7] n=1"),
                new SpecProbe("IsPair(*items) = items.count == 2\n((1, 2), 3, (4, 5), [6, 7]).filter(IsPair).count", "ok raw=0 n=1"),
                new SpecProbe("IsPair(x) = x.count == 2\n((1, 2), 3, (4, 5), [6, 7]).filter(IsPair).count", "ok raw=3 n=1"),
                new SpecProbe("R(*items, acc) = items == [10]\nreduce([10], R, 99)", "ok raw=true n=1"),
                new SpecProbe("R(*items, acc) = items\nreduce([(1, 2)], R, 99)", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("R(*items, acc) = items\nreduce([()], R, 99)", "ok raw=L[S[]] n=1"),
                new SpecProbe("R(*items, acc) = items\nreduce([[1, 2]], R, 99)", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("R(*items, acc) = items\nreduce([((1, 2), 3)], R, 99)", "ok raw=L[S[S[1, 2], 3]] n=1"),
                new SpecProbe("R(*items) = items\nreduce([10], R, 99)", "ok raw=L[10, 99] n=1"),
                new SpecProbe("Acc(x, *acc) = acc\nreduce([9], Acc, ((1, 2), 3))", "ok raw=L[S[S[1, 2], 3]] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A callback receives each iterated element as ONE ordinary argument, bound exactly as the direct call with that element, so a single-collecting map/filter callback collects it as one item whatever it is — a scalar, a sequence, a list, `()` (`[(1, 2)].map(Collect)` binds `items = [(1, 2)]`, `[()].map(Collect)` binds `[()]`), and a collecting filter predicate counts one argument per element (`IsPair(*items)` keeps nothing, while the fixed `IsPair(x) = x.count == 2` inspects each element's contents). Reducers are ordinary two-argument callbacks: a genuine single-collecting reducer collects `[element, accumulator]`, an element-side collector before a fixed accumulator collects `[element]`, and an accumulator-side collector collects the ONE accumulator value (`((1, 2), 3)` becomes `[((1, 2), 3)]`).",
        },
        new()
        {
            Id = "callback-mixed-variadic-rows",
            Category = "collection-builtins",
            Source = "F((first, *middle, last)) = middle\nRows = [(1, 2, 3, 4)]\n\nRows.map(F)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[[2, 3]]",
            ExpectedRaw = "L[L[2, 3]]",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("F(first, *middle, last) = middle\nRows = [(1, 2, 3, 4)]\nRows.map(F)", "err arity"),
                new SpecProbe("F((first, *middle, last)) = middle\nRows = [[1, 2, 3, 4]]\nRows.map(F)", "err type"),
                new SpecProbe("F([first, *middle, last]) = middle\nRows = [[1, 2, 3, 4]]\nRows.map(F)", "ok raw=L[L[2, 3]] n=1"),
                new SpecProbe("F(first, *rest) = rest\n[(1, 2, 3)].map(F)", "ok raw=L[L[]] n=1"),
                new SpecProbe("F((first, *rest)) = rest\n[(1, 2, 3)].map(F)", "ok raw=L[L[2, 3]] n=1"),
                new SpecProbe("F(first, *rest) = rest\n[7].map(F)", "ok raw=L[L[]] n=1"),
                new SpecProbe("F(*init, last) = init\n[(1, 2, 3)].map(F)", "ok raw=L[L[]] n=1"),
            ],
            Explanation = "A callback element is ONE ordinary argument (there is no callback row convention), so a row is opened by the callee's explicit structural pattern of the row's kind: `F((first, *middle, last))` opens each sequence row (and `F([first, *middle, last])` each list row) and COLLECTS the middle as an exact list. The flat `F(first, *middle, last)` receives one argument against two fixed positions and is the ordinary arity error, exactly like `F((1, 2, 3, 4))`; a flat prefix or suffix binds the whole element and leaves the collector empty.",
        },
        new()
        {
            Id = "callback-nested-pattern-binds-like-call",
            Category = "collection-builtins",
            Source = "Head((x, *rest)) = [x, rest]\n\nHead((7, 8))\n[(7, 8)].map(Head)\nmap([(7, 8), (9, 10, 11)], Head)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[7, [8]]\n[[7, [8]]]\n[[7, [8]], [9, [10, 11]]]",
            ExpectedRaw = "S[L[7, L[8]], L[L[7, L[8]]], L[L[7, L[8]], L[9, L[10, 11]]]]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // A scalar is no one-item structure: it is the pattern's kind mismatch, in the
                // direct call and the callback alike; the right kind of the wrong length is the
                // pattern's arity mismatch.
                new SpecProbe("Head((x, *rest)) = [x, rest]\nHead(7)", "err type"),
                new SpecProbe("Head((x, *rest)) = [x, rest]\n[7].map(Head)", "err type"),
                new SpecProbe("Pair((x, y)) = [x, y]\n[(1, 2, 3)].map(Pair)", "err arity"),
                // Each pattern opens its own kind one level, exactly as in the direct call.
                new SpecProbe("LHead([x, *rest]) = [x, rest]\n[[7], [8, 9]].map(LHead)", "ok raw=L[L[7, L[]], L[8, L[9]]] n=1"),
                new SpecProbe("Last((*init, z)) = z\n[(true, 1), (1, 2)].map(Last)", "ok raw=L[1, 2] n=1"),
                // filter and reduce bind their values through the same rules.
                new SpecProbe("Big((x, *rest)) = x > 1\n[(7, 0), (1, 0)].filter(Big)", "ok raw=L[S[7, 0]] n=1"),
                new SpecProbe("R((x, *rest), acc) = acc + x\nreduce([(7, 0), (8, 0)], R, 0)", "ok raw=15 n=1"),
                // The operation decides the invocations: an empty collection runs nothing, while
                // an empty element is one invocation with the value `()`.
                new SpecProbe("Head((x, *rest)) = [x, rest]\n[].map(Head)", "ok raw=L[] n=1"),
                new SpecProbe("Head((x, *rest)) = [x, rest]\n[()].map(Head)", "err arity"),
            ],
            Explanation = "A callback binds each value it supplies exactly as the ordinary call supplying that one value does: a nested sequence pattern opens a sequence element one level and a list pattern a list element, while any other value — a scalar, or the other kind — is the pattern's kind mismatch in the direct call and the callback alike (`Head(7)` and `[7].map(Head)`). The callback operation still decides how many values it supplies (one element for map and filter, element and accumulator for reduce) and how often it invokes the callback (never for an empty collection; once for the empty element `()`, which is too short for `(x, *rest)`).",
        },
        new()
        {
            Id = "forwarded-callable-keeps-its-algorithm-channel",
            Category = "collection-builtins",
            Source = "Cnt(*xs) = xs.count\nSumWhile(*s) = s.sum + 1, s.sum + 1 < 3\nApply(f, xs) = xs.map(f)\nLoop(g) = while(g, 0)\nOuter(xs) = {\n  Inner(g) = xs.map(g)\n  Inner(Cnt)\n}\n\nApply(Cnt, [1, 2])\nLoop(SumWhile)\nOuter([1, 2])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 1]\n2\n[1, 1]",
            ExpectedRaw = "S[L[1, 1], 2, L[1, 1]]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // Every invoking slot takes the callable: the plain map, filter (also fused
                // with count), reduce, and repeat, and a written forwarding wrapper or a
                // callable alias of the callable (`G = Only` IS Only's callable).
                new SpecProbe("Cnt(*xs) = xs.count\nApply(f, xs) = map(xs, f)\nApply(Cnt, [1, 2])", "ok raw=L[1, 1] n=1"),
                new SpecProbe("Big(*xs) = xs.sum > 1\nKeep(f, xs) = xs.filter(f)\nKeep(Big, [1, 2, 3])", "ok raw=L[2, 3] n=1"),
                new SpecProbe("Big(*xs) = xs.sum > 1\nHits(f, xs) = xs.filter(f).count\nHits(Big, [1, 2, 3])", "ok raw=2 n=1"),
                new SpecProbe("SumAll(*xs) = xs.sum\nFold(f, xs) = xs.reduce(f, 0)\nFold(SumAll, [1, 2, 3])", "ok raw=6 n=1"),
                new SpecProbe("CountStep(*s) = s.count + 1\nRun(g) = repeat(g, 3, 9)\nRun(CountStep)", "ok raw=2 n=1"),
                new SpecProbe("Only(*xs) = xs\nG(*xs) = Only(xs*)\nApply(f, xs) = map(xs, f)\nApply(G, [1])", "ok raw=L[L[1]] n=1"),
                new SpecProbe("Only(*xs) = xs\nG = Only\nApply(f, xs) = map(xs, f)\nApply(G, [1])", "ok raw=L[L[1]] n=1"),
                // VALUE slots read the bound value: the collection and reduce's initial
                // accumulator see the callable's zero-argument value.
                new SpecProbe("Only(*xs) = xs\nSize(xs) = count(xs)\nSize(Only)", "ok raw=0 n=1"),
                new SpecProbe("Seven(*xs) = 7\nR(x, acc) = acc + x\nStart(i) = reduce([1, 2], R, i)\nStart(Seven)", "ok raw=10 n=1"),
                // A value-only argument has no callable to invoke, directly or forwarded:
                // NotAnAlgorithm (Q-06).
                new SpecProbe("Apply(f, xs) = xs.map(f)\nApply(5, [1])", "err notAnAlgorithm"),
                new SpecProbe("[1].map(5)", "err notAnAlgorithm"),
                // A callable whose zero-argument demand fails is bound on the algorithm
                // channel only, and always worked.
                new SpecProbe("Z(*xs) = 10 / xs.count\nApply(f, xs) = xs.map(f)\nApply(Z, [1, 2])", "ok raw=L[10, 10] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Passing a callable to a parameter binds it as a callable, and also as a value when it can be read with no arguments (`Cnt` reads as `0`). A builtin slot that calls its argument — the map mapper, the filter predicate, the reduce reducer, a while or repeat step — calls the callable, so forwarding `Cnt` through `Apply` selects the same callable as `[1, 2].map(Cnt)`, including from a nested block that captures the parameter. Forwarding transports the same demandable cells; callback selection performs no VALUE demand. A slot that reads a value — the collection, reduce's initial accumulator — reads the bound value.",
        },
        new()
        {
            Id = "builtin-call-assembly-respects-argument-roles",
            Category = "collection-builtins",
            Source = "L = L + 1\nAdd(a, b) = a + b\n\nmap([], L)\nfilter([], L)\nreduce([], L, 7)\nreduce([1, 2], Add, 10)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[]\n[]\n7\n13",
            ExpectedRaw = "S[L[], L[], 7, 13]",
            ExpectedEmittedCount = 4,
            Probes =
            [
                // A CALLBACK slot is never evaluated merely because it was supplied: an unused
                // callback cannot fail and cannot recurse, exactly like an unused loop step.
                new SpecProbe("E = ()\nD = E.filter(D)\nD.count", "ok raw=0 n=1"),
                new SpecProbe("A = 1 / 0\nmap([], A), repeat(A, 0, 5)", "ok raw=S[L[], 5] n=2"),
                new SpecProbe("A = 5\nmap([1], A)", "err arity"),
                // reduce's initial is a VALUE slot, demanded once: its failure is the call's
                // failure, and a callable it cannot read keeps reduce's own report.
                new SpecProbe("Add(a, b) = a + b\nreduce([], Add, 1 / 0)", "err div0"),
                new SpecProbe("Add(a, b) = a + b\nreduce([1, 2], Add, 1 / 0)", "err div0"),
                new SpecProbe("Inc(x) = x + 1\nAdd(a, b) = a + b\nProbe(u) = reduce([1, 2], Add, Inc)\nProbe(0)", "err arity"),
                // A SPREAD either supplies exactly its items or its failure is the call's
                // failure, before the arity check — never one phantom argument.
                new SpecProbe("Bad = 1 / 0\ntake(Bad*)", "err div0"),
                new SpecProbe("Bad = 1 / 0\nmap([], Bad*)", "err div0"),
                new SpecProbe("Bad = 1 / 0\nreduce([], Bad*, 0)", "err div0"),
                new SpecProbe("count(1, {}*)", "err spreadMissingOutput"),
                new SpecProbe("P = [1, 2, 3], 2\ntake(P*)", "ok raw=L[1, 2] n=1"),
            ],
            Explanation = "A collection builtin handles each argument by the role its position has. A callback — the map mapper, the filter predicate, the reduce reducer — is invoked once per element and is never evaluated merely because it was passed, so an unused callback has no effect, cannot fail, and cannot recurse (`map([], L)` is `[]` although reading `L` would never end). A value — the collection, a count, reduce's initial accumulator — is evaluated once; if that fails, the failure is the call's failure and is never retried. A spread `X*` supplies exactly its items, and if evaluating `X` fails, that failure is the call's failure before the arguments are counted.",
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
            Explanation = "Three `take` examples (a composite fence from an earlier edition of the tutorial): a plain prefix list, the single-survivor case (the exact one-element list `[(1, 2)]`), and the dot-call form over a `range` list receiver.",
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
            Explanation = "Three `distinct` examples (a composite fence from an earlier edition of the tutorial): atom dedup, structural pair dedup, and the dot-call form over a captured multi-item body.",
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
                new SpecProbe("x = (range(1, 3)*)\nx:0", "ok raw=1 n=1"),
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
            Id = "range-integral-bound-quantum",
            Category = "collection-builtins",
            Source = "range(1.0, 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1, 2, 3]",
            ExpectedRaw = "L[1, 2, 3]",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Decimal128 quantum is outside the Lean Int numeric model: the whole-number bound `1.0` has no Int spelling distinct from `1` (the encoder refuses it), so only the runtime can observe — and must canonicalize — the representation of an integral range bound.",
            Probes =
            [
                // Every spelling of the same integer bounds is the same canonical list,
                // in either direction.
                new SpecProbe("range(1, 3.0)", "ok raw=L[1, 2, 3] n=1"),
                new SpecProbe("range(1.00, 3.000)", "ok raw=L[1, 2, 3] n=1"),
                new SpecProbe("range(3.0, 1)", "ok raw=L[3, 2, 1] n=1"),
                // Signed and fractional zero spellings emit canonical integer zero.
                new SpecProbe("range(-0.0, 2)", "ok raw=L[0, 1, 2] n=1"),
                // Whole-number validation is unchanged: a fractional bound is rejected.
                new SpecProbe("range(1.5, 3)", "err illegalInEval"),
            ],
            Notes = "The canonical case keeps the representative boundary: a whole-number bound written with a quantum is accepted and the list carries the canonical integer representation. RangeBoundCanonicalizationTests retains the denser matrix (exponent spellings, negative bounds, the 1e34 endpoint, the async twin, and fused direct-range iteration) with quantum-level assertions.",
            Explanation = "`range` emits canonical integer elements independent of its accepted whole-number bounds' Decimal128 quantum and zero sign: `range(1.0, 3)` produces `[1, 2, 3]`, and `range(-0.0, 2)` produces `[0, 1, 2]`. The existing bound and collection limits still apply.",
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
            Explanation = "`atoms` recursively erases all sequence-value structure and materializes the collected atoms as one list — the explicit contrast to one-level spread.",
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
                new SpecProbe("atoms(7) == [7]", "ok raw=true n=1"),
                new SpecProbe("atoms(7) == 7", "ok raw=false n=1"),
                new SpecProbe("atoms((1, 2)) == [1, 2]", "ok raw=true n=1"),
                new SpecProbe("atoms((1, 2)) == (1, 2)", "ok raw=false n=1"),
                new SpecProbe("atoms(()) == []", "ok raw=true n=1"),
                new SpecProbe("atoms(()) == ()", "ok raw=false n=1"),
                new SpecProbe("atoms('text')", "ok raw=L[] n=1"),
            ],
            Explanation = "`atoms` always returns one list, whatever the input kind or atom count: a lone number yields the singleton list `[7]` (never the bare `7`), a no-atom input yields `[]`, and the result is list-exact, never a sequence.",
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
                new SpecProbe("[1, [2, 3]].atoms == atoms([1, [2, 3]])", "ok raw=true n=1"),
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
            Source = "if(atoms((1, [2])), 10, 20)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Probes =
            [
                // Every non-Boolean condition is the same value-kind rejection: a list,
                // a sequence value, and a number alike.
                new SpecProbe("if([1], 10, 20)", "err type"),
                new SpecProbe("if([], 10, 20)", "err type"),
                new SpecProbe("if((1, [2]), 10, 20)", "err type"),
                new SpecProbe("if(([1], 0), 10, 20)", "err type"),
                new SpecProbe("if(1, 10, 20)", "err type"),
                // A truth test over atoms is written as a comparison, which yields a Boolean.
                new SpecProbe("if(atoms((1, [2])) == [1, 2], 10, 20)", "ok raw=10 n=1"),
                new SpecProbe("if(atoms(()).count > 0, 10, 20)", "ok raw=20 n=1"),
            ],
            Explanation = "`atoms` does not define truthiness, and neither does any other value: an `if` condition must be a Boolean value, so a list (an `atoms` result included), a sequence value, or a number in the condition slot is a value-kind error rather than a truth test. A truth test over atoms is a comparison, which yields the Boolean the condition needs.",
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
            Explanation = "`count` counts top-level items after the builtin collection binding opens a single grouped value: `()` counts 0, spreads splice before counting, nested pairs count as whole items, and a selected sequence item counts its own members once `count` opens it.",
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
            Source = "X = 1, 2, 3\nif(true, X, X)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3)",
            ExpectedRaw = "S[1, 2, 3]",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("X = 1, 2, 3\nif(true, X, X)*", "ok raw=S[1, 2, 3] n=3"),
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
            Explanation = "A collection builtin receives exactly ONE fixed collection argument plus its fixed control arguments: `count(collection)` and `take(collection, count)` are ordinary fixed-arity callables, so inline items (`count(1, 2, 3)`), a missing control (`take((1, 2, 3))`), a missing collection (`count()`), and spread items (`take([1, 2, 3]*, 2)`) are ordinary arity errors. A scalar is a one-element collection. USER-DEFINED variadic callables remain a separate general arity mechanism: `Inspect(1, 2, 3)` collects the three argument slots as the exact list `[1, 2, 3]`.",
        },
        new()
        {
            Id = "reduce-accumulates-value",
            Category = "collection-builtins",
            Source = "Append(item, (*history)) = (history*, item)\nreduce((2, 3, 4), Append, (0, 1))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(0, 1, 2, 3, 4)",
            ExpectedRaw = "S[0, 1, 2, 3, 4]",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("Append(item, (*history)) = (history*, item)\nProbe(u) = reduce(2, 3, 4, Append, (0, 1))\nProbe(0)", "err arity"),
                new SpecProbe("Append(item, *history) = (history*, item)\nreduce((2, 3, 4), Append, 1)", "ok raw=S[S[S[1, 2], 3], 4] n=1"),
                new SpecProbe("Append(item, [*history]) = [history*, item]\nreduce((2, 3, 4), Append, [1])", "ok raw=L[1, 2, 3, 4] n=1"),
                new SpecProbe("Append(item, (*history)) = (history*, item)\nreduce((2, 3, 4), Append, 1)", "err type"),
                new SpecProbe("Add(a, b) = a + b\nreduce((1, 2, 3, 4), Add, 0)", "ok raw=10 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`reduce(collection, reducer, initial)` takes exactly three arguments and threads ONE accumulator value: the reducer is called as `Append(item, accumulator)`, two ordinary arguments. The explicit sequence pattern `(*history)` opens a SEQUENCE accumulator — a scalar is its kind mismatch, so the accumulator starts as the pair `(0, 1)` — and the result displays as ONE sequence value `(0, 1, 2, 3, 4)`, not as separate rows; the list pattern `[*history]` opens a list accumulator of any length, one element included. An unopened collecting parameter `*history` collects the one accumulator value whole, nesting each step. Supplying the items inline (`reduce(2, 3, 4, Append, (0, 1))`) is an ordinary five-argument arity error.",
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
            ExpectedDisplay = "true",
            ExpectedRaw = "true",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("A = 1, (2, 3)\nC = 1, (2, 4)\nA == C", "ok raw=false n=1"),
                new SpecProbe("1 == (1, 2)", "ok raw=false n=1"),
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
            Id = "index-selects-one-value",
            Category = "equality-and-indexing",
            Source = "Pairs = (1, 2), (3, 4)\nPairs:0",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2)",
            ExpectedRaw = "S[1, 2]",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("Pairs = (1, 2), (3, 4)\n(Pairs:0).count", "ok raw=2 n=1"),
                new SpecProbe("G(a) = a\nPairs = (1, 2), (3, 4)\nG(Pairs:0)", "ok raw=S[1, 2] n=1"),
                new SpecProbe("Pairs = (1, 2), (3, 4)\nfirst(Pairs)", "ok raw=S[1, 2] n=1"),
                new SpecProbe("Pairs = (1, 2), (3, 4)\nX = Pairs:0\nX", "ok raw=S[1, 2] n=1"),
                new SpecProbe("Pairs = (1, 2), (3, 4)\n(Pairs:0)*", "ok raw=S[1, 2] n=2"),
                new SpecProbe("Pairs = (1, 2), (3, 4)\nPairs:0*", "ok raw=S[1, 2] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "SELECTION IS A VALUE BOUNDARY: `:` returns the selected item as ONE value without opening it, so a selected sequence value is one root row — exactly what `first(Pairs)` or a property holding the same value shows. Only an explicit spread `(Pairs:0)*` opens the selected value into its items.",
        },
        new()
        {
            Id = "selection-forms-agree",
            Category = "equality-and-indexing",
            Source = "Coll(*xs) = xs\nPairs = (1, 2), (3, 4)\nfirst(Pairs).Coll\nPairs:0.Coll\n(Pairs:0)*.Coll\nPairs:0.Coll(3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[(1, 2)]\n[(1, 2)]\n[1, 2]\n[(1, 2), 3]",
            ExpectedRaw = "S[L[S[1, 2]], L[S[1, 2]], L[1, 2], L[S[1, 2], 3]]",
            ExpectedEmittedCount = 4,
            Probes =
            [
                new SpecProbe("Coll(*xs) = xs\nA = ((), 1)\nA:0.Coll", "ok raw=L[S[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nA = ((), 1)\nfirst(A).Coll", "ok raw=L[S[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nA = (1, ())\nlast(A).Coll", "ok raw=L[S[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nA = ((), 1)\nA:0.Coll(3)", "ok raw=L[S[], 3] n=1"),
                new SpecProbe("Coll(*xs) = xs\nA = ((), 1)\n(A:0)*.Coll", "ok raw=L[] n=1"),
                new SpecProbe("Coll(*xs) = xs\nA = ([], 1)\nfirst(A).Coll", "ok raw=L[L[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nA = ([], 1)\n(A:0)*.Coll", "ok raw=L[] n=1"),
                new SpecProbe("Coll(*xs) = xs\nA = (3, [1, 2])\nlast(A).Coll", "ok raw=L[L[1, 2]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nA = (3, (1, 2))\n(last(A))*.Coll", "ok raw=L[1, 2] n=1"),
                new SpecProbe("Coll(*xs) = xs\nA = (3, (1, 2))\nlast(A).Coll", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nA = (((1, 2), 3), 9)\nA:0.Coll", "ok raw=L[S[S[1, 2], 3]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nE = ()\nE.Coll", "ok raw=L[S[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nE = ()\nColl(E)", "ok raw=L[S[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nV = (1, 2)\nV.Coll", "ok raw=L[S[1, 2]] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`first(A)`, `last(A)`, and `A:i` are the same selection: each returns the selected value through the ordinary value boundary, and dot-call passes that value as the ordinary leading argument. Later behavior depends only on that value, never on selection provenance: a selected pair is ONE argument, collected as one item (`[(1, 2)]`, exactly like `V.Coll` on a property holding the pair), a selected `()` is one visible item (`[()]`, like `Coll(())`), a selected `[]` stays one exact list, and beside another argument the selected value is one item too (`Pairs:0.Coll(3)` is `[(1, 2), 3]`). Only the spread marker opens a selected sequence or list — and a spread `()` supplies nothing.",
        },
        new()
        {
            Id = "index-nested-stays-intact",
            Category = "equality-and-indexing",
            Source = "Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8))\nBags:0\nBags:0:1",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "((1, 2), (3, 4))\n(3, 4)",
            ExpectedRaw = "S[S[S[1, 2], S[3, 4]], S[3, 4]]",
            ExpectedEmittedCount = 2,
            Explanation = "Selection is one-level only and never opens what it selects: nested pairs stay intact, each selection is one root row, and chaining `:` repeats the one-level step.",
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
            Probes =
            [
                new SpecProbe("Coll(*xs) = xs\nx = ((), ())\nx:0.Coll", "ok raw=L[S[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nx = ((), ())\nfirst(x).Coll", "ok raw=L[S[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nx = ((), ())\nx:0.Coll(1)", "ok raw=L[S[], 1] n=1"),
                new SpecProbe("Coll(*xs) = xs\nx = ((), ())\n(x:0)*.Coll", "ok raw=L[] n=1"),
                new SpecProbe("One(a) = 1\nx = ((), ())\nx:0.One", "ok raw=1 n=1"),
            ],
            Explanation = "Selecting a `()` item shows one `()` row (a non-spread root row is always one visible slot): the empty value is a real selectable item, and past the selection boundary it is simply `()` — ONE argument value when passed (dot-call passes a value: `x:0.One` binds it, `x:0.Coll` collects `[()]`, and `x:0.Coll(1)` collects `[(), 1]`), and zero items only when spread (`(x:0)*.Coll` is `[]`), whatever route selected it.",
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
            ExpectedDisplay = "true",
            ExpectedRaw = "true",
            ExpectedEmittedCount = 1,
            Explanation = "A stored selection is the selected value itself and compares structurally equal to the written literal.",
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
            Explanation = "Semicolon is not expression syntax: use a comma between slots on one line (or a new line where the context separates rows), or parentheses for one sequence value.",
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
            Id = "star-before-operand-row-is-multiplication",
            Category = "parser-layout",
            Source = "A = 4\nB = 6\nA*\nB",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "24",
            ExpectedRaw = "24",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("A = 4\nB = 6\nA *\nB", "ok raw=24 n=1"),
                new SpecProbe("A = 4\nB = 6\nA* B", "ok raw=24 n=1"),
                new SpecProbe("A = 4\nB = 6\nA * B", "ok raw=24 n=1"),
                new SpecProbe("A = 4\nB = 6\nX = A*\nB\nX", "ok raw=24 n=1"),
                new SpecProbe("A = (1, 2)\nB = 5\nA*,\nB", "ok raw=S[1, 2, 5] n=3"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "SYN-07B: the star is read by the token that follows it, never by spacing or by the line break. `A*` newline `B`, `A *` newline `B`, `A* B`, and `A * B` are all the multiplication `A * B` — when the next significant token can begin an operand and does not begin a declaration, a line-final star continues across the newline like every trailing binary operator, in a definition body too (Q-33). To spread `A` and then emit `B` as the next row, close the spread slot with a comma (`A*,` newline `B`).",
        },
        new()
        {
            Id = "star-before-declaration-or-boundary-is-spread",
            Category = "parser-layout",
            Source = "A = (1, 2)\nA*\nB = 5\nB",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n2\n5",
            ExpectedRaw = "S[1, 2, 5]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                new SpecProbe("A = (1, 2)\nA*", "ok raw=S[1, 2] n=2"),
                new SpecProbe("F(*items) = items\nA = (1, 2)\nF(A*, 3)", "ok raw=L[1, 2, 3] n=1"),
                new SpecProbe("A = (1, 2)\nX = (A*)\nX", "ok raw=S[1, 2] n=1"),
                new SpecProbe("A = (1, 2)\nB = 3\nX = A*\nB\nX", "err type"),
                // The detached spellings (`A *` before the declaration, at the
                // end of the program, or inside the call) are neither spread
                // nor multiplication: the marker attachment law rejects them —
                // a parse-level outcome, pinned by `spread-marker-must-be-attached`.
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A declaration head is never a multiplication operand, so a line-final star before `B = 5` is the spread marker — through the same declaration relation that ends an adjacency row. The star is likewise a spread before a comma, a closing delimiter, or the end of the program. A spread marker must be directly attached to its operand (`A*`): the detached `A *` in any of these positions is a parse error, never silently a spread and never silently a multiplication. A definition body that ends in a spread must be closed when an output row follows: `X = (A*)` captures the spread supply, while a bare `X = A*` above the row `B` is the multiplication `X = A * B`.",
        },
        new()
        {
            Id = "line-final-star-in-definition-continues",
            Category = "parser-layout",
            Source = "A = 2\nX = A*\n3\nX",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "6",
            ExpectedRaw = "6",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("A = (1, 2)\nX = (A*)\n3\nX", "ok raw=S[3, S[1, 2]] n=2"),
                new SpecProbe("A = (1, 2)\nX = { A* }\n3\nX", "ok raw=S[3, S[1, 2]] n=2"),
                new SpecProbe("A = 2\nX = A *\n3\nX", "ok raw=6 n=1"),
                new SpecProbe("A = 2\nB = 3\nX = A*\nB + 1\nX", "ok raw=7 n=1"),
                new SpecProbe("A = 2\nX = A*\n# comment\n\n3\nX", "ok raw=6 n=1"),
                new SpecProbe("A = (1, 2)\nX = A*\nY = 3\nX", "ok raw=S[1, 2] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Q-33 (decided 2026-10-09): a line-final star in a definition body is classified like every star. The next significant token, `3`, can begin an operand and does not begin a declaration, so the star is multiplication and the definition continues across the newline: its body is `A * 3`, so `X` is 6 and the line `3` belongs to the definition instead of being an output row. Operator precedence is unchanged (`X = A*` newline `B + 1` is `X = (A * B) + 1`), and the layout is valid source with no warning or error. A definition meant to end in a spread is closed structurally — `X = (A*)` or `X = { A* }` — and the next line is then its own output row; a following declaration head also ends the body, so `X = A*` newline `Y = 3` keeps `X` the spread of `A`.",
        },
        new()
        {
            Id = "spread-marker-must-be-attached",
            Category = "parser-layout",
            Source = "A = (1, 2)\nA *",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "The spread marker `*` must be directly attached to the expression it spreads",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidSpreadMarker,
            IncludeInGeneratorPrompt = true,
            Explanation = "The marker attachment law: a structural marker is directly attached to the syntax it modifies (`A*`, `*items`, `~x`, `x~`), while the multiplication operator may be spaced freely. `A *` with nothing that could be a right operand after it is classified as a spread marker (SYN-07B) and then rejected for being detached — whitespace never turns one valid operation into another; it only separates the valid `A*` from this error. Write `A*` to spread, or give the star a right operand to multiply.",
        },
        new()
        {
            Id = "grace-marker-must-be-attached",
            Category = "parser-layout",
            Source = "Divide = y / ~ x\nDivide(2, 10)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "The Grace marker `~` must be directly attached to the name it decorates",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidGraceMarker,
            Explanation = "Grace decorates exactly one bare name and must be written directly attached to it: `~x` or `x~`. A detached `~ x` (or `x ~`) is rejected rather than silently reordering — or silently not reordering — the parameters; the attached `Divide = y / ~x` infers `(x, y)` and `Divide(2, 10)` is `5`.",
        },
        new()
        {
            Id = "grace-on-bound-name-rejected",
            Category = "parser-layout",
            Source = "X = 1\nK = ~X + 2\nK",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Grace cannot reorder 'X' because it already resolves to a property",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidGraceMarker,
            IncludeInGeneratorPrompt = true,
            Explanation = "Grace requires an OWN inferred parameter: it is valid only on a FREE name that becomes one of its algorithm's inferred parameters — that is the one place its weight is consumed. `X` is a visible property, so there is no inferred parameter for `~X` to weight; instead of being silently ignored the marker is a front-end error naming what fixed the binding. Cancelling markers (`~X~`) still validate this binding. The same rule covers a builtin (`~count`), an opened name, a parameter of an enclosing algorithm, and a dot member the receiver is known to declare (`Obj.~V`). A marker on a free name that the ordering cannot move is NOT an error (`grace-saturation-is-valid`).",
        },
        new()
        {
            Id = "grace-under-explicit-list-rejected",
            Category = "parser-layout",
            Source = "K(b, a) = b, ~a\nK(1, 2)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Grace cannot reorder 'a' because it already resolves to an explicit parameter",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidGraceMarker,
            IncludeInGeneratorPrompt = true,
            Explanation = "An explicit parameter list fixes the parameter order, so nothing is inferred under it and a Grace marker there has no inferred parameter to weight: `K(b, a) = b, ~a` is rejected rather than silently keeping `(b, a)`. Write the order in the list (`K(a, b) = b, a`) or drop the list and let `~a` reorder the inferred parameters (`K = b, ~a` infers `(a, b)`).",
        },
        new()
        {
            Id = "grace-in-branch-deconstruction-rejected",
            Category = "parser-layout",
            Source = "F(0) = 0\nF(n) = {\n    a, b = (~n, 1)\n    a + b\n}\nF(5)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Grace cannot reorder 'n' because it is a binder of this clause's head",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidGraceMarker,
            Probes =
            [
                new SpecProbe("F(0) = 0\nF(n) = {\n    a, b = (n, 1)\n    a + b\n}\nF(5)", "ok raw=6 n=1"),
                // A property nested in the branch is a level of its own that infers `(x, y)`.
                new SpecProbe("F(0) = 0\nF(n) = {\n    P = {\n        a, b = (y, ~x)\n        a / b\n    }\n    P(2, 10) + n\n}\nF(1)", "ok raw=6 n=1"),
                // So is a brace block nested in the branch, its own deconstruction included (Q-16 G-O).
                new SpecProbe("Apply(f) = f(2, 10)\nF(0) = 0\nF(n) = Apply({\n    a, b = (y, ~x)\n    a / b\n}) + n\nF(1)", "ok raw=6 n=1"),
            ],
            Notes = "Constitution PV-49 (September 2026): assignment deconstruction hoists its right-hand side into a synthetic source whose rows are rows of the enclosing body, and the parser's branch Grace scan read only the branch's output rows, so the marker was silently accepted in a family branch while the same body under a single clause was refused; the scan was then extended to every written row (`AstHelpers.WrittenRows`). Q-16 G-O (2026-10-07) deleted that lexical scan: the parameter detector's branch region judges every row the branch writes (a closed level), and a block or property nested in the branch is an owner of its own. The expected fragment changed accordingly (formerly \"Grace is not allowed in conditional branch bodies for 'F'.\"); the verdict did not.",
            Explanation = "A clause branch's own level infers nothing — its head is the complete input specification — so no marker in any row the branch writes has an inferred parameter to weight, and a deconstruction's right-hand side is one of those rows: `a, b = (~n, 1)` in a family branch is rejected exactly like the same marker in a branch output row (`n` is a binder of the clause head). Drop the marker. Grace stays valid where a level really infers, such as a property or a brace block nested in the branch.",
        },
        new()
        {
            Id = "grace-in-branch-nested-block-belongs-to-the-block",
            Category = "name-resolution",
            Source = "Apply(f) = f(1, 10)\nF(0) = Apply({ y - ~x })\nF(0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "9",
            ExpectedRaw = "9",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // Without the marker the block infers `(y, x)`: y = 1, x = 10.
                new SpecProbe("Apply(f) = f(1, 10)\nF(0) = Apply({ y - x })\nF(0)", "ok raw=-9 n=1"),
                // The same owner written as a property of the branch agrees.
                new SpecProbe("Apply(f) = f(1, 10)\nF(0) = {\n    B = y - ~x\n    Apply(B)\n}\nF(0)", "ok raw=9 n=1"),
                // Adding a sibling clause never changes the nested owner's Grace: a single clause and a family agree.
                new SpecProbe("Apply(f) = f(1, 10)\nG(k) = Apply({ y - ~x }) + k\nG(1)", "ok raw=10 n=1"),
                new SpecProbe("Apply(f) = f(1, 10)\nG(0) = 0\nG(k) = Apply({ y - ~x }) + k\nG(1)", "ok raw=10 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Q-16 G-O (2026-10-07), Q-16(2) O: formerly the inline block was rejected by the parser's lexical branch scan (a representation side effect of the pre-#143 shared `Expr.Block`) while the named property was accepted (X-08). The branch's own level stays closed: `grace-in-branch-deconstruction-rejected`, `grace-on-branch-binder-in-nested-block-rejected`.",
            Explanation = "Grace belongs to the algorithm whose rows contain the marker. A clause branch's own level infers nothing — its head is its complete input specification — but a brace block nested in the branch is an algorithm of its own: `{ y - ~x }` infers `(x, y)` itself (`(y, x)` without the marker), so `Apply` calls it with `x = 1`, `y = 10` and `F(0)` is `9`. The same block written as the branch's property `B = y - ~x` agrees, adding a sibling clause changes nothing, and the branch never gains a parameter. A marker on the branch's own level — `F(n) = ~n + 1` — is still an error.",
        },
        new()
        {
            Id = "grace-saturation-is-valid",
            Category = "parser-layout",
            Source = "F = ~x + 1\nA = p - q\nG = A - z~\nH = ~a + b * 10\nF(3), G(1, 2, 3), H(1, 2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "4\n-2\n21",
            ExpectedRaw = "S[4, -2, 21]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // Already last: postfix weight on the last name.
                new SpecProbe("K = x + y~ * 10\nK(1, 2)", "ok raw=21 n=1"),
                // Excess weight: two units on a name that is already first.
                new SpecProbe("K = ~~x + y * 10\nK(1, 2)", "ok raw=21 n=1"),
                // A tie: an equal weight on the neighbour blocks the move.
                new SpecProbe("K = ~x + ~y * 10\nK(1, 2)", "ok raw=21 n=1"),
                // Cancelled weight on one occurrence.
                new SpecProbe("K = ~x~ + y * 10\nK(1, 2)", "ok raw=21 n=1"),
                // Cancelled weight across two occurrences of one name.
                new SpecProbe("K = ~x + y * 10 + 0 * x~\nK(1, 2)", "ok raw=21 n=1"),
                // The marker that does move: the same rule, applied.
                new SpecProbe("K = x + ~y * 10\nK(1, 2)", "ok raw=12 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "Q-16 G-O (2026-10-07), Q-16(1) E: Grace requires an OWN inferred parameter, never actual movement. The X-39 wording conflict (\"never a silent no-op\" versus \"excess movement is ignored\") is resolved in favour of eligibility.",
            Explanation = "Grace is an ordering weight on one of its algorithm's OWN inferred parameters, and it is valid whenever the marked name is one — even when the ordering cannot move it (saturation). `F = ~x + 1` has a single inferred parameter; in `H = ~a + b * 10`, `a` is already first; and in `G = A - z~` the own name `z` cannot cross into the names `G` lifts from `A`, because a formula's own names always come before the names it lifts: `G(z, p, q)`, so `G(1, 2, 3)` is `(2 - 3) - 1`. A name already last, excess weight, an equal weight on the neighbour and a cancelled `~x~` are saturation too. None of these is an error; Grace is rejected only where the marked name is not an inferred parameter at all (an explicit parameter, a clause binder, a property, a builtin, an opened name, a structural member).",
        },
        new()
        {
            Id = "grace-on-branch-binder-in-nested-block-rejected",
            Category = "name-resolution",
            Source = "Apply(f) = f(1)\nF(0) = 0\nF(n) = Apply({ x - ~n })\nF(1)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Grace cannot reorder 'n' because it already resolves to a parameter of an enclosing algorithm",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidGraceMarker,
            Probes =
            [
                // Without the marker the block captures the binder and infers only `x`.
                new SpecProbe("Apply(f) = f(1)\nF(0) = 0\nF(n) = Apply({ x - n })\nF(1)", "ok raw=0 n=1"),
                // The block's OWN free name may be graced.
                new SpecProbe("Apply(f) = f(1)\nF(0) = 0\nF(n) = Apply({ ~x - n })\nF(1)", "ok raw=0 n=1"),
            ],
            Notes = "Q-16 G-O (2026-10-07): exactly one report, by the block's own detector region (formerly the parser's lexical branch scan added a second report at the same span).",
            Explanation = "Inside a block nested in a clause branch, the branch binder `n` is a parameter of the ENCLOSING branch that the block captures — never one of the block's own inferred parameters — so a marker on it has no inferred parameter to weight and is rejected, once, at the marker. The block's own free name `x` is inferred as usual and may carry Grace.",
        },
        new()
        {
            Id = "declaration-head-never-spans-lines",
            Category = "parser-layout",
            Source = "Foo\n(x) = x + 1\nFoo(1)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "A declaration head cannot be assembled across a physical newline",
            ExpectedDiagnosticCode = DiagnosticCode.UnexpectedToken,
            IncludeInGeneratorPrompt = true,
            Explanation = "A simple definition or deconstruction head stays on one physical line. A clause head's name and `(` share a line, its closing `)` and `=` share a line, and the pattern list inside those parentheses may span lines. A newline never assembles a head: `Foo` on its own line is a closed output row, `(x)` the next row, and the `=` is a stray token reported with the repair. `A` newline `= 1` and `Foo(x)` newline `= x + 1` are rejected the same way (before this rule they silently became `Foo(x) = x + 1`, and `Foo(1)` newline `= 3` even added a clause to an existing family). The body of a recognized head may still begin on the next line: `A =` newline `1` defines `A = 1`, and `F(a,` newline `b) = a + b` keeps its pattern list open across the line.",
        },
        new()
        {
            Id = "collect-marker-must-be-attached",
            Category = "parser-layout",
            Source = "F(* items) = items\nF(1, 2)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "The collect marker `*` must be directly attached to its binding name",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidCollectMarker,
            Explanation = "A collecting binding is written `*items`, the collect marker directly attached to its name, on every binding surface (explicit parameter lists, nested sequence-value patterns, assignment deconstruction). A detached `* items` never creates a collecting binding; it is a parse error.",
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
            Id = "grace-line-final-marker-after-call-rejected",
            Category = "parser-layout",
            Source = "Q = {\n  b\n  F(1)~\n  a\n}\nF(z) = z\nQ(10, 20)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Grace `~` can only be applied to a parameter or name occurrence",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidGraceMarker,
            Explanation = "A grace marker never binds across a physical newline in either direction: `F(1)~` at the end of a row is the rejected `f(x)~` spelling (Grace decorates exactly one bare name), never prefix Grace on the next row's `a`. Write the marker on the name it decorates, on that name's line: `~a`.",
        },
        new()
        {
            Id = "grace-weights-accumulate",
            Category = "parser-layout",
            Source = "Weighted = a + 10 * b + 100 * ~~c\n\nWeighted(1, 2, 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "132",
            ExpectedRaw = "132",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // One unit moves one position: (a, c, b).
                new SpecProbe("Weighted = a + 10 * b + 100 * ~c\n\nWeighted(1, 2, 3)", "ok raw=231 n=1"),
                // Opposite markers on one occurrence cancel: the order stays (a, b, c).
                new SpecProbe("Weighted = a + 10 * b + 100 * ~c~\n\nWeighted(1, 2, 3)", "ok raw=321 n=1"),
                // Markers on separate occurrences of one name add up: two units again give (c, a, b).
                new SpecProbe("Weighted = a + 10 * b + 100 * ~c + ~c\n\nWeighted(1, 2, 3)", "ok raw=133 n=1"),
                // Weight beyond the start of the list is clamped, never wrapped.
                new SpecProbe("Weighted = a + 10 * b + 100 * ~~~~~c\n\nWeighted(1, 2, 3)", "ok raw=132 n=1"),
                // Postfix weight pushes later: (b, c, a).
                new SpecProbe("Weighted = a~~ + 10 * b + 100 * c\n\nWeighted(1, 2, 3)", "ok raw=213 n=1"),
                // The inferred signature is observable: an arity error names it.
                new SpecProbe("Weighted = a + 10 * b + 100 * ~~c\n\nWeighted(1)", "err arity"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Every Grace marker is one unit of weight on its name — prefix `~` one position earlier, postfix `~` one position later — and the weights of all markers on all occurrences of one name in the same body add up. First appearance gives `(a, b, c)`; `~~c` carries two units, so the signature is `Weighted(c, a, b)` and the call binds `c = 1`, `a = 2`, `b = 3`. A name never moves past the ends of the list, and `~c~` cancels to zero.",
        },
        new()
        {
            Id = "grace-front-first-movement",
            Category = "parser-layout",
            Source = "A = s * 100 + ~x * 10 + ~y\nB = s~ * 100 + x~ * 10 + y\nC = a * 100 + b~ * 10 + ~~c\nD = a~ * 100 + b * 10 + ~c\nE = ~a * 100 + b * 10 + ~~c\nA(1, 2, 3), B(1, 2, 3), C(1, 2, 3), D(1, 2, 3), E(1, 2, 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "312\n231\n231\n312\n132",
            ExpectedRaw = "S[312, 231, 231, 312, 132]",
            ExpectedEmittedCount = 5,
            Probes =
            [
                // Equal prefix weights at the front: a keeps its unused −1 and blocks b.
                new SpecProbe("K = ~a * 100 + ~b * 10 + c\nK(1, 2, 3)", "ok raw=123 n=1"),
                // Patent FIG. 12: a's unused second unit still protects it from b.
                new SpecProbe("SumOfParams = a~~ * 10 + b~\nSumOfParams(1, 2)", "ok raw=21 n=1"),
                // Equal-weight groups among zero-weight names move as a unit, rightward and leftward.
                new SpecProbe("K = a~ * 1000 + b~ * 100 + c~ * 10 + d\nK(1, 2, 3, 4)", "ok raw=2341 n=1"),
                new SpecProbe("K = a * 1000 + ~b * 100 + ~c * 10 + ~d\nK(1, 2, 3, 4)", "ok raw=4123 n=1"),
                // Passive displacement: b, c and d carry e one place left before e takes its own turn.
                new SpecProbe("K = a * 10000 + b~ * 1000 + c~ * 100 + d~ * 10 + ~e\nK(1, 2, 3, 4, 5)", "ok raw=23451 n=1"),
                // A stronger same-direction push passes residual weight.
                new SpecProbe("K = ~a * 100 + b * 10 + ~~~c\nK(1, 2, 3)", "ok raw=231 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "X-49 (decided 2026-10-08): front-first movement, postfix movers first, residual weights retained (PAR-06). `C` was `C(a, c, b)` = 132 before: a position cursor skipped `c` once `b` had displaced it.",
            Explanation = "Each Grace marker asks for one adjacent move, and the names move one at a time: first every name with postfix weight, starting from the last-written, then every name with prefix weight, starting from the first-written. A name passes a neighbour unless that neighbour moves the same way with at least as much weight left, and weight it cannot use stays with it. `A`: `x` moves first and clears the way for `y`, so `A(x, y, s)`. `B`: `x`, in front, moves first, then `s` passes `y`, so `B(y, s, x)`. `C`: `b` passes `c`, and `c` still takes its own turn and passes `a`, so `C(c, a, b)` — as without `b~`. `D`: `a` moves right first, then `c` moves left past `a`, so `D(b, c, a)`. `E`: `a` is already first and keeps its unused unit; `c` passes `b` but not `a`, whose remaining weight equals its own, so `E(a, c, b)`.",
        },
        new()
        {
            Id = "grace-prefix-marker-led-row",
            Category = "parser-layout",
            Source = "K = {\n  a\n  ~b\n}\nK(10, 20)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(20, 10)",
            ExpectedRaw = "S[20, 10]",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // `A` newline `~b` stays two rows of the block: the marker belongs
                // to its own line and never continues `A` as postfix Grace, so
                // `K(2)` yields the pair (1, 2) as one value. (`b` is a free name of
                // the block — Grace on the bound `A` would be rejected.)
                new SpecProbe("A = 1\nK = {\n  A\n  ~b\n}\nK(2)", "ok raw=S[1, 2] n=1"),
            ],
            Explanation = "A `~`-led row is its own prefix-grace expression, and the marker and its name share one physical line: `~b` moves `b` one position earlier, so the block's implicit parameters are `(b, a)` and `K(10, 20)` binds `b = 10`, `a = 20`.",
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
            Explanation = "A call delimiter continues the callable across same-line whitespace: `Add (1, 2)` is still the call (whitespace inside one expression is formatting, never a slot boundary).",
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
            Source = "X(*vals) = vals.count\nb = (1, 2)\nX(7, b*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3",
            ExpectedRaw = "3",
            ExpectedEmittedCount = 1,
            Explanation = "A spread expression is one whole expression-list slot: `X(7, b*)` supplies `7` and then b's two items, so the collecting parameter collects three values (the comma before `b*` is required like every same-line comma; `X(7 b*)` is rejected).",
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
            Id = "output-less-argument-is-not-an-omitted-argument",
            Category = "errors",
            Source = "Coll(*xs) = xs\nColl({})",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "missingOutput",
            Probes =
            [
                new SpecProbe("Coll(*xs) = xs\nColl()", "ok raw=L[] n=1"),
                new SpecProbe("Coll(*xs) = xs\nColl(())", "ok raw=L[S[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nEmpty = ()\nColl(Empty*)", "ok raw=L[] n=1"),
                new SpecProbe("Coll(*xs) = xs\nColl([])", "ok raw=L[L[]] n=1"),
                new SpecProbe("Coll(*xs) = xs\nColl({}*)", "err spreadMissingOutput"),
                new SpecProbe("Coll(*xs) = xs\nColl(1, {}, 3)", "err missingOutput"),
                new SpecProbe("F(x) = x\nF()", "err arity"),
                new SpecProbe("F(x) = x\nF({})", "err missingOutput"),
                new SpecProbe("F(x) = x\nF([])", "ok raw=L[] n=1"),
                new SpecProbe("F(x) = x\nF(())", "ok raw=S[] n=1"),
            ],
            Explanation = "A collector legally accepts zero supplied items, which is exactly why an ordinary written argument that produced no output must not be read as \"nothing was supplied\": `Coll({})` is an error, never `Coll()`. The four situations stay distinct — an OMITTED argument is an arity failure (`F()`), a written argument with no output is that argument's failure (`F({})`, `Coll({})`), a legitimate empty value is one ordinary argument (`F([])`, `F(())`, and `Coll(())` is `[()]`, `Coll([])` is `[[]]`), and an explicit spread supplying zero items is a legal supply (`Coll(Empty*)` is `[]`). The distinction follows slot provenance, never the final supplied-item count.",
        },
        new()
        {
            Id = "argument-value-outcome-is-final",
            Category = "errors",
            Source = "Plus(f, x) = f + x\nPlus({x + 1}, 5)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "unresolvedImplicitParams",
            Probes =
            [
                new SpecProbe("Apply(f, x) = f(x)\nApply({x + 1}, 5)", "ok raw=6 n=1"),
                new SpecProbe("Only(g) = g\nOnly({x + 1})", "err unresolvedImplicitParams"),
                new SpecProbe("G(v) = sum(v)\nG({x + 1})", "err unresolvedImplicitParams"),
                new SpecProbe("G(v) = if(true, v, 0)\nG({x + 1})", "err unresolvedImplicitParams"),
                new SpecProbe("G(v) = reduce([1], {e + a}, v)\nG({x + 1})", "err unresolvedImplicitParams"),
                new SpecProbe("Inc(y) = y + 1\nPlus(f, x) = f + x\nPlus(Inc, 5)", "err arity"),
                new SpecProbe("F(0) = 1\nF(n) = n\nApply(f) = f\nApply(F)", "err branch"),
                new SpecProbe("Bad = 1 / 0\nPair(x) = x, x\nPair(Bad)", "err div0"),
                new SpecProbe("Bad = 1 / 0\nFirst(x, y) = x\nFirst(1, Bad)", "ok raw=1 n=1"),
                new SpecProbe("Bad = 1 / 0\nSecond(x, y) = y\nSecond(1, Bad)", "err div0"),
                new SpecProbe("Box = { public X = 5 }\nMember(o) = o.X\nMember(Box)", "ok raw=5 n=1"),
            ],
            Explanation = "Each argument of a call is evaluated at most once for its value: if that evaluation succeeds, that is the parameter's value, and if it fails, that is the parameter's failure. Reading the parameter never evaluates the argument again, so every read reports the same outcome and a failure can never turn into a value. The brace algorithm `{x + 1}` cannot be evaluated as a value — its `x` is not supplied — so reading `f` as a value reports exactly that failure (`unresolvedImplicitParams`), while calling `f(x)` still runs the algorithm (`Apply({x + 1}, 5)` is 6), and structural access through the parameter still reaches the argument's members (`Member(Box)` is 5). A failing argument nobody reads is not an error (`First(1, Bad)` is 1).",
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
                new SpecProbe("() > 1", "err type"),
                new SpecProbe("() + 1", "err type"),
                new SpecProbe("1 + ()", "err type"),
                new SpecProbe("[] + 1", "err type"),
            ],
            Notes = "The probes pin that operand cardinality grants no exemption: an empty sequence value and an empty list are rejected exactly like a multi-item sequence value (SYN-01), on either operand side.",
            Explanation = "Binary scalar operators require numeric scalar operands; a sequence value is a type error whatever its item count, including the empty sequence value `()`.",
        },
        new()
        {
            Id = "empty-sequence-is-not-an-operator-identity",
            Category = "errors",
            Source = "10 / ()",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Probes =
            [
                // The other three SYN-01 reproductions; the case source is the
                // fourth. Each returned the OTHER operand before this rule — the
                // source was `10`, and these were `10`, `7`, and `text`.
                new SpecProbe("() > 10", "err type"),
                new SpecProbe("() and true", "err type"),
                new SpecProbe("() + 'text'", "err type"),
                // Left-empty and right-empty across the operator families.
                new SpecProbe("() + 1", "err type"),
                new SpecProbe("1 + ()", "err type"),
                new SpecProbe("() - 1", "err type"),
                new SpecProbe("1 - ()", "err type"),
                new SpecProbe("() * 2", "err type"),
                new SpecProbe("2 * ()", "err type"),
                new SpecProbe("() / 2", "err type"),
                new SpecProbe("() div 2", "err type"),
                new SpecProbe("() mod 2", "err type"),
                new SpecProbe("() ^ 2", "err type"),
                new SpecProbe("2 ^ ()", "err type"),
                new SpecProbe("() < 1", "err type"),
                new SpecProbe("1 < ()", "err type"),
                new SpecProbe("() >= 1", "err type"),
                new SpecProbe("1 >= ()", "err type"),
                new SpecProbe("() or false", "err type"),
                new SpecProbe("false or ()", "err type"),
                new SpecProbe("() xor true", "err type"),
                new SpecProbe("() + ()", "err type"),
                // Redundant parentheses normalize to `()` and change nothing.
                new SpecProbe("(()) + 1", "err type"),
                // A NAMED empty operand takes the same path as the literal.
                new SpecProbe("A = ()\nA / 2", "err type"),
                // Unary minus rejects every non-numeric operand as a value of the wrong
                // kind (Q-27), and unary `not` its non-Boolean operand, both in the type
                // category, with no empty-sequence bypass either.
                new SpecProbe("-()", "err type"),
                new SpecProbe("not ()", "err type"),
                new SpecProbe("-(1, 2)", "err type"),
                new SpecProbe("not (1, 2)", "err type"),
                new SpecProbe("-[1, 2]", "err type"),
                new SpecProbe("not [1, 2]", "err type"),
                new SpecProbe("-7", "ok raw=-7 n=1"),
                new SpecProbe("not false", "ok raw=true n=1"),
                new SpecProbe("not true", "ok raw=false n=1"),
                // Positive controls: equality stays total over empty operands, and
                // ordinary comparisons still produce a Boolean value.
                new SpecProbe("() == ()", "ok raw=true n=1"),
                new SpecProbe("() != (1, 2)", "ok raw=true n=1"),
                new SpecProbe("10 > 1", "ok raw=true n=1"),
                new SpecProbe("1 > 10", "ok raw=false n=1"),
                // Positive control: empty SUPPLY neutrality is a different rule and
                // is unchanged — the spread of `()` still contributes no items.
                new SpecProbe("Empty = ()\nEmpty*, 7", "ok raw=7 n=1"),
                new SpecProbe("count(())", "ok raw=0 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Notes = "SYN-01. Binary operators previously returned the other operand when either was `()`; unary operators propagated `()`. Both bypasses are removed. Unary and binary operand rejections are both the type category (unary sequence/list rejection was arity until Q-27, 2026-10-05). Empty NEUTRALITY belongs to the arity algebra's supply operations (capture/collect/spread) and is deliberately untouched, as the last two probes pin.",
            Explanation = "The empty sequence value is a real value, not an operator identity: scalar operators apply their ordinary operand validation to `()` just as to any other non-scalar value. `10 / ()`, `-()`, and `not ()` are errors.",
        },
        new()
        {
            Id = "order-rejects-non-numeric",
            Category = "errors",
            Source = "order((1, 'hello'))",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Probes =
            [
                new SpecProbe("order(((1, 2), (3, 4)))", "err type"),
            ],
            Explanation = "`order` requires each item to be a single numeric value; strings and sequence-value items are elements of the wrong kind (TypeMismatch).",
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
            Id = "invoking-slot-without-callable-is-not-an-algorithm",
            Category = "errors",
            Source = "map([1, 2], 5)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "notAnAlgorithm",
            Probes =
            [
                // Decided by CALLABLE projection only: the value is never demanded.
                new SpecProbe("map([1, 2], 1 / 0)", "err notAnAlgorithm"),
                new SpecProbe("filter([1], true)", "err notAnAlgorithm"),
                new SpecProbe("reduce([1, 2], 5, 0)", "err notAnAlgorithm"),
                new SpecProbe("count(filter([1, 2], 5))", "err notAnAlgorithm"),
                new SpecProbe("[1, 2].map(5)", "err notAnAlgorithm"),
                new SpecProbe("repeat(5, 1, 0)", "err notAnAlgorithm"),
                new SpecProbe("while(true, 0)", "err notAnAlgorithm"),
                new SpecProbe("repeat(map, 1, [1, 2], 5)", "err notAnAlgorithm"),
                new SpecProbe("Through(xs, f) = map(xs, f)\nThrough([1], 5)", "err notAnAlgorithm"),
                new SpecProbe("App(f, x) = f(x)\nApp(5, 1)", "err notAnAlgorithm"),
                // A slot that is never invoked is never projected.
                new SpecProbe("map([], 5)", "ok raw=L[] n=1"),
                new SpecProbe("reduce([], 5, 7)", "ok raw=7 n=1"),
                new SpecProbe("repeat(5, 0, 1)", "ok raw=1 n=1"),
            ],
            Notes = "Q-06, decided 2026-10-05: missing CALLABLE capability is NotAnAlgorithm in every invoking position (formerly a hand-written ArityMismatch(0, k) for builtin slots).",
            Explanation = "A position that INVOKES its argument — the `map` transform, the `filter` predicate, the `reduce` reducer, a `while` or `repeat` step, a user higher-order parameter — needs a callable. A value has no callable identity, so the first invocation that needs one reports NotAnAlgorithm, decided by CALLABLE projection alone: the value is never demanded (`map([1, 2], 1 / 0)` is not a division by zero), and a slot that is never invoked is never projected (`map([], 5)` is `[]`).",
        },
        new()
        {
            Id = "zero-parameter-callable-in-invoking-slot-is-arity",
            Category = "errors",
            Source = "A = 7\nmap([1, 2], A)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                new SpecProbe("map([1, 2], { 5 })", "err arity"),
                new SpecProbe("Lib = { public V = 5 }\nmap([1], Lib.V)", "err arity"),
                new SpecProbe("map([1], Math.Pi)", "err arity"),
                new SpecProbe("Z = 5\nrepeat(Z, 1, 0)", "err arity"),
                new SpecProbe("A = 7\nApp(f, x) = f(x)\nApp(A, 1)", "err arity"),
                new SpecProbe("map([1, 2], take)", "err arity"),
                // Supply cardinality stays arity for every binder, a clause family included.
                new SpecProbe("F(0) = 0\nF(n) = n\nF(1, 2)", "err arity"),
                // The contrast: the plain value has no callable identity.
                new SpecProbe("map([1, 2], 7)", "err notAnAlgorithm"),
            ],
            Explanation = "A zero-parameter callable — a property, a block, a member, a Math constant — HAS callable identity, so an invoking slot invokes it, and the supplied item does not fit its interface: ArityMismatch, exactly as any call that supplies more arguments than the callable accepts. The plain value `7` in the same slot has no callable identity and is NotAnAlgorithm instead.",
        },
        new()
        {
            Id = "kind-errors-are-type-mismatch",
            Category = "errors",
            Source = "-()",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Probes =
            [
                new SpecProbe("-[1]", "err type"),
                new SpecProbe("-'a'", "err type"),
                new SpecProbe("sqrt((4, 9))", "err type"),
                new SpecProbe("A = 1, 2\nA:[0]", "err type"),
                new SpecProbe("range([1], 3)", "err type"),
                new SpecProbe("repeat({ x }, [1], 0)", "err type"),
                new SpecProbe("sum((1, true))", "err type"),
                new SpecProbe("order((3, [1]))", "err type"),
                new SpecProbe("take([1, 2], 'x')", "err type"),
                new SpecProbe("skip([1, 2], ())", "err type"),
                // A number of the accepted kind outside the control's domain is not a kind error.
                new SpecProbe("take([1, 2], 1.5)", "err illegalInEval"),
            ],
            Notes = "Q-27, decided 2026-10-05: kind failures that passed through the numeric conversion, the collection-element check or the whole-number control were formerly reported as arity.",
            Explanation = "A present value of a kind the operation does not accept is TypeMismatch, whatever its shape: a Boolean, a string, a sequence (`()` included) or a list where a number is required — the operand of unary `-`, a Math argument, a selector, a `range` bound, a `repeat` count, a `take`/`skip` count, a numeric collection element. A number of the right kind that the operation cannot use, such as the fractional count `1.5`, is a domain failure instead (IllegalInEval).",
        },
        new()
        {
            Id = "first-last-empty-is-bad-index",
            Category = "errors",
            Source = "first(())",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "index",
            Probes =
            [
                new SpecProbe("first([])", "err index"),
                new SpecProbe("last(())", "err index"),
                new SpecProbe("last([])", "err index"),
                new SpecProbe("().first", "err index"),
                new SpecProbe("[].last", "err index"),
                new SpecProbe("E = ()\nlast(E)", "err index"),
                new SpecProbe("A = (), 1\nfirst(A:0)", "err index"),
                new SpecProbe("first(filter([1, 2], { x > 5 }))", "err index"),
                new SpecProbe("():0", "err index"),
                new SpecProbe("[]:(count([]) - 1)", "err index"),
                new SpecProbe("first((1, 2)), (1, 2):0, last([3, 4]), [3, 4]:1", "ok raw=S[1, 1, 4, 4] n=4"),
            ],
            Notes = "Q-27 / SEQ-04, decided 2026-10-05 (P2): `first`/`last` on an empty collection were formerly the collection's arity rejection.",
            Explanation = "`first(A)` is the selection `A:0` and `last(A)` is `A:(count(A) - 1)`, errors included: an empty collection names no position to select, so `first(())` and `last([])` report BadIndex exactly as `():0` does. BadIndex means a selection named no position, never merely that a container is empty.",
        },
        new()
        {
            Id = "aggregate-empty-is-domain-error",
            Category = "errors",
            Source = "min(())",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "illegalInEval",
            Probes =
            [
                new SpecProbe("max([])", "err illegalInEval"),
                new SpecProbe("avg([])", "err illegalInEval"),
                new SpecProbe("avg(())", "err illegalInEval"),
                new SpecProbe("min(filter([1], { x > 5 }))", "err illegalInEval"),
                new SpecProbe("sum(())", "ok raw=0 n=1"),
                new SpecProbe("count([])", "ok raw=0 n=1"),
            ],
            Notes = "Q-27, decided 2026-10-05: empty `min`/`max`/`avg` were formerly the collection's arity rejection.",
            Explanation = "`min`, `max` and `avg` select no position: an empty collection is outside their domain (IllegalInEval) — not a selection error, and not an arity error, since the argument count is right. `sum` and `count` accept an empty collection.",
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
            ExpectedDisplay = "true",
            ExpectedRaw = "true",
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
            Explanation = "`[1, 2, 3]` is a list value: one value whose elements are stored exactly, displayed with brackets.",
        },
        new()
        {
            Id = "list-exactness",
            Category = "lists",
            Source = "[7] == 7\n[[1, 2]] == [1, 2]\n[[]] == []",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "false\nfalse\nfalse",
            ExpectedRaw = "S[false, false, false]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                new SpecProbe("[1, 2] == [1, 2]", "ok raw=true n=1"),
                new SpecProbe("[[1], [2, 3]] == [[1], [2, 3]]", "ok raw=true n=1"),
                new SpecProbe("[1, [2]] == [1, 2]", "ok raw=false n=1"),
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
            ExpectedDisplay = "false\nfalse",
            ExpectedRaw = "S[false, false]",
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
                new SpecProbe("((1, 2, 3):1) == ([1, 2, 3]:1)", "ok raw=true n=1"),
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
                new SpecProbe("[[1, 2]]:0 == [1, 2]", "ok raw=true n=1"),
                new SpecProbe("[[1, 2]]:0 == (1, 2)", "ok raw=false n=1"),
                new SpecProbe("[(1, 2), (3, 4)]:0", "ok raw=S[1, 2] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A selected list element is returned exactly as stored — one opaque list, never flattened or converted — and a selected sequence element is likewise one intact value; chaining `:` selects one level at a time.",
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
            ExpectedDisplay = "true",
            ExpectedRaw = "true",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("(([1]))", "ok raw=L[1] n=1"),
            ],
            Explanation = "Ordinary parentheses stay a redundant sequence grouping even around lists: `([1, 2])` normalizes to the exact list itself.",
        },
        new()
        {
            Id = "list-spread-capture",
            Category = "lists",
            Source = "A = [1, 2, 3]\n\nx = A\ny = (A*)\n\nx\ny",
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
            Source = "A = []\nB = [7]\nC = [[7]]\n\nA*,\nB*,\nC*",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "7\n[7]",
            ExpectedRaw = "S[7, L[7]]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                new SpecProbe("A = []\nx = (A*)\nx", "ok raw=S[] n=1"),
            ],
            Explanation = "Spread opens ONE boundary: `[]*` supplies zero items (the row vanishes), `[7]*` supplies `7`, and `[[7]]*` supplies the inner list `[7]` intact. Each spread row that is followed by another row ends with a comma: a line-final `*` directly before an operand on the next line would be multiplication (SYN-07B).",
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
            Id = "list-written-slot-reifies-selection",
            Category = "lists",
            Source = "S = ((1, 2), (3, 4))\n\n[S:0, 5]\n[S:0*, 5]",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[(1, 2), 5]\n[1, 2, 5]",
            ExpectedRaw = "S[L[S[1, 2], 5], L[1, 2, 5]]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                new SpecProbe("S = ((1, 2), (3, 4))\nz = (S:0, 5)\nz", "ok raw=S[S[1, 2], 5] n=1"),
                new SpecProbe("S = ((1, 2), (3, 4))\nF((x, y)) = if(x == (1, 2), 1, 0) + y\nF((S:0, 5))", "ok raw=6 n=1"),
                new SpecProbe("S = ((1, 2), (3, 4))\nF((x, y, z)) = x + y + z\nF((S:0*, 5))", "ok raw=8 n=1"),
            ],
            Explanation = "A non-spread expression occupying one written slot contributes exactly ONE persistent value: the selection `S:0` is the pair `(1, 2)` as a list element, exactly as at a capture, a call argument, and every other receiver. Only an explicit spread `S:0*` opens the selected value into the surrounding slots.",
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
                new SpecProbe("x, y, z = ([1, 2, 3]*)\nx, y, z", "ok raw=S[1, 2, 3] n=3"),
                new SpecProbe("A = [1, 2, 3]\nx, y, z = A\nx, y, z", "ok raw=S[1, 2, 3] n=3"),
                new SpecProbe("A = [[1, 2]]\nx, *xs = A\ny, *ys = (A*)\nx, xs, y, ys", "ok raw=S[L[1, 2], L[], 1, L[2]] n=4"),
                new SpecProbe("A = []\n*xs = A\n*ys = (A*)\nxs, ys", "ok raw=S[L[], L[]] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A deconstruction whose captured right-hand side is one list value opens the list one level. Here, `= [1, 2, 3]` and `= ([1, 2, 3]*)` present the same three binding items. Empty lists and singleton lists containing an atom or string also present the same items with or without spread-before-capture. A singleton list containing a sequence or list can produce different bindings or an arity outcome: singleton capture after spread removes the outer list, so deconstruction opens its element instead. For `A = [[1, 2]]`, `x, *rest = A` binds `x = [1, 2]`, `rest = []`, while `x, *rest = (A*)` binds `x = 1`, `rest = [2]`.",
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
                new SpecProbe("x, *rest = [1]\nrest == []", "ok raw=true n=1"),
                new SpecProbe("x, *rest = [1]\nrest == ()", "ok raw=false n=1"),
                new SpecProbe("x, *rest = [1, 2]\nrest", "ok raw=L[2] n=1"),
                new SpecProbe("x, *rest = [[1, 2, 3]]\nx", "ok raw=L[1, 2, 3] n=1"),
                new SpecProbe("x, *rest = 1, [2, 3], 4\nrest", "ok raw=L[L[2, 3], 4] n=1"),
                new SpecProbe("x, *rest = (1, [2, 3]*, (4, 5)*)\nrest", "ok raw=L[2, 3, 4, 5] n=1"),
                new SpecProbe("Rows = [[1, 2], [3, 4]]\nfirst, *rest = Rows\nrest", "ok raw=L[L[3, 4]] n=1"),
                new SpecProbe("Rows = [[1, 2], [3, 4]]\nfirst, *rest = Rows\nrest.count", "ok raw=1 n=1"),
                new SpecProbe("skip([1, 2, 3], 1)", "ok raw=L[2, 3] n=1"),
                new SpecProbe("x, *rest = [1, 2, 3]\nrest == skip([1, 2, 3], 1)", "ok raw=true n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A collecting binding COLLECTS the item slots assigned to it into one list: `rest` from `x, *rest = [1, 2, 3]` is `[2, 3]`, the empty segment is `[]`, a singleton segment is `[item]` (a one-row segment of `[[1, 2], [3, 4]]` stays `[[3, 4]]`, count 1), and the result agrees with collection builtins — `rest == skip([1, 2, 3], 1)`.",
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
            Explanation = "A lone collecting binding opens one right-hand-side structure boundary and collects its items as one list; empty and singleton lists remain exact.",
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
                new SpecProbe("contains([1, 2, 3], 2)", "ok raw=true n=1"),
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
            LeanExclusionReason = "Decimal mean: the C# runtime performs Decimal128 division and returns `1.5`; the Lean Int core uses `Int.tdiv` and returns `1` (documented model limitation: the two-tier numeric bullet of src/KatLang/SEMANTIC-ALIGNMENT.md).",
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
                new SpecProbe("0.1 + 0.2 == 0.3", "ok raw=true n=1"),
                // Ordinary arithmetic keeps its IEEE quantum; literals keep the
                // quantum they were written with.
                new SpecProbe("2.50 * 4", "ok raw=10.00 n=1"),
                new SpecProbe("1.50", "ok raw=1.50 n=1"),
            ],
            Explanation = "Numbers are IEEE 754 Decimal128, so decimal fractions are exact (`0.1 + 0.2 == 0.3` is `true`) and ordinary arithmetic exposes the Decimal128-selected result quantum without canonicalizing it: `0.5 + 0.5` displays `1.0`, not `1`. Quantum affects display, not structural numeric equality; formatting never re-rounds the computed value.",
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
            ExpectedDisplay = "true\nfalse\nfalse\nfalse\nfalse",
            ExpectedRaw = "S[true, false, false, false, false]",
            ExpectedEmittedCount = 5,
            LeanExclusionReason = "NaN is a Decimal128 runtime value with no counterpart in the Lean Int numeric model; the equality-vs-ordering split (structural `==` treats NaN as one value, ordering comparisons follow IEEE and are false) is Decimal128-specific by construction.",
            Probes =
            [
                // Structural side: two INDEPENDENTLY computed NaN atoms are one
                // value (a same-property spelling like `N == N` would compare
                // the cached result against itself and never reach the atom
                // rule), so != is false and the collection consumers agree with ==.
                new SpecProbe("N = (-2) ^ 0.5\nN != (-3) ^ 0.5", "ok raw=false n=1"),
                new SpecProbe("N = (-2) ^ 0.5\ncontains((1, N), (-3) ^ 0.5)", "ok raw=true n=1"),
                new SpecProbe("N = (-2) ^ 0.5\ndistinct((N, (-3) ^ 0.5))", "ok raw=L[NaN] n=1"),
                // `order`/`orderDesc` use Decimal128.CompareTo's total preorder (NaN sorts
                // before every other value ascending), a third, deliberate
                // surface distinct from both `==` and the IEEE comparisons.
                new SpecProbe("N = (-2) ^ 0.5\norder((1, N, -1))", "ok raw=L[NaN, -1, 1] n=1"),
                new SpecProbe("N = (-2) ^ 0.5\norderDesc((1, N, -1))", "ok raw=L[1, -1, NaN] n=1"),
                // `min` canonically represents the NaN-propagating min/max
                // family; Decimal128NumericsTests pins `max` independently.
                new SpecProbe("N = (-2) ^ 0.5\nmin((3, N, 1))", "ok raw=NaN n=1"),
                // NaN is a number like any other: numbers have no truth value, so an `if`
                // over it is the value-kind rejection, never a truth test.
                new SpecProbe("N = (-2) ^ 0.5\nif(N, 1, 2)", "err type"),
            ],
            Notes = "`(-2) ^ 0.5` produces NaN through the operator surface alone (a fractional power of a negative base), keeping this case independent of the separately excluded Math-native surface. The equality, `contains`, and `distinct` rows deliberately compare SEPARATELY computed NaN values so each consumer reaches the structural atom rule instead of succeeding through the zero-arg property cache's reference identity.",
            Explanation = "NaN splits by operation: structural `==`/`!=` (also `contains`/`distinct`) treat NaN as ONE value, so two independently computed NaN results compare equal; the ordering operators follow IEEE, so every `<`/`>`/`<=`/`>=` involving NaN is `false`; and `order`/`orderDesc` sort by the total order, where NaN comes before every other value ascending. `min`/`max` propagate NaN. Like every number, NaN is rejected in a Boolean predicate position.",
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
                new SpecProbe("9e6144 * 10 > 9e6144", "ok raw=true n=1"),
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
                new SpecProbe("-0 == 0", "ok raw=true n=1"),
                new SpecProbe("distinct((-0, 0))", "ok raw=L[-0] n=1"),
                // Zero-VALUED divisors keep the Lean-modeled error: signed zero
                // does NOT adopt the IEEE 1/-0 = -Infinity convention.
                new SpecProbe("1 / -0", "err div0"),
            ],
            Notes = "The canonical case keeps the representative signed-zero boundary: construction/display, structural equality (including the hashed `distinct` consumer), and the shared zero-divisor rule. Decimal128NumericsTests retains the denser relational, arithmetic-sign, and Boolean-predicate rejection matrix.",
            Explanation = "`-0` (unary minus on zero — literals are unsigned) is an observable Decimal128 value: it displays with its sign while comparing structurally equal to `0`, and it remains a zero-valued divisor (`1 / -0` is the ordinary division-by-zero error, not `-Infinity`).",
        },
        new()
        {
            Id = "pow-integer-exponent-inexact-accuracy",
            Category = "arithmetic",
            Source = "0.9999999 ^ 10000000",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0.3678794227774694966078669291031613",
            ExpectedRaw = "0.3678794227774694966078669291031613",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "A fractional base and a 34-digit inexact power are outside the Lean Int numeric model: Lean's `intPow` is exact Int arithmetic, while the Decimal128 runtime rounds the exact mathematical power once to 34 significant digits.",
            Probes =
            [
                // One implementation behind the three spellings.
                new SpecProbe("Math.Pow(0.9999999, 10000000)", "ok raw=0.3678794227774694966078669291031613 n=1"),
                new SpecProbe("pow(0.9999999, 10000000)", "ok raw=0.3678794227774694966078669291031613 n=1"),
                // An exact 35-digit power ending in 5 is a rounding tie: to even.
                new SpecProbe("5 ^ 49", "ok raw=17763568394002504646778106689453120 n=1"),
                // A negative exponent rounds once, at the reciprocal.
                new SpecProbe("1.1 ^ -34", "ok raw=0.03914251301220414284805399307112554 n=1"),
            ],
            Notes = "The dense accuracy matrix (independent 90/140-digit references, exact-midpoint and near-midpoint cases, the exactness boundary `2 ^ 112` / `2 ^ 113`, the certification loop) lives in Decimal128NumericsTests.",
            Explanation = "An integer power that does not fit 34 significant digits is the exact mathematical power rounded ONCE to the nearest Decimal128 (ties to even): `0.9999999 ^ 10000000` is correct in every digit, `5 ^ 49` resolves its exact midpoint to even, and a negative exponent rounds once at the reciprocal. `^`, `Math.Pow`, and `pow` share the implementation.",
        },
        new()
        {
            Id = "pow-zero-base-negative-exponent",
            Category = "arithmetic",
            Source = "0 ^ -0.5",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "illegalInEval",
            LeanExclusionReason = "A fractional exponent is outside the Lean Int numeric model. The rule itself — a zero base rejects EVERY negative exponent — is shared: Lean's `negativeIntPow` states it at its only reachable instance (integer exponents, Lean-guarded by `CoreTests/Numerics.lean`; the `integer-division-truncates` probe `0 ^ -1` runs only in C#), while the fractional side is Decimal128-only.",
            Probes =
            [
                // The integer instance is the same error family (shared with Lean).
                new SpecProbe("0 ^ -1", "err illegalInEval"),
                new SpecProbe("0 ^ -2.5", "err illegalInEval"),
                // One implementation behind the three spellings.
                new SpecProbe("Math.Pow(0, -0.5)", "err illegalInEval"),
                new SpecProbe("pow(0, -2.5)", "err illegalInEval"),
                // A signed zero and a computed zero are zero-valued bases too.
                new SpecProbe("(-0) ^ -0.5", "err illegalInEval"),
                new SpecProbe("z = 1 - 1\nz ^ -0.5", "err illegalInEval"),
                // The boundary: non-negative exponents keep their IEEE results.
                new SpecProbe("0 ^ 0", "ok raw=1 n=1"),
                new SpecProbe("0 ^ 1", "ok raw=0 n=1"),
                new SpecProbe("0 ^ 0.5", "ok raw=0 n=1"),
            ],
            Notes = "The rule is the power-side counterpart of the zero-divisor rule (`1 / 0` is an error, never `Infinity`): a negative power of zero is reciprocal-like, so integrality of the exponent is irrelevant. The integer instance has a Lean guard in `CoreTests/Numerics.lean` and a C#-only probe in `integer-division-truncates`; the denser boundary matrix (signed zero, -Infinity exponent, NaN exponent) lives in Decimal128NumericsTests.",
            Explanation = "Raising zero to ANY negative exponent is an evaluation error, whether or not the exponent is an integer: `0 ^ -1`, `0 ^ -0.5`, and `Math.Pow(0, -2.5)` all report `zero cannot be raised to a negative exponent` instead of producing `Infinity`. Zero and positive exponents are unchanged (`0 ^ 0` is `1`, `0 ^ 0.5` is `0`).",
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
                new SpecProbe("G(radians) = [0, 1].map(sin)\nG(0.5) == [sin(0), sin(1)]", "ok raw=true n=1"),
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
            Id = "value-argument-parameter-shadowing",
            Category = "access-boundaries",
            Source = "Inc(x) = x + 1\n\nApply(f) = {\n    Inner(f) = f(2)\n    Inner(5)\n}\n\nApply(Inc)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "notAnAlgorithm",
            Probes =
            [
                // The standalone callee fails identically, so the enclosing parameter name is unobservable.
                new SpecProbe("Inner(f) = f(2)\nInner(5)", "err notAnAlgorithm"),
                // Patterned and item-supply callees take the same rule.
                new SpecProbe("Inc(x) = x + 1\nApply(f) = {\n    Inner(f, (a, b)) = f(2)\n    Inner(5, (1, 2))\n}\nApply(Inc)", "err notAnAlgorithm"),
                new SpecProbe("Inc(x) = x + 1\nApply(f) = {\n    Inner(f, *rest) = f(2)\n    Inner(5, 1)\n}\nApply(Inc)", "err notAnAlgorithm"),
                // A parameter bound per item or per iteration owns its name the same way.
                new SpecProbe("Inc(x) = x + 1\nApply(f) = {\n    Inner(f) = f(2)\n    [5].map(Inner)\n}\nApply(Inc)", "err notAnAlgorithm"),
                new SpecProbe("Inc(x) = x + 1\nApply(f) = {\n    Inner(f) = f(2)\n    repeat(Inner, 1, 5)\n}\nApply(Inc)", "err notAnAlgorithm"),
                // The lexical dot-call fallback and argument forwarding read the same shadowed binding.
                new SpecProbe("Inc(x) = x + 1\nApply(f) = {\n    Inner(f) = 2.f\n    Inner(5)\n}\nApply(Inc)", "err notAnAlgorithm"),
                new SpecProbe("Inc(x) = x + 1\nApply(f) = {\n    Pass(g) = g(1)\n    Inner(f) = Pass(f)\n    Inner(5)\n}\nApply(Inc)", "err notAnAlgorithm"),
                // The mirror direction: an algorithm-bound inner parameter hides the caller's same-named VALUE.
                new SpecProbe("Inc(x) = x + 1\nOuter(f) = {\n    Inner(f) = f + 1\n    Inner(Inc)\n}\nOuter(5)", "err arity"),
            ],
            Explanation = "`Inner`'s parameter `f` is bound to the value `5` at this call, and a value cannot be called. The callable `Inc` that the surrounding `Apply` received under the same name is never consulted: a parameter owns its name on every channel, so the program fails exactly like the standalone `Inner(5)` instead of silently computing `Inc(2)`.",
        },
        new()
        {
            Id = "value-parameter-shadowing-through-nested-scope",
            Category = "access-boundaries",
            Source = "Inc(x) = x + 1\n\nApply(f) = {\n    Inner(f) = {\n        Local(y) = f(y)\n        Local(2)\n    }\n    Inner(5)\n}\n\nApply(Inc)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "notAnAlgorithm",
            Probes =
            [
                // A nested zero-parameter property reads the same shadowed binding.
                new SpecProbe("Inc(x) = x + 1\nApply(f) = {\n    Inner(f) = {\n        Local = f(2)\n        Local\n    }\n    Inner(5)\n}\nApply(Inc)", "err notAnAlgorithm"),
            ],
            Explanation = "Shadowing is lexical and survives nested scopes: `Local` is called inside `Inner`, whose parameter `f` is the value `5`, so `f(y)` is not a call of a callable. `Local`'s own call binds only `y` and cannot bring back the `Inc` that `Apply` holds under the name `f`.",
        },
        new()
        {
            Id = "value-binder-parameter-shadowing",
            Category = "conditionals",
            Source = "Inc(x) = x + 1\n\nApply(f) = {\n    Inner(0) = 0\n    Inner(f) = f(2)\n    Inner(5)\n}\n\nApply(Inc)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "notAnAlgorithm",
            Explanation = "A clause-family binder is bound to the matched argument value, so `f` is `5` inside the selected branch and `f(2)` is not a call of a callable. The binder owns its name exactly like an explicit parameter: the `Inc` that `Apply` received under the same name is not visible in the branch.",
        },
        new()
        {
            Id = "ancestor-callable-visible-without-same-named-parameter",
            Category = "access-boundaries",
            Source = "Inc(x) = x + 1\n\nApply(f) = {\n    Inner(x) = f(x)\n    Inner(5)\n}\n\nApply(Inc)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "6",
            ExpectedRaw = "6",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // Only the callee's OWN parameter names are shadowed; a nested property reads its ancestor's parameter the same way.
                new SpecProbe("Outer(v) = Inner\n  Inner = v + 1\nOuter(7)", "ok raw=8 n=1"),
                // A callback callee that declares no `f` reaches the ancestor's callable too.
                new SpecProbe("Inc(x) = x + 1\nApply(f) = {\n    Inner(x) = f(x)\n    [5].map(Inner)\n}\nApply(Inc)", "ok raw=L[6] n=1"),
            ],
            Explanation = "Shadowing removes only the names the callee itself binds. `Inner` declares `x`, not `f`, so `f` still resolves outward to the callable `Apply` received, and `Inner(5)` computes `Inc(5)`.",
        },
        // ==================== name-resolution ====================
        new()
        {
            Id = "ownership-same-owner-nested-reference-rejected",
            Category = "name-resolution",
            Source = "Outer(v) = {\n    v = 5\n    Inner = v + 1\n    Inner\n}\nOuter(7)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.ParameterPropertyCollision,
            Explanation = "SYN-03 C1: the same-owner collision is a declaration error even when v is referenced only inside Inner.",
        },
        new()
        {
            Id = "ownership-same-owner-later-property-rejected",
            Category = "name-resolution",
            Source = "Outer(v) = {\n    Inner = v + 1\n    v = 5\n    Inner\n}\nOuter(7)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.ParameterPropertyCollision,
            Explanation = "Writing the conflicting property after the nested reference does not change declaration validity.",
        },
        new()
        {
            Id = "ownership-branch-binder-property-collision",
            Category = "name-resolution",
            Source = "F(0) = 0\nF(v) = {\n    v = 5\n    Inner = v + 1\n    Inner\n}\nF(7)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.ParameterPropertyCollision,
            Explanation = "A branch body owns its pattern binders, so a property that body declares cannot have the same name as a binder.",
        },
        new()
        {
            Id = "ownership-lifted-parameter-property-collision",
            Category = "name-resolution",
            Source = "Need(v) = v\nOuter = { v = 5\nInner = v\nNeed + Inner }\nOuter(7)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.ParameterPropertyCollision,
            Explanation = "A property is never forwarded as a parameter, so Need's v is not supplied by Outer's property v: Outer receives a forwarded parameter v, and that parameter conflicts with the same-named property, so the front end rejects the declaration even though v was not in Outer's initially inferred signature.",
        },
        new()
        {
            Id = "forwarded-parameter-leaves-an-opened-reference",
            Category = "name-resolution",
            Source = "Lib = { public v = 99 }\nOuter = {\n    Inner = { open Lib\n        v\n    }\n    Need = v\n    Inner + Need\n}\nOuter(7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "106",
            ExpectedRaw = "106",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // A reference to a PROPERTY keeps it (and its own forwarding) the same way.
                new SpecProbe("v = x + 99\nOuter = { Inner = v\nNeed(v) = v\nInner + Need }\nOuter(2, 7)", "ok raw=108 n=1"),
                new SpecProbe("v = 99\nNeed(v) = v\nOuter = { Inner = v\n  Inner + Need }\nOuter(7)", "ok raw=106 n=1"),
                // An opened name written directly in the forwarding owner stays the opened name.
                new SpecProbe("Lib = { public v = 99 }\nNeed(v) = v\nOuter = {\n    open Lib\n    v + Need\n}\nOuter(7)", "ok raw=106 n=1"),
            ],
            Explanation = "Automatic parameter forwarding must not change what an existing name refers to. Need requires v, and no parameter binding named v is available in Outer, so Outer receives a new forwarded parameter v for Need (7). The v written inside Inner was resolved to the opened Lib.v (99) before forwarding, and a forwarded parameter is never what a written name denotes, so it stays 99: 99 + 7. (Before the Q-04 decision the forwarded parameter captured every same-named reference in Outer, and both terms read 7.)",
        },
        new()
        {
            Id = "forwarded-parameter-names-nothing-in-a-closed-body",
            Category = "name-resolution",
            Source = "Need(v) = v\nOuter = { F(0) = 0\nF(n) = v\nF(1) + Need }\nOuter(7)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.UndeclaredIdentifier,
            Explanation = "A forwarded parameter exists only for the callee that needed it: Outer receives v for Need, but the v written in the closed branch body is resolved by name resolution alone, which finds nothing, so it stays undeclared. (Before the Q-04 decision the forwarded parameter gave it a meaning after the fact.)",
        },
        new()
        {
            Id = "forwarding-reuses-a-captured-ancestor-parameter",
            Category = "name-resolution",
            Source = "A = y + 1\nF(y) = {\n    G = y * 1000 + A\n    H(y) = G\n    H(100)\n}\nF(3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3004",
            ExpectedRaw = "3004",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // Extracting part of an expression into a property keeps every binding: the inlined helper.
                new SpecProbe("F(y) = {\n    G = y * 1000 + (y + 1)\n    H(y) = G\n    H(100)\n}\nF(3)", "ok raw=3004 n=1"),
                // A helper that reuses the enclosing parameter is an ordinary zero-parameter property.
                new SpecProbe("Area = width * height\nReport(width, height) = {\n    Doubled = Area * 2\n    if(width > 1, Doubled, 0)\n}\nReport(3, 4)", "ok raw=24 n=1"),
                // A clause-branch binder is reused like any parameter.
                new SpecProbe("A = n * 10\nF(0) = 0\nF(n) = {\n    G = n * 100 + A\n    H(n) = G\n    H(9)\n}\nF(2)", "ok raw=220 n=1"),
                // A formula under a closed parameter list forwards the captured ancestor parameter too.
                new SpecProbe("A = y + 1\nG = {\n  F(x) = A + 0\n  F(1) + y\n}\nG(10)", "ok raw=21 n=1"),
                // Bare forwarding reuses the same binding by name: F(x) = A supplies A's y from G's y,
                // and F's own x stays unused (it is never renamed to y).
                new SpecProbe("A = y + 1\nG = {\n  F(x) = A\n  F(1) + y\n}\nG(10)", "ok raw=21 n=1"),
                // Explicit shadowing stays intentional.
                new SpecProbe("A = y + 1\nOuter(y) = {\n    Inner(y) = A * 2\n    Inner(10) + y\n}\nOuter(3)", "ok raw=25 n=1"),
                // A genuinely unbound dependency is still forwarded as a new parameter.
                new SpecProbe("A = y + 1\nF = {\n    G = A * 2\n    G\n}\nF(5)", "ok raw=12 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Automatic parameter forwarding must not change what an existing name refers to. G uses A, which needs y, and the y written in G already denotes F's parameter, so forwarding hands A that same binding: G takes no parameter of its own, and G is 3 * 1000 + (3 + 1) whoever reads it — H(100) included, since H's own y is unrelated. Forwarding reuses parameter bindings only (the body's own, or an enclosing owner's parameter or clause binder) and adds a new parameter only when none exists. (Before the Q-04 decision G received its own y, the written y followed it, and the program gave 100101.)",
        },
        new()
        {
            Id = "forwarding-never-supplies-a-property-an-open-or-a-builtin",
            Category = "name-resolution",
            Source = "v = 99\nNeed(v) = v\nOuter = Need + 1\nOuter(7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8",
            ExpectedRaw = "8",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // Parameter names that match prelude builtins remain parameters to forward.
                new SpecProbe("Clamp(x, min, max) = if(x < min, min, if(x > max, max, x))\nSafe = Clamp + 0\nSafe(15, 0, 10)", "ok raw=10 n=1"),
                // ... and a written call of the builtin keeps calling the builtin.
                new SpecProbe("NeedMin(min) = min + 1\nSafe = NeedMin + min((3, 4))\nSafe(10)", "ok raw=14 n=1"),
                // An opened member of the same name is not forwarded either.
                new SpecProbe("Lib = { public v = 99 }\nNeed(v) = v\nOuter = {\n    open Lib\n    Need + 1\n}\nOuter(7)", "ok raw=8 n=1"),
            ],
            Explanation = "Automatic forwarding reuses parameter bindings only; properties, opened names and builtins are not forwarded as parameters. The root property v = 99 does not satisfy Need's parameter v, so Outer still receives its own forwarded parameter v, and Outer(7) is Need(7) + 1. An unrelated property elsewhere can therefore never turn a parameterized formula into a zero-parameter one.",
        },
        new()
        {
            Id = "forwarding-reused-binding-kind-preserves-values",
            Category = "name-resolution",
            Source = """
                Target(tag, *items) = items
                Collected(tag, *items) = {
                    G(q) = [Target]:0
                    G(99)
                }
                Fixed(tag, items) = {
                    G(q) = [Target]:0
                    G(99)
                }
                Head(x, *rest) = x + rest.count
                Partial(x) = {
                    H = [Head]:0
                    [H, H(10, 20)]
                }
                [Collected(0, (1, 2), [3], ()), Fixed(0, [(1, 2), [3], ()]), Partial(4)]
                """,
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[[(1, 2), [3], ()], [[(1, 2), [3], ()]], [4, 6]]",
            ExpectedRaw = "L[L[S[1, 2], L[3], S[]], L[L[S[1, 2], L[3], S[]]], L[4, 6]]",
            ExpectedEmittedCount = 1,
            Explanation = "Automatic parameter forwarding in a formula reuses the enclosing binding's kind. Both closed G(q) formulas reuse tag and items without gaining parameters: a collecting items is re-spread into Target's collector, preserving every structured item, while a fixed items supplies one whole list. Partial reuses x and forwards only rest into H, so H accepts zero arguments: its bare reference reads the empty-rest value under the existing Q-03 rule, while H(10, 20) explicitly supplies two items. (A lone row `G(q) = Target` forwards by name the same way — it reuses tag and items and never renames q — while a bare `H = Head` is a callable alias of Head, its callable — FWD-02.)",
        },
        new()
        {
            Id = "ownership-captured-parameter-beats-outer-property",
            Category = "name-resolution",
            Source = "v = 99\nOuter(v) = {\n    Inner = v + 1\n    Inner\n}\nOuter(7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8",
            ExpectedRaw = "8",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // The root property is not what makes this work: removing it changes nothing.
                new SpecProbe("Outer(v) = {\n    Inner = v + 1\n    Inner\n}\nOuter(7)", "ok raw=8 n=1"),
                // The unnested reference always selected the parameter; the nested one now agrees.
                new SpecProbe("v = 99\nOuter(v) = v + 1\nOuter(7)", "ok raw=8 n=1"),
                // Both references in one body select the same binding.
                new SpecProbe("v = 99\nOuter(v) = {\n    Inner = v + 1\n    Inner + v\n}\nOuter(7)", "ok raw=15 n=1"),
                // The owning scope need not be a child of the root.
                new SpecProbe("Wrapper = {\n    v = 99\n    Outer(v) = {\n        Inner = v + 1\n        Inner\n    }\n    Outer(7)\n}\nWrapper", "ok raw=8 n=1"),
                // Declaration order is not ownership: a property written after the algorithm decides nothing.
                new SpecProbe("Outer(v) = {\n    Inner = v + 1\n    Inner\n}\nv = 99\nOuter(7)", "ok raw=8 n=1"),
                // Depth is irrelevant: every level between the reference and the owner is silent about `v`.
                new SpecProbe("v = 99\nOuter(v) = {\n    Mid = {\n        Inner = v + 1\n        Inner\n    }\n    Mid\n}\nOuter(7)", "ok raw=8 n=1"),
                // A clause-family binder owns its name the same way.
                new SpecProbe("v = 99\nF(0) = 0\nF(v) = {\n    Inner = v + 1\n    Inner\n}\nF(7)", "ok raw=8 n=1"),
                // So do a sequence-value pattern capture and a collecting parameter.
                new SpecProbe("v = 99\nOuter((v, w)) = {\n    Inner = v + 1\n    Inner\n}\nOuter((7, 1))", "ok raw=8 n=1"),
                new SpecProbe("v = 99\nOuter(*v) = {\n    Inner = v.count\n    Inner\n}\nOuter(7, 8)", "ok raw=2 n=1"),
                // The callable view selects the same binding as the value view.
                new SpecProbe("v = 99\nOuter(v) = {\n    Inner = v(1)\n    Inner\n}\nOuter({a + 1})", "ok raw=2 n=1"),
                // A lexical dot receiver reads the parameter, not the outer property.
                new SpecProbe("v = 99\nAdd1(n) = n + 1\nOuter(v) = {\n    Inner = v.Add1\n    Inner\n}\nOuter(7)", "ok raw=8 n=1"),
                // A callback callee and a loop step read the same binding per element and per iteration.
                new SpecProbe("v = 99\nOuter(v) = {\n    Add(n) = n + v\n    [1, 2].map(Add)\n}\nOuter(7)", "ok raw=L[8, 9] n=1"),
                new SpecProbe("v = 99\nOuter(v) = {\n    Step(s) = s + v\n    repeat(Step, 2, 0)\n}\nOuter(7)", "ok raw=14 n=1"),
                new SpecProbe("v = 99\nOuter(v) = repeat({x + v}, 2, 0)\nOuter(7)", "ok raw=14 n=1"),
                // `Inner` is owned by `Outer` because it is written inside Outer's braces: it is not a root
                // property, and it is local-only because it reads Outer's parameter.
                new SpecProbe("Outer(v) = {\n    Inner = v + 1\n    Inner\n}\nOuter(7)\nInner(7)", "err unresolvedImplicitParams"),
                new SpecProbe("Outer(v) = {\n    Inner = v + 1\n    Inner\n}\nOuter.Inner", "err localOnlyProperty"),
                // Indentation is not nesting: written without braces, `Inner` is a ROOT property with its own
                // implicit `v`, callable from the root, and `Outer(v) = Inner` merely forwards its `v` to it.
                new SpecProbe("Outer(v) = Inner\n  Inner = v + 1\nOuter(7)\nInner(7)", "ok raw=S[8, 8] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Name resolution searches outward by owning scope. `Inner` is nested inside `Outer`, which binds the parameter `v`, so the walk stops there; the root property `v = 99` belongs to a farther owner and is never reached. A parameter therefore means the same thing written directly in its algorithm's body and written inside a body nested in it.",
        },
        new()
        {
            Id = "ownership-same-owner-parameter-beats-property",
            Category = "name-resolution",
            Source = "Outer(v) = {\n    v = 5\n    Inner = v + 1\n    Inner + v\n}\nOuter(7)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.ParameterPropertyCollision,
            Explanation = "A property cannot share a name with a completed parameter of the same or an enclosing owner. This is a declaration error before evaluation, regardless of whether the name is referenced directly, from a nested body, or not at all. Rename one declaration.",
        },
        new()
        {
            Id = "ownership-nearer-property-beats-outer-parameter",
            Category = "name-resolution",
            Source = "v = 99\nOuter(v) = {\n    Mid = {\n        v = 5\n        Inner = v + 1\n        Inner\n    }\n    Mid\n}\nOuter(7)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.ParameterPropertyCollision,
            Probes =
            [
                // Removing the intervening property hands the name back to the parameter.
                new SpecProbe("v = 99\nOuter(v) = {\n    Mid = {\n        Inner = v + 1\n        Inner\n    }\n    Mid\n}\nOuter(7)", "ok raw=8 n=1"),
                // Renaming the outer parameter makes the nested property legal.
                new SpecProbe("v = 99\nOuter(q) = {\n    Mid = {\n        v = 5\n        v + 1\n    }\n    Mid\n}\nOuter(7)", "ok raw=6 n=1"),
                // A name no owner declares still resolves to the ancestor property.
                new SpecProbe("v = 99\nOuter(q) = {\n    Inner = v + 1\n    Inner\n}\nOuter(7)", "ok raw=100 n=1"),
            ],
            Explanation = "Mid's property v conflicts with the completed parameter v of enclosing Outer. A nested algorithm does not make this declaration legal; rename the property or parameter. Editor recovery retains the nearer property's identity, but source evaluation is blocked.",
        },
        new()
        {
            Id = "ownership-nearest-enclosing-parameter-wins",
            Category = "name-resolution",
            Source = "v = 99\nOuter(v) = {\n    Mid(v) = {\n        Inner = v + 1\n        Inner\n    }\n    Mid(7)\n}\nOuter(20)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8",
            ExpectedRaw = "8",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // Each candidate binding would give a different answer: 20 gives 21, 99 gives 100.
                new SpecProbe("Outer(v) = {\n    Mid(v) = {\n        Inner = v + 1\n        Inner\n    }\n    Mid(7)\n}\nOuter(20)", "ok raw=8 n=1"),
                new SpecProbe("v = 99\nOuter(v) = {\n    Mid(w) = {\n        Inner = v + 1\n        Inner\n    }\n    Mid(7)\n}\nOuter(20)", "ok raw=21 n=1"),
            ],
            Explanation = "With several enclosing parameters of one name the nearest wins, because the outward walk reaches it first: `Mid`'s `v` is `7`, so `Inner` is `8` — never `Outer`'s `20` and never the root's `99`.",
        },
        new()
        {
            Id = "ownership-parameter-beats-prelude-alias",
            Category = "name-resolution",
            Source = "Outer(pi) = {\n    Inner = pi + 1\n    Inner\n}\nOuter(7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8",
            ExpectedRaw = "8",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // A builtin name binds the same way.
                new SpecProbe("Outer(count) = {\n    Inner = count + 1\n    Inner\n}\nOuter(7)", "ok raw=8 n=1"),
                // The alias is still there for anyone who did not bind the name.
                new SpecProbe("Outer(q) = {\n    Inner = count([1, 2, 3])\n    Inner\n}\nOuter(7)", "ok raw=3 n=1"),
            ],
            Explanation = "The prelude is simply the outermost owner, so any parameter is nearer than a builtin or a `Math` alias of the same name — from a nested body exactly as from the algorithm's own body.",
        },
        new()
        {
            Id = "ownership-parameter-beats-opened-name",
            Category = "name-resolution",
            Source = "Lib = {\n    public v = 99\n}\nOuter(v) = {\n    open Lib\n    Inner = v + 1\n    Inner\n}\nOuter(7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8",
            ExpectedRaw = "8",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // A reference written directly in the opening body always selected the parameter.
                new SpecProbe("Lib = {\n    public v = 99\n}\nOuter(v) = {\n    open Lib\n    v + 1\n}\nOuter(7)", "ok raw=8 n=1"),
                // Without the parameter the opened name resolves normally.
                new SpecProbe("Lib = {\n    public v = 99\n}\nOuter(q) = {\n    open Lib\n    Inner = v + 1\n    Inner\n}\nOuter(7)", "ok raw=100 n=1"),
                // An ancestor-owned property still beats an inner open, unchanged.
                new SpecProbe("Lib = {\n    public v = 99\n}\nOuter = {\n    v = 5\n    Inner = {\n        open Lib\n        v + 1\n    }\n    Inner\n}\nOuter", "ok raw=6 n=1"),
            ],
            Explanation = "`open` is consulted only after the whole owner walk, so an owned parameter beats an opened name exactly as an owned property does — and the nested reference agrees with the one written directly in `Outer`'s body.",
        },
        new()
        {
            Id = "ownership-open-target-parameter-rejected",
            Category = "name-resolution",
            Source = "Lib = {\n    public X = 7\n}\nOther = {\n    public X = 8\n}\nF(Lib) = {\n    open Lib\n    X, Lib.X\n}\nF(Other)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.OpenTargetIsParameter,
            ExpectedParseDiagnosticFragment = "Cannot open 'Lib': 'Lib' refers to a parameter",
            Probes =
            [
                // Ordinary parameter use keeps its meaning: the parameter is the dot receiver.
                new SpecProbe("Other = {\n    public X = 8\n}\nF(Lib) = Lib.X\nF(Other)", "ok raw=8 n=1"),
                // A static open of a declared algorithm is unchanged, bare and qualified alike.
                new SpecProbe("Lib = {\n    public X = 7\n}\nF = {\n    open Lib\n    X\n}\nF", "ok raw=7 n=1"),
                new SpecProbe("Root = {\n    public Sub = {\n        public X = 7\n    }\n}\nF = {\n    open Root.Sub\n    X\n}\nF", "ok raw=7 n=1"),
                // A parameter that merely shares its name with an OPENED member is not this rule:
                // the open target `Lib` is property-owned, and the owned parameter `v` simply
                // beats the opened `v` (ownership-parameter-beats-opened-name).
                new SpecProbe("Lib = {\n    public v = 99\n}\nOuter(v) = {\n    open Lib\n    v + 1\n}\nOuter(7)", "ok raw=8 n=1"),
                // The root is never called: an unresolved root name beside a nested `open` of that
                // name is the root's unresolved input, reported by evaluation — not a parameter
                // that cannot be opened; the nested open reaches its own body's `Q`. (An open whose
                // only candidate is the root's phantom names nothing and is a static
                // UnresolvedOpenTarget since audit #8 — StaticOpenOwnershipTests.)
                new SpecProbe("Q.X\nM = {\n    open Q\n    Q = {\n        public Z = 1\n    }\n    Z\n}\nM", "err unresolvedImplicitParams"),
            ],
            Explanation = "`open` is static, and lexical ownership still applies to its target name. Inside `F` the nearest binding of `Lib` is the parameter `Lib`, so the parameter owns the name; a parameter cannot be opened, and KatLang reports that instead of looking farther outward for the root property `Lib`. Adding or removing that farther declaration changes nothing — `Lib.X` in the same body reads the parameter, and so does `open Lib`.",
        },
        new()
        {
            Id = "ownership-open-target-parameter-without-farther-declaration",
            Category = "name-resolution",
            Source = "Other = {\n    public X = 8\n}\nF(Lib) = {\n    open Lib\n    X\n}\nF(Other)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.OpenTargetIsParameter,
            Explanation = "The same rejection without any farther `Lib`: the verdict depends only on the nearest binding of the target name, never on whether a farther declaration of that name exists.",
        },
        new()
        {
            Id = "ownership-open-qualified-target-parameter-rejected",
            Category = "name-resolution",
            Source = "Root = {\n    public Sub = {\n        public X = 7\n    }\n}\nF(Root) = {\n    open Root.Sub\n    X\n}\nF(Root)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.OpenTargetIsParameter,
            ExpectedParseDiagnosticFragment = "Cannot open 'Root.Sub': its first name 'Root' refers to a parameter",
            Explanation = "A qualified target is decided at its first name: `Root` is owned by the parameter, so `open Root.Sub` is rejected there and is never resolved through the farther root declaration `Root`.",
        },
        new()
        {
            Id = "ownership-open-target-enclosing-parameter-rejected",
            Category = "name-resolution",
            Source = "Lib = {\n    public X = 7\n}\nOuter(Lib) = {\n    Inner = {\n        open Lib\n        X\n    }\n    Inner\n}\nOuter(3)",
            Outcome = SpecOutcome.ParseError,
            ExpectedDiagnosticCode = DiagnosticCode.OpenTargetIsParameter,
            Explanation = "Ownership is inherited by nested bodies: `Inner`'s `open Lib` names the parameter `Lib` of the enclosing `Outer`, exactly as a reference to `Lib` written in `Inner` would, so it is rejected the same way.",
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
                // conditional value-access failure surfaces — here through a parameter bound on
                // the callable channel, which nothing lifts.
                new SpecProbe("C(0) = 1\nC(n) = 2\nF(g) = Math.Abs(g)\nF(C)", "err branch"),
                // A builtin argument reports the builtin's own arity failure.
                new SpecProbe("F(g) = Math.Abs(g)\nF(count)", "err arity"),
                // Written directly as the Math argument, a family or a builtin is a value position
                // an inferring root lifts (`C(n)`, `count(collection)`), like every callable.
                new SpecProbe("C(0) = 1\nC(n) = 2\nMath.Abs(C)", "err unresolvedImplicitParams"),
                new SpecProbe("Math.Abs(count)", "err unresolvedImplicitParams"),
                // Where the reference's parameters CAN be inferred, the math argument is an
                // ordinary value position and the program simply works.
                new SpecProbe("A = q + 1\nF(q) = Math.Abs(A)\nF(7)", "ok raw=8 n=1"),
                new SpecProbe("A = q + 1\nF = (Math.Abs)(A)\nF(7)", "ok raw=8 n=1"),
                new SpecProbe("F = (Math.Abs)(A)\nA = B + 1\nB = q\nF(7)", "ok raw=8 n=1"),
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
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            // A closed list does not gain q. Missing supply is rejected only when demanded.
            Probes =
            [
                // Declaring the required parameter, or leaving the list open so it is
                // inferred, keeps the program legal.
                new SpecProbe("A = q + 1\nF(q) = Math.Abs(A)\nF(7)", "ok raw=8 n=1"),
                new SpecProbe("A = q + 1\nF = Math.Abs(A)\nF(7)", "ok raw=8 n=1"),
                // A bare reference is not a value demand, and an ordinary call's arguments
                // stay higher-order: neither forces A before invocation.
                new SpecProbe("A = q + 1\nApply(f) = f(10)\nF(x) = Apply(A)\nF(7)", "ok raw=11 n=1"),
                new SpecProbe("F(x) = [0 - 1, 0 - 2].map(abs).sum\nF(9)", "ok raw=3 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            LeanExclusionReason = "Math.Abs executes the unmodeled native Math surface; the pure-core demand counterpart is need-closed-core-demand-is-runtime.",
            Explanation = "An explicit parameter list is closed. `F(x)` gains no implicit `q`, but referencing the resolved callable `A` is legal. When `Math.Abs` actually demands its value, the ordinary zero-argument call to `A(q)` rejects with arity mismatch. An unused argument or unselected branch does not demand it. Declaring `q`, calling `A` explicitly, or leaving the list open enables forwarding. Undeclared names remain static errors.",
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
            Source = "A = x + 1\nF(0) = A + 0\nF(n) = n\n\nF(0)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // A binder the pattern DOES bind supplies the referenced callable's implicit
                // parameter in a formula, without the body acquiring a parameter of its own.
                new SpecProbe("A = n + 1\nF(0) = 0\nF(n) = A + 0\nF(4)", "ok raw=5 n=1"),
                // The same formula behind a closed explicit list fails the same way.
                new SpecProbe("A = x + 1\nF(k) = A + 0\nF(0)", "err arity"),
                // A LONE row is bare forwarding by name from the branch pattern or the list.
                new SpecProbe("A = n + 1\nF(0) = 0\nF(n) = A\nF(4)", "ok raw=5 n=1"),
                new SpecProbe("A = k + 1\nF(k) = A\nF(0)", "ok raw=1 n=1"),
            ],
            Explanation = "A conditional branch pattern is a closed input specification, like a written explicit parameter list: the branch body's only inputs are its pattern binders, and the front end never invents a body parameter to feed a referenced callable. In a formula `F(0) = A + 0` therefore keeps `A` as a bare reference whose zero-argument value demand fails with the ordinary arity error, exactly as `F(k) = A + 0` does — never with an `Unknown name` for a parameter nothing binds. A body that is ONLY the callee is bare forwarding (FWD-02): it reuses a binder of the branch's own pattern by name (`F(n) = A` with `A = n + 1` is `F(n) = A(n)`), and a pattern that binds no such name — `F(0) = A` with `A = x + 1` — is rejected at the front end instead of renaming anything.",
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
                // it is the helper's own implicit parameter, never the branch binder ...
                new SpecProbe("F(0) = 0\nF(n) = {\n  open {\n    public Helper = n\n  }\n  Helper(n + 1)\n}\nF(5)", "ok raw=6 n=1"),
                // ... so a lone row naming the helper is bare forwarding, which supplies that
                // parameter from the branch binder of the same name — exactly as through the named
                // open.
                new SpecProbe("F(0) = 0\nF(n) = {\n  open {\n    public Helper = n\n  }\n  Helper\n}\nF(5)", "ok raw=5 n=1"),
                new SpecProbe("Helpers = {\n  public Helper = n\n}\nF(0) = 0\nF(n) = {\n  open Helpers\n  Helper\n}\nF(5)", "ok raw=5 n=1"),
                // Outside the branch the name resolves to nothing: the enclosing algorithm treats
                // it as its own implicit parameter.
                new SpecProbe("Outer = {\n  F(0) = {\n    open { public Helper = 5 }\n    1\n  }\n  F(n) = n\n  F(0), Helper\n}\nOuter(7)", "ok raw=S[1, 7] n=1"),
                // ...and that parameter is then an OWNED declaration of an enclosing scope, so
                // inside the branch it decides the name ahead of the branch's own open — the same
                // precedence an enclosing property has over an inner open.
                new SpecProbe("Outer = {\n  F(0) = {\n    open { public Helper = 5 }\n    Helper\n  }\n  F(n) = n\n  F(0), Helper\n}\nOuter(7)", "ok raw=S[7, 7] n=1"),
                new SpecProbe("Outer = {\n  Helper = 9\n  F(0) = {\n    open { public Helper = 5 }\n    Helper\n  }\n  F(n) = n\n  F(0)\n}\nOuter", "ok raw=9 n=1"),
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
            Id = "conditional-branch-inline-open-does-not-shadow-an-enclosing-open-in-sibling-branches",
            Category = "conditionals",
            Source = "open Lib\nLib = {\n  public Helper = 7\n}\nF(0) = {\n  open {\n    public Helper = 5\n  }\n  Helper\n}\nF(1) = Helper\nF(n) = n\n\nF(0), F(1), F(2)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5\n7\n2",
            ExpectedRaw = "S[5, 7, 2]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // Clause order decides nothing about open resolution.
                new SpecProbe("open Lib\nLib = {\n  public Helper = 7\n}\nF(1) = Helper\nF(0) = {\n  open {\n    public Helper = 5\n  }\n  Helper\n}\nF(n) = n\n\nF(0), F(1), F(2)", "ok raw=S[5, 7, 2] n=3"),
                // A branch-local named target is resolved from its own branch, even for a single literal clause.
                new SpecProbe("open Lib\nLib = {\n  public Y = 9\n}\nF(0) = {\n  open L\n  L = {\n    public H = 1\n  }\n  Y\n}\n\nF(0)", "ok raw=9 n=1"),
            ],
            Notes = "Constitution PV-24 (September 2026): Lean's `Algorithm.elaborateClauseGroup` copied branch 0's opens onto the family, whose scope is the parent level of every selected branch, so through that helper this program gave `5, 5, 2` (and `5, 7, 2` with the clauses swapped), and the branch-local `open L` failed. C# builds the family with no opens, and Lean now does too; this case's program is derived from the C# elaboration and evaluated by Lean, and `CoreTests/Conditionals.lean` pins the helper on the same programs.",
            Explanation = "An open written in one clause provides its names to that branch body and its nested scopes only. The sibling branch `F(1) = Helper` never sees branch 0's inline open, so its `Helper` is the one the enclosing `open Lib` provides — in whatever order the clauses are written.",
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
                // parameter-capturing member — which means local-context-dependent, not hidden:
                // `G` lies inside the branch that binds `n`, so `open Lib` provides it there.
                new SpecProbe("F(0) = 0\nF(n) = {\n  Lib = { public X = n }\n  G = {\n    open Lib\n    X\n  }\n  G\n}\nF(5)", "ok raw=5 n=1"),
                // Outside that branch the same member is refused at the access.
                new SpecProbe("Apply(f) = f.X\nF(0) = 0\nF(n) = {\n  Lib = { public X = n }\n  Apply(Lib)\n}\nF(5)", "err localOnlyProperty"),
                // By name, nothing declared in a branch is reachable from outside the family.
                new SpecProbe("F(0) = {\n  Lib = { public X = 1 }\n  Lib.X\n}\nF(n) = n\nF.Lib", "err localOnlyProperty"),
                new SpecProbe("Outer = {\n  F(0) = {\n    Lib = { public X = 1 }\n    G = {\n      open Lib\n      X\n    }\n    G\n  }\n  F(n) = n\n  F(0)\n}\nOuter", "ok raw=1 n=1"),
                // A same-named implicit parameter of the ENCLOSING algorithm is an owned
                // declaration of a scope the branch is nested in, so it decides `X` inside `G`
                // ahead of `G`'s own open — exactly as an enclosing property would.
                // The library is outside the parameter's owner; declaring its X inside
                // Outer would now be a parameter/property declaration error.
                new SpecProbe("Lib = { public X = 1 }\nOuter = {\n  F(0) = {\n    G = {\n      open Lib\n      X\n    }\n    G\n  }\n  F(n) = n\n  F(0), X\n}\nOuter(7)", "ok raw=S[7, 7] n=1"),
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
        // ============ SYN-05: builtins are ordinary prelude bindings ============
        new()
        {
            Id = "builtin-callable-is-an-ordinary-prelude-binding",
            Category = "name-resolution",
            Source = "if(x) = x + 1\n\nif(7)\n7.if\nif((7)*)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8\n8\n8",
            ExpectedRaw = "S[8, 8, 8]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // The same rule for every other builtin name — `if` is not special.
                new SpecProbe("count(x) = x + 1\ncount(7)", "ok raw=8 n=1"),
                new SpecProbe("sum(x) = x + 100\nsum(5)", "ok raw=105 n=1"),
                // A parameter is a binding too, so it shadows the prelude the same way.
                new SpecProbe("Apply(if, x) = if(x)\nInc(x) = x + 1\nApply(Inc, 7)", "ok raw=8 n=1"),
                new SpecProbe("F(count) = count + 1\nF(4)", "ok raw=5 n=1"),
                // Nothing nearer: the same spellings resolve the builtin.
                new SpecProbe("if(true, 10, 20)", "ok raw=10 n=1"),
                new SpecProbe("count((1, 2, 3))", "ok raw=3 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Builtin callables live at the prelude level of ordinary name resolution, so any nearer binding — a property or a parameter — shadows one completely. `if` is no different from `count` or `sum`: the three spellings here all select the user's `if`, because lexical resolution picks the binding and only then does the resolved callable decide the semantics.",
        },
        new()
        {
            Id = "no-arity-based-callable-selection",
            Category = "name-resolution",
            Source = "if(x) = x + 1\n\nif(true, 2, 3)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // A user `if` of the builtin's own arity still wins: 31 is the user's sum,
                // 10 would be the builtin's selected branch.
                new SpecProbe("if(a, b, c) = a + b + c\nif(1, 10, 20)", "ok raw=31 n=1"),
                new SpecProbe("if(a, b, c) = a + b + c\n1.if(10, 20)", "ok raw=31 n=1"),
                // The same for another builtin.
                new SpecProbe("count(x) = x + 1\ncount(1, 2)", "err arity"),
                // And with nothing shadowing it, the builtin's own arity applies.
                new SpecProbe("if(true, 2)", "err arity"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "KatLang never overloads by argument count. Lexical resolution selects exactly one callable, the argument supply is assembled, and only then is that callable's signature validated — so a user `if(x)` shadows builtin `if` COMPLETELY and a three-argument call fails against `if(x)` instead of falling back to the builtin.",
        },
        new()
        {
            Id = "if-composition-forms-agree",
            Category = "conditionals",
            Source = "Cond = true\nBranches = (10, 20)\nApply3(f, a, b, c) = f(a, b, c)\n\nif(Cond, 10, 20)\nCond.if(10, 20)\nif(Cond, Branches*)\nCond.if(Branches*)\nApply3(if, Cond, 10, 20)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "10\n10\n10\n10\n10",
            ExpectedRaw = "S[10, 10, 10, 10, 10]",
            ExpectedEmittedCount = 5,
            IncludeInGeneratorPrompt = true,
            Explanation = "Builtin `if` composes through the ordinary callable rules and nothing else: a dot-call injects the receiver as the leading argument, a spread supplies argument slots, and a higher-order parameter carries the resolved callable. All five spellings assemble the same three-argument supply, so they select the same branch.",
        },
        new()
        {
            Id = "if-arity-is-uniform-across-spellings",
            Category = "conditionals",
            Source = "if(true, 2)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // Every spelling that assembles other than three arguments fails alike,
                // at the same boundary, against the same resolved signature.
                new SpecProbe("if()", "err arity"),
                new SpecProbe("if(1)", "err arity"),
                new SpecProbe("if(true, 2, 3, 4)", "err arity"),
                new SpecProbe("if((1, 2)*)", "err arity"),
                new SpecProbe("if((1, 2, 3, 4)*)", "err arity"),
                new SpecProbe("true.if(2)", "err arity"),
                new SpecProbe("true.if(2, 3, 4)", "err arity"),
                new SpecProbe("Apply2(f, a, b) = f(a, b)\nApply2(if, 1, 2)", "err arity"),
                // ...and every spelling that assembles exactly three succeeds.
                new SpecProbe("if((true, 10, 20)*)", "ok raw=10 n=1"),
                new SpecProbe("if(true, (10, 20)*)", "ok raw=10 n=1"),
                new SpecProbe("true.if((10, 20)*)", "ok raw=10 n=1"),
            ],
            Explanation = "`if(condition, whenTrue, whenFalse)` is one fixed signature checked once, after receiver injection and spread expansion have produced the argument supply. A wrong count is therefore an ordinary evaluation-time arity mismatch, identical whichever spelling built the supply — never a rule attached to how the call was written.",
        },
        new()
        {
            Id = "if-laziness-follows-the-resolved-identity",
            Category = "conditionals",
            Source = "Boom = 1 / 0\n\nif(true, 10, Boom)\nfalse.if(Boom, 20)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "10\n20",
            ExpectedRaw = "S[10, 20]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // The wrapper can retain a failed value's algorithm binding; builtin if
                // leaves that binding unused (success does not prove no eager attempt).
                new SpecProbe("Boom = 1 / 0\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, true, 10, Boom)", "ok raw=10 n=1"),
                // The builtin still demands the selected binding.
                new SpecProbe("Boom = 1 / 0\nApply3(f, a, b, c) = f(a, b, c)\nApply3(if, true, Boom, 20)", "err div0"),
                // Shadow the builtin and the laziness goes with it: an ordinary user call
                // binds every argument eagerly.
                new SpecProbe("if(a, b, c) = b + c\nBoom = 1 / 0\nif(true, 10, Boom)", "err div0"),
                // Spread is NOT laziness: building the value evaluates its rows before any
                // argument slot exists, exactly as it does for a user-defined callable.
                new SpecProbe("Risky = (10, 1 / 0)\nif(true, Risky*)", "err div0"),
                new SpecProbe("Risky = (10, 1 / 0)\nMyIf(a, b, c) = if(a, b, c)\nMyIf(true, Risky*)", "err div0"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "The one intrinsic thing about `if` is its invocation: evaluate the condition, then only the selected branch. That belongs to the resolved builtin — shadow the name and the selected user callable determines which of the same suspended arguments it demands — and it is not a promise about arguments the CALLER already evaluated, so building a value before spreading it follows the ordinary expression-to-value-to-supply rule.",
        },
        new()
        {
            Id = "lazy-slot-demand-is-the-ordinary-zero-argument-demand",
            Category = "conditionals",
            Source = "Inc(x) = x + 1\nProbe(u) = if(true, Inc, 0)\nProbe(0)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // The false branch and the condition are the same demand.
                new SpecProbe("Inc(x) = x + 1\nProbe(u) = if(false, 0, Inc)\nProbe(0)", "err arity"),
                new SpecProbe("Inc(x) = x + 1\nProbe(u) = if(Inc, 1, 0)\nProbe(0)", "err arity"),
                // An unselected slot is never demanded: laziness is untouched.
                new SpecProbe("Inc(x) = x + 1\nProbe(u) = if(false, Inc, 7)\nProbe(0)", "ok raw=7 n=1"),
                new SpecProbe("Inc(x) = x + 1\nProbe(u) = if(true, 7, Inc)\nProbe(0)", "ok raw=7 n=1"),
                // A zero-parameter algorithm is an ordinary value, even one that captures an enclosing binding.
                new SpecProbe("A = 7\nif(true, A, 0)", "ok raw=7 n=1"),
                new SpecProbe("Outer(v) = { Inner = v + 1\n if(true, Inner, 0) }\nOuter(7)", "ok raw=8 n=1"),
                // The decision is the signature's, not the body's: K never reads x.
                new SpecProbe("K(x) = 5\nProbe(u) = if(true, K, 0)\nProbe(0)", "err arity"),
                // An explicit call is a value; an explicit zero-argument call is the ordinary call arity error.
                new SpecProbe("Inc(x) = x + 1\nif(true, Inc(4), 0)", "ok raw=5 n=1"),
                new SpecProbe("Inc(x) = x + 1\nif(true, Inc(), 0)", "err arity"),
                // An inferred parameter counts exactly like an explicit one.
                new SpecProbe("A = q + 1\nProbe(u) = if(true, A, 0)\nProbe(0)", "err arity"),
                // A COLLECTING parameter requires no supplied argument, so the bare
                // callable and its explicit zero-argument call agree (September 2026).
                new SpecProbe("Collect(*xs) = xs\nif(true, Collect, 0)", "ok raw=L[] n=1"),
                new SpecProbe("Collect(*xs) = xs\nif(true, Collect(), 0)", "ok raw=L[] n=1"),
                // A required fixed parameter beside a collector still needs one value.
                new SpecProbe("Head(x, *rest) = x\nProbe(u) = if(true, Head, 0)\nProbe(0)", "err arity"),
                // A clause family cannot be accessed as a value at all.
                new SpecProbe("F(0) = 10\nF(x) = x + 1\nProbe(u) = if(true, F, 0)\nProbe(0)", "err branch"),
                // A parameter bound only on the callable channel is the same demand.
                new SpecProbe("Inc(x) = x + 1\nApply(g) = if(true, g, 0)\nApply(Inc)", "err arity"),
                // A zero-parameter branch that fails still reports its own failure.
                new SpecProbe("Boom = 1 / 0\nif(true, Boom, 0)", "err div0"),
                // In a formula that infers its parameters every `if` argument is a value position,
                // selected or not, so the reference lifts instead (the unified formula-lifting law).
                new SpecProbe("Inc(x) = x + 1\nG = if(true, Inc, 0)\nG(4)", "ok raw=5 n=1"),
                new SpecProbe("Inc(x) = x + 1\nG = if(false, Inc, 7)\nG(4)", "ok raw=7 n=1"),
                new SpecProbe("Inc(x) = x + 1\nif(true, Inc, 0)", "err unresolvedImplicitParams"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Where nothing forwards to it — here a closed parameter list — the selected branch is demanded exactly like a bare property reference: `Inc` still needs its `x`, so the ordinary zero-argument arity error is reported at the reference and `Inc`'s body is never entered. Only the selected slot is demanded, so a parameterized algorithm in the unselected branch is harmless at run time, and an explicit call (`Inc(4)`) is an ordinary value. In a formula that infers its parameters, every `if` argument is a value position whether or not a run selects it, so the reference lifts instead: `G = if(false, Inc, 7)` is `G(x) = if(false, Inc(x), 7)`, and the root program `if(true, Inc, 0)` needs `x` itself.",
        },
        new()
        {
            Id = "lazy-slot-demand-covers-every-builtin-value-slot",
            Category = "collection-builtins",
            Source = "Inc(x) = x + 1\nStep(s) = s + 1\nProbe(u) = repeat(Step, 1, Inc)\nProbe(0)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // The repeat count and while's initial state are value slots too.
                new SpecProbe("Inc(x) = x + 1\nStep(s) = s + 1\nProbe(u) = repeat(Step, Inc, 0)\nProbe(0)", "err arity"),
                new SpecProbe("Inc(x) = x + 1\nDown(s) = s - 1, s\nProbe(u) = while(Down, Inc)\nProbe(0)", "err arity"),
                // So are the atoms and range arguments.
                new SpecProbe("Inc(x) = x + 1\nProbe(u) = atoms(Inc)\nProbe(0)", "err arity"),
                new SpecProbe("Inc(x) = x + 1\nProbe(u) = range(1, Inc)\nProbe(0)", "err arity"),
                // Zero-parameter controls evaluate as before.
                new SpecProbe("A = 0\nStep(s) = s + 1\nrepeat(Step, 1, A)", "ok raw=1 n=1"),
                new SpecProbe("A = 7\natoms(A)", "ok raw=L[7] n=1"),
                // Callback slots supply arguments and never consult the rule.
                new SpecProbe("Inc(x) = x + 1\nrepeat(Inc, 2, 0)", "ok raw=2 n=1"),
                new SpecProbe("Inc(x) = x + 1\nmap([1, 2], Inc)", "ok raw=L[2, 3] n=1"),
                new SpecProbe("Add(e, a) = e + a\nreduce([1, 2], Add, 0)", "ok raw=3 n=1"),
                // reduce's initial accumulator keeps its dedicated hint, decided from the signature: K never runs.
                new SpecProbe("K(x) = 5\nAdd(e, a) = e + a\nProbe(u) = reduce([1, 2], Add, K)\nProbe(0)", "err arity"),
                // Collection and fixed value controls use the same demand law after binding.
                new SpecProbe("K(x) = 5\nProbe(u) = count(K)\nProbe(0)", "err arity"),
                new SpecProbe("K(x) = 5\nProbe(u) = contains([1], K)\nProbe(0)", "err arity"),
                new SpecProbe("K(x) = 5\nProbe(u) = take([1], K)\nProbe(0)", "err arity"),
                new SpecProbe("K(x) = 5\nProbe(u) = skip([1], K)\nProbe(0)", "err arity"),
                // In a formula that infers its parameters each value slot lifts the reference instead,
                // while a callback slot keeps it (the unified formula-lifting law).
                new SpecProbe("Inc(x) = x + 1\nStep(s) = s + 1\nG = repeat(Step, 1, Inc)\nG(4)", "ok raw=6 n=1"),
                new SpecProbe("Inc(x) = x + 1\nG = count(Inc)\nG(4)", "ok raw=1 n=1"),
                new SpecProbe("Inc(x) = x + 1\nG = map([1, 2], Inc)\nG", "ok raw=L[2, 3] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Every builtin value slot — a loop's initial state, the `repeat` count, `atoms`, `range`, a collection, or a fixed value control — applies the ordinary zero-argument value-demand law to its argument wherever nothing forwards to it, as under a closed parameter list: an algorithm that still needs arguments is rejected at its reference before its body runs, and `reduce` keeps its dedicated initial-accumulator hint. In a formula that infers its parameters the same value slots lift the reference instead (`G = count(Inc)` is `G(x) = count(Inc(x))`). Callback slots (`repeat`/`while` steps, `map`, `filter`, `reduce` steps) supply arguments and are unaffected either way.",
        },
        new()
        {
            Id = "dot-string-receiver-is-a-zero-argument-value-demand",
            Category = "strings",
            Source = "Inc(x) = x + 1\nProbe(u) = Inc.string\nProbe(0)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                new SpecProbe("A = 7\nA.string", "ok raw='7' n=1"),
                new SpecProbe("Inc(x) = x + 1\nInc(4).string", "ok raw='5' n=1"),
                // A navigated parameterized member and a callable-channel parameter receiver are the same demand.
                new SpecProbe("Lib = { Sub(x) = x }\nProbe(u) = Lib.Sub.string\nProbe(0)", "err arity"),
                new SpecProbe("Inc(x) = x + 1\nF(g) = g.string\nF(Inc)", "err arity"),
                // In a formula that infers its parameters the receiver is a value position and lifts.
                new SpecProbe("Inc(x) = x + 1\nS = Inc.string\nS(4)", "ok raw='5' n=1"),
            ],
            Explanation = "`.string` converts its receiver's VALUE. Where nothing forwards to the receiver — here a closed parameter list — it is demanded as a zero-argument value, so a receiver that still needs arguments is the ordinary arity error at the receiver and its body is never entered; `Inc(4).string` converts the call's result. In a formula that infers its parameters the receiver lifts like any operand: `S = Inc.string` is `S(x) = Inc(x).string`.",
        },
        new()
        {
            Id = "zero-argument-demand-follows-actual-call-arity",
            Category = "variadic-calls",
            Source = "Only(*xs) = xs\nOnly",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[]",
            ExpectedRaw = "L[]",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // The explicit zero-argument call agrees with the bare demand.
                new SpecProbe("Only(*xs) = xs\nOnly()", "ok raw=L[] n=1"),
                // Parentheses group syntax: eligibility cannot depend on grouping.
                new SpecProbe("Only(*xs) = xs\n(Only)", "ok raw=L[] n=1"),
                new SpecProbe("Only(*xs) = xs\n((Only))", "ok raw=L[] n=1"),
                // Every value-demand position agrees, and the dotted and plain builtin
                // spellings agree with each other.
                new SpecProbe("Only(*xs) = xs\nif(true, Only, 0)", "ok raw=L[] n=1"),
                new SpecProbe("Only(*xs) = xs\ncount(Only)", "ok raw=0 n=1"),
                new SpecProbe("Only(*xs) = xs\nOnly.count", "ok raw=0 n=1"),
                new SpecProbe("Only(*xs) = xs\n(Only).count", "ok raw=0 n=1"),
                new SpecProbe("Only(*xs) = xs\nsum(Only)", "ok raw=0 n=1"),
                new SpecProbe("Only(*xs) = xs\nV = Only()\nV", "ok raw=L[] n=1"),
                new SpecProbe("Obj = {\n  public M(*xs) = xs\n}\nObj.M", "ok raw=L[] n=1"),
                // A required fixed parameter beside the collector still needs one value,
                // in both spellings.
                new SpecProbe("Head(x, *rest) = x\nHead", "err arity"),
                new SpecProbe("Head(x, *rest) = x\nHead()", "err arity"),
                new SpecProbe("Tail(*rest, z) = z\nTail", "err arity"),
                new SpecProbe("Tail(*rest, z) = z\nTail()", "err arity"),
                // A nested pattern consumes its one supplied slot: even a collector-only
                // pattern, which accepts zero ELEMENTS, requires the one supplied value.
                new SpecProbe("P((x, *rest)) = x\nP", "err arity"),
                new SpecProbe("P((x, *rest)) = x\nP()", "err arity"),
                new SpecProbe("P((*xs)) = xs\nP", "err arity"),
                new SpecProbe("P((*xs)) = xs\nP(())", "ok raw=L[] n=1"),
                new SpecProbe("P([*xs]) = xs\nP", "err arity"),
                // The ALGORITHM channel is untouched: a callback still receives the
                // callable, so each element is collected.
                new SpecProbe("Only(*xs) = xs\nmap((1, 2), Only)", "ok raw=L[L[1], L[2]] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A callable may be read as a zero-argument value exactly when an ordinary call with no arguments can bind it. A collecting parameter requires no supplied argument, so `Only` and `Only()` both collect nothing and give `[]`; `Head(x, *rest)` still requires one supplied value, so both of its zero-argument spellings are the same arity error. Callback positions still receive the callable itself.",
        },
        new()
        {
            Id = "zero-argument-callable-name-is-read-not-lifted",
            Category = "variadic-calls",
            Source = "Cnt(*xs) = xs.count\nPair(*xs) = 10, 20\nAlias = Cnt\nTwice(*items) = Cnt + Cnt\n\nCnt + 1, [Cnt], Cnt == Cnt, Pair:1\nAlias, Alias()\nTwice(1, 2, 3)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1\n[0]\ntrue\n20\n0\n0\n0",
            ExpectedRaw = "S[1, L[0], true, 20, 0, 0, 0]",
            ExpectedEmittedCount = 7,
            Probes =
            [
                // A strict Math argument reads the same value (probes only: Math natives are
                // a documented unmodeled gap in the Lean core, so the Lean-compared program
                // above uses operator, comparison, list, and index positions).
                new SpecProbe("Cnt(*xs) = xs.count\nabs(Cnt), Cnt.abs", "ok raw=S[0, 0] n=2"),
                // The alias is Cnt's callable (a callable alias): it takes arguments like Cnt.
                new SpecProbe("Cnt(*xs) = xs.count\nAlias = Cnt\nAlias(1, 2)", "ok raw=2 n=1"),
                // Forwarding to a callable that works with no arguments is written explicitly.
                new SpecProbe("Cnt(*xs) = xs.count\nAlias(*xs) = Cnt(xs*)\nAlias(1, 2)", "ok raw=2 n=1"),
                new SpecProbe("Cnt(*xs) = xs.count\nTwice(*items) = Cnt(items*) + Cnt(items*)\nTwice(1, 2, 3)", "ok raw=6 n=1"),
                // A callable that REQUIRES an argument still lifts and forwards.
                new SpecProbe("Head(x, *rest) = x\nH = Head + 0\nH(5, 6)", "ok raw=5 n=1"),
                new SpecProbe("Inc(x) = x + 1\nK = Inc * 2\nK(4)", "ok raw=10 n=1"),
                // A closed parameter list never blocks such a read: it needs no argument.
                new SpecProbe("Cnt(*ys) = ys.count\nH(k) = abs(Cnt) + k\nH(5)", "ok raw=5 n=1"),
                // Selection and the builtin first/last read the same value.
                new SpecProbe("Pair(*xs) = 10, 20\nfirst(Pair) == Pair:0, last(Pair) == Pair:1", "ok raw=S[true, true] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "If a callable works with no arguments, using its name alone reads its (cached) value, even if it declares optional or collecting parameters; `A()` evaluates it again. So `Cnt(*xs)` referenced by name inside an expression — as an operand or comparison operand, a list element, a Math argument, an index target, or anywhere in a formula — is never rewritten into a forwarding call: `Twice(*items) = Cnt + Cnt` reads that value twice and ignores its own arguments. A definition whose whole body is the name is a callable alias instead: `Alias = Cnt` names Cnt's callable, so `Alias(1, 2)` is Cnt's call, 2, while `Alias` alone is its own cached value, `0`. Forwarding inside a formula is written explicitly (`Cnt(items*)`). Implicit lifting and forwarding still apply to a callable that requires supplied arguments (`Head(x, *rest)`, `Inc(x)`).",
        },
        new()
        {
            Id = "same-arity-user-if-keeps-user-identity",
            Category = "name-resolution",
            Source = "if(a, b, c) = a + b + c\nif(1, 10, 20)\n1.if(10, 20)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "31\n31",
            ExpectedRaw = "S[31, 31]",
            ExpectedEmittedCount = 2,
            Explanation = "A user callable with the builtin's arity still shadows it: both calls compute the user's sum, never the builtin's selected branch.",
        },
        new()
        {
            Id = "parameter-named-if-carries-the-supplied-callable",
            Category = "name-resolution",
            Source = "Apply(if, x) = { Inner = if(x)\n Inner }\nInc(x) = x + 1\nApply(Inc, 7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "8",
            ExpectedRaw = "8",
            ExpectedEmittedCount = 1,
            Explanation = "A parameter named if owns that name in nested bodies too; its algorithm channel carries the supplied Inc callable.",
        },
        new()
        {
            Id = "if-spread-builds-values-before-branch-selection",
            Category = "conditionals",
            Source = "Risky = (10, 1 / 0)\nif(true, Risky*)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "div0",
            Explanation = "Spread evaluates its operand before supplying argument slots, so the failing row is evaluated before builtin if can select a branch.",
        },
        // ==================== final audit (September 2026) ====================
        new()
        {
            Id = "dot-string-intrinsic-rejects-arguments",
            Category = "strings",
            Source = "A = 42\nA.string(1)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                new SpecProbe("A = 42\nA.string()", "ok raw='42' n=1"),
                new SpecProbe("A = 42\nA.string(1, 2)", "err arity"),
                new SpecProbe("S = 1, 2\nA = 42\nA.string(S*)", "err arity"),
                new SpecProbe("Obj = {\n    5\n}\nObj.string(1)", "err arity"),
            ],
            Explanation = "The `.string` intrinsic is a zero-parameter member. A written argument list is formed exactly like every call's supply (explicit spreads opened, every other slot a suspended computation) and then rejected by its cardinality before any argument or the receiver is demanded — the outcome `Obj.V(1)` has for a declared zero-parameter member — so a written bundle is never silently dropped. An empty written list (`A.string()`) stays the intrinsic, as `A()` stays a call of `A`.",
        },
        new()
        {
            Id = "ownership-open-provided-captured-member-read-by-sibling-is-local-only",
            Category = "access-boundaries",
            Source = "Outer(p) = {\n    open Lib\n    Lib = { public X = p }\n    public Y = X\n    Y\n}\nOuter.Y",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "localOnlyProperty",
            Probes =
            [
                // Inside the owner, with p active, the same read succeeds.
                new SpecProbe("Outer(p) = {\n    open Lib\n    Lib = { public X = p }\n    public Y = X\n    Y\n}\nOuter(4)", "ok raw=4 n=1"),
                // The reader charges the requirement through every value-read spelling.
                new SpecProbe("Outer(p) = {\n    open Lib\n    Lib = { public X = p }\n    public Y = { X }\n    Y\n}\nOuter.Y", "err localOnlyProperty"),
                // An opened member that captures nothing charges nothing.
                new SpecProbe("Outer(p) = {\n    open Lib\n    Lib = { public X = 7 }\n    public Z = X\n    Z + p\n}\nOuter.Z", "ok raw=7 n=1"),
            ],
            Explanation = "An open-provided member that reads a captured ancestor parameter (`X = p`) is local-only, and so is every sibling that reads it: `Y = X` depends on `p` exactly as `Y = p` would, so `Outer.Y` from outside the owner is refused by the one accessibility check while `Outer(4)` reads it with `p` active. The requirement is settled through the same visible-name resolution a direct property reference uses, whatever the read's spelling; an opened member that captures nothing stays exported.",
        },
        new()
        {
            Id = "ownership-open-head-between-opener-and-settling-level-charges-the-capture",
            Category = "access-boundaries",
            Source = "Outer(p) = {\n    Mid = {\n        Lib = { public X = p }\n        Inner = {\n            open Lib\n            X\n        }\n        Inner\n    }\n    Mid\n}\nOuter.Mid",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "localOnlyProperty",
            Probes =
            [
                // Each activation reads its own p: the value is never served from a run cache.
                new SpecProbe("Outer(p) = {\n    Mid = {\n        Lib = { public X = p }\n        Inner = {\n            open Lib\n            X\n        }\n        Inner\n    }\n    Mid\n}\nOuter(1), Outer(2)", "ok raw=S[1, 2] n=2"),
                // The nearest declaration of the head provides: Mid's self-contained Lib, so Mid stays exported.
                new SpecProbe("Outer(p) = {\n    Lib = { public X = p }\n    Mid = {\n        Lib = { public X = 100 }\n        Inner = {\n            open Lib\n            X\n        }\n        Inner\n    }\n    Mid\n}\nOuter.Mid", "ok raw=100 n=1"),
            ],
            Explanation = "An `open` target is resolved from the opener's direct lexical chain outward, so a head declared at a level BETWEEN the opener and the level that settles the exposure is the provider, and the provided member's capture of `p` makes every reader up to that level local-only: `Outer.Mid` from outside the owner is refused, while `Outer(1), Outer(2)` reads each activation's own `p`. The nearest declaration of the head wins, exactly as it does for the evaluator's lookup.",
        },
        new()
        {
            Id = "grace-in-redundant-group-is-grace-on-the-name",
            Category = "name-resolution",
            Source = "V(x) = x * 2\nF = b + (~a).V\nF(5, 1)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "11",
            ExpectedRaw = "11",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // Without the marker the occurrence order `(b, a)` decides.
                new SpecProbe("V(x) = x * 2\nF = b + (a).V\nF(5, 1)", "ok raw=7 n=1"),
                // The group is the name itself whatever the marker: an algorithm-valued
                // argument is navigated for its own member V, exactly as `a.V` navigates it.
                new SpecProbe("Obj = {\n    public V = 7\n    1\n}\nV(x) = x * 2\nF = (~a).V\nF(Obj)", "ok raw=7 n=1"),
                new SpecProbe("Obj = {\n    public V = 7\n    1\n}\nV(x) = x * 2\nF = a.V\nF(Obj)", "ok raw=7 n=1"),
            ],
            Explanation = "Parentheses group syntax, and Grace is a parameter-order annotation that never changes selection: `(~a).V` is `~a.V` — it orders `a` before `b` exactly like `~a` would, and the edge is the ordinary structural-first dot edge on `a`, so a bound algorithm's own `V` is read and a number falls back to the lexical `V(x)`, exactly as `a.V` and `(a).V` do. The marker is stripped before evaluation; it can never change which receiver is navigated.",
        },
        new()
        {
            Id = "open-builtin-target-rejected",
            Category = "name-resolution",
            Source = "open count\nQ = 5\nQ",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "'count' cannot be opened because it is a builtin callable",
            ExpectedDiagnosticCode = DiagnosticCode.IllegalInOpen,
            Notes = "Front-end rejection by the same rule that refuses a parameterized provider (a builtin's arity lives in registry metadata, not in `Params`, so it is refused by kind); both evaluators refuse the target with `illegalInOpen` at open resolution (Lean `resolveAlgForOpen`) as soon as a lookup demands the list. Before the final audit the front end accepted the target and only the editor flagged it.",
            Explanation = "A prelude builtin is not an open provider: `open` imports the members of an algorithm that needs no call, and a builtin callable has no members to import, so `open count` is refused at the target rather than silently accepted. To use a builtin, call it.",
        },
        new()
        {
            Id = "owed-closer-recovery-keeps-later-declarations",
            Category = "parser-layout",
            Source = "F(a) = a\nA = F(1, )\nB = 2\nB",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Unexpected ')'",
            ExpectedDiagnosticCode = DiagnosticCode.UnexpectedToken,
            Notes = "Recovery contract, pinned in `RootStrayCloserRecoveryTests`: the one report is at the `)`, the recovered slot stays inside the call, and `B` is a ROOT declaration. Before the final audit the `)` was consumed as junk, the call stayed open to the end of input, and every later declaration was swallowed into it with cascading reports.",
            Explanation = "A trailing comma before a closing delimiter is a missing operand, reported once at the closer the enclosing construct is waiting for; recovery leaves that closer to its owner, so later declarations stay in the scope they were written in.",
        },
        new()
        {
            Id = "order-is-stable",
            Category = "collection-builtins",
            Source = "order((1.0, 1, 1.00))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[1.0, 1, 1.00]",
            ExpectedRaw = "L[1.0, 1, 1.00]",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Decimal128 quantum and signed zero are outside the Lean Int numeric model: two spellings of one value (`1.0` and `1`, `0` and `-0`) compare equal yet display differently, which is what makes sort stability observable in the runtime; the Lean Int core has one spelling per value, so stability is unobservable there.",
            Probes =
            [
                new SpecProbe("orderDesc((1.0, 1, 1.00))", "ok raw=L[1.00, 1, 1.0] n=1"),
                new SpecProbe("order((0, -0))", "ok raw=L[0, -0] n=1"),
                new SpecProbe("orderDesc((0, -0))", "ok raw=L[-0, 0] n=1"),
                new SpecProbe("order((2, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 0))", "ok raw=L[0, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 1.0, 1, 2] n=1"),
            ],
            Explanation = "`order` is a stable sort: values that compare equal keep their written order, so the spellings `1.0`, `1`, `1.00` come back as written however long the input. `orderDesc` is the reverse of that stable ascending order (Lean `sortIntsDesc`), so equal-comparing values reverse too. The arrangement never depends on the runtime's sort algorithm.",
        },
        new()
        {
            Id = "min-max-signed-zero",
            Category = "collection-builtins",
            Source = "min((0, -0))\nmin((-0, 0))\nmax((0, -0))\nmax((-0, 0))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "-0\n-0\n0\n0",
            ExpectedRaw = "S[-0, -0, 0, 0]",
            ExpectedEmittedCount = 4,
            LeanExclusionReason = "Decimal128 signed zero is outside the Lean Int numeric model: Int has one zero, so Lean's `evalMinCounted`/`evalMaxCounted` return `0` for every program here and the sign-decided tie between `0` and `-0` is unobservable there — the runtime rule agrees with Lean on every Int value.",
            Probes =
            [
                // The tie only chooses between zeros that are present: no sign is manufactured.
                new SpecProbe("max((-0, -0))", "ok raw=-0 n=1"),
                new SpecProbe("min((0, 0))", "ok raw=0 n=1"),
                // It matters only where zero IS the extremum.
                new SpecProbe("min((1, 0, -0))", "ok raw=-0 n=1"),
                new SpecProbe("max((-1, -0, 0))", "ok raw=0 n=1"),
                new SpecProbe("min((-1, -0, 0))", "ok raw=-1 n=1"),
                // Ordinary ordering still treats the two zeros as one value.
                new SpecProbe("-0 < 0", "ok raw=false n=1"),
            ],
            Notes = "C#-only Decimal128 rule owned by IEEE 754 `minimum`/`maximum` (`Decimal128.Min`/`Max`) in `Evaluator.EvalMinCounted`/`EvalMaxCounted`, the one implementation the synchronous dispatch, the async twin, and the planned loop's fallback all reach. Which of several SAME-SIGNED equal values with different quanta is returned (`1` vs `1.0`, `-0` vs `-0.0`) is not part of the rule. `SignedZeroExtremaTests` holds the exhaustive arrangement matrix against an order-free oracle and the route, strategy, and presentation parity.",
            Explanation = "`-0` and `0` are one value to `==` and to the ordering operators (`-0 < 0` is `false`), but `min` and `max` decide a tie between the two zeros by sign, as IEEE 754 `minimum`/`maximum` do: `min` returns `-0` whenever a negative zero takes part in a zero minimum, and `max` returns `0` whenever an ordinary zero takes part in a zero maximum, whatever the element order. The result is always one of the elements, so `max((-0, -0))` stays `-0`, and a nonzero extremum wins as usual. KatLang spells the two zeros `0` and `-0`; there is no unary `+`.",
        },
        new()
        {
            Id = "repeated-name-keeps-first-equally-rich-representative",
            Category = "variadic-calls",
            Source = "P(x, x) = x.string\n\nP(1.5, 1.50)\nP(1.50, 1.5)\nP(0, -0)\nP(-0, 0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "1.5\n1.50\n0\n-0",
            ExpectedRaw = "S['1.5', '1.50', '0', '-0']",
            ExpectedEmittedCount = 4,
            LeanExclusionReason = "Decimal128 quantum and signed zero are outside the Lean Int numeric model: Int has one representation per value, so which of several equal contributions supplies the retained representation is unobservable there. Lean's `bindNeedName` keeps the earlier complete contribution unless a later one is strictly richer — the same rule — so the runtime agrees with Lean on every Int value (Q-28, N-F).",
            Probes =
            [
                // NEED-04 decides first: a richer contribution (VALUE + CALLABLE) wins in either order.
                new SpecProbe("A = 1.50\nP(x, x) = x.string\nP(1.5, A)", "ok raw='1.50' n=1"),
                new SpecProbe("A = 1.50\nP(x, x) = x.string\nP(A, 1.5)", "ok raw='1.50' n=1"),
                // Three occurrences: the first equally rich one.
                new SpecProbe("P3(x, x, x) = x.string\nP3(1.50, 1.5, 1.500)", "ok raw='1.50' n=1"),
                // A clause family's repeated binder keeps the same representative.
                new SpecProbe("E(x, x) = x.string\nE(x, y) = 'diff'\nE(1.5, 1.50)", "ok raw='1.5' n=1"),
                new SpecProbe("E(x, x) = x.string\nE(x, y) = 'diff'\nE(-0, 0)", "ok raw='-0' n=1"),
                // Nested values: the first contribution whole, never a leaf-wise merge of both.
                new SpecProbe("P(x, x) = x\nP((1.0, 2), (1, 2.0))", "ok raw=S[1.0, 2] n=1"),
                // The verdict and the bound value up to == never depend on the order.
                new SpecProbe("P(x, x) = x\nP(1.5, 1.50) == P(1.50, 1.5)", "ok raw=true n=1"),
                new SpecProbe("P(x, x) = x\nP(1.5, 1.6)", "err arity"),
            ],
            Notes = "C#-only Decimal128 rule decided by Q-28 (N-F, 2026-10-07): `==` (Decimal128.Equals at numeric leaves) decides compatibility; the retained contribution is NEED-04's richest, the first in written pattern order among equally rich ones — `Evaluator.BindNeedPatterns` in C#, `bindNeedName` in Lean. `NumericRepresentativeSelectionTests` holds the six-route representation-exact matrix (22 representation pairs, four shapes, five origins, families and callbacks).",
            Explanation = "A repeated name binds ONE complete contribution. `==` decides compatibility — Decimal128 equality ignores the quantum and the zero sign, so `1.5` and `1.50`, `0` and `-0`, bind. NEED-04 keeps the richest compatible contribution (a named property, which carries a callable, outranks a plain value in either order), and among equally rich contributions the FIRST in written pattern order supplies the retained value with its exact representation. `.string` shows that representation, so `P(1.5, 1.50)` is `'1.5'` and `P(1.50, 1.5)` is `'1.50'`; the verdict, the error kind and the value up to `==` never depend on the argument order.",
        },
        new()
        {
            Id = "decimal-literal-patterns-match-by-value",
            Category = "conditionals",
            Source = "F(1.5) = 'hit'\nF(x) = 'miss'\nZ(0) = 'zero'\nZ(x) = 'other'\n\nF(1.50), F(3 / 2), F(1.6)\nZ(-0), Z(0.0)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "hit\nhit\nmiss\nzero\nzero",
            ExpectedRaw = "S['hit', 'hit', 'miss', 'zero', 'zero']",
            ExpectedEmittedCount = 5,
            LeanExclusionReason = "Fractional Decimal128 literals, quantum and signed zero are outside the Lean Int numeric model (LeanAstEncoder refuses fractional numbers by design, and Int has one zero); a Lean numeric literal pattern matches by the same `==`, where every value has one representation (Q-28, X-12).",
            Probes =
            [
                // The binder beside a literal keeps the argument's own representation; the literal binds nothing.
                new SpecProbe("K((1.5, x)) = x.string\nK((y, x)) = 'other'\nK((1.50, 1.50))", "ok raw='1.50' n=1"),
                // A positive exponent and an integral quantum are the same value too.
                new SpecProbe("F(1e3) = 'hit'\nF(x) = 'miss'\nF(1000)", "ok raw='hit' n=1"),
                new SpecProbe("F(1) = 'hit'\nF(x) = 'miss'\nF(0.5 + 0.5)", "ok raw='hit' n=1"),
                // A negative-zero literal matches the ordinary zero as well.
                new SpecProbe("F(-0) = 'hit'\nF(x) = 'miss'\nF(0)", "ok raw='hit' n=1"),
            ],
            Notes = "C#-only Decimal128 instance of PAT-05's value rule, recorded by Q-28 (X-12 resolved 2026-10-07). Equal literals with different representations are ONE clause head (`F(1.5)` beside `F(1.50)` is `DuplicateBranchPattern`), pinned by `NumericRepresentativeSelectionTests.EqualLiterals_AreTheSameClauseHead`.",
            Explanation = "A numeric literal pattern matches every argument that is `==` to it, whatever either representation: `F(1.5)` matches `1.50` and `3 / 2`, and `Z(0)` matches `-0` and `0.0`. The literal binds nothing, so a binder beside it keeps the argument's own representation, and two literals that are `==` are the same clause head.",
        },
        new()
        {
            Id = "display-decimals-rounds-ties-away-from-zero",
            Category = "arithmetic",
            Source = "DisplayDecimals = 2\n0.125, 0.375, -0.125, 2.5",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0.13\n0.38\n-0.13\n2.50",
            ExpectedRaw = "S[0.125, 0.375, -0.125, 2.5]",
            ExpectedEmittedCount = 4,
            LeanExclusionReason = "Fractional Decimal128 literals and the DisplayDecimals presentation option are outside the Lean Int numeric model; LeanAstEncoder refuses fractional numbers by design.",
            Probes =
            [
                new SpecProbe("DisplayDecimals = 0\n0.5, 1.5, 2.5, -0.5", "ok raw=S[0.5, 1.5, 2.5, -0.5] n=4"),
                new SpecProbe("Math.Round(0.125, 2), Math.Round(2.5, 0), Math.Round(-2.5, 0)", "ok raw=S[0.13, 3, -3] n=3"),
            ],
            Explanation = "`DisplayDecimals` presents each numeric leaf rounded to the requested places with midpoints rounded AWAY FROM ZERO — the rule `Math.Round` applies — so `0.125` shows as `0.13` and `-0.125` as `-0.13`. Display never re-rounds the computed value: the raw values keep their digits, only the presentation changes. KatLang owns this rule; it does not follow the host runtime's fixed-point formatter, whose tie rule has changed between releases.",
        },
        new()
        {
            Id = "logarithm-near-one-is-accurate",
            Category = "arithmetic",
            Source = "Math.Ln(1 + 1e-20)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0.00000000000000000000999999999999999999995",
            ExpectedRaw = "0.00000000000000000000999999999999999999995",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Transcendental Math functions and fractional Decimal128 values are outside the Lean Int numeric model; the accuracy class of `Ln`/`Lg`/`Log` and near-1 powers is a runtime (Decimal128Numerics) contract.",
            Probes =
            [
                // ln(1 − ε) = −ε − ε²/2 − …
                new SpecProbe("Math.Ln(1 - 1e-20)", "ok raw=-0.00000000000000000001000000000000000000005 n=1"),
                // A near-1 base with a fractional exponent takes the same reformulation:
                // (1 + 1e-20) ^ 0.5 = 1 + 5e-21 − 1.25e-41 + …, which rounds to 34 significant digits as 1 + 5e-21
                new SpecProbe("(1 + 1e-20) ^ 0.5", "ok raw=1.000000000000000000005 n=1"),
            ],
            Explanation = "Logarithms of arguments near 1 lose digits to cancellation in a naive ln(1 + ε), so the runtime evaluates them through the log1p reformulation: `Math.Ln(1 + 1e-20)` is `1e-20 − 5e-41 + …`, correct to the last digit of its 34 significant digits. `Lg` and `Log` share the reformulation, and a near-1 base raised to a fractional exponent is computed as `exp(y · ln x)` over it.",
        },
        new()
        {
            // Numeric audit #6 (September 2026): `avg` divided the left-to-right
            // Decimal128 sum, so a sum that rounded on the way produced a mean with no
            // correct digits (this source returned `0`), while an OVERFLOWING sum already
            // took the exact mean.
            Id = "avg-is-the-correctly-rounded-exact-mean",
            Category = "collection-builtins",
            Source = "avg((1, 1e34, -1e34))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "0.3333333333333333333333333333333333",
            ExpectedRaw = "0.3333333333333333333333333333333333",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Decimal128 rounding of the running sum and the fractional mean: the Lean Int core adds exactly and truncates the mean with `Int.tdiv`, so neither the 34-digit rounding of `sum` nor the correctly rounded decimal mean has a Lean counterpart.",
            Probes =
            [
                // The left-to-right `sum` rounds `1 + 1e34` back to `1e34`; `avg` is not that sum over the count.
                new SpecProbe("sum((1, 1e34, -1e34)) / 3", "ok raw=0 n=1"),
                // (1e34 + 2) / 3 is exactly 3333333333333333333333333333333334.
                new SpecProbe("avg((1e34, 1, 1))", "ok raw=3333333333333333333333333333333334 n=1"),
                // For finite elements the mean does not depend on their order.
                new SpecProbe("avg((1e34, -1e34, 1)) == avg((1, 1e34, -1e34))", "ok raw=true n=1"),
                // An exact sum keeps the ordinary division and its IEEE quantum.
                new SpecProbe("avg((1.0, 2.00))", "ok raw=1.50 n=1"),
            ],
            Explanation = "`avg` is the exact total of its elements divided by their count, rounded once to 34 significant digits. The left-to-right `sum` can round on the way (`1 + 1e34` is `1e34` again), so the mean is not `sum(x) / count(x)` whenever that sum was inexact: `avg((1, 1e34, -1e34))` is one third, while `sum((1, 1e34, -1e34)) / 3` is `0`. When every addition was exact the two agree, quantum included (`avg((1.0, 2.00))` is `1.50`).",
        },
        new()
        {
            // Numeric audit #6 (September 2026): the near-one power band admitted only
            // positive bases, so a negative base near -1 with an integral exponent beyond
            // `long` took the runtime power, which kept four correct digits here.
            Id = "negative-near-one-base-power-is-sign-symmetric",
            Category = "arithmetic",
            Source = "B = 0.9999999999999999999999999999999999\n(-B) ^ 1e34 == B ^ 1e34",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "true",
            ExpectedRaw = "true",
            ExpectedEmittedCount = 1,
            LeanExclusionReason = "Near-one powers with fractional values and exponents beyond `long` are Decimal128 approximations (the Lean Int core has no fractional power, and `negativeIntPow` rejects every non-unit reciprocal), so the sign-symmetry of the delegated power is a runtime accuracy property.",
            Probes =
            [
                // An odd exponent beyond `long` keeps the magnitude and negates it.
                new SpecProbe("B = 1.0000000000000000001\n(-B) ^ 10000000000000000001 == -(B ^ 10000000000000000001)", "ok raw=true n=1"),
                // Inside `long` the certified integer power was already symmetric.
                new SpecProbe("B = 1.0000000000000000001\n(-B) ^ 9223372036854775807 == -(B ^ 9223372036854775807)", "ok raw=true n=1"),
                // A fractional power of a negative base stays NaN.
                new SpecProbe("(-0.995) ^ 12345.5", "ok raw=NaN n=1"),
            ],
            Explanation = "For an integral exponent `n`, `(-b) ^ n` is `b ^ n` for even `n` and `-(b ^ n)` for odd `n`, whichever computation the exponent routes through: a base whose magnitude is within `0.99 <= |b| <= 1.01` takes the near-one power for a fractional exponent, an exponent beyond `long`, or a negative exponent whose positive power overflows, and a negative base there takes its magnitude's power with the exponent's parity sign.",
        },
    ];
}
