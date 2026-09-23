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
                // Loop state is NOT a value boundary: the finished loop hands its slots to the root as rows ...
                new SpecProbe("Step = a + 1, b + 1\nStep.repeat(1, 0, 0)", "ok raw=S[1, 1] n=2"),
                // ... and only an ordinary property/argument boundary captures them as one value.
                new SpecProbe("Step = a + 1, b + 1\nR = Step.repeat(1, 0, 0)\nR", "ok raw=S[1, 1] n=1"),
            ],
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
                new SpecProbe("A = 1, 2, 3, 4, 5\nG(*x) = x.sum\nG(A)", "err arity"),
                new SpecProbe("G(*x) = x.sum\nG((1, 2, 3, 4, 5))", "err arity"),
                new SpecProbe("A = 1, 2, 3, 4, 5\nG(*x) = x.count\nG(A)", "ok raw=1 n=1"),
                new SpecProbe("A = 1, 2, 3, 4, 5\nG(*x) = x.count\nG(A*)", "ok raw=5 n=1"),
                new SpecProbe("A = 1, 2, 3, 4, 5\nG(*x) = x.count\nG(A, 0)", "ok raw=2 n=1"),
                new SpecProbe("G(*x) = x.sum\nG([1, 2, 3, 4, 5])", "err arity"),
                new SpecProbe("G(*x) = x.sum\nG([1, 2, 3, 4, 5]*)", "ok raw=15 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A collecting parameter collects the ARGUMENTS supplied to it, exactly as one list. `G(A*)` and `G(1, 2, 3, 4, 5)` supply five numeric items (sum 15). The grouped calls `G(A)` and `G((1, 2, 3, 4, 5))` supply ONE sequence-valued argument, collected as one element (`G(A)` counts 1) that the numeric `sum` rejects — exactly like a list argument `G([1, 2, 3, 4, 5])`. Only the explicit spread turns a value into several supplied items (`G([1, 2, 3, 4, 5]*)` sums to 15).",
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
                new SpecProbe("Target(*items) = items\nUseVariadic(*items) = Target\nUseVariadic((1, 2))", "ok raw=L[S[1, 2]] n=1"),
                new SpecProbe("Target(first, *middle, last) = middle\nUse(first, *middle, last) = Target\nUse(1, 2, 3, 4)", "ok raw=L[2, 3] n=1"),
                new SpecProbe("Target(*a) = a\nUse((a, b)) = Target\nUse(([1, 2], 5))", "ok raw=L[L[1, 2]] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Implicit forwarding decides spread from the SOURCE binding kind, never from the destination parameter kind: an ordinary caller parameter is passed as ONE argument even into a collecting destination (`Use(items) = Target` elaborates to `Target(items)`, so a list and a sequence value alike stay one collected item), and a caller collecting parameter legitimately forwards as spread (`UseVariadic(*items) = Target` elaborates to `Target(items*)`, which re-supplies exactly the collected items — `spread(collect(S)) = S`).",
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
                new SpecProbe("Mean(*Vector) = Vector.sum / Vector.count\n(1, 2, 2.718).Mean", "err arity"),
                new SpecProbe("Mean(*Vector) = Vector.sum / Vector.count\n[1, 2, 3].Mean", "err arity"),
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
            Explanation = "VALUES STAY VALUES. A non-spread argument supplies exactly ONE item — its value, whatever it is: a scalar, a sequence, a list, `()`, or `[]`. A collecting parameter collects exactly the items supplied to it as one list (`Coll((1, 2))` is `[(1, 2)]`, `Coll([1, 2])` is `[[1, 2]]`, `Coll(())` is `[()]`), a fixed parameter binds its item unchanged (`Id((1, 2))` is the pair, `Add((1, 2))` is an arity error), and ONLY the explicit spread `v*` turns a value into several items, one level, a sequence and a list alike (`Coll((1, 2)*)` and `Coll([1, 2]*)` are `[1, 2]`; spread-produced items are never reopened, so `Coll([(1, 2)]*)` is `[(1, 2)]`). So `*xs` counts the arguments supplied (`Cnt((10, 7))` is 1) while `x.count` counts one collection value's elements (`CntValue((10, 7))` is 2). Forwarding is `spread(collect(S)) = S`.",
        },
        new()
        {
            Id = "callback-element-is-one-argument",
            Category = "collection-builtins",
            Source = "AddPair((x, y)) = x + y\n\nmap([(1, 2)], AddPair)\nmap([[1, 2]], AddPair)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[3]\n[3]",
            ExpectedRaw = "S[L[3], L[3]]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                new SpecProbe("Add(x, y) = x + y\nmap([(1, 2)], Add)", "err arity"),
                new SpecProbe("Add(x, y) = x + y\nmap([[1, 2]], Add)", "err arity"),
                new SpecProbe("Cnt(*xs) = xs.count\nmap([(1, 2)], Cnt), map([[1, 2]], Cnt)", "ok raw=S[L[1], L[1]] n=2"),
                new SpecProbe("Cnt(*xs) = xs.count\nAlias = Cnt\nApply(f, xs) = map(xs, f)\nApply(Alias, [(10, 7), 20]), Apply(Alias, [[10, 7], 20])", "ok raw=S[L[1, 1], L[1, 1]] n=2"),
                new SpecProbe("IsPair(*xs) = xs.count == 2\nfilter([(1, 2), [1, 2]], IsPair)", "ok raw=L[] n=1"),
                new SpecProbe("Acc(x, *acc) = acc\nreduce([9], Acc, (1, 2)), reduce([9], Acc, [1, 2])", "ok raw=S[L[S[1, 2]], L[L[1, 2]]] n=2"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "THE CALLBACK LAW: a callback element is ONE ordinary argument, bound exactly as the direct call `F(element)` — `map`, `filter`, and `reduce` add no implicit opening. A two-parameter flat callee therefore rejects a pair element with the ordinary arity error (`map([(1, 2)], Add)` like `Add((1, 2))`), a sequence and a list alike, while a structural pattern opens the element explicitly (`AddPair((x, y))`). A collecting callback counts one argument per element (`map([(1, 2)], Cnt)` is `[1]`), through aliases and forwarding too (`Apply(Alias, [(10, 7), 20])` is `[1, 1]`), and a reducer receives its accumulator as one argument (`Acc(x, *acc)` collects `[(1, 2)]`).",
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
                new SpecProbe("Inc(x) = x + 1\ncount((Inc))", "err arity"),
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
                new SpecProbe("CountSequenceValue((*values)) = values.count\nCountSequenceValue([1, 2, 3])", "ok raw=3 n=1"),
            ],
            Explanation = "Top-level `*values` collects the call's ARGUMENTS: a grouped `(1, 2, 3)` is ONE argument (count 1), two arguments stay two (`CountValues((1, 2, 3), 4)` counts 2), and a list is one argument too. The sequence-value pattern `(*values)` is the explicit structural opener instead: it consumes exactly one structured argument — a sequence value or a list — and opens it during binding (`CountSequenceValue((1, 2, 3))` and `CountSequenceValue([1, 2, 3])` count 3), so a second argument is an arity error.",
        },
        new()
        {
            Id = "ordinary-sequence-pattern-opens-sequence-or-list",
            Category = "variadic-calls",
            Source = "PairSum((x, y)) = x + y\nPairSum((2, 3))\nPairSum([2, 3])",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "5\n5",
            ExpectedRaw = "S[5, 5]",
            ExpectedEmittedCount = 2,
            Probes =
            [
                // The pattern opens ONE lone structure of either kind and binds its immediate items; a
                // wrong item count or a non-structure argument is an arity error against the pattern.
                new SpecProbe("PairSum((x, y)) = x + y\nPairSum([1, 2, 3])", "err arity"),
                new SpecProbe("PairSum((x, y)) = x + y\nPairSum(7)", "err arity"),
                // A collecting sequence-value pattern collects a lone list's items the same way.
                new SpecProbe("Count((*v)) = v.count\nCount([1, 2, 3])", "ok raw=3 n=1"),
                // Callback position uses the same binder, so a nested pattern opens list AND sequence rows.
                new SpecProbe("PairSum((x, y)) = x + y\n[[1, 2], (3, 4)].map(PairSum)", "ok raw=L[3, 7] n=1"),
                // Contrast: in a multi-clause family the same written pattern matches sequence values only.
                new SpecProbe("F((x, y)) = x + y\nF(z) = 0\nF([2, 3])", "ok raw=0 n=1"),
            ],
            Explanation = "An ordinary (single-clause) sequence-value parameter pattern consumes exactly one argument slot and opens that slot's value — a lone sequence value or a lone exact list, the same two kinds assignment deconstruction opens — binding only its immediate items. Any other value, or the wrong number of items, is an arity error against the pattern. A multi-clause family is narrower: there the same pattern matches sequence values only.",
        },
        new()
        {
            Id = "binding-failure-outranks-repeated-name-conflict",
            Category = "variadic-calls",
            Source = "Bad = 1 / 0\nP(x, x, (a, b)) = a\n\nP(1, 2, Bad)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "div0",
            Probes =
            [
                // Every pattern binds first; the unequal x is only a merge failure.
                new SpecProbe("P(x, x, (a, b)) = a\nP(1, 2, 7)", "err arity"),
                // Between different names the innermost merge decides: the (f, f) merge runs first.
                new SpecProbe("Inc(y) = y + 1\nP(x, x, f, f) = 0\nP(1, 2, Inc, Inc)", "err type"),
                new SpecProbe("Inc(y) = y + 1\nP(f, f, x, x) = 0\nP(Inc, Inc, 1, 2)", "err arity"),
                // A conflict inside a nested group is part of binding that group.
                new SpecProbe("Bad = 1 / 0\nP((x, x), (a, b)) = a\nP((1, 2), Bad)", "err arity"),
                // Equal repeated values still bind.
                new SpecProbe("P(x, x, (a, b)) = b\nP(1, 1, (2, 3))", "ok raw=3 n=1"),
            ],
            Explanation = "A parameter-pattern list binds EVERY pattern before it checks its repeated names, so a later pattern's failure — here the argument `Bad`, whose value the `(a, b)` pattern must open — is reported instead of the unequal `x`. Between different repeated names, the merge that runs first — the innermost, whose name completes furthest right — decides, and within one merge an unequal value (an arity error) is found before a callable-only repeat (a type error). A conflict inside a nested group belongs to binding that group, and equal repeated values still bind. Callbacks and loop state bind in the same order.",
        },
        new()
        {
            Id = "repeated-name-binding-is-order-independent",
            Category = "variadic-calls",
            Source = "A = 5\nInc(y) = y + 1\nP(f, f, f) = f\n\nP(A, 5, Inc)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Probes =
            [
                // Every permutation of the same arguments gives the same verdict.
                new SpecProbe("A = 5\nInc(y) = y + 1\nP(f, f, f) = f\nP(Inc, 5, A)", "err type"),
                new SpecProbe("A = 5\nInc(y) = y + 1\nP(f, f, f) = f\nP(5, A, Inc)", "err type"),
                // Every pair compatible: binds in every order.
                new SpecProbe("A = 5\nP(f, f, f) = f\nP(A, A, 5)", "ok raw=5 n=1"),
                new SpecProbe("A = 5\nP(f, f, f) = f\nP(5, A, A)", "ok raw=5 n=1"),
                // Unequal values outrank a callable-only repeat, in every order.
                new SpecProbe("A = 5\nB = 6\nInc(y) = y + 1\nP(f, f, f) = f\nP(Inc, B, A)", "err arity"),
                // Two occurrences keep the pairwise rule: a plain value beside a callable binds.
                new SpecProbe("Inc(y) = y + 1\nP(f, f) = f\nP(5, Inc)", "ok raw=5 n=1"),
            ],
            Explanation = "A repeated parameter name is checked once, after all of its occurrences have bound, by comparing every occurrence with every other: values must be equal, and when two or more arguments reach the name as callables, each of them must also carry a value to compare. `Inc` passed bare has no value, and `A = 5` is also usable as a callable, so `(A, 5, Inc)` fails in every order, while `(A, A, 5)` binds in every order. Argument order never changes whether the call binds.",
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
            Explanation = "The parameters left and right are genuine aliases of the one callable A. Both argument orders bind successfully and preserve all channels: f reads 5, its count is 1, and both direct invocation and the callback invoke A. Successful permutations preserve channel availability, values, counts and callable identity. Forwarding retains ordinary eager argument-binding effects.",
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
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "type",
            Explanation = "Each independently resolved dot result supplies a fresh wrapper algorithm, so two equal results do not establish one callable identity. Forwarding one such wrapper twice preserves its identity instead.",
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
            Explanation = "A dot-result wrapper keeps its runtime callable identity through parameter forwarding. Passing that one wrapper twice is compatible and invokes it as the same callable.",
        },
        new()
        {
            Id = "collecting-pattern-list-merges-after-the-collector",
            Category = "variadic-calls",
            Source = "Bad = 1 / 0\nP(x, *rest, x) = x\n\nP(1, Bad, 2)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "div0",
            Probes =
            [
                // The prefix binds and checks its repeated names before the suffix binds.
                new SpecProbe("Bad = 1 / 0\nP(x, x, *rest, (a, b)) = a\nP(1, 2, Bad)", "err arity"),
                // The suffix binds before the prefix/suffix check.
                new SpecProbe("Bad = 1 / 0\nP(x, *rest, x, (a, b)) = a\nP(1, 9, 2, Bad)", "err div0"),
                new SpecProbe("P(x, *rest, x) = rest\nP(1, 9, 1)", "ok raw=L[9] n=1"),
            ],
            Explanation = "With a collecting parameter the fixed prefix binds and checks its repeated names first, then the suffix does the same, then the collector gathers its values; only then are the prefix, the collector, and the suffix checked against each other. So `P(1, Bad, 2)` reports the collected argument's division by zero rather than the unequal `x`, while a conflict inside the prefix is still found before the suffix binds.",
        },
        new()
        {
            Id = "redundant-call-parens-canonical",
            Category = "variadic-calls",
            Source = "Inner = (1, 2, 3)\nCountSequenceValue((*values)) = values.count\nNestedCount(((*values))) = values.count\n\nCountSequenceValue(Inner)\nCountSequenceValue((Inner))\nCountSequenceValue(((1, 2, 3)))\nNestedCount([(1, 2, 3)])\nNestedCount(([[1, 2, 3]]))",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "3\n3\n3\n3\n3",
            ExpectedRaw = "S[3, 3, 3, 3, 3]",
            ExpectedEmittedCount = 5,
            Probes =
            [
                new SpecProbe("NestedCount(((*values))) = values.count\nNestedCount((1, 2, 3))", "err arity"),
                new SpecProbe("NestedCount(((*values))) = values.count\nNestedCount(((1, 2, 3)))", "err arity"),
                new SpecProbe("NestedCount(((*values))) = values\nNestedCount(7), NestedCount(((7))), NestedCount(true), NestedCount('s')", "ok raw=S[L[7], L[7], L[true], L['s']] n=4"),
                new SpecProbe("NestedCount(((*values))) = values\nNestedCount([()]), NestedCount(([(1, 2)]))", "ok raw=S[L[], L[1, 2]] n=2"),
                new SpecProbe("CountSequenceValue((*values)) = values.count\nCountSequenceValue(((1, 2), 3))", "ok raw=2 n=1"),
                new SpecProbe("S = 1, 2\nF((a, b)) = a + b\nF({S})", "ok raw=3 n=1"),
                new SpecProbe("A = [[1, 2]]\nP((*xs)) = xs\nP((A*))", "ok raw=L[1, 2] n=1"),
            ],
            Explanation = "Parentheses group syntax; they do not introduce a semantic boundary. A pattern-shaped callee opens the argument's VALUE: `Inner`, `(Inner)`, and `((1, 2, 3))` are all the sequence value `(1, 2, 3)`, so the collecting parameter collects its three items in every spelling — a redundant group is never a written level for the pattern to consume, and a single-row block `{S}` or a captured spread `(A*)` is likewise just its value. A nested pattern `((*values))` opens two real boundaries, and unary sequence structure never survives normalization, so a one-element list (`[(1, 2, 3)]`, `[[1, 2, 3]]`) supplies the outer structural level. Scalars also bind through the ordinary one-item fallback at each level, without creating a unary sequence; `(1, 2, 3)` and `((1, 2, 3))` open to three items against the one nested pattern and are the same arity error. Non-unary structure is preserved: `((1, 2), 3)` counts 2.",
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
            Explanation = "A singleton sequence-value clause head `(x)` matches ANY one argument whole via the scalar one-item rule: singleton sequence structure normalizes away during construction, so the pattern must also accept a non-sequence result as if it were a one-element sequence. It never opens the argument — an exact list binds entire, including a singleton list. Only a sequence value of a different arity fails the head.",
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
                // The singleton pattern is the one exception: it matches any single argument whole.
                new SpecProbe("F((x)) = x\nF(z) = 0\n\nF([2, 3])", "ok raw=L[2, 3] n=1"),
                // Contrast: the ordinary single-clause definition opens the same list.
                new SpecProbe("PairSum((x, y)) = x + y\nPairSum([2, 3])", "ok raw=5 n=1"),
            ],
            Explanation = "In a clause family a sequence-value pattern matches sequence values only: an exact list argument does not match `(x, y)` even when its element count fits, so it falls through to a later clause, or fails with no matching branch when none accepts it. A singleton pattern `(x)` is the one exception and matches any single argument whole. An ordinary single-clause definition is wider and also opens a lone list.",
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
            Explanation = "Grace composes with ordinary DotCall. Base occurrence order for `a.t` is receiver then participating fallback: `(a, t)`. In `a~.t`, ordinary postfix Grace moves `a` one place later; in `a.~t`, ordinary prefix Grace moves `t` one place earlier. Both infer `(t, a)` — the order the explicit spelling `K(t, a) = a.t` declares — and all three sources elaborate to the same ordinary `a.t` body. Grace is meaningful only on such FREE names: under an explicit parameter list (`K(t, a) = a~.t`) the marker could reorder nothing and is a front-end error.",
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
            Explanation = "`~` changes inferred parameter ORDER only — never member selection. `Read = o~.V` graces the FREE receiver name `o` (the marker is effective: `o` becomes Read's implicit parameter), and `Read(Obj)` performs ordinary structural-first DotCall lookup, reading Obj's own `V` even though a lexical `V` exists — exactly like the direct `Obj.V`. With no lexical `V` declaration, prefix member Grace behaves the same way on an opaque receiver: `Read = o.~V` infers `(V, o)`, and `Read({x}, Obj)` still reads Obj's structural `V`. To call the lexical `V` with Obj's value, write the call `V(Obj)`. A marker on the bound `Obj` itself (`Obj~.V`) could reorder nothing and is rejected instead of being ignored.",
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
            Explanation = "A member name the receiver does not declare is not an error by itself, and a statically known receiver (`Math`, a block, a module) gets no special status: `Lib.Dubel(4)` has no structural `Dubel`, so it is the ordinary lexical fallback `Dubel(Lib, 4)` — `a` receives the `Lib` algorithm and `b` receives `4`. Static receiver knowledge improves the DIAGNOSTIC when no such callable is visible (the report names the receiver, explains the fallback, and suggests a real member), but never the resolution or the validity of the program.",
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
                // The open channel refuses the same member from outside its owner.
                new SpecProbe("Outer(n) = {\n    public Inner = {\n        public X = n\n    }\n    Inner.X\n}\nopen Outer.Inner\nX", "err localOnlyProperty"),
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
            Id = "open-full-spelling-decides-provider-identity",
            Category = "name-resolution",
            Source = $"open {new string('N', 520)}A, {new string('N', 520)}B\n{new string('N', 520)}A = {{ public X = 1 }}\n{new string('N', 520)}B = {{ public X = 2 }}\nX",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "ambiguousOpen",
            Explanation = "Named open targets deduplicate by their complete spelling. Distinct names remain distinct providers even when their diagnostic displays abbreviate to the same text; two providers of X are ambiguous in either order.",
        },
        new()
        {
            Id = "open-local-only-member-is-a-second-provider",
            Category = "name-resolution",
            Source = "Pub = {\n    public X = 101\n}\nOuter(p) = {\n    public Lib = {\n        public X = p + 202\n    }\n    0\n}\nA = {\n    open Pub, Outer.Lib\n    X\n}\nA",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "ambiguousOpen",
            Probes =
            [
                new SpecProbe("Pub = {\n    public X = 101\n}\nLib = {\n    X = 202\n}\nA = {\n    open Pub, Lib\n    X\n}\nA", "ok raw=101 n=1"),
            ],
            Explanation = "`open` selects members by visibility alone: a public local-only member is provided by its open whatever its exposure and takes part in precedence and ambiguity like any provided name, so beside another provider of `X` it is a genuine second provider. Only a PRIVATE member is never provided. Whether the selected member may be used at the site is checked afterwards, which is what lets the front end select exactly what the evaluator selects before exposure is classified.",
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
                new SpecProbe("Lib(p) = {\n public Mid = {\n public Sub = { public X = 10 }\n q\n }\n p\n}\nopen Lib.Mid.Sub\nX", "ok raw=10 n=1"),
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
            Id = "capture-suppresses-higher-order-identity",
            Category = "access-boundaries",
            Source = "Apply = f(9)\nIncrement(x) = x + 1\nApply((Increment, Increment))",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                new SpecProbe("Apply = f(9)\nIncrement(x) = x + 1\nApply(Increment)", "ok raw=10 n=1"),
                new SpecProbe("Apply = f(9)\nIncrement(x) = x + 1\nApply((Increment))", "ok raw=10 n=1"),
                new SpecProbe("Apply = f(9)\nIncrement(x) = x + 1\nApply(((Increment)))", "ok raw=10 n=1"),
                new SpecProbe("Apply = f(9)\nIncrement(x) = x + 1\nApply((Increment*))", "err arity"),
            ],
            Explanation = "A capture — a group of several slots such as `(Increment, Increment)`, or a lone spread `(Increment*)` — supplies only a zero-parameter value thunk on the algorithm channel, so it suppresses the enclosed callable identity, and evaluating its rows demands `Increment` with zero arguments. Redundant parentheses are not a capture: parentheses group syntax, so `Apply((Increment))` and `Apply(((Increment)))` forward Increment's callable identity exactly like `Apply(Increment)`.",
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
                new SpecProbe("Obj = {public V = 7\n0}\nQ(z) = (Obj*).V\nQ(0)", "err unknownName"),
            ],
            Explanation = "Parentheses group syntax: `(Obj).V` IS `Obj.V`, so both read Obj's own property. A genuine capture receiver — a lone spread `(Obj*)` or a group of several slots — has no structural members, so `(Obj*).V` falls back lexically and injects the captured value as the leading argument. With no lexical member name in sight the fallback has nowhere to go — inside a closed parameter list that is an unknown-name error, and in an implicitly parameterized body the member becomes an inferred parameter instead.",
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
                // `open` exports only public members: Area arrives, Helper does not (it would be a root parameter).
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
            Explanation = "Private means not exported, not unreachable: `open` and `load` bring only `public` members into scope, while structural dot access ignores `public`, so `Lib.Helper` reaches the private, self-contained `Helper`. Exposure never removes a member from selection: a `public` member that depends on an enclosing parameter is selected as usual and then refused at any access written outside the owner of that parameter. A parameterized algorithm is refused as an `open` target outright, because `open` imports a namespace and never creates the activation its members would read.",
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
                new SpecProbe("Swap((a, b)) = (b, a)\nmap([[1, 2]], Swap)", "ok raw=L[S[2, 1]] n=1"),
            ],
            Explanation = "Each callback item is one selected value, passed to the callback as ONE ordinary argument — exactly as the direct call `Swap(item)`. A pair-shaped callback therefore opens the row with an explicit structural pattern `Swap((a, b))`, a sequence and a list row alike; the flat two-parameter `Swap(a, b)` is the ordinary arity error for a one-argument call. Each callback must return exactly one value, preserved as one exact list element.",
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
                new SpecProbe("F((first, *middle, last)) = middle\nRows = [[1, 2, 3, 4]]\nRows.map(F)", "ok raw=L[L[2, 3]] n=1"),
                new SpecProbe("F(first, *rest) = rest\n[(1, 2, 3)].map(F)", "ok raw=L[L[]] n=1"),
                new SpecProbe("F((first, *rest)) = rest\n[(1, 2, 3)].map(F)", "ok raw=L[L[2, 3]] n=1"),
                new SpecProbe("F(first, *rest) = rest\n[7].map(F)", "ok raw=L[L[]] n=1"),
                new SpecProbe("F(*init, last) = init\n[(1, 2, 3)].map(F)", "ok raw=L[L[]] n=1"),
            ],
            Explanation = "A callback element is ONE ordinary argument (there is no callback row convention), so a row is opened by the callee's explicit structural pattern: `F((first, *middle, last))` opens each row — a sequence and a list alike — and COLLECTS the middle as an exact list. The flat `F(first, *middle, last)` receives one argument against two fixed positions and is the ordinary arity error, exactly like `F((1, 2, 3, 4))`; a flat prefix or suffix binds the whole element and leaves the collector empty.",
        },
        new()
        {
            Id = "callback-nested-pattern-binds-like-call",
            Category = "collection-builtins",
            Source = "Head((x, *rest)) = [x, rest]\n\nHead(7)\n[7].map(Head)\nmap((7, (8, 9)), Head)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "[7, []]\n[[7, []]]\n[[7, []], [8, [9]]]",
            ExpectedRaw = "S[L[7, L[]], L[L[7, L[]]], L[L[7, L[]], L[8, L[9]]]]",
            ExpectedEmittedCount = 3,
            Probes =
            [
                // A scalar is ONE item for the nested pattern — too few for a fixed pair, in the
                // direct call and the callback alike.
                new SpecProbe("Pair((x, y)) = [x, y]\nPair(7)", "err arity"),
                new SpecProbe("Pair((x, y)) = [x, y]\n[7].map(Pair)", "err arity"),
                // A sequence or list element opens one level, exactly as in the direct call.
                new SpecProbe("Head((x, *rest)) = [x, rest]\n[[7, 8]].map(Head)", "ok raw=L[L[7, L[8]]] n=1"),
                new SpecProbe("Last((*init, z)) = z\n[true, (1, 2)].map(Last)", "ok raw=L[true, 2] n=1"),
                // filter and reduce bind their values through the same rules.
                new SpecProbe("Big((x, *rest)) = x > 1\n[7, 1].filter(Big)", "ok raw=L[7] n=1"),
                new SpecProbe("R((x, *rest), acc) = acc + x\nreduce([7, 8], R, 0)", "ok raw=15 n=1"),
                // The operation decides the invocations: an empty collection runs nothing, while
                // an empty element is one invocation with the value `()`.
                new SpecProbe("Head((x, *rest)) = [x, rest]\n[].map(Head)", "ok raw=L[] n=1"),
                new SpecProbe("Head((x, *rest)) = [x, rest]\n[()].map(Head)", "err arity"),
            ],
            Explanation = "A callback binds each value it supplies exactly as the ordinary call supplying that one value does: a nested sequence-value pattern opens a sequence or list value one level, and any other value (a number, string, or Boolean) is the ordinary one-item supply at every pattern level — so a scalar element binds `(x, *rest)` with an empty `rest` and is one item too few for `(x, y)`, just like `Head(7)` and `Pair(7)`. The callback operation still decides how many values it supplies (one element for map and filter, element and accumulator for reduce) and how often it invokes the callback (never for an empty collection).",
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
                // with count), reduce, and repeat, and a property alias of the callable.
                new SpecProbe("Cnt(*xs) = xs.count\nApply(f, xs) = map(xs, f)\nApply(Cnt, [1, 2])", "ok raw=L[1, 1] n=1"),
                new SpecProbe("Big(*xs) = xs.sum > 1\nKeep(f, xs) = xs.filter(f)\nKeep(Big, [1, 2, 3])", "ok raw=L[2, 3] n=1"),
                new SpecProbe("Big(*xs) = xs.sum > 1\nHits(f, xs) = xs.filter(f).count\nHits(Big, [1, 2, 3])", "ok raw=2 n=1"),
                new SpecProbe("SumAll(*xs) = xs.sum\nFold(f, xs) = xs.reduce(f, 0)\nFold(SumAll, [1, 2, 3])", "ok raw=6 n=1"),
                new SpecProbe("CountStep(*s) = s.count + 1\nRun(g) = repeat(g, 3, 9)\nRun(CountStep)", "ok raw=2 n=1"),
                new SpecProbe("Only(*xs) = xs\nG = Only\nApply(f, xs) = map(xs, f)\nApply(G, [1])", "ok raw=L[L[1]] n=1"),
                // VALUE slots read the bound value: the collection and reduce's initial
                // accumulator see the callable's zero-argument value.
                new SpecProbe("Only(*xs) = xs\nSize(xs) = count(xs)\nSize(Only)", "ok raw=0 n=1"),
                new SpecProbe("Seven(*xs) = 7\nR(x, acc) = acc + x\nStart(i) = reduce([1, 2], R, i)\nStart(Seven)", "ok raw=10 n=1"),
                // A value-only argument has no callable to invoke, directly or forwarded.
                new SpecProbe("Apply(f, xs) = xs.map(f)\nApply(5, [1])", "err arity"),
                new SpecProbe("[1].map(5)", "err arity"),
                // A callable whose zero-argument demand fails is bound on the algorithm
                // channel only, and always worked.
                new SpecProbe("Z(*xs) = 10 / xs.count\nApply(f, xs) = xs.map(f)\nApply(Z, [1, 2])", "ok raw=L[10, 10] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Passing a callable to a parameter binds it as a callable, and also as a value when it can be read with no arguments (`Cnt` reads as `0`). A builtin slot that calls its argument — the map mapper, the filter predicate, the reduce reducer, a while or repeat step — calls the callable, so forwarding `Cnt` through `Apply` selects the same callable as `[1, 2].map(Cnt)`, including from a nested block that captures the parameter. Forwarding retains ordinary eager parameter-binding effects; callback selection adds no further value demand. A slot that reads a value — the collection, reduce's initial accumulator — reads the bound value.",
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
            Source = "Append(item, (*history)) = (history*, item)\nreduce((2, 3, 4), Append, 1)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "(1, 2, 3, 4)",
            ExpectedRaw = "S[1, 2, 3, 4]",
            ExpectedEmittedCount = 1,
            Probes =
            [
                new SpecProbe("Append(item, (*history)) = (history*, item)\nreduce(2, 3, 4, Append, 1)", "err arity"),
                new SpecProbe("Append(item, *history) = (history*, item)\nreduce((2, 3, 4), Append, 1)", "ok raw=S[S[S[1, 2], 3], 4] n=1"),
                new SpecProbe("Add(a, b) = a + b\nreduce((1, 2, 3, 4), Add, 0)", "ok raw=10 n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "`reduce(collection, reducer, initial)` takes exactly three arguments and threads ONE accumulator value: the reducer is called as `Append(item, accumulator)`, two ordinary arguments. The explicit pattern `(*history)` opens the accumulator (a scalar is a one-item supply), so the result displays as ONE sequence value `(1, 2, 3, 4)` — not as separate rows — while an unopened collecting parameter `*history` collects the one accumulator value whole, nesting each step. Supplying the items inline (`reduce(2, 3, 4, Append, 1)`) is an ordinary five-argument arity error.",
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
            Explanation = "SYN-07B: the star is read by the token that follows it, never by spacing or by the line break. `A*` newline `B`, `A *` newline `B`, `A* B`, and `A * B` are all the multiplication `A * B` — a line-final star continues onto the next line exactly like every trailing binary operator, in a definition body too. To spread `A` and then emit `B` as the next row, close the spread slot with a comma (`A*,` newline `B`).",
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
            ExpectedParseDiagnosticFragment = "Grace has no effect on 'X' because it already resolves to a property",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidGraceMarker,
            IncludeInGeneratorPrompt = true,
            Explanation = "Grace is meaningful only on a FREE name that becomes an implicit parameter of the enclosing algorithm — that is the one place its weight is consumed. `X` is a visible property, so `~X` could reorder nothing; instead of being silently ignored the marker is a front-end error naming what fixed the binding. Cancelling markers (`~X~`) still validate this binding. The same rule covers a builtin (`~count`), an opened name, a parameter of an enclosing algorithm, and a dot member the receiver is known to declare (`Obj.~V`).",
        },
        new()
        {
            Id = "grace-under-explicit-list-rejected",
            Category = "parser-layout",
            Source = "K(b, a) = b, ~a\nK(1, 2)",
            Outcome = SpecOutcome.ParseError,
            ExpectedParseDiagnosticFragment = "Grace has no effect on 'a' because it already resolves to an explicit parameter",
            ExpectedDiagnosticCode = DiagnosticCode.InvalidGraceMarker,
            IncludeInGeneratorPrompt = true,
            Explanation = "An explicit parameter list fixes the parameter order, so nothing is inferred under it and a Grace marker there can reorder nothing: `K(b, a) = b, ~a` is rejected rather than silently keeping `(b, a)`. Write the order in the list (`K(a, b) = b, a`) or drop the list and let `~a` reorder the inferred parameters (`K = b, ~a` infers `(a, b)`).",
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
                // Unary minus uses its existing numeric conversion (arity category), and
                // unary `not` its Boolean-operand rule (type category), with no
                // empty-sequence bypass either.
                new SpecProbe("-()", "err arity"),
                new SpecProbe("not ()", "err type"),
                new SpecProbe("-(1, 2)", "err arity"),
                new SpecProbe("not (1, 2)", "err type"),
                new SpecProbe("-[1, 2]", "err arity"),
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
            Notes = "SYN-01. Binary operators previously returned the other operand when either was `()`; unary operators propagated `()`. Both bypasses are removed. Unary sequence/list rejection retains the existing arity category; binary rejection retains type. Empty NEUTRALITY belongs to the arity algebra's supply operations (capture/collect/spread) and is deliberately untouched, as the last two probes pin.",
            Explanation = "The empty sequence value is a real value, not an operator identity: scalar operators apply their ordinary operand validation to `()` just as to any other non-scalar value. `10 / ()`, `-()`, and `not ()` are errors.",
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
                // `order`/`orderDesc` use Decimal128's TOTAL order (NaN sorts
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
            Explanation = "Using Need completes Outer's signature with v. Its property v then conflicts with that parameter, so the front end rejects the declaration even though v was not in Outer's initially inferred signature.",
        },
        new()
        {
            Id = "ownership-later-lifted-parameter-beats-inner-open",
            Category = "name-resolution",
            Source = "Lib = { public v = 99 }\nOuter = {\n    Inner = { open Lib\n        v\n    }\n    Need = v\n    Inner + Need\n}\nOuter(7)",
            Outcome = SpecOutcome.Evaluates,
            ExpectedDisplay = "14",
            ExpectedRaw = "14",
            ExpectedEmittedCount = 1,
            Probes =
            [
                // Forwarding Need completes Outer's signature before final binding selection.
                new SpecProbe("Need(v) = v\nOuter = { F(0) = 0\nF(n) = v\nF(1) + Need }\nOuter(7)", "ok raw=14 n=1"),
                // The original bare v must not retain the synthesized v(x) call.
                new SpecProbe("v = x + 99\nOuter = { Inner = v\nNeed(v) = v\nInner + Need }\nOuter(2, 7)", "ok raw=14 n=1"),
            ],
            Explanation = "Established parameters include those lifted by implicit argument resolution: referencing Need supplies v to Outer's completed signature. The earlier nested v therefore selects Outer's parameter before Inner's open and both terms read 7. Completion preserves the inferred signatures and ordering, then rebuilds forwarding and closed-input diagnostics for the selected bindings.",
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
                // conditional value-access failure surfaces.
                new SpecProbe("C(0) = 1\nC(n) = 2\nMath.Abs(C)", "err branch"),
                // A builtin argument reports the builtin's own arity failure.
                new SpecProbe("Math.Abs(count)", "err arity"),
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
            Explanation = "The one intrinsic thing about `if` is its invocation: evaluate the condition, then only the selected branch. That belongs to the resolved builtin — shadow the name and an ordinary eager user call takes over — and it is not a promise about arguments the CALLER already evaluated, so building a value before spreading it follows the ordinary expression-to-value-to-supply rule.",
        },
        new()
        {
            Id = "lazy-slot-demand-is-the-ordinary-zero-argument-demand",
            Category = "conditionals",
            Source = "Inc(x) = x + 1\nif(true, Inc, 0)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // The false branch and the condition are the same demand.
                new SpecProbe("Inc(x) = x + 1\nif(false, 0, Inc)", "err arity"),
                new SpecProbe("Inc(x) = x + 1\nif(Inc, 1, 0)", "err arity"),
                // An unselected slot is never demanded: laziness is untouched.
                new SpecProbe("Inc(x) = x + 1\nif(false, Inc, 7)", "ok raw=7 n=1"),
                new SpecProbe("Inc(x) = x + 1\nif(true, 7, Inc)", "ok raw=7 n=1"),
                // A zero-parameter algorithm is an ordinary value, even one that captures an enclosing binding.
                new SpecProbe("A = 7\nif(true, A, 0)", "ok raw=7 n=1"),
                new SpecProbe("Outer(v) = { Inner = v + 1\n if(true, Inner, 0) }\nOuter(7)", "ok raw=8 n=1"),
                // The decision is the signature's, not the body's: K never reads x.
                new SpecProbe("K(x) = 5\nif(true, K, 0)", "err arity"),
                // An explicit call is a value; an explicit zero-argument call is the ordinary call arity error.
                new SpecProbe("Inc(x) = x + 1\nif(true, Inc(4), 0)", "ok raw=5 n=1"),
                new SpecProbe("Inc(x) = x + 1\nif(true, Inc(), 0)", "err arity"),
                // An inferred parameter counts exactly like an explicit one.
                new SpecProbe("A = q + 1\nif(true, A, 0)", "err arity"),
                // A COLLECTING parameter requires no supplied argument, so the bare
                // callable and its explicit zero-argument call agree (September 2026).
                new SpecProbe("Collect(*xs) = xs\nif(true, Collect, 0)", "ok raw=L[] n=1"),
                new SpecProbe("Collect(*xs) = xs\nif(true, Collect(), 0)", "ok raw=L[] n=1"),
                // A required fixed parameter beside a collector still needs one value.
                new SpecProbe("Head(x, *rest) = x\nif(true, Head, 0)", "err arity"),
                // A clause family cannot be accessed as a value at all.
                new SpecProbe("F(0) = 10\nF(x) = x + 1\nif(true, F, 0)", "err branch"),
                // A parameter bound only on the callable channel is the same demand.
                new SpecProbe("Inc(x) = x + 1\nApply(g) = if(true, g, 0)\nApply(Inc)", "err arity"),
                // A zero-parameter branch that fails still reports its own failure.
                new SpecProbe("Boom = 1 / 0\nif(true, Boom, 0)", "err div0"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "The selected branch is demanded exactly like a bare property reference: `Inc` still needs its `x`, so the ordinary zero-argument arity error is reported at the reference and `Inc`'s body is never entered — the same report writing `Inc` alone produces. Only the selected slot is demanded, so a parameterized algorithm in the unselected branch is harmless, and an explicit call (`Inc(4)`) is an ordinary value.",
        },
        new()
        {
            Id = "lazy-slot-demand-covers-every-builtin-value-slot",
            Category = "collection-builtins",
            Source = "Inc(x) = x + 1\nStep(s) = s + 1\nrepeat(Step, 1, Inc)",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                // The repeat count and while's initial state are value slots too.
                new SpecProbe("Inc(x) = x + 1\nStep(s) = s + 1\nrepeat(Step, Inc, 0)", "err arity"),
                new SpecProbe("Inc(x) = x + 1\nDown(s) = s - 1, s\nwhile(Down, Inc)", "err arity"),
                // So are the atoms and range arguments.
                new SpecProbe("Inc(x) = x + 1\natoms(Inc)", "err arity"),
                new SpecProbe("Inc(x) = x + 1\nrange(1, Inc)", "err arity"),
                // Zero-parameter controls evaluate as before.
                new SpecProbe("A = 0\nStep(s) = s + 1\nrepeat(Step, 1, A)", "ok raw=1 n=1"),
                new SpecProbe("A = 7\natoms(A)", "ok raw=L[7] n=1"),
                // Callback slots supply arguments and never consult the rule.
                new SpecProbe("Inc(x) = x + 1\nrepeat(Inc, 2, 0)", "ok raw=2 n=1"),
                new SpecProbe("Inc(x) = x + 1\nmap([1, 2], Inc)", "ok raw=L[2, 3] n=1"),
                new SpecProbe("Add(e, a) = e + a\nreduce([1, 2], Add, 0)", "ok raw=3 n=1"),
                // reduce's initial accumulator keeps its dedicated hint, decided from the signature: K never runs.
                new SpecProbe("K(x) = 5\nAdd(e, a) = e + a\nreduce([1, 2], Add, K)", "err arity"),
                // Collection and fixed value controls use the same demand law after binding.
                new SpecProbe("K(x) = 5\ncount(K)", "err arity"),
                new SpecProbe("K(x) = 5\ncontains([1], K)", "err arity"),
                new SpecProbe("K(x) = 5\ntake([1], K)", "err arity"),
                new SpecProbe("K(x) = 5\nskip([1], K)", "err arity"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "Every builtin value slot — a loop's initial state, the `repeat` count, `atoms`, `range`, a collection, or a fixed value control — applies the ordinary zero-argument value-demand law to its argument. An algorithm that still needs arguments is rejected at its reference before its body runs; `reduce` keeps its dedicated initial-accumulator hint. Callback slots (`repeat`/`while` steps, `map`, `filter`, `reduce` steps) supply arguments and are unaffected.",
        },
        new()
        {
            Id = "dot-string-receiver-is-a-zero-argument-value-demand",
            Category = "strings",
            Source = "Inc(x) = x + 1\nInc.string",
            Outcome = SpecOutcome.EvalError,
            ExpectedErrorCategory = "arity",
            Probes =
            [
                new SpecProbe("A = 7\nA.string", "ok raw='7' n=1"),
                new SpecProbe("Inc(x) = x + 1\nInc(4).string", "ok raw='5' n=1"),
                // A navigated parameterized member and a callable-channel parameter receiver are the same demand.
                new SpecProbe("Lib = { Sub(x) = x }\nLib.Sub.string", "err arity"),
                new SpecProbe("Inc(x) = x + 1\nF(g) = g.string\nF(Inc)", "err arity"),
            ],
            Explanation = "`.string` demands its receiver as a zero-argument value, so a receiver that still needs arguments is the ordinary arity error at the receiver and its body is never entered; `Inc(4).string` converts the call's result.",
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
                // A nested pattern consumes its one supplied slot: its scalar one-item
                // fallback binds a value, it does not accept none.
                new SpecProbe("P((x, *rest)) = x\nP", "err arity"),
                new SpecProbe("P((x, *rest)) = x\nP()", "err arity"),
                new SpecProbe("P((*xs)) = xs\nP", "err arity"),
                new SpecProbe("P((*xs)) = xs\nP(7)", "ok raw=L[7] n=1"),
                // The ALGORITHM channel is untouched: a callback still receives the
                // callable, so each element is collected.
                new SpecProbe("Only(*xs) = xs\nmap((1, 2), Only)", "ok raw=L[L[1], L[2]] n=1"),
            ],
            IncludeInGeneratorPrompt = true,
            Explanation = "A callable may be read as a zero-argument value exactly when an ordinary call with no arguments can bind it. A collecting parameter requires no supplied argument, so `Only` and `Only()` both collect nothing and give `[]`; `Head(x, *rest)` still requires one supplied value, so both of its zero-argument spellings are the same arity error. Callback positions still receive the callable itself.",
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
            Explanation = "The `.string` intrinsic is a zero-parameter member. A written argument list is assembled exactly like every call's (each slot evaluated once, spreads opened) and then rejected by arity, the outcome `Obj.V(1)` has for a declared zero-parameter member — a written bundle is never silently dropped. An empty written list (`A.string()`) stays the intrinsic, as `A()` stays a call of `A`.",
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
    ];
}
