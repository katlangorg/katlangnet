# KatLang Tutorial

Learn KatLang from a first calculation through collections, higher-order algorithms, pattern matching, and module loading. The examples are meant to be run as you read; most show their exact result immediately below the source.

## Contents

1. [How to Use This Tutorial](#how-to-use-this-tutorial)
2. [What KatLang Is](#what-katlang-is)
3. [Your First KatLang Program](#your-first-katlang-program)
   - [Comments](#comments)
4. [Values and Arithmetic](#values-and-arithmetic)
   - [Arithmetic Operators](#arithmetic-operators)
   - [Comparison Operators](#comparison-operators)
   - [Logical Operators](#logical-operators)
   - [Math Constants and Functions](#math-constants-and-functions)
   - [Reproducible random values](#reproducible-random-values)
   - [Lowercase Math Aliases](#lowercase-math-aliases)
   - [Display Decimal Places](#display-decimal-places)
5. [Output Rows and Sequences](#output-rows-and-sequences)
   - [Sequence Normalization](#sequence-normalization)
6. [Properties](#properties)
   - [Functions: Algorithms Without Properties](#functions-algorithms-without-properties)
   - [Calls Return One Value](#calls-return-one-value)
   - [Zero-Parameter Property Caching](#zero-parameter-property-caching)
   - [Algorithm Output](#algorithm-output)
   - [The Empty Sequence Value](#the-empty-sequence-value)
   - [Sequence Values and Count](#sequence-values-and-count)
   - [Output Selection](#output-selection)
   - [Dot-Call Syntax](#dot-call-syntax)
   - [Dot Members and Implicit Parameters](#dot-members-and-implicit-parameters)
   - [Misspelled Members on Known Receivers](#misspelled-members-on-known-receivers)
   - [Grace with Dot Calls](#grace-with-dot-calls)
   - [Name Resolution](#name-resolution)
7. [String Literals](#string-literals)
   - [String Equality](#string-equality)
   - [Number to String Conversion](#number-to-string-conversion)
8. [Parameters](#parameters)
   - [Collecting Explicit Parameters](#collecting-explicit-parameters)
   - [Reordering Parameters with Grace](#reordering-parameters-with-grace)
9. [Conditionals](#conditionals)
10. [Collections and Repetition](#collections-and-repetition)
    - [Inclusive Integer Lists: `range`](#inclusive-integer-lists-range)
    - [Selection: `filter`](#selection-filter)
    - [Mapping: `map`](#mapping-map)
    - [Collection Inputs](#collection-inputs)
    - [Ordering: `order` and `orderDesc`](#ordering-order-and-orderdesc)
    - [Counting: `count`](#counting-count)
    - [Membership: `contains`](#membership-contains)
    - [First Element: `first`](#first-element-first)
    - [Last Element: `last`](#last-element-last)
    - [Distinct: `distinct`](#distinct-distinct)
    - [Take Prefix: `take`](#take-prefix-take)
    - [Skip Prefix: `skip`](#skip-prefix-skip)
    - [Minimum: `min`](#minimum-min)
    - [Maximum: `max`](#maximum-max)
    - [Summation: `sum`](#summation-sum)
    - [Average: `avg`](#average-avg)
    - [Reduction: `reduce`](#reduction-reduce)
    - [Fixed Loop: `repeat`](#fixed-loop-repeat)
    - [Conditional Loop: `while`](#conditional-loop-while)
11. [Practical Examples](#practical-examples)
    - [Reusable Calculation with Parameters](#reusable-calculation-with-parameters)
    - [Returning a Sequence](#returning-a-sequence)
    - [Loop-Based Example: Sum of a List](#loop-based-example-sum-of-a-list)
    - [Fibonacci Sequence](#fibonacci-sequence)
12. [Higher-Order Algorithms](#higher-order-algorithms)
    - [Algorithm as Argument](#algorithm-as-argument)
    - [A Parameter Always Means This Call's Argument](#a-parameter-always-means-this-calls-argument)
    - [Algorithms vs. Grouped Expressions](#algorithms-vs-grouped-expressions)
13. [Spread with the Postfix Star](#spread-with-the-postfix-star)
    - [Capture Parentheses](#capture-parentheses)
    - [Repeated Spread Is Composition](#repeated-spread-is-composition)
    - [Value and Supply at a Glance](#value-and-supply-at-a-glance)
14. [Lists](#lists)
    - [Lists versus Sequence Values](#lists-versus-sequence-values)
    - [Indexing Lists](#indexing-lists)
    - [Spreading Lists](#spreading-lists)
    - [Lists in Calls and Deconstruction](#lists-in-calls-and-deconstruction)
    - [Lists and Collection Builtins](#lists-and-collection-builtins)
15. [Atoms](#atoms)
    - [Opening One Level vs. Flattening](#opening-one-level-vs-flattening)
16. [Conditional Algorithms](#conditional-algorithms)
    - [Basic Pattern Matching](#basic-pattern-matching)
    - [Nested Sequence-Value Patterns](#nested-sequence-value-patterns)
    - [The K Combinator: Ignoring a Parameter](#the-k-combinator-ignoring-a-parameter)
    - [Mixing Literals and Variables](#mixing-literals-and-variables)
    - [String Patterns](#string-patterns)
    - [Non-Exhaustive Patterns](#non-exhaustive-patterns)
17. [Loading and `open`](#loading-and-open)
    - [Loading External Algorithms](#loading-external-algorithms)
    - [`open`: Import Properties Directly](#open-import-properties-directly)
    - [Visibility](#visibility)
18. [Pitfalls](#pitfalls)
19. [Full Reference](#full-reference)
    - [Operators](#operators)
    - [Builtin Algorithms, Intrinsics, and Keywords](#builtin-algorithms-intrinsics-and-keywords)

---

## How to Use This Tutorial

If KatLang is new to you, read through [Practical Examples](#practical-examples) in order. That path introduces calculations, output, properties, parameters, conditionals, collections, and loops without requiring the advanced sections. Run the examples in the [KatLang online playground](https://katlang.org) and change their inputs to see how the result changes.

After that, continue with [Higher-Order Algorithms](#higher-order-algorithms), [Spread with the Postfix Star](#spread-with-the-postfix-star), [Lists](#lists), and [Conditional Algorithms](#conditional-algorithms) when you need those features. [Pitfalls](#pitfalls) and the [Full Reference](#full-reference) are designed for lookup rather than a first reading.

Examples labelled **Result** produce one top-level output. **Results** shows several top-level output rows in order. An example labelled **Result:** error is intentionally invalid and demonstrates a diagnostic. These labelled outputs are executable documentation: the test suite runs every labelled example and checks the displayed result (see `docs/design/executable-language-spec.md`).

Expression names in diagnostics preserve operator grouping: `(-2).f` keeps its parentheses, and `(Obj.F)(...)` distinguishes a call on a selected result from `Obj.F(...)`. The `...` in diagnostic names abbreviates arguments or a block body; it is not KatLang syntax. Parser repair suggestions also preserve Grace weights, including repeated and cancelling markers.

---

## What KatLang Is

KatLang is a language designed for calculations. Its basic computational structure is the **algorithm**: a unit of computation that can have parameters (its inputs), properties (named algorithms it owns), and output (the values its expression rows produce), and that may also declare `open` to import names. A program is itself an algorithm — the **root algorithm** — and everything you write belongs to it: the names you define with `=` are its properties, and its expression rows are its output.

You write expressions, give calculations names, and combine them:

- `2 + 3 * 4` is an expression row. It produces output.
- `Answer = 42` defines a property: a named algorithm owned by the root. It produces no output until an expression row reads it.
- `Tax = price * 0.2` defines a property with a parameter: `price` resolves to nothing, so it becomes an input that the caller supplies, as in `Tax(50)`.

**KatLang values and bindings are immutable.** Evaluating an expression produces a value that never changes afterwards, and a property binds one algorithm for good: within one scope, `A = 5` followed by `A = 6` is an error reporting that `A` is already defined, never a reassignment. Two things that may look like exceptions are not. Same-name clauses such as `Sign(1) = 100` beside `Sign(x) = 0` are valid together because they form one [conditional algorithm](#conditional-algorithms), and a nested `{ ... }` scope may declare a property that hides an outer property of the same name where the ownership rules allow it (see [Name Resolution](#name-resolution)) — that is shadowing, not reassignment. Immutability is a statement about values and bindings, not a promise that every evaluation yields the same value: separate evaluations of `Math.Random` or of a host operation may produce different values (see [Zero-Parameter Property Caching](#zero-parameter-property-caching)).

The vocabulary used throughout this tutorial:

| Term | Meaning |
|---|---|
| **Algorithm** | The basic computational structure. It can have parameters, properties, and output, and may declare `open`. The program is the root algorithm; `{ ... }` writes a nested one. |
| **Property** | A named algorithm belonging to another algorithm: `Answer = 42` makes `Answer` a property of the root. Parameters are named bindings, not properties. |
| **Function** | An algorithm with no properties of its own (see [Functions: Algorithms Without Properties](#functions-algorithms-without-properties)). |
| **Parameter** | A named input bound by a call — written in an explicit parameter list, or inferred from a name that resolves to nothing. |
| **Sequence** | An ordered value structure written with parentheses, `(1, 2, 3)`, governed by [sequence normalization](#sequence-normalization): a redundant single-item boundary disappears, so `(7)` is `7`. |
| **List** | An ordered collection written with square brackets, `[1, 2, 3]`, that keeps its boundary even when it is empty or holds one item. |
| **Item supply** | The items presented, in order, to an operation or parameter binding — output rows, call arguments, spread items. It is not a value kind of its own and has no literal. |

Algorithms and values are not interchangeable. An expression such as `42` produces a number value. A body such as `1, 2, 3` emits three output slots. Parentheses capture output slots into one sequence value, while braces create a nested algorithm with its own lexical scope.

Most simple formulas need no declared parameters — KatLang infers them. In an algorithm without an explicit parameter list, a name that resolves to nothing — no property or parameter of the algorithm or of an enclosing one, no opened name, no builtin — becomes a parameter.

The core forms are:

| Form | Meaning |
|---|---|
| `42` | One number value |
| `1, 2, 3` | Three output slots |
| `(1, 2, 3)` | One sequence value containing three items |
| `[1, 2, 3]` | One list value containing three items |
| `Total = price * quantity` | A property whose unresolved names become parameters |
| `Total(12, 4)` | An explicit call |
| `{ expression }` | A nested algorithm with its own scope |
| `value*` | Spread one sequence or list boundary into the surrounding slots |

The opening chapters focus on numbers, output slots, sequences, properties, and calls. Lists, braces, spread, and the boundary rules that connect values to item supplies are developed later.

---

## Your First KatLang Program

The simplest program is just an arithmetic expression:

<!-- spec:first-program -->
```
2 + 3 * 4
```

**Result:** `14`

Give a calculation a name and reuse it:

```
Answer = 42
Answer
```

**Result:** `42`

Names defined with `=` are called **properties**: each is a named algorithm owned by the program, and the expression row `Answer` reads it. In an algorithm without an explicit parameter list, a name that resolves to nothing is treated as a **parameter** — an input the caller must supply:

```
Tax = price * 0.2
Tax(50)
```

**Result:** `10.0`

The multiplication carries the one decimal place of `0.2`, and the default display shows the full decimal representation including trailing zeros — see [Display Decimal Places](#display-decimal-places) for controlling that. Here `price` appears without a definition, so it becomes a parameter. By convention, property names use PascalCase and parameter names use camelCase — but for physics or other specialized domains, prefer the naming that is standard in the field (e.g. `v = s / t` where `v` follows physics notation for velocity, rather than the conventional `V = s / t`).

### Comments

Use `#` to add notes. Everything from `#` to the end of the line is ignored.

```
# Full-line comment
1 + 1  # inline comment
```

**Result:** `2`

The lexical rule is permissive: a `#` outside a string literal starts a comment no matter what comes before it, so whitespace before `#` is optional — `value=6#7` assigns `6` and treats `7` as comment text. As a style matter, prefer one space before a trailing `#` and one space after it:

```
value = 6 # Explanation
```

Comments are helpful for explaining your algorithms — you'll see them throughout this tutorial.

---

## Values and Arithmetic

### Arithmetic Operators

KatLang supports the standard arithmetic operators:

```
1 + 2
10 - 3
4 * 5
```

**Results:**
```
3
7
20
```

KatLang provides two kinds of division. Regular division (`/`) keeps the fractional part; integer division (`div`) discards it. The `mod` operator returns only the remainder.

```
10 / 3
10 div 3
10 mod 3
```

**Results:**
```
3.333333333333333333333333333333333
3
1
```

Inexact quotients are correctly rounded to KatLang's 34 significant decimal digits.

`div` truncates the *exact* quotient, never a quotient that was first rounded to 34 digits. It returns the mathematical truncated integer exactly whenever that integer is representable. This includes every integer with magnitude at most 10^34, the **consecutive-integer boundary**, and sparse larger integers such as `1e35` (`1e40 div 1e5`). For finite operands and a nonzero divisor, `mod` is the exact remainder. The mathematical identity `x = y*q + r` holds when `q = x div y` is representable; evaluating `x == y * (x div y) + (x mod y)` in KatLang also requires exact multiplication and addition, as in this example:

```
X = 8999999999999999999999999999999999
X / 3
X div 3
X mod 3
X == 3 * (X div 3) + (X mod 3)
```

**Results:**
```
3000000000000000000000000000000000
2999999999999999999999999999999999
2
true
```

If the mathematical truncated integer is not representable and IEEE division remains finite, `div` drops its lower decimal digits, keeping the leading 34 digits toward zero. Its magnitude therefore never exceeds the true quotient's magnitude, for either sign: `1e40 div 7` is `1428571428571428571428571428571428000000`, while `1e40 / 7` rounds to `1428571428571428571428571428571429000000`. The exact `div`/`mod` identity is not promised for such a shortened quotient. IEEE overflow still produces signed infinity; NaN, infinity operands, signed zero, and division-by-zero errors keep their ordinary rules.

The `^` operator raises the left side to the power of the right side.

```
2 ^ 10
```

**Result:** `1024`

`^` binds tighter than the prefix `-`, so a leading minus negates the whole power — parenthesize the base to raise a negative value. The exponent side accepts a negated value directly, and `^` chains group from the right:

<!-- spec:power-unary-precedence -->
```
-2 ^ 2
(-2) ^ 2
2 ^ 3 ^ 2
```

**Results:**
```
-4
4
512
```

`2 ^ -2` is `0.25` — no parentheses are needed around a negated exponent (`2 ^ (-2)` means the same). The same rule applies to fractional exponents: `-2 ^ 0.5` negates the positive-base power (`-1.414…`), while `(-2) ^ 0.5` raises the negative base itself (a fractional power of a negative number is `NaN`).

Operator precedence follows standard math rules: `^` binds tightest, then prefix `-`, then `*`, `/`, `div`, `mod`, then `+` and `-`; the six comparison operators come next as one level (see [Chained Comparisons](#chained-comparisons)), then `not`, and `and`, `xor`, `or` bind loosest. Parentheses override precedence.

```
2 + 3 * 4
(2 + 3) * 4
```

**Results:**
```
14
20
```

### Comparison Operators

Comparisons produce the Boolean values `true` and `false`.

```
3 > 1
3 < 1
5 == 5
5 != 4
3 >= 3
2 <= 10
```

**Results:**
```
true
false
true
true
true
true
```

`==` and `!=` compare KatLang values structurally, so they also work on sequence values, not just numbers and strings. Two sequence values are equal when they have the same length and their elements are structurally equal (recursively). Values of different kinds — for example a number and a sequence value — compare unequal rather than reporting an error:

```
A = 1, (2, 3)
B = 1, (2, 3)
C = 1, (2, 4)

A == B
A == C
1 == (1, 2)
```

**Results:**
```
true
false
false
```

The ordering operators (`<`, `>`, `<=`, `>=`) and the arithmetic operators, by contrast, require numeric scalar operands, and the logical operators require Boolean operands; applying any of them to a sequence value — the empty sequence `()` included — is an error, so a comparison always produces `true` or `false` (see [The Empty Sequence Value](#the-empty-sequence-value)).

### Chained Comparisons

All six comparison operators share one precedence level and **chain**: comparison operators written one after another form a single comparison of each adjacent pair, exactly as in mathematics. `low <= x < high` means `low <= x` and `x < high`, `a < b <= c == d != e` compares `a < b`, `b <= c`, `c == d`, and `d != e`, and the whole chain is `true` only when every adjacent comparison holds. Equality and ordering mix freely, and `!=` compares adjacent pairs like every other operator — `1 != 2 != 1` is `true` (it is `1 != 2` and `2 != 1`, not "all three distinct"). Every operand is evaluated exactly once, left to right: the middle operand of `A() < B() < C()` runs once and its value serves both comparisons.

<!-- spec:comparison-chains-compare-adjacent-pairs -->
```
1 < 2 < 3
1 < 2 <= 2 == 2 != 3
1 == 1 == 1
1 != 2 != 1
1 != 1 != 1
3 < 2 < 1
1 == 1 < 2
1 < 2 == true
```

**Results:**
```
true
true
true
true
false
false
true
false
```

The last row shows that a chain never compares a Boolean *result* with the next operand: `1 < 2 == true` compares `2` with `true`, which is `false`. Parentheses end a chain, so `(1 < 2) == true` compares the Boolean value of the group and is `true`, while `1 < (2 == 2)` tries to order `1` against a Boolean and is a type error.

Like `and` and `or`, a chain is eager: a `false` comparison does not stop the later ones, so `3 < 2 < true` still performs `2 < true` and reports that comparison as an error rather than returning `false`. An error, on the other hand, ends the chain at once — the operands after it are not evaluated.

### Boolean Values

`true` and `false` are KatLang's Boolean values: a value kind of their own, distinct from numbers. They are reserved literals — they cannot be declared, shadowed, or inferred as parameters — and they display as `true` and `false`. There is no conversion between Booleans and numbers in either direction: `1` is not `true`, `0` is not `false`, and an operator or builtin that needs one kind rejects the other with a type error naming the value it was given.

```
true
not false
true == 1
true != 1
```

**Results:**
```
true
true
false
true
```

Equality is total across value kinds, so `true == 1` is simply `false`. Booleans have no ordering (`true < false` is a type error) and no arithmetic (`true + 1` is a type error).

### Logical Operators

KatLang has `and`, `or`, `xor`, and `not` for combining Boolean values. Both operands of a binary logical operator are evaluated, left to right, before the operator is applied — there is no short-circuit — and each operand must be a Boolean: `1 and 0` is a type error, never a truth test of the numbers.

```
true and true
true and false
false or true
false or false
true xor true
true xor false
not true
not false
```

**Results:**
```
true
false
true
false
false
true
false
true
```

Because comparisons return Booleans, logical operators compose naturally with them (a range test is usually clearest as one chain, `5 < x < 10`, but the two spellings are equivalent for a plain value):

```
InRange = x > 5 and x < 10
Between = 5 < x < 10

InRange(7)
InRange(3)
Between(7)
Between(3)
```

**Results:**
```
true
false
true
false
```

`not` binds less tightly than the comparisons and more tightly than `and`, `xor`, and `or` (comparisons > `not` > `and` > `xor` > `or`), so `not x > 3` negates the whole comparison — it is `not (x > 3)` — and `not a and b` is `(not a) and b`. Parentheses override the rule: `(not x) > 3` compares the negation itself, a type error for a numeric `x`. Because `not` binds so loosely, it can begin only a whole expression or an operand of a logical operator: `a == not b` and `2 ^ not x` are parse errors — write `a == (not b)` and `2 ^ (not x)`.

<!-- spec:not-binds-below-comparisons -->
```
not 5 > 3
not 2 > 3
not 5 == 5
not 5 == 4
not true == false
not true == 1
```

**Results:**
```
false
true
false
true
true
true
```

### Math Constants and Functions

KatLang provides a built-in `Math` namespace with common constants and functions.

**Constants:**
```
Math.Pi
```

**Results:**
```
3.141592653589793238462643383279503
```

The constant is correctly rounded to KatLang's full numeric precision of 34 significant decimal digits (IEEE 754 Decimal128). There is no `Math.E` constant: Euler's number is obtained through the natural exponential function, `Math.Exp(1)`.

**Single-argument functions:**

| Function | Description |
|---|---|
| `Math.Abs(x)` | Absolute value |
| `Math.Ceil(x)` | Ceiling (round up) |
| `Math.Floor(x)` | Floor (round down) |
| `Math.Sign(x)` | Sign: -1, 0, or 1 |
| `Math.Sqrt(x)` | Square root |
| `Math.Exp(x)` | Natural exponential (e raised to the power `x`; `Math.Exp(0)` is exactly `1`) |
| `Math.Ln(x)` | Natural logarithm |
| `Math.Lg(x)` | Base-10 logarithm |
| `Math.Sin(radians)` | Sine (radians) |
| `Math.Cos(radians)` | Cosine (radians) |
| `Math.Tan(radians)` | Tangent (radians) |
| `Math.Asin(x)` | Arc sine |
| `Math.Acos(x)` | Arc cosine |
| `Math.Atan(x)` | Arc tangent |

**Two-argument functions:**

| Function | Description |
|---|---|
| `Math.Round(value, digits)` | Round `value` to `digits` places after the decimal point |
| `Math.Pow(x, y)` | x raised to power y (floating-point) |
| `Math.Log(value, base)` | Logarithm of `value` in the given `base` |
| `Math.Atan2(y, x)` | Arc tangent of `y / x`, in standard atan2 argument order (`y` first, then `x`) |
| `Math.Random(start, end)` | Decimal random number in `[start; end)`, so `start <= x < end` |
| `Math.RandomInt(start, end)` | Whole-number random value in `[start; end)`, so `start <= x < end` |

`Math.Random(start, end)` and `Math.RandomInt(start, end)` both produce a value in the half-open range `[start; end)`: `start` is inclusive, and `end` is exclusive. The result follows this rule:

```
start <= result < end
```

Use `Math.Random(0, 1)` for a decimal unit-interval value where `0 <= result < 1`. Use `Math.RandomInt(1, 7)` for an integer-like dice roll where the result is `1`, `2`, `3`, `4`, `5`, or `6`. `Math.RandomInt` requires whole-number bounds within `±1e34` (the domain where every integer is exactly representable, so the draw can be exactly uniform over the interval), and the returned KatLang number is still represented as a decimal value with no fractional part. Random generation always requires both bounds. `Math.Rand`, `Math.Rand()`, and `Math.RandInt` are not valid random-generation syntax.

All math functions compute in KatLang's native IEEE 754 Decimal128 arithmetic end-to-end — there is no binary floating-point stage — so trigonometric, logarithmic, root, and power results carry up to 34 significant decimal digits. For example, `Math.Sin(1)` returns `0.841470984807896506652502321630299` rather than a value cut off near 16 digits. Two consequences of this honesty are worth knowing:

- Results are no longer snapped toward "nice" values. `Math.Pi` is π rounded to 34 digits (a hair above the true π), so `Math.Sin(Math.Pi)` returns the tiny residual of that rounding (about `-1.158e-34`), not `0`. `Math.Sin(0)` is still exactly `0`.
- An exact result stays clean wherever the function lands on it exactly — arithmetic, square roots, base-10 logarithms of powers of ten, and integer powers: `Math.Lg(1000)` is `3`, `Math.Sqrt(144)` is `12`, and `2 ^ 10` is `1024`. The two-argument `Math.Log(value, base)` divides two rounded logarithms, so it can land one unit away from an exact value (`Math.Log(9, 3)` is `1.999999999999999999999999999999999`); for base 10 use `Math.Lg`, which is not the same computation as `Math.Log(x, 10)`.

Domain violations follow IEEE 754 rather than raising errors: `Math.Sqrt(-1)` and `Math.Ln(-1)` return `NaN`, and `Math.Ln(0)` returns `-Infinity`. Division and modulo by a zero-valued divisor remain ordinary KatLang errors — the check applies to the evaluated value, so `1 / 0`, `1 / (1 - 1)`, and `1 / -0` all report the same division-by-zero diagnostic. The same policy covers a negative power of zero, which is reciprocal-like: `0 ^ -1`, `0 ^ -0.5`, and `Math.Pow(0, -2.5)` are all the error `zero cannot be raised to a negative exponent` rather than `Infinity` — whether the exponent is an integer makes no difference. Zero and positive exponents keep their ordinary results (`0 ^ 0` is `1`, `0 ^ 0.5` is `0`).

```
Math.Sqrt(144)
Math.Abs(-7)
Math.Floor(3.9)
Math.Sin(Math.Pi / 2)
Math.Log(100, 10)
```

**Results:**
```
12
7
3
1
2
```

### Reproducible random values

`Math.Random` and `Math.RandomInt` (and their aliases `random` and `randomInt`) are nondeterministic by default: each run initializes its stream from fresh entropy, so the same program may print different values between runs. A host can instead SEED one evaluation — `RunOptions.RandomSeed` in the .NET library, or `--random-seed <integer>` on the CLI's `run` and `eval` commands — and then, for a given KatLang version, the same program with the same seed reproduces the same random values on every supported platform:

```
katlang eval "Math.RandomInt(1, 7), Math.Random(0, 1)" --random-seed 42
```

Seeding is host configuration only: KatLang source has no seeding syntax, and a property named `RandomSeed` is an ordinary property that seeds nothing.

A seed reproduces a *stream*, not individual calls: both random operations, in every spelling, draw from one stream in evaluation order, so the values a call receives depend on which random calls executed before it. The ordinary evaluation rules decide that — arguments evaluate left to right and exactly once, only the selected branch of `if` runs, a zero-parameter property read as a value (`A`, `A.sum`, `F(A)`) is drawn once and reused while an explicit `A()` and every builtin value slot that demands the algorithm directly (`sum(A)`, `if(true, A, 0)`, `A.string` — see [Zero-Parameter Property Caching](#zero-parameter-property-caching)) draw again, callbacks draw in sequence order, and the output rows draw before a `DisplayDecimals` property is evaluated. Removing an earlier random call therefore generally changes the later values. Unseeded evaluation stays nondeterministic, and KatLang randomness is not cryptographically secure.

### Lowercase Math Aliases

Every `Math` member also has one predefined lower-camel-case prelude binding, so ordinary formulas can drop the `Math.` prefix:

```
cos(0.123)
sin(pi / 2)
round(sqrt(2), 10)
```

**Results:**
```
0.9924450321351935702938185222573315
1
1.4142135624
```

The complete alias table:

| Canonical | Alias | Canonical | Alias |
|---|---|---|---|
| `Math.Pi` | `pi` | `Math.Cos(radians)` | `cos(radians)` |
| `Math.Exp(x)` | `exp(x)` | `Math.Acos(x)` | `acos(x)` |
| `Math.Abs(x)` | `abs(x)` | `Math.Tan(radians)` | `tan(radians)` |
| `Math.Ceil(x)` | `ceil(x)` | `Math.Atan(x)` | `atan(x)` |
| `Math.Floor(x)` | `floor(x)` | `Math.Atan2(y, x)` | `atan2(y, x)` |
| `Math.Round(value, digits)` | `round(value, digits)` | `Math.Pow(x, y)` | `pow(x, y)` |
| `Math.Sign(x)` | `sign(x)` | `Math.Log(value, base)` | `log(value, base)` |
| `Math.Sqrt(x)` | `sqrt(x)` | `Math.Random(start, end)` | `random(start, end)` |
| `Math.Ln(x)` | `ln(x)` | `Math.RandomInt(start, end)` | `randomInt(start, end)` |
| `Math.Lg(x)` | `lg(x)` | | |
| `Math.Sin(radians)` | `sin(radians)` | | |
| `Math.Asin(x)` | `asin(x)` | | |

An alias binding points to the SAME function, not a copy: `pi` points to `Math.Pi`, and `sin(radians)` computes exactly `Math.Sin(radians)` with the same parameters, precision, domain behavior, and errors. `Math.X` remains the canonical qualified spelling; the aliases are synthetic ordinary prelude bindings resolved by the ordinary name-resolution rules:

- Your own definitions win. A local property `sin(x) = x * 10`, an explicit parameter `F(sin) = ...`, or an ancestor definition shadows the alias, and your `sin` behaves like any ordinary callable. The prelude is the outermost owner in the [owner walk](#name-resolution), so a parameter shadows an alias from a nested body exactly as from its own body.
- The aliases are prelude bindings, not members of `Math`: `Math.cos(1)` is still invalid — inside `Math` only the canonical PascalCase names exist.
- `open Math` still exposes only the canonical PascalCase names (`Cos`, `Pi`, ...); it is never needed for the aliases and is not implied by them.
- Aliases work everywhere ordinary names work: as values (`K = cos` infers `K(radians)`), through dot-call fallback (`v.cos` is `cos(v)`), and as higher-order references (`Apply(cos, 0)`).

**Compatibility note:** because the alias names are now part of the prelude vocabulary, a bare `pi`, `exp`, `abs`, `ceil`, `floor`, `round`, `sign`, `sqrt`, `ln`, `lg`, `sin`, `asin`, `cos`, `acos`, `tan`, `atan`, `atan2`, `pow`, `log`, `random`, or `randomInt` that previously did not resolve to anything is no longer inferred as an implicit parameter — it resolves to the Math alias instead. For example, a free `pi` such as `F = pi + 1` now means `Math.Pi + 1`. (`e` and `Math.E` are NOT part of this vocabulary: the Euler constant was replaced by the `Math.Exp` / `exp` function, so `e` is an ordinary identifier.) Explicit parameters remain valid and shadow the aliases normally:

```
F(pi) = pi + 1
F(5)
```

**Result:**
```
6
```

**Style:** prefer the lowercase aliases in ordinary formulas, keep `Math.X` as the qualified form for disambiguation (for example next to a local definition of the same name), and use one spelling style consistently within an example.

### Display Decimal Places

Define the top-level property `DisplayDecimals` to control how many digits after the decimal point are shown for decimal values in final displayed output:

```
DisplayDecimals = 6

Math.Pi
Math.Exp(1)
```

**Results:**
```
3.141593
2.718282
```

`DisplayDecimals` is display-only. It does not round stored values, intermediate calculations, comparisons, or cached property results. A displayed value that falls exactly halfway between two candidates rounds AWAY FROM ZERO, the same rule as `Math.Round` (`0.125` shows as `0.13` at two places, `2.5` as `3` at none, `-2.5` as `-3`), so the digits you see are the digits `Math.Round(value, DisplayDecimals)` would compute:

```
DisplayDecimals = 2

A = Math.Pi

A
A * 1000
```

**Results:**
```
3.14
3141.59
```

`DisplayDecimals` is still an ordinary readable property, so KatLang code can refer to it like any other property:

```
DisplayDecimals = 6

DisplayDecimals
DisplayDecimals + 1
```

**Results:**
```
6
7
```

Formatting applies recursively to numeric leaves in displayed structures:

```
DisplayDecimals = 2

(Math.Pi, Math.Exp(1))
```

**Results:**
```
(3.14, 2.72)
```

`DisplayDecimals` must be a single integer from 0 through 99. Negative values, fractional values, strings, and sequence-valued or multi-output values are reported as diagnostics.

A host can also supply a DEFAULT for programs that do not define `DisplayDecimals` — `RunOptions.DefaultDisplayDecimals` in the .NET library, or `--display-decimals <integer>` (0 through 99) on the CLI's `run` and `eval` commands:

```
katlang eval --display-decimals 3 "1 / 7"
```

This shows `0.143`. Your program's own `DisplayDecimals` always takes precedence: with `DisplayDecimals = 6` in the source, the same command shows `0.142857`, and an invalid `DisplayDecimals` is still reported as a diagnostic rather than replaced by the default. The default is not a property — your code cannot read it, and it never shadows or collides with your names — and, like `DisplayDecimals`, it changes only how the final output is displayed.

Per-value formatting such as `value.displayDecimals(n)` and `displayDecimals(value, n)` is intentionally not part of this feature. Structured display settings such as `Display = { Decimals = n }` and `Display.Decimals = n` are also intentionally out of scope.

---

<a id="multiple-outputs"></a>

## Output Rows and Sequences

> **Core idea:** commas and output rows create separate slots; whitespace alone never does. Parentheses capture slots into one sequence value; square brackets capture them into one list value.

An algorithm's output is written as expression rows, and one row may hold several comma-separated slots. Each top-level slot is one output of the program:

<!-- spec:supply-three-rows -->
```
10, 20, 30
```

**Results:**
```
10
20
30
```

The result window displays multiple top-level outputs on separate visual rows for readability. Those visual rows are presentation only; they do not create semantic groups. Parentheses create sequence values.

KatLang puts complete expressions next to each other with expression lists. A comma — or a new line, where the context keeps the list open — creates separate slots; parentheses materialize those slots as one sequence value. Whitespace alone never separates two slots, and semicolon is not expression syntax.

```
1 + 1
2 + 2
3 + 3
```

**Results:**
```
2
4
6
```

The same program can be written `1 + 1, 2 + 2, 3 + 3`; both spellings produce three expression-list slots (`1 + 1 2 + 2 3 + 3`, with only whitespace between the slots, is a parse error). Use parentheses when you want one sequence value:

<!-- spec:value-three-items -->
```
(1 + 1, 2 + 2, 3 + 3)
```

**Result:** `(2, 4, 6)`

The same expression-list rule applies inside brace bodies:

```
{
    1, 2
    3
}
```

This is equivalent to `{ 1, 2, 3 }`: all three items are expression-list slots (`{ 1, 2 3 }` is a parse error, because nothing separates `2` from `3`). Parentheses materialize an expression list as one sequence value, so `(1, 2)` is one sequence value. Call syntax consumes expression lists as argument slots, so `F(A, B)` is the two-argument call.

**Same-line slots need a comma.** A second complete expression on the same physical line as a closed expression, with nothing but whitespace between them, is a parse error — never a silent second slot. `1 2`, `F(1 2)`, `(1 2)`, `[1 2]`, `2(3)`, `2m`, `2pi`, `A[1]`, and `sqrt 2` are all rejected with one diagnostic that names the three repairs: add `,` to separate slots, add an operator to continue the expression, or start a declaration on a new line. The parser recovers by keeping the second item as the next slot of the same list, so later diagnostics stay useful, but the program is invalid. Parameter patterns require commas even across line breaks: `F(a b) = a + b` is rejected at `b` — inside a parameter list the comma is the only repair, and the diagnostic says so — and the parser recovers it as `F(a, b) = a + b`, so the definition keeps both parameters and its body. Whitespace never splits tokens either: `ab` stays one identifier and `12` stays one number.

Whitespace inside one expression is formatting, not structure. A token that continues the current expression — a binary operator, a call argument delimiter, `:`, `.`, or an attached marker — continues it, and only then does the parser ask whether a new slot begins; `F(1 -2)` is therefore the one argument `1 - 2`, and `F(1, -2)` is the two-argument call. You may write whitespace between a callable name and its argument list:

<!-- spec:adjacency-call-across-space -->
```
Add(a, b) = a + b

Add(1, 2)    # 3
Add (1, 2)   # the same call, 3
```

A physical newline never continues a closed expression into a call. A line that starts with `(` or `{` is its own output row, never call arguments for the previous line:

```
Add(a, b) = a + b

Add
(1, 2)       # not a call: expression-list slots `Add, (1, 2)`
```

For a multiline call, open the delimiter before the newline — an already-open argument list spans lines normally:

```
Add(a, b) = a + b

Add(
  1, 2
)            # the call Add(1, 2): 3
```

The same applies to dot calls and callback braces: `A.B (1)` is the dot call `A.B(1)` and `values.map { n * 2 }` is `values.map{n * 2}`, but `A.B` followed by `(1)` on the next line is the expression list `A.B, (1)`, and `values.map` followed by `{ n * 2 }` on the next line is not a callback call (write `values.map{` and break inside the braces instead). This is only about same-line whitespace between the callee and its delimiter — inside the argument list every same-line slot still needs its comma (`Add (1, 2)` is the call; `Add (1 2)` is a parse error). Comma and a newline both keep separate slots: `F, (1)` and `F` followed by `(1)` are expression-list structure. Non-callable targets never become calls: `2 (3)` is neither a call nor multiplication, it is the same missing-separator error as `2(3)`.

Postfix indexing follows the same line rule: `Pair:0`, `Pair :0`, and `Pair : 0` all index on the same line, but a `:`-led line never continues the previous expression — it is a parse error rather than a silent continuation, so `P = Pair` followed by a line `:0` does not define `P = Pair:0`. Postfix grace `~` is same-line only in the same way: `A~, B` graces `A` before the slot `B` (`A~B` without the comma is the missing-separator error), while `A` followed by a line `~B` keeps `A` ungraced and parses `~B` as its own prefix-grace row. Binary operators follow the rule too: an operator-led line never continues the previous expression, so `A` followed by a line `-1` is the expression list `A, -1`, never the subtraction `A - 1` — put the operator at the end of the line (`A -` then `1` on the next line) when you want the arithmetic to continue. A trailing `*` is no exception, and it does not matter whether it is spaced: `A *` and `A*` at the end of a line both continue as the multiplication `A * B` onto the next line whenever that line begins with a right operand. Only where no operand can follow — before a comma, a closing delimiter, the end of the program, or a definition — is the star the spread marker, and then it must be written attached: `A*` spreads, while a detached `A *` in that position is an error (see [Spread with the Postfix Star](#spread-with-the-postfix-star)). Comments never change any of these decisions: `A # note` followed by `-1` parses exactly like `A` followed by `-1`. Leading-dot lines are the one intentionally supported continuation: a line starting with `.` continues the dot-call chain, so method-chain layout works as long as each argument delimiter stays on the same line as its member name:

```
(1, 2, 3)
.map { n * 2 }
.sum         # 12
```

The newline boundary keeps definition boundaries predictable: a `(`- or `{`-led line after a definition body is a following output row, never call arguments appended to that body:

```
Sum(vector) = vector.sum
(1, 2).Sum         # separate report row: 3
```

A leading semicolon after a definition body is invalid and produces a diagnostic. During error recovery the parser may still attach the following expression to the current body so later diagnostics stay useful, but that recovery is not valid KatLang syntax — semicolon is never an expression operator.

Comma is the explicit expression-list separator, and on one physical line it is the only one: `a b` is a parse error, `a, b` is two slots. A newline is a different mechanism — a body, statement, or output boundary — so it does not extend an expression list across lines unless the syntax explicitly keeps the context open (for example an open `(`/`[`/`{`, a trailing comma, a same-line trailing binary operator, or a leading `.`); where the context is open, a newline between two closed expressions separates slots without a comma. Expression spreading uses the postfix spread marker `value*`; a `*` followed by a valid right operand — on the same line or on the next — is instead the multiplication operator regardless of spacing, so a comma is required between a spread and a following item (`a*, b`, or `a*,` newline `b` — both `a* b` and `a*` newline `b` are the product `a * b`). The prefix `*` in a binding pattern is the collect marker: it must be directly attached to its binding name in a parameter or deconstruction pattern (`*name`; `* name` is an error), and it is not an expression operator.

A definition body ends at the end of its line, and a declaration must begin a line (or be the first item after an opening `{`): `x = 1 y = 2`, `1 P = 3`, and `{ d = 2 n * d }` are parse errors, so a forgotten line break can never silently move a declaration or an expression into the preceding definition's body. Start a new line after a definition body for the next declaration or output row.

A simple definition or deconstruction head stays on one physical line. A clause head's name and `(` share a line, and its closing `)` and `=` share a line; the pattern list inside the open parentheses may span lines. These boundaries prevent retroactive declarations, so a newline never assembles a head after the fact: `Foo` followed by a line `(x) = x + 1` is the output row `Foo` and then a stray `=` (a parse error that names this rule), never the clause `Foo(x) = x + 1`; `A` followed by a line `= 1`, `Foo(x)` followed by a line `= x + 1`, and `x, y` followed by a line `= 1, 2` are rejected the same way, with or without a comment or indentation at the boundary. Explicit continuation after a recognized head is still fine: the body may begin on the line after the `=` (`A =` then `1` defines `A = 1`, exactly like the operand of a trailing operator), a clause head's pattern list may span lines inside its parentheses (`F(a,` then `b) = a + b`), and a trailing `.` continues a dot chain onto the next line (`a.` then `b` is `a.b`). Such a continuation only ever continues into an expression: when a line ends waiting for more (`1 +`, `x,`, `A =`, `a.`) and the next line begins a declaration (`Good = 41`), the parser reports the incomplete line at its dangling token and keeps the declaration as written.

At root output, you can mix commas and newlines freely:

```
1 + 2, 2 + 3
3 + 4
```

**Results:**
```
3
5
7
```

Use parentheses when sequence-valued output intent is clearer:

```
(1 + 2, 2 + 3, 3 + 4)
```

**Comma vs. parentheses vs. spread:** these serve different purposes.

| Syntax | Meaning |
|---|---|
| `1, 2` | Two top-level comma outputs |
| `(1, 2)` | One sequence value containing `1` followed by `2` |
| `1 2` | Parse error: two slots on one line need a comma — write `1, 2`, or put `2` on its own line |
| `X*` | Spread expression: open one item boundary of the evaluated value and contribute the items to the surrounding slot context |
| `X*, 2` | Spread then a separate expression-list slot — the comma is required, because `X* 2` is the multiplication `X * 2` |
| `X * 2` (any spacing, even across a line break) | Multiplication: a `*` followed by a valid right operand always multiplies — `X*2`, `X* 2`, `X *2`, `X * 2`, and `X*` followed by a line `2` are the same product |
| `*name` in a binding pattern | Collecting binding: collect the matched supply into one exact list |

Commas and permitted newline boundaries create expression lists. Root output consumes a bare expression list as output slots, call syntax consumes it as argument slots, parentheses materialize it as one sequence value, and square brackets materialize it as one [list value](#lists). Semicolon is not an expression separator; use commas (or separate lines) for separate slots or parentheses for one sequence value. A spread expression is one whole slot: `A, B*, C` is an expression list of three slots — the comma before `B*` is required like every same-line comma (`A B*` is the missing-separator error), and the comma after the spread is required for a second reason too, because `B* C` would be the multiplication `B * C`. Written slots stay structural (`F(a*, b)` has two written slots; its supplied argument count depends on a's spread items). Physical line breaks do not create sequence-value boundaries. Explicit parentheses do:

```
1, (2, 3)    # two slots: 1 and (2, 3)
(1, 2), 3    # two slots: (1, 2) and 3
(1, 2, 3)    # one sequence value
(1, 2, 3)    # (1, 2, 3)
```

Comma creates multiple top-level output slots; parentheses create one sequence-valued slot. The result window may show comma slots on separate rows, while sequence values display as sequence values. See [Spread with the Postfix Star](#spread-with-the-postfix-star).

A spread expression `x*` is the spread of `x` followed by nothing: the star is the spread marker only when no right operand can follow it, and it is then written directly attached to `x` (a detached `x *` with nothing to multiply is an error, not a spread). When a valid right operand does follow — spaced or not, on the same line or on the next — the star is multiplication: `x*y`, `x* y`, `x *y`, `x * y`, and `x*` newline `y` are all the product `x * y`. To spread and then supply another item, the comma is required: `x*, y`, or `x*,` at the end of the line with `y` on the next. Use parentheses, such as `(x*, y)`, when the spread value and the following expression should form one sequence value.

Flat fixed calls preserve expression boundaries. A property reference used as one argument is one argument expression, even if that property evaluates to multiple outputs. KatLang does not implicitly unpack one argument expression to satisfy additional fixed parameters; use separate arguments, explicit indexing (`value:i`), or an explicit spread (`value*`) where that is the intended shape.

```
Pair = 10, 20
Add(x, y) = x + y

Add(Pair)           # bad arity: one argument expression
Add(Pair:0, Pair:1) # 30

Tail = 2, 3
Use(a, b, c) = a + b + c

Use(1, Tail)    # bad arity: two argument boundaries
Use(1, Tail*) # 6: Tail* spreads its items into the b and c slots
Use(1*, Tail)  # bad arity: spreading the scalar 1 yields one item, so only two argument slots
```

### Sequence Normalization

A **sequence** is an ordered value structure, and parentheses are how you write one: `(1, 2, 3)` is one sequence value holding three items, and `()` is the empty sequence. KatLang builds sequences directly from expression lists; there is no tuple type to declare. What distinguishes sequences from [lists](#lists) is **sequence normalization**, the rule that produces the canonical form of a sequence whenever a value is constructed or captured. Normalization removes every redundant unary sequence boundary — a sequence boundary around exactly one item — at every nesting depth, including around sequence elements stored inside a list. It never removes a list boundary, and it never merges a boundary that holds two or more items. Because `(7)` and `7` are the same value, a sequence of exactly one item does not exist; a visibly wrapped single item is what lists are for.

```
(7)
((1, 2))
(1, (2, 3))
(1, ((2, 3)))
[7]
[[7]]
[(7)]
[((1, 2))]
(1, (), 2)
((), ())
```

**Results:**
```
7
(1, 2)
(1, (2, 3))
(1, (2, 3))
[7]
[[7]]
[7]
[(1, 2)]
(1, (), 2)
((), ())
```

Read the rows in pairs. `(7)` is the number `7`, and the redundant outer boundary of `((1, 2))` disappears, leaving the two-item sequence `(1, 2)`. Meaningful nesting stays: `(1, (2, 3))` keeps its inner pair, and `(1, ((2, 3)))` loses only the redundant boundary around that pair. List boundaries always survive — `[7]` and `[[7]]` stay as written — while normalization still reaches the sequence elements a list stores: `[(7)]` is `[7]` and `[((1, 2))]` is `[(1, 2)]`. Finally, the empty sequence is an item like any other, so `(1, (), 2)` and `((), ())` keep their visible empty items: normalization removes boundaries, never items.

Sequence normalization is not recursive flattening, sorting, deduplication, or list-boundary removal. It is the reason grouping parentheses are harmless around a single value — `(2 + 3) * 4` groups without creating a sequence — and the reason a call or property read that produces exactly one item hands back that item rather than a one-item wrapper (see [Calls Return One Value](#calls-return-one-value)). When a single item or an empty collection must stay visibly wrapped, use a [list](#lists).

---

## Properties

> **Core idea:** a property definition gives an algorithm a name but does not itself produce output. Expression rows produce output; reading or calling a property crosses a one-value boundary.

A **property** is a named algorithm belonging to another algorithm, its owner. You define one with `=`: the root owns the properties written at the top level, and a `{ ... }` body owns the properties written inside it. A property need not be parameterless, public, or reachable from outside its owner — `Tax = price * 0.2` and `Area(r) = r * r` are properties just as `Answer = 42` is. Keep the property apart from the value obtained by evaluating it: `Answer` names an algorithm, and an expression row that reads `Answer` evaluates it to the value `42`. By convention, property names use PascalCase.

<!-- spec:property-access-and-call -->
```
# Define a property:
Answer = 42

# Property-style access:
Answer

# Explicit zero-parameter call:
Answer()
```

**Results:**
```
42
42
```

### Functions: Algorithms Without Properties

KatLang uses **function** for one structural special case: an algorithm that owns no properties. The criterion is ownership alone. How many parameters an algorithm has, whether it returns a number or a sequence, how many output items it emits, whether it is written with braces, and whether its parameters are explicit or inferred play no part in the classification. Reading a property of an enclosing algorithm, or calling another algorithm, does not make that property belong to the caller, so a body full of calls is still a function as long as it declares no properties of its own.

```
F(x) = (x + 1)^2

G(x) = {
    Y = x + 1
    Y^2
}

F(3)
G(3)
```

**Results:**
```
16
16
```

`F` and `G` are both properties of the root algorithm, and both calls produce the same result. `F` is a function: it owns no properties. `G` owns the property `Y`, so `G` is an algorithm outside the special case. `Y` is a property of `G` and is itself a function — it owns nothing and reads `G`'s parameter `x`. Because `Y` depends on that parameter it is local-only, so `G.Y` is refused outside `G`, exactly like `Outer.Inner` in [A Parameter Always Means This Call's Argument](#a-parameter-always-means-this-calls-argument) (the rule is stated under [Visibility](#visibility)). "Property" and "function" describe different aspects of one algorithm: `F` is both a property of the root and a function, and a brace algorithm such as `{ a + 1 }` is a function too, because it declares no properties.

Owning properties changes nothing about what an algorithm can do. `G` is called exactly like `F`, and it can be passed to a higher-order algorithm or used as a callback just as `F` can:

```
G(x) = {
    Y = x + 1
    Y^2
}
Apply(f) = f(3)

Apply(G)
[1, 2].map(G)
```

**Results:**
```
16
[4, 9]
```

A few ownership checks keep the labels consistent. A deconstruction such as `a, b = 1, 2` declares the properties `a` and `b`, so the algorithm containing it is outside the special case. A clause family such as `Sign(1) = 100` beside `Sign(x) = 0` is a **conditional algorithm** whatever its branches contain; do not call it a function when any branch body declares a property. An `open` declaration makes imported names visible without making those properties belong to the opener. The ordinary builtin callables and the `Math` members own no properties and are functions, while `Math` itself is an algorithm with properties. Apply the criterion to the algorithm you are describing, never to declarations inside another algorithm it calls or contains.

This is KatLang's structural use of the word. Mathematically, `F` and `G` describe the same function from `x` to `(x + 1)^2`, and nothing here forbids local helper calculations; the label only records whether an algorithm owns named algorithms of its own.

### Calls Return One Value

A property/call boundary is a **value boundary**: it always returns exactly one value. A body may internally produce an item supply — comma slots, newline rows, or a body spread — but when you *call* it (or access a property, or invoke a builtin), the caller receives a single value. If the body produced several items, that value is a sequence containing them. To contribute its items back into the surrounding item supply, append the spread marker at the call site: `value*`. Python is similar in one respect: `return 1, 2, 3` hands back one tuple rather than three separate results. The KatLang value is a sequence, though, shaped by [sequence normalization](#sequence-normalization) rather than by tuple rules, so the comparison ends there.

<!-- spec:call-value-boundary -->
```
F(*a) = a
F(5, 9)
F(5, 9)*
```

**Results:**
```
[5, 9]

5
9
```

The body's internal shape is preserved inside the returned value — only the boundary count changes. Here the collecting parameter collected the two supplied arguments as the exact list `[5, 9]`, and that list is the call's one returned value. `F(*a) = a, 0` returns `([5, 9], 0)` (the collected list stays one nested value), while `F(*a) = a*, 0` returns `(5, 9, 0)` (the body spread supplies the list items first). Either way the call returns **one** value; spread at the call site is the only way to re-spread it.

Two boundary cases follow from the same rule. The empty sequence value is a real value, so a body whose output is `()` returns exactly that. A body with no output rows has nothing to return: calling it, or reading it as a value, is an error — never a silent `()`:

```
Empty = ()
Empty()
```

**Result:** `()`

A returned `()` stays visible wherever an ordinary, non-spread slot receives it — an output row or a call argument keeps it as one item. A [collecting parameter](#collecting-explicit-parameters) also keeps it: `Coll(())` collects `[()]`. Omitting the argument or explicitly spreading an empty value supplies zero items:

```
Coll(*xs) = xs
Coll(())
Coll()
Coll(()*)
```

**Results:**
```
[()]
[]
[]
```

An ordinary output slot keeps the empty value as well:

```
E = ()
(1, E(), 2)
(1, E(), 2).count
```

**Results:**
```
(1, (), 2)
3
```

```
Nothing = {}
Nothing()
```

**Result:** error — `Nothing` has no defined output, so there is no value for the call to return (see [The Empty Sequence Value](#the-empty-sequence-value)).

The same rule governs collection-producing builtins, with one refinement: `order`, `orderDesc`, `distinct`, `take`, `skip`, `filter`, `map`, `range`, and `atoms` each materialize their result as one [list value](#lists); an explicit spread opens it.

```
X = 1, 2, 3
X.order
X.order*
```

**Results:**
```
[1, 2, 3]

1
2
3
```

Three things are intentionally **not** value boundaries and keep emitting multiple top-level items: root program output (`1, 2, 3` still shows three rows), explicit caller-site spread (`value*`), and the multi-slot loop state of `while`/`repeat` — a step's several output slots become the next iteration's separate state slots, and the finished loop hands its final slots to the surrounding context the same way (`Step.repeat(1, 0, 0)` with `Step = a + 1, b + 1` shows two root rows, while `R = Step.repeat(1, 0, 0)` captures them as the one value `(1, 1)`). Scalar/reduction builtins (`count`, `sum`, `avg`, `min`, `max`, `contains`, `first`, `last`, `reduce`) already return one value and are unchanged. A `map`/`reduce` callback must still return exactly one element; a multi-output callback body is an error, not a silently-grouped value.

What a call returns is a separate question from how a dot-call receiver is handed to the callee's parameters, and the answer there is the same kind of rule: **dot-call passes a value**. In an ordinary lexical dot call the receiver is one ordinary leading argument — `R.F(args)` is exactly `F(R, args)` — so a fixed parameter binds it whole and a collecting parameter collects it as ONE item exactly as it would collect the written argument (a sequence and a list alike), while only the spread marker (`R*.F(args)`, which is `F(R*, args)`) hands over the receiver's items (see [Dotted Receivers and Collecting Parameters](#dotted-receivers-and-collecting-parameters)). The value boundary described here is about what the call itself produces.

### Zero-Parameter Property Caching

When a body always produces the same value, both forms show that value, but the call shape controls reuse. During one evaluation run, repeated property-style reads of the same self-contained zero-parameter property reuse its first successful result:

```
Fun = 1 + 2
Fun, Fun
```

When each fresh evaluation of the body may produce a different value — a random draw, or a host operation — property-style access and explicit calls are different:

```
Fun = Math.Random(0, 1), Math.Random(0, 1)

Fun, Fun     # property-style access: the same pair is reused
Fun(), Fun() # explicit calls: the body is evaluated again for each call
```

`Fun()` bypasses the zero-argument cache for `Fun` itself. It does not recursively force property-style references inside `Fun` to bypass their own caches. To request fresh nested values, write those nested calls explicitly with `()`:

```
A = Math.RandomInt(0, 10)

B = A, A        # uses cached/property-style A access
C = A(), A()    # explicitly asks for fresh A values

B()             # re-evaluates B's body; the property-style A inside it reuses A's cached entry
C()             # re-evaluates C, and A() is fresh because it is explicit
```

Here `A` is self-contained — its value depends on no caller input — so within one evaluation it has exactly one cached entry: whichever read comes first stores it, and every later property-style read of `A` in that evaluation reuses it, including the reads inside a second `B()` call. Both `B()` calls therefore show the same pair. That reuse is a promise about ONE evaluation and about self-contained properties; it is bounded in two ways:

- **Per evaluation.** Every independent evaluation (each `KatLangEngine.Run` or `RunAsync`, each CLI invocation) starts with an empty cache. Nothing is remembered between two evaluations of the same program: zero-argument cache state never survives between evaluations, ordinary unseeded evaluations receive independent nondeterministic random streams (so `B()` in one evaluation and `B()` in the next draw independently), and two evaluations deliberately given the same seed replay the same stream — see [Reproducible random values](#reproducible-random-values).
- **Per binding context for local-only properties.** A property whose value captures an enclosing input — a parameter of the algorithm that declares it, or the pattern binder of an enclosing branch — is cached only within its current binding context. Separate calls, callbacks, and loop iterations of the enclosing algorithm are separate contexts even when their argument values are equal, and an explicit call such as `B()` opens a new context for the local-only properties that `B`'s body reads. Returning restores the caller's context and its cached values. Evaluating an algorithm argument without binding parameters keeps the current context; rebuilding a lookup record alone does not create a new cache scope.

So "the property-style `A` inside `B` is reused" holds for the self-contained `A` above. For a local-only `A` it does not: each explicit `B()` re-draws it, while property-style reads of `B` in one context still share one pair.

```
F(x) = {
    A = Math.RandomInt(0, 10) + x    # captures x: local-only
    B = A, A
    B, B                             # property-style reads in one context: the same pair twice
    B(), B()                         # each explicit call opens a new context: A is drawn afresh in each
}
```

A self-contained (exported) zero-parameter property, by contrast, keeps its first successful property-style result for the whole evaluation — across calls, callbacks, loop iterations, and both structural and `open` access to that declaration.

```
Big = range(1, 100000).sum          # self-contained: computed once for the whole program
F(x) = Big + x                      # every call of F reuses the same Big
Scaled(k) = {
    Base = k * 10                   # captures k: computed once per call of Scaled
    Base + Base
}
range(1, 2000).map(F).count, Scaled(2), Scaled(10)
```

**Results:**
```
2000
40
200
```

The same rule applies when fresh evaluations may differ: `A = Math.RandomInt(0, 10)` read property-style from several calls of one algorithm yields the same draw in all of them during one evaluation, while every explicit `A()` is a fresh evaluation that may produce a different draw. A value that has been produced never changes; a new evaluation produces a new value.

Host-backed properties follow the same rule. Every independent evaluation starts with an empty cache. Errors and interrupted property evaluations are not cached; a successful nested property's entry remains available if an enclosing evaluation fails and the program continues. An explicit call neither reads nor replaces that property's cached entry.

A recursive read entered before any result is stored still evaluates the body. The first successful completion supplies the cache entry; reads already in progress finish with their own results and do not replace it.

The guarantee concerns property-value reads: a bare `A` in value position, `A + 0`, `A == A`, a list element `[A]`, a user call argument `F(A)` (and its dotted spelling `A.F`, which is the same call), all read A's cached value. Passing a name as an ALGORITHM argument follows the receiving callable's rules instead, and every builtin VALUE slot demands the algorithm directly rather than reading the property: `if(true, A, 0)`, the collection arguments `sum(A)`, `count(A)`, `take(A, n)`, `first(A)`, `atoms(A)`, `range(A, A)` — in the dotted spelling exactly as in the written one, because `A.sum` IS `sum(A)` — a loop's initial state and `repeat` count, the `reduce` initial accumulator, and the `.string` receiver (`A.string`) each evaluate A's body again and neither read nor store its entry. Parentheses change none of this, because parentheses group syntax and never introduce a boundary: `(A)` is `A`, so `if(true, (A), 0)`, `sum((A))`, `(A).sum`, and `(A).string` are the same direct demands as their bare spellings. Where a property draws randomness or calls a host operation this is observable — `sum(A)`, `sum((A))`, and `A.sum` all draw again, while `A == A` compares one cached draw with itself — so read such a property through a genuine value position (for example a helper property `V = A`, whose own demand reads `A` from the cache: `V.sum` reuses A's draw). (Whether a builtin's value slot should read the cache at all is a documented open design question; today every spelling of a builtin call agrees, grouped or not.)

A property body may produce several items, but property-style access is a value boundary: the caller observes them as one sequence value. Caller-site spread (`value*`) turns that value back into separate output rows:

<!-- spec:property-value-boundary -->
```
Coordinates = 10, 20
Coordinates
Coordinates*
```

**Results:**
```
(10, 20)

10
20
```

### Algorithm Output

An expression row in an algorithm body contributes its result to the algorithm's output. An algorithm may also define no output at all.

```
A = 3
B = 2
A + B
```

**Result:** `5`

Here `A` and `B` are property definitions; the expression row `A + B` is the algorithm's output.

Output rows and property definitions may be interleaved — an output row does not need to appear after all property definitions, because property resolution uses the complete property set of the algorithm, not textual order:

<!-- spec:output-rows-interleave-definitions -->
```
A = 3
A + B
B = 2
```

**Result:** `5`

`Output` and `output` are ordinary identifiers with no special meaning. `Output = A + B` is a regular property definition named `Output`; like any property, it contributes nothing to algorithm output unless some expression row references it:

<!-- spec:output-is-ordinary-property -->
```
Output = 5
Output
```

**Result:** `5`

If you declare explicit parameters on the enclosing algorithm, that algorithm must define output.

When an algorithm is used in call position, KatLang calls the algorithm using its own parameter list. Put the call interface on the algorithm head; the body's expression row is its result:

```
Algo(x) = {
    x + 1
}

Algo(6)
```

This produces `7`. Conditional branches follow the same rule: declare them on the enclosing algorithm head. To get an algorithm's result, call the algorithm directly. Bare `Algo` still refers to the algorithm value, not an automatic call. Self-contained helper properties remain accessible through dot syntax, for example `Algo.Helper(6)`. If a nested property depends on parameters owned by the enclosing algorithm — including the pattern binders of a conditional branch — it is local-only: only bodies inside the call that binds those parameters can read it, so `Algo.Helper` works inside `Algo`'s own body but is refused from outside, whether it is reached by dot access or through `open`. Properties defined inside a conditional branch are never reachable by name from outside that branch (`Algo.Helper` and `open Algo.Helper` are refused, and sibling branches never see them), but inside the branch they are ordinary properties: a self-contained branch-local library can be opened or dot-accessed by the branch body and by any body nested in it, exactly like an outer library.

Algorithm-level explicit parameters define the algorithm's direct-call interface, so they are valid only when the algorithm defines output. This is invalid:

```
Algo(x, y) = {
    Prop = 7
}
```

If the algorithm is only a container, remove the outer parameters and put parameters on the callable child property instead:

```
Algo = {
    Prop(x, y) = 7
}

Algo.Prop(1, 2)
```

An algorithm with no output is still valid when you use it structurally as a plain container or namespace-like scope:

```
A = {
    X = 1
}

A.X
```

**Result:** `1`

Using `A` itself where a concrete value is required is an error, because `A` does not define output. Do not add algorithm-level explicit parameters to this container form unless the algorithm also defines output.

### The Empty Sequence Value

The empty sequence value is written and displayed as `()`. It is a real value — not `null`, `void`, `false`, a unit value, or a no-output body.

<!-- spec:empty-capture -->
```
A = ()
A
```

**Result:** `()`

`()` is its own visible output slot and counts as zero items:

```
A = ()
A.count
```

**Result:** `0`

#### `()` and repeated empty parentheses

Parentheses around an empty-sequence literal are redundant grouping. [Sequence normalization](#sequence-normalization) reduces them to the same empty sequence value:

```
()       # the empty sequence
(())     # normalizes to ()
((()))   # normalizes to ()
```

They stay equal after parsing, assignment, display, and equality:

<!-- spec:empty-eq-family -->
```
() == ()      # true
() == (())    # true
() != (())    # false
count(())     # 0
count((()))   # 0
```

#### `()` versus a no-output body

`()` is a value. A no-output body is not a value at all: empty braces `{}` are an empty algorithm body with no defined output.

```
A = {
}
A
```

**Result:** error — `A` has no defined output.

Because equality compares values, comparing a no-output body with `()` is also an error, not `0`:

```
A = {
}
A == ()
```

**Result:** error — `A` has no defined output.

By contrast, `()` itself is a perfectly good value to store and compare:

```
A = ()
A == ()
```

**Result:** `true`

#### A written argument that produces no output

KatLang keeps four situations apart. Writing no argument is an arity error when the callable requires one:

```
F(x) = x
F()
```

**Result:** error — `F(x)` expects one argument, and none was written.

When a written argument must supply a value and its expression produces no output, the error identifies that **argument** — never as though you had left it out, and never as the callee's fault:

```
count({})
```

**Result:** error — the argument `{...}` has no defined output.

Fixed parameters keep lazy value demand: `F(x, y) = x` called as `F(1, {})` still returns `1`, because the body never demands `y`. If the body reads `y`, the error names the argument bound to `y` and points to that parameter read. Unselected `if` branches and callback algorithms keep their existing demand rules.

This matters most for a collector, which legally accepts zero supplied items. `Coll()` collects nothing and succeeds; `Coll({})` is an error, because an argument *was* written and produced nothing:

```
Coll(*xs) = xs
Coll()
```

**Result:** `[]`

```
Coll(*xs) = xs
Coll({})
```

**Result:** error — the argument `{...}` has no defined output.

An **empty value** is a value, so it is an ordinary argument — zero output values and one empty value are not the same thing:

```
Coll(*xs) = xs
Coll(())
Coll([])
```

**Results:**

```
[()]
[[]]
```

And an explicit **spread** that opens to zero items is a legal supply, exactly like writing no argument:

```
Coll(*xs) = xs
Empty = ()
Coll(Empty*)
```

**Result:** `[]`

#### `()` is a value, not an operator identity

`()` is an ordinary operand. It carries neither a numeric scalar value nor a Boolean value, so the arithmetic and ordering operators reject it exactly as they reject any other non-scalar operand, and the logical operators reject it as a non-Boolean operand — on either side, and whichever operand is empty:

<!-- spec:empty-sequence-is-not-an-operator-identity -->
```
10 / ()
```

**Result:** error

`() > 10`, `() and true`, `1 + ()`, and `() + 'text'` are errors for the same reason. An operator never returns the other operand, so an unexpectedly empty divisor or comparand fails loudly instead of yielding an apparently valid result.

Unary `-()` and `not ()` are errors too: `-` uses the same numeric conversion that rejects nonempty sequence and list operands, and `not` requires a Boolean operand — with no special rule for `()` in either case.

Equality is different by design: `==` and `!=` compare values structurally across every value kind, so they take `()` as a first-class operand and keep working.

```
() == ()
() == (1, 2)
```

**Results:**
```
true
false
```

Do not confuse the empty sequence **value** with an empty item **supply**. The value `()` is one thing you can store, compare, count, and pass as an argument. A supply is the temporary item stream that comma slots, output rows, and the spread marker feed into a receiver, and an *empty supply* is genuinely neutral there — `Empty*` contributes no items to the surrounding slots. That neutrality is a fact about supplies alone; it gives operators no passthrough rule.

#### Empty output slots stay visible; only spread opens

A normal output expression that evaluates to `()` is still a visible output slot. Only spreading an empty sequence with the spread marker (`value*`) contributes zero items:

```
Empty = ()
Empty
1
```

**Result:**
```
()
1
```

```
Empty = ()
Empty*,
1
```

**Result:** `1`

A collecting binding that collects zero items binds the empty [list](#lists) `[]`, not `()` — it is likewise one visible slot, and spreading it contributes zero items:

```
x, *rest = 1
rest
x
```

**Result:**
```
[]
1
```

```
x, *rest = 1
rest*,
x
```

**Result:** `1`

Collection builtins never produce `()` either: a builtin such as `filter` that keeps zero items returns the same empty list `[]`, which is a different value from `()`. Test an empty builtin or collecting-binding result against `[]` or with `count`:

```
IsEven = x mod 2 == 0
filter((1, 3, 5), IsEven) == []
filter((1, 3, 5), IsEven) == ()
count(filter((1, 3, 5), IsEven))
```

**Results:**
```
true
false
0
```

### Sequence Values and Count

Use `.count` (or `count(collection)`) to ask how many items a stored value contains. `count` receives one collection argument and views it one level deep: a lone sequence value or [list value](#lists) contributes its immediate items, while an atom or string is a one-element collection.

```
T = (1, 2, 3)
T.count

A = 1, 2, 3
A.count

count(A)
```

**Results:**
```
3

3

3
```

Collection builtins receive one collection object. Named helpers such as `A = 1, 2, 3` followed by `count(A)` and `A.count` both return `3` — the one bound collection value is opened one level, so its three items are counted. A sequence-valued helper such as `T = (1, 2, 3)` behaves the same way (`count(T)` and `T.count` return `3`), and a lone list value opens the same way too, so `count([1, 2, 3])` is also `3`. Multi-argument forms are not accepted: `count(1, 2, 3)` is an arity error because `count(collection)` expects exactly one argument, and `count(A*)` is an arity error too, because spread supplies ordinary call arguments — three of them here — rather than feeding the collection parameter. When extra items must join a collection, group them into one value: `count((A*, 7))` is `4`. See `count` below for the full collection-input rules.

### Output Selection

When an algorithm produces multiple outputs, the `:` operator selects one top-level item by its zero-based index. List values are indexable the same way: `value:index` selects one immediate element from a sequence or list target under identical index rules.

**Selection is a value boundary. `A:i`, `first(A)`, and `last(A)` return the selected value without opening it. Use `*` to open the selected value.**

Selection chooses a value; spread opens a value.

- If the selected item is atomic, the result is that atomic value.
- If the selected item is a sequence value, the result is that sequence value, exactly as stored — one value, not its members.
- If the selected item is a list value, the result is that list, exactly as stored.
- Nested sequence and list values stay intact; `:` never flattens or opens them.
- Chained selection repeats the same one-level step at each `:`.
- Once selected, the value's origin is forgotten: `A:0`, `first(A)`, `last(A)`, and a property holding the same value behave identically everywhere. A selected `()` is the empty sequence value, which emits zero items at a value boundary; a selected `[]` is one exact list value.

```
Nums = 10, 20, 30, 40, 50

# Select the third value (index 2):
Nums:2
```

**Result:** `30`

<!-- spec:index-selects-one-value -->
```
Pairs = (1, 2), (3, 4)
Pairs:0
```

**Result:** `(1, 2)`

<!-- spec:selection-forms-agree -->
```
Coll(*xs) = xs
Pairs = (1, 2), (3, 4)
first(Pairs).Coll
Pairs:0.Coll
(Pairs:0)*.Coll
Pairs:0.Coll(3)
```

**Results:**
```
[(1, 2)]
[(1, 2)]
[1, 2]
[(1, 2), 3]
```

Selection chooses a value; later collector behavior depends only on that value and whether it was spread, never on selection provenance. The selected pair is one value, shown as one row, exactly as `first(Pairs)` or a property `X = Pairs:0` would show it, and it is one argument at every receiver — `(Pairs:0).count` is `2` because `count` opens its one bound collection argument, and `G(Pairs:0)` passes one argument. A [collecting parameter](#collecting-explicit-parameters) collects that one argument exactly as it collects `Coll((1, 2))` — as ONE item — so `Pairs:0.Coll` is `[(1, 2)]`, and beside another argument the selected pair is one item too (`Pairs:0.Coll(3)` is `[(1, 2), 3]`). To hand the selected pair's items to any call as separate arguments, spread it: `(Pairs:0)*.Coll` is `[1, 2]`, and `(Pairs:0)*` (or `Pairs:0*`) emits the rows `1` and `2`.

<!-- spec:index-nested-stays-intact -->
```
Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8))
Bags:0
Bags:0:1
```

**Results:**
```
((1, 2), (3, 4))
(3, 4)
```

`Bags:0` is the intact inner pair-of-pairs and `Bags:0:1` selects one level further; neither selection opens what it selected.

List values use the same zero-based selection:

<!-- spec:list-index-selects-element -->
```
[1, 2, 3]:0
```

**Result:** `1`

`(1, 2, 3):1` and `[1, 2, 3]:1` agree on every index, and the same out-of-range and invalid-index errors apply to both target kinds. See [Indexing Lists](#indexing-lists) for how selected list elements keep their exact structure.

Output selection is especially useful with loops and multi-output algorithms where you only need one particular result.

### Dot-Call Syntax

A property call can be written with dot notation, placing the first argument before the dot. The two forms below are equivalent:

```
Square = n * n

# Standard call:
Square(5)

# Dot-call syntax:
5.Square
```

**Results:**
```
25
25
```

When the property has additional arguments beyond the first, they are supplied in parentheses after the property name:

```
Add = a + b

10.Add(5)
```

**Result:** `15`

Ordinary dot-call preserves the receiver as one leading argument boundary. A sequence-valued or multi-output receiver is not automatically spread across fixed parameters:

```
Add = a + b

Add(3, 7)      # 10
(3).Add(7)     # 10
(3, 7).Add     # error: receiver stays one argument
```

Use direct multi-argument syntax, or put one scalar receiver before the dot and the remaining arguments after the property name, when a user-defined algorithm expects several fixed parameters.

For that lexical fallback, `A.B(C, D)` assembles its arguments exactly like `B(A, C, D)`: the receiver is one ordinary leading argument, never a supply of `A`'s top-level values spread before `C` and `D` — write `A*.B(C, D)`, which is `B(A*, C, D)`, when you mean the items. This is a rule about the fallback, not an unconditional rewrite of dot syntax. Dot syntax is **property-first**: when `B` is a structural member of the receiver's algorithm, `A.B(C, D)` calls that member with `C` and `D` alone and no receiver is injected — even if a lexical `B` that could accept `(A, C, D)` is visible (see [Dotted Receivers and Collecting Parameters](#dotted-receivers-and-collecting-parameters) for how the fallback's receiver binds):

<!-- spec:dot-call-structural-member-is-not-a-lexical-rewrite -->
```
B(a, c) = a * 100 + c
Obj = {
    public B(c) = c + 1
}

Obj.B(5)
3.B(5)
```

**Results:**
```
6
305
```

`Obj` declares its own `B`, so `Obj.B(5)` calls that member with the one argument `5`; the visible two-parameter `B(a, c)` is never considered, although `B(Obj, 5)` is a well-formed two-argument call. The number `3` has no members, so `3.B(5)` is the lexical fallback `B(3, 5)`.

A parameter list with two or more parameters that contains a collecting parameter (`*name`) is a **mixed fixed/collecting parameter list**. The fixed parameters bind from the front and the back, and the collecting parameter collects the matched middle argument slots as one [list](#lists):

```
Arg = 1, 2, 3
Scale(*values, factor) = values.map{n * factor}

Scale(Arg*, 10)
Scale(1, 2, 3, 10)
```

**Results:**
```
[10, 20, 30]
[10, 20, 30]
```

Both item-supplying call forms agree: `factor` binds `10` from the back, `*values` collects the three front slots as `values = [1, 2, 3]`, the body's `map` call materializes the mapped items as the one list value `[10, 20, 30]`, and the call boundary returns that single value unchanged (see [Calls Return One Value](#calls-return-one-value)). Caller-site spread such as `Scale(Arg*, 10)*` opens the result into the flat items `10`, `20`, `30`.

An UNSPREAD structured argument is ONE argument, never an item supply — **values stay values**: `factor` takes `10` from the back, and the collecting parameter collects EXACTLY the arguments that remain. So `Scale(Arg, 10)` (and the dotted `Arg.Scale(10)`, which is the same call) binds `values = [(1, 2, 3)]` — one sequence-valued element, which the numeric `map` body rejects — and a written group receiver behaves the same (`(1, 2, 3).Scale(10)` binds `values = [(1, 2, 3)]`). A list is one argument too (`Scale([1, 2, 3], 10)` binds `values = [[1, 2, 3]]`), and several remaining arguments are collected the same way (`Scale(Arg, 4, 10)` binds `values = [(1, 2, 3), 4]`). Spreading is the explicit way to hand over items: `Scale(Arg*, 10)`, `Scale([1, 2, 3]*, 10)`, or the fluent `Arg*.Scale(10)`, which is `Scale(Arg*, 10)` (see [Dotted Receivers and Collecting Parameters](#dotted-receivers-and-collecting-parameters)). A lone collecting parameter such as `Helper(*values)` is the degenerate lone-collecting-binding case of the same item-supply binding (see [Collecting Explicit Parameters](#collecting-explicit-parameters)).

**Resolution rule:** KatLang first checks whether the property name exists as a structural property of the target algorithm. If found, it calls that property. If not found, it falls back to the same callable resolution a plain call would use, with the receiver as the leading argument. The rule applies at every level of a chained dot expression: a receiver that is itself an argumentless dot access such as `Lib.Sub` is navigated to `Sub`'s algorithm first, so `Lib.Sub.Q` reads `Sub`'s own `Q` whenever `Sub` has one (see [Chained Dot Access](#chained-dot-access)).

That fallback includes parameters: a member name that is a parameter of the calling context resolves exactly like the plain callee, so higher-order algorithm-valued parameters work in both spellings:

<!-- spec:dot-member-higher-order-parameter -->
```
K(a, t) = t(a)
D(a, t) = a.t

K(7, {a+1})
D(7, {a+1})
```

**Results:**
```
8
8
```

Parameter precedence in the fallback mirrors plain calls: the nearest lexical owner declaring the name supplies its parameter or property. An ancestor-owned parameter beats properties of farther owners and all opened providers; a property conflicting with a parameter in the same or an enclosing algorithm is a declaration error. Structural members of the resolved receiver always win before any of this — a receiver's own property is never bypassed in favor of a parameter.

### Chained Dot Access

Dot syntax is property-first at every level of a chain. When the receiver is itself an argumentless dot access, it is navigated to the member's algorithm before the next name is resolved, so an accessible structural member always beats a same-named extension — whether that extension is declared at the root, in the enclosing algorithm, or as a parameter of it:

<!-- spec:dot-chain-structural-member-beats-extension -->
```
Lib = {
    public Sub = {
        public Q = 1
    }
}

Q(x) = 99

Lib.Sub.Q
```

**Result:** `1`

`Lib.Sub` is navigated to `Sub`, and because `Sub` exposes an accessible `Q`, that member is read; the visible extension `Q(x)` is never considered, exactly as `Lib.Q` would read `Lib`'s own `Q`. Navigation does not evaluate the intermediate containers, so a container without output, or one that declares parameters, still exposes its members through a chain of any depth:

<!-- spec:dot-chain-nested-structural-members -->
```
A = {
    public B = {
        public C = {
            public D = 7
        }
    }
}
D(x) = 93

A.B.C.D
```

**Result:** `7`

Only a receiver that has no such member falls back to the extension call with the receiver as the leading argument, and those fallbacks compose along the chain like nested calls:

<!-- spec:dot-chain-extension-fallback-composes -->
```
A = x + 7
B = x * 5

3.A.B
B(A(3))
B(3.A)
```

**Results:**
```
50
50
50
```

The number `3` has no structural `A`, so `3.A` is `A(3)`; that result has no `B`, so `3.A.B` is `B(A(3))`. Structural access ignores `public` (a private intermediate member is still navigated) and selects every declared member: a local-only member is navigated like any other from a context inside the owner of what it captures, and from outside that owner — or when the member is defined only inside conditional branches — the edge is the same structural error that accessing it directly reports, never a fallback to a visible extension. A written call such as `Lib.Sub()` is a value, so a member after it is resolved by extension fallback on that value, while parentheses around a receiver or a single dot expression are ordinary grouping (`(Lib).Sub` is `Lib.Sub` and `(Lib.Sub).Q` is `Lib.Sub.Q` — parentheses never change which receiver is navigated).

### Dot Members and Implicit Parameters

Because a dot edge's lexical fallback is a real callable name, that name participates in implicit parameter inference whenever the fallback **may** be selected at runtime. Participation and ordering are separate: inferred names keep their normal semantic source-occurrence order. A dot edge contributes receiver occurrences first, then the participating member/fallback occurrence, then written argument occurrences:

<!-- spec:dot-member-fallback-implicit-signature -->
```
K = a.t
K(7, {a+1})
```

**Result:** `8`

`K = a.t` corresponds exactly to `K(a, t) = a.t`. The receiver `a` is an opaque implicit parameter, so at runtime `7` has no structural `t` and the edge falls back to `t(7)`. That runtime invocation order does not reorder the enclosing signature: the direct call `K = t(a)` independently infers `(t, a)`, while `K = a.t(b, c)` infers `(a, t, b, c)`.

When the fallback **cannot** be selected, nothing is inferred: with `Obj = {public t = 42 ...}`, `K = Obj.t` keeps arity 0 because the structural member always wins. An explicit parameter list is a different question again — it is closed, and it only requires names that are definitely needed, so a member whose fallback merely may be selected need not be declared:

<!-- spec:dot-member-fallback-in-closed-parameter-list -->
```
K(x) = x.V
Obj = {public V = 42}

K(Obj)
```

**Result:** `42`

`K` keeps arity 1: `V` resolves structurally on whatever `x` turns out to be, and reaches the lexical fallback only when the receiver has no such member.

### Misspelled Members on Known Receivers

Dot syntax is receiver injection, not a member lookup that fails when the member is absent: `a.F(x)` is `F(a, x)` whenever `a` has no structural `F`. That rule does not change when the receiver is statically known — `Math`, a block, or a loaded module has no special status. So a misspelled member on such a receiver is not an error by itself: the structural lookup finds nothing, the edge falls back to a lexical callable of that name, and when no such callable is visible an algorithm with inferred inputs treats the name as an implicit parameter exactly like any other unresolved name. An explicit parameter list stays closed; an unresolved dotted fallback there retains its existing runtime missing-name report. The program then fails only because nobody supplies that parameter:

```
Math.Ceiling(2.1)
```

**Result:** error — `Math` has no member `Ceiling`, so the call fell back to a lexical `Ceiling(Math, 2.1)`; no such callable is visible, so `Ceiling` became an implicit parameter of the program, and the report names the receiver, explains the fallback, and suggests `Math.Ceil`.

The report is receiver-aware — it points at the member token, names the receiver, and suggests a real member (`Math.Ceil`, `Lib.Double`) when one is a plausible respelling — but the underlying rule is the ordinary one, and it stays valid whenever a matching lexical callable does exist:

```
Ceiling(a, b) = b * 2
Math.Ceiling(2.1)
```

**Result:** `4.2`

Here `Ceiling` is visible, so `Math.Ceiling(2.1)` is the ordinary fallback call `Ceiling(Math, 2.1)`: `a` receives the `Math` algorithm and `b` receives `2.1`. This is a legitimate use of the language rule, not an accident — an extension defined for any receiver applies to `Math` too. A block receiver behaves the same way: with `Lib = { public Double(x) = 2 * x }` and `Dubel(a, b) = b * 3`, `Lib.Dubel(4)` is `Dubel(Lib, 4)`, which is `12`; without the lexical `Dubel` it is the implicit-parameter report with the suggestion `Lib.Double`. When you meant a member, check its spelling against the receiver's real members; when you meant an extension, make sure a callable of that name is visible.

<a id="grace-with-dotcall"></a>

### Grace with Dot Calls

[Grace](#reordering-parameters-with-grace) and ordinary dot syntax compose without creating another call form. `receiver~.Name(args...)` is postfix Grace on the bare receiver name followed by ordinary dot. `receiver.~Name(args...)` is ordinary dot with prefix Grace on the participating member/fallback name. In both cases `~` can change inferred parameter order only; it never changes structural-first member selection or lexical fallback execution:

<!-- spec:grace-dot-keeps-structural-precedence -->
```
V(x) = 99
Obj = {
    public V = 42
    0
}
Read = o~.V

Obj.V
Read(Obj)
```

**Results:**
```
42
42
```

`Read = o~.V` graces the free receiver name `o` — the marker is effective because `o` becomes `Read`'s implicit parameter — and `Read(Obj)` still reads Obj's own `V`, exactly like the direct `Obj.V`, even though a lexical `V` exists. With no lexical `V` declaration, prefix member Grace behaves the same way on an opaque receiver: `Read = o.~V` infers `(V, o)`, and `Read({x}, Obj)` still reads Obj's structural `V`. To call the lexical `V` with Obj's value instead, write the direct call `V(Obj)`. Grace is meaningful only on such free names: `Obj~.V` on the bound property `Obj`, or `Obj.~V` on a member Obj is known to declare, could reorder nothing and is rejected rather than silently ignored (see [Reordering Parameters with Grace](#reordering-parameters-with-grace)).

For an opaque receiver, ordinary DotCall occurrence order is receiver, participating fallback, then written arguments. Therefore `a.t` starts as `(a, t)`. Postfix Grace in `a~.t` moves `a` one position later; prefix Grace in `a.~t` moves `t` one position earlier. Both graced forms infer `(t, a)`:

<!-- spec:grace-dot-higher-order-implicit -->
```
K = a~.t
K({a+1}, 7)
```

**Result:** `8`

The executable body is still exactly ordinary `a.t`: parameter detection strips Grace, leaving the same DotCall target `a`, structural name `t`, and lexical fallback `t`. Only the enclosing inferred list differs. The prefix-member spelling works the same way: `K = a.~t` with `K({a+1}, 7)` also returns `8`.

Repeated markers use ordinary weight arithmetic. `a~~.t` is two postfix markers on `a`; with only `t` after it, the result is still `(t, a)`. `a~.~t` applies postfix Grace to `a` and prefix Grace to `t`, again through the same general pass. No token-sequence-specific permutation exists.

Grace still applies only to **one bare name occurrence**. Consequently `(x + y)~.t`, `f(x)~.t`, `[x, y]~.t`, `5~.t`, and `a~.t~.u` reject because postfix Grace would decorate a compound receiver at the failing edge. By contrast, `(x + y).~t` is valid: its prefix Grace decorates the bare fallback name `t`, not the receiver. Ordinary ungraced dot retains full receiver generality (`(x + y).t` and `(1, 2, 3).Mean` are unchanged).

Everything else is ordinary DotCall behavior: `.string` (`v~.string` with a free `v`), dotted sequence builtins (`S~.count` with a free `S`), and the receiver-as-leading-argument rule all use the same runtime paths as their ungraced forms. Prefix member Grace on a member that can never join the implicit parameters — the dot-only `.string` intrinsic (`v.~string`) or a builtin such as `count` in `S.~count` — is rejected as ineffective, like any marker on an already-bound name. Chaining an ordinary dot afterward is fine — `a~.t.string` has the same executable body as `a.t.string`.

The markers follow the marker attachment law: postfix Grace is written directly attached to its name (`a~.t`, or `a~ .t` — the space before a same-line dot is ordinary whitespace before a postfix continuation), while a detached `a ~ .t` or `a ~.t` is an error rather than Grace on `a`. Prefix member Grace must begin directly after the dot and be attached to the member name (`a.~t`; `a.~ t` is an error). A grace-marked target is not a valid `open` target: `open M~.C` is rejected because `open` consumes structural algorithm identity and has no parameter inference to reorder.

Exposure analysis is unaffected by Grace because it analyzes the same DotCall. A dot member marks a captured-parameter dependency only when static analysis proves its lexical fallback must be selected; when the receiver may own the member structurally, the possible fallback does not by itself change the property's exposure. That MUST-selection rule is deliberately stricter than signature inference, which includes a fallback whenever it MAY be needed.

### Name Resolution

Name resolution is especially important in KatLang because it may behave differently from what users expect from other languages. KatLang uses a fixed search order called **ownership-first lookup**. The idea is simple: a name belongs first to the algorithm that owns it, then to its parent structure, and only after that to anything brought in through `open`.

When KatLang sees a name, it searches **outward by owning scope** and stops at the first scope that declares it. A scope is one owner: an algorithm — or the root, or a conditional branch body — together with the names it binds. Two kinds of declaration are owned this way:

- the **parameters** it binds (written in its parameter list, inferred for it, or bound by its branch pattern), and
- the **properties** it declares (any visibility).

The search is therefore:

1. **The owner walk** — the algorithm containing the reference, then each enclosing algorithm outward, ending at the prelude (the builtins, `Math` and its aliases, and any host operations the running application provides, which form the outermost owner). The first owner that declares the name decides. A property may not share a name with a completed parameter of the **same or an enclosing lexical algorithm**; the front end reports a declaration error.
2. **Opens** — public properties from `open` targets, checked for the current algorithm first and then upward through the parent chain. Opens are consulted only when the whole owner walk found nothing, which is why an `open` never overrides something you own — and why a builtin name beats an opened one while still losing to anything you declare or bind yourself.

If the name is not found at any of these levels, KatLang treats it as an implicit parameter only when the current algorithm has no explicit parameter list (see [Parameters](#parameters)). Explicit parameter lists are closed, so an unresolved extra name is reported as an error instead.

The owner walk uses the complete parameter declarations, including parameters passed along implicitly from another property. For example, `Need = v` gives `Need` a parameter; using `Need` as a value can then give its enclosing algorithm that parameter too. Earlier nested references in that enclosing algorithm select the parameter, even inside a block that opens another `v`. This final selection preserves the inferred parameter lists, pattern shapes, and Grace order; it does not infer extra names from a newly available dot fallback.

Closedness also covers what a name needs *indirectly*. Referring to a property that has its own implicit parameters normally passes them along for you, and an explicit list can only do that for the parameters it declares. Where a value is definitely required — a math function's argument, for example — KatLang reports the gap instead of leaving it to fail at run time. Declaring the required name keeps the program legal:

```
A = q + 1
F(q) = Math.Abs(A)

F(7)
```

**Result:** `8`

Leaving the list off entirely works too (`F = Math.Abs(A)` infers `q` for you, as does `F = (Math.Abs)(A)` because the qualified reference selects the same Math callable), and so does supplying the argument at the call (`Math.Abs(A(1))`). But writing `F(x) = Math.Abs(A)` is rejected, because `Math.Abs` needs `A`'s value, producing that value needs `A`'s `q`, and `F(x)` declares no `q`: "'A' is required as a value here, but producing that value needs the implicit parameter 'q', which the enclosing explicit parameter list does not declare." Only a *value* demand is checked this way — passing `A` where a callable is wanted, as in `Apply(A)` or `map(abs)`, is unaffected.

```
X = 1
Inner = {
    Y = 2
    # X is declared by the enclosing owner
    # Y is declared by this owner
    X + Y
}
Inner
```

**Result:** `3`

In this example, `Y` is found immediately in `Inner`, because `Inner` owns it. `X` is not owned by `Inner`, so the walk continues outward and finds `X` in the enclosing algorithm.

Among properties, the nearer owner wins. If the same property name exists both locally and in a parent, the local one is used:

```
X = 10
Inner = {
    X = 99
    X
}
Inner
```

**Result:** `99`

Here `Inner`'s own `X` hides the outer `X`, so the result is `99`. This is shadowing, not reassignment: the root's `X` is still `10` wherever the root reads it, and each `X` is an immutable binding of its own scope. A nested property may hide an outer *property* this way; it may not reuse the name of a parameter bound by its own or an enclosing algorithm (see the next section).

#### Parameters take part in the walk

A parameter is a declaration of the algorithm that binds it, so it participates in exactly the same outward search — and it participates the same way whether the reference is written directly in that algorithm's body or in a body nested inside it:

<!-- spec:ownership-captured-parameter-beats-outer-property -->

```
v = 99
Outer(v) = {
    Inner = v + 1
    Inner
}
Outer(7)
```

**Result:** `8`

`Inner` is nested inside `Outer`, so the walk starts at `Inner`, reaches `Outer` — which binds `v` — and stops. The root property `v = 99` belongs to a farther owner and is never reached. `Inner` is evaluated inside the call that bound `v`, so it reads that call's argument.

When one owner declares both a parameter and a property of the same name, the program is invalid:

<!-- spec:ownership-same-owner-parameter-beats-property -->

```
Outer(v) = {
    v = 5
    Inner = v + 1
    Inner + v
}
Outer(7)
```

The front end reports a declaration error at the property name in `v = 5`, identifying the conflicting parameter. No evaluation takes place. The rule uses completed parameter signatures, including later lifted parameters, grouped and collecting parameters, and branch binders; it applies to private and public properties even when unused.

Declaring the property in a nested algorithm is also invalid:

<!-- spec:ownership-nearer-property-beats-outer-parameter -->

```
v = 99
Outer(v) = {
    Mid = {
        v = 5
        Inner = v + 1
        Inner
    }
    Mid
}
Outer(7)
```

The front end rejects `Mid`'s property `v` because `Outer` binds a parameter named `v`. Rename the property or parameter. Properties may still hide other properties, and a nested parameter may still reuse an outer parameter's name.

With several enclosing parameters of one name, the nearest one wins for the same reason:

<!-- spec:ownership-nearest-enclosing-parameter-wins -->

```
v = 99
Outer(v) = {
    Mid(v) = {
        Inner = v + 1
        Inner
    }
    Mid(7)
}
Outer(20)
```

**Result:** `8`

`Mid`'s parameter is reached before `Outer`'s, and the root property is never reached at all.

**Compatibility note:** SYN-03 initially allowed parameter/property collisions. The front end now rejects any property matching a completed parameter of its own or an enclosing lexical algorithm, including parameters discovered by later implicit forwarding. Moving the property into a nested body does not make it legal; rename one declaration. Captured parameters still beat farther properties and inner opens, and the nearest enclosing parameter still wins. A root property outside the parameter's owner remains legal, as in the first example above. Inline open targets keep their separate owner region — an inline `open { ... }` block (and an `open 'url'` string target) sees only its own declarations and the prelude, never the opener's properties or parameters, so a free name inside it becomes that block's own implicit parameter — and importing a name does not declare a property in the importing algorithm.

The root program is the one owner that is never called, so its implicit parameters are names it could not resolve rather than inputs a nested body could hide. A nested property that happens to share such a name is therefore not reported as a collision; the program fails with the root's unresolved-name error instead (reported at the root's first output row and naming the unresolved name), and the root reference is where the fix belongs:

```
Lib = {
    public Total = 1
}
Total + 1
```

**Result:** error — `Total` does not resolve at the root (write `open Lib` or `Lib.Total`); `Lib`'s own `Total` is not the problem and is not blamed.

Opens are checked only after the owner walk. This means a name introduced with `open` never overrides a name you already own — a property you defined structurally, and equally a parameter or branch binder bound by any enclosing scope.

In the next example, `open` appears first because KatLang requires opened sources to be declared before properties and output:

```
open Lib
Lib = {
    public X = 999
}
X = 1
# X resolves to the local property, not to Lib.X:
X
```

**Result:** `1`

#### Builtin names are ordinary bindings

The prelude is the outermost owner, so builtin callables are ordinary bindings and a nearer legal declaration shadows one like any other name. Builtin callable names are not reserved — `count`, `sum`, and `if` are all plain identifiers:

```
count(x) = x + 1
count(7)
```

**Result:** `8`

Resolution never considers how many arguments the call supplies. It selects exactly one callable, and only then checks that callable's signature, so KatLang has no overloading by argument count: a user `if(x)` replaces builtin `if` completely, and `if(true, 2, 3)` reports an arity error against `if(x)` instead of quietly falling back to `if(condition, whenTrue, whenFalse)`. A parameter shadows the prelude the same way, which is what lets you pass a callable in under a builtin's name:

```
Apply(if, x) = if(x)
Inc(x) = x + 1
Apply(Inc, 7)
```

**Result:** `8`

This ownership-first model makes name lookup more predictable in larger algorithms. In particular, adding an `open` does not silently change the meaning of names you already defined in the current algorithm or its parents, and adding a property somewhere far out in the program does not change what a parameter name means inside a nested body.

---

## String Literals

KatLang supports **string literals** as first-class values. A string is written with single quotes:

```
'hello'
'world'
```

**Results:**
```
hello
world
```

Strings can be stored as properties, passed as arguments, and returned as outputs:

```
Greeting = 'hello'
Tag = x

Tag('world')
```

**Result:** `world`

### String Equality

Strings support `==` and `!=`. Two strings are equal if they have identical content (case-sensitive):

```
'apple' == 'apple'
'apple' == 'Apple'
'cat' != 'dog'
```

**Results:**
```
true
false
true
```

Arithmetic operators (`+`, `-`, `*`, etc.) are not defined for strings.

### Number to String Conversion

Every numeric value exposes a `.string` property that converts it to a first-class string value. It takes no arguments — `A.string(1)` is an arity error, never a silent conversion of `A` — while an empty argument list (`A.string()`) is the same conversion.

```
123.string
0.string
(-5).string
1.20.string
```

**Results:**
```
123
0
-5
1.20
```

This also works on named properties:

```
A = 42
A.string
```

**Result:**
```
42
```

The result is a real KatLang string value — identical to a single-quoted string literal, even though string values display as their raw content without quotes. For example, `123.string == '123'` evaluates to `true`.

Only numeric values are supported. Applying `.string` to a non-numeric value (such as a string or a multi-output sequence value) produces an error.

---

## Parameters

> **Core idea:** in an algorithm without an explicit parameter list, unresolved names become parameters in first-occurrence order. An explicit parameter list fixes the accepted names and their order.

**Rule:** in an algorithm without an explicit parameter list, a name that resolves to nothing — not a property or parameter of the algorithm or of any enclosing algorithm, not an opened name, not a builtin (see [Name Resolution](#name-resolution)) — becomes an implicit parameter.

Parameters are named in camelCase by convention to distinguish them from PascalCase property names.

```
# 'x' is not defined as a property → it becomes a parameter
Add6 = x + 6

Add6(3)
Add6(10)
```

**Results:**
```
9
16
```

The order of implicit parameters is determined by their first appearance in the definition, reading left to right. Names written DIRECTLY in the definition come first, in that order; parameters a definition acquires only by FORWARDING — referring to a property that has its own implicit parameters passes them along (see [Name Resolution](#name-resolution)) — follow after every direct name, in the order they were forwarded, so `Need = v` and `F = Need * 10 + w` give `F(w, v)`, not `F(v, w)`. Grace reorders within each group and never moves a direct name behind a forwarded one.

```
# 'a' appears first, then 'b'
Sub = a - b

Sub(10, 3)
```

**Result:** `7`

Multiple parameters follow the same rule:

```
# Three parameters in order of appearance: a, b, c
WeightedSum = a * 2 + b * 3 + c * 5

WeightedSum(1, 2, 3)
```

**Result:** `23`

If an algorithm has an explicit parameter list, that list is closed. Names not declared in the parameter pattern must resolve from the surrounding scope; otherwise they are reported as unresolved. Implicit parameters are inferred only for algorithms without an explicit parameter list.

For example, `F((x, y)) = x + y` has signature `F((x, y))`. Adding an unresolved body name does not append a hidden parameter: `F((x, y)) = x + y + z` is still displayed as `F((x, y))`, and `z` must resolve from the surrounding scope or be reported as unresolved.

```
Add = x + y
Add(2, 3)
```

**Result:** `5`

By contrast, this is invalid because `y` is not part of the closed explicit parameter list:

```
Add(x) = x + y
# error: y is not part of the closed explicit parameter list
```

### Collecting Explicit Parameters

KatLang supports recursive parameter patterns in ordinary algorithm definitions and conditional branch heads. A sequence-value pattern consumes one parent-level argument slot and matches that slot's immediate contents. In an ordinary definition it opens a lone sequence value or a lone [list](#lists) alike:

<!-- spec:ordinary-sequence-pattern-opens-sequence-or-list -->
```
PairSum((x, y)) = x + y
PairSum((2, 3))
PairSum([2, 3])
```

**Results:**
```
5
5
```

Call arguments are evaluated exactly once, from left to right, before arity checking or
pattern binding. A sequence-value pattern opens the argument's VALUE — the pattern parentheses
describe the call shape (one argument that opens to so many items), never a runtime boundary —
and that value comes from that one evaluation. This matters for nondeterministic expressions
such as `Math.Random(...)`, for failures and their source context, and for host evaluation
budgets; parentheses never cause an argument to run again. Redundant parentheses around an
argument change nothing (`PairSum(((2, 3)))` is `PairSum((2, 3))`), and only an explicit postfix
spread contributes the evaluated value's immediate items as separate arguments.

A top-level collecting parameter (`*name`) instead consumes an **item supply**: it COLLECTS the arguments allocated to it, exactly, as one [list](#lists). Zero arguments collect `[]`, one argument collects `[item]` (never erased to the item), and many arguments collect `[item1, item2, ...]`. A callable with a collecting parameter can therefore accept a variable number of argument items — it is variadic in that sense. **Values stay values**: a non-spread argument supplies exactly ONE item whatever its value — a scalar, a sequence, a list, `()`, or `[]` — so the collector never opens an argument; only an explicit spread supplies a value's items, and the items a spread produces are never reopened. A lone collecting parameter is the simplest case — its segment is the whole supply:

<!-- spec:variadic-grouped-and-spread -->
```
A = 1, 2, 3, 4, 5

G(*x) = x.sum

G(A*)
G(1, 2, 3, 4, 5)
```

**Results:**
```
15
15
```

Both forms supply five numeric argument items, collected as `x = [1, 2, 3, 4, 5]`; `x.sum` opens the bound list and adds its elements. An UNSPREAD structure is one argument: `G(A)` and `G((1, 2, 3, 4, 5))` each supply ONE sequence-valued item, collected as `x = [(1, 2, 3, 4, 5)]` — one non-numeric element that the numeric `sum` rejects, exactly like the list argument `G([1, 2, 3, 4, 5])`, which collects `x = [[1, 2, 3, 4, 5]]`. So `G(*x) = x.count` reports `1` for `G(A)` and `5` for `G(A*)` — a collector counts arguments, never a value's elements — and `2` for `G(A, 0)`, with `x = [(1, 2, 3, 4, 5), 0]`. Nested structure stays intact: `G(((1, 2), 3))` collects `[((1, 2), 3)]`. Only the explicit spread supplies items, one level, a sequence and a list alike — `G([1, 2, 3, 4, 5]*)` sums to `15` — and a spread-produced item is never reopened: `G([(1, 2)]*)` collects `[(1, 2)]`. An empty call `G()` collects `x = []`, while `G(())` collects the one visible empty value, `x = [()]`.

Because a collecting parameter requires no supplied argument, a callable whose whole
parameter list is one collecting parameter accepts an empty call — and therefore reads as an
ordinary value too. **A callable may be read as a zero-argument value exactly when an ordinary
call with no arguments can bind it**, so the bare name and the empty call agree:

```
Only(*xs) = xs

Only()
Only   # valid value demand
```

**Results:**
```
[]
[]
```

Both spellings collect nothing, so both are the empty list. The bare name works wherever
KatLang already reads a value with no arguments — an output row, an `if` branch, a collection
builtin argument in either spelling (`count(Only)` and `Only.count` are both `0`), an ordinary
parameter that reads its argument, and a member read such as `Obj.M`. Redundant parentheses
change nothing: `Only`, `(Only)` and `((Only))` are the same value expression.

The two spellings differ only in the operational rule they already had: the bare name is a
property-style read, so repeated reads reuse the value in the property's applicable cache scope, while `Only()`
is an explicit call and runs the body each time (see
[Zero-Parameter Property Caching](#zero-parameter-property-caching)).

A required parameter is still required. A collecting parameter excuses only itself:

```
Head(first, *rest) = first

Head()
```

**Result:** error — `Head` needs one supplied value, so a call with none cannot bind it.

`Head` needs one supplied value, so `Head()` is an arity error — and so is reading `Head` as a
value, with the same "expects 1 parameter" report. The same holds for `Tail(*rest, last)` and
for a grouped parameter such as `Pair((x, y))`, which consumes one supplied argument whatever
its group contains: a group's one-item fallback binds ONE value, it never accepts none. And
where a callable is used as an algorithm rather than as a value — a `map` or `filter` callback,
a loop step, a higher-order argument — it is still the callable itself, so
`map((1, 2), Only)` is `[[1], [2]]`.

This holds when the callable is passed on through a parameter, too. Passing `Only` to a
parameter binds the parameter to both the callable and its zero-argument value `[]`. A builtin
position that calls its argument (a `map`, `filter` or `reduce` callback, a `while` or
`repeat` step) calls the callable, and a position that reads a value reads `[]`:

```
Only(*xs) = xs
Apply(f, xs) = xs.map(f)
Size(f) = count(f)

Apply(Only, [1, 2])
Size(Only)
```

**Results:**
```
[[1], [2]]
0
```

The collect marker and the spread marker have opposite meanings and are never interchangeable — they match the semantic directions `collect : Supply → ListValue` and `spread : Value → Supply`. Prefix `*name` in a binding position is a **collecting binding**: it collects its matched items into an exact list, and when it appears in a parameter list it is called a **collecting parameter**. Postfix `value*` is instead a **spread expression** that contributes the operand's items to the surrounding item supply. Both markers must be directly attached to what they modify: `*items` is a collecting binding while `* items` is an error, and `value*` is a spread while `value *` is an error. Which of the three meanings a star has is decided by position, never by spacing: a `*` followed by a valid right operand — on the same line or on the next — is always the multiplication operator, however it is spaced, and a `*` that nothing can follow (a comma, a closing delimiter, the end of the program, or a definition comes next) is the spread marker — which must then be attached. Whitespace therefore never turns one valid operation into another; it only separates the valid `value*` from the rejected `value *`.

Multiple sibling sequence values are **not** auto-flattened — they are preserved unless you open them explicitly with a spread marker. With `A = 1, 2` and `B = 3, 4`, `G(A, B)` collects `x = [(1, 2), (3, 4)]` (count 2), while `G(A*, B*)` collects `x = [1, 2, 3, 4]` (count 4):

<!-- spec:variadic-siblings-preserved -->
```
A = 1, 2
B = 3, 4

G(*x) = x.count

G(A, B)
G(A*, B*)
```

**Results:**
```
2
4
```

Because the collected value is an ordinary exact list, **forwarding a collecting parameter is ordinary spread**: `items*` re-supplies exactly the collected items to the next call, with no special forwarding machinery:

```
Target(*items) = items
Forward(*items) = Target(items*)

Forward(1, 2)
Forward([1, 2])
```

**Results:**
```
[1, 2]
[[1, 2]]
```

`Forward(1, 2)` collects `[1, 2]`, the spread re-supplies `1` and `2`, and `Target` re-collects the same list — the round trip is exact, including for the empty call (`Forward()` is `[]`) and structured arguments (`Forward([1, 2])` collects the list as one element and forwards it as one element). The [fluent supply chain](#spread-with-the-postfix-star) writes the same forwarding left to right: `Forward(*items) = items*.Target` is exactly equivalent to `Forward(*items) = Target(items*)` — the spread items become the arguments of the lexical call `Target(...)`. Passing the collected list WITHOUT spread passes one list argument: with `TargetOne(item) = item`, `ForwardAsOne(*items) = TargetOne(items)` gives `ForwardAsOne(1, 2)` → `[1, 2]` — the whole collected list bound to the fixed parameter. The same works for feeding collection builtins: `Qmean(*args) = args.sum / args.count` divides the sum of the collected list by its element count, so `Qmean(2, 4, 6)` is `4`.

Ordinary (non-collecting) parameters bind the receiver value itself, while a collecting parameter collects the receiver as ONE item — dot-call passes a value: `Arg.CollectMany` is `CollectMany(Arg)`, one argument. So the two shapes differ observably, for a sequence and a list alike:

```
Arg = 1, 2, 3
ArgList = [1, 2, 3]

Collect(list) = list
CollectMany(*list) = list

Arg.Collect.count
Arg.CollectMany.count
ArgList.Collect.count
ArgList.CollectMany.count
```

**Results:**
```
3
1
3
1
```

`Arg.Collect` binds `list = (1, 2, 3)`, so `count` opens the sequence (3 items), and `ArgList.Collect` binds the list itself (`count` opens it: 3). `Arg.CollectMany` collects the receiver as one item, `[(1, 2, 3)]`, and `ArgList.CollectMany` collects `[[1, 2, 3]]` — values stay values — so both counts are 1. Spreading the receiver supplies its items: the fluent `Arg*.CollectMany.count` and `ArgList*.CollectMany.count` are `CollectMany(Arg*).count` and `CollectMany(ArgList*).count`, `3`. Parentheses around a spread capture it back into one value: `(Arg*).CollectMany.count` is `1`, exactly like `CollectMany((Arg*))`.

#### Dotted Receivers and Collecting Parameters

**Dot-call passes a value. Spread opens a value.** For the extension-call fallback, `R.F(args)` is exactly `F(R, args)`: the receiver is one ordinary leading argument whatever it is — a property, a written group, a brace block, a list, a call result, a selection — so its item count never satisfies arity and a fixed parameter binds it whole. Dot-call is ordinary receiver injection; the collector rule explains fluent collection behavior: a collecting parameter collects the receiver as ONE item exactly as it would collect the written argument — a sequence and a list alike — and only the spread `R*.F(args)` — `F(R*, args)` — hands over the receiver's items. So a dotted aggregate over a group or a list spells its spread:

<!-- spec:dot-receiver-passes-a-value -->
```
Mean(*Vector) = Vector.sum / Vector.count

Mean(1, 2, 3)
(1, 2, 3)*.Mean
[1, 2, 3]*.Mean
```

**Results:**
```
2
2
2
```

`(1, 2, 3)*.Mean` spreads the written group into the three argument items of `Mean(1, 2, 3)` (`Vector = [1, 2, 3]`), and `[1, 2, 3]*.Mean` spreads the list the same way. Without the star, `(1, 2, 3).Mean` is `Mean((1, 2, 3))`: the group is ONE sequence value, collected as `Vector = [(1, 2, 3)]`, so the numeric `sum` fails on that one element — exactly like the list receiver `[1, 2, 3].Mean`, which collects `Vector = [[1, 2, 3]]`. The receiver is always ONE argument for arity and for fixed parameters: with `F(first, *middle, last)`, `(1, 2).F(9)` binds `first = (1, 2)` whole, `(1, 2).F` is an arity error — the receiver's item count never satisfies fixed-parameter arity — and `(1, 2)*.F` binds `first = 1`, `last = 2`. An extra written boundary changes nothing (`((1, 2)).CollectMany` collects `[(1, 2)]`, like `(1, 2).CollectMany`), a receiver beside another written argument is one item too (`(1, 2).CollectMany(3)` collects `[(1, 2), 3]`), the empty receiver is one visible argument (`().CollectMany` collects `[()]`, exactly like `CollectMany(())`), and only the spread opens (`[1, 2].CollectMany` collects `[[1, 2]]`; `[1, 2]*.CollectMany` collects `[1, 2]`; `[(1, 2)]*.CollectMany` collects `[(1, 2)]`, a spread-produced pair never being reopened). The [graced source](#grace-with-dot-calls) `S~.Mean` is the same ordinary dot edge with frontend-only Grace on `S`, so it keeps the same one-argument receiver rule (a written group is not a valid postfix-Grace operand).

Because the receiver is an ordinary argument, its origin never matters — a property holding `()` is passed exactly like the literal:

```
E = ()
CollectMany(*items) = items

E.CollectMany
CollectMany(E)
E*.CollectMany
E.CollectMany(1)
```

**Results:**
```
[()]
[()]
[]
[(), 1]
```

`E` returns the value `()` at every ordinary boundary — `E.count` is `0`, and `(1, E(), 2)` keeps it as a visible item. `E.CollectMany` and `CollectMany(E)` are the same call: an argument holding `()` is one visible item (arity is satisfied — `Collect(list) = list` gives `E.Collect` the value `()`), collected as such, `items = [()]`; only the spread `E*.CollectMany` (that is, `CollectMany(E*)`) supplies zero items and collects `[]`. Beside another argument the `()` is a visible collected item too: `E.CollectMany(1)` collects `[(), 1]`. A collection builtin's fixed `collection` parameter binds the value too (`E.count` is `count(E)`, which is `0`). A property's value count of zero is a fact about the value boundary, never a missing argument.

A parameter list may contain fixed and collecting parameters. When a parameter list has two or more parameters and one of them is a collecting parameter, the collecting parameter may appear at the front, middle, or end. Fixed parameters before it bind from the front, fixed parameters after it bind from the back — a bare argument supplies one slot, a stored sequence value included, and only an explicit spread opens a sequence value into separate slots — and the collecting parameter then collects the remaining middle arguments EXACTLY, a lone remaining sequence value included, which is one collected item:

<!-- spec:mixed-front-back-family -->
```
Arg = 1, 2, 3

Head(first, *rest) = first
Tail(first, *rest) = rest
Init(*init, last) = init
Last(*init, last) = last

Head(1, (2, 3))
Tail(1, (2, 3))
Init((1, 2), 3)
Last(Arg, 3)
```

**Results:**
```
1
[(2, 3)]
[(1, 2)]
3
```

`Head(1, (2, 3))` binds `first = 1`, and `Last(Arg, 3)` binds `last = 3` from the back. `Tail(1, (2, 3))` collects the remaining pair as one item: `[(2, 3)]`; `Init((1, 2), 3)` allocates `last = 3` first and collects the remaining pair as one item: `init = [(1, 2)]`. Several remaining arguments are collected the same way — `Tail(1, (2, 3), 4)` collects `[(2, 3), 4]` — so a structured item always stays distinguishable from its own elements, a list included (`Init([1, 2], 3)` collects `[[1, 2]]`), and only a spread supplies the elements (`Tail(1, (2, 3)*)` collects `[2, 3]`).

A parameter list with two or more captures and one collecting parameter matches the supplied item supply prefix/collecting/suffix. With `F(x, *y, z) = x + y.sum + z` and `A = 1, 2, 3, 4, 5`, `F(A)` supplies one argument and fails because `x` and `z` need two fixed arguments. `F(A*)` and `F(1, 2, 3, 4, 5)` bind `x = 1`, `y = [2, 3, 4]`, `z = 5` and return `15`; `F(1, 2)` binds `x = 1`, `y = []`, `z = 2` (the collecting parameter collects zero items) and returns `3`.

The fixed bindings set a **minimum item count**: `F(first, *middle, last)` requires at least two supplied items, because `first` and `last` each bind one, while the movable collecting parameter collects the (possibly empty) middle as an exact list:

<!-- spec:collecting-minimum-arity -->
```
F(first, *middle, last) = middle

F(1, 2)
F(1, 2, 3)
```

**Results:**
```
[]
[2]
```

A call below the minimum reports a targeted arity error naming the signature and both counts — `F(1)` fails with: ``Callable `F(first, *middle, last)` expects at least 2 items, but received 1 item.``

#### Deconstruction Assignment

The same comma binding pattern works on the left of `=`, binding several names from one right-hand side. Assignment deconstruction is an **unpacking receiver**, like Python's `x, y = pair`: when the right-hand side is exactly one sequence value or one exact [list value](#lists), the pattern opens that lone value and matches its items to the targets. At most one collecting binding `*name` is allowed, and it may appear anywhere in the pattern:

<!-- spec:decon-tutorial-full -->
```
A = 1, 2, 3, 4, 5

x, *y, z = A
x
y
z
```

**Results:**
```
1
[2, 3, 4]
5
```

The pattern unpacks the single stored sequence value `A`, so `x, *y, z = A` splits `A` into its items: `x = 1`, `y = [2, 3, 4]`, `z = 5`. Explicit `x, *y, z = A*` supplies the same items, and a direct item supply `x, *y, z = 1, 2, 3, 4, 5` binds the same way. Fixed targets bind from the start and end; the collecting target collects the middle as one [list](#lists). `*head, last = 1, 2, 3` binds `head = [1, 2]` and `last = 3`; `first, *tail = 1, 2, 3` binds `first = 1` and `tail = [2, 3]`; a singleton collected segment stays a one-element list (`x, *tail = 1, 2` binds `tail = [2]`), and `x, *y, z = 1, 2` binds `y = []`. With a single fixed target plus a collecting binding, `first, *rest = A` unpacks `A` into `first = 1` and `rest = [2, 3, 4, 5]` — the same as `first, *rest = A*`. A lone collecting target is also valid: `*all = 1, 2, 3` binds `all = [1, 2, 3]`, while `*all = ()` binds `all = []`. Without a collecting binding the item count must match exactly, so `x, y = 1, 2` binds `x = 1` and `y = 2`, while `x, y = 1` (one item) and `x, y = 1, 2, 3` (three items) are arity errors against the two targets. This unpacking is deconstruction-specific: an ordinary call `F(A)` still passes `A` as one argument, so calls need `F(A*)` to open it. More than one collecting binding (`*a, *b = 1, 2, 3`) is rejected. The right-hand side is an ordinary expression of the surrounding algorithm: it is evaluated once for all of its targets, and a name it does not resolve becomes an implicit parameter of that algorithm (never of the deconstruction itself):

```
F = {
  a, b = x, 10
  a + b
}

F(1)
```

**Result:** `11`

The same closed-input rule applies as for an ordinary row: in `F(k) = { a, b = x, 10 }`, undeclared `x` is a front-end error. Direct free names and lifted sibling dependencies keep their respective ordinary-row ordering across right-hand sides and output rows. A written brace on the right-hand side still creates its own lexical scope; its local properties, opens, and nested deconstructions stay inside that brace.

The exactness matters most when the remaining items are themselves structured — one leftover row stays distinguishable from the row's own elements:

```
Rows = [[1, 2], [3, 4]]

first, *rest = Rows
first
rest
rest.count
```

**Results:**
```
[1, 2]
[[3, 4]]
1
```

Segment collection is not recursive flattening. Spreading supplies a value's IMMEDIATE items, which the collecting parameter collects exactly — nested structures stay whole elements (here `Many(Arg*)` supplies `Arg`'s two pairs as two slots, so `values = [(1, 2), (3, 4)]` and its count is 2, not the four atoms; `atoms` is the explicit recursive projection):

```
Arg = (1, 2), (3, 4)

Many(*values) = values.count
Flattened = atoms(Arg).count

Many(Arg*)
Flattened
```

**Results:**
```
2
4
```

Use sequence-value parameter patterns when one fixed argument slot should be opened during binding. This is different from a top-level `*name`: the sequence-value pattern consumes exactly one argument slot, opens that slot's value — a lone sequence value or a lone exact [list](#lists), the same two kinds [deconstruction](#deconstruction-assignment) opens — and binds only its immediate contents. Any other value, or a value with the wrong number of items, is an arity error against the pattern. (In a multi-clause [conditional family](#nested-sequence-value-patterns) the same written pattern is narrower: there it matches sequence values only.)

```
SequenceValueCount((*values)) = values.count
SequenceValueCount((1, 2, 3))
```

**Result:** `3`

These two forms bind at different pattern levels. The top-level `*values` consumes an item supply, while the sequence-value pattern `(*values)` consumes one grouped value:

```
CountValues(*values) = values.count
CountSequenceValue((*values)) = values.count

CountValues()
CountValues(1, 2, 3)
CountValues((1, 2, 3))
CountSequenceValue((1, 2, 3))
```

**Results:**
```
0
3
1
3
```

In `CountValues`, top-level `*values` collects the call's arguments: `CountValues()` collects the empty supply `[]` (count `0`), `CountValues(1, 2, 3)` collects the three arguments as `values = [1, 2, 3]` (count `3`), and `CountValues((1, 2, 3))` supplies ONE sequence-valued argument, collected as `values = [(1, 2, 3)]` (count `1`) — a collector counts arguments, never a value's elements. The sequence-value pattern `(*values)` is the explicit opener instead: `CountSequenceValue((1, 2, 3))` consumes the one argument and opens it (count `3`). The forms differ again with a second argument — `CountValues((1, 2, 3), 4)` collects two items (count `2`) while `CountSequenceValue((1, 2, 3), 4)` is an arity error — and a list behaves like a sequence: `CountValues([1, 2, 3])` keeps it as one collected item (count `1`) while `CountSequenceValue([1, 2, 3])` opens it (count `3`). In `CountSequenceValue`, the outer sequence-value pattern consumes one parent-level argument slot, opens it, and `*values` collects that structure's immediate contents. The builtin `count(collection)` has no collecting parameter: it is an ordinary fixed-arity callable that takes exactly one collection argument, so with `Values = 1, 2, 3`, `count(Values)` is `3` while `count(1, 2, 3)` and `count(Values*)` are arity errors (see [Counting: `count`](#counting-count)); fixed-only user calls likewise preserve their exact call shape.

A pattern-shaped callee opens the argument's value, never a written grouping level. Parentheses group syntax; they do not introduce a semantic boundary: a bare reference, the same reference in redundant parentheses, and a literal in redundant parentheses all supply the same sequence value, and the pattern opens that value once. A nested pattern opens one more REAL boundary, which unary sequence structure can never supply ([sequence normalization](#sequence-normalization) removes it during value construction), so a one-element list supplies the outer structural level. Scalars also work through the ordinary one-item fallback at each pattern level: `CountSequenceValue3(7)` returns 1 without creating a unary sequence, and a `map`, `filter`, or `reduce` callback binds a scalar element by the same rule (see [Mapping: `map`](#mapping-map)). The structured examples are:

<!-- spec:redundant-call-parens-canonical -->
```
Inner = (1, 2, 3)
CountSequenceValue((*values)) = values.count
NestedCount(((*values))) = values.count

CountSequenceValue(Inner)
CountSequenceValue((Inner))
CountSequenceValue(((1, 2, 3)))
NestedCount([(1, 2, 3)])
NestedCount(([[1, 2, 3]]))
```

**Results:**
```
3
3
3
3
3
```

`CountSequenceValue(Inner)` opens the stored sequence into its three items, and `CountSequenceValue((Inner))` and `CountSequenceValue(((1, 2, 3)))` open exactly the same value — `(Inner)` is `Inner`, and `((1, 2, 3))` is `(1, 2, 3)`. `NestedCount` declares a second pattern level, so its argument must open to ONE item that itself opens: the one-element lists `[(1, 2, 3)]` and `[[1, 2, 3]]` do, and the redundant parentheses around the second one change nothing. Two further distinctions remain observable. First, a sequence value can never satisfy the nested level: `NestedCount((1, 2, 3))` and `NestedCount(((1, 2, 3)))` are the same arity error, because the value opens to three items where the outer pattern expects one. Second, non-unary structure is preserved: `CountSequenceValue(((1, 2), 3))` reports `2`, because the sequence value's items are `(1, 2)` and `3`.

Destructuring is recursive by syntax, but each sequence-value pattern opens only one value boundary. A collecting binding consumes siblings only at its own pattern level:

```
Window((first, *middle, last), scale) = first * scale, middle.count, last * scale
Window((1, 2, 3, 4), 10)
```

**Result:** `(10, 2, 40)`

The top-level argument structure still matters. These two signatures accept different call shapes:

```
FlatState((*history, previous), current) = history.count, previous, current
NestedState(((*history, previous), current)) = history.count, previous, current

FlatState((1, 2, 3), 4)
NestedState(((1, 2, 3), 4))
```

**Results:**
```
(2, 3, 4)
(2, 3, 4)
```

Nested sequence values remain intact unless the nested pattern explicitly opens them:

```
FirstSequenceValue((*values)) = values:0
FirstSequenceValue(((1, 2), 3))
```

**Result:** `(1, 2)`

This is useful for loop state where an accumulated history should remain one state slot while helper values sit beside it:

```
Step((*history), previous) = (history*, previous + 1), previous + 1
Step.repeat(2, (1, 2), 2):0
```

**Result:** `(1, 2, 3, 4)`

(`:0` selects the accumulator state slot as one value — selection never opens what it selects, so the selected history is one row; see [Output Selection](#output-selection).)

`(*history)` opens the single sequence-value state slot and collects its items as the exact list `history`. Inside `(history*, previous + 1)`, the spread `history*` opens that one list boundary into its immediate items (see [Opening One Level vs. Flattening](#opening-one-level-vs-flattening)), so each step rebuilds one flat accumulator sequence value beside the new value: `(1, 2)` → `(1, 2, 3)` → `(1, 2, 3, 4)`. The accumulator grows flat while remaining a single state slot beside `previous + 1`. The comma after the spread is required — `history* previous` would be the multiplication `history * previous` — and it is what places `previous + 1` beside the spread history items.

Only one collecting binding is allowed in each comma-separated pattern level, collecting bindings must be explicit, and they cannot use the Grace `~` reordering operator. The collect marker must be directly attached to its binding name: `*items` is a collecting binding, while `* items` is an error.

<a id="reordering-parameters-with-grace-operator"></a>

### Reordering Parameters with Grace

Sometimes the natural reading order of parameters in a definition does not match the intended calling convention. Grace (`~`) shifts a parameter's position.

Prefix `~x` moves `x` one position earlier in the parameter list. Postfix `x~` moves `x` one position later. Grace applies only to a bare parameter/name occurrence — `~x` and `x~` are the two supported forms — and the marker must be written directly attached to that name: `~ x` and `x ~` are errors, not Grace (a detached marker decorates nothing; the program is rejected rather than silently reordered or silently left in place). Repeated markers stay attached to each other and to the name (`~~x`, `~x~`). Attaching `~` to anything else (a parenthesized expression, a call result, a dot result, a list, a literal) is an error: `(x + y)~`, `f(x)~`, and `5~` are rejected, and parentheses never smuggle an expression into Grace (`(x)~` is rejected too). The marker and the name it decorates must also share one physical line: `f(x)~` at the end of a line is that same error rather than prefix Grace on the next line's name, and a prefix-grace slot after another slot on one line needs a comma (`f(x), ~c`). A marker written before a call, `~f(x)`, is grace on the callee name `f` itself — the call applies to the graced name, exactly like the postfix `f~(x)` idiom.

Grace is meaningful in exactly one place: on a free name that becomes an implicit parameter of the enclosing algorithm, because that inferred parameter list is the only thing Grace reorders. A marker on a name whose binding is already fixed cannot reorder anything, and KatLang rejects it instead of silently ignoring it: an explicit parameter (`K(b, a) = b, ~a` — the list already fixes the order), a parameter of an enclosing algorithm, a visible property (`X = 1` followed by `K = ~X + 2`), a builtin (`~count(...)`), an opened property, a dot member the receiver is known to declare (`Obj.~V`), or any occurrence under an explicit parameter list. Cancelling markers such as `~a~` still require a free name; their zero weight only cancels the reordering. The error names the reason:

```
K(b, a) = b, ~a
K(1, 2)
```

The report is `Grace has no effect on 'a' because it already resolves to an explicit parameter.` Write the order in the parameter list instead (`K(a, b) = b, a`), or drop the list and let Grace order the inferred parameters (`K = b, ~a` infers `(a, b)`).

```
# Without Grace, parameter order would be (y, x) since 'y' appears first.
# ~x moves x one position earlier → call order: (x, y)
Divide = y / ~x

Divide(2, 10)
```

**Result:** `5`

#### Grace weights

Every marker is one unit of **weight** on its name: a prefix `~` pulls the name one position earlier, a postfix `~` pushes it one position later, and the weights of all markers on all occurrences of one name in the same body add up. `~~c` is two units earlier; `~c~` is zero, so the markers cancel and the name stays where first appearance put it; `~c` written on two occurrences of `c` is two units as well. The inferred list is then reordered: a name moves one position per unit, stops at either end of the list, and never passes a neighbour that is pulling at least as hard in the same direction.

<!-- spec:grace-weights-accumulate -->
```
Weighted = a + 10 * b + 100 * ~~c

Weighted(1, 2, 3)
```

**Result:** `132`

First appearance gives `(a, b, c)`; the two units on `c` move it two positions earlier, so the signature is `Weighted(c, a, b)` and the call binds `c = 1`, `a = 2`, `b = 3`. With a single `~c` the signature is `Weighted(a, c, b)` and the same call returns `231`; with `~c~` it stays `Weighted(a, b, c)` and returns `321`. The inferred signature is what an arity error reports, which is a convenient way to check an order: `Weighted(1)` fails with ``Callable `Weighted(c, a, b)` expects 3 arguments, but was called with 1 argument.``

---

## Conditionals

`if` is a builtin algorithm with exactly three argument slots: `if(condition, whenTrue, whenFalse)`. Usually you pass the three arguments directly. There is no two-argument form. A grouped value used without spread is still one argument, so `if(X)` is invalid when `X = true, 2, 3`; explicit spread in call-argument position supplies one value's items across the three slots, so `if(X*)` works (the arguments are counted after spread expansion).

Like every builtin, `if` is an ordinary prelude binding: it is found by the usual [name resolution](#name-resolution), a nearer property or parameter shadows it, and its arity is checked when the call runs — against whichever callable resolution selected. What is special about `if` is only its invocation.

The condition must be a Boolean value: `true` selects `whenTrue` and `false` selects `whenFalse`. A number, string, sequence value, or list in the condition slot is a type error — there is no numeric truthiness, so write a comparison such as `x != 0` where another language would test a number.

Examples:

```
if(3 > 2, 1, 0)
if(1 > 2, 1, 0)
10 + if(1 == 1, 5, 0)
10 + if(1 == 2, 5, 0)
```

**Results:**
```
1
0
15
10
```

Combining `if` with properties:

```
# Return 1 if n is divisible by 3, 0 otherwise
DivBy3 = if(n mod 3 == 0, 1, 0)

DivBy3(9)
DivBy3(10)
```

**Results:**
```
1
0
```

For multi-case dispatch based on patterns, see [Conditional Algorithms](#conditional-algorithms).

`if(condition, whenTrue, whenFalse)` evaluates only the selected branch and returns that branch as **one value**. This is just the general [call value boundary](#calls-return-one-value) applied to `if`: if the selected branch is a multi-output property such as `X = 1, 2, 3`, the `if` result is the grouped sequence value `(1, 2, 3)` — the same single value you observe by referencing `X` directly. Use a caller-site spread, for example `if(true, X, X)*`, to contribute its items as separate output slots:

```
X = 1, 2, 3
if(true, X, X)
if(true, X, X)*
```

**Results:**
```
(1, 2, 3)

1
2
3
```

Explicit spread also works in **call-argument position**. Spreading a three-item value into the call opens it across the three argument slots, so `if(X*)` is equivalent to `if(true, 2, 3)` and selects the `whenTrue` branch:

```
X = true, 2, 3
if(X*)
```

**Result:**
```
2
```

This makes a direct `if(X*)` behave the same as a user-defined wrapper such as `MyIF(a, b, c) = if(a, b, c)` called as `MyIF(X*)`. A supply that does not come to three values is an evaluation-time arity error, just like any other builtin.

#### `if` composes like any other callable

Because `if` is reached by ordinary resolution, it also composes by ordinary rules. A dot-call injects the receiver as the leading argument, a spread supplies argument slots, and a bare `if` is a legal [higher-order](#higher-order-algorithms) reference. All of these assemble the same three arguments, so they all select the same branch:

<!-- spec:if-composition-forms-agree -->

```
Cond = true
Branches = (10, 20)
Apply3(f, a, b, c) = f(a, b, c)

if(Cond, 10, 20)
Cond.if(10, 20)
if(Cond, Branches*)
Cond.if(Branches*)
Apply3(if, Cond, 10, 20)
```

**Results:**
```
10
10
10
10
10
```

Evaluating only the selected branch belongs to the builtin **identity**, not to the name. It survives dot-calls and higher-order invocation:

<!-- spec:if-laziness-follows-the-resolved-identity -->

```
Boom = 1 / 0

if(true, 10, Boom)
false.if(Boom, 20)
```

**Results:**
```
10
20
```

Two things do *not* follow from it. Shadow the name and the laziness goes with it — `if(a, b, c) = b + c` is an ordinary algorithm, so it binds every argument eagerly and `if(true, 10, Boom)` then fails. And spread is not laziness: `if(true, Risky*)` has to build `Risky` before there are any argument slots to fill, so a failing row inside it fails first. That is the ordinary [value-then-supply](#value-and-supply-at-a-glance) order, not an exception for `if`.

A higher-order wrapper also binds its own arguments before invoking the received callable. Thus `Apply3(if, true, Tick(10), Tick(20))` would run both host callbacks before builtin `if` chooses. To give the builtin the branch expressions directly, write `Apply(f) = f(true, Tick(10), Tick(20))` and call `Apply(if)`; only `Tick(10)` runs. Naming a failing argument as a property can preserve its algorithm binding after an attempted value evaluation fails, so a successful wrapper call alone does not prove that the caller skipped that evaluation.

#### A selected branch is an ordinary value demand

The selected branch follows the same zero-argument signature check as a bare property reference. A branch that names an algorithm still needing arguments is therefore the same arity error that writing the name alone reports, and the body of that algorithm is never entered:

<!-- spec:lazy-slot-demand-is-the-ordinary-zero-argument-demand -->
```
Inc(x) = x + 1
if(true, Inc, 0)
```

**Result:** error — `Inc` expects 1 parameter, but the selected branch demands it with 0 arguments; the report names `Inc` at its reference, exactly as writing `Inc` alone would.

Only the selected branch is demanded, so the same name in the branch that is not taken is never demanded or evaluated:

```
Inc(x) = x + 1
if(false, Inc, 7)
```

**Result:** `7`

The same rule applies to every builtin value slot — the `if` condition, a loop's initial state and `repeat` count, `atoms`, `range`, collection arguments and fixed value controls, and the `.string` receiver — while callback slots (`map`, `filter`, `reduce` steps, loop steps) supply arguments and are unaffected. `reduce`'s initial accumulator is also a value demand and keeps its dedicated hint when arguments are missing. Call the algorithm, as in `if(true, Inc(4), 0)`, when you mean its result.

---

<a id="repetition"></a>

## Collections and Repetition

> **Core idea:** collection builtins receive one collection value. Use `range`, `filter`, `map`, and the other collection operations for data transformations; use `repeat` or `while` when a calculation must carry state between steps.

### Inclusive Integer Lists: `range`

`range(start, stop)` is a builtin algorithm that returns every integer from `start` to `stop`, inclusive.

- If `start < stop`, it counts upward by `1`
- If `start > stop`, it counts downward by `1`
- If `start == stop`, it returns a one-element list
- Both arguments must be whole numbers

```
range(1, 5)
range(5, 1)
range(3, 3)
```

**Results:**
```
[1, 2, 3, 4, 5]

[5, 4, 3, 2, 1]

[3]
```

A bound's evaluated value must be a finite whole number within ±`1e34`; a fractional value such as `1.5` is rejected. Accepted bounds may use decimal or exponent notation (`1.0`, `3.000`, `1e1`). `range` produces canonical integer elements independent of the bounds' Decimal128 quantum and zero sign: `range(1.0, 3)` produces `[1, 2, 3]`, and `range(-0.0, 2)` produces `[0, 1, 2]`. This normalization is specific to `range`; ordinary arithmetic retains its result quantum. Collection and evaluation limits still apply.

<!-- spec:range-integral-bound-quantum -->
```
range(1.0, 3)
```

**Result:** `[1, 2, 3]`

A `range` call is a value boundary: each bare call materializes one [list value](#lists) (`range(3, 3)` is the one-element list `[3]`, never erased to the bare atom `3`). The list result is itself one collection argument for the next builtin:

```
range(1, 3)
range(1, 3)*,
sum(range(1, 3))
```

**Results:**
```
[1, 2, 3]

1
2
3

6
```

`sum(range(1, 3))` is `6` because the bound list opens one level. Spread supplies ordinary call arguments instead: `sum(range(1, 3)*)` passes three separate arguments and is an arity error for the one-parameter `sum(collection)`. To combine the range's integers with more items, re-group the spread inside one collection value: `sum((range(1, 3)*, 4))` is `10`.

### Selection: `filter`

`filter(collection, predicate)` walks the bound collection's items from left to right and keeps only the top-level elements whose predicate result is the Boolean `true`.

Both call styles are supported: `filter(collection, predicate)` and `collection.filter(predicate)`.

- Kept elements stay in their original order
- Rejected elements disappear completely; no placeholders are inserted
- The predicate's current item is the selected element, one value — exactly what `S:i` returns for the traversed sequence `S`
- The current item is ONE argument of the predicate, exactly as in the direct call `predicate(item)`: a structural pattern such as `KeepPair((tag, value))` opens a sequence-value item to its members, and `filter` still keeps or discards the original top-level element
- Nested sequence values stay intact; the callback view is one-level only
- Predicate result must be a Boolean value: `true` keeps, `false` rejects
- Numeric, sequence-valued, list-valued, multi-output, empty, or string predicate results are type errors — there is no numeric truthiness

```
IsEven = x mod 2 == 0
filter((1, 2, 3, 4, 5, 6), IsEven)

GreaterThanThree = x > 3
filter(range(1, 5), GreaterThanThree)

KeepPair((tag, value)) = tag mod 2 == 0
filter(((1, 10), (2, 20), (3, 30), (4, 40)), KeepPair)
```

**Results:**
```
[2, 4, 6]

[4, 5]

[(2, 20), (4, 40)]
```

`filter` is a value boundary: the bare call returns one list value. Open the kept items with caller-site spread:

```
IsBig = x > 1
X = 1, 2, 3
X.filter(IsBig)
X.filter(IsBig)*
```

**Results:**
```
[2, 3]

2
3
```

If every predicate result is `false`, `filter` returns the empty list `[]` (never `()`).
Predicate results such as `1`, `0, 999`, `(true, false)`, or `x.string` are invalid because `filter` does not derive truth from numbers, sequence values, lists, or multi-output results.
The same callback rule applies everywhere, and parentheses shape the collection argument. `filter((1, 2), predicate)` and a helper `Values = (1, 2)` followed by `filter(Values, predicate)` each call `predicate` once for each item in that sequence value, and a lone list value is opened the same way, so `filter([1, 2], predicate)` also calls `predicate` once per element. Calls such as `filter(range(1, 5), predicate)` (the range result is a list, opened as the bound collection), `P = range(1, 5)` followed by `filter(P, predicate)`, and `filter((range(1, 5)*, 8), predicate)` call `predicate` once per immediate item. The collection must stay one argument: `filter(1, 3, 5, IsEven)` and `filter(range(1, 5)*, 8, predicate)` are arity errors because `filter(collection, predicate)` expects exactly 2 arguments.

### Mapping: `map`

`map(collection, mapper)` walks the bound collection's items from left to right and replaces each top-level element with `mapper(element)`.

- The mapper's current item is the selected element, one value — exactly what `S:i` returns for the traversed sequence `S`
- The current item is ONE argument of the mapper, exactly as in the direct call `mapper(item)`: a structural pattern such as `Swap((a, b))` opens a sequence-value item; nested sequence values stay intact
- The mapper must return exactly one mapped element
- One atomic value is valid
- One sequence value such as `(x, x * x)` is also valid
- Empty or multi-output mapper results are errors
- Output order and element count are preserved

Both call styles are supported: `map(collection, mapper)` and `collection.map(mapper)`.

```
Double = x * 2
map((1, 2, 3), Double)

Square = x * x
map(range(1, 5), Square)

PairWithSquare(x) = (x, x * x)
map((1, 2, 3), PairWithSquare)
```

**Results:**
```
[2, 4, 6]

[1, 4, 9, 16, 25]

[(1, 1), (2, 4), (3, 9)]
```

`map` is a value boundary: the bare call returns one list value. Open the mapped items with caller-site spread:

```
Double = x * 2
X = 1, 2, 3
X.map(Double)
X.map(Double)*
```

**Results:**
```
[2, 4, 6]

2
4
6
```

A mapper receives each element as ONE argument — **the callback law**: `map` calls `Swap(element)` exactly as a direct call would — and must return exactly one element. To swap pairs, open the element with a structural pattern and return one pair: `Swap((a, b)) = (b, a)`. A flat two-parameter `Swap(a, b)` is the ordinary arity error of `Swap((1, 2))`, and `Swap((a, b)) = b, a` returns two output rows, which a mapper may not. (The callback item itself is one value — `Id(x) = x` maps `((1, 2), 3)` to `[(1, 2), 3]`.)
With that rule, `map(((1, 2), (3, 4)), Swap)` calls `Swap` once per pair and produces the list value `[(2, 1), (4, 3)]` (append `*` to open the mapped pairs into an item supply). A single sequence-value argument such as `Values = (1, 2)` followed by `map(Values, Swap)` is opened one level into the two atom items `1` and `2`, so the mapper runs once per atom — and the pair pattern of `Swap` then rejects each atom with a pattern arity error. Use a one-parameter callback for atom items, and reserve `Swap((a, b))` for collections whose items are pairs, as in `map(((1, 2), (3, 4)), Swap)`. The one bound collection may be a grouped sequence value or a lone list value — both open one level: `map(range(1, 5), Double)` (the range result is a list), `Values = 1, 2, 3` followed by `map(Values, Double)`, and `map((1, range(2, 4)*), Double)` run once per immediate item.

Math functions and their lowercase aliases are ordinary callables, so they work directly as callbacks: `[1, -2].map(abs)` and `[1, -2].map(Math.Abs)` are both `[1, 2]`, and `[0, 1].map(sin)` maps each element through `sin`. The callback always binds its own per-element argument — a same-named value in the surrounding algorithm is never captured:

<!-- spec:native-flat-callback-binding -->
```
F(x) = [1, -2].map(abs)
F(5)
```

**Result:** `[1, 2]`

Callbacks with a collecting parameter collect exactly like ordinary calls: each iterated element is ONE argument of the callback call, so a callback whose only parameter is a collecting parameter collects every element — a scalar, a sequence, or a list alike — as the one-element list `[element]`:

<!-- spec:callback-variadic-collects -->
```
Collect(*items) = items

[7].map(Collect)
[(1, 2)].map(Collect)
[[1, 2]].map(Collect)
```

**Results:**
```
[[7]]
[[(1, 2)]]
[[[1, 2]]]
```

A `()` element is one visible item too (`[()].map(Collect)` is `[[()]]`), and a nested element stays intact (`[((1, 2), 3)].map(Collect)` is `[[((1, 2), 3)]]`). A multi-parameter flat callback does not open an element either: with `F(first, *middle, last) = middle` and `Rows = [(1, 2, 3, 4)]`, `Rows.map(F)` is the ordinary arity error of `F((1, 2, 3, 4))` — one argument against two fixed positions. The explicit structural pattern `F((first, *middle, last))` opens each row instead — a sequence and a list row alike — and `Rows.map(F)` is `[[2, 3]]`. The same collection rule reaches `filter` predicates, which count one argument per element (`IsSingleSeven(*items) = items == [7]` keeps `7` out of `[7, 8]`; `IsPair(*items) = items.count == 2` keeps none of the elements of `((1, 2), 3, (4, 5), [6, 7])`, while the fixed `IsPair(x) = x.count == 2` inspects each element's contents and keeps three). Reduce supplies two ordinary arguments, element and accumulator, so a reducer whose only parameter is a collecting parameter, `R(*items)`, collects `items = [element, accumulator]`; with `R(*items, acc)`, the collecting parameter before the fixed accumulator collects the one element (`reduce([(1, 2)], R, 99)` with `R(*items, acc) = items` returns `[(1, 2)]`), and a collecting parameter on the accumulator side (`Acc(x, *acc)`) collects the ONE accumulator value (`reduce([9], Acc, ((1, 2), 3))` is `[((1, 2), 3)]`).

A callback whose parameter is a nested sequence-value pattern binds each element exactly as the ordinary call with that one element binds it. The pattern opens a sequence or list element one level, and any other element (a number, a string, a Boolean) is the ordinary one-item supply at every pattern level. So a scalar element binds `(x, *rest)` with an empty `rest`, just like the direct call:

<!-- spec:callback-nested-pattern-binds-like-call -->
```
Head((x, *rest)) = [x, rest]

Head(7)
[7].map(Head)
map((7, (8, 9)), Head)
```

**Results:**
```
[7, []]
[[7, []]]
[[7, []], [8, [9]]]
```

One element is still one item: with `Pair((x, y)) = [x, y]`, `[7].map(Pair)` fails with the same pattern arity error as `Pair(7)`. `filter` and `reduce` bind their callback values by the same rules. The operation still decides how many values it supplies (the element for `map` and `filter`, the element and the accumulator for `reduce`) and how often it invokes the callback: never for an empty collection, and once for an empty `()` element.

Direct and forwarded callbacks use the same callable in the callback slot. Forwarding still has ordinary parameter-binding effects: passing a zero-argument-eligible callable can evaluate it once to establish the parameter's value channel. Selecting its callable channel afterward performs no additional value demand. For a host-backed `Cnt(*xs)` that records `xs.count`, mapping two items directly records `[1, 1]`; forwarding it through `Apply(f) = map([5, 6], f)` records `[0, 1, 1]`, including the initial binding demand. Value consumers continue reading the established value channel.

Multi-clause conditional algorithms used as callbacks match the selected element as ONE argument too, like every callback: a clause head with two flat parameters never matches a single element (`No matching branch`). Write nested sequence-value clause heads — `F((0, y)) = ...`, `F((x, y)) = ...` — when a clause family should destructure rows.

### Collection Inputs

`filter`, `map`, `order`, `orderDesc`, `count`, `contains`, `first`, `last`, `distinct`, `take`, `skip`, `min`, `max`, `sum`, `avg`, and `reduce` are ordinary fixed-arity callables that receive **one collection object** plus fixed control arguments. The fixed signatures are:

`count(collection)`, `sum(collection)`, `first(collection)`, `last(collection)`, `min(collection)`, `max(collection)`, `avg(collection)`, `order(collection)`, `orderDesc(collection)`, `distinct(collection)`, `take(collection, count)`, `skip(collection, count)`, `contains(collection, item)`, `map(collection, mapper)`, `filter(collection, predicate)`, and `reduce(collection, reducer, initial)`.

Use `()` for a sequence value, `[]` for a [list](#lists), or receiver-style dot syntax (`collection.take(2)`) for concise expressions.

- After binding, the one collection argument is viewed one level deep: a lone sequence value or list value opens into its immediate items, an atom or string is a one-element collection, and nested sequence or list elements stay opaque items. So `count((1, 2, 3))`, `count([1, 2, 3])`, and `count(range(1, 5))` count their items (`3`, `3`, and `5`), `count(7)` is `1`, `count(((1, 2), (3, 4)))` is `2` (each pair is one item), and `count((1, [2], 3))` is `3` (the nested list is one opaque item).
- The remaining parameters are ordinary fixed arguments: `take((1, 2, 3), 2)` binds `collection = (1, 2, 3)` and `count = 2`; `map`, `filter`, and `reduce` bind their callback and accumulator arguments the same fixed way.
- The argument count is checked like any callable. `count(1, 2, 3)` is an arity error — `count(collection)` expects 1 argument, but was called with 3 — and `take([1, 2, 3])` is an arity error too: the list is the one collection argument, and `count` is missing.
- A call with no argument is never an empty collection: `count()` is an arity error, distinct from `count(())` which returns `0` (and `count([])`, also `0`). Absence of an argument and an empty collection value are different things.
- Spread supplies ordinary call arguments; it does not feed a builtin's collection parameter. With `Values = 1, 2, 3`, `count(Values*)` passes three arguments and is an arity error, as is `take([1, 2, 3]*, 2)`. Re-group with parentheses when a spread must become one collection: `count((Values*, 8))` is `4`, and with `A = 1, 2` and `B = 3, 4`, the grouped `sum((A*, B*))` is `10` — the concatenation form — while `sum(A*, B*)` and `sum(A, B)` are arity errors. A spread that lands on exactly the right argument count is an ordinary call: `take([7]*, 1)` passes `7` and `1` and returns `[7]`.
- Dot-call supplies the receiver as the collection argument. With `Values = 1, 2, 3`, `Values.count` is `3`; `range(1, 5).take(2)` is `[1, 2]`; `X.filter(P).count` counts the kept items. A user-defined collecting helper is different from a builtin here: `Helper(*values) = values.count` accepts `Helper(1, 2, 3)` and `Helper(Values*)` because a collecting parameter collects the call's argument slots as one exact list, while the builtin `count` accepts only the single-collection forms. (See [Collecting Explicit Parameters](#collecting-explicit-parameters).)
- `:` selection returns the selected value whole, and the builtin then opens that one bound collection value one level. `Pairs = (1, 2), (3, 4)` gives `(Pairs:0).count = 2` (and `Pairs:0.count`, `first(Pairs).count` agree). `Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)` gives `(Data:0).order` as the list value `[1, 2, 4, 6, 7]`.
- Higher-order callbacks receive the current item as one selected value, so sequence elements are available through ordinary parameters or `item:i`. Any collection builtin applied to that callback variable binds the item as its one collection argument and opens it one level (`item.count` counts a sequence-valued item's members)
- Nested sequence values are never recursively flattened unless a builtin explicitly says so, such as `atoms`; use a spread expression (`value*`) to open only one outer boundary
- `contains` compares its searched item against the collection's top-level items using ordinary KatLang value equality; it does not recurse into nested sequence elements
- `distinct` compares those top-level items structurally, using the same ordinary KatLang value equality rules
- `take` and `skip` follow the same family pattern: direct calls take the count as the second fixed argument (`take((1, 2, 3), 2)` / `skip((1, 2, 3), 2)`), and dot-calls use `collection.take(2)` / `collection.skip(2)`

### Ordering: `order` and `orderDesc`

`order(collection)` sorts the bound collection's top-level numeric items in ascending order.
`orderDesc(collection)` sorts the same kind of top-level items in descending order.

- Both builtins evaluate the full collection eagerly before sorting
- Duplicates are preserved; there is no implicit distinct or unique step, so use `distinct` separately when deduplication is required
- `order` is stable: items that compare equal keep their written order. `orderDesc` reverses that ascending result, including the order within equal-value groups — visible when equal values are spelled differently (`order((1.0, 1))` is `[1.0, 1]`, `orderDesc((1.0, 1))` is `[1, 1.0]`)
- The result is one list value (the call is a value boundary); use a caller-site spread (`value*`) when the surrounding context needs the sorted items as an item supply
- Each top-level element must be exactly one atomic numeric value
- Sequence values and list values are not flattened or inspected recursively
- Strings and mixed-type collections are invalid

Both call styles are supported: `order(collection)` / `orderDesc(collection)` and `collection.order` / `collection.orderDesc`.

```
order((3, 4, 2, 1, 3, 3))

orderDesc((3, 4, 2, 1, 3, 3))

Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
(Data:0).order
```

**Results:**
```
[1, 2, 3, 3, 3, 4]

[4, 3, 3, 3, 2, 1]

[1, 2, 4, 6, 7]
```

`order`/`orderDesc` are value boundaries: each bare call returns one list value. Open the sorted items with caller-site spread:

```
X = 3, 1, 2
X.order
X.order*,
X.orderDesc*
```

**Results:**
```
[1, 2, 3]

1
2
3

3
2
1
```

Applying `order` or `orderDesc` to a collection like `(1, 'hello')` is invalid because KatLang does not define a loose mixed-type ordering rule. `order(((1, 2), (3, 4)))` is also invalid, because each item must be a sortable atom and sequence-value items are not flattened.
Named sequence helpers and call receivers such as `Values = 1, 2, 3` followed by `order(Values)` and `Values.order` return the list value `[1, 2, 3]`; `P = range(5, 1)` followed by `order(P)` and `range(5, 1).order` return `[1, 2, 3, 4, 5]` (the range result is itself a list, opened as the bound collection), and `order([3, 4, 2, 1])` sorts a literal list the same way. Inline and spread forms are arity errors — `order(3, 4, 2, 1)`, `order(Values*)`, and `order(Values*, 8)` all supply more than the one argument `order(collection)` expects. To add an extra item, group it into the collection: `order((Values*, 8))` returns `[1, 2, 3, 8]`. Selection returns the selected sequence value whole and the builtin then opens that one bound collection, so `(Data:0).order` sorts `7, 6, 4, 2, 1` to `[1, 2, 4, 6, 7]`. Each is one value at the call boundary; append the spread marker (for example `Values.order*`) when the surrounding context needs the sorted items as an item supply.

### Counting: `count`

`count(collection)` returns how many top-level values the bound collection denotes.

- Each atom, string, sequence value, or list value counts as one top-level element
- Sequence values and list values are not flattened or inspected recursively

Both call styles are supported: `count(collection)` and `collection.count`.

<!-- spec:count-family -->
```
count(())
count((()))

count(range(1, 5))

count((10, 20, 30))

count((3, 4, range(1, 5)*, 7))

count((range(1, 5)*, 7))

count(((1, 2), (3, 4)))

Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
(Data:0).count
```

**Results:**
```
0

0

5

3

8

6

2

5
```

`count(5)` and `count('hello')` both return `1`, because an atomic value is treated as a one-element collection.
`count(())` and `count((()))` both return `0` because sequence normalization reduces repeated ordinary parentheses around the empty sequence to `()`. `count()` with no argument at all is an arity error, not `0` — absence of an argument is never an empty collection. `count({})` is an error because a no-output body has no defined output. `count((1, 2, 3))`, `Values = (1, 2, 3)` followed by `count(Values)`, `Values.count`, and `((1, 2, 3)).count` all return `3`, because the one bound collection value is opened one level; a lone list value is opened the same way, so `count([1, 2, 3])` is also `3`, and `count(range(1, 5))` counts the five elements of the range list. `Values = 1, 2, 3` followed by `count(Values)` and `Values.count` also return `3`, but `count(1, 2, 3)` and `count(Values*)` are arity errors — `count(collection)` expects exactly one argument, and spread supplies ordinary call arguments (three here) rather than feeding the collection parameter. In `count((3, 4, range(1, 5)*, 7))`, the spread opens the range list's elements inside one sequence value, so the count is `8`. Selection returns the selected pair as one collection value, which `count` then opens, so `Pairs = (1, 2), (3, 4)` followed by `(Pairs:0).count` returns `2`.

### Membership: `contains`

`contains(collection, item)` returns `true` when any top-level item of the bound collection equals `item`, otherwise `false`.

- Comparison uses ordinary KatLang value equality
- Atoms compare by numeric value, strings by exact string value, and sequence values structurally by sequence elements
- Search is top-level only; nested sequence elements are not searched recursively
- Empty collections return `false`

Both call styles are supported: `contains(collection, item)` and `collection.contains(item)`.

```
contains(range(1, 5), 3)

contains(range(1, 5), (1, 2, 3, 4, 5))

Pairs = (1, 2), (3, 4)
Pairs.contains((1, 2))
```

**Results:**
```
true

false

true
```

`contains(range(1, 5), 9)` returns `false` because no top-level item equals `9`.
`contains(((1, 2), (3, 4)), (1, 2))` returns `true` after the outer collection value is opened one level — a lone list value opens the same way, so `contains([1, 2, 3], 2)` returns `true` (and the `range` examples above already search a list collection). KatLang still does not recurse beyond the immediate top-level items. Selection returns the selected sequence value as the one collection argument, which `contains` then opens, so with `Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)`, `(Data:0).contains(4)` and `contains(Data:0, 4)` both return `true`. Spreading the collection is an arity error instead: `contains((Data:0)*, 4)` supplies the five selected items plus `4` as six ordinary arguments, but `contains(collection, item)` expects 2.

### First Element: `first`

`first(collection)` selects the first top-level value in the bound collection and returns it unchanged — the same selection as `collection:0` (see [Output Selection](#output-selection)).

- The collection must be non-empty
- Atoms, strings, and sequence values each count as one top-level element
- Selection is a value boundary: a selected sequence value or list is returned whole as ONE value (never opened or flattened), a selected `()` is simply `()`, and only an explicit spread opens the selected value — with `Coll(*xs) = xs`, `first(((1, 2), 3)).Coll` is `[(1, 2)]` and `(first(((1, 2), 3)))*.Coll` is `[1, 2]`

Both call styles are supported: `first(collection)` and `collection.first`.

```
first(range(1, 5))

first((4, 5, 6))

first(((1, 2), (3, 4)))
```

**Results:**
```
1

4

(1, 2)
```

Applying `first` to an empty collection is invalid because `first` requires at least one top-level element.
`first((1, 2, 3))`, `first(((1, 2, 3)))`, `Values = (1, 2, 3)` followed by `first(Values)`, and `Values.first` all return `1`: the one collection argument is opened one level, and a literal `((1, 2, 3))` already collapses to `(1, 2, 3)`, so the grouped and nested forms agree — `first([1, 2, 3])` and `first(range(1, 5))` open a list the same way. `first(1, 2, 3)` is an arity error: `first(collection)` expects one argument, so the items must arrive as one collection value. Sibling grouped values inside one collection are preserved — `first(((1, 2), (3, 4)))` returns the whole pair `(1, 2)`, and with `A = 1, 2` and `B = 3, 4`, `first((A, B))` returns `(1, 2)` while `last((A, B))` returns `(3, 4)`; the ungrouped `first(A, B)` (two arguments) is an arity error.

### Last Element: `last`

`last(collection)` selects the last top-level value in the bound collection and returns it unchanged — the same selection as `collection:(collection.count - 1)`.

- The collection must be non-empty
- Atoms, strings, and sequence values each count as one top-level element
- Selection is a value boundary exactly as for `first` and `:`: the selected value is returned whole as ONE value and only an explicit spread opens it

Both call styles are supported: `last(collection)` and `collection.last`.

```
last(range(1, 5))

last((4, 5, 6))

last(((1, 2), (3, 4)))
```

**Results:**
```
5

6

(3, 4)
```

Applying `last` to an empty collection is invalid because `last` requires at least one top-level element.
`last((1, 2, 3))`, `last(((1, 2, 3)))`, `Values = (1, 2, 3)` followed by `last(Values)`, and `Values.last` all return `3`: the one collection argument is opened one level (a literal `((1, 2, 3))` already collapses to `(1, 2, 3)`, and `last(range(1, 5))` opens the range's list result the same way). `last(1, 2, 3)` is an arity error — supply the items as one collection value. Sibling grouped values inside one collection stay whole: with `A = 1, 2` and `B = 3, 4`, `last((A, B))` returns the last grouped sibling `(3, 4)`; the ungrouped `last(A, B)` (two arguments) is an arity error.

### Distinct: `distinct`

`distinct(collection)` returns the bound collection's top-level items with later duplicates removed, as one list value.

- The original left-to-right order of first occurrence is preserved
- Atoms compare by numeric value, strings by exact string value, and sequence values structurally by sequence elements
- Sequence values stay whole and are not flattened
- Zero collected items produce the empty list `[]`
- A single kept item is kept as the one element of a one-element list, so `distinct(((), ()))` returns `[()]`. (The bare two-argument form `distinct((), ())` is an arity error — the two empty sequences must arrive inside one collection value.)

Both call styles are supported: `distinct(collection)` and `collection.distinct`.

<!-- spec:distinct-family-tutorial -->
```
distinct((3, 1, 3, 2, 1, 2))

distinct(((1, 2), (1, 2), (3, 4)))

Values = 3, 1, 3, 2, 1, 2
Values.distinct
```

**Results:**
```
[3, 1, 2]

[(1, 2), (3, 4)]

[3, 1, 2]
```

`distinct` is a value boundary: the bare call returns one list value. Open the deduplicated items with caller-site spread:

```
Values = 1, 1, 2, 3
Values.distinct
Values.distinct*
```

**Results:**
```
[1, 2, 3]

1
2
3
```

`Values = ((1, 2), (1, 2), (3, 4))` followed by `distinct(Values)` removes the duplicate sequence value after the one bound collection value is opened one level (a lone list value is opened the same way); `Values.distinct` agrees — both return `[(1, 2), (3, 4)]`. `distinct(Values*)` is an arity error instead: the spread supplies the three pairs as three ordinary arguments, but `distinct(collection)` expects one. The same rule makes `distinct(1, 1)` an arity error — write `distinct((1, 1))`, which returns `[1]`.

### Take Prefix: `take`

`take(collection, count)` returns the first `count` top-level values of the bound collection, unchanged, as one list value.

- The count must evaluate to exactly one whole-number value
- `count <= 0` returns the empty list `[]`
- Counts larger than the sequence length return a list of all the items
- Sequence values are preserved whole as elements and are not flattened
- A single taken item is kept as the one element of a one-element list: `take(collection, 1)` returns `[item]`, while `first(collection)` returns the item itself

Both call styles are supported: `take(collection, count)` and `collection.take(count)`.

<!-- spec:take-family-tutorial -->
```
take((1, 2, 3, 4, 5), 3)

take(((1, 2), (3, 4)), 1)

range(1, 5).take(2)
```

**Results:**
```
[1, 2, 3]

[(1, 2)]

[1, 2]
```

`take(((1, 2), (3, 4)), 1)` keeps exactly one item, the sequence value `(1, 2)`, and returns it as the exact one-element list `[(1, 2)]` — the element stays exact inside the list. (The sequence shape `((1, 2))` is still not a writable KatLang value, but the list shape `[(1, 2)]` is.) `first(((1, 2), (3, 4)))` returns the bare item `(1, 2)` instead.

`take` is a value boundary: the bare call returns one list value. Open the taken items with caller-site spread:

```
range(1, 5).take(2)
range(1, 5).take(2)*
```

**Results:**
```
[1, 2]

1
2
```

`take((1, 2, 3), 0)` and `take((1, 2, 3), -2)` both return the empty list `[]`. `take((3, 4), (1, 2, 3))` is invalid because the count must be exactly one whole-number value, not a sequence value. The collection must arrive as one argument: `take([1, 2, 3])` is an arity error — `take(collection, count)` expects 2 arguments, the list is the one collection argument, and `count` is missing — while `take([1, 2, 3], 2)` returns `[1, 2]`. Spread supplies ordinary call arguments, so `take(Values*, 1)` with `Values = (1, 2, 3)` and `take([1, 2, 3]*, 2)` are arity errors too; `take(Values, 1)` returns `[1]`, and `Values.take(2)` returns the list value `[1, 2]` (use `Values.take(2)*` to spread it). A spread that lands on exactly the right argument count is still an ordinary call: `take([7]*, 1)` passes `7` and `1` and returns `[7]`.

### Skip Prefix: `skip`

`skip(collection, count)` returns the bound collection's items after skipping the first `count` top-level values, as one list value.

- The count must evaluate to exactly one whole-number value
- `count <= 0` returns a list of all the original items
- Counts larger than the sequence length return the empty list `[]`
- Sequence values are preserved whole as elements and are not flattened
- A single remaining item is kept as the one element of a one-element list: `skip` returns `[item]`, while `last(collection)` returns the item itself

Both call styles are supported: `skip(collection, count)` and `collection.skip(count)`.

```
skip((1, 2, 3, 4, 5), 3)

skip(((1, 2), (3, 4)), 1)

range(1, 5).skip(2)
```

**Results:**
```
[4, 5]

[(3, 4)]

[3, 4, 5]
```

`skip(((1, 2), (3, 4)), 1)` leaves exactly one item, the sequence value `(3, 4)`, and returns it as the exact one-element list `[(3, 4)]`; `last(((1, 2), (3, 4)))` returns the bare item `(3, 4)` instead.

`skip` is a value boundary: the bare call returns one list value. Supply the remaining items with caller-site spread:

```
range(1, 5).skip(2)
range(1, 5).skip(2)*
```

**Results:**
```
[3, 4, 5]

3
4
5
```

`skip((1, 2, 3), 0)` and `skip((1, 2, 3), -2)` both return `[1, 2, 3]`. `skip((1, 2), 'hello')` is invalid because the count must be exactly one whole-number value. `Values = (1, 2, 3)` followed by `skip(Values, 1)` and the list form `skip([1, 2, 3], 1)` both return the list value `[2, 3]`, and `Values.skip(1)` does the same (use `Values.skip(1)*` to spread it) — the one bound collection opens one level, whether grouped, list, or receiver. `skip(Values*, 1)` is an arity error: the spread supplies three ordinary arguments plus the count, but `skip(collection, count)` expects 2.

### Minimum: `min`

`min(collection)` returns the smallest top-level numeric element in the bound collection.

- The collection must be non-empty
- Each top-level element must be exactly one atomic numeric value
- Sequence values are not flattened or inspected recursively
- Strings are invalid

Both call styles are supported: `min(collection)` and `collection.min`.

```
min((10, 4, 7))

Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
(Data:0).min
```

**Results:**
```
4

1
```

Applying `min` to an empty collection is invalid because `min` requires at least one top-level numeric element. `min(((1, 2), (3, 4)))` is invalid because sequence-value items are preserved (not flattened), and each top-level item must be one atomic numeric value. `min(range(1, 5))`, `P = range(1, 5)` followed by `min(P)`, `Values = 1, 2, 3` followed by `min(Values)`, `Values.min`, `min((1, 2, 3))`, and `(1, 2, 3).min` all succeed — the one bound collection opens one level, whether it is a sequence value, a list value (such as the `range(1, 5)` result), or a dot-call receiver, so the grouped, list, and dot-call forms agree. `min(1, 2, 3)` is an arity error: `min(collection)` expects one argument. Selection such as `(Data:0).min` supplies the selected sequence value as the one collection argument, which `min` opens one level.

### Maximum: `max`

`max(collection)` returns the largest top-level numeric element in the bound collection.

- The collection must be non-empty
- Each top-level element must be exactly one atomic numeric value
- Sequence values are not flattened or inspected recursively
- Strings are invalid

Both call styles are supported: `max(collection)` and `collection.max`.

```
max((10, 4, 7))

Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
(Data:0).max
```

**Results:**
```
10

7
```

Applying `max` to an empty collection is invalid because `max` requires at least one top-level numeric element. `max(((1, 2), (3, 4)))` is invalid because sequence-value items are preserved (not flattened), and each top-level item must be one atomic numeric value. `max(range(1, 5))`, `P = range(1, 5)` followed by `max(P)`, `Values = 1, 2, 3` followed by `max(Values)`, `Values.max`, `max((1, 2, 3))`, and `(1, 2, 3).max` all succeed — the one bound collection opens one level, whether it is a sequence value, a list value (such as the `range(1, 5)` result), or a dot-call receiver, so the grouped, list, and dot-call forms agree. `max(1, 2, 3)` is an arity error: `max(collection)` expects one argument. Selection such as `(Data:0).max` supplies the selected sequence value as the one collection argument, which `max` opens one level.

### Summation: `sum`

`sum(collection)` adds the bound collection's top-level numeric elements from left to right and returns one numeric result.

- Each top-level element must be exactly one atomic numeric value
- Empty collections return `0`
- A single numeric value is treated as a one-element collection
- Sequence values are invalid and are not flattened
- Strings are invalid

Both call styles are supported: `sum(collection)` and `collection.sum`.

```
sum((10, 20, 30))

Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
(Data:0).sum
```

**Results:**
```
60

20
```

Applying `sum` to an empty collection returns `0`: `sum(())` and `sum([])` are both `0` — but `sum()` with no argument at all is an arity error, because absence of an argument is never an empty collection. `sum(((1, 2), (3, 4)))` is invalid because `sum` preserves sequence-value items (it does not flatten them), and each top-level item must be one atomic numeric value. `sum(range(1, 5))`, `P = range(1, 100)` followed by `sum(P)`, `Values = 1, 2, 3` followed by `sum(Values)`, `Values.sum`, `sum((1, 2, 3))`, `sum([1, 2, 3])`, `(1, 2, 3).sum`, and `{1, 2, 3}.sum` all succeed — the one bound collection opens one level, so the grouped, list, and dot-call forms agree. `sum(1, 2, 3)` and `sum(Values*)` are arity errors; to concatenate two stored collections, group the spreads into one collection value: with `A = 1, 2` and `B = 3, 4`, `sum((A*, B*))` is `10`, while `sum(A*, B*)` and `sum(A, B)` are arity errors. Selection such as `(Data:0).sum` supplies the selected sequence value as the one collection argument, which `sum` opens one level.

### Average: `avg`

`avg(collection)` averages the bound collection's top-level numeric elements and returns one numeric result.

- The collection must be non-empty
- Each top-level element must be exactly one atomic numeric value
- A single numeric value is treated as a one-element collection
- The C# runtime returns the decimal arithmetic mean — the exact total divided by the count, rounded once to 34 significant digits — for example `avg((1, 2))` returns `1.5` and `avg((-1, -2))` returns `-1.5`. (Lean's Int-only core approximates this with truncation toward zero, e.g. `avg((1, 2)) = 1` there — a model limitation, not the runtime contract.)
- Sequence values are invalid and are not flattened
- Strings are invalid

Both call styles are supported: `avg(collection)` and `collection.avg`.

```
avg((10, 20, 30))

Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
(Data:0).avg

avg((1, 2))
```

**Results:**
```
20

4

1.5
```

For finite elements, the exact total makes the numerical mean independent of their order, and it can differ from `sum(X) / count(X)`: `sum` adds from left to right in Decimal128, where a large intermediate value can absorb a small element before cancelling (`1 + 1e34` is `1e34` again). Collections containing NaN or an infinity keep the ordinary left-to-right IEEE sum divided by the count; intermediate overflow can make those results depend on order.

```
avg((1, 1e34, -1e34))
sum((1, 1e34, -1e34)) / 3
```

**Results:**
```
0.3333333333333333333333333333333333
0
```

When every addition is exact the two agree, displayed decimal places included (`avg((1.0, 2.00))` is `1.50`).

Applying `avg` to an empty collection is invalid because `avg` requires at least one top-level numeric element. `avg(((1, 2), (3, 4)))` is invalid because `avg` preserves sequence-value items (it does not flatten them), and each top-level item must be one atomic numeric value. `avg(range(1, 5))`, `P = range(1, 5)` followed by `avg(P)`, `Values = 1, 2, 3` followed by `avg(Values)`, `Values.avg`, `avg((1, 2, 3))`, and `(1, 2, 3).avg` all succeed — the one bound collection opens one level, whether it is a sequence value, a list value (such as the `range(1, 5)` result), or a dot-call receiver, so the grouped, list, and dot-call forms agree. `avg(1, 2, 3)` is an arity error: `avg(collection)` expects one argument. Selection such as `(Data:0).avg` supplies the selected sequence value as the one collection argument, which `avg` opens one level.

### Reduction: `reduce`

`reduce(collection, reducer, initial)` walks the bound collection from left to right and threads an accumulator through the top-level items.

- `reducer(element, accumulator)` receives the current item as one selected value — exactly what `S:i` returns
- A reducer whose only parameter is a collecting parameter, `R(*items)`, collects both callback slots as the exact list `[element, accumulator]`; this is the ordinary collecting-call rule, not a reducer-specific exception
- `reduce` passes the accumulated value as ONE ordinary argument, exactly like the direct call `reducer(element, accumulator)`: a normal accumulator parameter receives it as one structural value, a top-level collecting accumulator parameter collects it as one item (`[accumulator]`), and an explicit structural pattern such as `(acc, counter)` or `(*history)` opens it
- The reducer must return exactly one next accumulator value
- One sequence-value top-level element still contributes one fold step; the element is passed intact as one value, never opened or flattened
- Sequence-value accumulator states are allowed when they are returned as one sequence value
- Empty collections return `initial` unchanged

Both call styles are supported: `reduce(collection, reducer, initial)` and `collection.reduce(reducer, initial)`.

```
Add = x + total
reduce((1, 2, 3, 4), Add, 0)

TakeValue((tag, value), acc) = acc + value
reduce(((1, 10), (2, 20), (3, 30)), TakeValue, 0)

Stats(x, (acc, counter)) = (x + acc, counter + 1)
reduce((1, 2, 3, 4), Stats, (0, 0))

Append(item, (*history)) = (history*, item)
reduce((2, 3, 4), Append, 1)
```

**Results:**
```
10

60

(10, 4)

(1, 2, 3, 4)
```

No wrapper helper is required for sequence-value accumulators: a parenthesized sequence value such as `(a, b)` is one accumulator value, and the reducer receives it as ONE ordinary argument — the second argument of `reducer(element, accumulator)`. A structural accumulator pattern opens it explicitly: `(acc, counter)` binds its two items, and `(*history)` collects all of its items (a scalar accumulator such as the initial `1` is a one-item supply), a sequence and a list accumulator alike — `(0, 0)` and `[0, 0]` open the same way. A top-level collecting accumulator parameter does NOT open it: `Append(item, *history) = (history*, item)` collects `history = [accumulator]`, so the same fold nests each step instead (`reduce((2, 3, 4), Append, 1)` is then `(((1, 2), 3), 4)`). To grow a sequence-value accumulator, spread the prior items beside the new value with a comma — `(history*, item)`. The comma is required: `history* item` (without the comma) is the multiplication `history * item`, because a `*` with a same-line right operand always multiplies.
`reduce(collection, reducer, initial)` takes exactly three arguments: the collection, the reducer, and the initial accumulator. The one bound collection opens one level — `reduce((1, 2), reducer, initial)`, `Values = 1, 2` followed by `reduce(Values, reducer, initial)`, `P = range(1, 5)` followed by `reduce(P, reducer, initial)`, and `reduce([1, 2, 3], reducer, initial)` all call the reducer once per immediate item; nested sequence elements are not split recursively. Named sequence-valued helpers behave the same in dot form: `Values = (1, 2, 3)` followed by `Values.reduce(reducer, initial)` reduces over its three items. If a visibly parameterized reducer is the sole dotted control, `Values.reduce(reducer)` adds a targeted hint that the initial value is missing; the equivalent plain `reduce(Values, reducer)` remains an ordinary two-versus-three arity error. Inline and spread forms are arity errors: `reduce(1, 2, reducer, initial)` supplies four arguments, and `reduce(Values*, reducer, initial)` and `reduce(range(1, 5)*, reducer, initial)` spread the items into ordinary argument slots that overflow the three parameters. `reduce(A, B, reducer, initial)` with two stored collections is an arity error for the same reason — to reduce over both, group them into one collection: with `A = 1, 2` and `B = 3, 4`, `reduce((A*, B*), reducer, initial)` reduces over all four numbers, while `reduce((A, B), reducer, initial)` reduces over the two grouped values `(1, 2)` and `(3, 4)` (so a numeric reducer rejects them).
Results such as `acc, x` or any empty result are still invalid step outputs because `reduce` requires exactly one accumulator value at every step.

### Fixed Loop: `repeat`

`repeat` is a builtin algorithm that takes three arguments: a step algorithm, a count, and an initial state. It runs the step algorithm the given number of times, feeding each output back as the next input.

```
# Step: add 1 to x
Increment = x + 1

# Run 5 times starting from 0:
Increment.repeat(5, 0)
```

**Result:** `5`

Multi-output step algorithms maintain all outputs as state across iterations:

```
# Accumulate a running sum of 1..4
# State: (index, total)
Step = a + 1, total + a

# Run 4 times starting from (a=1, total=0), then select total:
Step.repeat(4, 1, 0) : 1
```

**Result:** `10`

(1 + 2 + 3 + 4 = 10, selected with `:1`.)

**Factorial:**

```
# State: (n, accumulator)
# Each step: advance counter, multiply accumulator
Fact = n + 1, acc * n

Fact.repeat(5, 1, 1) : 1
```

**Result:** `120`

### Conditional Loop: `while`

`while` is a builtin algorithm that runs a step algorithm repeatedly until a stop condition is reached.

**How it works:**

1. The step algorithm's **last output** is the continuation flag, a Boolean: `true` means continue, `false` means stop. A number (or any other non-Boolean value) in the flag position is a type error.
2. All outputs except the last form the working state, passed as input to the next iteration.
3. **Pre-check semantics:** the loop returns the state from the last iteration where the flag was `true`. The iteration that produces flag `false` is never committed.

```
# Step: decrement x, continue while x > 1
Step = x - 1, x > 1

Step.while(5)
```

**Result:** `1`

When `Step` runs with `x = 1`, it would produce `(0, false)` — the flag is `false`, so this result is discarded and the loop returns `1` from the previous iteration.

Multi-output state works the same way — only the last output is the continue-flag:

```
# Sum multiples of 3 or 5 below 1000
# State: (n, total) — last output is the continue flag
Algo = n - 1, total + if(n mod 3 == 0 or n mod 5 == 0, n, 0), n > 2

# Start from (n=999, total=0), select total:
Algo.while(999, 0) : 1
```

**Result:** `233168`

---

## Practical Examples

### Reusable Calculation with Parameters

A simple unit converter with one parameter:

```
# Convert between temperature units
FtoC = (f - 32) * 5 / 9

FtoC(212)
FtoC(32)
FtoC(98.6)
```

**Results:**
```
100
0
37.0
```

<a id="multi-output-example"></a>

### Returning a Sequence

Computing both area and circumference of a circle. The property's two output slots come back from the call as one sequence value, and `:` selects one item of it:

```
Circle = r * r * Math.Pi, 2 * r * Math.Pi

# Call to get area and circumference as one sequence value:
Circle(5)

# Pick just the area (index 0):
Circle(5) : 0
```

**Results:**
```
(78.53981633974483096156608458198758, 31.41592653589793238462643383279503)
78.53981633974483096156608458198758
```

### Loop-Based Example: Sum of a List

Compute the sum of all numbers in a multi-value property using `repeat`:

```
Numbers = 3, 5, 9, 1, 0, 6

# Step: advance index, accumulate Numbers:a
Step = a + 1, total + Numbers:a

# Repeat once per element, then select the accumulated sum:
repeat(Step, Numbers.count, 0, 0) : 1
```

**Result:** `24`

### Fibonacci Sequence

Compute the Nth Fibonacci number:

```
# State: (a, b) — consecutive Fibonacci numbers
Fib = b~, a + b

# 10 steps starting from (0, 1), take the first value:
Fib.repeat(10, 0, 1) : 0
```

**Result:** `55`

---

## Higher-Order Algorithms

> **Core idea:** pass a named algorithm or a brace algorithm when a caller expects a callable. A group of several slots or of a spread captures a value and so suppresses callable identity; redundant parentheses around one expression are only grouping and change nothing.

An algorithm can accept another algorithm as an argument and call it. This is how you write generic, reusable computation patterns.

### Algorithm as Argument

Fixed calls preserve argument expression boundaries. If a property expects multiple arguments and you already have a multi-output value, select the pieces explicitly (`value:i`) or use a spread expression (`value*`) when you intentionally want that result sequence to spread into call argument items.

```
Sum3 = a + b + c
Input = 1, 2, 3

# Input is one argument expression, so this is bad arity:
Sum3(Input)

# Explicit forms:
Sum3(Input:0, Input:1, Input:2)
Sum3(1, 2, 3)
```

Both explicit forms produce `6`.

Algorithms can also be passed as callable values:

```
# Apply takes a callable 'f' and calls it with 9
Apply = f(9)

# Pass an algorithm that adds 1 to its argument:
Apply{a + 1}
```

**Result:** `10`

You can also pass a named algorithm directly:

```
Apply = f(9)
Increment = x + 1

Apply(Increment)
```

**Result:** `10`

An algorithm needs no parameters to cross a higher-order boundary — `{42}` is as much an algorithm as `{a + 1}`, and a zero-argument call invokes it:

<!-- spec:zero-param-block-higher-order -->
```
Call0 = f()
Call0({42})
```

**Result:** `42`

A genuine capture is different: a parenthesized group of several slots, or of a spread, captures a *value*, and a captured value never carries the algorithm identity of what it encloses, so `Apply((Increment, Increment))` and `Call0((Const*))` fail even though the bare names work. Redundant parentheses are not a capture — parentheses group syntax and never introduce a boundary — so `Apply((Increment))` is exactly `Apply(Increment)`, `Call0((Const))` is `Call0(Const)`, and `Call0(({42}))` behaves exactly like `Call0({42})`.

### A Parameter Always Means This Call's Argument

Passing a callable binds the receiving parameter on the *callable* channel rather than the value channel. Calling that parameter works as shown above; reading it as a plain value asks the callable for a zero-argument result, which fails when the callable still needs arguments:

<!-- spec:callable-argument-parameter-shadowing -->
```
A = q + 1
Add1(x) = x + 1
F(x) = Add1(A)

F(7)
```

**Result:** error — `Add1`'s parameter `x` is bound to the callable `A`, and `A` still needs its implicit `q`, so demanding `x` as a value is an arity error.

The name `x` here happens to be a parameter of the *caller* `F` as well, and that changes nothing: a parameter always means the argument bound at this call, never a same-named binding from the surrounding algorithm. Renaming `F`'s parameter to `zz` produces exactly the same error. Either call the parameter — `Apply(x) = x(10)` with `Apply(A)` gives `11` — or pass a value instead of a callable.

Names the callee does *not* declare as parameters still resolve outward as usual, so a property nested in a brace body keeps reading its ancestor's parameter:

```
Outer(v) = {
    Inner = v + 1
    Inner
}

Outer(7)
```

**Result:** `8`

`Inner` belongs to `Outer` because it is written inside `Outer`'s braces, and that ownership is the only reason its `v` is `Outer`'s parameter: `Inner` is local to that scope, so a root-level `Inner(7)` does not resolve and `Outer.Inner` is refused as local-only. Indentation is not nesting. Written without the braces — `Outer(v) = Inner` on one line and `Inner = v + 1` indented beneath it — `Inner` would be a root property with its own implicit parameter `v`, callable from the root, and `Outer` would merely forward its `v` to it as an ordinary call; the same `8` would then come from implicit argument forwarding, not from lexical ownership. See [Parameters take part in the walk](#parameters-take-part-in-the-walk) for the ownership rule.

The rule holds in the other direction too. A parameter bound to a *value* is not callable, even when the surrounding algorithm received a callable under the same name:

<!-- spec:value-argument-parameter-shadowing -->
```
Inc(x) = x + 1

Apply(f) = {
    Inner(f) = f(2)
    Inner(5)
}

Apply(Inc)
```

**Result:** error — `Inner`'s parameter `f` is the value `5` at this call, so `f(2)` is not a call of a callable; the `Inc` that `Apply` holds under its own `f` is never consulted, and the program fails exactly as the standalone `Inner(5)` does.

Only the names a callee binds itself are hidden. `Inner(x)` below declares no `f`, so `f` still resolves outward to the callable `Apply` received:

<!-- spec:ancestor-callable-visible-without-same-named-parameter -->
```
Inc(x) = x + 1

Apply(f) = {
    Inner(x) = f(x)
    Inner(5)
}

Apply(Inc)
```

**Result:** `6`

Sequence builtins `filter`, `map`, and `reduce` are a higher-order case of ORDINARY argument binding. Their per-item callback argument is the selected element as one value (exactly what `S:i` returns for the traversed sequence `S`), bound exactly like the direct call `F(element)` — for `reduce`, `F(element, accumulator)`: a flat multi-parameter callback does not open it, and a nested pattern such as `F((x, y))` opens it explicitly, without recursive flattening. Ordinary higher-order calls such as `Apply(Increment)` use the same ordinary argument binding.

### Algorithms vs. Grouped Expressions

The distinction between braces, parentheses, and square brackets is critical. Their roles are:

| Syntax | Meaning |
|---|---|
| `( ... )` | Expression grouping/capture, or call-argument syntax after a callable — no new parameter scope and no declarations |
| `[ ... ]` | List construction — element expressions only, no declarations |
| `{ ... }` | Algorithm value — a new lexical scope that owns its inferred parameters, local declarations, and `open` |
| `{a + 1}` | Algorithm with parameter `a`, passable as an argument |

`{}` braces create an **algorithm** — a computation with its own identity and scope, which owns whatever parameters its body needs (`a` in the example above; an algorithm with zero parameters is still an algorithm). A `()` expression is **grouping**, not an algorithm — it has no scope of its own, so any free names inside it belong to the enclosing algorithm instead.

Only `{ ... }` creates an algorithm-level lexical scope, so only brace blocks (and the root) own declarations. Parentheses may group and compose output expressions, but an `open` declaration or a property definition inside `( ... )` is a parse error pointing you at braces:

```
M = {
    public P = 5
}

Y = {
    open M
    P + 1
}

Y
```

**Result:** `6`

Writing `Y = (open M ...)` or `(A = 5 ...)` instead is rejected — for example: "An 'open' declaration is not allowed inside parentheses. Use a `{ ... }` block for a scoped algorithm."

A brace block works anywhere an expression-valued algorithm is allowed, including directly as a call argument. The block's own opens and local properties resolve inside the block; they never leak outward or become implicit parameters of the surrounding algorithm:

```
M = {
    public P = 5
}

Identity(x) = x

Identity({
    open M
    P + 1
})
```

**Result:** `6`

When a block has defined output and no free parameters, `{...}` and `(...)` produce the same result:

```
(1, 2, 3).count
{1, 2, 3}.count
```

**Results:**
```
3
3
```

With no contents, `()` is the empty sequence value (a real value, displayed as `()`), while `{}` is an empty algorithm body with no defined output. They are not interchangeable: `()` is a value you can store, count, compare, and spread, whereas `{}` produces no value at all and is an error when used where a value is required.

An algorithm — with or without parameters — is a computation that can produce zero or more outputs. A sequence value is what you get when produced outputs are **captured** as one value: `(1, 2)` captures two outputs into one value. Call-argument parentheses do not capture — they are call syntax, and the argument list's slots become the call's separate arguments. Capturing happens one level in, when you write an extra pair of parentheses inside the argument list:

```
Add(x, y) = x + y

Add(1, 2)
```

**Result:** `3`

`Add(1, 2)` passes two arguments. `Add((1, 2))` passes one argument — the sequence value `(1, 2)` — so the two-parameter callable rejects it: "Callable `Add(x, y)` expects 2 arguments, but was called with 1 argument." The one-argument shape is exactly what the fixed one-collection builtins expect: `sum((10, 20, 30))` is `60`, while `sum(10, 20, 30)` is a three-argument arity error under the fixed `sum(collection)` signature.

---

## Spread with the Postfix Star

> **Core idea:** postfix `*` opens exactly one sequence or list boundary and supplies those items to the surrounding context. It is explicit, one level deep, and different from multiplication and the prefix collect marker.

Expression spreading is written with the postfix star — the **spread marker**. A spread expression `value*` evaluates `value` exactly once and contributes the items of its evaluated value to the surrounding item supply (output rows, call argument slots, or list/sequence elements), opening exactly ONE item-producing boundary. Conceptually `spread : Value → Supply` — a spread expression does not return or create a sequence or list by itself; the RECEIVER decides what the supplied items become. A sequence value or an exact [list value](#lists) supplies its contained items; an atom or string supplies itself as one item. The marker follows any completed expression — `items*`, `Calculate(x)*`, `(a + b)*`, `[1, 2]*`, `()*`, `[]*` — and repeated stars compose through an intermediate capture: `value**` means `(value*)*` (see [Repeated Spread Is Composition](#repeated-spread-is-composition)).

The same star is the multiplication operator, and multiplication wins whenever it can: **a `*` followed by a valid right operand is multiplication, and neither whitespace nor a line break decides** — `a*b`, `a* b`, `a *b`, `a * b`, and `a*` followed by `b` on the next line are all the product `a * b`, exactly like the trailing operator `a *` followed by a line `b`. The `*` is the spread marker only when the surrounding syntax closes the expression before any right operand could follow: before a comma, before a closing `)`, `]`, or `}`, at the end of the program, or before a declaration (`a*` followed by a line `b = 1` is the spread of `a` and then the definition of `b`, because a definition head is never an operand). To spread `a` and then supply another item, the comma is REQUIRED — `a*, b`, or `a*,` at the end of a line with `b` on the next — because `a* b` and `a*` newline `b` both multiply. The spread marker itself must be written directly attached to its operand: `a*`, `Calculate(x)*`, `(a + b)*`. A detached `a *` that no right operand follows — `F(values *)`, `(values *)`, `values *` at the end of the program — is neither multiplication nor spread; it is an error that tells you to write `values*` (or to supply the missing operand). This is the general **marker attachment law**: the structural and annotation markers — collect `*items`, spread `items*`, Grace `~x` and `x~` — are directly attached to the syntax they modify, while ordinary operators such as multiplication may be spaced freely. Whitespace can therefore never turn one valid operation into another: `a* b` and `a *` newline `b` multiply exactly like `a * b`, and the only thing spacing decides is whether a marker is well-formed.

The most common receiver for a spread is a call. The explicit form to learn first is `Target(A*)`: it evaluates `A` once, spreads its items, and supplies them as separate argument slots of `Target`. The same call has a fluent left-to-right spelling — the **fluent supply chain**: a dot may chain directly after a spread, and `A*.Target` is exactly equivalent to `Target(A*)`. The spread receiver is an item supply, not a value, so the parser lowers the dotted form to that same lexical call with the spread items as the leading arguments — both spellings build one AST and evaluate the operand once. This reads a multi-step calculation left to right instead of inside out: `x.Calculate*.Target` evaluates `x.Calculate`, spreads the completed result, and supplies the items to `Target(...)`; `Forward(*items) = items*.Target` forwards collected items and is the same call as `Forward(*items) = Target(items*)`.

To construct one sequence argument from a spread value and another expression, capture the pair explicitly with parentheses: `Use((1*, Tail))` passes one sequence-valued argument, while `Use(1*, Tail)` passes two argument slots.

Spread is **total** — every value has an item view. A sequence or list value supplies its contained items; an atom or string contributes itself as a one-item supply, so spreading an atom is observationally neutral in a collecting context. (This is a fact about the item view, not a claim that atoms and collection values are the same kind of value.)

<!-- spec:scalar-spread-neutral -->
```
Collect(*items) = items

Collect(5)
Collect(5*)
```

**Results:**
```
[5]
[5]
```

A line break after the star changes nothing. When the next line begins with a right operand, the star is multiplication whichever way it is spaced:

```
X*
Y
```

is interpreted as:

```
X * Y
```

To spread `X` and then emit `Y` as the next output row, end the spread row with a comma — the trailing comma keeps the expression list open across the newline, and the comma is exactly what tells the parser the spread slot is complete:

```
X*,
Y
```

This is the two-slot expression list `X*, Y`. When nothing follows the star — end of the program, a closing delimiter, or a definition on the next line — `x*` simply spreads `x` followed by nothing:

```
X = 1, 2
X*
Y = 5
```

**Result:**
```
1
2
```

The same applies to a definition body that ends with a spread: `P = a*` on one line followed by `b` on the next is the multiplication `P = a * b`, since a trailing operator continues a definition body across the newline. Close the body when an output row follows — with capture parentheses, `P = (a*)`, which capture the spread supply exactly as the single-name definition does anyway, or with a brace body, `P = { a* }`.

Use parentheses for one sequence value:

```
(X, Y)
```

A spread expression is one whole expression-list slot, so:

```
Use(a, b*)
```

supplies `a` and then `b`'s items as separate argument slots. Because the `(` keeps the argument list open across lines, a newline separates slots there too, so

```
Use(a
b*)
```

means exactly the same `Use(a, b*)`. On one line the comma is never optional: `Use(a b*)` is the missing-separator error like every other same-line pair, and a slot that FOLLOWS a spread — on the same line or on the next — needs the explicit comma for a second reason as well (`b* c` is multiplication).

A spread applies only to its own operand. `a, b*, c` is an expression list of three slots — every same-line comma is required, and the comma after `b*` is required even across a line break, because `b* c` and `b*` newline `c` are the multiplication `b * c`. Use `(a, b*, c)` for one sequence value.

The explicit parenthesized form can intentionally force a different value boundary around a spread expression, but it does not change which operand the spread owns. `Use((a, b*))` and `Use((a, (b*)))` both spread only `b`.

This is different from comma and parentheses: comma preserves structural output or argument boundaries, parentheses create one sequence value, and a spread supplies already evaluated result content. A bare spread does not create a new structural sequence value, does not preserve or merge properties, and does not recursively flatten nested sequence values. If the spread operand has no defined output, evaluation fails; the empty sequence value `()` is defined, so `()*` simply contributes no items.

Parentheses around a spread preserve one sequence-value result boundary. Use this when a spread result should travel as one value at a boundary-sensitive site such as a call argument, named property, or loop step output.

`{ }` introduces an algorithm/body scope. The outer body block of a program or property can be omitted and is transparent as that program or property's output. A nested `{ }` is still an expression boundary, like nested `( )`, except that it also introduces local scope. Multi-output nested expression boundaries are preserved unless you explicitly spread them with the spread marker.

Output/body newlines are useful for report-shaped output without commas:

```
SalaryExpenses(3800, 1, 0)
''
SalaryExpenses(50, 0, 0)
```

This behaves like comma-separated output rows:

```
SalaryExpenses(3800, 1, 0), '', SalaryExpenses(50, 0, 0)
```

Inside call argument lists and explicit parenthesized sequence values the list stays open across lines, so a newline separates slots there just as a comma does; on one line the comma is required. Use parentheses when one sequence value is intended, such as `(a, b, c)`.

<!-- spec:root-spread-then-value-slot -->
```
First = 1, 2
Second = 3, 4

First*, Second
```

**Results:**
```
1
2
(3, 4)
```

`First*` opens `First` into its two items as root rows, and `Second` stays one sequence-valued row — the spread does not merge the two properties into one sequence value. The comma is required: `First* Second` would be the multiplication `First * Second`.

`B = 1*, 2` is the expression list `1*, 2` — a spread of the scalar `1` followed by a separate `2` slot. Without the comma, `1* 2` would be the multiplication `1 * 2`:

```
A = 1, 2
B = 1*, 2

A.count
B.count
```

**Results:**
```
2
2
```

Parenthesizing a spread plus the following expression-list slot keeps those results as one sequence value. `(First*, Second)` is a parenthesized expression list whose first slot is the spread — the comma is required here too, since `(First* Second)` would multiply:

```
First = 1, 2
Second = 3, 4

Test = (First*, Second)
Test.count
```

**Results:**
```
3
```

Spread projects only one immediate level. Each spread contributes its spread items as separate root rows, and the expression after the comma is a separate slot:

<!-- spec:spread-one-level-family -->
```
(1, 2)*, 3
1*, (2, 3)
(1, (2, 3))*, 4
```

**Results:**
```
1
2
3

1
(2, 3)

1
(2, 3)
4
```

| Expression | Interpretation |
|---|---|
| `1, 2, 3` | Single algorithm producing 3 outputs |
| `1*, 2, 3` | Three expression-list slots: the spread `1*`, then `2`, then `3` |
| `1* 2, 3` | The star has a right operand, so it multiplies regardless of spacing: the slots are `1 * 2` and `3`, producing `2, 3` (`1*` followed by a line `2, 3` reads the same way) |
| `(1*, 2), 3` | The parenthesized expression list `(1*, 2)` is one sequence-valued output, followed by the separate output `3` |
| `(1, 2)*, 3` | The spread applies to `(1, 2)` (spreading its items `1, 2`); after the required comma, `3` is a separate expression-list slot. Produces `1, 2, 3` |
| `(1, (2, 3))*, 4` | Spread opens one level: `1` and the intact inner sequence value `(2, 3)` become items, and `4` is a separate slot, producing `1, (2, 3), 4` |
| `((1, 2))*, 3` | Sequence normalization removes the redundant unary parentheses during value construction, so `((1, 2))` is the value `(1, 2)`; the spread opens its items and `3` is a separate slot, producing `1, 2, 3` — same as `(1, 2)*, 3` |
| `1, { 2, 3 }` | Preserves the nested block boundary, producing `1, (2, 3)` |
| `1*, { 2, 3 }` | `1*` spreads `1`, then after the required comma the block `{ 2, 3 }` is a separate expression-list slot. Produces `1, (2, 3)` |

### Capture Parentheses

> **Parentheses group syntax; they do not introduce a semantic boundary. Around a supply-producing expression they perform capture — that is the one case where the parentheses do something.**

Around an ordinary single expression, parentheses are redundant grouping and the group *is* that expression, whatever its kind: `(7)` is `7`, `([1, 2])` is `[1, 2]`, `(A)` is `A`, `(Obj.X)` is `Obj.X`, `(F(1))` is `F(1)`, `(A:0)` is `A:0`, `((1, 2))` is `(1, 2)`, and `(())` is `()`. Nothing downstream can tell the group from its content — not a call's argument binding, not a collecting or patterned parameter, not a stored property, not the zero-argument property cache, not a dot-call receiver (`(Obj).X` reads Obj's own `X` exactly like `Obj.X`), not a spread (`(A)*` is `A*`), and not a call delimiter (`(F)(1)` is `F(1)`). Around a spread, they are the capture receiver (`capture : Supply → Value`): the supplied items materialize as ONE canonical sequence value through [sequence normalization](#sequence-normalization) — two or more items become a sequence holding them, exactly one item becomes that item's normalized value, and an empty supply becomes `()`. Capture is an operation on a supply that was actually produced; it does not turn a body with no output rows into `()`, which stays the error described in [Calls Return One Value](#calls-return-one-value). The pair below is the clearest picture of the Value/Supply distinction:

<!-- spec:spread-capture-count -->
```
A = [1, 2, 3]

(A*).count
```

**Result:** `3`

`A*` produces a three-item supply; the parentheses capture it into the one sequence value `(1, 2, 3)`, and `.count` counts that value's items.

The unparenthesized fluent form is a different program:

```
A = [1, 2, 3]
A*.count
```

**Result:** error — `A*.count` is the fluent supply chain, exactly `count(A*)`: the three items become three separate argument slots, and the fixed `count(collection)` signature reports an arity error.

Grouping only the operand changes nothing: `(A)*.count` groups `A` before the star, so the spread is still the fluent receiver — it is `count((A)*)`, the same arity error. What changes the meaning is capturing the **spread** (`(A*)`), not parenthesizing its operand.

### Repeated Spread Is Composition

A spread expression is itself a completed expression, so it can wear another star. There is no special depth operator — the second star is ordinary postfix composition:

`value**` means exactly `(value*)*`.

The first star produces a **supply**, not a value (`spread : Value → Supply`), and a spread marker needs a value to operate on. Between the two stars the ordinary expression boundary performs **capture** (`capture : Supply → Value`) — the same operation written parentheses perform. The full pipeline is:

```
Value ──spread──▶ Supply ──capture──▶ Value ──spread──▶ Supply
```

conceptually `value** = spread(capture(spread(value)))`. The intermediate capture is not an implementation accident; it follows from ordinary KatLang expression composition. Avoid reading `value**` as "spread the value, then spread the result again" — the first spread has no value result to re-spread; it is the capture step that turns the supply back into a value for the second star.

Because capture applies sequence normalization, what a second star changes depends only on how many items the FIRST spread supplies:

- **Zero items** — the capture is `()`, whose item view is also empty: `[]*` and `[]**` both contribute nothing.
- **Exactly one item** — singleton capture collapses to that item. If it is a structured value, the second star opens one more boundary: `[[7]]*` contributes `[7]`, while `[[7]]**` contributes `7`. A scalar stays neutral: `[7]*` and `[7]**` both contribute `7`.
- **Two or more items** — capture groups the items as one sequence whose spread restores exactly the same items: a fixed point. The second star does NOT open the individual items.

<!-- spec:repeated-spread-singleton-opens -->
```
Collect(*items) = items

Collect([[7]]*)
Collect([[7]]**)
Collect([7]*)
Collect([7]**)
```

**Results:**
```
[[7]]
[7]
[7]
[7]
```

The multi-item fixed point is the case to internalize — repeated spread is **not** recursive flattening:

<!-- spec:repeated-spread-fixed-point -->
```
Collect(*items) = items
A = [[1, 2], [3, 4]]

Collect(A*)
Collect(A**)
Collect((A*)*)
```

**Results:**
```
[[1, 2], [3, 4]]
[[1, 2], [3, 4]]
[[1, 2], [3, 4]]
```

The first star supplies the two inner lists. The capture between the stars groups them as `([1, 2], [3, 4])`, and the second star re-spreads that captured sequence back into the same two items — never into `1, 2, 3, 4`. A second star changes the observable supply only when the first spread contributes exactly one structured value that exposes another item boundary.

Repeated spread exists as a compositional consequence of the postfix syntax; it is rarely the clearest way to write anything. To dig into nested data, prefer selecting the level you mean (`A:0*`), and when recursive flattening to numeric atoms is genuinely intended, that is what [`atoms`](#atoms) is for.

### Value and Supply at a Glance

Every form below is decided purely syntactically; the receiver of the supply decides what the items become:

| Form | Meaning |
|---|---|
| `A:0*` | Select `A:0` as one value, then spread the selected value — the star attaches to the completed index |
| `(A:0)*` | The same select-then-spread, with explicit grouping |
| `A*.F` | Supply `A*`'s items to `F` — exactly `F(A*)` |
| `A*.F*` | Call `F(A*)`, then spread `F`'s one result value |
| `A**.F` | Repeated (capture-law) spread supplies the arguments — exactly `F(A**)` |
| `(A*).F` | Capture the spread supply as one sequence value, then dot-call `F` on that one value — exactly `F((A*))` (a collecting `F` collects it as ONE item, per the [collector rule](#collecting-explicit-parameters); only `A*.F` supplies the items) |
| `A*:0` | Invalid — selection cannot be applied directly to an item supply (targeted parse error) |
| `(A*):0` | Capture the spread supply into one sequence value, then select from it |

Select-then-spread and capture-then-select are different operations:

<!-- spec:select-spread-vs-capture-select -->
```
A = [[1, 2], [3, 4]]

(A:0)*,
(A*):0
```

**Results:**
```
1
2
[1, 2]
```

`(A:0)*` selects the stored list `[1, 2]` and spreads its elements into two rows; `(A*):0` captures the two-item spread supply as one sequence value and selects its first item — the intact list `[1, 2]`. The comma after `(A:0)*` matters: without it the `(` on the next line is a right operand and the star is the multiplication `(A:0) * (A*):0`, which fails on the list operands. Writing `A*:0` directly is a targeted parse error: "Selection cannot be applied directly to a spread expression — a spread supplies items to the surrounding item supply, not one selectable value," and the message names both rewrites so you can pick the intended one.

---

## Lists

> **Core idea:** `[items]` creates one list value. Unlike a sequence, a list keeps its boundary whether it holds zero, one, or many items, and nested list boundaries stay significant.

Square brackets construct a **list value** — KatLang's second collection kind, complementing sequences:

<!-- spec:list-literal -->
```
[1, 2, 3]
```

**Result:** `[1, 2, 3]`

A list literal always evaluates to exactly ONE list value. Its elements use the ordinary expression-list rules (commas separate elements on one line, a newline separates elements while the `[` is open, and an already-open `[` spans lines just like `(` and `{`), but unlike parenthesized sequences, **[sequence normalization](#sequence-normalization) never removes a list boundary**: a list preserves its exact element count and nesting, while each element expression still follows the ordinary evaluation rules (so `[(7)]` is `[7]`).

<!-- spec:list-exactness -->
```
[7] == 7
[[1, 2]] == [1, 2]
[[]] == []
```

**Results:**
```
false
false
false
```

`[]` is the empty list, `[7]` is a singleton list (it never collapses to `7`), and `[[7]]` is a singleton list containing another singleton list. List equality is structural and recursive: `[1, 2] == [1, 2]` is `true`, and `[1, [2]] == [1, 2]` is `false`.

Lists are observably immutable: assigning a list to another name shares the same value, and no operation modifies a list in place.

### Lists versus Sequence Values

Lists and sequence values are **different value kinds** — equal elements never make them equal:

<!-- spec:list-vs-sequence-kind -->
```
[] == ()
[1, 2] == (1, 2)
```

**Results:**
```
false
false
```

The conceptual split:

| Kind | Written | Role |
|---|---|---|
| sequence `()` | parentheses | the canonical captured value — sequence normalization removes singleton and redundant sequence boundaries |
| list `[]` | brackets | a collection value whose structure is preserved exactly |
| item supply | (no literal) | the ordered items presented to an operation or binding — not a value kind; consumed by capture, collect, and binding |

Ordinary parentheses stay a redundant SEQUENCE grouping even around lists:

<!-- spec:list-redundant-parens-canonicalize -->
```
([1, 2]) == [1, 2]
```

**Result:** `true`

Neither empty collection is an operator identity: `[] > 1` and `() > 1` are both type errors, because neither value is a numeric scalar. They still differ as values — `[] == ()` is `false` — and they differ at the supply boundary: `F([])` passes one empty-list argument while `F([]*)` supplies zero arguments.

### Indexing Lists

Selection `:` indexes into list values: `value:index` selects ONE immediate element by zero-based position, using exactly the same index rules as sequence selection. The selected element is returned exactly as stored — a nested list element stays an exact list, a sequence-valued element stays a sequence value, and nothing is flattened, spread, or converted between kinds.

<!-- spec:list-index-nested-element-stays-exact -->
```
Rows = [[1, 2], [3, 4]]
Rows:0
Rows:0:1
```

**Results:**
```
[1, 2]
2
```

`Rows:0` selects the stored element `[1, 2]` (one opaque list, count 1), and chaining `:` selects one level at a time, so `Rows:0:1` is `2`. Exact kinds survive selection: `[[1, 2]]:0 == [1, 2]` is `true` while `[[1, 2]]:0 == (1, 2)` is `false`.

Collection-producing builtin results are exact lists, so they index directly — no spread-and-recapture step is needed:

<!-- spec:list-index-builtin-results -->
```
range(1, 3):2
```

**Result:** `3`

Likewise `take([1, 2, 3], 1):0` is `1` and `[3, 1, 2].order:0` is `1`.

Empty and past-the-end positions report the same out-of-range index error as sequences: `[]:0`, `[1, 2]:2`, and `[1, 2]:100` are all index errors — never `()`, `[]`, or a default value.

Indexing and spread stay distinct operations: `A:0` selects one element, while `A*` opens the whole list into the surrounding item supply. With `A = [1, 2]`, `A:0` is `1` and `B = A*` captures the canonical sequence `(1, 2)`.

### Spreading Lists

A spread expression opens exactly ONE list boundary into the surrounding item supply — the same spread marker and rules as sequence values. Because single-name assignment is capture (not deconstruction), the captured spread becomes a canonical sequence:

<!-- spec:list-spread-capture -->
```
A = [1, 2, 3]

x = A
y = (A*)

x
y
```

**Results:**
```
[1, 2, 3]
(1, 2, 3)
```

This distinction is essential: `x = value` preserves the value, `x = (value*)` opens one boundary and captures the resulting item supply. The parentheses close the definition body: a bare `y = A*` followed by the output row `x` on the next line would be the multiplication `y = A * x`, because a line break never separates a `*` from a right operand (see [Spread with the Postfix Star](#spread-with-the-postfix-star)).

Spread opens only the outermost boundary:

<!-- spec:list-spread-edges -->
```
A = []
B = [7]
C = [[7]]

A*,
B*,
C*
```

**Results:**
```
7
[7]
```

`A*` supplies zero items (its output row vanishes), `B*` supplies `7`, and `C*` supplies the inner list `[7]` intact. Each spread row that another row follows ends with a comma: `A*` directly followed by a line `B*` would be the multiplication `A * B*`, which is rejected because a spread is not a scalar operand.

Spread also works INSIDE list literals — a spread element inserts its item supply into the list being constructed:

<!-- spec:list-literal-spread-elements -->
```
A = 1, 2, 3

[A*]
[0, A*, 4]
```

**Results:**
```
[1, 2, 3]
[0, 1, 2, 3, 4]
```

Non-spread values stay single elements; only an explicit spread slot (`value*`) opens them:

<!-- spec:list-elements-preserve-boundaries -->
```
A = [1, 2]
B = [3, 4]

[A, B]
[A*, B*]
[A, B*]
```

**Results:**
```
[[1, 2], [3, 4]]
[1, 2, 3, 4]
[[1, 2], 3, 4]
```

An empty spread contributes no elements, while a non-spread `()` or `[]` element stays one visible element:

<!-- spec:list-empty-spread-neutral -->
```
[1, []*, 2]
[1, ()*, 2]
```

**Results:**
```
[1, 2]
[1, 2]
```

### Lists in Calls and Deconstruction

Calls never open lists implicitly. A list passed without spread is ONE argument; explicit spread supplies its elements:

<!-- spec:list-call-boundary -->
```
F(a, b, c) = a + b + c
One(x) = 7

A = [1, 2, 3]

One(A)
F(A*)
```

**Results:**
```
7
6
```

`F(A)` without the spread is an arity error (one argument for three parameters), and `F([]*)` supplies zero arguments. An ordinary dotted call `A.F(9)` passes the whole list `A` as one leading argument — it is `F(A, 9)`. The graced source `A~.F(9)` is the same ordinary dot edge with frontend-only postfix Grace on `A`, so it keeps the same one-argument receiver and list opacity.

Multi-target **deconstruction**, by contrast, is an unpacking receiver: a right-hand side that is exactly one list value opens the list and matches its elements — the same rule that already opens a lone sequence value, and the same bindings the explicit spread `x, y, z = [1, 2, 3]*` produces. (The two written forms coincide except for one exotic shape: a singleton list whose lone element is itself a sequence or list, such as `[(1, 2)]`, where the spread form re-groups through a capture boundary and opens one level further.)

<!-- spec:list-lone-deconstruction -->
```
x, y, z = [1, 2, 3]

x
y
z
```

**Results:**
```
1
2
3
```

Only the OUTER lone structure opens — nested values stay intact, and a list that is one item of an already multi-item supply stays one value (`x, y = [1, 2], 3` binds `x = [1, 2]`, `y = 3`):

<!-- spec:list-deconstruction-not-recursive -->
```
x, y = [[1, 2], 3]

x
y
```

**Results:**
```
[1, 2]
3
```

A collecting binding COLLECTS the unmatched items as one list — the same value kind the collection builtins produce:

<!-- spec:collecting-binding-exact-list -->
```
x, *rest = [1, 2, 3]

x
rest
```

**Results:**
```
1
[2, 3]
```

With `x, *rest = [1]` the collected list is the empty list `[]`, and with `x, *rest = [1, 2]` the singleton segment is the one-element list `[2]` — exact collection never erases the list boundary. A lone collecting binding uses the same exact collection rule: `*items = [1, 2, 3]` binds `items = [1, 2, 3]`; `*items = []` binds `items = []`.

### Lists and Collection Builtins

Sequence builtins accept lists directly: the builtin's post-binding collection view opens ONE outer boundary of a lone collection value — a lone grouped sequence value or a lone list value — so a stored list feeds a builtin without any spread:

```
count([1, 2, 3])
```

**Result:** `3`

And the collection-producing builtins (`filter`, `map`, `order`, `orderDesc`, `distinct`, `take`, `skip`, `range`, `atoms`) materialize their results as lists: zero kept items produce `[]`, one kept item produces the one-element list `[item]`, and nested elements stay exact.

```
A = [1, 2, 3]

A.take(1)
tail = A.skip(1)
tail
```

**Results:**
```
[1]
[2, 3]
```

Collecting bindings and collection builtins agree on the result kind — both produce lists — while ordinary single-name capture applies sequence normalization. Compare:

```
A = [1, 2, 3]

x = (A.take(1)*)
x

head, *rest = A
rest
rest == A.skip(1)
```

**Results:**
```
1
[2, 3]
true
```

`x = (A.take(1)*)` spreads the one-element list `[1]` and CAPTURES the single item through sequence normalization (`x = 1`), while the collecting binding COLLECTS the remaining items as the exact list `[2, 3]` — equal to `A.skip(1)`. The rule of thumb is the operation triple: **ordinary value capture applies sequence normalization (`capture`), collecting binding collects an exact list (`collect`), and the spread marker spreads one boundary (`spread`).**

`range` and `order` produce lists too:

```
range(1, 3)
order([3, 1, 2])
```

**Results:**
```
[1, 2, 3]
[1, 2, 3]
```

Only a LONE list opens during collection binding: a nested list stays one opaque item (`count((1, [2], 3))` is `3`), and sibling lists inside one collection stay separate items (`count(([], []))` is `2` — note the grouping parentheses; the bare two-argument `count([], [])` is an arity error). Spread does not feed the collection parameter either: `count([1, 2, 3]*)` and `sum([1, 2, 3]*)` supply three ordinary arguments each and are arity errors — use the spread-free `count([1, 2, 3])` and `sum([1, 2, 3])`, which bind the list as the one collection argument.

`atoms` also traverses list values: it recursively collects every numeric atom through both sequence and list boundaries and returns them as one exact list — see [Atoms](#atoms).

---

## Atoms

Algorithms in KatLang can produce structured, nested outputs — sequence values inside sequence values, exact lists inside lists, or any mix of the two. The `atoms` builtin recursively collects every numeric atom from that structure — opening **both** sequence and list boundaries, depth-first and left to right — and returns them as one [list value](#lists).

<!-- spec:atoms-recursive-flatten -->
```
atoms(((1, 2), (3, 4)))
```

**Results:**
```
[1, 2, 3, 4]
```

`atoms` is a collection-producing builtin like `order` or `range`: the call always returns one exact list, whatever the input kind and however many atoms were found. Empty and singleton results keep their list structure:

<!-- spec:atoms-exact-list-result -->
```
atoms(7)
```

**Results:**
```
[7]
```

`atoms(7)` is the singleton list `[7]`, never the bare `7` (`atoms(7) == [7]` is `true`; `atoms(7) == 7` is `false`), and `atoms((1, 2))` is the exact list `[1, 2]`, never the sequence `(1, 2)`. A no-atom input — `atoms('text')`, `atoms(())`, `atoms([])` — is the visible empty list `[]`. Strings and other non-numeric leaves contribute no atoms: `atoms((1, ['a', 2]))` is `[1, 2]`.

List values are traversed exactly like sequence values:

<!-- spec:atoms-list-traversal -->
```
atoms([1, 2])
```

**Results:**
```
[1, 2]
```

Mixed nesting flattens depth-first, left to right, into one flat list of atoms — container boundaries are opened, never preserved, with no sorting and no deduplication:

<!-- spec:atoms-mixed-traversal -->
```
atoms([(1, 2), [3, [4]]])
```

**Results:**
```
[1, 2, 3, 4]
```

Because the result is an ordinary exact list, it composes directly with every collection consumer — `atoms((3, 1, 2)).order` is `[1, 2, 3]`, `atoms((1, 2, 3)).count` is `3`, and list indexing works: `atoms((10, 20)):0` is `10`. List-producing builtins compose directly with `atoms` too, with no spread-and-recapture workaround:

<!-- spec:atoms-list-composition -->
```
[1, 2, 3].skip(1).atoms
```

**Results:**
```
[2, 3]
```

The call boundary is unchanged: `atoms(value)` takes exactly one argument, an unspread list is one argument, `atoms(1, 2)` is an arity error, and `atoms([1, 2]*)` spreads two ordinary arguments — also an arity error (regroup with `atoms(([1, 2]*))` if you need to pass spread items as one value). Only explicit caller-site spread turns the result into an item supply: `atoms(A)*` contributes the collected atoms to the surrounding items. Finally, `atoms` returns a list, so `if(atoms((1, 2)), a, b)` is invalid: a condition requires a Boolean value and rejects lists rather than searching their contents.

### Opening One Level vs. Flattening

KatLang keeps three operations distinct, so pick the one that matches your intent:

- A plain value reference such as `X` **preserves one value boundary** — a sequence value travels as one value.
- A spread expression `X*` **opens one level**, contributing the sequence value's immediate items to the surrounding output, argument list, or item supply.
- `atoms(X)` **recursively collects** every numeric atom, erasing all sequence-value and list structure, and materializes them as one exact list.

```
X = (1, 2, 3)
X*
```

**Results:**
```
1
2
3
```

`X*` spreads only one level, so `((1, 2), (3, 4))*` produces `(1, 2), (3, 4)` with the inner boundaries intact, while `((1, 2), (3, 4)).atoms` recursively flattens to the single exact list `[1, 2, 3, 4]` (append `*` to open that list into an item supply).

---

## Conditional Algorithms

The `if` builtin handles simple branching. For algorithms that need to dispatch based on structure or select from many cases, KatLang provides **conditional algorithms** — a form of pattern matching. A conditional algorithm is defined by writing multiple clause-style branches, each specifying a pattern to match against the arguments.

Each branch pattern is a closed input specification: the branch body cannot acquire additional implicit parameters. Pattern binders and names captured from enclosing scopes remain available, and nested brace algorithms and clause families follow their ordinary scope rules. Implicit forwarding to a referenced helper may use the branch's pattern binders, just as forwarding behind an explicit parameter list uses its declared parameters. If a proven value demand such as `Math.Abs(A)` needs an implicit parameter that the pattern does not bind, elaboration reports that missing name. An unforwarded bare helper reference instead keeps the ordinary zero-argument arity failure. A closed declaration inside a brace block is checked even when that block occurs in an output row, call argument, capture, or list element; ordinary higher-order argument and capture positions still suppress implicit forwarding as usual.

### Basic Pattern Matching

Conditional algorithms use the same clause-style definition syntax as ordinary explicit parameter patterns: `Name(pattern) = body`. Use `public Name(pattern) = body` when the clause family should be externally exposed. Public visibility is family-level, so every clause in a same-name family must either include `public` or omit it. On the left-hand side of `=` in definition context, `Name(...)` is not a call expression. A same-name family with multiple clauses, or a clause head with literals/mixed matching structure, becomes a conditional algorithm. Conditional branches are tried top to bottom — the first match wins.

```
Sign(1) = 100
Sign(-1) = -100
Sign(x) = 0

Sign(1)
Sign(-1)
Sign(42)
```

**Results:**
```
100
-100
0
```

A variable name in a pattern (like `x`) matches any value — it acts as a catch-all. Number literals match only that exact number. Place the catch-all branch last, since branches are tried in order.

A branch is selected by the shape of its patterns alone — a number literal, a string literal, a sequence-value pattern of a given arity, a repeated binder (an equality constraint), or a catch-all variable — tried top to bottom. Arity never distinguishes branches: all clauses of one family share one top-level arity (the same number of top-level patterns) and one top-level output arity (the same number of written output slots). The front end rejects a family whose clauses disagree before anything runs, even though `F(0)` below would have matched the first clause:

<!-- spec:conditional-clauses-share-top-level-arity -->
```
F(0) = 1
F(x, y) = 2

F(0)
```

The diagnostic names the clause that disagrees: every clause of `F` must take the same number of top-level patterns, and the second clause takes two. `F(0) = 1` beside `F(x) = 1, 2` is rejected the same way, for output arity; when one branch's result is a pair, write it as the one captured slot `(1, 2)`.

Repeating a binder name within one pattern adds an equality constraint. The first occurrence binds the value; later occurrences must be structurally equal and do not overwrite it:

```
Equal(x, x) = 1
Equal(x, y) = 0

Equal(1, 1)  # 1
Equal(1, 2)  # 0
```

This also works inside sequence-value parameter patterns such as `SamePair((x, x))`. Repeated names involving a collecting binding, such as `F(*xs, xs)`, are not supported.

In a single-clause callable an unequal repeated value is an error. It is checked only after every pattern of the parameter list has bound, so when another pattern also fails, that failure is the one reported: with `P(x, x, (a, b)) = a`, `P(1, 2, 7)` reports that `(a, b)` received one value, not that the two `x` values differ. (Around a collecting parameter, the patterns before it are bound and checked first.) The check compares every occurrence with every other, so argument order never changes whether a call binds. A bare callable such as `Inc` (with `Inc(y) = y + 1`) has no value to compare, so a repeated name cannot receive it together with another argument that is also usable as a callable — another bare callable, or a property such as `A = 5` — while a plain value beside it is fine (`P(f, f) = f` binds `P(5, Inc)` to 5).

When two occurrences also carry callables, equal values are not enough: they must identify the same callable, including the same captured lexical activation. With `A(*xs) = 5` and `B(*xs) = 5 + xs.count`, both have the value 5, but `A(1)` is 5 and `B(1)` is 6. Thus `P(f, f) = f(1)` rejects both `P(A, B)` and `P(B, A)`. Repeated references to `B` remain compatible: `P(B, B)` is 6. The rule applies to two occurrences as well as three or more, and successful permutations preserve the complete binding: channel availability, values, counts, and callable identity. Genuine aliases remain compatible: `Both(left, right) = P(left, right)` called through `Share(original) = Both(original, original)` passes the same callable in both occurrences when `Share(B)` runs. Ordinary eager argument-binding effects still occur before these bindings are compared.


### Nested Sequence-Value Patterns

Parentheses inside a pattern denote a **sequence-value pattern** with a specific arity. This lets you match nested structure:

```
Else(1, (a, b)) = a
Else(c, (a, b)) = b

Else(1, (20, 30))
Else(0, (20, 30))
```

**Results:**
```
20
30
```

In a clause family a sequence-value pattern matches **sequence values only**: an exact [list](#lists) argument does not match `(a, b)` even when its element count fits, so it falls through to a later clause — or fails with no matching branch when none accepts it. A singleton pattern `(x)` is the one exception: it matches any single argument whole (a number, a string, or an entire list) and never opens it. An ordinary single-clause definition is wider — its sequence-value pattern also opens a lone list (see [Collecting Explicit Parameters](#collecting-explicit-parameters)):

<!-- spec:conditional-sequence-pattern-matches-sequence-values-only -->
```
F((x, y)) = x + y
F(z) = 0

F((2, 3))
F([2, 3])
```

**Results:**
```
5
0
```

A bare variable without parentheses matches anything, including a sequence value:

```
Loose(a, b) = a

# b binds to the entire sequence value (2, 3):
Loose(1, (2, 3))
```

**Result:** `1`

But a parenthesized single variable `(b)` is a 1-element sequence-value pattern — it only matches a single value, not a multi-element sequence value:

```
# (b) does not match (2, 3) because arities differ:
Strict(a, (b)) = a
Strict(1, (2, 3))
```

This fails with an arity mismatch error because `(b)` expects exactly one element.

### The K Combinator: Ignoring a Parameter

A classic problem in functional programming is the **K combinator** — an algorithm that accepts two arguments and returns only the first, discarding the second. In many languages this requires special syntax for unused parameters.

In KatLang, a variable in a pattern binds the argument but does not need to be used in the body. This naturally solves the K combinator:

```
K(a, b) = a

K(1, 2)
K(42, 999)
```

**Results:**
```
1
42
```

The parameter `b` is bound by the pattern but never referenced in the body — it is simply ignored. This is the idiomatic way to accept and discard arguments in KatLang.

Single-branch clauses whose pattern is made only of captures and structural sequence-value patterns elaborate as ordinary algorithms, even at arity 1, so higher-order arguments stay callable just like ordinary parameters. For example:

```
Apply(f) = f(4)
Double(x) = x * 2

Apply(Double)
```

**Result:** `8`

The same rule applies to larger binder lists:

```
Apply(x, f) = f(x)
Increment = y + 1

Apply(9, Increment)
```

**Result:** `10`

A sole recursive parameter pattern may also contain one explicit collecting binder at each pattern level. These are ordinary explicit parameter lists, not conditional matching:

```
PairSum((x, y)) = x + y
CountSequenceValue((*values)) = values.count
Step((*history), previous) = history.count + previous
```

### Mixing Literals and Variables

Branches can combine literal matches with variable bindings to create dispatch tables:

```
Else(true, a, b) = a
Else(false, a, b) = b

Else(5 < 6, 2, 3)
Else(7 < 6, 2, 3)
```

**Results:**
```
2
3
```

The first argument is matched against the Boolean literals `true` or `false` (a comparison produces exactly those values); the remaining arguments are bound to `a` and `b`.

### String Patterns

String literals can be used as branch patterns in conditional algorithms. A string pattern matches only that exact string (case-sensitive). A variable catch-all handles any unmatched value. Algorithms that dispatch on string patterns can be called with string arguments directly and combined with other algorithms:

```
Price('tomatoes')  = 1.20
Price('apples')    = 0.80
Price('cucumbers') = 0.60
Price(item)        = 0

Expense = Price(item) * quantity

Price('apples')
Price('bananas')
Expense('apples', 3)
```

**Results:**
```
0.80
0
2.40
```

### Non-Exhaustive Patterns

If no branch matches the provided arguments, evaluation fails with an error. There is no implicit default — add a catch-all branch if you want to handle all cases:

```
F(1) = 100
F(x) = 0

F(1)
F(999)
```

**Results:**
```
100
0
```

---

## Loading and `open`

### Loading External Algorithms

Algorithms can be loaded from URLs using `load`. The loaded algorithm becomes a property whose members you access with dot syntax.

Loading needs the host's permission: it is off unless the host application supplies a downloader (the `katlang` command-line tool's `--allow-loading`), and a program that uses `load` or `open 'url'` without one is rejected with a diagnostic. A module URL is an absolute `https` address without user information (`user@`), on a host the application allows — by default `katlang.org` and its subdomains; a `#fragment` is ignored. The same rules apply to the loads a loaded module makes, and loaded code runs as part of your program.

Scoping: a module bound with `Name = load('url')` is elaborated and evaluated exactly as if its text were written inline as `Name = { ... }` at that place — its free names resolve through the importing algorithm's owner walk before the prelude (an importer property or parameter with the same name, the import name `Name` included, is what the module's occurrence means; only a name nothing provides becomes an implicit parameter of the module member), and the same URL loaded at two different places elaborates once per place. An `open 'url'` target, by contrast, is elaborated in isolation like an inline `open { ... }` block (its free names see only the prelude), so the two spellings differ for a module that mentions a name it does not define; a module that declares everything it uses means the same thing everywhere.

<!-- spec:skip module loading needs a host-configured network downloader; the URL and its outputs are illustrative -->
```
# Load and bind to property 'Lib':
Lib = load('https://katlang.org/algorithm.kat')

# Access a public property 'X' from the loaded algorithm:
Lib.X + 3

# Use the second output value of the loaded algorithm (index 1):
Lib:1 + 10
```

**Results:**
```
23
16
```

### `open`: Import Properties Directly

The `open` keyword makes all **public** properties of a target algorithm available directly in the current scope, without qualifying them with a prefix.

<!-- spec:skip open 'url' needs a host-configured network downloader; the URL and its output are illustrative -->
```
open 'https://katlang.org/algorithm.kat'

# X is now directly accessible:
X + 3
```

**Result:** `23`

A module-backed open written inside a conditional branch is loaded only when that branch is actually selected: alternatives that are never selected fetch nothing and cannot fail because of their own modules, nested branches follow the same rule, and a module-load error inside a branch is reported when the branch runs. Opens outside conditional branches keep loading up front, and syntax errors anywhere are still reported before anything runs.

You can open a locally defined algorithm the same way:

```
open Lib
Lib = {
    public Pi = 3.14159
    public Double = x * 2
}

Pi
Double(5)
```

**Results:**
```
3.14159
10
```

`open` is a declaration, not an output expression, and each algorithm may have at most one `open` statement. Open multiple sources in that one statement with a comma-separated target list:

```
open LibA, LibB
```

String targets use single quotes and mix freely with names: `open 'https://example.org/lib.kat', LibA`. Comma is the only separator — `open A ; B` and `open A B` are parse errors asking for a comma, never two targets. An open target must provide algorithm identity: a genuinely grouped target such as `open (LibA, LibB)` or `open (LibA*)` is a parse error, because a group of several slots or of a spread captures a value and a captured value never exposes the algorithm inside it — name each algorithm directly, or use a brace block. Redundant parentheses are only grouping, so `open (LibA)` is exactly `open LibA` and `open ({ ... })` opens the block. The first target must begin on the same line as `open`. Comma keeps its normal explicit line-continuation behavior, so a long list may span lines with a trailing or leading comma:

```
open LibA,
LibB

open LibA
, LibB
```

A leading `.` likewise continues a dotted target across the line (`open Lib` followed by `.Sub` opens `Lib.Sub`). A plain newline never continues `open`: `open Math` followed by `Math.Pi` on the next line is an open plus a report row. Neither the collect marker nor a spread expression is valid open-target syntax: `open *A` and `open A*` are rejected — use comma for multiple targets. Valid targets are names, argumentless dot-call paths like `Lib.Sub`, single-quoted string URLs, and inline blocks.

A target must name something that exists. Because `open` is resolved statically, `open Nope` (nothing visible is called `Nope`), `open Lib.Missing` (`Lib` declares no `Missing`), and `open Lib.Helper` (`Helper` is private — open paths select public members) are errors reported before the program runs, even when no name is ever looked up through them. The first name of a target resolves through the enclosing declarations and the prelude, never through another open: with `open Outer, Lib`, a `Lib` that only `Outer` provides is not visible to the open list itself.

`open` also works with builtin namespaces like `Math`, letting you use its functions and constants without the `Math.` prefix:

```
open Math

Sin(Pi / 2)
Sqrt(16)
```

**Results:**
```
1
4
```

`open` must appear before all property definitions and output expressions in the current algorithm. This rule keeps KatLang code uniform and easy to read: first declare opened sources, then define properties, then produce output.

**Isolation:** an inline open target (`open { ... }`) and a string target (`open 'url'`) do not inherit the opener's scope: such a library sees only the properties it defined itself and the prelude. A NAMED target (`open Lib` with `Lib = { ... }` or `Lib = load('url')`) is an ordinary property of the scope that declares it, so its free names resolve exactly as that property's would (see [Loading External Algorithms](#loading-external-algorithms)).

**Imported names stay owned by their library:** `open` makes a library's public properties visible; it does not make them properties of the opener. Opening a library therefore never changes what the opening algorithm owns (see [Functions: Algorithms Without Properties](#functions-algorithms-without-properties)).

**Ambiguity:** if two targets of the same `open` declaration both provide a public property with the same name, a bare reference to that name is an error and neither target is selected. An `open` in a nested algorithm is consulted before one in an enclosing algorithm, so only targets opened at the same level can collide. Define a local property with that name to shadow the ambiguity.

**Ownership:** `open` is resolved statically, and the target name follows the ordinary lexical ownership rules. If the nearest binding of the target's first name is a parameter — of the algorithm containing the `open`, or of an enclosing one — that parameter owns the name, and a parameter cannot be opened. KatLang reports an error instead of searching farther outward for another declaration with the same name, so a farther library that happens to be called `Lib` never takes over silently:

```
Lib = {
    public X = 7
}

F(Lib) = {
    open Lib
    # error: cannot open 'Lib' — it refers to the parameter 'Lib', which cannot be used as an open target
    X
}
```

Use the parameter directly instead (`F(Lib) = Lib.X`), or open a declared algorithm from a body that does not bind its name: without the parameter, `open Lib` inside `F = { ... }` opens the declared `Lib` exactly as before.

### Visibility

By default, properties are **private**: `open` provides only `public` members. Structural dot access ignores `public`, so `Lib.Helper` may reach a private member. Visibility is separate from capture accessibility. A property whose value depends on an enclosing algorithm's parameter is **local-only**; it is usable when the reading body has that exact ancestor activation in its lexical chain. A `public` local-only member is therefore available through `open` inside the required activation. A same-named parameter of another owner, or a different call of the same owner, cannot supply that requirement. Transitive captures retain their original owners even across shadowing. Conditional branch binders follow the same rule. A family exposes no branch declarations structurally, but a self-contained provider declared or opened inside a branch works in that branch and its nested bodies.

<!-- spec:visibility-private-member-is-structural-not-exported -->
```
Lib = {
    public Area = 4
    Helper = Area / 2
}

Lib.Area
Lib.Helper
```

**Results:**
```
4
2
```

`open Lib` provides `Area` alone: after it, a bare `Helper` is still unresolved (it would become an implicit parameter of the root), while `Lib.Helper` keeps working. A `public` member that reads an enclosing parameter is local-only — with `Lib(r) = { public Area = r * r ... }`, a root-level `Lib.Area` is refused, because the root is not inside `Lib` — and `open Lib` itself is rejected before the program runs: `Lib` requires an argument, and `open` never creates the activation its members would read. An `open` target must be an algorithm that needs no call (no explicit or inferred parameters, not a clause family); intermediate owners in a dotted target are navigated statically, without calling them. Thus `Lib.Sub.X` and `open Lib.Sub` can traverse explicit or inferred parameter lists on `Lib` or deeper intermediate owners. Each selected member must satisfy capture accessibility; dotted `open` steps must also be public. Only the final provider `Sub` must have zero effective call parameters. A bare `open Lib` never evaluates Lib's output: an unused captured output does not make a consumer of Lib's constant members local-only.

Inside the owner of the captured parameter the same local-only member is fully usable, through both channels:

<!-- spec:open-local-only-member-inside-owner -->
```
Outer(n) = {
    open Inner
    Inner = {
        public X = n
    }
    X + 0
}
Outer(5)
```

**Result:**
```
5
```

`Inner` is a zero-parameter provider whose `X` reads the active `Outer.n`; Outer's own body — and any sibling or nested scope under the same activation — lies inside `Outer`, so `open Inner` provides `X` there and `Inner.X` reaches it. From outside `Outer` the member is refused:

<!-- spec:dot-local-only-member-outside-owner -->
```
Outer(n) = {
    Inner = {
        public X = n
    }
    Inner.X
}
Outer.Inner.X
```

**Result:** error — `X` is local-only because it depends on the parameter `n` owned by `Outer`, and the root row is not inside `Outer`'s body; the member is still selected, and the report names it and the parameter it needs.

The rule is lexical ownership, never a dynamic lookup: a callee written outside `Outer` that happens to run while an `Outer` call is active, or that has its own parameter named `n`, still cannot read `Inner.X`.

```
# In a library algorithm:
public Area = r * r * Math.Pi
public Kind(0) = 'zero'
public Kind(x) = 'nonzero'   # visibility is family-level: every clause is public or none
Helper = Area / 2   # private: never provided by open, still reachable by dot access
```

`open` selects public members before checking capture accessibility. Two providers of the same public name are ambiguous even if one member would be inaccessible at that site; a private member does not create that collision.

---

## Pitfalls

- **Numeric precision:** KatLang numbers are IEEE 754 Decimal128 — 34 significant decimal digits with a huge exponent range (about ±6144). Results needing more than 34 significant digits round to the nearest representable value, and arithmetic past the representable range saturates to `Infinity`/`-Infinity` rather than erroring.
- **No hidden rounding of math functions:** trig, logarithm, root, and power results carry full Decimal128 precision and are never snapped toward "nice" values. `Math.Pi` is π rounded to 34 digits, so `Math.Sin(Math.Pi)` is the tiny residual of that rounding (about `-1.158e-34`), not `0` — compare against a tolerance when testing near-zero trig identities. Irrational results such as `Math.Sin(1)` are approximations at 34 digits, correct to roughly the last digit or two. `Math.Acos`/`acos` and `Math.Asin`/`asin` are sensitive to input error near ±1. For `0.9999 < |x| <= 1`, KatLang uses a decimal endpoint reformulation to avoid the tested runtime's accuracy loss (`acos(1 - 1e-30)` previously retained about 9 digits). The logarithm family gets the same treatment near 1: for `0.5 <= x <= 1.5`, `Math.Ln`, `Math.Lg`, and `Math.Log` compute through the runtime's `log(1 + ε)` primitive on the exact difference `x - 1` (the plain logarithm lost roughly one digit per decade of closeness to 1 — `Math.Ln(1 + 1e-33)` kept five correct digits), and a fractional or beyond-`long` exponent — or a negative integer exponent whose positive power overflows — on a base whose magnitude is within `0.99 <= |b| <= 1.01` computes `exp(exponent · ln |base|)` with the exponent product carried at 80 fixed-point places instead of the runtime power, which inherited the loss (`(1 + 1e-33) ^ 9223372036854775808` came out smaller than the same base to the power `9223372036854775807`), and a negative base there keeps the integer exponent's sign parity, so `(-b) ^ n` is exactly `(-1) ^ n · b ^ n`; the product is never rounded to Decimal128 before exponentiation, because a power loses about one digit per decade of `|exponent · ln(base)|` when it is (`0.99 ^ 12345.5` computed through a 34-digit product was 123 last-place units off). The logarithm reformulation is an accurate composition of runtime primitives, verified against an independent series oracle, not a correct-rounding guarantee; the near-1 power uses 80-place fixed-point approximations with truncation error propagated through the exponent, checked against an independent binomial-series oracle and separately derived power constants; it has no interval-certified correct-rounding guarantee. A deterministic sweep of 23,080 distinct signed inputs, including every representable gap `n * 1e-34` for `n = 1..999`, observed maximum errors of about 1.526 result ulp for `acos` near +1, 0.504 near −1, and 0.503 for `asin` on either side. These are sample measurements, not universal error bounds or a correct-rounding guarantee; some previously correctly rounded in-band results change by one last-place digit. `acos(-1) == Math.Pi` and `asin(±1)` retains the existing Decimal128 ±π/2 value: both identities involve rounded constants. For finite nonzero bases and integer exponents with magnitude at most 9223372036854775807, successful certified powers (`0.9999999 ^ 10000000`, `2 ^ 113`, `1.1 ^ -34`) round the exact mathematical power once to Decimal128, ties to even. If refinement cannot certify the result within 4096 working digits, evaluation reports a structured error. Fractional and larger finite exponents, and negative integer exponents whose positive power overflows, use the near-one fixed-point approximation when the base's magnitude is within [0.99, 1.01]. Outside that band, and for non-finite exponents, the existing Decimal128.Pow delegation is retained; those approximations are outside the certification guarantee. Exact results retain compatible existing display quanta, including the trailing zeros of `5 ^ -50`.
- **IEEE special values:** `NaN`, `Infinity`, `-Infinity`, and `-0` are ordinary numeric values (from domain violations like `Math.Sqrt(-1)`, overflow, writing `-0`, or an integer operation whose zero result takes IEEE's sign rules — `-4 mod 2`, `-7 div 8`, and `0 * -1` are all `-0`, which displays and converts to `'-0'` while comparing equal to `0`). Ordering comparisons involving `NaN` are always false, while `==`/`!=` use structural value identity (so `NaN == NaN` is `true`). Dividing by any zero-valued divisor (including `-0` and computed zeros) is still an error, not `Infinity`, and so is raising a zero-valued base to any negative exponent (`0 ^ -1` and `0 ^ -0.5` alike). With `DisplayDecimals` set, the special values keep these same spellings (`NaN`, `Infinity`, `-Infinity`), while a finite signed zero follows the fixed-point rule like any other finite value (`-0` stays `-0`; `-0.0` shows as `-0.00` at two decimals).
- **Parameter order surprises:** parameter order is determined by first appearance reading left to right. If your expression reads `b - a`, the first parameter is `b`, not `a`. Use Grace (`~`) to override when needed.
- **`if` arity:** builtin `if` requires three arguments after spread expansion: `if(cond, a, b)`. There is no two-argument form. A grouped value is one argument, so `if(X)` is invalid when `X = true, 2, 3`; spread it with `if(X*)` to supply the three slots. The check happens when the call runs, against the callable that [name resolution](#name-resolution) selected — declaring your own `if` shadows the builtin, and a wrong-arity call then reports *your* signature.
- **Misspelled members on known receivers:** dot syntax is receiver injection — `a.F(x)` is `F(a, x)` when `a` has no structural `F` — and a statically known receiver such as `Math`, a block, or a module gets no special treatment. So `Math.Ceiling(2.1)` is not a "missing member" error: the edge falls back to a lexical `Ceiling`, and since none is visible, `Ceiling` becomes an implicit parameter of the program. The report names the receiver, explains the fallback, and suggests `Math.Ceil`; if a lexical `Ceiling(a, b)` IS visible, the call is the valid fallback `Ceiling(Math, 2.1)` and simply runs (see [Misspelled Members on Known Receivers](#misspelled-members-on-known-receivers)).
- **`()` vs `{}` confusion:** `(expr)` groups an expression in the current scope. `{expr}` creates a new algorithm with its own parameters. Passing `(a + 1)` as an argument doesn't create a callable — it evaluates `a + 1` immediately in the enclosing scope. Bare `()` is the empty sequence value (a real value); bare `{}` is a no-output body and is not a value. Declarations follow the same split: `open` and property definitions belong to `{ ... }` blocks (or the root) and are parse errors inside `( ... )`.
- **Ignoring a parameter:** there is no special "ignore" syntax for implicit parameters — every name that resolves to nothing becomes a required argument. If you want to accept and discard an argument, use an explicit parameter pattern. Bind the unwanted argument to a variable in the pattern, then simply don't reference it in the body:

  ```
  # Wrong — no way to declare 'b' to discard; calling with two args fails:
  KeepFirst = a
  KeepFirst(42, 999)  # error: too many arguments

  # Right — 'b' is bound by the explicit parameter pattern but never used:
  KeepFirst(a, b) = a
  KeepFirst(42, 999) # Result: 42
  ```
- **Property redefinition:** defining the same property name twice in one scope is an error — KatLang values and bindings are immutable, so a property is bound once and never reassigned (a same-named property in a nested `{ ... }` scope is a separate, shadowing binding — see [Name Resolution](#name-resolution)):

  ```
  A = 5
  A = 6  # error: Property 'A' is already defined
  ```

- **Duplicate branch patterns:** two conditional branches with match-equivalent patterns are rejected because the second branch would be unreachable under first-match semantics. Binder spelling does not matter, but repeated-name equality relationships do:

  ```
  F(x) = x + 1
  F(y) = y + 2  # error: duplicate branch pattern
  ```

  `F(x, x)` and `F(a, a)` are also equivalent, while `F(x, x)` and `F(a, b)` are distinct because only the first pattern requires equal arguments.

  Use different literal values, string patterns, sequence-value structure, or repeated-name constraints to distinguish branches — never different arities: every clause of one family must have the same top-level pattern arity (see [Basic Pattern Matching](#basic-pattern-matching)):

  ```
  F(0) = 1
  F(x) = x + 1  # OK — 0 and a variable are not equivalent
  ```

- **Recursion depth:** evaluation bounds how many algorithm calls may be active at once, so a runaway recursion reports an error instead of taking the host process down with it. A missing base case, a mutual cycle (`f` calls `g` calls `f`), and a self-referential property (`A = A`) all stop the same way:

  ```
  f(0) = 0
  f(n) = f(n - 1)

  f(1000)  # error: Evaluation recursion limit of 128 was exceeded
  ```

  This is a host runtime limit, not a language rule: a program that finishes within the limit produces exactly the result it always did. Recursion deeper than the limit needs an iterative form — `repeat` or `while` — which repeats work without stacking up calls. The limit is the deterministic ceiling; on a host with a small thread stack (or a debug build of KatLang) the stack-headroom backstop can stop the most stack-expensive shapes — recursion through `if` or through a collection callback — EARLIER, with the structured `EvaluationStackExhausted` error rather than the recursion-limit error, never by terminating the process.

- **Loops still run as long as you ask:** there is no work budget by default, so `Step.while(...)` with a condition that never becomes false runs forever. Check your continuation slot. (Hosts embedding KatLang can configure a step budget to bound this.)

- **Collection size:** one sequence or list can hold up to 100,000 items. A request for more is rejected before anything is allocated, so an accidental extra zero costs you an error message rather than the whole process:

  ```
  range(1, 10000000)  # error: Collection size limit of 100000 items was exceeded; requested 10000000 items
  ```

  This counts the items of a single collection, so nesting is fine for evaluation — `[[1, 2], [3, 4]]` is three small collections, not one big one. One more bound applies to the PROGRAM OUTPUT as a whole on the engine entry points (`KatLangEngine.Run`/`RunAsync`, and therefore the CLI): a successful run is also projected into the flat list of numeric atoms hosts read through `RunResult.Success.Atoms`, and that projection opens every nested sequence and list, so an output whose atoms exceed 100,000 IN TOTAL (`A = range(1, 60000)` then `[A, A]`) is refused with the same collection-size error even though each collection is within the limit; the direct evaluator entry points (`Evaluator.Run`) do not project and accept it. Like the recursion limit these are host runtime limits, not language rules: results within the limits are exactly what they always were.

- **Displayed output size:** printing a value flattens it, and nesting a value inside itself doubles the printed text each time even though the value itself barely grows:

  ```
  Values = range(1, 200)
  L0 = [Values, Values]
  L1 = [L0, L0]
  # ... a few more lines and the printed form is megabytes

  ```

  Displayed output is capped at 1,000,000 characters. Past that, printing reports the limit instead of the text — never a silent half-answer. The value itself is unaffected: it evaluated fine, and a host embedding KatLang can still work with it structurally (subject to the whole-output atom projection bound described under "Collection size": the doubling example above reaches that bound before the display limit, because its leaves are numbers).
---

## Full Reference

### Operators

| Operator | Description | Precedence |
|---|---|---|
| `^` | Power (right-associative; binds tighter than prefix `-` on the left, so `-2 ^ 2` is `-(2 ^ 2)` and a negative base needs parentheses: `(-2) ^ 2`. The exponent side accepts prefix `-` directly: `2 ^ -2`) | Highest |
| `-` | Arithmetic negation (prefix; between `^` and the multiplicative operators) | |
| `*`, `/`, `div`, `mod` | Multiplication, division, integer division, modulo | |
| `+`, `-` | Addition, subtraction | |
| `<`, `>`, `<=`, `>=`, `==`, `!=` | The comparisons: ONE precedence level that chains — `a < b <= c == d` compares each adjacent pair and is `true` only when every pair holds (operands evaluated once each, left to right; a `false` pair never stops the chain, an error does; parentheses end a chain). Ordering takes numeric scalar operands only; `==`/`!=` are structural value equality / inequality across all value kinds (numbers, Booleans, strings, sequence values, and lists — different kinds compare unequal). Returns `true` or `false` | |
| `not` | Logical negation (prefix; binds less tightly than the comparisons and more tightly than `and`, so `not x > 3` is `not (x > 3)` and `not a and b` is `(not a) and b`; it cannot begin the operand of a tighter operator — write `a == (not b)`, not `a == not b`) | |
| `and` | Logical and | |
| `xor` | Logical exclusive or | |
| `or` | Logical or | Lowest |
| `:` | Output selection (zero-based index over a sequence or list target; the selected element is one value, never opened — a value boundary like `first`/`last`) | Postfix |
| `.` | Dot-call / property access | Postfix |
| `*` (prefix, directly attached) | Collect marker (binding positions only: `*name` collects the matched segment as one exact list) | — |
| `*` (postfix, directly attached) | Spread marker (`value*` contributes the operand's items to the surrounding supply; a `*` followed by a valid right operand, on the same line or the next, is multiplication instead — spacing never decides that, but a spread marker must be attached: `value *` with no operand is an error) | — |
| `~` (prefix, directly attached) | Grace: one unit of weight moving the inferred parameter one position earlier (`~x`; `~~x` two, weights on one name add up, `~ x` is an error) | — |
| `~` (postfix, directly attached) | Grace: one unit of weight moving the inferred parameter one position later (`x~`; `x~~` two, `~x~` cancels, `x ~` is an error) | — |
| `[` `]` | List literal (`[1, 2, 3]`; never a call or indexing delimiter — `A[1]` is a missing-separator parse error, `A, [1]` is two slots, and `A:1` indexes) | — |

### Builtin Algorithms, Intrinsics, and Keywords

The collection builtins below receive ONE collection argument plus fixed control arguments. The bound collection is viewed one level deep: a lone sequence value or list value opens into its immediate items, so `count(Values)`, `count((1, 2, 3))`, and `count([1, 2, 3])` all count three items; an atom or string is a one-element collection (`count(7)` is `1`); and nested sequence or list elements stay opaque items. Multi-item inline forms are arity errors (`count(1, 2, 3)` fails — `count(collection)` expects one argument), and spread supplies ordinary call arguments rather than feeding the collection parameter (`count(Values*)` fails; re-group as `count((Values*, 8))` or `sum((A*, B*))` when combining items into one collection). The collection-producing builtins (`range`, `filter`, `map`, `order`, `orderDesc`, `distinct`, `take`, `skip`, `atoms`) materialize their results as one list value (`[]` for zero items, `[item]` for one). Dot-call supplies the receiver as the collection argument, for example `collection.take(2)`. Selection is a value boundary — `A:0` is the selected value, whole — so `(A:0).count` follows the ordinary collection rules for that one bound value without any extra builtin-specific expansion. Higher-order builtins such as `filter`, `map`, and `reduce` do not recursively flatten sequence-value elements beyond that.

For `repeat` and `while`, each explicit init argument becomes one initial state slot. `Step.repeat(3, a, b)` starts with two slots, while `Step.repeat(3, Pair)` starts with one slot even if `Pair` evaluates to multiple values. Use selections such as `Pair:0, Pair:1` or spread such as `Pair*` when you want a multi-output value to provide multiple initial slots; capture the step result as a sequence value when one structured slot should be preserved across iterations. A spread followed by a comma keeps its neighbor a separate slot, so `Step = history*, next` emits history's items followed by `next` as multiple next-state slots, while `Step = (history*, next)` captures them into one next-state slot. (The comma is required — `history* next` would be the multiplication `history * next`.)

A collecting step parameter follows the same collection rule as every other collecting binding: the fixed parameters bind state slots from the front and back, and the collecting parameter collects the matched middle slots as one exact list — including ZERO slots, so `Step(acc, *extras)` runs fine on a single-slot state with `extras = []`. Only the fixed parameters set the state-slot minimum. One receiver-specific exception applies to steps that use sequence-value parameter patterns (for example `Step((*history), previous)`): in such a patterned step's OUTPUT, a top-level spread expression contributes its combined value as ONE next-state slot instead of re-spreading into separate slots — the pattern-shaped step preserves structured state boundaries in both directions. Flat steps re-spread top-level output spread into separate state slots as described above.

| Keyword | Usage |
|---|---|
| `if` | `if(cond, a, b)` |
| `while` | `step.while(init1, init2, …)` or `while(step, init1, init2, …)` |
| `repeat` | `step.repeat(n, init1, init2, …)` or `repeat(step, n, init1, init2, …)` |
| `range` | `range(start, stop)` — inclusive integers ascending or descending, materialized as one list value |
| `filter` | `filter(collection, predicate)` or `collection.filter(predicate)` — keep top-level elements whose predicate result is `true`; the predicate must return a Boolean value, the callback item is one selected value (as `S:i` returns it), and the kept elements are returned unchanged as one list value (`[]` when nothing is kept) |
| `map` | `map(collection, mapper)` or `collection.map(mapper)` — transform top-level elements left to right; the callback item is one selected value (as `S:i` returns it), the mapper must return exactly one mapped element, and the mapped elements are returned as one list value |
| `order` | `order(collection)` or `collection.order` — eagerly sort top-level numeric elements ascending into one list value; duplicates are preserved and sequence-valued/string/list elements are invalid |
| `orderDesc` | `orderDesc(collection)` or `collection.orderDesc` — eagerly sort top-level numeric elements descending into one list value; duplicates are preserved and sequence-valued/string/list elements are invalid |
| `count` | `count(collection)` or `collection.count` — denotational top-level value count after evaluation, without flattening sequence values or lists |
| `contains` | `contains(collection, item)` or `collection.contains(item)` — return `true` when any extracted top-level element equals `item` under ordinary KatLang value semantics, otherwise `false`; sequence values stay intact and search is top-level only |
| `first` | `first(collection)` or `collection.first` — select the first top-level element (the same selection as `collection:0`): one value, never opened, and the collection must be non-empty |
| `last` | `last(collection)` or `collection.last` — select the last top-level element (the same selection as `collection:(collection.count - 1)`): one value, never opened, and the collection must be non-empty |
| `distinct` | `distinct(collection)` or `collection.distinct` — remove later duplicate top-level elements while preserving first-occurrence order; sequence values stay intact, duplicate detection follows KatLang value semantics, and the kept elements are returned as one list value (a single survivor is the one-element list `[item]`) |
| `take` | `take(collection, count)` or `collection.take(count)` — keep the first `count` top-level elements unchanged as one list value; non-positive counts return the empty list `[]`, sequence values stay intact as elements, and a single kept element is the one-element list `[item]` |
| `skip` | `skip(collection, count)` or `collection.skip(count)` — drop the first `count` top-level elements and return the rest as one list value; non-positive counts return all original items, sequence values stay intact as elements, and a single remaining element is the one-element list `[item]` |
| `min` | `min(collection)` or `collection.min` — find the smallest top-level numeric element; the sequence must be non-empty and sequence values are not flattened |
| `max` | `max(collection)` or `collection.max` — find the largest top-level numeric element; the sequence must be non-empty and sequence values are not flattened |
| `sum` | `sum(collection)` or `collection.sum` — add top-level numeric elements; each element must be a single atomic numeric value and sequence values are not flattened |
| `avg` | `avg(collection)` or `collection.avg` — average top-level numeric elements and return the decimal arithmetic mean (for finite elements, the exact total divided by the count, rounded once); the sequence must be non-empty, each element must be a single atomic numeric value, and sequence values are not flattened |
| `reduce` | `reduce(collection, reducer, initial)` or `collection.reduce(reducer, initial)` — fold left over top-level elements; the current item is one selected value (as `S:i` returns it), the accumulator is ONE ordinary argument (a normal parameter binds it whole, a collecting parameter collects `[accumulator]`, and a structural pattern such as `(*history)` opens it), and the reducer must return exactly one accumulator value |
| `atoms` | `atoms(value)` or `value.atoms` — recursively collect numeric atoms through both sequence and exact-list boundaries (left to right; strings contribute none) and return them as one list |
| `string` | `value.string` — value intrinsic that converts an atomic numeric result to a first-class string value; non-numeric receivers (strings, sequence values) are errors |
| `load` | `Name = load('url')` — load external algorithm |
| `open` | `open target` — import public properties into scope |
| `public` | `public Prop = ...` or `public Prop(pattern) = ...` — make a property visible to `open` (a member that captures an enclosing parameter is still checked for capture accessibility where it is read; structural dot access ignores `public`) |
| `Math` | Built-in namespace for constants and functions |
