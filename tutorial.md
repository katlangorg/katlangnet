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
   - [Lowercase Math Aliases](#lowercase-math-aliases)
   - [Display Decimal Places](#display-decimal-places)
5. [Multiple Outputs](#multiple-outputs)
6. [Properties](#properties)
   - [Calls Return One Value](#calls-return-one-value)
   - [Zero-Parameter Property Caching](#zero-parameter-property-caching)
   - [Algorithm Output](#algorithm-output)
   - [The Empty Sequence Value](#the-empty-sequence-value)
   - [Sequence Values and Count](#sequence-values-and-count)
   - [Output Selection](#output-selection)
   - [Dot-Call Syntax](#dot-call-syntax)
   - [Dot Members and Implicit Parameters](#dot-members-and-implicit-parameters)
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
    - [Multi-Output Example](#multi-output-example)
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

---

## What KatLang Is

KatLang is a language designed for calculations. A program is a root algorithm: it can define named calculations and produce values. You write expressions, give calculations names, and combine them.

All computation is expressed through algorithms, but algorithms and values are not interchangeable. An expression such as `42` produces a number value. A body such as `1, 2, 3` emits three output slots. Parentheses capture output slots into one sequence value, while braces create a nested algorithm and a new lexical scope. Named algorithms are called **properties** because they belong to a parent algorithm.

Most simple formulas do not need declared parameters — KatLang figures them out. Any name you use that isn't defined as a property automatically becomes a parameter unless the algorithm has an explicit parameter list.

The core forms are:

| Form | Meaning |
|---|---|
| `42` | One number value |
| `1, 2, 3` | Three output slots |
| `(1, 2, 3)` | One sequence value containing three items |
| `[1, 2, 3]` | One exact list value containing three items |
| `Total = price * quantity` | A property whose unresolved names become parameters |
| `Total(12, 4)` | An explicit call |
| `{ expression }` | A nested algorithm with its own scope |
| `value*` | Spread one sequence or list boundary into the surrounding slots |

The opening chapters focus on numbers, output slots, sequence values, properties, and calls. Lists, braces, spread, and their exact boundary rules are developed later.

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

Names defined with `=` are called **properties**. In an algorithm without an explicit parameter list, if a name isn't defined, KatLang treats it as a **parameter** — an input the caller must supply:

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

Operator precedence follows standard math rules: `^` binds tightest, then prefix `-` and `not`, then `*`, `/`, `div`, `mod`, then `+` and `-`. Parentheses override precedence.

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

Comparisons produce `1` for true and `0` for false.

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
1
0
1
1
1
1
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
1
0
0
```

The ordering operators (`<`, `>`, `<=`, `>=`) and the arithmetic operators, by contrast, require numeric scalar operands; applying them to a sequence value is an error.

### Logical Operators

KatLang has `and`, `or`, `xor`, and `not` for combining boolean values (where any non-zero value is truthy and `0` is false).

```
1 and 1
1 and 0
0 or 1
0 or 0
1 xor 1
1 xor 0
not 1
not 0
```

**Results:**
```
1
0
1
0
0
1
0
1
```

Because comparisons return `1` or `0`, logical operators compose naturally with them:

```
InRange = x > 5 and x < 10

InRange(7)
InRange(3)
```

**Results:**
```
1
0
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
- A mathematically exact result stays clean: `Math.Lg(1000)` is `3` and `Math.Sqrt(144)` is `12`.

Domain violations follow IEEE 754 rather than raising errors: `Math.Sqrt(-1)` and `Math.Ln(-1)` return `NaN`, and `Math.Ln(0)` returns `-Infinity`. Division and modulo by a zero-valued divisor remain ordinary KatLang errors — the check applies to the evaluated value, so `1 / 0`, `1 / (1 - 1)`, and `1 / -0` all report the same division-by-zero diagnostic.

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

- Your own definitions win. A local property `sin(x) = x * 10`, an explicit parameter `F(sin) = ...`, or an ancestor definition shadows the alias, and your `sin` behaves like any ordinary callable.
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

`DisplayDecimals` is display-only. It does not round stored values, intermediate calculations, comparisons, or cached property results:

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

Per-value formatting such as `value.displayDecimals(n)` and `displayDecimals(value, n)` is intentionally not part of this feature. Structured display settings such as `Display = { Decimals = n }` and `Display.Decimals = n` are also intentionally out of scope.

---

## Multiple Outputs

> **Core idea:** commas, allowed adjacency, and output rows create separate slots. Parentheses capture slots into one sequence value; square brackets capture them into one exact list value.

A KatLang algorithm can produce more than one value. Use commas to list multiple outputs:

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

KatLang puts complete expressions next to each other with expression lists. Comma and allowed expression adjacency create separate slots; parentheses materialize those slots as one sequence value. Semicolon is not expression syntax.

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

The same program can be written `1 + 1, 2 + 2, 3 + 3` or `1 + 1 2 + 2 3 + 3`; all three produce three expression-list slots. Use parentheses when you want one sequence value:

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

This is equivalent to `{ 1, 2, 3 }` and to `{ 1, 2 3 }`: all three items are expression-list slots. Parentheses materialize an expression list as one sequence value, so `(1 2)` is the sequence value `(1, 2)`. Call syntax consumes expression lists as argument slots, so `F(A B)` is the two-argument call `F(A, B)`.

Adjacency is an implicit expression-list separator only between complete independent expressions where adjacency is allowed. It never splits tokens: `ab` stays one identifier, `12` stays one number, and `2(3)` is the expression list `2, 3`, never multiplication.

Postfix continuations win over adjacency on the same physical line. An implicit expression-list separator is inserted only when the next token cannot legally continue the current expression; a token that continues it — such as a call argument delimiter — continues it instead. You may therefore write whitespace between a callable name and its argument list:

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

The same applies to dot calls and callback braces: `A.B (1)` is the dot call `A.B(1)` and `values.map { n * 2 }` is `values.map{n * 2}`, but `A.B` followed by `(1)` on the next line is the expression list `A.B, (1)`, and `values.map` followed by `{ n * 2 }` on the next line is not a callback call (write `values.map{` and break inside the braces instead). This is only about same-line whitespace between the callee and its delimiter — inside the argument list adjacency still creates argument slots, so `Add (1 2)` is the two-argument call `Add(1, 2)`. Comma and a newline both keep separate slots: `F, (1)` and `F` followed by `(1)` are expression-list structure. Non-callable targets never become calls: `2 (3)` stays the expression list `2, 3`.

Postfix indexing follows the same line rule: `Pair:0`, `Pair :0`, and `Pair : 0` all index on the same line, but a `:`-led line never continues the previous expression — it is a parse error rather than a silent continuation, so `P = Pair` followed by a line `:0` does not define `P = Pair:0`. Postfix grace `~` is same-line only in the same way: `A~B` graces `A`, while `A` followed by a line `~B` keeps `A` ungraced and parses `~B` as its own prefix-grace row. Binary operators follow the rule too: an operator-led line never continues the previous expression, so `A` followed by a line `-1` is the expression list `A, -1`, never the subtraction `A - 1` — put the operator at the end of the line (`A -` then `1` on the next line) when you want the arithmetic to continue. For `*` the trailing operator must stay detached: `A *` at the end of a line continues as the multiplication `A * B` onto the next line, while the directly attached `A*` is a completed spread expression, so `A*` followed by `B` is a spread slot and a separate row (see [Spread with the Postfix Star](#spread-with-the-postfix-star)). Comments never change any of these decisions: `A # note` followed by `-1` parses exactly like `A` followed by `-1`. Leading-dot lines are the one intentionally supported continuation: a line starting with `.` continues the dot-call chain, so method-chain layout works as long as each argument delimiter stays on the same line as its member name:

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

Comma is the explicit expression-list separator. Where an expression list is already open, same-line adjacency acts as an implicit comma, so `a b` means `a, b`. A newline is a different mechanism — a body, statement, or output boundary, not a global implicit comma — so it does not extend an expression list across lines unless the syntax explicitly keeps the context open (for example an open `(`/`{`, a trailing comma, a same-line binary operator, or a leading `.`). Expression spreading uses the postfix spread marker `value*`; a `*` with a valid same-line right operand is instead the multiplication operator regardless of spacing, so a comma is required between a spread and a following same-line item (`a*, b` — `a* b` is the product `a * b`), while a spread whose star ends the line leaves the next line a separate slot. The prefix `*` in a binding pattern is the collect marker: it must be directly attached to its binding name in a parameter or deconstruction pattern (`*name`; `* name` is an error), and it is not an expression operator.

Because same-line adjacency creates expression-list slots in the current body, an expression that follows a definition on the same line becomes another output slot in that definition's body. Start a new line after a definition body when the next expression should be a separate output contribution.

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
| `1 2` | Implicit expression-list separator by adjacency: exactly `1, 2` |
| `X*` | Spread expression: open one item boundary of the evaluated value and contribute the items to the surrounding slot context |
| `X*, 2` | Spread then a separate expression-list slot — the comma is required, because `X* 2` is the multiplication `X * 2` |
| `X * 2` (any spacing) | Multiplication: a `*` with a valid same-line right operand always multiplies — `X*2`, `X* 2`, `X *2`, and `X * 2` are the same product |
| `*name` in a binding pattern | Collecting binding: collect the matched supply into one exact list |

Comma and adjacency create expression lists. Root output consumes a bare expression list as output slots, call syntax consumes it as argument slots, parentheses materialize it as one sequence value, and square brackets materialize it as one exact [list value](#lists). Semicolon is not an expression separator; use comma/adjacency for separate slots or parentheses for one sequence value. A spread expression is one whole slot: `A B*, C` is the expression list `A, B*, C` — adjacency separates `A` from `B*`, and the comma after the spread is required because `B* C` would be the multiplication `B * C`. Comma and adjacency slots stay structural (`F(a*, b)` is a two-argument call). Physical line breaks do not create sequence-value boundaries. Explicit parentheses do:

```
1, (2, 3)    # two slots: 1 and (2, 3)
(1, 2), 3    # two slots: (1, 2) and 3
(1, 2, 3)    # one sequence value
(1, 2, 3)    # (1, 2, 3)
```

Comma creates multiple top-level output slots; parentheses create one sequence-valued slot. The result window may show comma slots on separate rows, while sequence values display as sequence values. `EvaluateToString()` is a separate convenience stringification path that extracts atoms and joins them with spaces. See [Spread with the Postfix Star](#spread-with-the-postfix-star).

A spread expression `x*` is the spread of `x` followed by nothing: the star must be directly attached to its operand, and it is the spread marker only when nothing usable follows it on the same line. When a valid right operand does follow, the star is multiplication regardless of spacing — `x*y`, `x* y`, `x *y`, and `x * y` are all the product `x * y`. To spread and then supply another same-line item, the comma is required: `x*, y`. At a line ending the attachment decides: `x*` closes the line as a spread and the next line starts a new expression-list slot, while a detached trailing `x *` continues as multiplication onto the next line. Use parentheses, such as `(x*, y)`, when the spread value and the following expression should form one sequence value.

Flat fixed calls preserve expression boundaries. A property reference used as one argument is one argument expression, even if that property evaluates to multiple outputs. KatLang does not implicitly unpack one argument expression to satisfy additional fixed parameters; use separate arguments, explicit indexing/projection, or an explicit spread (`value*`) where that is the intended shape.

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

---

## Properties

> **Core idea:** a property definition gives an algorithm a name but does not itself produce output. Expression rows produce output; reading or calling a property crosses a one-value boundary.

An algorithm can be given a name using `=`. Named algorithms are called **properties**, because a named algorithm always belongs to its parent algorithm. By convention, property names use PascalCase.

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

### Calls Return One Value

A property/call boundary is a **value boundary**: it always returns exactly one value. A body may internally produce an item supply — comma slots, adjacency, or a body spread — but when you *call* it (or access a property, or invoke a builtin), the caller receives a single value. If the body produced several items, that value is a sequence containing them. To contribute its items back into the surrounding item supply, append the spread marker at the call site: `value*`. This is analogous to Python, where `return 1, 2, 3` returns one tuple, not three independent results.

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

The same rule governs collection-producing builtins, with one refinement: `order`, `orderDesc`, `distinct`, `take`, `skip`, `filter`, `map`, `range`, and `atoms` each materialize their result as one exact immutable [list value](#lists); an explicit spread opens it.

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

Three things are intentionally **not** value boundaries and keep emitting multiple top-level items: root program output (`1, 2, 3` still shows three rows), explicit caller-site spread (`value*`), and the multi-slot loop state of `while`/`repeat`. Scalar/reduction builtins (`count`, `sum`, `avg`, `min`, `max`, `contains`, `first`, `last`, `reduce`) already return one value and are unchanged. A `map`/`reduce` callback must still return exactly one element; a multi-output callback body is an error, not a silently-grouped value.

### Zero-Parameter Property Caching

For pure calculations these forms produce the same visible value, but the call shape controls reuse. A zero-parameter property read without parentheses may reuse a cached result during the current evaluation:

```
Fun = 1 + 2
Fun, Fun
```

When the property produces values that can change, property-style access and explicit calls are different:

```
Fun = Math.Random(0, 1), Math.Random(0, 1)

Fun, Fun     # property-style access: the same pair may be reused
Fun(), Fun() # explicit calls: the body is evaluated again for each call
```

`Fun()` bypasses the zero-argument cache for `Fun` itself. It does not recursively force property-style references inside `Fun` to bypass their own caches. To request fresh nested values, write those nested calls explicitly with `()`:

```
A = Math.RandomInt(0, 10)

B = A, A        # uses cached/property-style A access
C = A(), A()    # explicitly asks for fresh A values

B()             # re-evaluates B, but A remains cached inside B
C()             # re-evaluates C, and A() is fresh because it is explicit
```

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

This produces `7`. Conditional branches follow the same rule: declare them on the enclosing algorithm head. To get an algorithm's result, call the algorithm directly. Bare `Algo` still refers to the algorithm value, not an automatic call. Self-contained helper properties remain accessible through dot syntax, for example `Algo.Helper(6)`. If a nested property depends on parameters owned by the enclosing algorithm — including the pattern binders of a conditional branch — it is local-only and cannot be accessed as `Algo.Helper` or exported through `open`/`load`. Properties defined inside a conditional branch are never reachable by name from outside that branch (`Algo.Helper` and `open Algo.Helper` are refused, and sibling branches never see them), but inside the branch they are ordinary properties: a self-contained branch-local library can be opened or dot-accessed by the branch body and by any body nested in it, exactly like an outer library.

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

Parentheses around an empty-sequence literal are redundant grouping. They canonicalize to the same empty sequence value:

```
()       # the empty sequence
(())     # canonicalizes to ()
((()))   # canonicalizes to ()
```

They stay equal after parsing, assignment, display, and equality:

<!-- spec:empty-eq-family -->
```
() == ()      # 1
() == (())    # 1
() != (())    # 0
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

**Result:** `1`

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
Empty*
1
```

**Result:** `1`

A collecting binding that collects zero items binds the empty exact [list](#lists) `[]`, not `()` — it is likewise one visible slot, and spreading it contributes zero items:

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
rest*
x
```

**Result:** `1`

Collection builtins never produce `()` either: a builtin such as `filter` that keeps zero items returns the same empty exact list `[]`, which is a different value from `()`. Test an empty builtin or collecting-binding result against `[]` or with `count`:

```
IsEven = x mod 2 == 0
filter((1, 3, 5), IsEven) == []
filter((1, 3, 5), IsEven) == ()
count(filter((1, 3, 5), IsEven))
```

**Results:**
```
1
0
0
```

### Sequence Values and Count

Use `.count` (or `count(collection)`) to ask how many items a stored value contains. `count` receives one collection argument and views it one level deep: a lone sequence value or exact [list value](#lists) contributes its immediate items, while an atom or string is a one-element collection.

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

Collection builtins receive one collection object. Named helpers such as `A = 1, 2, 3` followed by `count(A)` and `A.count` both return `3` — the one bound collection value is opened one level, so its three items are counted. A sequence-valued helper such as `T = (1, 2, 3)` behaves the same way (`count(T)` and `T.count` return `3`), and a lone exact list value opens the same way too, so `count([1, 2, 3])` is also `3`. Multi-argument forms are not accepted: `count(1, 2, 3)` is an arity error because `count(collection)` expects exactly one argument, and `count(A*)` is an arity error too, because spread supplies ordinary call arguments — three of them here — rather than feeding the collection parameter. When extra items must join a collection, group them into one value: `count((A*, 7))` is `4`. See `count` below for the full collection-input rules.

### Output Selection

When an algorithm produces multiple outputs, the `:` operator selects one top-level item by its zero-based index and projects that selected item's content one level. Exact list values are indexable the same way: `value:index` selects one immediate element from a sequence or list target under identical index rules.

Construction preserves structure; selection projects content.

- If the selected item is atomic, the result is that atomic value.
- If the selected item is a sequence value, the result is its immediate top-level members.
- If the selected item is an exact list value, the result is that list, exactly as stored.
- Nested sequence and list values stay intact; `:` does not recursively flatten them.
- Chained selection repeats the same one-level projection step at each `:`.

```
Nums = 10, 20, 30, 40, 50

# Select the third value (index 2):
Nums:2
```

**Result:** `30`

<!-- spec:index-projects-one-level -->
```
Pairs = (1, 2), (3, 4)
Pairs:0
```

**Results:**
```
1
2
```

The selected pair projects to its two immediate members, which a lone root row shows as two rows. Any other receiver re-materializes them as the one value `(1, 2)` — for example `(Pairs:0).count` is `2` and `G(Pairs:0)` passes one argument.

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

Here each selection sits beside another output row, so each displays as one value row (`Bags:0` is the intact inner pair-of-pairs). Only a lone root row spreads a projection across rows, as in the `Pairs:0` example above.

Exact list values use the same zero-based selection:

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

As an invariant, `A.B(C, D)` means `B(A, C, D)` for ordinary properties, not a call where `A`'s top-level values are spread before `C` and `D`.

A parameter list with two or more parameters that contains a collecting parameter (`*name`) is a **mixed fixed/collecting parameter list**. The fixed parameters bind from the front and the back, and the collecting parameter collects the matched middle argument slots as one exact immutable [list](#lists):

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

Both item-supplying call forms agree: `factor` binds `10` from the back, `*values` collects the three front slots as `values = [1, 2, 3]`, the body's `map` call materializes the mapped items as the one exact list value `[10, 20, 30]`, and the call boundary returns that single value unchanged (see [Calls Return One Value](#calls-return-one-value)). Caller-site spread such as `Scale(Arg*, 10)*` opens the result into the flat items `10`, `20`, `30`.

An UNSPREAD structured argument is one collected slot, not an item supply: `Scale(Arg, 10)` (and the dotted `Arg.Scale(10)`, whose named receiver supplies its one stored value) binds `values = [Arg]` — a one-element list holding the whole sequence — so the numeric `map` callback fails on the sequence element. To supply a stored property's items, spread them (`Scale(Arg*, 10)`); a WRITTEN group receiver supplies its rows directly (`(1, 2, 3).Scale(10)` binds `values = [1, 2, 3]` — see [Dotted Receivers and Collecting Parameters](#dotted-receivers-and-collecting-parameters)). A lone collecting parameter such as `Helper(*values)` is the degenerate lone-collecting-binding case of the same item-supply binding (see [Collecting Explicit Parameters](#collecting-explicit-parameters)).

**Resolution rule:** KatLang first checks whether the property name exists as a structural property of the target algorithm. If found, it calls that property. If not found, it falls back to the same callable resolution a plain call would use, with the receiver as the leading argument.

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

Parameter precedence in the fallback mirrors plain calls: a parameter of the current algorithm wins over a same-name visible property, while a parameter captured from an enclosing algorithm yields to a visible non-builtin declaration of the same name. Structural members of the resolved receiver always win before any of this — a receiver's own property is never bypassed in favor of a parameter.

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

Obj.V
Obj~.V
```

**Results:**
```
42
42
```

`Obj.V`, `Obj~.V`, and `Obj.~V` all read Obj's own property. To call the lexical `V` with Obj's value instead, write the direct call `V(Obj)`.

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

Everything else is ordinary DotCall behavior: `.string` (`v~.string` and `v.~string`), dotted sequence builtins (`S~.count` and `S.~count`), and receiver-segment supply all use the same runtime paths as their ungraced forms. Chaining an ordinary dot afterward is fine — `a~.t.string` has the same executable body as `a.t.string`.

`a ~ .t` is lexically distinct from `a~.t` by source offsets, but whitespace is insignificant between these postfix tokens. The normal grammar therefore gives it the same postfix Grace on `a`, the same ordinary dot, and the same `(t, a)` inferred order. Prefix member Grace must begin directly after the dot (`a.~t`). A grace-marked target is not a valid `open` target: `open M~.C` is rejected because `open` consumes structural algorithm identity and has no parameter inference to reorder.

Exposure analysis is unaffected by Grace because it analyzes the same DotCall. A dot member marks a captured-parameter dependency only when static analysis proves its lexical fallback must be selected; when the receiver may own the member structurally, the possible fallback does not by itself change the property's exposure. That MUST-selection rule is deliberately stricter than signature inference, which includes a fallback whenever it MAY be needed.

### Name Resolution

Name resolution is especially important in KatLang because it may behave differently from what users expect from other languages. KatLang uses a fixed search order called **ownership-first lookup**. The idea is simple: a name belongs first to the algorithm that owns it, then to its parent structure, and only after that to anything brought in through `open`.

When KatLang sees a name, it checks these places in order and stops at the first match:

1. **Local properties** — properties defined in the current algorithm (any visibility).
2. **Parent chain** — properties defined in enclosing algorithms, walking upward through the nesting structure. In this step, KatLang checks only structural properties; parent-level opens are not considered yet.
3. **Opens** — public properties from `open` targets, checked for the current algorithm first and then upward through the parent chain.

If the name is not found at any of these levels, KatLang treats it as an implicit parameter only when the current algorithm has no explicit parameter list (see [Parameters](#parameters)). Explicit parameter lists are closed, so an unresolved extra name is reported as an error instead.

Closedness also covers what a name needs *indirectly*. Referring to a property that has its own implicit parameters normally passes them along for you, and an explicit list can only do that for the parameters it declares. Where a value is definitely required — a math function's argument, for example — KatLang reports the gap instead of leaving it to fail at run time. Declaring the required name keeps the program legal:

```
A = q + 1
F(q) = Math.Abs(A)

F(7)
```

**Result:** `8`

Leaving the list off entirely works too (`F = Math.Abs(A)` infers `q` for you), and so does supplying the argument at the call (`Math.Abs(A(1))`). But writing `F(x) = Math.Abs(A)` is rejected, because `Math.Abs` needs `A`'s value, producing that value needs `A`'s `q`, and `F(x)` declares no `q`: "'A' is required as a value here, but producing that value needs the implicit parameter 'q', which the enclosing explicit parameter list does not declare." Only a *value* demand is checked this way — passing `A` where a callable is wanted, as in `Apply(A)` or `map(abs)`, is unaffected.

```
X = 1
Inner = {
    Y = 2
    # X is found at level 2 (parent chain)
    # Y is found at level 1 (local)
    X + Y
}
Inner
```

**Result:** `3`

In this example, `Y` is found immediately in `Inner`, because it is local. `X` is not local to `Inner`, so KatLang continues to the parent chain and finds `X` in the enclosing algorithm.

Local properties always win. If the same name exists both locally and in a parent, the local one is used:

```
X = 10
Inner = {
    X = 99
    X
}
Inner
```

**Result:** `99`

Here `Inner.X` hides the outer `X`, so the result is `99`.

Opens are checked only after local and parent-owned properties. This means a name introduced with `open` never overrides a name you already defined structurally.

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

This ownership-first model makes name lookup more predictable in larger algorithms. In particular, adding an `open` does not silently change the meaning of names you already defined in the current algorithm or its parents.

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
1
0
1
```

Arithmetic operators (`+`, `-`, `*`, etc.) are not defined for strings.

### Number to String Conversion

Every numeric value exposes a `.string` property that converts it to a first-class string value.

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

The result is a real KatLang string value — identical to a single-quoted string literal, even though string values display as their raw content without quotes. For example, `123.string == '123'` evaluates to `1` (true).

Only numeric values are supported. Applying `.string` to a non-numeric value (such as a string or a multi-output sequence value) produces an error.

---

## Parameters

> **Core idea:** in an algorithm without an explicit parameter list, unresolved names become parameters in first-occurrence order. An explicit parameter list fixes the accepted names and their order.

**Rule:** in an algorithm without an explicit parameter list, any identifier that is not defined as a property in the current algorithm becomes an implicit parameter.

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

The order of implicit parameters is determined by their first appearance in the definition, reading left to right.

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

KatLang supports recursive parameter patterns in ordinary algorithm definitions and conditional branch heads. A sequence-value pattern consumes one parent-level argument slot and matches that slot's immediate contents.

```
PairSum((x, y)) = x + y
PairSum((2, 3))
```

**Result:** `5`

Call arguments are evaluated exactly once, from left to right, before arity checking or
pattern binding. A parenthesized argument sent to a sequence-value pattern has two views—the
combined sequence value and its explicit written items—but both come from that same evaluation.
This matters for nondeterministic expressions such as `Math.Random(...)`, for failures and their
source context, and for host evaluation budgets; parentheses never cause an argument to run again.
Nested parentheses still contribute one grouped written item, and only an explicit postfix spread
contributes the evaluated value's immediate items.

A top-level collecting parameter (`*name`) instead consumes an **item supply**: it COLLECTS the supplied argument slots as one exact immutable [list](#lists). Zero slots collect `[]`, one slot collects `[item]` (never erased to the item), and many slots collect `[item1, item2, ...]`. A callable with a collecting parameter can therefore accept a variable number of argument items — it is variadic in that sense. A lone collecting parameter is the degenerate case — it collects the whole supply:

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

Both forms supply five numeric argument slots, collected as `x = [1, 2, 3, 4, 5]`; `x.sum` opens the bound list and adds its elements. An UNSPREAD structure is one argument slot: `G(A)` and `G((1, 2, 3, 4, 5))` each supply one sequence-valued slot, so `x = [A]` — a one-element list holding the whole sequence — and the numeric `sum` element constraint rejects it. Supplying a value's items is always the explicit spread `A*`; there is no implicit opening at calls. An empty call `G()` collects `x = []`, and `G(*x) = x.count` reports `1` for `G(A)` and `5` for `G(A*)`.

The collect marker and the spread marker have opposite meanings and are never interchangeable — they match the semantic directions `collect : Supply → ListValue` and `spread : Value → Supply`. Prefix `*name` in a binding position is a **collecting binding**: it collects its matched items into an exact list, and when it appears in a function signature it is called a **collecting parameter**. Postfix `value*` is instead a **spread expression** that contributes the operand's items to the surrounding item supply. Each marker must be directly attached to its name or operand: `* items` is not a collecting binding, a detached trailing `value *` is not a spread, and a `*` with a valid same-line right operand is always the multiplication operator — position and attachment, not spacing, decide which of the three meanings a star has.

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

Ordinary (non-collecting) parameters bind the receiver value itself, while a collecting parameter collects a NAMED property receiver as ONE list element (a stored receiver supplies its one value) — the two shapes are observably different:

```
Arg = 1, 2, 3

Collect(list) = list
CollectMany(*list) = list

Arg.Collect.count
Arg.CollectMany.count
```

**Results:**
```
3
1
```

`Arg.Collect` binds `list = (1, 2, 3)`, so `count` opens the sequence (3 items); `Arg.CollectMany` binds `list = [(1, 2, 3)]` — a named property receiver supplies its one stored value — so its count is 1. To supply the stored items instead, spread them: the fluent `Arg*.CollectMany.count` and the grouped receiver `(Arg*).CollectMany.count` are both `3`.

#### Dotted Receivers and Collecting Parameters

A **written group receiver** is different: the receiver of an ordinary dot call's lexical fallback is one leading segment whose evaluated top-level supply a flat top-level collecting parameter consumes, so writing the rows inline supplies them individually. This is what makes dotted aggregates read naturally:

<!-- spec:dot-receiver-segment-supply -->
```
Mean(*Vector) = Vector.sum / Vector.count

Mean(1, 2, 3)
(1, 2, 3).Mean
```

**Results:**
```
2
2
```

`(1, 2, 3).Mean` supplies the written rows `1`, `2`, `3` to the collector (`Vector = [1, 2, 3]`), exactly like the flat call `Mean(1, 2, 3)`. The receiver is still ONE segment for arity and for fixed parameters: with `F(first, *middle, last)`, `(1, 2).F(9)` binds `first = (1, 2)` whole (fixed parameters bind the receiver's one captured value), and `(1, 2).F` is an arity error — the receiver's item count never satisfies fixed-parameter arity. An extra written boundary survives as one item (`((1, 2)).CollectMany` collects `[(1, 2)]`), the empty receiver supplies nothing (`().CollectMany` collects `[]`), and exact lists stay opaque (`[1, 2].CollectMany` collects `[[1, 2]]`). Direct calls are unchanged: a written argument slot always reifies to one value, so `CollectMany((1, 2, 3))` still collects `[(1, 2, 3)]`. The [graced source](#grace-with-dot-calls) `S~.Mean` is the same ordinary dot edge with frontend-only Grace on `S`, so it keeps the same one-segment receiver behavior and raw-supply rule (a written group is not a valid postfix-Grace operand).

A function signature may contain fixed and collecting parameters. When a parameter list has two or more parameters and one of them is a collecting parameter, the collecting parameter may appear at the front, middle, or end. Fixed parameters before it bind from the front, fixed parameters after it bind from the back, and the collecting parameter collects the remaining middle slots (possibly zero) as one exact immutable list. The supplied items are the call argument slots: a bare argument supplies one slot (a stored sequence value is one slot, not opened), and only an explicit spread opens a sequence value into separate slots:

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

A collected segment of one grouped value is the one-element list holding it — `Tail(1, (2, 3))` collects `rest = [(2, 3)]`, never the bare pair — so one remaining structured item stays distinguishable from the item's own elements.

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

The pattern unpacks the single stored sequence value `A`, so `x, *y, z = A` splits `A` into its items: `x = 1`, `y = [2, 3, 4]`, `z = 5`. Explicit `x, *y, z = A*` supplies the same items, and a direct item supply `x, *y, z = 1, 2, 3, 4, 5` binds the same way. Fixed targets bind from the start and end; the collecting target collects the middle as one exact immutable [list](#lists). `*head, last = 1, 2, 3` binds `head = [1, 2]` and `last = 3`; `first, *tail = 1, 2, 3` binds `first = 1` and `tail = [2, 3]`; a singleton collected segment stays a one-element list (`x, *tail = 1, 2` binds `tail = [2]`), and `x, *y, z = 1, 2` binds `y = []`. With a single fixed target plus a collecting binding, `first, *rest = A` unpacks `A` into `first = 1` and `rest = [2, 3, 4, 5]` — the same as `first, *rest = A*`. A lone collecting target is also valid: `*all = 1, 2, 3` binds `all = [1, 2, 3]`, while `*all = ()` binds `all = []`. Without a collecting binding the item count must match exactly, so `x, y = 1, 2` binds `x = 1` and `y = 2`, while `x, y = 1` (one item) and `x, y = 1, 2, 3` (three items) are arity errors against the two targets. This unpacking is deconstruction-specific: a function call `F(A)` still passes `A` as one argument, so calls need `F(A*)` to open it. More than one collecting binding (`*a, *b = 1, 2, 3`) is rejected. The right-hand side is an ordinary expression of the surrounding algorithm: it is evaluated once for all of its targets, and a name it does not resolve becomes an implicit parameter of that algorithm (never of the deconstruction itself):

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

Use sequence-value parameter patterns when one fixed argument slot should be opened during binding. This is different from a top-level `*name`: the sequence-value pattern consumes exactly one argument slot, requires that slot to be a sequence value, and binds only that sequence value's immediate contents.

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

In `CountValues`, top-level `*values` collects the call's argument slots: `CountValues()` collects the empty supply `[]` (count `0`), `CountValues(1, 2, 3)` collects the three slots as `values = [1, 2, 3]` (count `3`), and `CountValues((1, 2, 3))` supplies ONE sequence-valued argument, collected as `values = [(1, 2, 3)]` (count `1`). In `CountSequenceValue`, the outer sequence-value pattern consumes one parent-level argument slot, opens it, and `*values` collects that sequence value's immediate contents (count `3`). The builtin `count(collection)` has no collecting parameter: it is an ordinary fixed-arity callable that takes exactly one collection argument, so with `Values = 1, 2, 3`, `count(Values)` is `3` while `count(1, 2, 3)` and `count(Values*)` are arity errors (see [Counting: `count`](#counting-count)); fixed-only user calls likewise preserve their exact call shape.

A pattern-shaped callee consumes written grouping levels at the call site. A bare reference supplies the stored value for the pattern to open, while ONE extra written level of parentheses leaves a single grouped item — which the collecting parameter collects exactly. Levels beyond that stay redundant (unary sequence structure canonicalizes during value construction), and a nested pattern consumes matching written depth:

```
Inner = (1, 2, 3)
CountSequenceValue((*values)) = values.count
NestedCount(((*values))) = values.count

CountSequenceValue(Inner)
CountSequenceValue((Inner))
CountSequenceValue(((1, 2, 3)))
NestedCount(((1, 2, 3)))
NestedCount((((1, 2, 3))))
```

**Results:**
```
3
1
1
3
3
```

`CountSequenceValue(Inner)` opens the stored sequence into its three items. `CountSequenceValue((Inner))` supplies one written grouping level whose single item is `Inner`, so `values = [Inner]` (count `1`), and `CountSequenceValue(((1, 2, 3)))` is the same shape. `NestedCount` declares a second pattern level, so it consumes the extra written level and still opens down to the three items — and a fourth written level around it stays redundant. Two further distinctions remain observable. First, a nested pattern still needs at least its explicit sequence-value level: `NestedCount((1, 2, 3))` is an arity error, because the pattern expects one nested sequence-value argument but the spread items supply three. Second, non-unary structure is preserved: `CountSequenceValue(((1, 2), 3))` reports `2`, because the sequence value's items are `(1, 2)` and `3`.

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
Final = Step.repeat(2, (1, 2), 2):0
Final
```

**Result:** `(1, 2, 3, 4)`

(The capture into `Final` keeps the projected accumulator one report row; a bare `Step.repeat(...):0` as the lone root row would spread the projection across rows — see the lone-root projection rule in [Output Selection](#output-selection).)

`(*history)` opens the single sequence-value state slot and collects its items as the exact list `history`. Inside `(history*, previous + 1)`, the spread `history*` opens that one list boundary into its immediate items (see [Opening One Level vs. Flattening](#opening-one-level-vs-flattening)), so each step rebuilds one flat accumulator sequence value beside the new value: `(1, 2)` → `(1, 2, 3)` → `(1, 2, 3, 4)`. The accumulator grows flat while remaining a single state slot beside `previous + 1`. The comma after the spread is required — `history* previous` would be the multiplication `history * previous` — and it is what places `previous + 1` beside the spread history items.

Only one collecting binding is allowed in each comma-separated pattern level, collecting bindings must be explicit, and they cannot use the Grace `~` reordering operator. The collect marker must be directly attached to its binding name: `*items` is a collecting binding, while `* items` is an error.

<a id="reordering-parameters-with-grace-operator"></a>

### Reordering Parameters with Grace

Sometimes the natural reading order of parameters in a definition does not match the intended calling convention. Grace (`~`) shifts a parameter's position.

Prefix `~x` moves `x` one position earlier in the parameter list. Postfix `x~` moves `x` one position later. Grace applies only to a bare parameter/name occurrence — `~x` and `x~` are the two supported forms. Attaching `~` to anything else (a parenthesized expression, a call result, a dot result, a list, a literal) is an error: `(x + y)~`, `f(x)~`, and `5~` are rejected, and parentheses never smuggle an expression into Grace (`(x)~` is rejected too). A marker written before a call, `~f(x)`, is grace on the callee name `f` itself — the call applies to the graced name, exactly like the postfix `f~(x)` idiom.

```
# Without Grace, parameter order would be (y, x) since 'y' appears first.
# ~x moves x one position earlier → call order: (x, y)
Divide = y / ~x

Divide(2, 10)
```

**Result:** `5`

---

## Conditionals

`if` is a builtin algorithm with exactly three argument slots: `if(condition, whenTrue, whenFalse)`. Usually you pass the three arguments directly. There is no two-argument form. A grouped value used without spread is still one argument, so `if(X)` is invalid when `X = 1, 2, 3`; explicit spread in call-argument position supplies one value's items across the three slots, so `if(X*)` works (the arguments are counted after spread expansion).

The condition is numeric: `0` is false and any nonzero number is true.

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

`if(condition, whenTrue, whenFalse)` evaluates only the selected branch and returns that branch as **one value**. This is just the general [call value boundary](#calls-return-one-value) applied to `if`: if the selected branch is a multi-output property such as `X = 1, 2, 3`, the `if` result is the grouped sequence value `(1, 2, 3)` — the same single value you observe by referencing `X` directly. Use a caller-site spread, for example `if(1, X, X)*`, to contribute its items as separate output slots:

```
X = 1, 2, 3
if(1, X, X)
if(1, X, X)*
```

**Results:**
```
(1, 2, 3)

1
2
3
```

Explicit spread also works in **call-argument position**. Spreading a three-item value into the call opens it across the three argument slots, so `if(X*)` is equivalent to `if(1, 2, 3)` and selects the `whenTrue` branch:

```
X = 1, 2, 3
if(X*)
```

**Result:**
```
2
```

This makes a direct `if(X*)` behave the same as a user-defined wrapper such as `MyIF(a, b, c) = if(a, b, c)` called as `MyIF(X*)`. A spread that does not expand to three values is an evaluation-time arity error, just like any other builtin.

---

<a id="repetition"></a>

## Collections and Repetition

> **Core idea:** collection builtins receive one collection value. Use `range`, `filter`, `map`, and the other collection operations for data transformations; use `repeat` or `while` when a calculation must carry state between steps.

### Inclusive Integer Lists: `range`

`range(start, stop)` is a builtin algorithm that returns every integer from `start` to `stop`, inclusive.

- If `start < stop`, it counts upward by `1`
- If `start > stop`, it counts downward by `1`
- If `start == stop`, it returns a one-element list
- Both arguments must be integers

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

A `range` call is a value boundary: each bare call materializes one exact immutable [list value](#lists) (`range(3, 3)` is the one-element list `[3]`, never erased to the bare atom `3`). The list result is itself one collection argument for the next builtin:

```
range(1, 3)
range(1, 3)*
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

`filter(collection, predicate)` walks the bound collection's items from left to right and keeps only the top-level elements whose predicate result is exactly one atomic numeric value.

Both call styles are supported: `filter(collection, predicate)` and `collection.filter(predicate)`.

- Kept elements stay in their original order
- Rejected elements disappear completely; no placeholders are inserted
- The predicate's current item behaves like `S:i` for the traversed sequence `S`
- Sequence-value current items therefore expose their immediate members to the predicate, but `filter` still keeps or discards the original top-level element
- Nested sequence values stay intact; the callback view is one-level only
- Predicate result must be exactly one atomic numeric value: `0` rejects, nonzero keeps
- Sequence-valued, multi-output, empty, or string predicate results are errors

```
IsEven = x mod 2 == 0
filter((1, 2, 3, 4, 5, 6), IsEven)

GreaterThanThree = x > 3
filter(range(1, 5), GreaterThanThree)

KeepPair(tag, value) = tag mod 2 == 0
filter(((1, 10), (2, 20), (3, 30), (4, 40)), KeepPair)
```

**Results:**
```
[2, 4, 6]

[4, 5]

[(2, 20), (4, 40)]
```

`filter` is a value boundary: the bare call returns one exact immutable list value. Open the kept items with caller-site spread:

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

If every predicate result is `0`, `filter` returns the empty list `[]` (never `()`).
Predicate results such as `0, 999`, `(1, 0)`, or `x.string` are invalid because `filter` does not derive truth from sequence-valued, list-valued, or multi-output results.
The same callback rule applies everywhere, and parentheses shape the collection argument. `filter((1, 2), predicate)` and a helper `Values = (1, 2)` followed by `filter(Values, predicate)` each call `predicate` once for each item in that sequence value, and a lone exact list value is opened the same way, so `filter([1, 2], predicate)` also calls `predicate` once per element. Calls such as `filter(range(1, 5), predicate)` (the range result is a list, opened as the bound collection), `P = range(1, 5)` followed by `filter(P, predicate)`, and `filter((range(1, 5)*, 8), predicate)` call `predicate` once per immediate item. The collection must stay one argument: `filter(1, 3, 5, IsEven)` and `filter(range(1, 5)*, 8, predicate)` are arity errors because `filter(collection, predicate)` expects exactly 2 arguments.

### Mapping: `map`

`map(collection, mapper)` walks the bound collection's items from left to right and replaces each top-level element with `mapper(element)`.

- The mapper's current item behaves like `S:i` for the traversed sequence `S`
- Sequence-value current items expose their immediate members; nested sequence values stay intact
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

`map` is a value boundary: the bare call returns one exact immutable list value. Open the mapped items with caller-site spread:

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

Because sequence-value callback items are projected one level, write `Swap(a, b) = (b, a)` when mapping over sequence-value pairs.
With that rule, `map(((1, 2), (3, 4)), Swap)` calls `Swap` once per pair and produces the exact list value `[(2, 1), (4, 3)]` (append `*` to open the mapped pairs into an item supply). A single sequence-value argument such as `Values = (1, 2)` followed by `map(Values, Swap)` is opened one level into the two atom items `1` and `2`, so the mapper runs once per atom — a two-parameter callback like `Swap` then fails with an arity error. Use a one-parameter callback for atom items, and reserve `Swap(a, b)` for collections whose items are pairs, as in `map(((1, 2), (3, 4)), Swap)`. The one bound collection may be a grouped sequence value or a lone exact list value — both open one level: `map(range(1, 5), Double)` (the range result is a list), `Values = 1, 2, 3` followed by `map(Values, Double)`, and `map((1, range(2, 4)*), Double)` run once per immediate item.

Math functions and their lowercase aliases are ordinary callables, so they work directly as callbacks: `[1, -2].map(abs)` and `[1, -2].map(Math.Abs)` are both `[1, 2]`, and `[0, 1].map(sin)` maps each element through `sin`. The callback always binds its own per-element argument — a same-named value in the surrounding algorithm is never captured:

<!-- spec:native-flat-callback-binding -->
```
F(x) = [1, -2].map(abs)
F(5)
```

**Result:** `[1, 2]`

Callbacks with a collecting parameter collect exactly like ordinary calls. A callback whose only parameter is a collecting parameter receives each iterated element as ONE collected slot, so `items` is the one-element list `[element]`, whatever the element's kind:

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

A multi-parameter flat callback instead opens a lone sequence-valued element into row slots first (the same row rule fixed callbacks use), and the shared front/collecting/back allocation then collects the middle: with `F(first, *middle, last) = middle` and `Rows = [(1, 2, 3, 4)]`, `Rows.map(F)` is `[[2, 3]]` — exactly what the nested pattern form `F((first, *middle, last))` produces on sequence rows. Exact-list elements stay opaque in flat binding (a lone `[1, 2]` element is ONE argument, so a two-parameter flat callback arity-errors); use the nested pattern form `F((x, y))`, which opens sequence AND list rows. The same collection rule reaches `filter` predicates (`IsSingleSeven(*items) = items == [7]` keeps `7` out of `[7, 8]`). Reduce supplies two callback slots, element and accumulator, so a reducer whose only parameter is a collecting parameter, `R(*items)`, collects `items = [element, accumulator]`; with `R(*items, acc)`, the collecting parameter before the fixed accumulator instead collects only `[element]`.

Multi-clause conditional algorithms used as callbacks match the projected element as ONE argument and get no flat-callback row expansion: a flat two-parameter mapper `F(x, y)` works over pair rows, but adding a second clause (making the family conditional) flips the same `Rows.map(F)` to `No matching branch`, because each clause now matches against the single projected element. Write nested sequence-value clause heads — `F((0, y)) = ...`, `F((x, y)) = ...` — when a clause family should destructure rows.

### Collection Inputs

`filter`, `map`, `order`, `orderDesc`, `count`, `contains`, `first`, `last`, `distinct`, `take`, `skip`, `min`, `max`, `sum`, `avg`, and `reduce` are ordinary fixed-arity callables that receive **one collection object** plus fixed control arguments. The fixed signatures are:

`count(collection)`, `sum(collection)`, `first(collection)`, `last(collection)`, `min(collection)`, `max(collection)`, `avg(collection)`, `order(collection)`, `orderDesc(collection)`, `distinct(collection)`, `take(collection, count)`, `skip(collection, count)`, `contains(collection, item)`, `map(collection, mapper)`, `filter(collection, predicate)`, and `reduce(collection, reducer, initial)`.

Use `()` for a canonical sequence, `[]` for an exact [list](#lists), or receiver-style dot syntax (`collection.take(2)`) for concise expressions.

- After binding, the one collection argument is viewed one level deep: a lone sequence value or exact list value opens into its immediate items, an atom or string is a one-element collection, and nested sequence or list elements stay opaque items. So `count((1, 2, 3))`, `count([1, 2, 3])`, and `count(range(1, 5))` count their items (`3`, `3`, and `5`), `count(7)` is `1`, `count(((1, 2), (3, 4)))` is `2` (each pair is one item), and `count((1, [2], 3))` is `3` (the nested list is one opaque item).
- The remaining parameters are ordinary fixed arguments: `take((1, 2, 3), 2)` binds `collection = (1, 2, 3)` and `count = 2`; `map`, `filter`, and `reduce` bind their callback and accumulator arguments the same fixed way.
- The argument count is checked like any callable. `count(1, 2, 3)` is an arity error — `count(collection)` expects 1 argument, but was called with 3 — and `take([1, 2, 3])` is an arity error too: the list is the one collection argument, and `count` is missing.
- A call with no argument is never an empty collection: `count()` is an arity error, distinct from `count(())` which returns `0` (and `count([])`, also `0`). Absence of an argument and an empty collection value are different things.
- Spread supplies ordinary call arguments; it does not feed a builtin's collection parameter. With `Values = 1, 2, 3`, `count(Values*)` passes three arguments and is an arity error, as is `take([1, 2, 3]*, 2)`. Re-group with parentheses when a spread must become one collection: `count((Values*, 8))` is `4`, and with `A = 1, 2` and `B = 3, 4`, the grouped `sum((A*, B*))` is `10` — the concatenation form — while `sum(A*, B*)` and `sum(A, B)` are arity errors. A spread that lands on exactly the right argument count is an ordinary call: `take([7]*, 1)` passes `7` and `1` and returns `[7]`.
- Dot-call supplies the receiver as the collection argument. With `Values = 1, 2, 3`, `Values.count` is `3`; `range(1, 5).take(2)` is `[1, 2]`; `X.filter(P).count` counts the kept items. A user-defined collecting helper is different from a builtin here: `Helper(*values) = values.count` accepts `Helper(1, 2, 3)` and `Helper(Values*)` because a collecting parameter collects the call's argument slots as one exact list, while the builtin `count` accepts only the single-collection forms. (See [Collecting Explicit Parameters](#collecting-explicit-parameters).)
- `:` selection projects one level of content before the builtin binds the selected value. `Pairs = (1, 2), (3, 4)` gives `(Pairs:0).count = 2`. `Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)` gives `(Data:0).order` as the exact list value `[1, 2, 4, 6, 7]`.
- Higher-order callbacks still receive the one-level projected current item, so sequence elements are available through ordinary parameters or `item:i`. Any collection builtin applied to that callback variable consumes the projected item's emitted top-level items
- Nested sequence values are never recursively flattened unless a builtin explicitly says so, such as `atoms`; use a spread expression (`value*`) to open only one outer boundary
- `contains` compares its searched item against the collection's top-level items using ordinary KatLang value equality; it does not recurse into nested sequence elements
- `distinct` compares those top-level items structurally, using the same ordinary KatLang value equality rules
- `take` and `skip` follow the same family pattern: direct calls take the count as the second fixed argument (`take((1, 2, 3), 2)` / `skip((1, 2, 3), 2)`), and dot-calls use `collection.take(2)` / `collection.skip(2)`

### Ordering: `order` and `orderDesc`

`order(collection)` sorts the bound collection's top-level numeric items in ascending order.
`orderDesc(collection)` sorts the same kind of top-level items in descending order.

- Both builtins evaluate the full collection eagerly before sorting
- Duplicates are preserved; there is no implicit distinct or unique step, so use `distinct` separately when deduplication is required
- The result is one exact immutable list value (the call is a value boundary); use a caller-site spread (`value*`) when the surrounding context needs the sorted items as an item supply
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

`order`/`orderDesc` are value boundaries: each bare call returns one exact immutable list value. Open the sorted items with caller-site spread:

```
X = 3, 1, 2
X.order
X.order*
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
Named sequence helpers and call receivers such as `Values = 1, 2, 3` followed by `order(Values)` and `Values.order` return the exact list value `[1, 2, 3]`; `P = range(5, 1)` followed by `order(P)` and `range(5, 1).order` return `[1, 2, 3, 4, 5]` (the range result is itself a list, opened as the bound collection), and `order([3, 4, 2, 1])` sorts a literal list the same way. Inline and spread forms are arity errors — `order(3, 4, 2, 1)`, `order(Values*)`, and `order(Values*, 8)` all supply more than the one argument `order(collection)` expects. To add an extra item, group it into the collection: `order((Values*, 8))` returns `[1, 2, 3, 8]`. Selection already projects one level of content, so `(Data:0).order` sorts `7, 6, 4, 2, 1` to `[1, 2, 4, 6, 7]`. Each is one value at the call boundary; append the spread marker (for example `Values.order*`) when the surrounding context needs the sorted items as an item supply.

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
`count(())` and `count((()))` both return `0` because repeated ordinary parentheses around the empty sequence canonicalize to `()`. `count()` with no argument at all is an arity error, not `0` — absence of an argument is never an empty collection. `count({})` is an error because a no-output body has no defined output. `count((1, 2, 3))`, `Values = (1, 2, 3)` followed by `count(Values)`, `Values.count`, and `((1, 2, 3)).count` all return `3`, because the one bound collection value is opened one level; a lone exact list value is opened the same way, so `count([1, 2, 3])` is also `3`, and `count(range(1, 5))` counts the five elements of the range list. `Values = 1, 2, 3` followed by `count(Values)` and `Values.count` also return `3`, but `count(1, 2, 3)` and `count(Values*)` are arity errors — `count(collection)` expects exactly one argument, and spread supplies ordinary call arguments (three here) rather than feeding the collection parameter. In `count((3, 4, range(1, 5)*, 7))`, the spread opens the range list's elements inside one sequence value, so the count is `8`. Selection still projects one level first, so `Pairs = (1, 2), (3, 4)` followed by `(Pairs:0).count` returns `2`.

### Membership: `contains`

`contains(collection, item)` returns `1` when any top-level item of the bound collection equals `item`, otherwise `0`.

- Comparison uses ordinary KatLang value equality
- Atoms compare by numeric value, strings by exact string value, and sequence values structurally by sequence elements
- Search is top-level only; nested sequence elements are not searched recursively
- Empty collections return `0`

Both call styles are supported: `contains(collection, item)` and `collection.contains(item)`.

```
contains(range(1, 5), 3)

contains(range(1, 5), (1, 2, 3, 4, 5))

Pairs = (1, 2), (3, 4)
Pairs.contains((1, 2))
```

**Results:**
```
1

0

1
```

`contains(range(1, 5), 9)` returns `0` because no top-level item equals `9`.
`contains(((1, 2), (3, 4)), (1, 2))` returns `1` after the outer collection value is opened one level — a lone exact list value opens the same way, so `contains([1, 2, 3], 2)` returns `1` (and the `range` examples above already search a list collection). KatLang still does not recurse beyond the immediate top-level items. Selection projects one level first, so with `Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)`, `(Data:0).contains(4)` and `contains(Data:0, 4)` both return `1`. Spreading the collection is an arity error instead: `contains((Data:0)*, 4)` supplies the five projected items plus `4` as six ordinary arguments, but `contains(collection, item)` expects 2.

### First Element: `first`

`first(collection)` returns the first top-level value in the bound collection, unchanged.

- The collection must be non-empty
- Atoms, strings, and sequence values each count as one top-level element
- Sequence values are preserved whole and are not flattened

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

`last(collection)` returns the last top-level value in the bound collection, unchanged.

- The collection must be non-empty
- Atoms, strings, and sequence values each count as one top-level element
- Sequence values are preserved whole and are not flattened

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

`distinct(collection)` returns the bound collection's top-level items with later duplicates removed, as one exact immutable list value.

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

`distinct` is a value boundary: the bare call returns one exact immutable list value. Open the deduplicated items with caller-site spread:

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

`Values = ((1, 2), (1, 2), (3, 4))` followed by `distinct(Values)` removes the duplicate sequence value after the one bound collection value is opened one level (a lone exact list value is opened the same way); `Values.distinct` agrees — both return `[(1, 2), (3, 4)]`. `distinct(Values*)` is an arity error instead: the spread supplies the three pairs as three ordinary arguments, but `distinct(collection)` expects one. The same rule makes `distinct(1, 1)` an arity error — write `distinct((1, 1))`, which returns `[1]`.

### Take Prefix: `take`

`take(collection, count)` returns the first `count` top-level values of the bound collection, unchanged, as one exact immutable list value.

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

`take` is a value boundary: the bare call returns one exact immutable list value. Open the taken items with caller-site spread:

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

`take((1, 2, 3), 0)` and `take((1, 2, 3), -2)` both return the empty list `[]`. `take((3, 4), (1, 2, 3))` is invalid because the count must be exactly one whole-number value, not a sequence value. The collection must arrive as one argument: `take([1, 2, 3])` is an arity error — `take(collection, count)` expects 2 arguments, the list is the one collection argument, and `count` is missing — while `take([1, 2, 3], 2)` returns `[1, 2]`. Spread supplies ordinary call arguments, so `take(Values*, 1)` with `Values = (1, 2, 3)` and `take([1, 2, 3]*, 2)` are arity errors too; `take(Values, 1)` returns `[1]`, and `Values.take(2)` returns the exact list value `[1, 2]` (use `Values.take(2)*` to spread it). A spread that lands on exactly the right argument count is still an ordinary call: `take([7]*, 1)` passes `7` and `1` and returns `[7]`.

### Skip Prefix: `skip`

`skip(collection, count)` returns the bound collection's items after skipping the first `count` top-level values, as one exact immutable list value.

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

`skip` is a value boundary: the bare call returns one exact immutable list value. Supply the remaining items with caller-site spread:

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

`skip((1, 2, 3), 0)` and `skip((1, 2, 3), -2)` both return `[1, 2, 3]`. `skip((1, 2), 'hello')` is invalid because the count must be exactly one whole-number value. `Values = (1, 2, 3)` followed by `skip(Values, 1)` and the list form `skip([1, 2, 3], 1)` both return the exact list value `[2, 3]`, and `Values.skip(1)` does the same (use `Values.skip(1)*` to spread it) — the one bound collection opens one level, whether grouped, list, or receiver. `skip(Values*, 1)` is an arity error: the spread supplies three ordinary arguments plus the count, but `skip(collection, count)` expects 2.

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

Applying `min` to an empty collection is invalid because `min` requires at least one top-level numeric element. `min(((1, 2), (3, 4)))` is invalid because sequence-value items are preserved (not flattened), and each top-level item must be one atomic numeric value. `min(range(1, 5))`, `P = range(1, 5)` followed by `min(P)`, `Values = 1, 2, 3` followed by `min(Values)`, `Values.min`, `min((1, 2, 3))`, and `(1, 2, 3).min` all succeed — the one bound collection opens one level, whether it is a sequence value, an exact list value (such as the `range(1, 5)` result), or a dot-call receiver, so the grouped, list, and dot-call forms agree. `min(1, 2, 3)` is an arity error: `min(collection)` expects one argument. Selection such as `(Data:0).min` projects one level of content first.

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

Applying `max` to an empty collection is invalid because `max` requires at least one top-level numeric element. `max(((1, 2), (3, 4)))` is invalid because sequence-value items are preserved (not flattened), and each top-level item must be one atomic numeric value. `max(range(1, 5))`, `P = range(1, 5)` followed by `max(P)`, `Values = 1, 2, 3` followed by `max(Values)`, `Values.max`, `max((1, 2, 3))`, and `(1, 2, 3).max` all succeed — the one bound collection opens one level, whether it is a sequence value, an exact list value (such as the `range(1, 5)` result), or a dot-call receiver, so the grouped, list, and dot-call forms agree. `max(1, 2, 3)` is an arity error: `max(collection)` expects one argument. Selection such as `(Data:0).max` projects one level of content first.

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

Applying `sum` to an empty collection returns `0`: `sum(())` and `sum([])` are both `0` — but `sum()` with no argument at all is an arity error, because absence of an argument is never an empty collection. `sum(((1, 2), (3, 4)))` is invalid because `sum` preserves sequence-value items (it does not flatten them), and each top-level item must be one atomic numeric value. `sum(range(1, 5))`, `P = range(1, 100)` followed by `sum(P)`, `Values = 1, 2, 3` followed by `sum(Values)`, `Values.sum`, `sum((1, 2, 3))`, `sum([1, 2, 3])`, `(1, 2, 3).sum`, and `{1, 2, 3}.sum` all succeed — the one bound collection opens one level, so the grouped, list, and dot-call forms agree. `sum(1, 2, 3)` and `sum(Values*)` are arity errors; to concatenate two stored collections, group the spreads into one collection value: with `A = 1, 2` and `B = 3, 4`, `sum((A*, B*))` is `10`, while `sum(A*, B*)` and `sum(A, B)` are arity errors. Selection such as `(Data:0).sum` projects one level of content first.

### Average: `avg`

`avg(collection)` averages the bound collection's top-level numeric elements and returns one numeric result.

- The collection must be non-empty
- Each top-level element must be exactly one atomic numeric value
- A single numeric value is treated as a one-element collection
- The C# runtime returns the decimal arithmetic mean (total divided by count), for example `avg((1, 2))` returns `1.5` and `avg((-1, -2))` returns `-1.5`. (Lean's Int-only core approximates this with truncation toward zero, e.g. `avg((1, 2)) = 1` there — a model limitation, not the runtime contract.)
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

Applying `avg` to an empty collection is invalid because `avg` requires at least one top-level numeric element. `avg(((1, 2), (3, 4)))` is invalid because `avg` preserves sequence-value items (it does not flatten them), and each top-level item must be one atomic numeric value. `avg(range(1, 5))`, `P = range(1, 5)` followed by `avg(P)`, `Values = 1, 2, 3` followed by `avg(Values)`, `Values.avg`, `avg((1, 2, 3))`, and `(1, 2, 3).avg` all succeed — the one bound collection opens one level, whether it is a sequence value, an exact list value (such as the `range(1, 5)` result), or a dot-call receiver, so the grouped, list, and dot-call forms agree. `avg(1, 2, 3)` is an arity error: `avg(collection)` expects one argument. Selection such as `(Data:0).avg` projects one level of content first.

### Reduction: `reduce`

`reduce(collection, reducer, initial)` walks the bound collection from left to right and threads an accumulator through the top-level items.

- `reducer(element, accumulator)` receives the current item through the same one-level projection as `S:i`
- A reducer whose only parameter is a collecting parameter, `R(*items)`, collects both callback slots as the exact list `[element, accumulator]`; this is the ordinary collecting-call rule, not a reducer-specific exception
- `reduce` treats the accumulated value as reducer state: a normal accumulator parameter receives that state as one structural value, while a top-level collecting accumulator parameter receives the accumulator's top-level state slots, matching collecting `while` and `repeat` step parameters
- The reducer must return exactly one next accumulator value
- One sequence-value top-level element still contributes one fold step; the element view is projected one level, not recursively flattened
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

Append(item, *history) = (history*, item)
reduce((2, 3, 4), Append, 1)
```

**Results:**
```
10

60

(10, 4)

(1, 2, 3, 4)
```

No wrapper helper is required for sequence-value accumulators: a parenthesized sequence value such as `(a, b)` is one sequence-value accumulator value when the reducer uses a normal accumulator parameter. Use a top-level collecting accumulator parameter when the reducer should treat that accumulator as state slots. The state-slot view follows the ordinary non-spread item rule: a sequence-valued accumulator opens into its items as slots, while an exact-list accumulator stays ONE opaque slot — so switching an accumulator from `(0, 0)` to `[0, 0]` changes the collecting reducer's slot shape. To grow a sequence-value accumulator, spread the prior items beside the new value with a comma — `(history*, item)`. The comma is required: `history* item` (without the comma) is the multiplication `history * item`, because a `*` with a same-line right operand always multiplies.
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

1. The step algorithm's **last output** is the continuation flag: non-zero means continue, `0` means stop.
2. All outputs except the last form the working state, passed as input to the next iteration.
3. **Pre-check semantics:** the loop returns the state from the last iteration where the flag was non-zero. The iteration that produces flag `0` is never committed.

```
# Step: decrement x, continue while x > 1
Step = x - 1, x > 1

Step.while(5)
```

**Result:** `1`

When `Step` runs with `x = 1`, it would produce `(0, 0)` — the flag is `0`, so this result is discarded and the loop returns `1` from the previous iteration.

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

### Multi-Output Example

Computing both area and circumference of a circle:

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

> **Core idea:** pass a named algorithm or a brace algorithm when a caller expects a callable. Parentheses create a value grouping, so they deliberately suppress callable identity.

An algorithm can accept another algorithm as an argument and call it. This is how you write generic, reusable computation patterns.

### Algorithm as Argument

Fixed calls preserve argument expression boundaries. If a property expects multiple arguments and you already have a multi-output value, project the pieces explicitly or use a spread expression (`value*`) when you intentionally want that result sequence to spread into call argument items.

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

Grouping is different: parentheses capture a *value*, and a captured value never carries the algorithm identity of what it encloses, so `Apply((Increment))` and `Call0((Const))` fail even though the bare names work. (Parentheses directly around a brace block simply normalize away, so `Call0(({42}))` behaves exactly like `Call0({42})`.)

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

Names the callee does *not* declare as parameters still resolve outward as usual, so a nested property keeps reading its ancestor's parameter:

```
Outer(v) = Inner
  Inner = v + 1

Outer(7)
```

**Result:** `8`

Sequence builtins `filter`, `map`, and `reduce` are a special higher-order case. Their per-item callback argument behaves like `S:i` for the traversed sequence `S`, so sequence-value current items expose their immediate members without recursive flattening. This rule is local to those builtins; ordinary higher-order calls such as `Apply(Increment)` still use ordinary argument binding.

### Algorithms vs. Grouped Expressions

The distinction between braces, parentheses, and square brackets is critical. Their roles are:

| Syntax | Meaning |
|---|---|
| `( ... )` | Expression grouping/capture, or call-argument syntax after a callable — no new parameter scope and no declarations |
| `[ ... ]` | Exact immutable list construction — element expressions only, no declarations |
| `{ ... }` | Algorithm value — a new lexical scope that owns its inferred parameters, local declarations, and `open` |
| `{a + 1}` | Algorithm with parameter `a`, passable as an argument |

`{}` braces create an **algorithm** — a computation with its own identity and scope, which owns whatever parameters its body needs (`a` in the example above; an algorithm with zero parameters is still an algorithm). A `()` expression is **grouping**, not an algorithm — it has no scope of its own, so any free names inside it belong to the enclosing algorithm instead.

Only `{ ... }` creates an algorithm-level lexical scope, so only brace blocks (and the root) own declarations. Parentheses may group and compose output expressions, but an `open` declaration or a property/function definition inside `( ... )` is a parse error pointing you at braces:

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

A brace block works anywhere an expression-valued algorithm is allowed, including directly as a function argument. The block's own opens and local properties resolve inside the block; they never leak outward or become implicit parameters of the surrounding algorithm:

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

Expression spreading is written with the postfix star — the **spread marker**. A spread expression `value*` evaluates `value` exactly once and contributes the items of its evaluated value to the surrounding item supply (output rows, call argument slots, or list/sequence elements), opening exactly ONE item-producing boundary. Conceptually `spread : Value → Supply` — a spread expression does not return or create a sequence or list by itself; the RECEIVER decides what the supplied items become. A sequence value or an exact [list value](#lists) supplies its contained items; an atom or string supplies itself as one item. The marker attaches to any completed expression — `items*`, `Calculate(x)*`, `(a + b)*`, `[1, 2]*`, `()*`, `[]*` — and repeated attached stars compose through an intermediate capture: `value**` means `(value*)*` (see [Repeated Spread Is Composition](#repeated-spread-is-composition)).

The same star is the multiplication operator, and multiplication wins whenever it can: **a `*` with a valid same-line right operand is multiplication regardless of spacing** — `a*b`, `a* b`, `a *b`, and `a * b` are all the product `a * b`. A directly attached `*` is the spread marker only when nothing on the same line can serve as a right operand: before a comma, before a closing delimiter, or at the end of the line. To spread `a` and then supply another same-line item, the comma is REQUIRED: `a*, b` — because `a* b` multiplies. The line ending separates the two readings as well: `a*` at the end of a line is a completed spread and the next line is a separate slot, while a detached trailing `a *` is a binary operator awaiting its operand, continuing the multiplication `a * b` across the newline.

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

A spread whose star closes the line does not continue onto the next line. In an algorithm body, the next complete expression is another expression-list item:

```
X*
Y
```

is interpreted as:

```
X*, Y
```

(Contrast the detached form: `X *` at the end of a line is the multiplication operator awaiting its right operand, so `X *` followed by a line `Y` is the product `X * Y`.)

You may still write an explicit comma for clarity:

```
X*,
Y
```

This has the same expression-list shape. If `x*` has no following expression, it simply spreads `x` followed by nothing.

Use parentheses for one sequence value:

```
(X, Y)
```

A spread expression is one whole expression-list slot, so:

```
Use(a b*)
```

means:

```
Use(a, b*)
```

Inside the open call-argument list the comma may be implicit — same-line adjacency separates slots, and because the `(` keeps the list open across lines a newline separates slots there too — so `Use(a b*)` and

```
Use(a
b*)
```

mean exactly the same `Use(a, b*)`. Adjacency can precede a spread because the star sits at the end of its own slot; only a slot that FOLLOWS a spread on the same line needs the explicit comma.

A spread applies only to its own operand. `a, b*, c` and its three-line form are expression lists of three slots — the comma after `b*` is required, because `a b* c` contains the multiplication `b * c` (two slots: `a` and `b * c`). Use `(a, b*, c)` for one sequence value.

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

Inside call argument lists and explicit parenthesized sequence values the list stays open across lines, so both same-line adjacency and a newline separate slots. Use parentheses when one sequence value is intended, such as `(a, b, c)`.

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
| `1* 2, 3` | The star has a same-line right operand, so it multiplies regardless of spacing: the slots are `1 * 2` and `3`, producing `2, 3` |
| `(1*, 2), 3` | The parenthesized expression list `(1*, 2)` is one sequence-valued output, followed by the separate output `3` |
| `(1, 2)*, 3` | The spread applies to `(1, 2)` (spreading its items `1, 2`); after the required comma, `3` is a separate expression-list slot. Produces `1, 2, 3` |
| `(1, (2, 3))*, 4` | Spread opens one level: `1` and the intact inner sequence value `(2, 3)` become items, and `4` is a separate slot, producing `1, (2, 3), 4` |
| `((1, 2))*, 3` | Redundant unary parentheses canonicalize during value construction, so `((1, 2))` is the value `(1, 2)`; the spread opens its items and `3` is a separate slot, producing `1, 2, 3` — same as `(1, 2)*, 3` |
| `1, { 2, 3 }` | Preserves the nested block boundary, producing `1, (2, 3)` |
| `1*, { 2, 3 }` | `1*` spreads `1`, then after the required comma the block `{ 2, 3 }` is a separate expression-list slot. Produces `1, (2, 3)` |

### Capture Parentheses

> **Parentheses around a supply-producing expression perform capture — they are not always redundant grouping.**

Around an ordinary single value, parentheses are redundant grouping: `(7)` is `7` and `([1, 2])` is `[1, 2]`. Around a spread, they are the capture receiver (`capture : Supply → Value`): the supplied items materialize as ONE canonical sequence value. The pair below is the clearest picture of the Value/Supply distinction:

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

A spread expression is itself a completed expression, so it can wear another attached star. There is no special depth operator — the second star is ordinary postfix composition:

`value**` means exactly `(value*)*`.

The first star produces a **supply**, not a value (`spread : Value → Supply`), and a spread marker needs a value to operate on. Between the two stars the ordinary expression boundary performs **capture** (`capture : Supply → Value`) — the same operation written parentheses perform. The full pipeline is:

```
Value ──spread──▶ Supply ──capture──▶ Value ──spread──▶ Supply
```

conceptually `value** = spread(capture(spread(value)))`. The intermediate capture is not an implementation accident; it follows from ordinary KatLang expression composition. Avoid reading `value**` as "spread the value, then spread the result again" — the first spread has no value result to re-spread; it is the capture step that turns the supply back into a value for the second star.

Because capture canonicalizes, what a second star changes depends only on how many items the FIRST spread supplies:

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
| `(A*).F` | Capture the spread supply as one sequence value, then dot-call `F` on that value |
| `A*:0` | Invalid — selection cannot be applied directly to an item supply (targeted parse error) |
| `(A*):0` | Capture the spread supply into one sequence value, then select from it |

Select-then-spread and capture-then-select are different operations:

<!-- spec:select-spread-vs-capture-select -->
```
A = [[1, 2], [3, 4]]

(A:0)*
(A*):0
```

**Results:**
```
1
2
[1, 2]
```

`(A:0)*` selects the stored list `[1, 2]` and spreads its elements into two rows; `(A*):0` captures the two-item spread supply as one sequence value and selects its first item — the intact list `[1, 2]`. Writing `A*:0` directly is a targeted parse error: "Selection cannot be applied directly to a spread expression — a spread supplies items to the surrounding item supply, not one selectable value," and the message names both rewrites so you can pick the intended one.

---

## Lists

> **Core idea:** `[items]` creates one exact immutable list. Unlike a sequence value, a list keeps its boundary even when it is empty or contains only one item.

Square brackets construct an **exact immutable list value** — KatLang's second collection kind, complementing sequence values:

<!-- spec:list-literal -->
```
[1, 2, 3]
```

**Result:** `[1, 2, 3]`

A list literal always evaluates to exactly ONE list value. Its elements use the ordinary expression-list rules (comma or adjacency separate elements, and an already-open `[` spans lines just like `(` and `{`), but unlike parenthesized sequence values, **no canonicalization ever applies to list structure**: lists preserve exact cardinality and nesting.

<!-- spec:list-exactness -->
```
[7] == 7
[[1, 2]] == [1, 2]
[[]] == []
```

**Results:**
```
0
0
0
```

`[]` is the empty list, `[7]` is a singleton list (it never collapses to `7`), and `[[7]]` is a singleton list containing another singleton list. List equality is structural and recursive: `[1, 2] == [1, 2]` is `1`, and `[1, [2]] == [1, 2]` is `0`.

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
0
0
```

The conceptual split:

| Kind | Written | Role |
|---|---|---|
| sequence value `()` | parentheses | canonical captured arity value — singleton and redundant boundaries canonicalize away |
| list `[]` | brackets | exact immutable collection value — structure is preserved exactly |
| item supply | (no literal) | temporary non-value structure consumed by binding and spread |

Ordinary parentheses stay a redundant SEQUENCE grouping even around lists:

<!-- spec:list-redundant-parens-canonicalize -->
```
([1, 2]) == [1, 2]
```

**Result:** `1`

Unlike `()`, the empty list `[]` is never transparent: `[] > 1` is a type error while `() > 1` passes the operand through, and `F([])` passes one empty-list argument while `F([]*)` supplies zero arguments.

### Indexing Lists

Selection `:` indexes into exact list values: `value:index` selects ONE immediate element by zero-based position, using exactly the same index rules as sequence selection. The selected element is returned exactly as stored — a nested list element stays an exact list, a sequence-valued element stays a sequence value, and nothing is flattened, spread, or converted between kinds.

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

`Rows:0` selects the stored element `[1, 2]` (one opaque list, count 1), and chaining `:` selects one level at a time, so `Rows:0:1` is `2`. Exact kinds survive selection: `[[1, 2]]:0 == [1, 2]` is `1` while `[[1, 2]]:0 == (1, 2)` is `0`.

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
y = A*

x
y
```

**Results:**
```
[1, 2, 3]
(1, 2, 3)
```

This distinction is essential: `x = value` preserves the value, `x = value*` opens one boundary and captures the resulting item supply.

Spread opens only the outermost boundary:

<!-- spec:list-spread-edges -->
```
A = []
B = [7]
C = [[7]]

A*
B*
C*
```

**Results:**
```
7
[7]
```

`A*` supplies zero items (its output row vanishes), `B*` supplies `7`, and `C*` supplies the inner list `[7]` intact.

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

`F(A)` without the spread is an arity error (one argument for three parameters), and `F([]*)` supplies zero arguments. An ordinary dotted call `A.F(9)` passes the whole list `A` as one leading receiver segment. The graced source `A~.F(9)` is the same ordinary dot edge with frontend-only postfix Grace on `A`, so it keeps the same receiver segment and list opacity.

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

A collecting binding COLLECTS the unmatched items as one exact immutable list — the same value kind the collection builtins produce:

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

Sequence builtins accept lists directly: the builtin's post-binding collection view opens ONE outer boundary of a lone collection value — a lone grouped sequence value or a lone exact list value — so a stored list feeds a builtin without any spread:

```
count([1, 2, 3])
```

**Result:** `3`

And the collection-producing builtins (`filter`, `map`, `order`, `orderDesc`, `distinct`, `take`, `skip`, `range`, `atoms`) materialize their results as exact immutable lists: zero kept items produce `[]`, one kept item produces the one-element list `[item]`, and nested elements stay exact.

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

Collecting bindings and collection builtins now agree on the result kind — both produce exact immutable lists — while ordinary single-name capture stays canonical. Compare:

```
A = [1, 2, 3]

x = A.take(1)*
x

head, *rest = A
rest
rest == A.skip(1)
```

**Results:**
```
1
[2, 3]
1
```

`x = A.take(1)*` spreads the one-element list `[1]` and CAPTURES the single item canonically (`x = 1`), while the collecting binding COLLECTS the remaining items as the exact list `[2, 3]` — equal to `A.skip(1)`. The rule of thumb is the operation triple: **ordinary value capture canonicalizes (`capture`), collecting binding collects an exact list (`collect`), and the spread marker spreads one boundary (`spread`).**

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

Algorithms in KatLang can produce structured, nested outputs — sequence values inside sequence values, exact lists inside lists, or any mix of the two. The `atoms` builtin recursively collects every numeric atom from that structure — opening **both** sequence and list boundaries, depth-first and left to right — and returns them as one exact immutable [list value](#lists).

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

`atoms(7)` is the singleton list `[7]`, never the bare `7` (`atoms(7) == [7]` is `1`; `atoms(7) == 7` is `0`), and `atoms((1, 2))` is the exact list `[1, 2]`, never the sequence `(1, 2)`. A no-atom input — `atoms('text')`, `atoms(())`, `atoms([])` — is the visible empty list `[]`. Strings and other non-numeric leaves contribute no atoms: `atoms((1, ['a', 2]))` is `[1, 2]`.

Exact list values are traversed exactly like sequence values:

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

The call boundary is unchanged: `atoms(value)` takes exactly one argument, an unspread list is one argument, `atoms(1, 2)` is an arity error, and `atoms([1, 2]*)` spreads two ordinary arguments — also an arity error (regroup with `atoms(([1, 2]*))` if you need to pass spread items as one value). Only explicit caller-site spread turns the result into an item supply: `atoms(A)*` contributes the collected atoms to the surrounding items. Finally, `atoms` does not define truthiness — its result is a list like any other, so `if(atoms((1, 2)), a, b)` is invalid, and truth testing still ignores list values entirely.

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

Repeating a binder name within one pattern adds an equality constraint. The first occurrence binds the value; later occurrences must be structurally equal and do not overwrite it:

```
Equal(x, x) = 1
Equal(x, y) = 0

Equal(1, 1)  # 1
Equal(1, 2)  # 0
```

This also works inside sequence-value parameter patterns such as `SamePair((x, x))`. Repeated names involving a collecting binding, such as `F(*xs, xs)`, are not supported.

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
Else(1, a, b) = a
Else(0, a, b) = b

Else(5 < 6, 2, 3)
Else(7 < 6, 2, 3)
```

**Results:**
```
2
3
```

The first argument is matched against `1` or `0`; the remaining arguments are bound to `a` and `b`.

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

Algorithms can be loaded from URLs using `load`. The loaded algorithm becomes a property whose public sub-properties you access with dot syntax.

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

String targets use single quotes and mix freely with names: `open 'https://example.org/lib.kat', LibA`. Comma is the only separator — `open A ; B` and `open A B` are parse errors asking for a comma, never two targets. An open target must provide algorithm identity: a parenthesized target such as `open (LibA)` is a parse error, because parentheses capture a value and a captured value never exposes the algorithm inside it — open the algorithm directly, or use a brace block (`open ({ ... })` works because parentheses around braces normalize away). The first target must begin on the same line as `open`. Comma keeps its normal explicit line-continuation behavior, so a long list may span lines with a trailing or leading comma:

```
open LibA,
LibB

open LibA
, LibB
```

A leading `.` likewise continues a dotted target across the line (`open Lib` followed by `.Sub` opens `Lib.Sub`). A plain newline never continues `open`: `open Math` followed by `Math.Pi` on the next line is an open plus a report row. Neither the collect marker nor a spread expression is valid open-target syntax: `open *A` and `open A*` are rejected — use comma for multiple targets. Valid targets are names, argumentless dot-call paths like `Lib.Sub`, single-quoted string URLs, and inline blocks.

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

**Isolation:** opened libraries do not inherit the opener's scope. A library only sees the properties it defined itself.

**Ambiguity:** if two open sources both provide a property with the same name, KatLang raises an error. Define a local property with that name to shadow the ambiguity.

### Visibility

By default, properties are private — accessible within their own algorithm and its children, but not visible to outside callers who load or open the algorithm. Marking a property `public` makes it eligible for external exposure, but a property is exported only if it is self-contained. A nested property is not exported if it depends on parameters owned by an enclosing algorithm, including the pattern binders of a conditional branch. Properties defined inside a conditional branch are additionally unreachable by name from outside that branch — a conditional exposes no members of its branches — but inside the branch they follow the ordinary rules: a self-contained branch-local library, whether declared there, opened inline, or backed by `open 'url'`, exposes its public members to the branch body and to any body nested in it, and nowhere else.

```
# In a library algorithm:
public Area = r * r * Math.Pi
public Kind(0) = 'zero'
public Kind(x) = 'nonzero'   # visibility is family-level: every clause is public or none
Helper = Area / 2   # private — not visible to callers
```

Only `public` exported properties are exposed through `load` and `open`.

---

## Pitfalls

- **Numeric precision:** KatLang numbers are IEEE 754 Decimal128 — 34 significant decimal digits with a huge exponent range (about ±6144). Results needing more than 34 significant digits round to the nearest representable value, and arithmetic past the representable range saturates to `Infinity`/`-Infinity` rather than erroring.
- **No hidden rounding of math functions:** trig, logarithm, root, and power results carry full Decimal128 precision and are never snapped toward "nice" values. `Math.Pi` is π rounded to 34 digits, so `Math.Sin(Math.Pi)` is the tiny residual of that rounding (about `-1.158e-34`), not `0` — compare against a tolerance when testing near-zero trig identities. Irrational results such as `Math.Sin(1)` are approximations at 34 digits, correct to roughly the last digit or two.
- **IEEE special values:** `NaN`, `Infinity`, `-Infinity`, and `-0` are ordinary numeric values (from domain violations like `Math.Sqrt(-1)`, overflow, or writing `-0`). Ordering comparisons involving `NaN` are always false, while `==`/`!=` use structural value identity (so `NaN == NaN` is `1`). Dividing by any zero-valued divisor (including `-0` and computed zeros) is still an error, not `Infinity`.
- **Parameter order surprises:** parameter order is determined by first appearance reading left to right. If your expression reads `b - a`, the first parameter is `b`, not `a`. Use Grace (`~`) to override when needed.
- **`if` arity:** builtin `if` requires three arguments after spread expansion: `if(cond, a, b)`. There is no two-argument form. A grouped value is one argument, so `if(X)` is invalid when `X = 1, 2, 3`; spread it with `if(X*)` to supply the three slots.
- **`()` vs `{}` confusion:** `(expr)` groups an expression in the current scope. `{expr}` creates a new algorithm with its own parameters. Passing `(a + 1)` as an argument doesn't create a callable — it evaluates `a + 1` immediately in the enclosing scope. Bare `()` is the empty sequence value (a real value); bare `{}` is a no-output body and is not a value. Declarations follow the same split: `open` and property definitions belong to `{ ... }` blocks (or the root) and are parse errors inside `( ... )`.
- **Ignoring a parameter:** there is no special "ignore" syntax for implicit parameters — every undeclared name becomes a required argument. If you want to accept and discard an argument, use an explicit parameter pattern. Bind the unwanted argument to a variable in the pattern, then simply don't reference it in the body:

  ```
  # Wrong — no way to declare 'b' to discard; calling with two args fails:
  KeepFirst = a
  KeepFirst(42, 999)  # error: too many arguments

  # Right — 'b' is bound by the explicit parameter pattern but never used:
  KeepFirst(a, b) = a
  KeepFirst(42, 999) # Result: 42
  ```
- **Property redefinition:** defining the same property name twice is an error — properties are immutable bindings, not reassignable variables:

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

  Use different literal values or different arities to distinguish branches:

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

  This is a host runtime limit, not a language rule: a program that finishes within the limit produces exactly the result it always did. Recursion deeper than the limit needs an iterative form — `repeat` or `while` — which repeats work without stacking up calls.

- **Loops still run as long as you ask:** there is no work budget by default, so `Step.while(...)` with a condition that never becomes false runs forever. Check your continuation slot. (Hosts embedding KatLang can configure a step budget to bound this.)

- **Collection size:** one sequence or list can hold up to 100,000 items. A request for more is rejected before anything is allocated, so an accidental extra zero costs you an error message rather than the whole process:

  ```
  range(1, 10000000)  # error: Collection size limit of 100000 items was exceeded; requested 10000000 items
  ```

  This counts the items of a single collection, so nesting is fine — `[[1, 2], [3, 4]]` is three small collections, not one big one. Like the recursion limit it is a host runtime limit, not a language rule: results within the limit are exactly what they always were.

- **Displayed output size:** printing a value flattens it, and nesting a value inside itself doubles the printed text each time even though the value itself barely grows:

  ```
  Values = range(1, 200)
  L0 = [Values, Values]
  L1 = [L0, L0]
  # ... a few more lines and the printed form is megabytes

  ```

  Displayed output is capped at 1,000,000 characters. Past that, printing reports the limit instead of the text — never a silent half-answer. The value itself is unaffected: it evaluated fine, and a host embedding KatLang can still work with it structurally.
---

## Full Reference

### Operators

| Operator | Description | Precedence |
|---|---|---|
| `^` | Power (right-associative; binds tighter than the prefix operators on the left, so `-2 ^ 2` is `-(2 ^ 2)` and a negative base needs parentheses: `(-2) ^ 2`. The exponent side accepts a prefix operator directly: `2 ^ -2`) | Highest |
| `not` | Logical negation (prefix; between `^` and the multiplicative operators) | |
| `-` | Arithmetic negation (prefix; between `^` and the multiplicative operators) | |
| `*`, `/`, `div`, `mod` | Multiplication, division, integer division, modulo | |
| `+`, `-` | Addition, subtraction | |
| `<`, `>`, `<=`, `>=` | Ordering comparison, numeric scalar operands only (returns 1 or 0) | |
| `==`, `!=` | Structural value equality / inequality across all value kinds (numbers, strings, sequence values, and lists — different kinds compare unequal); returns 1 or 0 | |
| `and` | Logical and | |
| `xor` | Logical exclusive or | |
| `or` | Logical or | Lowest |
| `:` | Output selection (zero-based index over a sequence or exact list target, one-level content projection) | Postfix |
| `.` | Dot-call / property access | Postfix |
| `*` (prefix, directly attached) | Collect marker (binding positions only: `*name` collects the matched segment as one exact list) | — |
| `*` (postfix, directly attached) | Spread marker (`value*` contributes the operand's items to the surrounding supply; a `*` with a valid same-line right operand is multiplication instead) | — |
| `~` (prefix) | Grace: move parameter one position earlier | — |
| `~` (postfix) | Grace: move parameter one position later | — |
| `[` `]` | Exact immutable list literal (`[1, 2, 3]`; never a call or indexing delimiter — `A[1]` is the adjacency list `A, [1]`) | — |

### Builtin Algorithms, Intrinsics, and Keywords

The collection builtins below receive ONE collection argument plus fixed control arguments. The bound collection is viewed one level deep: a lone sequence value or exact list value opens into its immediate items, so `count(Values)`, `count((1, 2, 3))`, and `count([1, 2, 3])` all count three items; an atom or string is a one-element collection (`count(7)` is `1`); and nested sequence or list elements stay opaque items. Multi-item inline forms are arity errors (`count(1, 2, 3)` fails — `count(collection)` expects one argument), and spread supplies ordinary call arguments rather than feeding the collection parameter (`count(Values*)` fails; re-group as `count((Values*, 8))` or `sum((A*, B*))` when combining items into one collection). The collection-producing builtins (`range`, `filter`, `map`, `order`, `orderDesc`, `distinct`, `take`, `skip`, `atoms`) materialize their results as one exact immutable list value (`[]` for zero items, `[item]` for one). Dot-call supplies the receiver as the collection argument, for example `collection.take(2)`. Selection already projects one level of selected content, so `(A:0).count` follows the ordinary collection rules for the selected content without any extra builtin-specific expansion. Higher-order builtins such as `filter`, `map`, and `reduce` do not recursively flatten sequence-value elements beyond that.

For `repeat` and `while`, each explicit init argument becomes one initial state slot. `Step.repeat(3, a, b)` starts with two slots, while `Step.repeat(3, Pair)` starts with one slot even if `Pair` evaluates to multiple values. Use selections such as `Pair:0, Pair:1` or spread such as `Pair*` when you want a multi-output value to provide multiple initial slots; capture the step result as a sequence value when one structured slot should be preserved across iterations. A spread followed by a comma keeps its neighbor a separate slot, so `Step = history*, next` emits history's items followed by `next` as multiple next-state slots, while `Step = (history*, next)` captures them into one next-state slot. (The comma is required — `history* next` would be the multiplication `history * next`.)

A collecting step parameter follows the same collection rule as every other collecting binding: the fixed parameters bind state slots from the front and back, and the collecting parameter collects the matched middle slots as one exact list — including ZERO slots, so `Step(acc, *extras)` runs fine on a single-slot state with `extras = []`. Only the fixed parameters set the state-slot minimum. One receiver-specific exception applies to steps that use sequence-value parameter patterns (for example `Step((*history), previous)`): in such a patterned step's OUTPUT, a top-level spread expression contributes its combined value as ONE next-state slot instead of re-spreading into separate slots — the pattern-shaped step preserves structured state boundaries in both directions. Flat steps re-spread top-level output spread into separate state slots as described above.

| Keyword | Usage |
|---|---|
| `if` | `if(cond, a, b)` |
| `while` | `step.while(init1, init2, …)` or `while(step, init1, init2, …)` |
| `repeat` | `step.repeat(n, init1, init2, …)` or `repeat(step, n, init1, init2, …)` |
| `range` | `range(start, stop)` — inclusive integers ascending or descending, materialized as one exact list value |
| `filter` | `filter(collection, predicate)` or `collection.filter(predicate)` — keep top-level elements whose predicate result is truthy (non-zero); the predicate must return exactly one atomic numeric value, the callback item behaves like `S:i`, and the kept elements are returned unchanged as one exact list value (`[]` when nothing is kept) |
| `map` | `map(collection, mapper)` or `collection.map(mapper)` — transform top-level elements left to right; the callback item behaves like `S:i`, the mapper must return exactly one mapped element, and the mapped elements are returned as one exact list value |
| `order` | `order(collection)` or `collection.order` — eagerly sort top-level numeric elements ascending into one exact list value; duplicates are preserved and sequence-valued/string/list elements are invalid |
| `orderDesc` | `orderDesc(collection)` or `collection.orderDesc` — eagerly sort top-level numeric elements descending into one exact list value; duplicates are preserved and sequence-valued/string/list elements are invalid |
| `count` | `count(collection)` or `collection.count` — denotational top-level value count after evaluation, without flattening sequence values or lists |
| `contains` | `contains(collection, item)` or `collection.contains(item)` — return `1` when any extracted top-level element equals `item` under ordinary KatLang value semantics, otherwise `0`; sequence values stay intact and search is top-level only |
| `first` | `first(collection)` or `collection.first` — return the first top-level element unchanged; sequence values stay intact and the sequence must be non-empty |
| `last` | `last(collection)` or `collection.last` — return the last top-level element unchanged; sequence values stay intact and the sequence must be non-empty |
| `distinct` | `distinct(collection)` or `collection.distinct` — remove later duplicate top-level elements while preserving first-occurrence order; sequence values stay intact, duplicate detection follows KatLang value semantics, and the kept elements are returned as one exact list value (a single survivor is the one-element list `[item]`) |
| `take` | `take(collection, count)` or `collection.take(count)` — keep the first `count` top-level elements unchanged as one exact list value; non-positive counts return the empty list `[]`, sequence values stay intact as elements, and a single kept element is the one-element list `[item]` |
| `skip` | `skip(collection, count)` or `collection.skip(count)` — drop the first `count` top-level elements and return the rest as one exact list value; non-positive counts return all original items, sequence values stay intact as elements, and a single remaining element is the one-element list `[item]` |
| `min` | `min(collection)` or `collection.min` — find the smallest top-level numeric element; the sequence must be non-empty and sequence values are not flattened |
| `max` | `max(collection)` or `collection.max` — find the largest top-level numeric element; the sequence must be non-empty and sequence values are not flattened |
| `sum` | `sum(collection)` or `collection.sum` — add top-level numeric elements; each element must be a single atomic numeric value and sequence values are not flattened |
| `avg` | `avg(collection)` or `collection.avg` — average top-level numeric elements and return the decimal arithmetic mean (total divided by count); the sequence must be non-empty, each element must be a single atomic numeric value, and sequence values are not flattened |
| `reduce` | `reduce(collection, reducer, initial)` or `collection.reduce(reducer, initial)` — fold left over top-level elements; the current item behaves like `S:i`, normal accumulator parameters receive one structural state value, top-level collecting accumulator parameters receive state slots, and the reducer must return exactly one accumulator value |
| `atoms` | `atoms(value)` or `value.atoms` — recursively collect numeric atoms through both sequence and exact-list boundaries (left to right; strings contribute none) and return them as one exact immutable list |
| `string` | `value.string` — value intrinsic that converts an atomic numeric result to a first-class string value; non-numeric receivers (strings, sequence values) are errors |
| `load` | `Name = load('url')` — load external algorithm |
| `open` | `open target` — import public properties into scope |
| `public` | `public Prop = ...` or `public Prop(pattern) = ...` — expose property to callers |
| `Math` | Built-in namespace for constants and functions |
