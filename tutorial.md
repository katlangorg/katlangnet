# KatLang Tutorial

## Contents

1. [What KatLang Is](#what-katlang-is)
2. [Your First KatLang Program](#your-first-katlang-program)
   - [Comments](#comments)
3. [Values and Arithmetic](#values-and-arithmetic)
   - [Arithmetic Operators](#arithmetic-operators)
   - [Comparison Operators](#comparison-operators)
   - [Logical Operators](#logical-operators)
   - [Math Constants and Functions](#math-constants-and-functions)
   - [Display Decimal Places](#display-decimal-places)
4. [Multiple Outputs](#multiple-outputs)
5. [Properties](#properties)
   - [Calls Return One Value](#calls-return-one-value)
   - [Zero-Parameter Property Caching](#zero-parameter-property-caching)
   - [Implicit and Explicit Output](#implicit-and-explicit-output)
   - [The Empty Sequence Value](#the-empty-sequence-value)
    - [Sequence Values and Count](#sequence-values-and-count)
   - [Output Selection](#output-selection)
   - [Extension Dot-Call Syntax](#extension-dot-call-syntax)
   - [Name Resolution](#name-resolution)
6. [String Literals](#string-literals)
   - [String Equality](#string-equality)
   - [Number to String Conversion](#number-to-string-conversion)
7. [Parameters](#parameters)
   - [Variadic Explicit Parameters](#variadic-explicit-parameters)
   - [Reordering Parameters with Grace~ operator](#reordering-parameters-with-grace-operator)
8. [Conditionals](#conditionals)
9. [Repetition](#repetition)
    - [Inclusive Sequences: `range`](#inclusive-sequences-range)
    - [Selection: `filter`](#selection-filter)
    - [Mapping: `map`](#mapping-map)
    - [Sequence Inputs](#sequence-inputs)
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
10. [Practical Examples](#practical-examples)
    - [Reusable Calculation with Parameters](#reusable-calculation-with-parameters)
    - [Multi-Output Example](#multi-output-example)
    - [Loop-Based Example: Sum of a List](#loop-based-example-sum-of-a-list)
    - [Fibonacci Sequence](#fibonacci-sequence)
11. [Higher-Order Algorithms](#higher-order-algorithms)
    - [Algorithm as Argument](#algorithm-as-argument)
    - [Parametrized vs non-parametrized algorithms](#parametrized-vs-non-parametrized-algorithms)
12. [Spread with ellipsis operator](#spread-with-ellipsis-operator)
13. [Lists](#lists)
    - [Lists versus Sequence Values](#lists-versus-sequence-values)
    - [Spreading Lists](#spreading-lists)
    - [Lists in Calls and Deconstruction](#lists-in-calls-and-deconstruction)
    - [Lists and Collection Builtins](#lists-and-collection-builtins)
14. [Atoms](#atoms)
    - [Opening one level vs flattening](#opening-one-level-vs-flattening)
15. [Conditional Algorithms](#conditional-algorithms)
    - [Basic Pattern Matching](#basic-pattern-matching)
    - [Nested Sequence-Value Patterns](#nested-sequence-value-patterns)
    - [The K Combinator: Ignoring a Parameter](#the-k-combinator-ignoring-a-parameter)
    - [Mixing Literals and Variables](#mixing-literals-and-variables)
    - [String Patterns](#string-patterns)
    - [Non-Exhaustive Patterns](#non-exhaustive-patterns)
16. [Loading and `open`](#loading-and-open)
    - [Loading External Algorithms](#loading-external-algorithms)
    - [`open`: Import Properties Directly](#open-import-properties-directly)
    - [Visibility](#visibility)
17. [Pitfalls](#pitfalls)
18. [Full Reference](#full-reference)
    - [Operators](#operators)
    - [Builtin Algorithms, Intrinsics, and Keywords](#builtin-algorithms-intrinsics-and-keywords)

---

## What KatLang Is

KatLang is a language designed for calculations. You write expressions, give them names, and combine them — that's it.

One thing to know upfront: **everything is an algorithm**. A bare number like `42` is an algorithm that produces one value. An output sequence like `1, 2, 3` produces three values. A named formula is an algorithm that belongs to its parent. There are no statements or side effects — just algorithms that evaluate to sequences of values.

Most simple formulas do not need declared parameters — KatLang figures them out. Any name you use that isn't defined as a property automatically becomes a parameter unless the algorithm has an explicit parameter list.

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

Use `//` to add notes. Everything from `//` to the end of the line is ignored.

```
// Full-line comment
1 + 1  // inline comment
```

**Result:** `2`

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
3.3333333333333333333333333333
3
1
```

The `^` operator raises the left side to the power of the right side.

```
2 ^ 10
```

**Result:** `1024`

Operator precedence follows standard math rules: `^` binds tightest, then `*`, `/`, `div`, `mod`, then `+` and `-`. Parentheses override precedence.

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
Math.E
```

**Results:**
```
3.1415926535897932384626433833
2.7182818284590452353602874714
```

**Single-argument functions:**

| Function | Description |
|---|---|
| `Math.Abs(x)` | Absolute value |
| `Math.Ceil(x)` | Ceiling (round up) |
| `Math.Floor(x)` | Floor (round down) |
| `Math.Sign(x)` | Sign: -1, 0, or 1 |
| `Math.Sqrt(x)` | Square root |
| `Math.Ln(x)` | Natural logarithm |
| `Math.Lg(x)` | Base-10 logarithm |
| `Math.Sin(x)` | Sine (radians) |
| `Math.Cos(x)` | Cosine (radians) |
| `Math.Tan(x)` | Tangent (radians) |
| `Math.Asin(x)` | Arc sine |
| `Math.Acos(x)` | Arc cosine |
| `Math.Atan(x)` | Arc tangent |

**Two-argument functions:**

| Function | Description |
|---|---|
| `Math.Round(x, digits)` | Round to `digits` places after the decimal point |
| `Math.Pow(x, y)` | x raised to power y (floating-point) |
| `Math.Log(x, y)` | Logarithm of x with base y |
| `Math.Atan2(y, x)` | Arc tangent of `y / x`, in standard atan2 argument order (`y` first, then `x`) |
| `Math.Random(start, end)` | Decimal random number in `[start; end)`, so `start <= x < end` |
| `Math.RandomInt(start, end)` | Whole-number random value in `[start; end)`, so `start <= x < end` |

`Math.Random(start, end)` and `Math.RandomInt(start, end)` both produce a value in the half-open range `[start; end)`: `start` is inclusive, and `end` is exclusive. The result follows this rule:

```
start <= result < end
```

Use `Math.Random(0, 1)` for a decimal unit-interval value where `0 <= result < 1`. Use `Math.RandomInt(1, 7)` for an integer-like dice roll where the result is `1`, `2`, `3`, `4`, `5`, or `6`. `Math.RandomInt` requires whole-number bounds, but the returned KatLang number is still represented as a decimal value with no fractional part. Random generation always requires both bounds. `Math.Rand`, `Math.Rand()`, and `Math.RandInt` are not valid random-generation syntax.

Functions that compute via floating-point internally (trig, logarithm, square root, power) normalize their results to 15 significant digits, eliminating insignificant floating-point artifacts. For example, `Math.Sin(Math.Pi)` returns exactly `0` rather than a tiny residual like `1.22e-16`.

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

### Display Decimal Places

Define the top-level property `DisplayDecimals` to control how many digits after the decimal point are shown for decimal values in final displayed output:

```
DisplayDecimals = 6

Math.Pi
Math.E
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

(Math.Pi, Math.E)
```

**Results:**
```
(3.14, 2.72)
```

`DisplayDecimals` must be a single integer from 0 through 99. Negative values, fractional values, strings, and sequence-valued or multi-output values are reported as diagnostics.

Per-value formatting such as `value.displayDecimals(n)` and `displayDecimals(value, n)` is intentionally not part of this feature. Structured display settings such as `Display = { Decimals = n }` and `Display.Decimals = n` are also intentionally out of scope.

---

## Multiple Outputs

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

Add(1, 2)    // 3
Add (1, 2)   // the same call, 3
```

A physical newline never continues a closed expression into a call. A line that starts with `(` or `{` is its own output row, never call arguments for the previous line:

```
Add(a, b) = a + b

Add
(1, 2)       // not a call: expression-list slots `Add, (1, 2)`
```

For a multiline call, open the delimiter before the newline — an already-open argument list spans lines normally:

```
Add(a, b) = a + b

Add(
  1, 2
)            // the call Add(1, 2): 3
```

The same applies to dot calls and callback braces: `A.B (1)` is the dot call `A.B(1)` and `values.map { n * 2 }` is `values.map{n * 2}`, but `A.B` followed by `(1)` on the next line is the expression list `A.B, (1)`, and `values.map` followed by `{ n * 2 }` on the next line is not a callback call (write `values.map{` and break inside the braces instead). This is only about same-line whitespace between the callee and its delimiter — inside the argument list adjacency still creates argument slots, so `Add (1 2)` is the two-argument call `Add(1, 2)`. Comma and a newline both keep separate slots: `F, (1)` and `F` followed by `(1)` are expression-list structure. Non-callable targets never become calls: `2 (3)` stays the expression list `2, 3`.

Postfix indexing follows the same line rule: `Pair:0`, `Pair :0`, and `Pair : 0` all index on the same line, but a `:`-led line never continues the previous expression — it is a parse error rather than a silent continuation, so `P = Pair` followed by a line `:0` does not define `P = Pair:0`. Postfix grace `~` is same-line only in the same way: `A~B` graces `A`, while `A` followed by a line `~B` keeps `A` ungraced and parses `~B` as its own prefix-grace row. Binary operators follow the rule too: an operator-led line never continues the previous expression, so `A` followed by a line `-1` is the expression list `A, -1`, never the subtraction `A - 1` — put the operator at the end of the line (`A -` then `1` on the next line) when you want the arithmetic to continue. Comments never change any of these decisions: `A // note` followed by `-1` parses exactly like `A` followed by `-1`. Leading-dot lines are the one intentionally supported continuation: a line starting with `.` continues the dot-call chain, so method-chain layout works as long as each argument delimiter stays on the same line as its member name:

```
(1, 2, 3)
.map { n * 2 }
.sum         // 12
```

The newline boundary keeps definition boundaries predictable: a `(`- or `{`-led line after a definition body is a following output row, never call arguments appended to that body:

```
Sum(vector...) = vector.sum
(1, 2).Sum         // separate report row: 3
```

A leading semicolon after a definition body is invalid and produces a diagnostic. During error recovery the parser may still attach the following expression to the current body so later diagnostics stay useful, but that recovery is not valid KatLang syntax — semicolon is never an expression operator. When a definition and its result read better together, `Output = ...` states the result explicitly:

```
Sum(vector...) = vector.sum
Output = (1, 2).Sum     // 3
```

Comma is the explicit expression-list separator. Where an expression list is already open, same-line adjacency acts as an implicit comma, so `a b` means `a, b`. A newline is a different mechanism — a body, statement, or output boundary, not a global implicit comma — so it does not extend an expression list across lines unless the syntax explicitly keeps the context open (for example an open `(`/`{`, a trailing comma, a same-line binary operator, or a leading `.`). The `...` operator token itself is line-bound and postfix-only: it must appear on the same physical line as the expression it follows, and it never consumes a right operand — any token after `...` starts a new expression-list slot.

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

**Comma vs. parentheses vs. ellipsis:** these serve different purposes.

| Syntax | Meaning |
|---|---|
| `1, 2` | Two top-level comma outputs |
| `(1, 2)` | One sequence value containing `1` followed by `2` |
| `1 2` | Implicit expression-list separator by adjacency: exactly `1, 2` |
| `1...` | Postfix spread: open one item boundary of the evaluated value and contribute the items to the surrounding slot context |
| `1...2` | Postfix spread then an adjacent expression-list slot: `1..., 2` — `...` takes no right operand |

Comma and adjacency create expression lists. Root output consumes a bare expression list as output slots, call syntax consumes it as argument slots, parentheses materialize it as one sequence value, and square brackets materialize it as one exact [list value](#lists). Semicolon is not an expression separator; use comma/adjacency for separate slots or parentheses for one sequence value. Postfix `...` applies only to its immediate operand: `A B... C` is the expression list `A, B..., C`. Comma and adjacency slots stay structural (`F(a..., b)` and `F(a...b)` are both two-argument calls). Physical line breaks do not create sequence-value boundaries. Explicit parentheses do:

```
1, (2, 3)    // two slots: 1 and (2, 3)
(1, 2), 3    // two slots: (1, 2) and 3
(1, 2, 3)    // one sequence value
(1, 2, 3)    // (1, 2, 3)
```

Comma creates multiple top-level output slots; parentheses create one sequence-valued slot. The result window may show comma slots on separate rows, while sequence values display as sequence values. `EvaluateToString()` is a separate convenience stringification path that extracts atoms and joins them with spaces. See [Spread with `...`](#spread-with-ellipsis-operator).

Postfix `x...` is only the spread of `x` followed by nothing; it does not mean “continue this expression on the next line.” The `...` operator itself must appear on the same physical line as the expression it follows, and it never consumes a right operand: a token after the dots — tight, spaced, or on the next line — starts a new expression-list slot, so `x...y` is `x..., y`. Use parentheses, such as `(x..., y)`, when the spread value and the following expression should form one sequence value.

Flat fixed calls preserve expression boundaries. A property reference used as one argument is one argument expression, even if that property evaluates to multiple outputs. KatLang does not implicitly unpack one argument expression to satisfy additional fixed parameters; use separate arguments, explicit indexing/projection, or `...` spread where that is the intended shape.

```
Pair = 10, 20
Add(x, y) = x + y

Add(Pair)           // bad arity: one argument expression
Add(Pair:0, Pair:1) // 30

Tail = 2, 3
Use(a, b, c) = a + b + c

Use(1, Tail)    // bad arity: two argument boundaries
Use(1, Tail...) // 6: Tail... spreads its items into the b and c slots
Use(1...Tail)   // bad arity: 1...Tail is 1..., Tail — spreading the scalar 1 yields one item, so only two argument slots
```

---

## Properties

An algorithm can be given a name using `=`. Named algorithms are called **properties**, because a named algorithm always belongs to its parent algorithm. By convention, property names use PascalCase.

<!-- spec:property-access-and-call -->
```
// Define a property:
Answer = 42

// Property-style access:
Answer

// Explicit zero-parameter call:
Answer()
```

**Results:**
```
42
42
```

### Calls Return One Value

A property/call boundary is a **value boundary**: it always returns exactly one value. A body may internally produce an item supply — comma slots, adjacency, or a body spread — but when you *call* it (or access a property, or invoke a builtin), the caller receives a single value. If the body produced several items, that value is a sequence containing them. To open it back into the surrounding item supply, use postfix `...` at the call site. This is analogous to Python, where `return 1, 2, 3` returns one tuple, not three independent results.

<!-- spec:call-value-boundary -->
```
F(a...) = a
F(5, 9)
F(5, 9)...
```

**Results:**
```
(5, 9)

5
9
```

The body's internal shape is preserved inside the returned value — only the boundary count changes. `F(a...) = a, 0` returns `((5, 9), 0)` (the capture stays grouped as a nested value), while `F(a...) = a..., 0` returns `(5, 9, 0)` (the body spread flattens first). Either way the call returns **one** value; spread at the call site is the only way to re-open it.

The same rule governs collection-producing builtins. `order`, `orderDesc`, `distinct`, `take`, `skip`, `filter`, `map`, `range`, and `atoms` each return one sequence value; postfix `...` opens it:

```
X = 1, 2, 3
X.order
X.order...
```

**Results:**
```
(1, 2, 3)

1
2
3
```

Three things are intentionally **not** value boundaries and keep emitting multiple top-level items: root program output (`1, 2, 3` still shows three rows), explicit caller-site spread (the whole point of `...`), and the multi-slot loop state of `while`/`repeat`. Scalar/reduction builtins (`count`, `sum`, `avg`, `min`, `max`, `contains`, `first`, `last`, `reduce`) already return one value and are unchanged. A `map`/`reduce` callback must still return exactly one element; a multi-output callback body is an error, not a silently-grouped value.

### Zero-Parameter Property Caching

For pure calculations these forms produce the same visible value, but the call shape controls reuse. A zero-parameter property read without parentheses may reuse a cached result during the current evaluation:

```
Fun = 1 + 2
Fun, Fun
```

When the property produces values that can change, property-style access and explicit calls are different:

```
Fun = Math.Random(0, 1), Math.Random(0, 1)

Fun, Fun     // property-style access: the same pair may be reused
Fun(), Fun() // explicit calls: the body is evaluated again for each call
```

`Fun()` bypasses the zero-argument cache for `Fun` itself. It does not recursively force property-style references inside `Fun` to bypass their own caches. To request fresh nested values, write those nested calls explicitly with `()`:

```
A = Math.RandomInt(0, 10)

B = A, A        // uses cached/property-style A access
C = A(), A()    // explicitly asks for fresh A values

B()             // re-evaluates B, but A remains cached inside B
C()             // re-evaluates C, and A() is fresh because it is explicit
```

A property body may produce several items, but property-style access is a value boundary: the caller observes them as one sequence value. Caller-site spread `...` re-opens that value into separate output rows:

<!-- spec:property-value-boundary -->
```
Coordinates = 10, 20
Coordinates
Coordinates...
```

**Results:**
```
(10, 20)

10
20
```

### Implicit and Explicit Output

An algorithm may define output in one of two ways, and it may also define no output at all.

**Implicit output (preferred):** any expression that appears after all property definitions becomes the algorithm's output. This is the concise, idiomatic style.

```
A = 3
B = 2
A + B
```

**Result:** `5`

Here `A` and `B` are property definitions; the trailing `A + B` is the implicit output.

**Explicit output:** you can instead write `Output = expression` to declare the output anywhere in the algorithm body — even before some property definitions. This can improve readability when the property list is long.

```
A = 3
Output = A + B
B = 2
```

**Result:** `5`

`Output = expr` is reserved syntax, not a regular property assignment. An algorithm may use it at most once, and you cannot mix it with implicit output in the same algorithm — in either direction: an expression row before `Output = ...` and an expression row after it both report the mixing error. Like every definition body, the `Output = ...` body is line-bounded: a newline ends it, so write sequence-valued explicit output with parentheses, for example `Output = (A, B)`. `Output = A` followed by `B` on a later line — indented or not — is the mixing error (the body ended at the newline and `B` is a separate output row), not a sequence-valued output. The name `Output` is reserved in definition position: `Output(x) = ...` and multi-branch `Output` definitions are invalid. If you need explicit parameters or clause branches, declare them on the enclosing algorithm instead. If you declare explicit parameters on the enclosing algorithm, that algorithm must define output. External qualified access is also invalid: `Algo.Output` and `Algo.Output(...)` are rejected because `Output` is not a public property surface.

When an algorithm is used in call position, KatLang calls the algorithm using its own parameter list. Put the call interface on the algorithm head, and use `Output = ...` only to declare its result:

```
Algo(x) = {
    Output = x + 1
}

Algo(6)
```

This produces `7`. Conditional branches follow the same rule: declare them on the enclosing algorithm head, not on `Output`. To get an algorithm's designated result, call the algorithm directly; do not write `Algo.Output(...)`. Bare `Algo` still refers to the algorithm value, not an automatic call. Self-contained helper properties remain accessible through dot syntax, for example `Algo.Helper(6)`. If a nested property depends on parameters owned by the enclosing algorithm, or is defined inside a conditional algorithm branch, it is local-only and cannot be accessed as `Algo.Helper` or exported through `open`/`load`.

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
()       // the empty sequence
(())     // canonicalizes to ()
((()))   // canonicalizes to ()
```

They stay equal after parsing, assignment, display, and equality:

<!-- spec:empty-eq-family -->
```
() == ()      // 1
() == (())    // 1
() != (())    // 0
count(())     // 0
count((()))   // 0
```

#### `()` versus a no-output body

`()` is a value. A no-output body is not a value at all: empty braces `{}` are an empty parametrized body with no defined output.

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

A normal output expression that evaluates to `()` is still a visible output slot. Only spreading an empty sequence with `...` contributes zero items:

```
x, rest... = 1
rest
```

**Result:** `()`

```
x, rest... = 1
rest
x
```

**Result:**
```
()
1
```

```
x, rest... = 1
rest...
x
```

**Result:** `1`

The empty sequence value also appears naturally as a sequence result:

```
IsEven = x mod 2 == 0
filter(1, 3, 5, IsEven) == ()
```

**Result:** `1`

### Sequence Values and Count

Use `.count` (or `count(...)`) to ask how many items an expression contributes once the builtin's collection binding opens sequence values: a single grouped sequence value is opened by singleton-boundary normalization, so its immediate items are counted.

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

Sequence values are consumed by sequence builtins through builtin-owned item-supply binding. Named helpers such as `A = 1, 2, 3` followed by `count(A)`, `A.count`, `count(1, 2, 3)`, and `count(A...)` all return `3` — a single grouped value is opened by singleton-boundary normalization for the builtin collection, and an explicit spread joins the same supply. A sequence-valued helper such as `T = (1, 2, 3)` is opened the same way, so `count(T)` and `T.count` return `3`. User-defined function calls are different: they preserve argument boundaries unless `...` is written. See `count` below for the full sequence-input rules.

### Output Selection

When an algorithm produces multiple outputs, the `:` operator selects one top-level item by its zero-based index and projects that selected item's content one level.

Construction preserves structure; selection projects content.

- If the selected item is atomic, the result is that atomic value.
- If the selected item is a sequence value, the result is its immediate top-level members.
- Nested sequence values stay intact; `:` does not recursively flatten them.
- Chained selection repeats the same one-level projection step at each `:`.

```
Nums = 10, 20, 30, 40, 50

// Select the third value (index 2):
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

Output selection is especially useful with loops and multi-output algorithms where you only need one particular result.

### Extension Dot-Call Syntax

A property call can be written with dot notation, placing the first argument before the dot. The two forms below are equivalent:

```
Square = n * n

// Standard call:
Square(5)

// Extension (dot-call) syntax:
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

Add(3, 7)      // 10
(3).Add(7)     // 10
(3, 7).Add     // error: receiver stays one argument
```

Use direct multi-argument syntax, or put one scalar receiver before the dot and the remaining arguments after the property name, when a user-defined algorithm expects several fixed parameters.

As an invariant, `A.B(C, D)` means `B(A, C, D)` for ordinary properties, not a call where `A`'s top-level values are spread before `C` and `D`.

A parameter list with two or more parameters that contains a rest parameter (postfix ellipsis) is a **deconstruction pattern**. The fixed parameters bind from the front and the back, and the rest parameter captures the remaining middle items as one grouped sequence value:

```
Arg = 1, 2, 3
Scale(values..., factor) = values.map{n * factor}

Scale(Arg, 10)
Arg.Scale(10)
Scale(Arg..., 10)
Scale(1, 2, 3, 10)
```

**Results:**
```
(10, 20, 30)
(10, 20, 30)
(10, 20, 30)
(10, 20, 30)
```

All four call forms agree. Each call is a value boundary (see [Calls Return One Value](#calls-return-one-value)): the mapped items are observed as the one sequence value `(10, 20, 30)`, and caller-site spread such as `Scale(Arg, 10)...` opens it into the flat items `10`, `20`, `30`. `factor` binds `10` from the back and `values...` captures the front items: `Scale(Arg, 10)` supplies `Arg` as one front item, captured as `values = Arg = (1, 2, 3)` (a singleton capture collapses to the captured value), while `Scale(Arg..., 10)` and `Scale(1, 2, 3, 10)` supply three front items, captured as the same `values = (1, 2, 3)`. The plain argument is not opened during binding; it just happens to display the same captured value here. A lone rest-only parameter such as `Helper(values...)` is the degenerate single-rest case of the same item-supply binding (see [Variadic Explicit Parameters](#variadic-explicit-parameters)).

**Resolution rule:** KatLang first checks whether the property name exists as a structural property of the target algorithm. If found, it calls that property. If not found, it falls back to lexical lookup in the current scope — this is how extension-style calls work.

### Name Resolution

Name resolution is especially important in KatLang because it may behave differently from what users expect from other languages. KatLang uses a fixed search order called **ownership-first lookup**. The idea is simple: a name belongs first to the algorithm that owns it, then to its parent structure, and only after that to anything brought in through `open`.

When KatLang sees a name, it checks these places in order and stops at the first match:

1. **Local properties** — properties defined in the current algorithm (any visibility).
2. **Parent chain** — properties defined in enclosing algorithms, walking upward through the nesting structure. In this step, KatLang checks only structural properties; parent-level opens are not considered yet.
3. **Opens** — public properties from `open` targets, checked for the current algorithm first and then upward through the parent chain.

If the name is not found at any of these levels, KatLang treats it as an implicit parameter only when the current algorithm has no explicit parameter list (see [Parameters](#parameters)). Explicit parameter lists are closed, so an unresolved extra name is reported as an error instead.

```
X = 1
Inner = {
    Y = 2
    // X is found at level 2 (parent chain)
    // Y is found at level 1 (local)
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
// X resolves to the local property, not to Lib.X:
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

**Rule:** in an algorithm without an explicit parameter list, any identifier that is not defined as a property in the current algorithm becomes an implicit parameter.

Parameters are named in camelCase by convention to distinguish them from PascalCase property names.

```
// 'x' is not defined as a property → it becomes a parameter
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
// 'a' appears first, then 'b'
Sub = a - b

Sub(10, 3)
```

**Result:** `7`

Multiple parameters follow the same rule:

```
// Three parameters in order of appearance: a, b, c
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
// error: y is not part of the closed explicit parameter list
```

### Variadic Explicit Parameters

KatLang supports recursive parameter patterns in ordinary algorithm definitions and conditional branch heads. A sequence-value pattern consumes one parent-level argument slot and matches that slot's immediate contents.

```
PairSum((x, y)) = x + y
PairSum((2, 3))
```

**Result:** `5`

A top-level variadic parameter (`name...`) instead consumes an **item supply**: it binds the supplied top-level items as one grouped sequence value. A lone rest parameter is the degenerate case — it captures the whole supply:

<!-- spec:variadic-grouped-and-spread -->
```
A = 1, 2, 3, 4, 5

G(x...) = x.sum

G(A)
G(A...)
G(1, 2, 3, 4, 5)
G((1, 2, 3, 4, 5))
```

**Results:**
```
15
15
15
15
```

All four forms display `x = (1, 2, 3, 4, 5)` for this rest-only function, but they do not supply the same argument stream. `G(A)` and `G((1, 2, 3, 4, 5))` each supply one sequence-valued argument; `G(A...)` and `G(1, 2, 3, 4, 5)` supply five arguments. Mixed fixed/rest parameter shapes make that boundary difference observable. An empty call `G()` binds the empty stream, so `x = ()`.

Multiple sibling sequence values are **not** auto-flattened — they are preserved unless you open them explicitly with `...`. With `A = 1, 2` and `B = 3, 4`, `G(A, B)` binds `x = ((1, 2), (3, 4))` (count 2), while `G(A..., B...)` binds `x = (1, 2, 3, 4)` (count 4):

<!-- spec:variadic-siblings-preserved -->
```
A = 1, 2
B = 3, 4

G(x...) = x.count

G(A, B)
G(A..., B...)
```

**Results:**
```
2
4
```

Ordinary (non-variadic) parameters still preserve one argument boundary:

```
Arg = 1, 2, 3

Collect(list) = list
CollectMany(list...) = list

Arg.Collect.count
Arg.CollectMany.count
```

**Results:**
```
3
3
```

When a parameter list has two or more parameters and one of them is a rest parameter, the list is a **deconstruction pattern**: the rest parameter may appear at the front, middle, or end. Fixed parameters before it bind from the front, fixed parameters after it bind from the back, and the rest parameter captures the remaining middle items (possibly zero) as one grouped sequence value. The supplied items are the call argument slots: a bare argument supplies one slot (a stored sequence value is one slot, not opened), and only an explicit `...` spreads a sequence value into separate slots:

<!-- spec:mixed-front-back-family -->
```
Arg = 1, 2, 3

Head(first, rest...) = first
Tail(first, rest...) = rest
Init(init..., last) = init
Last(init..., last) = last

Head(1, (2, 3))
Tail(1, (2, 3))
Init((1, 2), 3)
Last(Arg, 3)
```

**Results:**
```
1
(2, 3)
(1, 2)
3
```

A parameter list with two or more captures and one rest matches the supplied item supply prefix/rest/suffix. With `F(x, y..., z) = x + y.sum + z` and `A = 1, 2, 3, 4, 5`, `F(A)` supplies one argument and fails because `x` and `z` need two fixed arguments. `F(A...)` and `F(1, 2, 3, 4, 5)` bind `x = 1`, `y = (2, 3, 4)`, `z = 5` and return `15`; `F(1, 2)` binds `x = 1`, `y = ()`, `z = 2` (the rest captures zero items) and returns `3`.

#### Deconstruction Assignment

The same comma binding pattern works on the left of `=`, binding several names from one right-hand side. Assignment deconstruction is an **unpacking receiver**, like Python's `x, y = pair`: when the right-hand side is exactly one sequence value or one exact [list value](#lists), the pattern opens that lone value and matches its items to the targets. At most one rest binding `name...` is allowed, and it may appear anywhere in the pattern:

<!-- spec:decon-tutorial-full -->
```
A = 1, 2, 3, 4, 5

x, y..., z = A
x
y
z
```

**Results:**
```
1
(2, 3, 4)
5
```

The pattern unpacks the single stored sequence value `A`, so `x, y..., z = A` splits `A` into its items: `x = 1`, `y = (2, 3, 4)`, `z = 5`. Explicit `x, y..., z = A...` supplies the same items, and a direct item supply `x, y..., z = 1, 2, 3, 4, 5` binds the same way. Fixed targets bind from the start and end; the rest target captures the middle. `head..., last = 1, 2, 3` binds `head = (1, 2)` and `last = 3`; `first, tail... = 1, 2, 3` binds `first = 1` and `tail = (2, 3)`; `x, y..., z = 1, 2` binds `y = ()`. With a single fixed target plus a rest, `first, rest... = A` unpacks `A` into `first = 1` and `rest = (2, 3, 4, 5)` — the same as `first, rest... = A...`. Without a rest the item count must match exactly, so `x, y = 1, 2` binds `x = 1` and `y = 2`, while `x, y = 1` (one item) and `x, y = 1, 2, 3` (three items) are arity errors against the two targets. This unpacking is deconstruction-specific: a function call `F(A)` still passes `A` as one argument, so calls need `F(A...)` to open it. A deconstruction pattern needs at least two comma-separated targets, so a single rest target such as `all... = 1, 2, 3` is not a valid assignment form — rest-only item-supply binding belongs to function parameters such as `Sum(values...)`, not to assignment. More than one rest binding (`a..., b... = 1, 2, 3`) is also rejected.

Variadic capture is not recursive flattening. A captured sequence value keeps its nested sequence values as top-level items (here `Many(Arg)` supplies the one value `Arg`, so `values` is `Arg` and its count is its two top-level items, not the four atoms):

```
Arg = (1, 2), (3, 4)

Many(values...) = values.count
Flattened = atoms(Arg).count

Many(Arg)
Flattened
```

**Results:**
```
2
4
```

Use sequence-value parameter patterns when one fixed argument slot should be opened during binding. This is different from a top-level `name...`: the sequence-value pattern consumes exactly one argument slot, requires that slot to be a sequence value, and binds only that sequence value's immediate contents.

```
SequenceValueCount((values...)) = values.count
SequenceValueCount((1, 2, 3))
```

**Result:** `3`

These two forms bind at different pattern levels. The top-level `values...` consumes an item supply, while the sequence-value pattern `(values...)` consumes one grouped value:

```
CountValues(values...) = values.count
CountSequenceValue((values...)) = values.count

CountValues()
CountValues(1, 2, 3)
CountValues((1, 2, 3))
CountSequenceValue((1, 2, 3))
```

**Results:**
```
0
3
3
3
```

In `CountValues`, top-level `values...` captures the call's item supply: `CountValues()` binds the empty supply (count `0`), `CountValues(1, 2, 3)` binds the three slots as `values = (1, 2, 3)` (count `3`), and `CountValues((1, 2, 3))` supplies one sequence-valued argument whose visible value also counts as `3`. In `CountSequenceValue`, the outer sequence-value pattern consumes one parent-level argument slot, then `values...` captures that sequence value's immediate contents. The builtin `count(values...)` has builtin-owned collection binding, so `count(Values)`, `count(1, 2, 3)`, and `count(Values...)` all agree; fixed/non-rest user calls still preserve their exact call shape.

Redundant unary parentheses at the call site never change the items a sequence-value capture binds — redundant unary sequence structure is canonicalized during value construction, so extra grouping around a single value does not add an observable sequence-value level:

```
Inner = (1, 2, 3)
CountSequenceValue((values...)) = values.count
NestedCount(((values...))) = values.count

CountSequenceValue(Inner)
CountSequenceValue((Inner))
CountSequenceValue(((1, 2, 3)))
NestedCount(((1, 2, 3)))
NestedCount((((1, 2, 3))))
```

**Results:**
```
3
3
3
3
3
```

All five calls bind the same three items. Two distinctions remain observable. First, a nested pattern still needs at least its explicit sequence-value level: `NestedCount((1, 2, 3))` is an arity error, because the pattern expects one nested sequence-value argument but the opened items supply three. Second, non-unary structure is preserved: `CountSequenceValue(((1, 2), 3))` reports `2`, because the sequence value's items are `(1, 2)` and `3`.

Destructuring is recursive by syntax, but each sequence-value pattern opens only one value boundary. A variadic capture consumes siblings only at its own pattern level:

```
Window((first, middle..., last), scale) = first * scale, middle.count, last * scale
Window((1, 2, 3, 4), 10)
```

**Result:** `(10, 2, 40)`

The top-level argument structure still matters. These two signatures accept different call shapes:

```
FlatState((history..., previous), current) = history.count, previous, current
NestedState(((history..., previous), current)) = history.count, previous, current

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
FirstSequenceValue((values...)) = values:0
FirstSequenceValue(((1, 2), 3))
```

**Result:** `(1, 2)`

This is useful for loop state where an accumulated history should remain one state slot while helper values sit beside it:

```
Step((history...), previous) = (history..., previous + 1), previous + 1
Step.repeat(2, (1, 2), 2):0
```

**Result:** `(1, 2, 3, 4)`

`(history...)` opens the single sequence-value state slot and binds `history` to its items as one grouped sequence value. Inside `(history..., previous + 1)`, postfix `history...` opens that one sequence-value boundary into its immediate items (see [Opening one level vs flattening](#opening-one-level-vs-flattening)), so each step rebuilds one flat accumulator sequence value beside the new value: `(1, 2)` → `(1, 2, 3)` → `(1, 2, 3, 4)`. The accumulator grows flat while remaining a single state slot beside `previous + 1`. Postfix `...` still never consumes a right operand — the comma is what places `previous + 1` beside the spread history items.

Only one variadic capture is allowed in each comma-separated pattern level, variadic captures must be explicit, and they cannot use the Grace `~` reordering operator. `Output(values...) = ...` is invalid; declare explicit parameters on the enclosing algorithm or property head instead.

### Reordering Parameters with Grace~ operator

Sometimes the natural reading order of parameters in a definition does not match the intended calling convention. The Grace`~` operator shifts a parameter's position.

Prefix `~x` moves `x` one position earlier in the parameter list. Postfix `x~` moves `x` one position later.

```
// Without Grace, parameter order would be (y, x) since 'y' appears first.
// ~x moves x one position earlier → call order: (x, y)
Divide = y / ~x

Divide(2, 10)
```

**Result:** `5`

---

## Conditionals

`if` is a builtin algorithm with exactly three argument slots: `if(condition, whenTrue, whenFalse)`. Usually you pass the three arguments directly. There is no two-argument form. A grouped value used without spread is still one argument, so `if(X)` is invalid when `X = 1, 2, 3`; explicit spread in call-argument position opens one value across the three slots, so `if(X...)` works (the arguments are counted after spread expansion).

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
// Return 1 if n is divisible by 3, 0 otherwise
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

`if(condition, whenTrue, whenFalse)` evaluates only the selected branch and returns that branch as **one value**. This is just the general [call value boundary](#calls-return-one-value) applied to `if`: if the selected branch is a multi-output property such as `X = 1, 2, 3`, the `if` result is the grouped sequence value `(1, 2, 3)` — the same single value you observe by referencing `X` directly. Use the spread operator, for example `if(1, X, X)...`, to open it into separate output slots:

```
X = 1, 2, 3
if(1, X, X)
if(1, X, X)...
```

**Results:**
```
(1, 2, 3)

1
2
3
```

Explicit spread also works in **call-argument position**. Spreading a three-item value into the call opens it across the three argument slots, so `if(X...)` is equivalent to `if(1, 2, 3)` and selects the `whenTrue` branch:

```
X = 1, 2, 3
if(X...)
```

**Result:**
```
2
```

This makes a direct `if(X...)` behave the same as a user-defined wrapper such as `MyIF(a, b, c) = if(a, b, c)` called as `MyIF(X...)`. A spread that does not expand to three values is an evaluation-time arity error, just like any other builtin.

---

## Repetition

### Inclusive Sequences: `range`

`range(start, stop)` is a builtin algorithm that returns every integer from `start` to `stop`, inclusive.

- If `start < stop`, it counts upward by `1`
- If `start > stop`, it counts downward by `1`
- If `start == stop`, it returns a single value
- Both arguments must be integers

```
range(1, 5)
range(5, 1)
range(3, 3)
```

**Results:**
```
(1, 2, 3, 4, 5)

(5, 4, 3, 2, 1)

3
```

A `range` call is a value boundary: each bare call is one sequence value (`range(3, 3)` is the single value `3`). Use caller-site spread `...` to open it into an item supply — for example to feed the integers into another call:

```
range(1, 3)
range(1, 3)...
sum(range(1, 3)...)
```

**Results:**
```
(1, 2, 3)

1
2
3

6
```

### Selection: `filter`

`filter(values..., predicate)` walks the sequence from left to right and keeps only the top-level elements whose predicate result is exactly one atomic numeric value.

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
(2, 4, 6)

(4, 5)

((2, 20), (4, 40))
```

`filter` is a value boundary: the bare call returns one sequence value. Open the kept items with caller-site spread:

```
IsBig = x > 1
X = 1, 2, 3
X.filter(IsBig)
X.filter(IsBig)...
```

**Results:**
```
(2, 3)

2
3
```

If every predicate result is `0`, `filter` returns an empty collection.
Predicate results such as `0, 999`, `(1, 0)`, or `x.string` are invalid because `filter` does not derive truth from sequence-valued or multi-output results.
The same callback rule applies everywhere, but parentheses shape the collection before binding. `filter((1, 2), predicate)` and a helper `Values = (1, 2)` followed by `filter(Values, predicate)` each call `predicate` once for each item in that sequence value. Calls such as `filter(range(1, 5), predicate)`, `P = range(1, 5)` followed by `filter(P, predicate)`, and `filter((range(1, 5)..., 8), predicate)` call `predicate` once per immediate sequence item. Use spread only when opening a value produces the structural slot count the callable expects.

### Mapping: `map`

`map(values..., mapper)` walks the sequence from left to right and replaces each top-level element with `mapper(element)`.

- The mapper's current item behaves like `S:i` for the traversed sequence `S`
- Sequence-value current items expose their immediate members; nested sequence values stay intact
- The mapper must return exactly one mapped element
- One atomic value is valid
- One sequence value such as `(x, x * x)` is also valid
- Empty or multi-output mapper results are errors
- Output order and element count are preserved

Both call styles are supported: `map(values..., mapper)` and `collection.map(mapper)`.

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
(2, 4, 6)

(1, 4, 9, 16, 25)

((1, 1), (2, 4), (3, 9))
```

`map` is a value boundary: the bare call returns one sequence value. Open the mapped items with caller-site spread:

```
Double = x * 2
X = 1, 2, 3
X.map(Double)
X.map(Double)...
```

**Results:**
```
(2, 4, 6)

2
4
6
```

Because sequence-value callback items are projected one level, write `Swap(a, b) = (b, a)` when mapping over sequence-value pairs.
With that rule, `map(((1, 2), (3, 4)), Swap)` calls `Swap` once per pair and produces the sequence value `((2, 1), (4, 3))` (append `...` to open the mapped pairs into an item supply). A single sequence-value argument such as `Values = (1, 2)` followed by `map(Values, Swap)` is opened by singleton-boundary normalization into the two atom items `1` and `2`, so the mapper runs once per atom — a two-parameter callback like `Swap` then fails with an arity error. Use a one-parameter callback for atom items, and reserve `Swap(a, b)` for collections whose items are pairs, as in `map(((1, 2), (3, 4)), Swap)`. A grouped sequence value is one valid way to provide the item supply to a rest-shaped builtin — it is opened by singleton-boundary normalization: `map(range(1, 5), Double)`, `Values = 1, 2, 3` followed by `map(Values, Double)`, and `map((1, range(2, 4)...), Double)` run once per immediate sequence item.

### Sequence Inputs

`filter`, `map`, `order`, `orderDesc`, `count`, `contains`, `first`, `last`, `distinct`, `take`, `skip`, `min`, `max`, `sum`, `avg`, and `reduce` all expose a rest-shaped `values...` signature and consume a builtin-owned **item supply**. The prefix/rest/suffix matching is shared with user-defined variadics, but a rest-shaped builtin additionally opens a single grouped value (singleton-boundary normalization, below) — something a user-variadic call does not do (a user call keeps a single sequence argument as one argument unless `...` is written). Any suffix parameters (such as the `count` of `take`/`skip` or the `item` of `contains`) bind from the back.

- Each comma argument is one item in the supply. If `Values = 1, 2, 3`, then `count(Values)`, `Values.count`, `count(1, 2, 3)`, and `count(Values...)` are all `3` (`Values` is opened by singleton-boundary normalization, and the spread joins the same supply). If `P = range(1, 5)`, then `count(P)` and `P.count` are `5`.
- Suffix parameters bind as separate structural slots. `take((1, 2, 3), 2)` binds `values = (1, 2, 3)` and `count = 2`; `map(values..., mapper)`, `filter(values..., predicate)`, and `reduce(values..., reducer, initial)` bind their callback or accumulator arguments from the suffix.
- Spread `...` explicitly opens evaluated content before binding and joins the item supply. With `Values = 10, 20`, `sum(Values)` and `sum(Values...)` are both `30` (here `sum` is a builtin, which opens the single grouped `Values`). Once items are in the supply, every rest-shaped signature matches them the same way — user variadics such as `values...` and `x, y..., z`, and rest-shaped builtins such as `sum(values...)` and `contains(values..., item)` — by prefix/rest/suffix. The difference is upstream: a builtin opens a single grouped argument into that supply, while a user-variadic call keeps it as one argument unless `...` is written. (See [Variadic Explicit Parameters](#variadic-explicit-parameters).)
- Selection `:` also explicitly projects one selected item one level before sequence consumption.
- Sequence-builtin dot-call passes the receiver as the leading item in the supply. With `Values = 1, 2, 3`, `Values.count` is `3`; `range(1, 5).count` is `5`; and with `Items = (range(1, 3)..., 7)`, `Items.count` is `4`. For a rest-only helper over a single grouped value, user-variadic capture and builtin opening coincide, so `Helper(values...) = values.count` and `count` agree: `Helper(Values)`, `Values.Helper()`, `Helper(Values...)`, `count(Values)`, and `count(Values...)` all give the same result. They diverge only for mixed fixed/rest shapes, where a user-variadic call keeps a single grouped argument intact unless `...` is written.
- Parentheses build one grouped value, which a rest-shaped builtin opens by singleton-boundary normalization, so `count((1, 2, 3))` is `3`, `order((3, 4, 2, 1))` works, and `sum((10, 20, 30))` is valid — each agreeing with the inline form `count(1, 2, 3)`, `order(3, 4, 2, 1)`, `sum(10, 20, 30)`.
- Sequence-value arguments are destructured by the `values...` slot one boundary deep; nested sequence values stay intact and are never recursively flattened.
- `:` selection projects one level of content before the builtin consumes the selected sequence value. `Pairs = (1, 2), (3, 4)` gives `(Pairs:0).count = 2`. `Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)` gives `(Data:0).order` as the sequence value `(1, 2, 4, 6, 7)`.
- Higher-order callbacks still receive the one-level projected current item, so sequence elements are available through ordinary parameters or `item:i`. Any sequence builtin applied to that callback variable consumes the projected item's emitted top-level items
- Nested sequence values are never recursively flattened unless a builtin explicitly says so, such as `atoms`; use postfix spread `value...` to open only one outer boundary
- `contains` compares its searched item against those extracted top-level items using ordinary KatLang value equality; it does not recurse into nested sequence elements
- `distinct` compares those extracted top-level items structurally, using the same ordinary KatLang value equality rules
- `take` and `skip` follow the same family pattern as the other sequence builtins: direct calls use a suffix count parameter (`take((1, 2, 3), 2)` / `skip((1, 2, 3), 2)`), and dot-calls use `collection.take(2)` / `collection.skip(2)`

### Ordering: `order` and `orderDesc`

`order(values...)` sorts top-level numeric items in ascending order.
`orderDesc(values...)` sorts the same kind of top-level items in descending order.

- Both builtins evaluate the full collection eagerly before sorting
- Duplicates are preserved; there is no implicit distinct or unique step, so use `distinct` separately when deduplication is required
- The result is one sequence value (the call is a value boundary); use caller-site spread `...` when the surrounding context needs the sorted items as an item supply
- Each top-level element must be exactly one atomic numeric value
- Sequence values are not flattened or inspected recursively
- Strings and mixed-type collections are invalid

Both call styles are supported: `order(values...)` / `orderDesc(values...)` and `collection.order` / `collection.orderDesc`.

```
order((3, 4, 2, 1, 3, 3))

orderDesc((3, 4, 2, 1, 3, 3))

Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
(Data:0).order
```

**Results:**
```
(1, 2, 3, 3, 3, 4)

(4, 3, 3, 3, 2, 1)

(1, 2, 4, 6, 7)
```

`order`/`orderDesc` are value boundaries: each bare call returns one sequence value. Open the sorted items with caller-site spread:

```
X = 3, 1, 2
X.order
X.order...
X.orderDesc...
```

**Results:**
```
(1, 2, 3)

1
2
3

3
2
1
```

Applying `order` or `orderDesc` to a collection like `(1, 'hello')` is invalid because KatLang does not define a loose mixed-type ordering rule. `order((1, 2), (3, 4))` is also invalid, because each sequence value is not a sortable atom.
Named sequence helpers and call receivers such as `Values = 1, 2, 3` followed by `order(Values)`, `Values.order`, `order(Values...)`, and `order(1, 2, 3)` all return the sequence value `(1, 2, 3)`; `P = range(5, 1)` followed by `order(P)` and `range(5, 1).order` return the same value. To add an extra item, supply it as another item in the supply — grouped or inline: `order((Values..., 8))` and `order(Values..., 8)` both return `(1, 2, 3, 8)`. Selection already projects one level of content, so `(Data:0).order` sorts `7, 6, 4, 2, 1` to `(1, 2, 4, 6, 7)`. Each is one value at the call boundary; append `...` (for example `Values.order...`) when the surrounding context needs the sorted items as an item supply.

### Counting: `count`

`count(values...)` returns how many top-level values the evaluated sequence denotes.

- Each atom, string, or sequence value counts as one top-level element
- Sequence values are not flattened or inspected recursively

Both call styles are supported: `count(values...)` and `collection.count`.

<!-- spec:count-family -->
```
count(())
count((()))

count(range(1, 5))

count((10, 20, 30))

count((3, 4, range(1, 5)..., 7))

count((range(1, 5)..., 7))

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
`count(())` and `count((()))` both return `0` because repeated ordinary parentheses around the empty sequence canonicalize to `()`. `count({})` is an error because a no-output body has no defined output. `count((1, 2, 3))`, `Values = (1, 2, 3)` followed by `count(Values)`, `Values.count`, and `((1, 2, 3)).count` all return `3`, because the rest-shaped `count(values...)` opens that single grouped value by singleton-boundary normalization. `Values = 1, 2, 3` followed by `count(Values)`, `Values.count`, `count(1, 2, 3)`, and `count(Values...)` all return `3` (the spread joins the same item supply). In `count((3, 4, range(1, 5)..., 7))`, the range contributes its emitted items inside one sequence value, so the count is `8`. Selection still projects one level first, so `Pairs = (1, 2), (3, 4)` followed by `(Pairs:0).count` returns `2`.

### Membership: `contains`

`contains(values..., item)` returns `1` when any extracted top-level sequence item equals `item`, otherwise `0`.

- Comparison uses ordinary KatLang value equality
- Atoms compare by numeric value, strings by exact string value, and sequence values structurally by sequence elements
- Search is top-level only; nested sequence elements are not searched recursively
- Empty collections return `0`

Both call styles are supported: `contains(values..., item)` and `collection.contains(item)`.

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
`contains(((1, 2), (3, 4)), (1, 2))` returns `1` after the outer sequence value is opened one level. KatLang still does not recurse beyond the immediate top-level items. Selection projects one level first, so with `Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)`, `(Data:0).contains(4)`, `contains(Data:0, 4)`, and `contains((Data:0)..., 4)` all return `1` (the spread joins the item supply, and `4` binds the `item` suffix from the back).

### First Element: `first`

`first(values...)` returns the first top-level value in the evaluated sequence, unchanged.

- The collection must be non-empty
- Atoms, strings, and sequence values each count as one top-level element
- Sequence values are preserved whole and are not flattened

Both call styles are supported: `first(values...)` and `collection.first`.

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
`first(1, 2, 3)`, `first((1, 2, 3))`, `first(((1, 2, 3)))`, `Values = (1, 2, 3)` followed by `first(Values)`, and `Values.first` all return `1`: `first(values...)` consumes an item supply, opening a single grouped sequence boundary where required rather than repeatedly normalizing nested structure. A literal `((1, 2, 3))` already collapses to `(1, 2, 3)`, so the inline, grouped, and nested forms agree. Multiple sibling grouped values are preserved, though — with `A = 1, 2` and `B = 3, 4`, `first(A, B)` returns the first grouped sibling `(1, 2)` (not flattened to `1`), and `last(A, B)` returns `(3, 4)`. To make a grouped sequence value itself the first item, supply it among siblings such as `first((1, 2), (3, 4))`.

### Last Element: `last`

`last(values...)` returns the last top-level value in the evaluated sequence, unchanged.

- The collection must be non-empty
- Atoms, strings, and sequence values each count as one top-level element
- Sequence values are preserved whole and are not flattened

Both call styles are supported: `last(values...)` and `collection.last`.

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
`last(1, 2, 3)`, `last((1, 2, 3))`, `last(((1, 2, 3)))`, `Values = (1, 2, 3)` followed by `last(Values)`, and `Values.last` all return `3`: `last(values...)` consumes an item supply, opening a single grouped sequence boundary where required rather than repeatedly normalizing nested structure (a literal `((1, 2, 3))` already collapses to `(1, 2, 3)`). Multiple sibling grouped values are preserved, though — with `A = 1, 2` and `B = 3, 4`, `last(A, B)` returns the last grouped sibling `(3, 4)`. To make a grouped sequence value itself the last item, supply it among siblings such as `last((1, 2), (3, 4))`.

### Distinct: `distinct`

`distinct(values...)` returns the extracted top-level sequence items with later duplicates removed.

- The original left-to-right order of first occurrence is preserved
- Atoms compare by numeric value, strings by exact string value, and sequence values structurally by sequence elements
- Sequence values stay whole and are not flattened
- Empty collections stay empty
- A single kept item is returned as that item itself (no one-item wrapper), so `distinct((), ())` returns `()`

Both call styles are supported: `distinct(values...)` and `collection.distinct`.

<!-- spec:distinct-family-tutorial -->
```
distinct((3, 1, 3, 2, 1, 2))

distinct(((1, 2), (1, 2), (3, 4)))

Values = 3, 1, 3, 2, 1, 2
Values.distinct
```

**Results:**
```
(3, 1, 2)

((1, 2), (3, 4))

(3, 1, 2)
```

`distinct` is a value boundary: the bare call returns one sequence value. Open the deduplicated items with caller-site spread:

```
Values = 1, 1, 2, 3
Values.distinct
Values.distinct...
```

**Results:**
```
(1, 2, 3)

1
2
3
```

`Values = ((1, 2), (1, 2), (3, 4))` followed by `distinct(Values)` removes the duplicate sequence value after the outer sequence value is opened. The same is true for `Values.distinct`. `distinct(Values...)` opens its items into the same item supply, so it agrees with `distinct(Values)`.

### Take Prefix: `take`

`take(values..., count)` returns the first `count` top-level values in the evaluated sequence, unchanged.

- The count must evaluate to exactly one whole-number value
- `count <= 0` returns an empty sequence
- Counts larger than the sequence length return the whole sequence
- Sequence values are preserved whole and are not flattened
- A single taken item is returned as that item itself (no one-item wrapper), so `take(values..., 1)` agrees with `first(values...)`

Both call styles are supported: `take(values..., count)` and `collection.take(count)`.

<!-- spec:take-family-tutorial -->
```
take((1, 2, 3, 4, 5), 3)

take(((1, 2), (3, 4)), 1)

range(1, 5).take(2)
```

**Results:**
```
(1, 2, 3)

(1, 2)

(1, 2)
```

`take(((1, 2), (3, 4)), 1)` keeps exactly one item, the sequence value `(1, 2)`, and returns that item itself — the same value `first(((1, 2), (3, 4)))` returns. There is no one-item wrapper `((1, 2))`; that shape is not a writable KatLang value.

`take` is a value boundary: the bare call returns one sequence value. Open the taken items with caller-site spread:

```
range(1, 5).take(2)
range(1, 5).take(2)...
```

**Results:**
```
(1, 2)

1
2
```

`take((1, 2, 3), 0)` and `take((1, 2, 3), -2)` both return an empty result. `take((3, 4), (1, 2, 3))` is invalid because the count must be exactly one whole-number value, not a sequence value. `Values = (1, 2, 3)` followed by `take(Values, 1)` and `take(Values..., 1)` both return `1`, and `Values.take(2)` returns the sequence value `(1, 2)` (use `Values.take(2)...` to open it): the collection is bound from the item supply — a grouped receiver is opened by singleton-boundary normalization and a spread joins the same supply — while the count `1` binds the suffix parameter from the back.

### Skip Prefix: `skip`

`skip(values..., count)` returns the evaluated sequence after skipping the first `count` top-level values.

- The count must evaluate to exactly one whole-number value
- `count <= 0` returns the original sequence unchanged
- Counts larger than the sequence length return an empty sequence
- Sequence values are preserved whole and are not flattened
- A single remaining item is returned as that item itself (no one-item wrapper), agreeing with `last(values...)`

Both call styles are supported: `skip(values..., count)` and `collection.skip(count)`.

```
skip((1, 2, 3, 4, 5), 3)

skip(((1, 2), (3, 4)), 1)

range(1, 5).skip(2)
```

**Results:**
```
(4, 5)

(3, 4)

(3, 4, 5)
```

`skip(((1, 2), (3, 4)), 1)` leaves exactly one item, the sequence value `(3, 4)`, and returns that item itself — the same value `last(((1, 2), (3, 4)))` returns.

`skip` is a value boundary: the bare call returns one sequence value. Open the remaining items with caller-site spread:

```
range(1, 5).skip(2)
range(1, 5).skip(2)...
```

**Results:**
```
(3, 4, 5)

3
4
5
```

`skip((1, 2, 3), 0)` and `skip((1, 2, 3), -2)` both return `(1, 2, 3)`. `skip((1, 2), 'hello')` is invalid because the count must be exactly one whole-number value. `Values = (1, 2, 3)` followed by `skip(Values, 1)` and `skip(Values..., 1)` both return the sequence value `(2, 3)`, and `Values.skip(1)` does the same (use `Values.skip(1)...` to open it): the collection is bound from the item supply while the count `1` binds the suffix parameter from the back.

### Minimum: `min`

`min(values...)` returns the smallest top-level numeric element in a sequence.

- The collection must be non-empty
- Each top-level element must be exactly one atomic numeric value
- Sequence values are not flattened or inspected recursively
- Strings are invalid

Both call styles are supported: `min(values...)` and `collection.min`.

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

Applying `min` to an empty collection is invalid because `min` requires at least one top-level numeric element. A collection such as `((1, 2), (3, 4))` is invalid because sibling sequence values are preserved (not flattened), and each top-level item must be one atomic numeric value. `min(range(1, 5))`, `P = range(1, 5)` followed by `min(P)`, `Values = 1, 2, 3` followed by `min(Values)`, `Values.min`, `min(1, 2, 3)`, `min((1, 2, 3))`, and `(1, 2, 3).min` all succeed because `min(values...)` consumes an item supply — singleton grouped boundaries are normalized, so the inline, grouped, and dot-call forms agree. Selection such as `(Data:0).min` projects one level of content first.

### Maximum: `max`

`max(values...)` returns the largest top-level numeric element in a sequence.

- The collection must be non-empty
- Each top-level element must be exactly one atomic numeric value
- Sequence values are not flattened or inspected recursively
- Strings are invalid

Both call styles are supported: `max(values...)` and `collection.max`.

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

Applying `max` to an empty collection is invalid because `max` requires at least one top-level numeric element. A collection such as `((1, 2), (3, 4))` is invalid because sibling sequence values are preserved (not flattened), and each top-level item must be one atomic numeric value. `max(range(1, 5))`, `P = range(1, 5)` followed by `max(P)`, `Values = 1, 2, 3` followed by `max(Values)`, `Values.max`, `max(1, 2, 3)`, `max((1, 2, 3))`, and `(1, 2, 3).max` all succeed because `max(values...)` consumes an item supply — singleton grouped boundaries are normalized, so the inline, grouped, and dot-call forms agree. Selection such as `(Data:0).max` projects one level of content first.

### Summation: `sum`

`sum(values...)` adds the top-level numeric elements of a sequence from left to right and returns one numeric result.

- Each top-level element must be exactly one atomic numeric value
- Empty collections return `0`
- A single numeric value is treated as a one-element collection
- Sequence values are invalid and are not flattened
- Strings are invalid

Both call styles are supported: `sum(values...)` and `collection.sum`.

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

Applying `sum` to an empty collection returns `0`. A collection such as `((1, 2), (3, 4))` is invalid because `sum` preserves sibling sequence values (it does not flatten them), and each top-level item must be one atomic numeric value. `sum(range(1, 5))`, `P = range(1, 100)` followed by `sum(P)`, `Values = 1, 2, 3` followed by `sum(Values)`, `Values.sum`, `sum(1, 2, 3)`, `sum((1, 2, 3))`, `(1, 2, 3).sum`, and `{1, 2, 3}.sum` all succeed because `sum(values...)` consumes an item supply — singleton grouped boundaries are normalized, so the inline, grouped, and dot-call forms agree. Selection such as `(Data:0).sum` projects one level of content first.

### Average: `avg`

`avg(values...)` averages the top-level numeric elements of a sequence and returns one numeric result.

- The collection must be non-empty
- Each top-level element must be exactly one atomic numeric value
- A single numeric value is treated as a one-element collection
- The C# runtime returns the decimal arithmetic mean (total divided by count), for example `avg((1, 2))` returns `1.5` and `avg((-1, -2))` returns `-1.5`. (Lean's Int-only core approximates this with truncation toward zero, e.g. `avg((1, 2)) = 1` there — a model limitation, not the runtime contract.)
- Sequence values are invalid and are not flattened
- Strings are invalid

Both call styles are supported: `avg(values...)` and `collection.avg`.

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

Applying `avg` to an empty collection is invalid because `avg` requires at least one top-level numeric element. A collection such as `((1, 2), (3, 4))` is invalid because `avg` preserves sibling sequence values (it does not flatten them), and each top-level item must be one atomic numeric value. `avg(range(1, 5))`, `P = range(1, 5)` followed by `avg(P)`, `Values = 1, 2, 3` followed by `avg(Values)`, `Values.avg`, `avg(1, 2, 3)`, `avg((1, 2, 3))`, and `(1, 2, 3).avg` all succeed because `avg(values...)` consumes an item supply — singleton grouped boundaries are normalized, so the inline, grouped, and dot-call forms agree. Selection such as `(Data:0).avg` projects one level of content first.

### Reduction: `reduce`

`reduce(values..., reducer, initial)` walks the sequence from left to right and threads an accumulator through the top-level items.

- `reducer(element, accumulator)` receives the current item through the same one-level projection as `S:i`
- `reduce` treats the accumulated value as reducer state: a normal accumulator parameter receives that state as one structural value, while a top-level variadic accumulator parameter receives the accumulator's top-level state slots, matching variadic `while` and `repeat` step parameters
- The reducer must return exactly one next accumulator value
- One sequence-value top-level element still contributes one fold step; the element view is projected one level, not recursively flattened
- Sequence-value accumulator states are allowed when they are returned as one sequence value
- Empty collections return `initial` unchanged

Both call styles are supported: `reduce(values..., reducer, initial)` and `collection.reduce(reducer, initial)`.

```
Add = x + total
reduce((1, 2, 3, 4), Add, 0)

TakeValue((tag, value), acc) = acc + value
reduce(((1, 10), (2, 20), (3, 30)), TakeValue, 0)

Stats(x, (acc, counter)) = (x + acc, counter + 1)
reduce((1, 2, 3, 4), Stats, (0, 0))

Append(item, history...) = (history..., item)
reduce((2, 3, 4), Append, 1)
```

**Results:**
```
10

60

(10, 4)

(1, 2, 3, 4)
```

No wrapper helper is required for sequence-value accumulators: a parenthesized sequence value such as `(a, b)` is one sequence-value accumulator value when the reducer uses a normal accumulator parameter. Use a top-level variadic accumulator parameter when the reducer should treat that accumulator as state slots. To grow a sequence-value accumulator, spread the prior items beside the new value with a comma — `(history..., item)`. Note that `...` is postfix and takes no right operand, so `history...item` (without the comma) is the postfix spread of `history` joined with `item`, not a special binary spread.
`reduce(values..., reducer, initial)` consumes an item supply — a grouped collection is opened by singleton-boundary normalization — while the `reducer` and `initial` suffix parameters bind from the back. So `reduce(1, 2, reducer, initial)`, `reduce((1, 2), reducer, initial)`, `Values = 1, 2` followed by `reduce(Values, reducer, initial)`, and `reduce(Values..., reducer, initial)` all reduce over the two items `1` and `2`, calling the reducer once per item; nested sequence elements are not split recursively. Multi-output inputs such as `reduce(range(1, 5)..., reducer, initial)`, `P = range(1, 5)` followed by `reduce(P..., reducer, initial)`, and `reduce(1, range(2, 4)..., reducer, initial)` iterate once per immediate item, and named sequence-valued helpers behave the same: `Values = (1, 2, 3)` followed by `Values.reduce(reducer, initial)` reduces over its three items. Multiple sibling grouped values are preserved unless explicitly opened — with `A = 1, 2` and `B = 3, 4`, `reduce(A, B, reducer, initial)` reduces over the two grouped values `(1, 2)` and `(3, 4)` (so a numeric reducer rejects them), while `reduce(A..., B..., reducer, initial)` reduces over all four numbers.
Results such as `acc, x` or any empty result are still invalid step outputs because `reduce` requires exactly one accumulator value at every step.

### Fixed Loop: `repeat`

`repeat` is a builtin algorithm that takes three arguments: a step algorithm, a count, and an initial state. It runs the step algorithm the given number of times, feeding each output back as the next input.

```
// Step: add 1 to x
Increment = x + 1

// Run 5 times starting from 0:
Increment.repeat(5, 0)
```

**Result:** `5`

Multi-output step algorithms maintain all outputs as state across iterations:

```
// Accumulate a running sum of 1..4
// State: (index, total)
Step = a + 1, total + a

// Run 4 times starting from (a=1, total=0), then select total:
Step.repeat(4, 1, 0) : 1
```

**Result:** `10`

(1 + 2 + 3 + 4 = 10, selected with `:1`.)

**Factorial:**

```
// State: (n, accumulator)
// Each step: advance counter, multiply accumulator
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
// Step: decrement x, continue while x > 1
Step = x - 1, x > 1

Step.while(5)
```

**Result:** `1`

When `Step` runs with `x = 1`, it would produce `(0, 0)` — the flag is `0`, so this result is discarded and the loop returns `1` from the previous iteration.

Multi-output state works the same way — only the last output is the continue-flag:

```
// Sum multiples of 3 or 5 below 1000
// State: (n, total) — last output is the continue flag
Algo = n - 1, total + if(n mod 3 == 0 or n mod 5 == 0, n, 0), n > 2

// Start from (n=999, total=0), select total:
Algo.while(999, 0) : 1
```

**Result:** `233168`

---

## Practical Examples

### Reusable Calculation with Parameters

A simple unit converter with one parameter:

```
// Convert between temperature units
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

// Call to get area and circumference as one sequence value:
Circle(5)

// Pick just the area (index 0):
Circle(5) : 0
```

**Results:**
```
(78.539816339744830961566084582, 31.415926535897932384626433833)
78.539816339744830961566084582
```

### Loop-Based Example: Sum of a List

Compute the sum of all numbers in a multi-value property using `repeat`:

```
Numbers = 3, 5, 9, 1, 0, 6

// Step: advance index, accumulate Numbers[index]
Step = a + 1, total + Numbers:a

// Repeat once per element, then select the accumulated sum:
repeat(Step, Numbers.count, 0, 0) : 1
```

**Result:** `24`

### Fibonacci Sequence

Compute the Nth Fibonacci number:

```
// State: (a, b) — consecutive Fibonacci numbers
Fib = b~, a + b

// 10 steps starting from (0, 1), take the first value:
Fib.repeat(10, 0, 1) : 0
```

**Result:** `55`

---

## Higher-Order Algorithms

An algorithm can accept another algorithm as an argument and call it. This is how you write generic, reusable computation patterns.

### Algorithm as Argument

Fixed calls preserve argument expression boundaries. If a property expects multiple arguments and you already have a multi-output value, project the pieces explicitly or use `...` when you intentionally want that result sequence to spread into call argument items.

```
Sum3 = a + b + c
Input = 1, 2, 3

// Input is one argument expression, so this is bad arity:
Sum3(Input)

// Explicit forms:
Sum3(Input:0, Input:1, Input:2)
Sum3(1, 2, 3)
```

Both explicit forms produce `6`.

Algorithms can also be passed as callable values:

```
// Apply takes a callable 'f' and calls it with 9
Apply = f(9)

// Pass an algorithm that adds 1 to its argument:
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

Sequence builtins `filter`, `map`, and `reduce` are a special higher-order case. Their per-item callback argument behaves like `S:i` for the traversed sequence `S`, so sequence-value current items expose their immediate members without recursive flattening. This rule is local to those builtins; ordinary higher-order calls such as `Apply(Increment)` still use ordinary argument binding.

### Parametrized vs non-parametrized algorithms

The distinction between braces and parentheses is critical:

| Syntax | Meaning |
|---|---|
| `( ... )` | Non-parametrized sequence-value construction — evaluated in the enclosing scope; no new parameter scope |
| `{ ... }` | Parametrized algorithm value — creates a new scope with its own inferred parameters |
| `{a + 1}` | Parametrized algorithm with parameter `a`, passable as an argument |

`{}` braces mark the passed algorithm as **parametrized** — it owns its own parameters (`a` in the example above). A **non-parametrized** `()` expression has no parameter scope of its own — any free names are absorbed by the enclosing algorithm instead.

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

With no contents, `()` is the empty sequence value (a real value, displayed as `()`), while `{}` is an empty parametrized body with no defined output. They are not interchangeable: `()` is a value you can store, count, compare, and spread, whereas `{}` produces no value at all and is an error when used where a value is required.

---

## Spread with ellipsis operator

The `...` operator is KatLang's POSTFIX spread operator. `x...` opens ONE item-producing boundary of `x`'s evaluated value and contributes the opened items to the surrounding item supply (output rows, call argument slots, or list/sequence elements) — it does not create or emit a sequence value by itself. A sequence value or an exact [list value](#lists) supplies its contained items; an atom or string supplies itself as one item. It NEVER consumes a right operand: any token after `...` — tight, spaced, or on the next physical line — starts a new expression-list slot. So `x...y` is `x..., y`, and `x...C` is `x..., C`; `C` is just the following expression-list slot, not a right operand of `...`. (Internally `x...` is a unary spread node over its single operand, with no right operand.)

Because `...` is postfix everywhere, `x...y`, `x ...y`, and `x... y` all mean `x..., y` (whitespace before `...` is insignificant). This matters at boundary-sensitive sites: `Use(1...Tail)` has two argument slots, `1...` and `Tail`. To construct one sequence argument from a spread value and another expression, capture it explicitly with parentheses: `Use((1..., Tail))`.

Postfix `...` does not continue an expression onto the next line. In an algorithm body, the next complete expression is another expression-list item:

```
X...
Y
```

is interpreted as:

```
X..., Y
```

You may still write an explicit comma for clarity:

```
X...,
Y
```

This has the same expression-list shape. If `x...` has no following expression, it simply spreads `x` followed by nothing.

Use parentheses for one sequence value:

```
(X, Y)
```

`...` binds to its immediate operand before expression-list handling, so:

```
Use(a b...)
```

means:

```
Use(a, b...)
```

Inside the open call-argument list the comma may be implicit — same-line adjacency separates slots, and because the `(` keeps the list open across lines a newline separates slots there too — so `Use(a b...)` and

```
Use(a
b...)
```

mean exactly the same `Use(a, b...)`.

Postfix `...` applies only to the expression it follows. `a b... c` and the three-line form are expression lists `a, b..., c`; use `(a, b..., c)` for one sequence value.

The explicit parenthesized form can intentionally force a different value boundary around a spread expression, but it does not change which operand `...` owns. `Use((a, b...))` and `Use((a, (b...)))` both apply `...` only to `b`.

This is different from comma and parentheses: comma preserves structural output or argument boundaries, parentheses create one sequence value, and `...` spreads already evaluated result content. A bare spread does not create a new structural sequence value, does not preserve or merge properties, and does not recursively flatten nested sequence values. If the spread operand has no defined output, evaluation fails; the empty sequence value `()` is defined, so `()...` simply contributes no items.

Parentheses around a spread preserve one sequence-value result boundary. Use this when a spread result should travel as one value at a boundary-sensitive site such as a call argument, named property, or loop step output.

`{ }` introduces an algorithm/body scope. The outer body block of a program or property can be omitted and is transparent as that program or property's output. A nested `{ }` is still an expression boundary, like nested `( )`, except that it also introduces local scope. Multi-output nested expression boundaries are preserved unless you explicitly spread them with `...`.

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

First...Second
```

**Results:**
```
1
2
(3, 4)
```

`First...` opens `First` into its two items as root rows, and `Second` stays one sequence-valued row — the spread does not merge the two properties into one sequence value.

`B = 1...2` is the expression list `1..., 2` — postfix spread of `1` followed by a separate `2` slot — not one binary spread expression (`...` takes no right operand):

```
A = 1, 2
B = 1...2

A.count
B.count
```

**Results:**
```
2
2
```

Parenthesizing postfix spread plus the following expression-list slot keeps those results as one sequence value. `(First...Second)` is not one binary spread expression — it is the parenthesized expression list `(First..., Second)` (`Second` is not a right operand of `...`):

```
Test = (First...Second)
Test.count
```

**Results:**
```
3
```

Spread projects only one immediate level. Each spread contributes its opened items as separate root rows, and the expression after it is a separate slot:

<!-- spec:spread-one-level-family -->
```
(1, 2)...3
1...(2, 3)
(1, (2, 3))...4
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
| `1...2, 3` | Three expression-list slots after spread: `1...`, `2`, and `3` |
| `(1...2), 3` | The parenthesized expression list `(1..., 2)` is one sequence-valued output, followed by the separate output `3` |
| `(1, 2)...3` | `...` applies only to `(1, 2)` (spreading its items `1, 2`); `3` is a separate expression-list slot. There is no right operand of `...`. Produces `1, 2, 3` |
| `(1, (2, 3))...4` | Spread opens one level: `1` and the intact inner sequence value `(2, 3)` become items, and `4` is a separate slot, producing `1, (2, 3), 4` |
| `((1, 2))...3` | Redundant unary parentheses canonicalize during value construction, so `((1, 2))` is the value `(1, 2)`; the spread opens its items and `3` is a separate slot, producing `1, 2, 3` — same as `(1, 2)...3` |
| `1, { 2, 3 }` | Preserves the nested block boundary, producing `1, (2, 3)` |
| `1...{ 2, 3 }` | `1...` spreads `1`, then the block `{ 2, 3 }` is a separate expression-list slot; `...` has no right operand. Produces `1, (2, 3)` |

---

## Lists

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

Unlike `()`, the empty list `[]` is never transparent: `[] > 1` is a type error while `() > 1` passes the operand through, and `F([])` passes one empty-list argument while `F([]...)` supplies zero arguments.

Selection `:` follows the generic one-item projection rule for opaque values — it is **not** list-element indexing. A list is one top-level item, so `[1, 2]:0` yields the whole list `[1, 2]` (just as `7:0` is `7`), and with `A = (0, [1, 2])`, `A:1` yields the intact list `[1, 2]`. List-element indexing is deferred follow-up work.

### Spreading Lists

Postfix `...` opens exactly ONE list boundary into the surrounding item supply — the same spread operator and rules as sequence values. Because single-name assignment is capture (not deconstruction), the captured spread becomes a canonical sequence:

<!-- spec:list-spread-capture -->
```
A = [1, 2, 3]

x = A
y = A...

x
y
```

**Results:**
```
[1, 2, 3]
(1, 2, 3)
```

This distinction is essential: `x = value` preserves the value, `x = value...` opens one boundary and captures the resulting item supply.

Spread opens only the outermost boundary:

<!-- spec:list-spread-edges -->
```
A = []
B = [7]
C = [[7]]

A...
B...
C...
```

**Results:**
```
7
[7]
```

`A...` supplies zero items (its output row vanishes), `B...` supplies `7`, and `C...` supplies the inner list `[7]` intact.

Spread also works INSIDE list literals — a spread element inserts its item supply into the list being constructed:

<!-- spec:list-literal-spread-elements -->
```
A = 1, 2, 3

[A...]
[0, A..., 4]
```

**Results:**
```
[1, 2, 3]
[0, 1, 2, 3, 4]
```

Non-spread values stay single elements; only explicit `...` opens them:

<!-- spec:list-elements-preserve-boundaries -->
```
A = [1, 2]
B = [3, 4]

[A, B]
[A..., B...]
[A, B...]
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
[1, []..., 2]
[1, ()..., 2]
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
F(A...)
```

**Results:**
```
7
6
```

`F(A)` without the spread is an arity error (one argument for three parameters), and `F([]...)` supplies zero arguments. Extension dot-calls follow the ordinary receiver rule: `A.F(9)` passes the whole list `A` as the one leading argument.

Multi-target **deconstruction**, by contrast, is an unpacking receiver: a right-hand side that is exactly one list value opens the list and matches its elements — the same rule that already opens a lone sequence value, and the same bindings the explicit spread `x, y, z = [1, 2, 3]...` produces. (The two written forms coincide except for one exotic shape: a singleton list whose lone element is itself a sequence or list, such as `[(1, 2)]`, where the spread form re-groups through a capture boundary and opens one level further.)

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

Rest capture always groups the unmatched items as one canonical SEQUENCE value — it never reconstructs the source list:

<!-- spec:list-rest-capture-is-sequence -->
```
x, rest... = [1, 2, 3]

x
rest
```

**Results:**
```
1
(2, 3)
```

With `x, rest... = [1]` the rest is `()`, and with `x, rest... = [1, 2]` the singleton rest normalizes to `2` — exactly the existing sequence-capture rules. Rest-only assignment stays forbidden for lists exactly as for sequences: `items... = [1, 2, 3]` is a parse error; write producer-side spread `items = value...` to open a stored list into a captured sequence.

### Lists and Collection Builtins

Builtin collection support for lists is deliberately deferred: a list value inside a builtin's item supply reports a targeted error, and only explicit spread supplies list elements to builtins today.

```
count([1, 2, 3])
```

**Result:** error — `count does not support list values yet; spread the list with `...` to supply its items`.

The explicit spread forms are fully supported:

```
count([1, 2, 3]...)
sum([1, 2, 3]...)
```

**Results:**
```
3
6
```

(`atoms` is the one exception: it flattens numeric structure directly and omits list values exactly like strings.)

---

## Atoms

Algorithms in KatLang can produce structured, nested outputs — for example, a sequence value inside a sequence value. The `atoms` builtin strips away all of that sequence-value structure and returns a flat list of plain numeric values.

```
A = 1...2, 3
atoms(A)
atoms(A)...
```

**Results:**
```
(1, 2, 3)

1
2
3
```

`atoms` is a value boundary like the other builtins: the bare call returns one flat sequence value, and caller-site spread `...` opens it into an item supply. This is useful when you need to treat a complex algorithm's output as a simple sequence of numbers, regardless of its original sequence-value structure.

### Opening one level vs flattening

KatLang keeps three operations distinct, so pick the one that matches your intent:

- A plain value reference such as `X` **preserves one value boundary** — a sequence value travels as one value.
- Postfix spread `X...` **opens one level**, contributing the sequence value's immediate items to the surrounding output, argument list, or item supply.
- `atoms(X)` **recursively projects** every numeric atom, erasing all sequence-value structure.

```
X = (1, 2, 3)
X...
```

produces:

```
1
2
3
```

`X...` opens only one level, so `((1, 2), (3, 4))...` produces `(1, 2), (3, 4)` with the inner boundaries intact, while `((1, 2), (3, 4)).atoms` recursively flattens to the single sequence value `(1, 2, 3, 4)` (append `...` to open it into an item supply).

---

## Conditional Algorithms

The `if` builtin handles simple branching. For algorithms that need to dispatch based on structure or select from many cases, KatLang provides **conditional algorithms** — a form of pattern matching. A conditional algorithm is defined by writing multiple clause-style branches, each specifying a pattern to match against the arguments.

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

Equal(1, 1)  // 1
Equal(1, 2)  // 0
```

This also works inside sequence-value parameter patterns such as `SamePair((x, x))`. Repeated names involving a variadic capture, such as `F(xs..., xs)`, are not supported.

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

// b binds to the entire sequence value (2, 3):
Loose(1, (2, 3))
```

**Result:** `1`

But a parenthesized single variable `(b)` is a 1-element sequence-value pattern — it only matches a single value, not a multi-element sequence value:

```
// (b) does not match (2, 3) because arities differ:
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

A sole recursive parameter pattern may also contain one explicit variadic binder at each pattern level. These are ordinary explicit parameter lists, not conditional matching:

```
PairSum((x, y)) = x + y
CountSequenceValue((values...)) = values.count
Step((history...), previous) = history.count + previous
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

```
// Load and bind to property 'Lib':
Lib = load('https://katlang.org/algorithm.kat')

// Access a public property 'X' from the loaded algorithm:
Lib.X + 3

// Use the second output value of the loaded algorithm (index 1):
Lib:1 + 10
```

**Results:**
```
23
16
```

### `open`: Import Properties Directly

The `open` keyword makes all **public** properties of a target algorithm available directly in the current scope, without qualifying them with a prefix.

```
open 'https://katlang.org/algorithm.kat'

// X is now directly accessible:
X + 3
```

**Result:** `23`

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

String targets use single quotes and mix freely with names: `open 'https://example.org/lib.kat', LibA`. Comma is the only separator — `open A ; B` and `open A B` are parse errors asking for a comma, never two targets. The first target must begin on the same line as `open`. Comma keeps its normal explicit line-continuation behavior, so a long list may span lines with a trailing or leading comma:

```
open LibA,
LibB

open LibA
, LibB
```

A leading `.` likewise continues a dotted target across the line (`open Lib` followed by `.Sub` opens `Lib.Sub`). A plain newline never continues `open`: `open Math` followed by `Math.Pi` on the next line is an open plus a report row. Spread `...` is **not** open-target syntax for any target kind: `open A...`, `open A...B`, `open A, B...`, and `open 'url'...` are parse errors — use comma for multiple targets. Valid targets are names, argumentless dot-call paths like `Lib.Sub`, single-quoted string URLs, and inline blocks.

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

By default, properties are private — accessible within their own algorithm and its children, but not visible to outside callers who load or open the algorithm. Marking a property `public` makes it eligible for external exposure, but a property is exported only if it is self-contained. A nested property is not exported if it depends on parameters owned by an enclosing algorithm, or if it is defined inside a conditional algorithm branch.

```
// In a library algorithm:
public Area = r * r * Math.Pi
public Kind(0) = 'zero'
public Kind(x) = 'nonzero'   // visibility is family-level: every clause is public or none
Helper = Area / 2   // private — not visible to callers
```

Only `public` exported properties are exposed through `load` and `open`.

---

## Pitfalls

- **Decimal precision limits:** KatLang uses fixed-precision decimal arithmetic. Extremely large numbers or deeply nested calculations may hit precision boundaries.
- **Floating-point-backed precision:** trig, logarithm, square root, and power functions compute in double precision and normalize their results to about 15 significant digits, so residuals snap away — `Math.Sin(Math.Pi)` returns exactly `0`. The flip side: do not rely on more than 15 significant digits from these functions, while other irrational results (such as `Math.Sin(1)`) remain approximations.
- **Parameter order surprises:** parameter order is determined by first appearance reading left to right. If your expression reads `b - a`, the first parameter is `b`, not `a`. Use Grace (`~`) to override when needed.
- **`if` arity:** builtin `if` requires three arguments after spread expansion: `if(cond, a, b)`. There is no two-argument form. A grouped value is one argument, so `if(X)` is invalid when `X = 1, 2, 3`; spread it with `if(X...)` to open it into the three slots.
- **`()` vs `{}` confusion:** `(expr)` groups an expression in the current scope. `{expr}` creates a new algorithm with its own parameters. Passing `(a + 1)` as an argument doesn't create a callable — it evaluates `a + 1` immediately in the enclosing scope. Bare `()` is the empty sequence value (a real value); bare `{}` is a no-output body and is not a value.
- **Ignoring a parameter:** there is no special "ignore" syntax for implicit parameters — every undeclared name becomes a required argument. If you want to accept and discard an argument, use an explicit parameter pattern. Bind the unwanted argument to a variable in the pattern, then simply don't reference it in the body:

  ```
  // Wrong — no way to declare 'b' to discard; calling with two args fails:
  KeepFirst = a
  KeepFirst(42, 999)  // error: too many arguments

  // Right — 'b' is bound by the explicit parameter pattern but never used:
  KeepFirst(a, b) = a
  KeepFirst(42, 999) // Result: 42
  ```
- **Property redefinition:** defining the same property name twice is an error — properties are immutable bindings, not reassignable variables:

  ```
  A = 5
  A = 6  // error: Property 'A' is already defined
  ```

- **Duplicate branch patterns:** two conditional branches with match-equivalent patterns are rejected because the second branch would be unreachable under first-match semantics. Binder spelling does not matter, but repeated-name equality relationships do:

  ```
  F(x) = x + 1
  F(y) = y + 2  // error: duplicate branch pattern
  ```

  `F(x, x)` and `F(a, a)` are also equivalent, while `F(x, x)` and `F(a, b)` are distinct because only the first pattern requires equal arguments.

  Use different literal values or different arities to distinguish branches:

  ```
  F(0) = 1
  F(x) = x + 1  // OK — 0 and a variable are not equivalent
  ```
---

## Full Reference

### Operators

| Operator | Description | Precedence |
|---|---|---|
| `^` | Power (right-associative) | Highest |
| `*`, `/`, `div`, `mod` | Multiplication, division, integer division, modulo | |
| `+`, `-` | Addition, subtraction | |
| `<`, `>`, `<=`, `>=` | Ordering comparison, numeric scalar operands only (returns 1 or 0) | |
| `==`, `!=` | Structural value equality / inequality across all value kinds (numbers, strings, sequence values, and lists — different kinds compare unequal); returns 1 or 0 | |
| `and` | Logical and | |
| `xor` | Logical exclusive or | |
| `or` | Logical or | Lowest |
| `not` | Logical negation (prefix) | — |
| `-` | Arithmetic negation (prefix) | — |
| `:` | Output selection (zero-based index, one-level content projection) | Postfix |
| `.` | Dot-call / property access | Postfix |
| `...` | Spread (spread immediate evaluated results) | — |
| `~` (prefix) | Grace: move parameter one position earlier | — |
| `~` (postfix) | Grace: move parameter one position later | — |
| `[` `]` | Exact immutable list literal (`[1, 2, 3]`; never a call or indexing delimiter — `A[1]` is the adjacency list `A, [1]`) | — |

### Builtin Algorithms, Intrinsics, and Keywords

For the sequence builtins below, each top-level argument is one item in the `values...` item supply. A single grouped value is opened by singleton-boundary normalization, so `count(Values)`, `count((1, 2, 3))`, and `count(1, 2, 3)` all count three items; multiple sibling grouped values are preserved unless explicitly opened with `...`. Suffix parameters bind from the back, so a collection-plus-suffix call may be written either grouped or inline, for example `filter((range(1, 5)..., 8), predicate)` and `filter(range(1, 5)..., 8, predicate)`. Sequence-builtin dot-call passes the receiver as the leading item. Selection already projects one level of selected content, so `(A:0).count` follows the ordinary sequence rules for the selected content without any extra builtin-specific expansion. Higher-order builtins such as `filter`, `map`, and `reduce` do not recursively flatten sequence-value receivers beyond that.

For `repeat` and `while`, each explicit init argument becomes one initial state slot. `Step.repeat(3, a, b)` starts with two slots, while `Step.repeat(3, Pair)` starts with one slot even if `Pair` evaluates to multiple values. Use selections such as `Pair:0, Pair:1` or spread such as `Pair...` when you want a multi-output value to provide multiple initial slots; capture the step result as a sequence value when one structured slot should be preserved across iterations. `...` is postfix with no right operand, so `Step = history... next` emits history's items followed by `next` as multiple next-state slots, while `Step = (history..., next)` captures them into one next-state slot.

| Keyword | Usage |
|---|---|
| `if` | `if(cond, a, b)` |
| `while` | `step.while(init...)` or `while(step, init...)` |
| `repeat` | `step.repeat(n, init...)` or `repeat(step, n, init...)` |
| `range` | `range(start, stop)` — inclusive integer sequence, ascending or descending |
| `filter` | `filter(values..., predicate)` or `collection.filter(predicate)` — keep top-level elements whose predicate result is truthy (non-zero); the predicate must return exactly one atomic numeric value, the callback item behaves like `S:i`, and kept results remain the original top-level elements |
| `map` | `map(values..., mapper)` or `collection.map(mapper)` — transform top-level elements left to right; the callback item behaves like `S:i`, and the mapper must return exactly one mapped element |
| `order` | `order(values...)` or `collection.order` — eagerly sort top-level numeric elements ascending; duplicates are preserved and sequence-valued/string elements are invalid |
| `orderDesc` | `orderDesc(values...)` or `collection.orderDesc` — eagerly sort top-level numeric elements descending; duplicates are preserved and sequence-valued/string elements are invalid |
| `count` | `count(values...)` or `collection.count` — denotational top-level value count after evaluation, without flattening sequence values |
| `contains` | `contains(values..., item)` or `collection.contains(item)` — return `1` when any extracted top-level element equals `item` under ordinary KatLang value semantics, otherwise `0`; sequence values stay intact and search is top-level only |
| `first` | `first(values...)` or `collection.first` — return the first top-level element unchanged; sequence values stay intact and the sequence must be non-empty |
| `last` | `last(values...)` or `collection.last` — return the last top-level element unchanged; sequence values stay intact and the sequence must be non-empty |
| `distinct` | `distinct(values...)` or `collection.distinct` — remove later duplicate top-level elements while preserving first-occurrence order; sequence values stay intact, duplicate detection follows KatLang value semantics, and a single kept element is returned as that element itself |
| `take` | `take(values..., count)` or `collection.take(count)` — keep the first `count` top-level elements unchanged; non-positive counts return empty, sequence values stay intact, and a single kept element is returned as that element itself |
| `skip` | `skip(values..., count)` or `collection.skip(count)` — drop the first `count` top-level elements; non-positive counts keep the original sequence, sequence values stay intact, and a single remaining element is returned as that element itself |
| `min` | `min(values...)` or `collection.min` — find the smallest top-level numeric element; the sequence must be non-empty and sequence values are not flattened |
| `max` | `max(values...)` or `collection.max` — find the largest top-level numeric element; the sequence must be non-empty and sequence values are not flattened |
| `sum` | `sum(values...)` or `collection.sum` — add top-level numeric elements; each element must be a single atomic numeric value and sequence values are not flattened |
| `avg` | `avg(values...)` or `collection.avg` — average top-level numeric elements and return the decimal arithmetic mean (total divided by count); the sequence must be non-empty, each element must be a single atomic numeric value, and sequence values are not flattened |
| `reduce` | `reduce(values..., reducer, initial)` or `collection.reduce(reducer, initial)` — fold left over top-level elements; the current item behaves like `S:i`, normal accumulator parameters receive one structural state value, top-level variadic accumulator parameters receive state slots, and the reducer must return exactly one accumulator value |
| `atoms` | `atoms(value)` — recursively flatten to numeric atoms |
| `string` | `value.string` — value intrinsic that converts an atomic numeric result to a first-class string value; non-numeric receivers (strings, sequence values) are errors |
| `load` | `Name = load('url')` — load external algorithm |
| `open` | `open target` — import public properties into scope |
| `public` | `public Prop = ...` or `public Prop(pattern) = ...` — expose property to callers |
| `Output` | `Output = expr` — explicit output declaration |
| `Math` | Built-in namespace for constants and functions |
