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
4. [Multiple Outputs](#multiple-outputs)
5. [Properties](#properties)
   - [Implicit and Explicit Output](#implicit-and-explicit-output)
    - [Algorithm Arity](#algorithm-arity)
   - [Output Selection](#output-selection)
   - [Extension Dot-Call Syntax](#extension-dot-call-syntax)
   - [Name Resolution](#name-resolution)
6. [String Literals](#string-literals)
   - [String Equality](#string-equality)
   - [Number to String Conversion](#number-to-string-conversion)
7. [Parameters](#parameters)
   - [Reordering Parameters with Grace~ operator](#reordering-parameters-with-grace-operator)
8. [Conditionals](#conditionals)
9. [Repetition](#repetition)
    - [Inclusive Sequences: `range`](#inclusive-sequences-range)
    - [Selection: `filter`](#selection-filter)
    - [Mapping: `map`](#mapping-map)
    - [Counting: `count`](#counting-count)
    - [First Element: `first`](#first-element-first)
    - [Last Element: `last`](#last-element-last)
    - [Distinct: `distinct`](#distinct-distinct)
    - [Take Prefix: `take`](#take-prefix-take)
    - [Skip Prefix: `skip`](#skip-prefix-skip)
    - [Minimum: `min`](#minimum-min)
    - [Maximum: `max`](#maximum-max)
    - [Summation: `sum`](#summation-sum)
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
12. [Structural Composition with semicolon operator](#structural-composition-with-semicolon-operator)
13. [Atoms](#atoms)
14. [Conditional Algorithms](#conditional-algorithms)
    - [Basic Pattern Matching](#basic-pattern-matching)
    - [Nested Group Patterns](#nested-group-patterns)
    - [The K Combinator: Ignoring a Parameter](#the-k-combinator-ignoring-a-parameter)
    - [Mixing Literals and Variables](#mixing-literals-and-variables)
    - [String Patterns](#string-patterns)
    - [Non-Exhaustive Patterns](#non-exhaustive-patterns)
15. [Loading and `open`](#loading-and-open)
    - [Loading External Algorithms](#loading-external-algorithms)
    - [`open`: Import Properties Directly](#open-import-properties-directly)
    - [Visibility](#visibility)
16. [Pitfalls](#pitfalls)
17. [Full Reference](#full-reference)
    - [Operators](#operators)
    - [Builtin Algorithms and Keywords](#builtin-algorithms-and-keywords)

---

## What KatLang Is

KatLang is a language designed for calculations. You write expressions, give them names, and combine them — that's it.

One thing to know upfront: **everything is an algorithm**. A bare number like `42` is an algorithm that produces one value. A list like `1, 2, 3` produces three values. A named formula is an algorithm that belongs to its parent. There are no statements or side effects — just algorithms that evaluate to sequences of values.

And you don't declare parameters — KatLang figures them out. Any name you use that isn't defined as a property automatically becomes a parameter.

---

## Your First KatLang Program

The simplest program is just an arithmetic expression:

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

Names defined with `=` are called **properties**. If a name isn't defined, KatLang treats it as a **parameter** — an input the caller must supply:

```
Tax = price * 0.2
Tax(50)
```

**Result:** `10`

Here `price` appears without a definition, so it becomes a parameter. By convention, property names use PascalCase and parameter names use camelCase — but for physics or other specialized domains, prefer the naming that is standard in the field (e.g. `v = s / t` where `v` follows physics notation for velocity, rather than the conventional `V = s / t`).

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
3.3333333333333333
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
| `Math.Round(x)` | Round to nearest integer (banker's rounding) |
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
| `Math.Pow(x, y)` | x raised to power y (floating-point) |
| `Math.Log(x, y)` | Logarithm of x with base y |

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

---

## Multiple Outputs

A KatLang algorithm can produce more than one value. Use commas to list multiple outputs:

```
10, 20, 30
```

**Results:**
```
10
20
30
```

Because the parser treats all whitespace uniformly (spaces, newlines, tabs are equivalent), any whitespace also separates expressions. Prefer commas for clarity:

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

You can mix commas and newlines freely:

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

**Comma vs. semicolon:** these serve different purposes.

| Syntax | Meaning |
|---|---|
| `1, 2` | Single algorithm with 2 outputs |
| `1; 2` | Two separate algorithms, structurally combined |

For simple values the result looks the same, but the distinction matters when composing algorithms — see [Structural Composition with `;`](#structural-composition-with-semicolon-operator).

---

## Properties

An algorithm can be given a name using `=`. Named algorithms are called **properties**, because a named algorithm always belongs to its parent algorithm. By convention, property names use PascalCase.

```
// Define a property:
Answer = 42

// Using () or just the name are equivalent when there are no arguments:
Answer()
Answer
```

**Results:**
```
42
42
```

Properties can themselves produce multiple outputs:

```
Coordinates = 10, 20
Coordinates
```

**Results:**
```
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

`Output = expr` is reserved syntax, not a regular property assignment. An algorithm may use it at most once, and you cannot mix it with implicit output in the same algorithm. The name `Output` is reserved in definition position: `Output(x) = ...` and multi-branch `Output` definitions are invalid. If you need explicit parameters or clause branches, declare them on the enclosing algorithm instead. If you declare explicit parameters on the enclosing algorithm, that algorithm must define output. External qualified access is also invalid: `Algo.Output` and `Algo.Output(...)` are rejected because `Output` is not a public property surface.

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

An algorithm with no output is still valid when you use it structurally as a plain container or namespace-like group:

```
A = {
    X = 1
}

A.X
```

**Result:** `1`

Using `A` itself where a concrete value is required is an error, because `A` does not define output. Do not add algorithm-level explicit parameters to this container form unless the algorithm also defines output.

### Algorithm Arity

Every algorithm exposes an `.arity` property that reports how many top-level output slots it has structurally.

- `arity` = how many top-level output slots the expression/algorithm has structurally
- `count` = how many top-level output values that expression denotes when evaluated

```
T = (1, 2, 3)
T.arity
T.count

A = 1, 2, 3
A.arity
A.count
```

**Results:**
```
1
3
3
3
```

`T` has one structural output slot whose value denotes three top-level outputs when evaluated. `A` has three structural output slots and also denotes three top-level values when evaluated.

Use `.arity` when you care about structural output shape. Use `.count` when you care about denoted top-level values.

### Output Selection

When an algorithm produces multiple outputs, the `:` operator selects one by its zero-based index.

```
Nums = 10, 20, 30, 40, 50

// Select the third value (index 2):
Nums:2
```

**Result:** `30`

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

**Resolution rule:** KatLang first checks whether the property name exists as a structural property of the target algorithm. If found, it calls that property. If not found, it falls back to lexical lookup in the current scope — this is how extension-style calls work.

### Name Resolution

Name resolution is especially important in KatLang because it may behave differently from what users expect from other languages. KatLang uses a fixed search order called **ownership-first lookup**. The idea is simple: a name belongs first to the algorithm that owns it, then to its parent structure, and only after that to anything brought in through `open`.

When KatLang sees a name, it checks these places in order and stops at the first match:

1. **Local properties** — properties defined in the current algorithm (any visibility).
2. **Parent chain** — properties defined in enclosing algorithms, walking upward through the nesting structure. In this step, KatLang checks only structural properties; parent-level opens are not considered yet.
3. **Opens** — public properties from `open` targets, checked for the current algorithm first and then upward through the parent chain.

If the name is not found at any of these levels, KatLang treats it as an implicit parameter (see [Parameters](#parameters)).

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
'123'
'0'
'-5'
'1.20'
```

This also works on named properties:

```
A = 42
A.string
```

**Result:**
```
'42'
```

The result is a real KatLang string value — identical to a single-quoted string literal. For example, `123.string == '123'` evaluates to `1` (true).

Only numeric values are supported. Applying `.string` to a non-numeric value (such as a string or a multi-output group) produces an error.

---

## Parameters

**Rule:** any identifier that is not defined as a property in the current algorithm becomes an implicit parameter.

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

`if` is a builtin algorithm and always takes exactly three arguments: `if(condition, whenTrue, whenFalse)`.

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
1
2
3
4
5

5
4
3
2
1

3
```

### Selection: `filter`

`filter(...items, predicate)` walks the sequence from left to right and keeps only the top-level elements whose predicate result is exactly one atomic numeric value.

- Kept elements stay in their original order
- Rejected elements disappear completely; no placeholders are inserted
- Grouped elements are passed to the predicate and preserved as whole elements
- Predicate result must be exactly one atomic numeric value: `0` rejects, nonzero keeps
- Grouped, multi-output, empty, or string predicate results are errors

```
IsEven = x mod 2 == 0
filter(1, 2, range(3, 6), IsEven)

IsEven = x mod 2 == 0
filter(range(1, 10), IsEven)

KeepPair(tag, value) = tag mod 2 == 0
filter(((1, 10), (2, 20), (3, 30), (4, 40)), KeepPair)
```

**Results:**
```
2
4
6

2
4
6
8
10

(2, 20)
(4, 40)
```

If every predicate result is `0`, `filter` returns an empty collection.
Predicate results such as `0, 999`, `(1, 0)`, or `x.string` are invalid because `filter` does not derive truth from grouped or multi-output results.
The same extraction rule applies to grouped wrapper outputs: `filter((1, 2), predicate)` and `Values = (1, 2); filter(Values, predicate)` each treat `(1, 2)` as one top-level item.

### Mapping: `map`

`map(...items, transform)` walks the sequence from left to right and replaces each top-level element with `transform(element)`.

- The transform receives each whole top-level element
- The transform must return exactly one mapped element
- One atomic value is valid
- One grouped value such as `(x, x * x)` is also valid
- Empty or multi-output transform results are errors
- Output order and element count are preserved
- Empty collections stay empty

Both call styles are supported: `map(...items, transform)` and `collection.map(transform)`.

```
Double = x * 2
map(1, range(2, 4), Double)

Double = x * 2
range(1, 5).map(Double)

PairWithSquare(x) = (x, x * x)
map(range(1, 3), PairWithSquare)
```

**Results:**
```
2
4
6
8

2
4
6
8
10

(1, 1)
(2, 4)
(3, 9)
```

Grouped input elements are passed to the transform as whole values, so `Swap((a, b)) = (b, a)` works on grouped pairs without flattening them.
The same rule applies to grouped wrapper outputs: `map((1, 2), transform)` and `Values = (1, 2); map(Values, transform)` each call `transform` once with the grouped value.

### Sequence Inputs

`filter`, `map`, `order`, `orderDesc`, `count`, `first`, `last`, `distinct`, `take`, `skip`, `min`, `max`, `sum`, `avg`, and `reduce` all consume top-level items.

- They always consume counted top-level items emitted by each sequence argument
- The same extraction rule applies whether there is one sequence argument or many
- An argument such as `Values` where `Values = 3, 4, 2` contributes three items
- A grouped argument such as `(1, 2)` contributes one grouped item, even when it is the only sequence argument
- A helper such as `Wrapped` where `Wrapped = (1, 2, 3)` also contributes one grouped item rather than three separate numeric items
- Nested grouped values are not recursively flattened unless a builtin explicitly says so, such as `atoms`
- `distinct` compares those extracted top-level items using ordinary KatLang value semantics: atoms by numeric value, strings by exact string value, and grouped values structurally by grouped contents
- `take` and `skip` keep their count first in direct-call surface syntax (`take(2, Values)` / `skip(2, Values)`), but they still consume the same extracted top-level items as the other sequence builtins

This is why `order(3, 4, 2, 1)` works directly, while `order((1, 2, 3))` and `order((1, 2), (3, 4))` are invalid: grouped values remain grouped top-level items instead of being flattened into sortable atoms.

### Ordering: `order` and `orderDesc`

`order(...items)` sorts top-level numeric items in ascending order.
`orderDesc(...items)` sorts the same kind of top-level items in descending order.

- Both builtins evaluate the full collection eagerly before sorting
- Duplicates are preserved; there is no implicit distinct or unique step, so use `distinct` separately when deduplication is required
- The result is still an ordinary KatLang multi-output sequence
- Each top-level element must be exactly one atomic numeric value
- Grouped values are not flattened or inspected recursively
- Strings and mixed-type collections are invalid
- Empty collections stay empty

Both call styles are supported: `order(...items)` / `orderDesc(...items)` and `collection.order` / `collection.orderDesc`.

```
order(3, 4, 2, 1, 3, 3)

Values = 3, 4, 2, 1, 3, 3
Values.order
Values.orderDesc

order(Values, 0, 5)

range(5, 1).order
```

**Results:**
```
1
0
1
2
3
3
3
4
5

2
3
3
3
4

4
3
3
2
1

1
2
3
4
5
```

Applying `order` or `orderDesc` to a collection like `(1, 'hello')` is invalid because KatLang does not define a loose mixed-type ordering rule. `order((1, 2, 3))` is invalid because the single grouped argument remains one grouped top-level item, not three sortable atoms. `order((1, 2), (3, 4))` is also invalid, because each grouped argument is a separate top-level item and grouped items are not sortable atoms.

### Counting: `count`

`count(...items)` returns how many top-level values the evaluated sequence denotes.

Use `.arity` for structural top-level output slots. Use `count` for denotational top-level value count after evaluation.

- Each atom, string, or grouped value counts as one top-level element
- Grouped values are not flattened or inspected recursively
- Empty collections return `0`

Both call styles are supported: `count(...items)` and `collection.count`.

```
count(range(1, 5))

count(10, 20, 30)

IsEven = x mod 2 == 0
range(1, 10).filter(IsEven).count

count((1, 2), (3, 4))
```

**Results:**
```
5

3

5

2
```

`count(5)` and `count('hello')` both return `1`, because an atomic value is treated as a one-element collection.
`count((1, 2, 3))` also returns `1`, and `Values = (1, 2, 3); count(Values)` does the same because the grouped wrapper output is still one top-level item. By contrast, `Values = 1, 2, 3; count(Values)` returns `3`.

### First Element: `first`

`first(...items)` returns the first top-level value in the evaluated sequence, unchanged.

- The collection must be non-empty
- Atoms, strings, and grouped values each count as one top-level element
- Grouped values are preserved whole and are not flattened

Both call styles are supported: `first(...items)` and `collection.first`.

```
first(range(1, 5))

first(4, 5, 6)

first((1, 2), (3, 4))
```

**Results:**
```
1

4

(1, 2)
```

Applying `first` to an empty collection is invalid because `first` requires at least one top-level element.
`first((1, 2, 3))` and `Values = (1, 2, 3); first(Values)` both return `(1, 2, 3)` unchanged because that grouped value is one top-level item.

### Last Element: `last`

`last(...items)` returns the last top-level value in the evaluated sequence, unchanged.

- The collection must be non-empty
- Atoms, strings, and grouped values each count as one top-level element
- Grouped values are preserved whole and are not flattened

Both call styles are supported: `last(...items)` and `collection.last`.

```
last(range(1, 5))

last(4, 5, 6)

last((1, 2), (3, 4))
```

**Results:**
```
5

6

(3, 4)
```

Applying `last` to an empty collection is invalid because `last` requires at least one top-level element.
`last((1, 2, 3))` and `Values = (1, 2, 3); last(Values)` both return `(1, 2, 3)` unchanged for the same reason.

### Distinct: `distinct`

`distinct(...items)` returns the extracted top-level sequence items with later duplicates removed.

- The original left-to-right order of first occurrence is preserved
- Atoms compare by numeric value, strings by exact string value, and grouped values structurally by grouped contents
- Grouped values stay whole and are not flattened
- Empty collections stay empty

Both call styles are supported: `distinct(...items)` and `collection.distinct`.

```
distinct(3, 1, 3, 2, 1, 2)

distinct((1, 2), (1, 2), (3, 4))

Values = 3, 1, 3, 2, 1, 2
Values.distinct
```

**Results:**
```
3
1
2

(1, 2)
(3, 4)

3
1
2
```

`Values = ((1, 2), (1, 2), (3, 4)); distinct(Values)` returns that single grouped value unchanged because the outer grouped wrapper is one top-level item. By contrast, `Values = (1, 2), (1, 2), (3, 4); distinct(Values)` removes the duplicate grouped top-level item and returns two grouped outputs.

### Take Prefix: `take`

`take(count, ...items)` returns the first `count` top-level values in the evaluated sequence, unchanged.

- The count must evaluate to exactly one whole-number value
- `count <= 0` returns an empty sequence
- Counts larger than the sequence length return the whole sequence
- Grouped values are preserved whole and are not flattened

Both call styles are supported: `take(count, ...items)` and `collection.take(count)`.

```
take(3, 1, 2, 3, 4, 5)

take(1, (1, 2), (3, 4))

range(1, 5).take(2)
```

**Results:**
```
1
2
3

(1, 2)

1
2
```

`take(0, 1, 2, 3)` and `take(-2, 1, 2, 3)` both return an empty result. `take((1, 2, 3), 4, 5)` is invalid because the count must be exactly one whole-number value, not a grouped item.

### Skip Prefix: `skip`

`skip(count, ...items)` returns the evaluated sequence after skipping the first `count` top-level values.

- The count must evaluate to exactly one whole-number value
- `count <= 0` returns the original sequence unchanged
- Counts larger than the sequence length return an empty sequence
- Grouped values are preserved whole and are not flattened

Both call styles are supported: `skip(count, ...items)` and `collection.skip(count)`.

```
skip(3, 1, 2, 3, 4, 5)

skip(1, (1, 2), (3, 4))

range(1, 5).skip(2)
```

**Results:**
```
4
5

(3, 4)

3
4
5
```

`skip(0, 1, 2, 3)` and `skip(-2, 1, 2, 3)` both return `1, 2, 3`. `skip('hello', 1, 2)` is invalid because the count must be exactly one whole-number value.

### Minimum: `min`

`min(...items)` returns the smallest top-level numeric element in a sequence.

- The collection must be non-empty
- Each top-level element must be exactly one atomic numeric value
- Grouped values are not flattened or inspected recursively
- Strings are invalid

Both call styles are supported: `min(...items)` and `collection.min`.

```
min(10, 4, 7)

min(range(1, 5))

IsEven = x mod 2 == 0
range(1, 10).filter(IsEven).min
```

**Results:**
```
4

1

2
```

Applying `min` to an empty collection is invalid because `min` requires at least one top-level numeric element. A collection such as `((1, 2), (3, 4))` is also invalid because grouped elements are not flattened before comparison. The same is true for a grouped wrapper output such as `Values = (1, 2, 3); min(Values)`: `Values` contributes one grouped item, not three numeric items.

### Maximum: `max`

`max(...items)` returns the largest top-level numeric element in a sequence.

- The collection must be non-empty
- Each top-level element must be exactly one atomic numeric value
- Grouped values are not flattened or inspected recursively
- Strings are invalid

Both call styles are supported: `max(...items)` and `collection.max`.

```
max(10, 4, 7)

max(range(1, 5))

IsEven = x mod 2 == 0
range(1, 10).filter(IsEven).max
```

**Results:**
```
10

5

10
```

Applying `max` to an empty collection is invalid because `max` requires at least one top-level numeric element. A collection such as `((1, 2), (3, 4))` is also invalid because grouped elements are not flattened before comparison. The same is true for a grouped wrapper output such as `Values = (1, 2, 3); max(Values)`.

### Summation: `sum`

`sum(...items)` adds the top-level numeric elements of a sequence from left to right and returns one numeric result.

- Each top-level element must be exactly one atomic numeric value
- Empty collections return `0`
- A single numeric value is treated as a one-element collection
- Grouped values are invalid and are not flattened
- Strings are invalid

Both call styles are supported: `sum(...items)` and `collection.sum`.

```
sum(10, 20, 30)

sum(range(1, 5))

IsEven = x mod 2 == 0
range(1, 10).filter(IsEven).sum
```

**Results:**
```
60

15

30
```

Applying `sum` to an empty collection returns `0`. A collection such as `((1, 2), (3, 4))` is invalid because `sum` does not flatten grouped elements before adding. The same is true for `sum((1, 2, 3))` or `Values = (1, 2, 3); sum(Values)`: the grouped value stays one non-atomic top-level item.

### Average: `avg`

`avg(...items)` averages the top-level numeric elements of a sequence and returns one numeric result.

- The collection must be non-empty
- Each top-level element must be exactly one atomic numeric value
- A single numeric value is treated as a one-element collection
- The final quotient follows KatLang's current Lean integer semantics, so non-exact averages use floor division, for example `avg(1, 2)` returns `1`
- Grouped values are invalid and are not flattened
- Strings are invalid

Both call styles are supported: `avg(...items)` and `collection.avg`.

```
avg(10, 20, 30)

avg(range(1, 5))

Square = x * x
range(1, 4).map(Square).avg

avg(1, 2)
```

**Results:**
```
20

3

7

1
```

Applying `avg` to an empty collection is invalid because `avg` requires at least one top-level numeric element. A collection such as `((1, 2), (3, 4))` is also invalid because `avg` does not flatten grouped elements before averaging. The same is true for a grouped wrapper output such as `Values = (1, 2, 3); avg(Values)`.

### Reduction: `reduce`

`reduce(...items, step, initial)` walks the sequence from left to right and threads an accumulator through the top-level items.

- `step(element, accumulator)` receives each whole top-level element and the current accumulator
- The step must return exactly one next accumulator value
- Grouped input elements stay whole
- Grouped accumulator values are allowed when they are returned as one grouped value
- Empty collections return `initial` unchanged

Both call styles are supported: `reduce(...items, step, initial)` and `collection.reduce(step, initial)`.

```
Add = x + total
reduce(1, 2, range(3, 4), Add, 0)

Add = x + total
range(1, 5).reduce(Add, 0)

Stats(x, (acc, counter)) = (x + acc, counter + 1)
range(1, 4).reduce(Stats, (0, 0))
```

**Results:**
```
10

15

(10, 4)
```

No wrapper helper is required for grouped accumulators: a parenthesized tuple such as `(a, b)` is one grouped accumulator value.
With the same extraction rule, `reduce((1, 2), step, initial)` and `Values = (1, 2); reduce(Values, step, initial)` each call `step` once with the grouped value. They do not split that group into separate iterations.
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
37
```

### Multi-Output Example

Computing both area and circumference of a circle:

```
Circle = r * r * Math.Pi, 2 * r * Math.Pi

// Call to get area and circumference as a group:
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
repeat(Step, Numbers.arity, 0, 0) : 1
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

If a property expects multiple arguments, you can pass a multi-output algorithm in place of the argument list. KatLang unpacks the algorithm's outputs and passes them individually.

```
Sum3 = a + b + c
Input = 1, 2, 3

// Input produces 3 outputs — they are unpacked into a, b, c:
Sum3(Input)
```

**Result:** `6`

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

### Parametrized vs non-parametrized algorithms

The distinction between braces and parentheses is critical:

| Syntax | Meaning |
|---|---|
| `( ... )` | Non-parametrized grouping — evaluated in the enclosing scope; no new parameter scope |
| `{ ... }` | Parametrized algorithm value — creates a new scope with its own inferred parameters |
| `{a + 1}` | Parametrized algorithm with parameter `a`, passable as an argument |

`{}` braces mark the passed algorithm as **parametrized** — it owns its own parameters (`a` in the example above). A **non-parametrized** `()` expression has no parameter scope of its own — any free names are absorbed by the enclosing algorithm instead.

When a block has no free parameters, `{}` and `()` produce the same result:

```
(1, 2, 3).count
{1, 2, 3}.count
```

**Results:**
```
3
3
```

---

## Structural Composition with semicolon operator

The `;` operator joins two algorithms into one, concatenating their output sequences. This is different from comma: comma separates outputs *within* a single algorithm, while `;` combines two *separate* algorithms into a composite.

Why does this matter? When an algorithm has properties and parameters, the `;` boundary preserves each side's scope. Each algorithm fragment keeps its own parameter inference and property definitions.

```
First = 1, 2
Second = 3, 4

First; Second
```

**Results:**
```
1
2
3
4
```

Inline combining works similarly:

```
1; 2, 3
```

**Results:**
```
(1, 2)
3
```

| Expression | Interpretation |
|---|---|
| `1, 2, 3` | Single algorithm producing 3 outputs |
| `1; 2, 3` | Parsed as `(1; 2), 3` — the combine `1; 2` produces a group `(1, 2)`, followed by a separate output `3` |

---

## Atoms

Algorithms in KatLang can produce structured, nested outputs — for example, a group inside a group. The `atoms` builtin strips away all of that structure (tuples, groups, nesting) and returns a flat list of plain numeric values.

```
A = 1; 2, 3
atoms(A)
```

**Results:**
```
1
2
3
```

This is useful when you need to treat a complex algorithm's output as a simple sequence of numbers, regardless of how the values were originally grouped.

---

## Conditional Algorithms

The `if` builtin handles simple branching. For algorithms that need to dispatch based on structure or select from many cases, KatLang provides **conditional algorithms** — a form of pattern matching. A conditional algorithm is defined by writing multiple clause-style branches, each specifying a pattern to match against the arguments.

### Basic Pattern Matching

Each branch is declared as `Name(pattern) = body`. On the left-hand side of `=` in definition context, `Name(...)` is not a call expression — it is pattern syntax for a conditional algorithm branch. Branches are tried top to bottom — the first match wins.

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

### Nested Group Patterns

Parentheses inside a pattern denote a **group** — a tuple of a specific arity. This lets you match nested structure:

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

Single-branch clauses whose top-level pattern is a plain binder list elaborate as ordinary algorithms, even at arity 1, so higher-order arguments stay callable just like ordinary parameters. For example:

```
Apply(f) = f(4)
Double(x) = x * 2

Apply(Double)
```

**Result:** `8`

The same rule applies to larger plain binder lists:

```
Apply(x, f) = f(x)
Increment = y + 1

Apply(9, Increment)
```

**Result:** `10`

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

### Nested Group Patterns

Parentheses inside a pattern denote a **group** — a tuple of a specific arity. This lets you match nested structure:

```
Get(1, (a, b)) = a
Get(2, (a, b)) = b

Get(1, (10, 20))
Get(2, (10, 20))
```

**Results:**
```
10
20
```

A bare variable without parentheses matches anything, including a tuple:

```
K(a, b) = a

// b binds to the entire tuple (2, 3):
K(1, (2, 3))
```

**Result:** `1`

But a parenthesized single variable `(b)` is a 1-element group pattern — it only matches a single value, not a multi-element tuple:

```
// (b) does not match (2, 3) because arities differ:
Strict(a, (b)) = a
Strict(1, (2, 3))
```

This fails with a "no matching branch" error because `(b)` expects exactly one element.

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
2.4
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

Open multiple sources at once by separating them with commas:

```
open LibA, LibB
```

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
Helper = Area / 2   // private — not visible to callers
```

Only `public` exported properties are exposed through `load` and `open`.

---

## Pitfalls

- **Decimal precision limits:** KatLang uses fixed-precision decimal arithmetic. Extremely large numbers or deeply nested calculations may hit precision boundaries.
- **Trigonometric precision:** `Math.Sin(Math.Pi)` does not produce exact `0` — it returns a very small number close to zero. This is inherent to decimal approximation of π.
- **Parameter order surprises:** parameter order is determined by first appearance reading left to right. If your expression reads `b - a`, the first parameter is `b`, not `a`. Use Grace (`~`) to override when needed.
- **`if` arity:** builtin `if` always requires three arguments: `if(cond, a, b)`. There is no two-argument form.
- **`()` vs `{}` confusion:** `(expr)` groups an expression in the current scope. `{expr}` creates a new algorithm with its own parameters. Passing `(a + 1)` as an argument doesn't create a callable — it evaluates `a + 1` immediately in the enclosing scope.
- **Ignoring a parameter:** there is no special "ignore" syntax for implicit parameters — every undeclared name becomes a required argument. If you want to accept and discard an argument, use a conditional algorithm branch. Bind the unwanted argument to a variable in the pattern, then simply don't reference it in the body:

  ```
  // Wrong — no way to declare 'b' to discard; calling with two args fails:
  KeepFirst = a
  KeepFirst(42, 999)  // error: too many arguments

  // Right — 'b' is bound by the pattern but never used:
  KeepFirst(a, b) = a
  KeepFirst(42, 999) // Result: 42
  ```
- **Property redefinition:** defining the same property name twice is an error — properties are immutable bindings, not reassignable variables:

  ```
  A = 5
  A = 6  // error: Property 'A' is already defined
  ```

- **Duplicate branch patterns:** two conditional branches with match-equivalent patterns are rejected because the second branch would be unreachable under first-match semantics. Binder names don't matter — only the structure of the pattern:

  ```
  F(x) = x + 1
  F(y) = y + 2  // error: duplicate branch pattern
  ```

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
| `<`, `>`, `<=`, `>=` | Comparison (returns 1 or 0) | |
| `==`, `!=` | Equality, inequality (numbers and strings) | |
| `and` | Logical and | |
| `xor` | Logical exclusive or | |
| `or` | Logical or | Lowest |
| `not` | Logical negation (prefix) | — |
| `-` | Arithmetic negation (prefix) | — |
| `:` | Output selection (zero-based index) | Postfix |
| `.` | Dot-call / property access | Postfix |
| `;` | Structural composition (combine algorithms) | — |
| `~` (prefix) | Grace: move parameter one position earlier | — |
| `~` (postfix) | Grace: move parameter one position later | — |

### Builtin Algorithms, Intrinsics, and Keywords

| Keyword | Usage |
|---|---|
| `if` | `if(cond, a, b)` |
| `while` | `step.while(init...)` or `while(step, init)` |
| `repeat` | `step.repeat(n, init...)` or `repeat(step, n, init)` |
| `arity` | `expr.arity` — structural top-level output slot count without evaluation |
| `range` | `range(start, stop)` — inclusive integer sequence, ascending or descending |
| `filter` | `filter(...items, predicate)` or `collection.filter(predicate)` — keep top-level elements whose predicate returns exactly one atomic numeric value; grouped elements stay whole |
| `map` | `map(...items, transform)` or `collection.map(transform)` — transform top-level elements left to right; transform must return exactly one mapped element |
| `order` | `order(...items)` or `collection.order` — eagerly sort top-level numeric elements ascending; duplicates are preserved and grouped/string elements are invalid |
| `orderDesc` | `orderDesc(...items)` or `collection.orderDesc` — eagerly sort top-level numeric elements descending; duplicates are preserved and grouped/string elements are invalid |
| `count` | `count(...items)` or `collection.count` — denotational top-level value count after evaluation, without flattening grouped values |
| `first` | `first(...items)` or `collection.first` — return the first top-level element unchanged; grouped values stay grouped and the sequence must be non-empty |
| `last` | `last(...items)` or `collection.last` — return the last top-level element unchanged; grouped values stay grouped and the sequence must be non-empty |
| `distinct` | `distinct(...items)` or `collection.distinct` — remove later duplicate top-level elements while preserving first-occurrence order; grouped values stay grouped and duplicate detection follows KatLang value semantics |
| `take` | `take(count, ...items)` or `collection.take(count)` — keep the first `count` top-level elements unchanged; non-positive counts return empty and grouped values stay grouped |
| `skip` | `skip(count, ...items)` or `collection.skip(count)` — drop the first `count` top-level elements; non-positive counts keep the original sequence and grouped values stay grouped |
| `min` | `min(...items)` or `collection.min` — find the smallest top-level numeric element; the sequence must be non-empty and grouped values are not flattened |
| `max` | `max(...items)` or `collection.max` — find the largest top-level numeric element; the sequence must be non-empty and grouped values are not flattened |
| `sum` | `sum(...items)` or `collection.sum` — add top-level numeric elements; each element must be a single atomic numeric value and grouped values are not flattened |
| `avg` | `avg(...items)` or `collection.avg` — average top-level numeric elements using the current Lean integer quotient rule; the sequence must be non-empty, each element must be a single atomic numeric value, and grouped values are not flattened |
| `reduce` | `reduce(...items, step, initial)` or `collection.reduce(step, initial)` — fold left over top-level elements; step must return exactly one accumulator value |
| `atoms` | `atoms(alg)` — flatten to individual values |
| `load` | `Name = load('url')` — load external algorithm |
| `open` | `open target` — import public properties into scope |
| `public` | `public Prop = ...` — expose property to callers |
| `Output` | `Output = expr` — explicit output declaration |
| `Math` | Built-in namespace for constants and functions |
