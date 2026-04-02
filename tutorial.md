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
   - [Algorithm Length](#algorithm-length)
   - [Output Selection](#output-selection)
   - [Extension Dot-Call Syntax](#extension-dot-call-syntax)
   - [Name Resolution](#name-resolution)
6. [Parameters](#parameters)
   - [Reordering Parameters with Grace~ operator](#reordering-parameters-with-grace-operator)
7. [Conditionals](#conditionals)
8. [Repetition](#repetition)
   - [Fixed Loop: `repeat`](#fixed-loop-repeat)
   - [Conditional Loop: `while`](#conditional-loop-while)
9. [Practical Examples](#practical-examples)
   - [Reusable Calculation with Parameters](#reusable-calculation-with-parameters)
   - [Multi-Output Example](#multi-output-example)
   - [Loop-Based Example: Sum of a List](#loop-based-example-sum-of-a-list)
   - [Fibonacci Sequence](#fibonacci-sequence)
10. [Higher-Order Algorithms](#higher-order-algorithms)
    - [Algorithm as Argument](#algorithm-as-argument)
    - [Parametrized vs non-parametrized algorithms](#parametrized-vs-non-parametrized-algorithms)
11. [Structural Composition with semicolon operator](#structural-composition-with-semicolon-operator)
12. [Atoms](#atoms)
13. [Conditional Algorithms (`when`)](#conditional-algorithms-when)
    - [Basic Pattern Matching](#basic-pattern-matching)
    - [The K Combinator: Ignoring a Parameter](#the-k-combinator-ignoring-a-parameter)
    - [Mixing Literals and Variables](#mixing-literals-and-variables)
    - [Nested Group Patterns](#nested-group-patterns)
    - [Non-Exhaustive Patterns](#non-exhaustive-patterns)
14. [Loading and `open`](#loading-and-open)
    - [Loading External Algorithms](#loading-external-algorithms)
    - [`open`: Import Properties Directly](#open-import-properties-directly)
    - [Visibility](#visibility)
15. [Pitfalls](#pitfalls)
16. [Full Reference](#full-reference)
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

Because comparisons return `1` or `0`, logical operators compose naturally with them.

```
x > 5 and x < 10
```

When called with `x = 7` this produces `1`.

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

For simple values the result looks the same, but the distinction matters when composing algorithms — see [Structural Composition with `;`](#structural-composition-with-semicolon operator).

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

Every algorithm produces its output in one of two ways.

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

`Output = expr` is reserved syntax, not a regular property assignment. An algorithm may use it at most once, and you cannot mix it with implicit output in the same algorithm. The name `Output` in assignment position is reserved — you cannot define a property named `Output`.

### Algorithm Length

Every algorithm exposes a `.length` property that returns the number of output expressions in its definition.

```
Pair = 10, 20
Triple = 1, 2, 3

Pair.length
Triple.length
(100, 200, 300).length
```

**Results:**
```
2
3
3
```

This is useful when iterating or when you need to know how many values an algorithm produces.

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
Outer = {
    X = 1
    Inner = {
        Y = 2
        // X is found at level 2 (parent chain)
        // Y is found at level 1 (local)
        X + Y
    }
    Inner
}
Outer
```

**Result:** `3`

In this example, `Y` is found immediately in `Inner`, because it is local. `X` is not local to `Inner`, so KatLang continues to the parent chain and finds `X` in `Outer`.

Local properties always win. If the same name exists both locally and in a parent, the local one is used:

```
Outer = {
    X = 10
    Inner = {
        X = 99
        X
    }
    Inner
}
Outer
```

**Result:** `99`

Here `Inner.X` hides `Outer.X`, so the result is `99`.

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

Sometimes the natural reading order of parameters in a definition does not match the intended calling convention. The `~` operator (Grace) shifts a parameter's position.

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

`if` is a builtin algorithm that comes in two forms.

**Three-argument form** — `if(condition, whenTrue, whenFalse)` — always returns a value:

```
if(3 > 2, 1, 0)
if(1 > 2, 1, 0)
```

**Results:**
```
1
0
```

**Two-argument form** — `if(condition, value)` — returns `value` when true. When the condition is false, the expression **produces no value** — it simply disappears from the output.

This is not an error. If a binary operator like `+` loses its right operand this way, it returns the left operand unchanged:

```
10 + if(1 == 1, 5)
10 + if(1 == 2, 5)
```

**Results:**
```
15
10
```

In the second line, `if(1 == 2, 5)` vanishes, so `10 +` has no right operand and returns `10`.

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

For multi-case dispatch based on patterns, see [Conditional Algorithms (`when`)](#conditional-algorithms-when).

---

## Repetition

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
Sum = Algo.while(999, 0) : 1
Sum
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

// Call and get both outputs:
Circle(5)

// Pick just the area (index 0):
Circle(5) : 0
```

**Results:**
```
78.539816339744830961566084582
31.415926535897932384626433833
78.539816339744830961566084582
```

### Loop-Based Example: Sum of a List

Compute the sum of all numbers in a multi-value property using `repeat`:

```
Numbers = 3, 5, 9, 1, 0, 6

// Step: advance index, accumulate Numbers[index]
Step = a + 1, sum + Numbers:a

// Repeat once per element, then select the accumulated sum:
repeat(Step, Numbers.length, 0, 0) : 1
```

**Result:** `24`

### Fibonacci Sequence

Compute the Nth Fibonacci number:

```
// State: (a, b) — consecutive Fibonacci numbers
Fib = b, a + b

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
(1, 2, 3).length
{1, 2, 3}.length
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
1
2
3
```

| Expression | Interpretation |
|---|---|
| `1, 2, 3` | Single algorithm producing 3 outputs |
| `1; 2, 3` | Left algorithm (1 output) combined with right algorithm (2 outputs) |

---

## Atoms

Algorithms in KatLang can produce structured, nested outputs — for example, a group inside a group. The `atoms` builtin strips away all of that structure (tuples, groups, nesting) and returns a flat list of plain numeric values.

```
A = 1, 2, 3
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

## Conditional Algorithms (`when`)

The `if` builtin handles simple branching. For algorithms that need to dispatch based on structure or select from many cases, KatLang provides **conditional algorithms** — a form of pattern matching. A conditional algorithm is defined by writing multiple branches with the `when` keyword, each specifying a pattern to match against the arguments.

### Basic Pattern Matching

Each branch is declared as `Name when (pattern) = body`. Branches are tried top to bottom — the first match wins.

```
Sign when (1) = 100
Sign when (-1) = -100
Sign when (x) = 0

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

### The K Combinator: Ignoring a Parameter

A classic problem in functional programming is the **K combinator** — an algorithm that accepts two arguments and returns only the first, discarding the second. In many languages this requires special syntax for unused parameters.

In KatLang, a variable in a pattern binds the argument but does not need to be used in the body. This naturally solves the K combinator:

```
K when (a, b) = a

K(1, 2)
K(42, 999)
```

**Results:**
```
1
42
```

The parameter `b` is bound by the pattern but never referenced in the body — it is simply ignored. This is the idiomatic way to accept and discard arguments in KatLang.

### Mixing Literals and Variables

Branches can combine literal matches with variable bindings to create dispatch tables:

```
Else when (1, a, b) = a
Else when (0, a, b) = b

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

Parentheses inside a pattern denote a **group** — a tuple of a specific length. This lets you match nested structure:

```
Get when (1, (a, b)) = a
Get when (2, (a, b)) = b

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
K when (a, b) = a

// b binds to the entire tuple (2, 3):
K(1, (2, 3))
```

**Result:** `1`

But a parenthesized single variable `(b)` is a 1-element group pattern — it only matches a single value, not a multi-element tuple:

```
// (b) does not match (2, 3) because arities differ:
Strict when (a, (b)) = a
Strict(1, (2, 3))
```

This fails with a "no matching branch" error because `(b)` expects exactly one element.

### Non-Exhaustive Patterns

If no branch matches the provided arguments, evaluation fails with an error. There is no implicit default — add a catch-all branch if you want to handle all cases:

```
F when (1) = 100
F when (x) = 0

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
Lib = (
    public Pi = 3.14159
    public Double = x * 2
)
open Lib

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

By default, properties are private — accessible within their own algorithm and its children, but not visible to outside callers who load or open the algorithm. Marking a property `public` exposes it externally.

```
// In a library algorithm:
public Area = r * r * Math.Pi
Helper = Area / 2   // private — not visible to callers
```

Only `public` properties are exposed through `load` and `open`.

---

## Pitfalls

- **Decimal precision limits:** KatLang uses fixed-precision decimal arithmetic. Extremely large numbers or deeply nested calculations may hit precision boundaries.
- **Trigonometric precision:** `Math.Sin(Math.Pi)` does not produce exact `0` — it returns a very small number close to zero. This is inherent to decimal approximation of π.
- **Parameter order surprises:** parameter order is determined by first appearance reading left to right. If your expression reads `b - a`, the first parameter is `b`, not `a`. Use Grace (`~`) to override when needed.
- **`if(cond, value)` disappearing:** the two-argument `if` produces no output when the condition is false. If you expect a value in all cases, use the three-argument form `if(cond, a, b)`.
- **`()` vs `{}` confusion:** `(expr)` groups an expression in the current scope. `{expr}` creates a new algorithm with its own parameters. Passing `(a + 1)` as an argument doesn't create a callable — it evaluates `a + 1` immediately in the enclosing scope.
- **Ignoring a parameter:** there is no special "ignore" syntax for implicit parameters — every undeclared name becomes a required argument. If you want to accept and discard an argument, use a `when` pattern. Bind the unwanted argument to a variable in the pattern, then simply don't reference it in the body:

  ```
  // Wrong — no way to declare 'b' to discard; calling with two args fails:
  KeepFirst = a
  KeepFirst(42, 999)  // error: too many arguments

  // Right — 'b' is bound by the pattern but never used:
  KeepFirst when (a, b) = a
  KeepFirst(42, 999) // Result: 42
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
| `==`, `!=` | Equality, inequality | |
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

### Builtin Algorithms and Keywords

| Keyword | Usage |
|---|---|
| `if` | `if(cond, a, b)` or `if(cond, a)` |
| `when` | `Name when (pattern) = body` — conditional branch |
| `while` | `step.while(init...)` or `while(step, init)` |
| `repeat` | `step.repeat(n, init...)` or `repeat(step, n, init)` |
| `atoms` | `atoms(alg)` — flatten to individual values |
| `load` | `Name = load('url')` — load external algorithm |
| `open` | `open target` — import public properties into scope |
| `public` | `public Prop = ...` — expose property to callers |
| `Output` | `Output = expr` — explicit output declaration |
| `Math` | Built-in namespace for constants and functions |
