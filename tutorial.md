# KatLang Tutorial

KatLang is a language for calculations. You write formulas, give them names, and combine them into larger calculations, and KatLang evaluates them with exact decimal arithmetic. This tutorial is a learning path: it starts with a single expression and builds up, chapter by chapter, to collections, algorithms that take other algorithms, pattern matching, and larger programs. Each chapter relies only on the chapters before it, so it reads best from beginning to end.

## Contents

1. [Getting Started](#getting-started)
2. [Numbers and Arithmetic](#numbers-and-arithmetic)
3. [Properties](#properties)
4. [Parameters](#parameters)
5. [Booleans and Decisions](#booleans-and-decisions)
6. [Text](#text)
7. [Dot Calls](#dot-calls)
8. [Sequences](#sequences)
9. [Lists](#lists)
10. [Algorithms as Values](#algorithms-as-values)
11. [Working with Collections](#working-with-collections)
12. [Collecting Parameters](#collecting-parameters)
13. [Deconstruction](#deconstruction)
14. [Loops](#loops)
15. [Pattern Matching](#pattern-matching)
16. [Organizing Programs](#organizing-programs)
17. [Layout and Common Pitfalls](#layout-and-common-pitfalls)
18. [Quick Reference](#quick-reference)

---

## Getting Started

### Running the Examples

Run the examples in the [KatLang playground](https://katlang.org), or with the `katlang` command-line tool, which evaluates a program given on the command line or stored in a file:

```text
katlang eval "2 + 3 * 4"
katlang run program.kat
```

Each example below is followed by its result: **Result** for one output, **Results** for several outputs in order, and **Result:** error for an example that is intentionally invalid. These results are checked automatically against the current implementation of KatLang.

### Your First Program

A program can be a single expression:

<!-- spec:first-program -->
```
2 + 3 * 4
```

**Result:** `14`

### Several Results

Every line of a program is an output row, and commas separate several outputs on one line:

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

```
1 + 1
2 + 2, 3 + 3
```

**Results:**
```
2
4
6
```

On one line the comma is required: `1 2` is an error, never two outputs.

### Comments

`#` starts a comment, which runs to the end of the line:

```
# Floor area of a 4 m by 3 m room
4 * 3  # square metres
```

**Result:** `12`

---

## Numbers and Arithmetic

### Arithmetic Operators

```
7 + 2
7 - 2
7 * 2
7 / 2
7 div 2
7 mod 2
7 ^ 2
```

**Results:**
```
9
5
14
3.5
3
1
49
```

`/` is ordinary division. `div` divides and drops the fractional part (it truncates toward zero), `mod` gives the remainder, and `^` raises to a power.

### Precedence

The usual rules of arithmetic apply: `^` binds tightest, then `*`, `/`, `div`, and `mod`, then `+` and `-`. Parentheses change the grouping:

```
2 + 3 * 4
(2 + 3) * 4
2 * 3 ^ 2
```

**Results:**
```
14
20
18
```

As in mathematical notation, a leading minus applies to the whole power, and a chain of powers groups from the right:

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

The [Quick Reference](#operators) lists every operator in precedence order.

### Decimal Numbers

KatLang numbers are decimal numbers with 34 significant digits. Decimal fractions such as `0.1` are stored exactly, so calculations with them have none of the binary rounding surprises found in many programming languages:

```
0.1 + 0.2
19.99 * 3
1 / 3
```

**Results:**
```
0.3
59.97
0.3333333333333333333333333333333333
```

A result keeps the decimal places of its inputs, which is why `0.2 * 50` is displayed as `10.0` and `2.50 * 4` as `10.00`: the value is ten either way, and only the display differs. To shorten a result, round it with `round(value, digits)` or set the number of displayed decimal places for the whole program (see [Displayed Decimal Places](#displayed-decimal-places)).

Number literals may use `_` between digits and an exponent written with a lowercase `e`: `1_000_000`, `6.674e-11`, `1.5e3`. A decimal point needs digits on both sides (`0.5`, not `.5`).

Dividing by zero is an error:

```
1 / 0
```

**Result:** error — division by zero.

### Math Functions

The common mathematical functions are available by name:

```
sqrt(2)
round(pi, 4)
sin(pi / 2)
abs(-7)
lg(1000)
exp(1)
```

**Results:**
```
1.414213562373095048801688724209698
3.1416
1
7
3
2.718281828459045235360287471352662
```

| Function | Meaning |
|---|---|
| `abs(x)`, `sign(x)` | Absolute value; the sign as `-1`, `0`, or `1` |
| `floor(x)`, `ceil(x)` | Round down; round up |
| `round(x, digits)` | Round to `digits` decimal places (halves round away from zero) |
| `sqrt(x)` | Square root |
| `exp(x)`, `ln(x)`, `lg(x)`, `log(x, base)` | Exponential; natural, base-10, and any-base logarithm |
| `pow(x, y)` | `x` raised to the power `y`, the same as `x ^ y` |
| `sin(x)`, `cos(x)`, `tan(x)` | Trigonometric functions of an angle in radians |
| `asin(x)`, `acos(x)`, `atan(x)`, `atan2(y, x)` | Inverse trigonometric functions |
| `pi` | The constant π |
| `random(start, end)`, `randomInt(start, end)` | Random numbers (see below) |

There is no separate constant for Euler's number: write `exp(1)`.

These names are shortcuts for the members of the built-in `Math` algorithm: `sqrt(2)` is `Math.Sqrt(2)`, and `pi` is `Math.Pi`. Both spellings work. The lowercase names read well in formulas; the `Math.` form is useful when one of your own definitions uses the same name.

### Random Numbers

`random(start, end)` returns a decimal number and `randomInt(start, end)` a whole number, each at least `start` and less than `end`. So `randomInt(1, 7)` rolls a die:

```
randomInt(1, 7)
random(0, 1)
```

Every run draws new values, so this example has no fixed result. To reproduce a run, the host can fix the random seed; with the command-line tool, `katlang eval "randomInt(1, 7)" --random-seed 42` prints the same number every time.

---

## Properties

### Naming a Calculation

```
Width = 4
Height = 3
Area = Width * Height

Area
```

**Result:** `12`

`Name = expression` defines a **property**: a named calculation. A definition produces no output by itself; the last row reads the property `Area` and outputs its value. Property names are conventionally written in PascalCase.

### Definitions and Output Rows

A program is a mix of definitions and output rows. The order of the definitions does not matter — a property may use one that is defined further down:

<!-- spec:output-rows-interleave-definitions -->
```
A = 3
A + B
B = 2
```

**Result:** `5`

By convention, definitions come first and output rows last.

### Algorithms

KatLang's general word for a calculation is **algorithm**. An algorithm can have *parameters* (its inputs, the subject of the next chapter), *properties* (named algorithms that belong to it), and *output* (the values its rows produce). The program itself is an algorithm, the **root algorithm**: the properties you define at the top level belong to it, and its output rows are what the program displays. A property is a named algorithm, and reading the property evaluates it. Where other languages speak of functions and modules, KatLang uses this one idea for both.

### Names Are Bound Once

KatLang has no variables to update. A name is defined once, and a second definition of the same name in the same algorithm is an error, not a reassignment:

```
Rate = 5
Rate = 6  # error: Property 'Rate' is already defined.
```

A value, once computed, never changes.

### Reading and Calling

A property without parameters can be read (`Answer`) or called with empty parentheses (`Answer()`):

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

The two forms differ only for a calculation that can give a different result each time, such as a random number. KatLang evaluates a property when it is first read, and a later read of the same property during the run reuses that value, while an explicit call evaluates the property anew:

```
Roll = randomInt(1, 7)
Roll == Roll
```

**Result:** `true`

`Roll() == Roll()`, by contrast, rolls twice and is `true` only when the two rolls happen to agree.

### Displayed Decimal Places

A property named `DisplayDecimals` sets how many decimal places the program's results show:

```
DisplayDecimals = 4

pi
1 / 7
2.5
5 * 2
```

**Results:**
```
3.1416
0.1429
2.5000
10
```

Numbers with decimal places are rounded or padded to exactly that many places, while a number without decimal places, such as the `10` of `5 * 2`, is shown as it is. The setting changes only the display: calculations and comparisons still use the full values. It must be a whole number from 0 to 99. A host can also supply a default for programs that do not set it; the command-line tool has the option `--display-decimals` for this.

---

## Parameters

### Inferred Parameters

```
Tax = price * 0.2
Tax(50)
```

**Result:** `10.0`

`price` is not defined anywhere, so KatLang treats it as a **parameter** of `Tax`: an input that the caller supplies. `Tax(50)` calls `Tax` with `price` equal to `50`. Parameter names are conventionally written in camelCase, which keeps them apart from PascalCase property names; in physics and similar fields, prefer the field's standard notation, as in `v = s / t`.

### Parameter Order

Inferred parameters are ordered by their first appearance in the definition, reading from left to right:

```
Sub = a - b
Speed = distance / time

Sub(10, 3)
Speed(100, 8)
```

**Results:**
```
7
12.5
```

Take care when the reading order is not the order you want to call with: `Ratio = b / a` takes `b` first.

### Explicit Parameter Lists

You can also list the parameters yourself:

```
Hypotenuse(a, b) = sqrt(a ^ 2 + b ^ 2)
Hypotenuse(3, 4)
```

**Result:** `5`

An explicit list fixes the parameters' names and order. It is also **closed**: every other name in the body must refer to something that is defined, or the definition is an error — no parameter is added silently. An explicit list is also the way to accept an argument you do not use:

```
KeepFirst(a, b) = a
KeepFirst(42, 999)
```

**Result:** `42`

Inferred parameters keep short formulas short; explicit lists document the inputs of larger algorithms. Many later examples use an explicit list because they need one — for example, to call with an order other than the order of first appearance, or because a name written after a dot or inside braces is not inferred the way you might expect (see [Members Come First](#members-come-first) and [Callbacks Receive One Element](#callbacks-receive-one-element)).

### Each Argument Is Evaluated At Most Once

Each call argument is evaluated at most once for its value. If the corresponding parameter is read multiple times, those reads reuse the same argument outcome and do not re-evaluate the original argument expression:

```
Double(x) = x + x
Double(randomInt(1, 7)) mod 2
```

**Result:** `0`

The die is rolled once, so `x + x` is always even. The same holds when evaluating an argument fails: every read of the parameter reports that same failure, and reading the parameter again never evaluates the argument again, so it cannot turn the failure into a value.

An argument that a lazy builtin does not select may never be evaluated. Explicitly calling a callable parameter is a separate invocation; it does not replace the outcome reused by value reads.

### Formulas That Use Formulas

A formula can use another formula that still needs inputs. KatLang then passes those inputs along, and they become parameters of the formula that uses it:

```
Speed = distance / time
KineticEnergy = mass * Speed ^ 2 / 2

KineticEnergy(2, 10, 5)
```

**Result:** `4`

`KineticEnergy` uses `Speed`, which needs `distance` and `time`, so `KineticEnergy` takes them as well and hands them on to `Speed`. Its parameters are its own names first, followed by the ones it passes on: `KineticEnergy(mass, distance, time)`. The inputs are handed on **by name**, not by position, so an explicit parameter list must declare them under the same names: `KineticEnergy(mass, distance, time) = mass * Speed ^ 2 / 2` works, while in `KineticEnergy(m, d, t) = m * Speed ^ 2 / 2` nothing named `distance` or `time` is there to hand on, and calling it is an error.

<a id="reordering-parameters-with-grace-operator"></a>
<a id="grace-with-dotcall"></a>

### Reordering Parameters with Grace

When the first-appearance order is not the order you want, the Grace marker `~` adjusts it: `~x` moves the parameter `x` one position earlier, and `x~` one position later.

```
Divide = y / ~x
Divide(2, 10)
```

**Result:** `5`

Without the marker, `y` would be the first parameter. The marker is written directly against the name (`~x`, not `~ x`), and it applies only to inferred parameters: with an explicit parameter list, write the order you want.

### Undefined Names in the Program

The program itself is never called, so nothing can supply a parameter to it, and an undefined name at the top level is an error. This is how KatLang reports a typo:

```
Total = 5
Totl + 1
```

**Result:** error — `Totl` is not defined, so it becomes a parameter of the program, which nothing supplies; the report suggests `Total`.

---

## Booleans and Decisions

### Comparisons

```
3 > 1
3 < 1
5 == 5
5 != 4
3 >= 3
```

**Results:**
```
true
false
true
true
true
```

Comparisons produce the **Boolean** values `true` and `false`. The ordering operators `<`, `>`, `<=`, and `>=` compare numbers. `==` and `!=` compare any two values — numbers, text, and the sequences and lists of later chapters — and values of different kinds are simply unequal, so `true == 1` is `false`.

### Chained Comparisons

Comparisons chain as they do in mathematics: `a < b < c` means that `a < b` and `b < c`.

```
IsTeen = 13 <= age <= 19

IsTeen(15)
IsTeen(21)
```

**Results:**
```
true
false
```

A chain compares each adjacent pair, is `true` when every pair holds, and evaluates each operand once.

### Logical Operators

`and`, `or`, `xor`, and `not` combine Booleans:

```
CanVote = age >= 18 and registered

CanVote(20, true)
CanVote(20, false)
CanVote(16, true)
```

**Results:**
```
true
false
false
```

Comparisons bind more tightly than the logical operators, so `x > 0 and x < 10` needs no parentheses, and `not x > 3` means `not (x > 3)`. Both operands of `and`, `or`, and `xor` are always evaluated.

Only `true` and `false` are truth values. Numbers are not, so `1 and 0` is a type error: write the comparison you mean, such as `x != 0`.

### Choosing a Value with `if`

`if(condition, whenTrue, whenFalse)` chooses between two values:

```
Abs = if(x < 0, -x, x)

Abs(-5)
Abs(3)
```

**Results:**
```
5
3
```

Only the chosen branch is evaluated, so the other branch may even be invalid for the current inputs:

```
SafeDivide(n, d) = if(d == 0, 0, n / d)

SafeDivide(10, 4)
SafeDivide(1, 0)
```

**Results:**
```
2.5
0
```

The condition must be a Boolean:

```
if(1, 2, 3)
```

**Result:** error — the condition `1` is a number, not a Boolean.

For a choice among many cases, see [Pattern Matching](#pattern-matching).

---

## Text

Text values — strings — are written in single quotes and displayed without them:

```
Greeting = 'hello'

Greeting
Greeting == 'hello'
'Hello' == 'hello'
```

**Results:**
```
hello
true
false
```

Strings can be stored, passed to and returned from algorithms, and compared with `==` and `!=`, which compare them exactly, including case. Arithmetic and ordering are not defined for text. Strings are useful as labels and categories:

```
Verdict = if(score >= 50, 'pass', 'fail')

Verdict(72)
Verdict(35)
```

**Results:**
```
pass
fail
```

The next chapter shows how to turn a number into text, and [Pattern Matching](#pattern-matching) shows how to choose among text values.

---

## Dot Calls

Every call so far has been written `f(a)`. KatLang has a second spelling of the same call, `a.f`, in which the value before the dot becomes the call's first argument; the one refinement, for algorithms that have members of their own, is explained in [Members Come First](#members-come-first). The rest of this tutorial uses both spellings, because the dot lets a calculation read from left to right.

### Two Ways to Write a Call

```
Square = n * n

Square(5)
5.Square
```

**Results:**
```
25
25
```

Further arguments go in parentheses after the name, so `a.f(b)` is `f(a, b)`:

```
Add(a, b) = a + b

Add(10, 5)
10.Add(5)
```

**Results:**
```
15
15
```

In general, `a.f(b, c)` is the call `f(a, b, c)`. The value before the dot is called the **receiver**, and it is passed as a single argument. The rule applies to every callable, your own and the built-in ones alike:

```
16.sqrt
pi.round(2)
2.pow(10)
```

**Results:**
```
4
3.14
1024
```

### Chains Read Left to Right

Dot calls chain, and each step receives the result of the step before it:

```
Double = n * 2
Increment = n + 1

3.Double.Increment
Increment(Double(3))
3.Increment.Double
```

**Results:**
```
7
7
8
```

`3.Double.Increment` reads in the order in which the work happens — take 3, double it, then increment the result — while the equivalent nested call `Increment(Double(3))` has to be read from the inside out. The order of the steps matters: `3.Increment.Double` is `Double(Increment(3))`.

This style is especially natural for processing collections, as in `range(1, 10).filter{...}.map{...}.sum` in [Working with Collections](#working-with-collections).

### Members Come First

A dot can also select a **member** of an algorithm. `Math` is a built-in algorithm whose members are the mathematical functions and constants: `Math.Pi` reads its member `Pi`, and `Math.Sqrt(16)` calls its member `Sqrt` with the argument `16`. In this case the receiver is not passed as an argument.

The complete rule for `a.f(...)` is therefore:

1. If the receiver `a` is an algorithm with a member named `f`, that member is used.
2. Otherwise, `a.f(...)` is the call `f(a, ...)`.

Numbers, text, and the sequences and lists of the next chapters have no members, so for them the dot always means a call: `16.sqrt` is `sqrt(16)`. You will define algorithms with members of your own in [Organizing Programs](#organizing-programs).

The rule also affects inferred parameters. In `Area = shape.V * 2`, the argument for `shape` might have no member `V`, and then `shape.V` would be the call `V(shape)`; so when nothing named `V` is defined, `V` is inferred as a parameter as well, and the signature is `Area(shape, V)`. To keep `V` out of the inferred parameters, write the parameter list: `Area(shape) = shape.V * 2`. The list settles only the signature, not what the dot does: a member `V` of `shape` still wins, and otherwise `shape.V` is still the call `V(shape)`.

### Converting a Number to Text

`.string` turns a number into text. It is a built-in dot operation rather than a call, so it exists only in dot form — `string(42)` is not defined:

```
42.string
42.string == '42'
```

**Results:**
```
42
true
```

---

<a id="multiple-outputs"></a>

## Sequences

<a id="multi-output-example"></a>

### Several Outputs Become One Value

An algorithm can produce several outputs:

```
Rectangle(width, height) = width * height, 2 * (width + height)

Rectangle(3, 4)
```

**Result:** `(12, 14)`

In the body, `width * height` and `2 * (width + height)` are two outputs. A call returns one value, so the caller receives the two outputs together as a **sequence**: an ordered group of values, displayed in parentheses. This is how an algorithm returns several related results — here, the area and the perimeter of a rectangle.

Reading a property works the same way. At the top level each output is displayed in its own row, while a sequence is one value, so it takes one row:

```
Point = 3, 4

Point
10, 20
```

**Results:**
```
(3, 4)
10
20
```

### Writing Sequences

Parentheses around comma-separated items make a sequence value:

<!-- spec:value-three-items -->
```
(1 + 1, 2 + 2, 3 + 3)
```

**Result:** `(2, 4, 6)`

Parentheses around a single item only group it, as in arithmetic: `(7)` is just `7`, and `((1, 2))` is the same sequence as `(1, 2)`. A sequence therefore has either no items or at least two; there is no one-item sequence. ([Lists](#lists) do keep a single item as a group of its own.)

```
(7)
((1, 2))
(1, (2, 3))
```

**Results:**
```
7
(1, 2)
(1, (2, 3))
```

Sequences nest: `(1, (2, 3))` has two items, the second of which is itself a sequence.

### Counting and Selecting

`count` gives the number of items, and `value:index` selects one item. Indexing is **zero-based**: `:0` selects the first item.

<!-- spec:index-selects-atom -->
```
Nums = 10, 20, 30, 40, 50

# Select the third value (index 2):
Nums:2
```

**Result:** `30`

```
Pairs = (1, 2), (3, 4)

Pairs.count
Pairs:1
Pairs:1:0
```

**Results:**
```
2
(3, 4)
3
```

Selection returns the chosen item as it is: selecting a sequence gives the whole sequence `(3, 4)`, and a further `:0` selects inside it. An index outside the sequence is an error.

### Values Stay Values

A sequence is one value wherever it goes. In particular, passing it to an algorithm passes **one** argument:

<!-- spec:fixed-call-preserves-boundaries -->
```
Pair = 10, 20
Add(x, y) = x + y

Add(Pair)
```

**Result:** error — `Pair` is one argument, but `Add` needs two.

KatLang never takes a value apart on its own. A dot call passes its receiver in the same way: `(10, 20).Add` is `Add((10, 20))`, which fails for the same reason. To use the items of a value, say so explicitly in one of three ways: select them with `:`, as in `Add(Pair:0, Pair:1)`; open the value with `*` (next section); or declare a parameter that unpacks it (see [Unpacking an Argument](#unpacking-an-argument)).

### Opening a Value with `*`

A star after a value opens it: `value*` hands the value's items to the surrounding context one by one. At the top level they become separate outputs:

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

In a call, they become separate arguments:

```
Pair = 10, 20
Add(x, y) = x + y

Add(Pair*)
Pair*.Add
```

**Results:**
```
30
30
```

`Pair*.Add` is the dot spelling of `Add(Pair*)`: the spread items become the arguments of the call. An expression `value*` is called a **spread**, and spreads can appear wherever several items can — among the items of a new sequence, and several times in one call:

```
A = 1, 2
B = 3, 4

(A*, B*)
(A, B)
```

**Results:**
```
(1, 2, 3, 4)
((1, 2), (3, 4))
```

```
Distance(x1, y1, x2, y2) = sqrt((x2 - x1) ^ 2 + (y2 - y1) ^ 2)
P = 0, 0
Q = 3, 4

Distance(P*, Q*)
```

**Result:** `5`

A spread opens exactly one level: `((1, 2), 3)*` supplies the two items `(1, 2)` and `3`, and the inner sequence stays whole.

When another item follows a spread, separate the two with a comma, as in `A*, B`. Without the comma, `A* B` is the multiplication `A * B`: a star followed by an operand always multiplies, even when the operand is on the next line.

### Unpacking an Argument

A parameter written as a parenthesized pattern takes one argument and unpacks its items into names:

```
Length((x, y)) = sqrt(x ^ 2 + y ^ 2)
Point = 3, 4

Length(Point)
Length((6, 8))
```

**Results:**
```
5
10
```

`Length` has one parameter, the pattern `(x, y)`, so it takes one argument — a pair — and names the pair's two items.

### The Empty Sequence

`()` is the empty sequence, a value with no items:

```
()
().count
```

**Results:**
```
()
0
```

Spreading `()` supplies nothing. Do not confuse it with `{}`, an empty algorithm body: `{}` has no output at all, and using it where a value is required is an error.

### Comparing Values

`==` compares sequences item by item, nested sequences included:

```
(1, 2) == (1, 2)
(1, 2) == (2, 1)
(1, (2, 3)) == (1, (2, 3))
```

**Results:**
```
true
false
true
```

---

## Lists

### List Values

Square brackets make a **list**:

<!-- spec:list-literal -->
```
[1, 2, 3]
```

**Result:** `[1, 2, 3]`

A list keeps exactly the structure you write. Unlike a sequence, a list of one item stays a list, and `[]` is the empty list:

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

Lists and sequences are different kinds of value, so a list never equals a sequence, even one with the same items:

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

### Working with Lists

Lists support the same operations as sequences — counting, zero-based selection, and spreading:

```
Primes = [2, 3, 5, 7]

Primes.count
Primes:0
[0, Primes*, 11]
[Primes, 11]
```

**Results:**
```
4
2
[0, 2, 3, 5, 7, 11]
[[2, 3, 5, 7], 11]
```

With the star, the items of `Primes` become elements of the new list; without it, the whole list `Primes` is one element. Lists nest, and selection goes one level at a time:

```
Grid = [[1, 2], [3, 4]]

Grid:1
Grid:1:0
```

**Results:**
```
[3, 4]
3
```

A list, too, is one value in a call: `Add([10, 20])` passes one argument, and `Add([10, 20]*)` passes two. A single definition with a pattern parameter, such as `Length((x, y))`, unpacks a list as well as a sequence; the clauses of [Pattern Matching](#matching-structure) are stricter.

### Lists or Sequences?

- A **sequence** is what several outputs become, and what parentheses write. It is the natural shape for results that belong together, like the area and perimeter returned by `Rectangle`.
- A **list** is a collection that keeps its exact shape, even with one item or none. Use lists for data such as measurements, scores, or the rows of a table.

The collection operations of the next chapters accept both, and every operation that produces a collection returns a list.

---

## Algorithms as Values

### Passing an Algorithm

An algorithm can be passed to another algorithm and called there:

```
Apply(f, x) = f(x)
Square = n * n

Apply(Square, 4)
Apply(sqrt, 16)
```

**Results:**
```
16
4
```

The parameter `f` receives an algorithm, and `f(x)` calls it. Inferred parameters work the same way — a name that is called becomes a parameter that receives an algorithm:

```
Twice = f(f(x))
Square = n * n

Twice(Square, 3)
```

**Result:** `81`

### Brace Algorithms

Braces write an algorithm without giving it a name. The undefined names inside the braces become the brace algorithm's own parameters, in order of first appearance:

```
Apply(f, x) = f(x)

Apply({n + 1}, 4)
Apply({n * n}, 4)
```

**Results:**
```
5
16
```

When a brace algorithm is a call's only argument, the parentheses may be left out: `F{n * 2}` is `F({n * 2})`. Together with dot calls, this reads naturally when the data comes first:

```
Twice(x, f) = f(f(x))

Twice(5, {n * 2})
5.Twice{n * 2}
```

**Results:**
```
20
20
```

So when you design an algorithm that takes other algorithms, put the data parameter first; it will then work well in dot chains.

### Parentheses versus Braces

Parentheses and braces look alike but mean different things:

- `(n + 1)` is computed right where it is written, with the `n` of the surrounding algorithm.
- `{n + 1}` is an algorithm that computes `n + 1` whenever it is called, and `n` is its own parameter.

A brace algorithm without parameters simply produces its output when it is read, so `{1, 2, 3}.count` is `3`, just like `(1, 2, 3).count`. Braces also give an algorithm room for definitions of its own, as [Organizing Programs](#organizing-programs) shows.

---

## Working with Collections

### Ranges

`range(start, end)` lists the whole numbers from `start` to `end`, inclusive:

<!-- spec:range-inclusive -->
```
range(1, 5)
```

**Result:** `[1, 2, 3, 4, 5]`

When `start` is greater than `end`, the range counts down: `range(5, 1)` is `[5, 4, 3, 2, 1]`.

### Pipelines

Collection operations combine into pipelines:

```
range(1, 10).filter{n mod 2 == 0}.map{n * n}.sum
```

**Result:** `220`

Read it from left to right: the numbers from 1 to 10, keep the even ones, square each of them, add them up. Every step is a dot call — `range(1, 10).filter{...}` is `filter(range(1, 10), {...})` — and each brace algorithm receives one element at a time as its parameter `n`.

A long pipeline can be split across lines, because a line that starts with `.` continues the line before it:

<!-- spec:dot-chain-continuation -->
```
(1, 2, 3)
.map { n * 2 }
.sum
```

**Result:** `12`

A named algorithm works as well as a brace algorithm:

<!-- spec:filter-keeps-matching -->
```
IsEven = x mod 2 == 0
filter((1, 2, 3, 4, 5, 6), IsEven)
```

**Result:** `[2, 4, 6]`

### Common Operations

```
Scores = [72, 95, 58, 88, 64]

Scores.count
Scores.sum
Scores.avg
Scores.max
Scores.order
Scores.filter{s >= 60}
Scores.map{s + 5}
Scores.contains(88)
Scores.orderDesc.take(3)
```

**Results:**
```
5
377
75.4
95
[58, 64, 72, 88, 95]
[72, 95, 88, 64]
[77, 100, 63, 93, 69]
true
[95, 88, 72]
```

The last row chains two operations to find the three best scores.

| Operation | Result |
|---|---|
| `xs.count` | The number of items |
| `xs.sum`, `xs.avg` | The total and the mean of the numeric items |
| `xs.min`, `xs.max` | The smallest and the largest numeric item |
| `xs.first`, `xs.last` | The first and the last item |
| `xs.contains(v)` | `true` when an item equals `v` |
| `xs.filter(p)` | The items for which `p` returns `true` |
| `xs.map(f)` | `f` applied to every item |
| `xs.order`, `xs.orderDesc` | The numeric items sorted in ascending or descending order |
| `xs.distinct` | The items with later duplicates removed |
| `xs.take(n)`, `xs.skip(n)` | The first `n` items; the items after the first `n` |
| `xs.reduce(f, initial)` | The items combined into one value (see below) |
| `range(start, end)` | The whole numbers from `start` to `end` |
| `atoms(value)` | Every number inside a nested structure, in one flat list |

Each operation can also be written as an ordinary call, such as `count(xs)` or `take(xs, n)`. The test given to `filter` must return a Boolean: `{n mod 2 == 0}` is right, while `{n mod 2}` is a type error. `min`, `max`, `avg`, `first`, and `last` need at least one item, and the `sum` of an empty collection is `0`.

### One Collection Argument

A collection operation takes the whole collection as one argument — a list, a sequence, or a property holding either:

```
sum([1, 2, 3])
sum((1, 2, 3))
(1, 2, 3).sum
```

**Results:**
```
6
6
6
```

Separate numbers are not a collection:

```
sum(1, 2, 3)
```

**Result:** error — `sum` takes one collection, but three separate numbers were passed.

To combine collections, build one collection from their items: with `A = 1, 2` and `B = 3, 4`, `sum((A*, B*))` is `10`.

### Results Are Lists

An operation that produces a collection always returns a list, even when the list has one item or none. `first` and `last` return the item itself:

```
Scores = [72, 95, 58, 88, 64]

Scores.take(1)
Scores.filter{s > 100}
Scores.first
```

**Results:**
```
[72]
[]
72
```

Add a star to use the items of a result directly:

```
[3, 1, 2].order*
```

**Results:**
```
1
2
3
```

### Callbacks Receive One Element

`map`, `filter`, and `reduce` call their algorithm — the *callback* — once per element, and they pass the element as **one** argument: `map` and `filter` make the call `f(element)`, and `reduce` makes the call `f(element, accumulator)`, as described below. When the elements are pairs, the callback receives each pair whole, and can select its items or unpack it with a pattern parameter:

```
Pairs = [(2, 3), (4, 5)]

Pairs.map{p:0 * p:1}
```

**Result:** `[6, 20]`

<!-- spec:map-pair-callback -->
```
Swap((a, b)) = (b, a)
map(((1, 2), (3, 4)), Swap)
```

**Result:** `[(2, 1), (4, 3)]`

A `map` or `filter` callback with two ordinary parameters, such as `Add(a, b) = a + b`, does not accept a pair element, just as `Add((1, 2))` is an error.

A brace callback's parameters are its undefined names, so choose names that are not already defined around it. If the program defines a property `x`, then `{x * 2}` uses that `x`, and no parameter is left to receive the element.

Conversely, a name that appears only inside the braces is a parameter of the callback, not of the algorithm around it: in `Scale = values.map{n * factor}`, the callback has the parameters `n` and `factor`, `Scale` has only `values`, and calling the callback with one element fails. To make `factor` an input of `Scale`, declare it — `Scale(values, factor) = values.map{n * factor}` — and the `factor` in the braces is then the parameter of `Scale`.

### Folding with `reduce`

`reduce(collection, reducer, initial)` combines the elements into one value. It starts with `initial` and calls `reducer(element, accumulator)` for each element in turn, and each result becomes the next accumulator:

```
Numbers = [1, 2, 3, 4]

Numbers.reduce({x + total}, 0)
range(1, 5).reduce({x * product}, 1)
```

**Results:**
```
10
120
```

The parameters of a brace reducer follow first appearance, so write the element's name first and the accumulator's name second.

### Flattening with `atoms`

`atoms` collects every number from a nested structure into one flat list:

<!-- spec:atoms-recursive-flatten -->
```
atoms(((1, 2), (3, 4)))
```

**Result:** `[1, 2, 3, 4]`

A spread opens one level; `atoms` opens every level.

### Example: Descriptive Statistics

```
Data = [2, 4, 4, 4, 5, 5, 7, 9]

Mean = Data.avg
Variance = Data.map{(x - Mean) ^ 2}.avg
Deviation = Variance.sqrt

Mean, Variance, Deviation
```

**Results:**
```
5
4
2
```

Inside the brace algorithm, `Mean` refers to the property of the program, and the undefined `x` is the element.

---

## Collecting Parameters

### Collecting Arguments into a List

A parameter written with a leading star, such as `*values`, collects all the arguments of a call into one list. An algorithm with such a **collecting parameter** accepts any number of arguments:

```
Mean(*values) = values.sum / values.count

Mean(1, 2, 3, 4)
Mean(10)
```

**Results:**
```
2.5
10
```

Each argument is one item of the collected list. A sequence or a list passed as an argument stays whole, and a call without arguments collects the empty list:

```
Collect(*items) = items

Collect(1, 2, 3)
Collect()
Collect((1, 2), 3)
Collect([1, 2])
```

**Results:**
```
[1, 2, 3]
[]
[(1, 2), 3]
[[1, 2]]
```

### Passing Items with `*`

To pass a stored collection to `Mean`, spread it, so that its items become the arguments. `Mean(Data)` would pass one argument — the whole list — and the sum would fail on that one non-numeric item:

```
Mean(*values) = values.sum / values.count
Data = [2, 4, 6]

Mean(2, 4, 6)
Mean(Data*)
Data*.Mean
```

**Results:**
```
4
4
4
```

`Data*.Mean` is the dot spelling of `Mean(Data*)`. Compare the built-in `avg`, which takes one collection argument: `Data.avg` needs no star. A collecting parameter collects separate arguments, while a collection operation receives one collection.

### Fixed and Collecting Parameters Together

A collecting parameter can stand beside ordinary parameters. The ordinary parameters take their arguments from the front and the back, and the collecting parameter collects the rest:

```
Scale(*values, factor) = values.map{n * factor}
Head(first, *rest) = first
Tail(first, *rest) = rest

Scale(1, 2, 3, 10)
Head(5, 6, 7)
Tail(5, 6, 7)
```

**Results:**
```
[10, 20, 30]
5
[6, 7]
```

A parameter list may contain only one collecting parameter.

### Forwarding Collected Arguments

To pass collected arguments on to another collecting algorithm, spread the collected list:

<!-- spec:variadic-forwarding-list-spread -->
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

`Forward` hands on exactly the arguments it received: `Forward(1, 2)` passes two numbers, and `Forward([1, 2])` passes one list.

### Values and Items at a Glance

The last chapters rest on one idea: a value stays one value until you open it explicitly. With `A = [1, 2]` and `B = [3, 4]`:

| You write | Meaning |
|---|---|
| `F(A)` | One argument: the list `A` |
| `F(A*)` | Two arguments: the items `1` and `2` |
| `A.F` | The call `F(A)`, unless `A` has a member `F` |
| `A*.F` | The call `F(A*)` |
| `A:0` | One item of `A`, selected as a value: `1` |
| `(A*, B*)`, `[A*, B*]` | One sequence, or one list, of the items `1, 2, 3, 4` |
| `F(*xs) = ...` | `F` collects its arguments into the list `xs` |
| `F((x, y)) = ...` | `F` takes one argument and unpacks its two items |
| `A.count`, `A.sum` | A collection operation receives the whole list `A` |

---

## Deconstruction

One definition can bind several names at once:

<!-- spec:decon-pair -->
```
x, y = 1, 2
x
y
```

**Results:**
```
1
2
```

This is convenient for calculations whose results come in groups:

```
q, r = 17 div 5, 17 mod 5
q, r
```

**Results:**
```
3
2
```

When the right-hand side is one sequence or list, deconstruction unpacks it, and a name with a leading star collects the remaining items into a list:

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

Without a collecting name, the number of names must match the number of items: `x, y = 1, 2, 3` is an error as soon as `x` or `y` is used.

---

<a id="repetition"></a>

## Loops

### Repeating a Step with `repeat`

`repeat` applies a step algorithm a fixed number of times, feeding each result back in as the next input:

```
Increment = x + 1
Increment.repeat(5, 0)
```

**Result:** `5`

`Increment.repeat(5, 0)` — the dot spelling of `repeat(Increment, 5, 0)` — starts from `0` and applies `Increment` five times.

### State with Several Values

A step with several outputs carries several values from one round to the next; together they are the loop's **state**. Give one initial value for each state value:

```
Fibonacci(a, b) = b, a + b
Final = Fibonacci.repeat(10, 0, 1)

Final
Final:0
```

**Results:**
```
(55, 89)
55
```

Each round turns the state `(a, b)` into `(b, a + b)`. Starting from `(0, 1)`, ten rounds reach `(55, 89)`, and `:0` selects the tenth Fibonacci number.

Each initial value is one state value, and values stay values here too: to start from a stored pair such as `Start = 0, 1`, spread it, as in `Fibonacci.repeat(10, Start*)`.

### Looping While a Condition Holds

`while` repeats a step as long as a condition holds. The step's **last output** is the condition, and the outputs before it are the state:

```
Countdown = x - 1, x > 1
Countdown.while(5)
```

**Result:** `1`

Read `Countdown` as "while `x > 1`, replace `x` with `x - 1`": starting from 5, the state becomes 4, 3, 2, and 1, and at 1 the condition `x > 1` is `false`, so the loop stops with `1`. Precisely: each round computes the next state together with the condition; if the condition is `true`, the next state is kept and the loop continues, and if it is `false`, the loop ends and returns the current state. When the condition is written in terms of the step's inputs, as here, `while` behaves like an ordinary while loop. The condition must be a Boolean.

Two more examples: how many years it takes 5% interest to double 1000, and how many steps the Collatz sequence needs to get from 27 down to 1:

```
Grow(years, balance) = years + 1, balance * 1.05, balance < 2000
Collatz(n, steps) = if(n mod 2 == 0, n / 2, 3 * n + 1), steps + 1, n != 1

Grow.while(0, 1000):0
Collatz.while(27, 0):1
```

**Results:**
```
15
111
```

A loop whose condition never becomes `false` runs forever, so check the condition carefully. When you are transforming a known collection, a pipeline with `map`, `filter`, and `reduce` is usually clearer than a loop; loops are for state that evolves step by step.

---

## Pattern Matching

### Clauses

Several definitions with the same name, each with **patterns** in place of plain parameters, form one **conditional algorithm**:

```
Describe(0) = 'zero'
Describe(n) = if(n > 0, 'positive', 'negative')

Describe(0)
Describe(-4)
Describe(7)
```

**Results:**
```
zero
negative
positive
```

A call tries the clauses from top to bottom and uses the first one whose patterns match. A literal such as `0` matches only that value; a name such as `n` matches any value and binds it. Put the catch-all clause last.

### Recursion

A clause may call its own algorithm, and clauses make the base case of a recursion explicit:

```
Factorial(0) = 1
Factorial(n) = n * Factorial(n - 1)

Factorial(5)
```

**Result:** `120`

```
Gcd(a, 0) = a
Gcd(a, b) = Gcd(b, a mod b)

Gcd(48, 18)
```

**Result:** `6`

Recursion cannot go arbitrarily deep. By default KatLang allows at most 128 nested calls, and a separate protection of the host's stack can stop a deep recursion sooner, depending on what each call does; either way the calculation stops with an error. For long iterations use `repeat`, `while`, or `reduce` instead: `range(1, n).reduce({x * product}, 1)` computes a factorial without recursion.

### Matching Text

String literals are patterns too:

```
Price('tomatoes') = 1.20
Price('apples') = 0.80
Price(item) = 0

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

`true` and `false` can be matched in the same way.

### Matching Structure

A parenthesized pattern matches a sequence with that many items and unpacks it, and literals inside it make it selective, so clauses can tell shapes apart:

```
Area(('circle', r)) = pi * r ^ 2
Area(('rect', w, h)) = w * h

Area(('rect', 3, 4))
Area(('circle', 1)).round(4)
```

**Results:**
```
12
3.1416
```

When a parenthesized pattern of several items chooses between clauses or contains a literal, it matches sequences, not lists: `['rect', 3, 4]` matches no clause of `Area`, so `Area(['rect', 3, 4])` is an error.

### Equal Arguments

Using the same name twice in one clause requires the two arguments to be equal:

```
Same(x, x) = true
Same(x, y) = false

Same(3, 3)
Same(3, 4)
```

**Results:**
```
true
false
```

### Rules for Clauses

When no clause matches, the call is an error, so add a catch-all clause if every input should be handled:

```
Grade(1) = 'excellent'
Grade(2) = 'good'

Grade(3)
```

**Result:** error — no clause of `Grade` matches the argument `3`.

All clauses of one conditional algorithm take the same number of parameters and produce the same number of outputs. A family of clauses that disagrees is rejected before anything runs:

<!-- spec:conditional-clauses-share-top-level-arity -->
```
F(0) = 1
F(x, y) = 2

F(0)
```

The error points at the second clause, which takes two parameters where the first takes one. Two clauses whose patterns have the same structure, such as `F(x)` and `F(y)`, are rejected too, as duplicates, even when the names they bind differ. Apart from such duplicates, KatLang does not check whether a clause can ever be chosen: after `F(n)`, a clause `F(0)` is accepted but never used, which is why the catch-all belongs last.

---

## Organizing Programs

### Local Definitions

An algorithm's body may be written in braces, with definitions of its own — local helpers — followed by its output:

```
Loan(principal, rate, years) = {
    MonthlyRate = rate / 12
    Months = years * 12
    principal * MonthlyRate / (1 - (1 + MonthlyRate) ^ -Months)
}

Loan(200000, 0.06, 30).round(2)
```

**Result:** `1199.10`

`MonthlyRate` and `Months` belong to `Loan`. They can use the parameters of `Loan`, and each call of `Loan` computes them from that call's arguments. Because they depend on those parameters, they can be used only inside `Loan`:

```
Loan(principal, rate, years) = {
    MonthlyRate = rate / 12
    Months = years * 12
    principal * MonthlyRate / (1 - (1 + MonthlyRate) ^ -Months)
}

Loan.MonthlyRate
```

**Result:** error — `MonthlyRate` depends on the parameter `rate` of `Loan`, so it can be used only inside `Loan`.

### How Names Are Found

KatLang looks up a name starting in the algorithm where it is written and then in each enclosing algorithm, outward; the first algorithm that declares the name — as a property or as a parameter — provides it. A nested definition therefore hides an outer one with the same name:

```
X = 10
Inner = {
    X = 99
    X
}

Inner
X
```

**Results:**
```
99
10
```

Parameters are found in the same way, so a nested helper reads the parameter of its enclosing algorithm even when a farther algorithm defines the same name:

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

A property may not reuse the name of a parameter of its own algorithm or of an enclosing one; rename one of the two. After your own definitions come the built-in names such as `sum`, `sqrt`, and `if`, so a definition of your own with the same name takes precedence over a built-in one. A name that is found nowhere becomes an inferred parameter, as described in [Parameters](#parameters), or is an error in an algorithm with an explicit parameter list.

### Algorithms as Containers

An algorithm can also be a container that groups related definitions. Its members are reached with a dot:

```
Physics = {
    public G = 9.81
    public FallTime(h) = sqrt(2 * h / G)
}

Physics.G
Physics.FallTime(20).round(3)
```

**Results:**
```
9.81
2.019
```

This is the member rule from [Dot Calls](#members-come-first): when the receiver has a member with the given name, the dot selects that member, and the receiver is not passed as an argument. Only a receiver without such a member turns `a.f(...)` into `f(a, ...)`:

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

`Obj` has its own member `B`, so `Obj.B(5)` calls that member with `5`. The number `3` has no members, so `3.B(5)` is the call `B(3, 5)`.

### Public Members and `open`

`open` makes the `public` members of an algorithm usable without the prefix:

```
open Physics
Physics = {
    public G = 9.81
    public FallTime(h) = sqrt(2 * h / G)
}

FallTime(20).round(3)
```

**Result:** `2.019`

A member without `public` is private: `open` leaves it out, although a dot can still reach it.

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

After `open Lib`, `Area` could be used on its own, but `Helper` could not. A few rules keep `open` predictable:

- `open` comes first in its algorithm, before any definitions and output rows. An algorithm has one `open` declaration, which may list several targets: `open Geometry, Physics`.
- Opened names never override other names. Your own definitions and the built-in names are found first, and `open` is consulted only for a name that neither provides. If two opened targets provide the same name, using that name is an error.
- `open Math` makes the members of `Math` available under their own names, such as `Sqrt(16)` and `Pi`.

### Loading External Algorithms

A program can load an algorithm from a URL with `load` and use its members, or `open` a URL directly:

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

<!-- spec:skip open 'url' needs a host-configured network downloader; the URL and its output are illustrative -->
```
open 'https://katlang.org/algorithm.kat'

# X is now directly accessible:
X + 3
```

**Result:** `23`

Loading is off unless the host application allows it — the command-line tool needs the option `--allow-loading` — and a program that loads without permission is rejected. A module URL must use `https` and a host that the application allows, by default `katlang.org` and its subdomains.

---

## Layout and Common Pitfalls

### Line Layout

Each line of a program is an output row or a definition. On one line, items must be separated by commas, so this program is rejected — write `1, 2, 3` instead:

<!-- spec:same-line-slots-need-comma -->
```
1 2 3
```

A line ends its expression. To continue an expression on the next line, end the line with an operator or a comma, keep a `(`, `[`, or `{` open, or start the next line with `.` to continue a dot chain:

```
Total = 1 +
    2
Values = [
    10,
    20
]

Total, Values.sum
```

**Results:**
```
3
30
```

Conversely, a new line never continues an expression that is already complete. `Add` followed by a line `(1, 2)` is two rows, not a call, so keep a call's opening parenthesis on the same line as its name; and `A` followed by a line `-1` is the two rows `A` and `-1`, not a subtraction. Each definition starts on its own line: `x = 1 y = 2` is an error.

### Spread or Multiplication?

A star after a value is a multiplication whenever an operand follows it, on the same line or on the next. It is a spread only when nothing can follow: before a comma, a closing bracket, a new definition, or the end of the program. So when another item follows a spread, write a comma:

```
A = 2
B = 3

A*, B
A* B
```

**Results:**
```
2
3
6
```

### Common Mistakes

- **A misspelled name becomes a parameter.** An undefined name is inferred as a parameter, so a typo shows up as a missing argument ([Undefined Names in the Program](#undefined-names-in-the-program)).
- **A misspelled member falls back to a call.** `Math` has no member `Ceiling`, so `Math.Ceiling(2.1)` means `Ceiling(Math, 2.1)`; as nothing named `Ceiling` is defined, the name becomes a parameter, and the error message suggests `Math.Ceil`.
- **Parameters follow first appearance.** `Ratio = b / a` takes `b` first; use an explicit parameter list or Grace to change the order.
- **Values are not unpacked automatically.** A sequence or list is one argument. Open it with `*`, select its items with `:`, or unpack it with a pattern parameter.
- **Collection operations take one collection.** Write `sum((1, 2, 3))` or `[1, 2, 3].sum`, not `sum(1, 2, 3)`.
- **Collecting parameters take separate arguments.** Spread a stored collection into them: `Data*.Mean`.
- **Only Booleans are conditions.** `if`, `filter`, `while`, and the logical operators need `true` or `false`; a number is a type error.
- **Parentheses compute, braces define.** `(n + 1)` is a value computed now; `{n + 1}` is an algorithm with the parameter `n`.
- **`()`, `[]`, and `{}` are different.** They are the empty sequence, the empty list, and an algorithm without output.
- **Deep recursion stops with an error.** Use `repeat`, `while`, or `reduce` for long iterations.

### Numbers: Precision and Limits

- Numbers have 34 significant digits, and a result that needs more is rounded. A result too large to represent becomes `Infinity` or `-Infinity`, and an undefined operation such as `sqrt(-1)` gives `NaN`.
- Math functions are computed to full precision and never rounded to "nice" values. `pi` is π rounded to 34 digits, so `sin(pi)` is a tiny number of about `-1.16e-34` rather than `0`. Irrational results such as `sin(1)` are approximations at 34 digits, correct to roughly the last digit or two. Compare such results with a tolerance, or `round` them.
- Division by zero is an error, and so is raising zero to a negative power (`0 ^ -1`).
- A single list or sequence holds at most 100,000 items by default.

---

## Quick Reference

### Operators

| Operator | Description | Precedence |
|---|---|---|
| `^` | Power; groups from the right (`2 ^ 3 ^ 2` is `2 ^ 9`) | Highest |
| `-` (prefix) | Negation; `-2 ^ 2` is `-(2 ^ 2)` | |
| `*`, `/`, `div`, `mod` | Multiplication, division, integer division, remainder | |
| `+`, `-` | Addition, subtraction | |
| `<`, `>`, `<=`, `>=`, `==`, `!=` | Comparisons; they chain, as in `a < b <= c` | |
| `not` | Logical negation | |
| `and` | Logical and | |
| `xor` | Logical exclusive or | |
| `or` | Logical or | Lowest |
| `:` | Selection by zero-based index (`value:0`) | Postfix |
| `.` | Dot call or member access (`a.f(b)`) | Postfix |

### Syntax

| Syntax | Meaning |
|---|---|
| `Name = expression` | Define a property |
| `Name(a, b) = expression` | Define a property with an explicit parameter list |
| `Name(pattern) = expression` | One clause of a conditional algorithm |
| `a, b` | Separate outputs, arguments, or items |
| `(a, b)` | A sequence; parentheses around one expression only group it |
| `[a, b]` | A list |
| `{ ... }` | An algorithm: a brace algorithm, or a body with local definitions |
| `value*` | Spread: supply the items of a value |
| `*name` | Collecting parameter or collecting deconstruction target |
| `(x, y)` in a parameter list | Pattern parameter: unpack one argument |
| `~x`, `x~` | Grace: move an inferred parameter one position earlier or later |
| `load('url')` | Load an algorithm from a URL; a special form, not a keyword |
| `'text'` | String |
| `# ...` | Comment |

### Built-in Operations

| Operation | Written as | Result |
|---|---|---|
| `if` | `if(condition, a, b)` | `a` when the condition is `true`, otherwise `b`; only the chosen branch is evaluated |
| `range` | `range(start, end)` | The whole numbers from `start` to `end`, counting up or down |
| `count` | `xs.count` | The number of items |
| `sum`, `avg` | `xs.sum`, `xs.avg` | The total and the mean of numeric items (the sum of no items is `0`) |
| `min`, `max` | `xs.min`, `xs.max` | The smallest and the largest numeric item |
| `first`, `last` | `xs.first`, `xs.last` | The first and the last item |
| `contains` | `xs.contains(v)` | `true` when an item equals `v` |
| `filter` | `xs.filter(p)` | The items for which `p(item)` is `true` |
| `map` | `xs.map(f)` | `f(item)` for every item |
| `reduce` | `xs.reduce(f, initial)` | The items combined from left to right by `f(item, accumulator)`, starting from `initial` |
| `order`, `orderDesc` | `xs.order`, `xs.orderDesc` | The numeric items in ascending or descending order |
| `distinct` | `xs.distinct` | The items without later duplicates |
| `take`, `skip` | `xs.take(n)`, `xs.skip(n)` | The first `n` items; the items after the first `n` |
| `atoms` | `atoms(value)` | Every number in a nested structure, in one flat list |
| `repeat` | `step.repeat(n, initial...)` | The state after `n` applications of `step` |
| `while` | `step.while(initial...)` | The state reached while the last output of `step` is `true` |
| `string` | `number.string` | The number as text (dot form only) |
| `Math` | `Math.Sqrt(2)`, `sqrt(2)` | Mathematical functions and constants (see [Math Functions](#math-functions)) |

Operations that produce a collection (`range`, `filter`, `map`, `order`, `orderDesc`, `distinct`, `take`, `skip`, `atoms`) return a list. Built-in names such as `count` and `if` are not reserved: a definition of your own with the same name takes precedence.

### Keywords

| Keyword | Meaning |
|---|---|
| `true`, `false` | The Boolean values |
| `and`, `or`, `xor`, `not` | Logical operators |
| `div`, `mod` | Integer division and remainder |
| `public` | Make a member available to `open` |
| `open` | Use the public members of other algorithms without a prefix |
