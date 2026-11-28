# KatLang Tutorial

KatLang is a language for calculations. You write formulas, give them names, and combine them into larger calculations, and KatLang evaluates them in decimal arithmetic. This tutorial starts with a single expression and builds up, chapter by chapter, to collections, algorithms that take other algorithms, pattern matching, and larger programs.

Chapters 1 to 16 teach the language, each building on the ones before it. Chapters 17 to 19 cover advanced features, and the last two chapters sum up the layout rules and common mistakes and collect reference tables.

Every example is a complete program. Its result is shown below it, and **Open in Playground** runs it in your browser, where you can change it and try your own ideas.

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
10. [Algorithms as Arguments](#algorithms-as-arguments)
11. [Working with Collections](#working-with-collections)
12. [Collecting Parameters](#collecting-parameters)
13. [Deconstruction](#deconstruction)
14. [Pattern Matching](#pattern-matching)
15. [Loops](#loops)
16. [Organizing Programs](#organizing-programs)
17. [Formulas and Aliases in Depth](#formulas-and-aliases-in-depth)
18. [Algorithms Whose Calls Spread](#algorithms-whose-calls-spread)
19. [Captured Calls](#captured-calls)
20. [Layout and Common Pitfalls](#layout-and-common-pitfalls)
21. [Quick Reference](#quick-reference)

---

## Getting Started

### Your First Program

A program can be a single expression:

<!-- spec:first-program -->
```
2 + 3 * 4
```

**Result:** `14`

[Open in Playground](https://katlang.org/#1/7MF_wBg)

### Several Results

Every line of a program like this one is an output row, and commas separate several outputs on one line:

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

[Open in Playground](https://katlang.org/#1/6sXZQu)

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

[Open in Playground](https://katlang.org/#1/9rM6I13)

On one line the comma is required: `1 2` is an error, never two outputs. A line that ends with an operator or a comma continues on the next line, so a long calculation can span several lines ([Line Layout](#line-layout) has the full rule). If any part of a program fails, the program shows only the error, not the results of its other rows.

### Comments

`#` starts a comment, which runs to the end of the line:

```
# Floor area of a 4 m by 3 m room
4 * 3  # square metres
```

**Result:** `12`

[Open in Playground](https://katlang.org/#1/-O1tMMuIhYGB)

### Running Programs on Your Computer

The `katlang` command-line tool evaluates a program given on the command line or stored in a file. It writes the results to stdout and an error to stderr:

```text
katlang eval "2 + 3 * 4"
katlang run program.kat
```

[Command-Line Tool](#command-line-tool) shows how the tool shares programs as playground links.

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

[Open in Playground](https://katlang.org/#1/-kr6ay3Ge)

`/` is ordinary division. `div` divides and drops the fractional part (it truncates toward zero), `mod` gives the remainder (with the sign of the left number), and `^` raises to a power.

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

[Open in Playground](https://katlang.org/#1/8DBf8cVBj)

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

[Open in Playground](https://katlang.org/#1/8zRkt1de-s)

The [Quick Reference](#operators) lists every operator in precedence order.

### Decimal Numbers

KatLang numbers are decimal numbers with 34 significant digits. Decimal fractions such as `0.1` are stored exactly, so calculations with them have none of the binary rounding surprises found in many programming languages:

```
0.1 + 0.2
19.99 * 3
1 / 3
2.50 * 4
```

**Results:**
```
0.3
59.97
0.3333333333333333333333333333333333
10.00
```

[Open in Playground](https://katlang.org/#1/-6zyFRbHPXKKtHa)

A result can keep decimal places from its inputs: `2.50 * 4` is ten, displayed as `10.00`. [Displayed Decimal Places](#displayed-decimal-places) shows how to choose the number of decimal places.

Number literals may use `_` between digits and an exponent written with a lowercase `e`: `1_000_000`, `6.674e-11`, `1.5e3`. A decimal point needs digits on both sides (`0.5`, not `.5`). A written nonzero literal that rounds to zero, such as `1e-7000`, is a source error. Small representable numbers such as `1e-6176` are valid. Arithmetic can still round to zero. A result that needs more than 34 significant digits is rounded, and one too large to represent becomes `Infinity` or `-Infinity`.

Dividing by zero is an error, and so is raising zero to a negative power, as in `0 ^ -1`:

```
1 / 0
```

**Result:** error — division by zero.

[Open in Playground](https://katlang.org/#1/0zJ_a)

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

[Open in Playground](https://katlang.org/#1/-OFJ9-mqNwZ)

| Function | Meaning |
|---|---|
| `abs(x)`, `sign(x)` | Absolute value; the sign as `-1`, `0`, or `1` |
| `floor(x)`, `ceil(x)` | Round down; round up |
| `round(value, digits)` | Round to `digits` decimal places (halves round away from zero) |
| `sqrt(x)` | Square root |
| `exp(x)`, `ln(x)`, `lg(x)`, `log(value, base)` | Exponential; natural, base-10, and any-base logarithm |
| `pow(x, y)` | `x` raised to the power `y`, the same as `x ^ y` |
| `sin(radians)`, `cos(radians)`, `tan(radians)` | Trigonometric functions of an angle in radians |
| `asin(x)`, `acos(x)`, `atan(x)`, `atan2(y, x)` | Inverse trigonometric functions |
| `pi` | The constant π |
| `random(start, end)`, `randomInt(start, end)` | Random numbers (see below) |

There is no separate constant for Euler's number: write `exp(1)`. An undefined operation such as `sqrt(-1)` gives `NaN`.

Math functions are computed to the full 34 digits and never rounded to "nice" values. `pi` is π rounded to 34 digits, so `sin(pi)` is a tiny number of about `-1.16e-34` rather than `0`. Compare such results with a tolerance, or `round` them.

### Random Numbers

`random(start, end)` returns a decimal number and `randomInt(start, end)` a whole number, each at least `start` and less than `end`. So `randomInt(1, 7)` rolls a die:

```
randomInt(1, 7)
random(0, 1)
```

[Open in Playground](https://katlang.org/#1/8YY-vQ0Cy)

Every run draws new values, so this example has no fixed result. To repeat a run exactly, fix the random seed: with the command-line tool, `katlang eval "randomInt(1, 7)" --random-seed 42` prints the same number every time.

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

[Open in Playground](https://katlang.org/#1/-eNNbGdsvE)

`Name = expression` defines a **property**: a named calculation. A definition produces no output by itself; the last row reads the property `Area` and outputs its value. Property names are conventionally written in PascalCase. Names are case-sensitive, so `Area` and `area` are two different names. A name may contain letters, digits, and `_`, but cannot start with a digit.

### Definitions and Output Rows

A program is a mix of definitions and output rows. The order of the definitions does not matter, so a property may use one that is defined further down:

<!-- spec:output-rows-interleave-definitions -->
```
A = 3
A + B
B = 2
```

**Result:** `5`

[Open in Playground](https://katlang.org/#1/9yjpqTVE)

By convention, definitions come first and output rows last.

KatLang's general word for a calculation is **algorithm**. An algorithm can have *parameters* (its inputs, the subject of the next chapter), *properties* (named algorithms that belong to it), and *output* (the values its rows produce). The program itself is an algorithm: the properties you define at the top level belong to it, and its output rows are what the program displays. A property is a named algorithm. Where other languages have functions and modules, KatLang has this one idea.

### Names Are Bound Once

KatLang has no variables to update. A name is defined once, and a second definition of the same name in the same algorithm is an error, not a reassignment (the [clauses](#clauses) of a later chapter are the one exception):

```
Rate = 5
Rate = 6
```

[Open in Playground](https://katlang.org/#1/9xSsb9hR)

This program is rejected: `Property 'Rate' is already defined.` A value, once computed, never changes.

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

[Open in Playground](https://katlang.org/#1/_KNbdaiEd1d1)

The parentheses belong to the call, not to the definition: a property without parameters is defined without them, so `Answer() = 42` is an error.

The two forms differ only for a calculation that can give a different result each time. KatLang evaluates a property when it is first read, and later reads during the run reuse that value, while an explicit call evaluates the property anew.

### Counting Evaluations with `tick()`

`tick()` makes this rule visible. Each run starts a counter at zero; every time `tick()` runs, it adds one and returns the new count:

```
tick(), tick(), tick()
```

**Results:**
```
1
2
3
```

[Open in Playground](https://katlang.org/#1/9IRycnK)

A property that uses `tick()` runs it once, when it is first read. An explicit call runs it again, and later reads still see the stored value:

```
A = tick()
A, A, A(), A
```

**Results:**
```
1
1
2
1
```

[Open in Playground](https://katlang.org/#1/9CjGU8Mx)

An explicit call can also provide the stored value: if nothing has read `A` yet, the first `A()` stores its result for later reads, so `A(), A` shows `1` twice. Random numbers follow the same rule: with `Roll = randomInt(1, 7)`, `Roll` is one roll however often it is read, while each `Roll()` rolls again. Write `tick` with its parentheses: the name alone is not a number.

### Displayed Decimal Places

Two properties at the top level of a program decide how many digits its results show after the decimal point: `MinDecimalPlaces`, the fewest, and `MaxDecimalPlaces`, the most:

```
MinDecimalPlaces = 2
MaxDecimalPlaces = 4

pi
1 / 7
2.5
5 * 2
```

**Results:**
```
3.1416
0.1429
2.50
10.00
```

[Open in Playground](https://katlang.org/#1/-EYnXWoaQyy)

A number with more decimal places than the maximum is rounded to it, and one with fewer than the minimum is filled up with zeros, a whole number too. A digit exactly in the middle rounds away from zero, so `0.125` shown with two places is `0.13`. Only the display changes: calculations and comparisons always use the full value.

The two settings are independent, and either one can be used alone: with only a maximum nothing is filled up, and with only a minimum nothing is rounded. For a fixed number of decimal places, as for money, set both to the same value:

```
MinDecimalPlaces = 2
MaxDecimalPlaces = 2

Price = 19.99

Price * 3
Price * 3 / 7
1200
```

**Results:**
```
59.97
8.57
1200.00
```

[Open in Playground](https://katlang.org/#1/_UmJ12ol-r)

Each setting must be a whole number from 0 to 99, and the minimum must not be greater than the maximum. When neither is set, a number is shown with the digits it has. The command-line options `--min-decimal-places` and `--max-decimal-places` work the same way; when a program and the tool both set one, the smaller number is used.

---

## Parameters

### Inferred Parameters

```
Tax = price * 0.2
Tax(50)
```

**Result:** `10.0`

[Open in Playground](https://katlang.org/#1/8w68wgIl)

`price` is not defined anywhere, so KatLang treats it as a **parameter** of `Tax`: an input that the caller supplies. `Tax(50)` calls `Tax` with `price` equal to `50`. A short definition like this, one expression over its inputs, is called a **formula**. Parameter names are conventionally written in camelCase, which keeps them apart from PascalCase property names; in physics and similar fields, prefer the field's standard notation, as in `v = s / t`.

Only a name that nothing defines becomes a parameter. Built-in names such as `pi`, `sqrt`, and `abs` are defined, so they never become parameters.

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

[Open in Playground](https://katlang.org/#1/-EP3hc-5ZGz)

Take care when the reading order is not the order you want to call with: `Ratio = b / a` takes `b` first.

### Explicit Parameter Lists

You can also list the parameters yourself:

```
Hypotenuse(a, b) = sqrt(a ^ 2 + b ^ 2)
Hypotenuse(3, 4)
```

**Result:** `5`

[Open in Playground](https://katlang.org/#1/-Qdyej2oxT)

An explicit list fixes the parameters' names and order. It is also **closed**: every other name in the body must refer to something that is defined, or the definition is an error. An explicit list is also the way to accept an argument you do not use:

```
KeepFirst(a, b) = a
KeepFirst(42, 999)
```

**Result:** `42`

[Open in Playground](https://katlang.org/#1/-yb4O2IAej)

Inferred parameters keep short formulas short; explicit lists document the inputs of larger algorithms.

### Undefined Names in the Program

The program itself is never called, so nothing can supply a parameter to it, and an undefined name at the top level is an error. This is how KatLang reports a typo:

```
Total = 5
Totl + 1
```

**Result:** error — `Totl` is not defined, so it becomes a parameter of the program, which nothing supplies; the report suggests `Total`.

[Open in Playground](https://katlang.org/#1/9o6YBkMq)

### Each Argument Is Evaluated At Most Once

An argument is evaluated only when its value is first needed, and at most once: however many times the parameter is read, those reads reuse the same result. An argument that is never used is never evaluated, even if evaluating it would fail:

```
Keep(x) = 42
Keep(1 / 0)
```

**Result:** `42`

[Open in Playground](https://katlang.org/#1/85vh9pxL)

`tick()` shows both rules at once. The argument of `Ignore` never runs, and the argument of `Double` runs once, however often `x` is read:

```
Ignore(x) = 7
Double(x) = x + x
Ignore(tick()), Double(tick()), tick()
```

**Results:**
```
7
2
2
```

[Open in Playground](https://katlang.org/#1/_cnYKwP29CJSNCtoc5)

A call with the wrong number of arguments is an error, reported before any of its arguments runs. (Spreads, a later topic, are the one exception.)

### Formulas That Use Formulas

A formula can use another formula that still needs inputs. KatLang then hands those inputs on, and they become parameters of the formula that uses it:

```
Speed = distance / time
KineticEnergy = mass * Speed ^ 2 / 2

KineticEnergy(2, 10, 5)
```

**Result:** `4`

[Open in Playground](https://katlang.org/#1/_VERErsoMiT)

`KineticEnergy` uses `Speed`, which needs `distance` and `time`, so `KineticEnergy` takes them as well and hands them on to `Speed`. Its parameters are its own names first, followed by the ones it hands on: `KineticEnergy(mass, distance, time)`. A formula that works with no arguments is not handed anything; it is simply read, like a property.

Inputs are handed on **by name**, so two formulas that need the same name share one input:

```
F(x) = x + 1
G(x) = x * 2
H = F + G

H(3)
```

**Result:** `10`

[Open in Playground](https://katlang.org/#1/-sf-C2oRu)

`H = F + G` means `H(x) = F(x) + G(x)`. Because the names matter, an explicit parameter list must use the same names: `KineticEnergy(mass, distance, time) = mass * Speed ^ 2 / 2` works, while `KineticEnergy(m, d, t) = m * Speed ^ 2 / 2` has nothing named `distance` or `time` to hand on, and calling it is an error. An algorithm with an explicit list never gains a parameter this way.

A built-in operation that needs an input hands it on in the same way:

```
Half = abs / 2

Half(-6)
```

**Result:** `3`

[Open in Playground](https://katlang.org/#1/854WZQUohxxCYOp7)

A definition whose whole body is the name of another formula, such as `Doubled = Double`, is different again: it is an **alias**, the same formula under a second name ([Aliases, Forwarding, and Explicit Calls](#aliases-forwarding-and-explicit-calls)).

<a id="reordering-parameters-with-grace-operator"></a>
<a id="grace-with-dotcall"></a>

### Reordering Parameters with Grace

When the first-appearance order is not the order you want, the Grace marker `~` adjusts it: `~x` moves the parameter `x` one position earlier, and `x~` one position later.

```
Divide = y / ~x
Divide(2, 10)
```

**Result:** `5`

[Open in Playground](https://katlang.org/#1/8SEE7FopT)

Without the marker, `y` would be the first parameter. The marker is written directly against the name (`~x`, not `~ x`), and it applies only to inferred parameters: with an explicit parameter list, write the order you want. A marker on a name that is not an inferred parameter, such as a property or `~sqrt`, is an error. [Several Grace Markers](#several-grace-markers) shows how markers combine.

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

[Open in Playground](https://katlang.org/#1/--vDxoLrTShh)

Comparisons produce the **Boolean** values `true` and `false`. The ordering operators `<`, `>`, `<=`, and `>=` compare numbers. `==` and `!=` compare any two values, including the text, sequences, and lists of later chapters; values of different kinds are simply unequal, so `true == 1` is `false`.

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

[Open in Playground](https://katlang.org/#1/-gcyJ6Vbsd)

A chain is `true` when every adjacent pair holds, and it evaluates each operand once.

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

[Open in Playground](https://katlang.org/#1/_So2_TTK5xu0)

`xor` is `true` when exactly one operand is `true`; unlike `or`, it is `false` when both are. Comparisons bind more tightly than the logical operators, so `x > 0 and x < 10` needs no parentheses, and `not x > 3` means `not (x > 3)`.

`and` and `or` evaluate their right operand only when the result still depends on it: `false and …` is `false` and `true or …` is `true`, whatever follows. So `and` can guard a calculation:

```
GoodAverage = games != 0 and points / games >= 20

GoodAverage(4, 100)
GoodAverage(0, 0)
```

**Results:**
```
true
false
```

[Open in Playground](https://katlang.org/#1/_TnpiFcoOZu9I55FnmSWafLolTqI-N0FasYhjL2xCf6VD6U57nHbY)

In `GoodAverage(0, 0)` the left operand is `false`, so the division is never evaluated. A comparison chain does not stop early in this way: `3 < 2 < 1 / 0` is an error, while `3 < 2 and 2 < 1 / 0` is `false`.

Only `true` and `false` are truth values. Numbers are not, so `1 and 0` is an error: write the comparison you mean, such as `x != 0`.

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

[Open in Playground](https://katlang.org/#1/-yoMzot5BU)

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

[Open in Playground](https://katlang.org/#1/_aE8xVqNV3Yr)

An `if` can sit inside another `if` to choose among more than two values:

```
Sign = if(x > 0, 1, if(x < 0, -1, 0))

Sign(-4), Sign(0), Sign(9)
```

**Results:**
```
-1
0
1
```

[Open in Playground](https://katlang.org/#1/_fEceCCKPDDQYKHdoSMS0PcYMCuGd7YjlL)

The condition must be a Boolean:

```
if(1, 2, 3)
```

**Result:** error — the condition `1` is a number, not a Boolean.

[Open in Playground](https://katlang.org/#1/6B_UJI)

---

## Text

Text values, called **strings**, are written in single quotes and displayed without them:

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

[Open in Playground](https://katlang.org/#1/_eHm4VKiwRj)

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

[Open in Playground](https://katlang.org/#1/_ejYBKazphq)

### Text Is Written as It Is

A string is raw: its text is exactly what is written between the single quotes. Nothing inside it is evaluated and there are no escapes, so braces, backslashes, and double quotes are ordinary characters:

<!-- spec:string-single-quoted-text-is-raw -->
```
'{x}'
'C:\temp'
'say "hi"'
```

**Results:**
```
{x}
C:\temp
say "hi"
```

[Open in Playground](https://katlang.org/#1/8rWKt0yUTp)

A string is written on one line and cannot contain a single quote. Single quotes are the only way to write text: a double quote outside a string or a comment is an error, and there is no string interpolation.

### Results Are Values, Not Messages

A KatLang result is the calculated value itself, not a sentence about it. There is no `+` for text and no other way to build one string out of several values, so a number never becomes part of a text: it stays a number, with its full precision. To label a result, output the label as a value of its own:

```
Score = 72

Score, if(Score >= 50, 'pass', 'fail')
```

**Results:**
```
72
pass
```

[Open in Playground](https://katlang.org/#1/-aS62yT6wUd)

---

## Dot Calls

The calls so far have been written `f(a)`. KatLang has a second spelling of the same call, `a.f`, in which the value before the dot becomes the call's first argument. The rest of this tutorial uses both spellings, because the dot lets a calculation read from left to right.

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

[Open in Playground](https://katlang.org/#1/-6Qw6xF9O)

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

[Open in Playground](https://katlang.org/#1/-wnxP4XXK)

The value before the dot is called the **receiver**, and it is passed as a single argument. The rule applies to every algorithm, your own and the built-in ones alike:

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

[Open in Playground](https://katlang.org/#1/8TDTvG4cf)

A leading minus is not part of the receiver: `-7.abs` is `-(7.abs)`, which is `-7`. Write `(-7).abs` to pass the negative number.

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

[Open in Playground](https://katlang.org/#1/_RoOqOuNyn)

`3.Double.Increment` reads in the order in which the work happens — take 3, double it, then increment the result — while the equivalent nested call `Increment(Double(3))` has to be read from the inside out. The order of the steps matters: `3.Increment.Double` is `Double(Increment(3))`.

### Members

A dot can also select a **member** of an algorithm. `Math` is a built-in algorithm whose members are the functions and constants of the [Math table](#math-functions), named in PascalCase:

```
Math.Pi
Math.Sqrt(16)
```

**Results:**
```
3.141592653589793238462643383279503
4
```

[Open in Playground](https://katlang.org/#1/9RlpDnX5)

When the receiver has a member with the name after the dot, the dot selects that member, and the receiver is not passed as an argument. Numbers, text, and the sequences and lists of the next chapters have no members, so for them the dot means a call, apart from `.string` below. [Algorithms as Containers](#algorithms-as-containers) shows how to define algorithms with members of your own.

### Converting a Number to Text

`.string` turns a number into text:

```
42.string
42.string == '42'
```

**Results:**
```
42
true
```

[Open in Playground](https://katlang.org/#1/8i0fPZCnzX)

`.string` exists only in dot form: `string(42)` is not defined. It gives all of a number's digits, whatever `MinDecimalPlaces` and `MaxDecimalPlaces` say, and it works on a number only.

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

[Open in Playground](https://katlang.org/#1/_XlJoadH7BXW)

In the body, `width * height` and `2 * (width + height)` are two outputs. A call returns one value, so the caller receives the two outputs together as a **sequence**: an ordered group of values, displayed in parentheses. This is how an algorithm returns several related results, here the area and the perimeter of a rectangle.

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

[Open in Playground](https://katlang.org/#1/8pZ24MGo)

### Writing Sequences

Parentheses around comma-separated items make a sequence value:

<!-- spec:value-three-items -->
```
(1 + 1, 2 + 2, 3 + 3)
```

**Result:** `(2, 4, 6)`

[Open in Playground](https://katlang.org/#1/9TU42qL1)

Parentheses around a single item only group it, as in arithmetic: `(7)` is just `7`, and `((1, 2))` is the same sequence as `(1, 2)`. So a sequence has at least two items, or none: `()` is the **empty sequence**. Sequences nest:

```
(7)
((1, 2))
()
(1, (2, 3))
```

**Results:**
```
7
(1, 2)
()
(1, (2, 3))
```

[Open in Playground](https://katlang.org/#1/8jTKnv4djwQ)

`(1, (2, 3))` has two items, the second of which is itself a sequence.

### Counting and Selecting

`count` gives the number of values, and postfix brackets select by position: `value[index]`. Positions are **zero-based**: `[0]` selects the first value.

<!-- spec:index-selects-atom -->
```
Nums = 10, 20, 30, 40, 50

# Select the third value (index 2):
Nums[2]
```

**Result:** `30`

[Open in Playground](https://katlang.org/#1/_cl8gkPN3hWH)

```
Pairs = (1, 2), (3, 4)

Pairs.count
Pairs[1]
Pairs[1][0]
```

**Results:**
```
2
(3, 4)
3
```

[Open in Playground](https://katlang.org/#1/-OWzL3CrO0)

Selection returns the chosen value as it is: selecting a sequence gives the whole sequence `(3, 4)`, and a further `[0]` selects inside it. An index outside the sequence is an error, and so is a negative one; there is no counting from the end.

Several indices select several values at once, in the order written. The selected values form one sequence; a single index gives the value itself, and no index at all gives the empty value `()`:

```
Data = 10, 20, 30

Data[2, 0, 2]
Data[0]
Data[]
```

**Results:**
```
(30, 10, 30)
10
()
```

[Open in Playground](https://katlang.org/#1/-ghboDvq-J)

The empty sequence has no positions, so `().count` is `0`. A number, a Boolean, or a string is one value with the single position `0`, so `count('abc')` is `1`; KatLang has no character selection.

### Values Stay Values

A sequence is one value wherever it goes. In particular, passing it to an algorithm passes **one** argument:

<!-- spec:fixed-call-preserves-boundaries -->
```
Pair = 10, 20
Add(x, y) = x + y

Add(Pair)
```

**Result:** error — `Pair` is one argument, but `Add` needs two.

[Open in Playground](https://katlang.org/#1/-qW5_u9RG)

KatLang never takes a value apart on its own, and a dot call passes its receiver the same way: `(10, 20).Add` is `Add((10, 20))`, which fails for the same reason. To use the items of a value, say so: select them with brackets, as in `Add(Pair[0], Pair[1])`, open the value with `*` (next section), or declare a parameter that unpacks it ([Unpacking an Argument](#unpacking-an-argument)). Arithmetic does not reach inside a value either: `Pair * 2` is an error.

### Opening a Value with `*`

A star after a value opens it: `value*` supplies the value's items to the surrounding context one by one. An expression `value*` is called a **spread**. At the top level the items become separate outputs:

<!-- spec:property-value-boundary -->
```
Coordinates = 10, 20
Coordinates
Coordinates*, 997
```

**Results:**
```
(10, 20)
10
20
997
```

[Open in Playground](https://katlang.org/#1/-aiU7aoo2)

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

[Open in Playground](https://katlang.org/#1/-UW5_uxSR)

`Pair*.Add` is the dot spelling of `Add(Pair*)`. Spreads can appear wherever several items can, such as among the items of a new sequence, and several times in one call:

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

[Open in Playground](https://katlang.org/#1/-6o-ImyhQT)

```
Distance(x1, y1, x2, y2) = sqrt((x2 - x1) ^ 2 + (y2 - y1) ^ 2)
P = 0, 0
Q = 3, 4

Distance(P*, Q*)
```

**Result:** `5`

[Open in Playground](https://katlang.org/#1/_OoQl8tQGlNrEWl)

A spread opens exactly one level: `((1, 2), 3)*` supplies the two items `(1, 2)` and `3`, and the inner sequence stays whole. A single value supplies itself, so `7*` is just `7`, and spreading the empty sequence `()` supplies nothing. A spread also works among the indices of a selection: with `Order = 2, 0`, `Data[Order*]` is `Data[2, 0]`.

A call computes its spreads first, while it gathers its arguments, so a spread that fails makes the call fail with the same error:

```
Add(x, y) = x + y
Bad = 1 / 0

Add(Bad*)
```

**Result:** error — division by zero, while computing `Bad*` for the call.

[Open in Playground](https://katlang.org/#1/-unjViiAI)

This happens even where the argument would never be used. Not even `if` can skip a spread: `if(false, Bad*, 0)` fails in the same way, while `if(false, Bad, 0)` is `0`.

When another item follows a spread on the same line, separate the two with a comma, as in `A*, B`: without the comma, `A* B` is the multiplication `A * B`. At the end of a line the star's spacing decides; see [Spread or Multiplication?](#spread-or-multiplication).

### Unpacking an Argument

A parameter written as a parenthesized **pattern** takes one argument and unpacks its items into names:

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

[Open in Playground](https://katlang.org/#1/_YGtI_yzEPg)

`Length` has one parameter, the pattern `(x, y)`, so it takes one argument, a pair, and names the pair's two items. A parenthesized pattern unpacks only a **sequence** of exactly its length, so `Length(5)` and `Length((1, 2, 3))` are errors. There is no pattern `(x)`, because no sequence has exactly one item: to take one whole value, write `x`.

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

[Open in Playground](https://katlang.org/#1/-G1LR7yZd0rQL)

---

## Lists

### List Values

Square brackets make a **list**:

<!-- spec:list-literal -->
```
[1, 2, 3]
```

**Result:** `[1, 2, 3]`

[Open in Playground](https://katlang.org/#1/7DA8Y)

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

[Open in Playground](https://katlang.org/#1/-yKdAu2GooCo)

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

[Open in Playground](https://katlang.org/#1/8wnTsGkJr)

### Working with Lists

Lists support the same operations as sequences: counting, zero-based selection, and spreading.

```
Primes = [2, 3, 5, 7]

Primes.count
Primes[0]
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

[Open in Playground](https://katlang.org/#1/_aFbfepfXLR)

With the star, the items of `Primes` become elements of the new list; without it, the whole list `Primes` is one element. Lists nest, and selection goes one level at a time:

```
Grid = [[1, 2], [3, 4]]

Grid[1]
Grid[1][0]
```

**Results:**
```
[3, 4]
3
```

[Open in Playground](https://katlang.org/#1/-oeYucLuR4)

A list, too, is one value in a call: `Add([10, 20])` passes one argument, and `Add([10, 20]*)` passes two.

### List Patterns

A bracketed pattern unpacks a list the way a parenthesized pattern unpacks a sequence. Since a list keeps even one element, `[x]` is a pattern too:

```
Only([x]) = x
PairSum([x, y]) = x + y

Only([10])
PairSum([10, 20])
```

**Results:**
```
10
30
```

[Open in Playground](https://katlang.org/#1/_eF2uzUmdRAW)

Each pattern unpacks only its own kind: `Only(10)` and `PairSum((10, 20))` are errors, because a number is not a list and neither is a sequence. Patterns nest, and every level keeps its kind; here a sequence whose first item is a list:

```
F(([x, y], z)) = x + y + z

F(([10, 20], 30))
```

**Result:** `60`

[Open in Playground](https://katlang.org/#1/-kgbzOuCuuL)

| Pattern | Matches |
|---|---|
| `x` | any one value, whole |
| `()` | the empty sequence |
| `(x, y)` | a sequence of exactly two items |
| `[]` | the empty list |
| `[x]` | a list of exactly one element |
| `[x, y]` | a list of exactly two elements |

### Lists Are Calculated on Demand

A list does not calculate its items when it is written. Each item is calculated the first time something reads it, and at most once:

<!-- spec:lazy-list-selection-reads-only-the-selected-position -->
```
[10, 1 / 0][0]
```

**Result:** `10`

[Open in Playground](https://katlang.org/#1/4i9WsWzThoM)

Selection reads only the item it names, so the division by zero is never calculated. Counting a written list reads no item at all, because its length is known: `[10, 1 / 0].count` is `2`. A spread in a list is different: the list needs it to know its length, so the spread runs as soon as the list is built, and `[(1 / 0)*].count` is an error. Displaying a list reads every item, so a list whose item fails makes the program fail:

```
[1, 1 / 0]
```

**Result:** error — division by zero.

[Open in Playground](https://katlang.org/#1/6jFpWCe7)

A sequence is different: computing `(10, 1 / 0)` computes both of its items, so `(10, 1 / 0)[0]` is an error.

### Lists or Sequences?

- A **sequence** is what several outputs become, and what parentheses write. It is the natural shape for results that belong together, like the area and perimeter returned by `Rectangle`.
- A **list** is a collection that keeps its exact shape, even with one item or none. Use lists for data such as measurements, scores, or the rows of a table.

The collection operations of the next chapters accept both, and those that produce a collection return a list.

---

<a id="algorithms-as-values"></a>

## Algorithms as Arguments

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

[Open in Playground](https://katlang.org/#1/_eJnhQsIZW)

The parameter `f` receives an algorithm, and `f(x)` calls it. Passing an algorithm does not run it: `f` holds the algorithm itself until the body calls it. Inferred parameters work the same way: a name that is called becomes a parameter that receives an algorithm.

```
Twice = f(f(x))
Square = n * n

Twice(Square, 3)
```

**Result:** `81`

[Open in Playground](https://katlang.org/#1/-eOejHQ44C)

Anything that can be called, whether an algorithm of your own, a built-in operation, or a Math function, is called a **callable**.

Passing works in one direction: a call can receive an algorithm, but its result is always a calculated value, which cannot be called. A plain value cannot be called either, so `Apply(5, 4)` is an error. A call must also receive all of its arguments: for `Add(x, y) = x + y`, `Add(10)` is an error, not a partly applied `Add`.

### Brace Algorithms

Braces write an algorithm without giving it a name:

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

[Open in Playground](https://katlang.org/#1/-QmeHLglp)

The undefined names inside the braces are the brace algorithm's own parameters, in order of first appearance. A name that the algorithm around the braces defines or takes as a parameter keeps that meaning inside them. Here `n` is the brace algorithm's parameter, and `k` is the parameter of `Shift`:

```
Apply(f, x) = f(x)
Shift(k) = Apply({n + k}, 1)

Shift(10)
```

**Result:** `11`

[Open in Playground](https://katlang.org/#1/-KmeFGmy0jEpToq08B8tUOxMYzbyp)

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

[Open in Playground](https://katlang.org/#1/-QOYCbVMhJ)

So when you design an algorithm that takes other algorithms, put the data parameter first; it will then work well in dot chains.

### Parentheses versus Braces

Parentheses and braces look alike but mean different things:

- `(n + 1)` is just the expression `n + 1`: the parentheses only group it, and `n` means whatever it means around it.
- `{n + 1}` is an algorithm that computes `n + 1` whenever it is called, and `n` is its own parameter unless `n` is already defined around it.

A brace algorithm without parameters simply produces its output when it is read, so `{1, 2, 3}.count` is `3`, just like `(1, 2, 3).count`. Empty braces are an algorithm with no output: unlike the empty sequence `()`, `{}` is an error where a value is required.

Braces around a definition's whole body give it room for definitions of its own. They belong to that algorithm, and the rows that are not definitions are its output:

```
Circle(r) = {
    Area = pi * r ^ 2
    Area.round(2)
}

Circle(1)
```

**Result:** `3.14`

[Open in Playground](https://katlang.org/#1/_eosBWB-cO)

Such braces change nothing about the parameters: `F(a) = { b + a }` is as closed as `F(a) = b + a`. [Local Definitions](#local-definitions) has the full rules.

---

## Working with Collections

### Ranges

`range(start, stop)` lists the whole numbers from `start` to `stop`, inclusive:

<!-- spec:range-inclusive -->
```
range(1, 5)
```

**Result:** `[1, 2, 3, 4, 5]`

[Open in Playground](https://katlang.org/#1/6BjMj)

When `start` is greater than `stop`, the range counts down: `range(5, 1)` is `[5, 4, 3, 2, 1]`.

### Pipelines

Collection operations combine into pipelines:

```
range(1, 10).filter{n mod 2 == 0}.map{n * n}.sum
```

**Result:** `220`

[Open in Playground](https://katlang.org/#1/-eGNjQ2zstK)

Read it from left to right: the numbers from 1 to 10, keep the even ones, square each of them, add them up. Every step is a dot call, so `range(1, 10).filter{...}` is `filter(range(1, 10), {...})`, and each brace algorithm receives one element at a time as its parameter `n`.

A long pipeline can be split across lines, because a line that starts with `.` continues the line before it:

<!-- spec:dot-chain-continuation -->
```
(1, 2, 3)
.map { n * 2 }
.sum
```

**Result:** `12`

[Open in Playground](https://katlang.org/#1/8TUpbVnTFJ)

A named algorithm works as well as a brace algorithm:

<!-- spec:filter-keeps-matching -->
```
IsEven = x mod 2 == 0
filter((1, 2, 3, 4, 5, 6), IsEven)
```

**Result:** `[2, 4, 6]`

[Open in Playground](https://katlang.org/#1/-Oczfo7GF53)

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

[Open in Playground](https://katlang.org/#1/_qBLGoxwTjzfB6p)

The last row chains two operations to find the three best scores. In the same way, `min`, `first`, and `last` give the smallest, the first, and the last item, `distinct` drops later duplicates, and `skip(n)` drops the first `n` items. Each operation can also be written as an ordinary call, such as `count(Scores)` or `take(Scores, 3)`. The test given to `filter` must return a Boolean: `{n mod 2 == 0}` is right, while `{n mod 2}` is an error. `min`, `max`, `avg`, `first`, and `last` need at least one item, and the `sum` of an empty collection is `0`. [Built-in Operations](#built-in-operations) lists every operation.

### One Collection Argument

A collection operation takes the whole collection as one argument: a list, a sequence, or a property holding either.

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

[Open in Playground](https://katlang.org/#1/-oE7efmbAcC)

Separate numbers are not a collection:

```
sum(1, 2, 3)
```

**Result:** error — `sum` takes one collection, but three separate numbers were passed.

[Open in Playground](https://katlang.org/#1/5hPGKl)

To combine collections, build one collection from their items: with `A = 1, 2` and `B = 3, 4`, `sum((A*, B*))` is `10`. The same goes for two numbers: `max(3, 5)` is an error, and `max((3, 5))` is `5`.

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

[Open in Playground](https://katlang.org/#1/_XEsajHhd-C)

Add a star to use the items of a result directly:

```
[3, 1, 2].order*, 997
```

**Results:**
```
1
2
3
997
```

[Open in Playground](https://katlang.org/#1/9QsFist)

### Callbacks Receive One Element

`map` and `filter` call the algorithm they are given, the **callback**, with one element at a time, passed as **one** argument; `reduce`, below, also passes the result so far. When the elements are pairs, the callback receives each pair whole, and can select its items or unpack it with a pattern parameter:

```
Pairs = [(2, 3), (4, 5)]

Pairs.map{p[0] * p[1]}
```

**Result:** `[6, 20]`

[Open in Playground](https://katlang.org/#1/-eWy-Do4anE)

<!-- spec:map-pair-callback -->
```
Swap((a, b)) = (b, a)
map(((1, 2), (3, 4)), Swap)
```

**Result:** `[(2, 1), (4, 3)]`

[Open in Playground](https://katlang.org/#1/-cPv4eEPTRr)

A callback with two ordinary parameters, such as `Add(a, b) = a + b`, does not accept a pair element, just as `Add((1, 2))` is an error. A list element is unpacked by a list pattern instead, as in `LSwap([a, b]) = [b, a]`.

A brace callback's parameters are its undefined names, so choose names that are not already defined around it. A built-in name is defined too, so `[10, 20, 30].map{count + 1}` hands each element to `count` and gives `[2, 2, 2]`. Likewise, a name that appears only inside the braces belongs to the callback, not to the algorithm around it: in `Scale = values.map{n * factor}`, the callback has the parameters `n` and `factor`, and calling it with one element fails. Declare the input instead, and the braces use it:

```
Scale(values, factor) = values.map{n * factor}

Scale([1, 2, 3], 10)
```

**Result:** `[10, 20, 30]`

[Open in Playground](https://katlang.org/#1/_dkw1vqizKvc4DYEf6a)

A callback runs only when it is called, so a callback that is never called, here because the collection is empty, cannot fail:

```
Broken(x) = x / 0

map([], Broken)
```

**Result:** `[]`

[Open in Playground](https://katlang.org/#1/-6kJGyZPSAJteE)

### A Callback Returns One Value

A callback's result is exactly what an ordinary call of it returns. When the callback has several output rows, they become one sequence value: one element of the result, never several.

```
Both(x) = x, x

[1, 2].map(Both)
```

**Result:** `[(1, 1), (2, 2)]`

[Open in Playground](https://katlang.org/#1/--kS2F3ecPJ9-d)

`()` and `[]` are ordinary values too, so mapping with an identity callback returns the same list:

<!-- spec:map-identity-preserves-empty-elements -->
```
Id(x) = x
map([(), 1, [], 2], Id)
```

**Result:** `[(), 1, [], 2]`

[Open in Playground](https://katlang.org/#1/-8djNSiHh8)

A callback that returns `()` therefore keeps an `()` element; `()` does not mean "skip this element". Use `filter` to leave elements out:

```
Half(n) = if(n mod 2 == 0, n / 2, ())

[4, 5, 6].map(Half)
[4, 5, 6].filter{n mod 2 == 0}.map(Half)
```

**Results:**
```
[2, (), 3]
[2, 3]
```

[Open in Playground](https://katlang.org/#1/_OHhT32EFcAQQ)

For the same reason, an output row written by mistake is not an error: it silently turns every element into a sequence value. Here the `Tax` row was meant only as a check, and without it the result is `[120, 60]`:

```
Total(price) = {
    Tax = price div 5
    Tax
    price + Tax
}

[100, 50].map(Total)
```

**Result:** `[(20, 120), (10, 60)]`

[Open in Playground](https://katlang.org/#1/_UjpO9Qeqxyv)

### Folding with `reduce`

`reduce(collection, reducer, initial)` combines the elements into one value. The reducer is called with an element and the result so far, the **accumulator**, which starts as `initial`:

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

[Open in Playground](https://katlang.org/#1/_SF9WGeiVAJ)

The parameters of a brace reducer follow first appearance, so write the element's name first and the accumulator's name second. For two elements `a` and `b`, the calls nest as `reducer(b, reducer(a, initial))`, and each result is passed on whole as the next accumulator:

```
Pair(x, acc) = x, acc

[1, 2].reduce(Pair, 0)
```

**Result:** `(2, (1, 0))`

[Open in Playground](https://katlang.org/#1/-kW2NvaZsClB)

An accumulator is calculated only when the reducer uses it. `reduce` runs the last call first, and reading its accumulator runs the call before it, back to `initial`. So a reducer that ignores its accumulator skips every earlier call, and `initial` too:

```
Last(x, acc) = x

[1, 2, 3].reduce(Last, 1 / 0)
```

**Result:** `3`

[Open in Playground](https://katlang.org/#1/-ga8A5N6btCrUPQNOlbAfO)

Only reducer calls and `initial` can be skipped: `reduce` reads its whole collection before the first call, so an element that fails still makes the fold fail. The `reduce` of an empty collection is `initial` itself.

### Pipelines Read Only What They Need

Like a written list, the list that `map`, `filter`, or `take` returns calculates its items only when they are read. `map` runs its callback only for the items that are read, and `filter` looks for matches only as far as its reader needs:

<!-- spec:lazy-map-runs-its-mapper-only-for-the-positions-read -->
```
[1, 2].map{if(n == 1, 10, 1 / 0)}.first
```

**Result:** `10`

[Open in Playground](https://katlang.org/#1/-wMBMGtfUNDn2vQNbee00)

<!-- spec:lazy-filter-discovers-only-the-matches-it-needs -->
```
[1, 0].filter{1 / n > 0}.take(1)
```

**Result:** `[1]`

[Open in Playground](https://katlang.org/#1/--MXU0d1K-1UCAMpaoquc)

Operations that need every item read them all, in order: adding them up with `sum`, opening the list with `*`, comparing with `==`, and displaying a result.

### Flattening with `atoms`

`atoms` collects every number from a nested structure into one flat list:

<!-- spec:atoms-recursive-flatten -->
```
atoms(((1, 2), (3, 4)))
```

**Result:** `[1, 2, 3, 4]`

[Open in Playground](https://katlang.org/#1/9AjQYkSY)

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

[Open in Playground](https://katlang.org/#1/_uSFsNEaIh3Y5dQ)

Inside the brace algorithm, `Mean` is the property of the program, and the undefined `x` is the element.

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

[Open in Playground](https://katlang.org/#1/_dmPlEQ-WI)

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

[Open in Playground](https://katlang.org/#1/_Uon847Hf50)

Collected arguments are not evaluated when the call starts. `count`, `first`, `last`, `take`, and selection on the collecting parameter evaluate only the items they read, while using it as a whole list, for example returning it or passing it to `map`, evaluates every item. An algorithm that can be called without arguments, like `Collect`, can also be read by its name alone: `Collect` is the value of `Collect()`, worked out once and reused, as for a property.

### Passing Items with `*`

To pass a stored collection to `Mean`, spread it, so that its items become the arguments. `Mean(Data)` would pass one argument, the whole list, and the sum would fail on that one item, which is not a number:

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

[Open in Playground](https://katlang.org/#1/_PmPlD1ZMYW)

Compare the built-in `avg`, which takes one collection argument: `Data.avg` needs no star. A collecting parameter collects separate arguments, while a collection operation receives one collection.

### Fixed and Collecting Parameters Together

A collecting parameter can stand beside fixed parameters, which take one argument each. The fixed parameters take their arguments from the front and the back, and the collecting parameter collects the rest:

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

[Open in Playground](https://katlang.org/#1/_tZMRy5jXcpRU)

A parameter list may contain only one collecting parameter of its own.

### Collecting Inside a Pattern

A star also works inside a pattern, where it collects the remaining items of the one argument that the pattern unpacks:

```
Rest((x, *others)) = others
Items([*xs]) = xs.count

Rest((1, 2, 3))
Items([5, 6])
Items([])
```

**Results:**
```
[2, 3]
2
0
```

[Open in Playground](https://katlang.org/#1/_RlIodmQLAY2l)

| Pattern | Matches |
|---|---|
| `(x, *rest)` | a non-empty sequence; `rest` is the list of the others |
| `(*xs)` | any sequence; `xs` is the list of its items |
| `[x, *rest]` | a non-empty list; `rest` is the list of the others |
| `[*xs]` | any list; `xs` is the list of its elements |

A pattern counts separately from the parameter list around it, so it may collect even when the list does.

### Forwarding Collected Arguments

To pass collected arguments on to another algorithm, spread the collected list:

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

[Open in Playground](https://katlang.org/#1/_UjsUxLbxHg)

`Forward` passes along exactly the arguments it received: `Forward(1, 2)` passes two numbers, and `Forward([1, 2])` passes one list. Spreading a collecting parameter into a call passes its arguments on without computing them, so each is computed only if the called algorithm uses it.

### Values and Items at a Glance

The chapters since Sequences rest on one idea: a value stays one value until you open it explicitly. With `A = [1, 2]`, `B = [3, 4]`, and an algorithm `F`, called or defined:

| You write | Meaning |
|---|---|
| `F(A)` | One argument: the list `A` |
| `F(A*)` | Two arguments: the items `1` and `2` |
| `A.F` | The call `F(A)`, unless `A` has a member `F` |
| `A*.F` | The call `F(A*)` |
| `A[0]` | One item of `A`, selected as a value: `1` |
| `(A*, B*)`, `[A*, B*]` | One sequence, or one list, of the items `1, 2, 3, 4` |
| `F(*xs) = ...` | `F` collects its arguments into the list `xs` |
| `F((x, y)) = ...` | `F` takes one sequence argument and unpacks its two items |
| `F([x, y]) = ...` | `F` takes one list argument and unpacks its two elements |
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

[Open in Playground](https://katlang.org/#1/4At2NphZ)

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

[Open in Playground](https://katlang.org/#1/8IaoMo2fx)

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

[Open in Playground](https://katlang.org/#1/-0o9hEGGkm)

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

[Open in Playground](https://katlang.org/#1/8YL93XBVL)

Without a collecting name, the number of names must match the number of items: `x, y = 1, 2, 3` is an error as soon as `x` or `y` is used. All the names of one deconstruction share one calculation of the right-hand side, which runs when the first of them is needed.

---

## Pattern Matching

### Clauses

Here is the one exception to [Names Are Bound Once](#names-are-bound-once): an algorithm with parameters may have several definitions of the same name. They are the **clauses** of one **conditional algorithm**, and their parameter lists may hold patterns such as literals:

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

[Open in Playground](https://katlang.org/#1/_KoSwvhuGNeM)

A call tries the clauses from top to bottom and uses the first one whose patterns match. A literal such as `0` matches only that value; a name such as `n` matches any value and binds it. Put the catch-all clause last. Patterns match fixed values and shapes, not conditions, so a range of values still takes an `if`, as in `Describe`.

While the clauses are tried, a pattern evaluates only what it inspects: a literal evaluates its argument to compare it, and a name used once evaluates nothing. So an argument that no pattern inspects and the chosen clause does not use is never evaluated, as with `if`:

```
Pick(0, a, b) = a
Pick(n, a, b) = b

Pick(0, 10, 1 / 0)
```

**Result:** `10`

[Open in Playground](https://katlang.org/#1/-QWoVefyBhdWY5ZgkwLJn)

### Recursion

A clause may call its own algorithm, and clauses make the base case of a recursion explicit:

```
Factorial(0) = 1
Factorial(n) = n * Factorial(n - 1)

Factorial(5)
```

**Result:** `120`

[Open in Playground](https://katlang.org/#1/_en9H1vfl)

```
Gcd(a, 0) = a
Gcd(a, b) = Gcd(b, a mod b)

Gcd(48, 18)
```

**Result:** `6`

[Open in Playground](https://katlang.org/#1/-SeqzLZsphX)

A definition without a written parameter list can recurse too, by calling itself with its arguments written out:

```
Fact = if(n <= 1, 1, n * Fact(n - 1))

Fact(5)
```

**Result:** `120`

[Open in Playground](https://katlang.org/#1/-if2UduiHh)

Recursion cannot go arbitrarily deep: by default KatLang allows at most 128 nested calls, and a deeper recursion stops with an error. For long iterations, use `reduce` or the loops of the next chapter instead.

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

[Open in Playground](https://katlang.org/#1/_s5Xu08-4Ck4)

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

[Open in Playground](https://katlang.org/#1/_Hpfa229ETuo)

As in [List Patterns](#list-patterns), each pattern matches only its own kind, so `Area(['rect', 3, 4])` matches no clause. Bracketed patterns tell lists apart by their length:

```
Kind([]) = 0
Kind([x]) = 1
Kind(xs) = 2

Kind([])
Kind([5])
Kind([5, 6])
```

**Results:**
```
0
1
2
```

[Open in Playground](https://katlang.org/#1/_bm2-F4FrQ7)

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

[Open in Playground](https://katlang.org/#1/-ITWhnuXd5Pa)

`_` is an ordinary name, not a wildcard, so `F(_, _)` also requires two equal arguments. Values are equal when `==` says so, so `1.5` and `1.50` are one number. Two names of definitions, however, match only when they name the same definition: with `A = 3` and `B = 3`, `Same(A, B)` is `false`, while `Same(A, 3)` and `Same(A(), B())` are `true`.

### Rules for Clauses

When no clause matches, the call is an error, so add a catch-all clause if every input should be handled:

```
Grade(1) = 'excellent'
Grade(2) = 'good'

Grade(3)
```

**Result:** error — no clause of `Grade` matches the argument `3`.

[Open in Playground](https://katlang.org/#1/-aeizxtpMR)

All clauses of one conditional algorithm take the same number of parameters and write the same number of outputs. A conditional algorithm whose clauses disagree is rejected before anything runs:

<!-- spec:conditional-clauses-share-top-level-arity -->
```
F(0) = 1
F(x, y) = 2

F(0)
```

[Open in Playground](https://katlang.org/#1/8qBXQKPp)

This program is rejected: its second clause takes two parameters where the first takes one. Two clauses whose patterns have the same structure, such as `F(x)` and `F(y)`, are rejected as duplicates. KatLang does not check whether a clause can ever be chosen: after `F(n)`, a clause `F(0)` is accepted but never used, which is why the catch-all belongs last.

A clause infers no parameters: every name in its body must come from its head, the part before `=`, or be defined around it, so `F(0) = z` is an error.

A conditional algorithm takes a fixed number of arguments. Inside one argument, a list or sequence pattern may collect, as in [Collecting Inside a Pattern](#collecting-inside-a-pattern):

<!-- spec:family-list-pattern-collects-tail -->
```
Tail([]) = []
Tail([head, *rest]) = rest

Tail(['a', ['b', 'c'], 'd'])
```

**Result:** `[[b, c], d]`

[Open in Playground](https://katlang.org/#1/_cjtDphTw9367X2Mca5_aZIQtvlZTFjU1iqIKy2-u6vUBJYB)

Both clauses take one argument, a list, and `rest` is the list of the elements after the first. `Tail(['a'])` is `[]`. `Tail(('a', 'b'))` matches no clause, because a list pattern does not match a sequence, and `Tail('a', 'b')` is an error, because it passes two arguments where every clause takes one.

A clause cannot collect the arguments themselves: beside `F(0, 0) = 0`, the clause `F(first, *others) = others` is rejected, and so is the single clause `F(0, *others) = others`, whose literal makes it a conditional algorithm. A single definition without literal patterns keeps its collecting parameter, so separate arguments are gathered by an ordinary definition such as `TailArgs(*items) = Tail(items)`.

Collecting patterns make a recursion over a list read like its definition:

```
Sum([]) = 0
Sum([first, *others]) = first + Sum(others)

Last([only]) = only
Last([first, *others]) = Last(others)

Sum([1, 2, 3])
Last([4, 5, 9])
```

**Results:**
```
6
9
```

[Open in Playground](https://katlang.org/#1/_to_LlTN4LkvMCCXb_b6EoLmjtPuKo0kDrEijR6kM67SrYIDbTPxtYpPw8_OgX2)

Because the clauses may inspect any argument, a conditional algorithm takes its arguments as values. So, as in arithmetic, the name of a formula that needs inputs is called there, and its inputs are handed on. To pass an algorithm itself, write it in braces:

```
Times(0, f, x) = x
Times(n, f, x) = Times(n - 1, f, f(x))

Times(3, {y + 1}, 0)
```

**Result:** `3`

[Open in Playground](https://katlang.org/#1/_YDq9qdErHhX)

With `Inc(y) = y + 1`, the call `Times(3, Inc, 0)` is therefore an error, because nothing supplies `y`, while `Times(3, {Inc}, 0)` passes `Inc` itself and is `3`. A parameter that already holds an algorithm, such as `f` inside `Times`, is passed on as it is. [Value or Algorithm?](#value-or-algorithm) has the general rule.

### Example: An Invoice

This program combines what the chapters so far have taught: display settings, clauses that match text, an argument unpacked by a pattern, a list, a pipeline, and a decision.

```
MinDecimalPlaces = 2
MaxDecimalPlaces = 2

Price('apple') = 0.80
Price('bread') = 2.50
Price('milk') = 1.20

Line((item, quantity)) = Price(item) * quantity

Order = [('apple', 6), ('bread', 1), ('milk', 2)]

Subtotal = Order.map(Line).sum
Discount = if(Subtotal > 5, Subtotal * 0.1, 0)

Subtotal, Discount, Subtotal - Discount
```

**Results:**
```
9.70
0.97
8.73
```

[Open in Playground](https://katlang.org/#1/_1wYnXaJ2k_iE9ZH378Pa7i7T6ofI3NWYOnoKsbfCCxz1DVYW0WwsAFJgXWo4fMXisjd0z-iXO9_SMZ2CaVmmYrV4yV4bDh2NXwoznWJwlY41YnQXA57-UltS5puRlL)

---

<a id="repetition"></a>

## Loops

### Repeating a Step with `repeat`

`repeat` applies a step algorithm a fixed number of times, feeding each result back in as the next input. You write the step as a call with its starting value, and the number of rounds after it:

```
Increment = x + 1
Increment(0).repeat(5)
```

**Result:** `5`

[Open in Playground](https://katlang.org/#1/-udM68Xd)

`Increment(0).repeat(5)`, the dot spelling of `repeat(Increment(0), 5)`, starts from `0` and applies `Increment` five times. `repeat` does not simply run the call `Increment(0)`: it takes it apart, using `Increment` as the step and the call's arguments as the starting state. ([Captured Calls](#captured-calls) shows how your own algorithms can do the same.)

### State with Several Values

A step with several outputs carries several values from one round to the next; together they are the loop's **state**. Write the step's call with one starting value for each state value:

```
Fibonacci(a, b) = b, a + b
Final = Fibonacci(0, 1).repeat(10)

Final
Final[0]
```

**Results:**
```
(55, 89)
55
```

[Open in Playground](https://katlang.org/#1/_ZH5-xVq5l)

Each round turns the state `(a, b)` into `(b, a + b)`. Starting from `(0, 1)`, ten rounds reach `(55, 89)`, and `[0]` selects the tenth Fibonacci number. To start from a stored pair such as `Start = 0, 1`, spread it inside the call: `Fibonacci(Start*).repeat(10)`.

Each output becomes an argument of the next round, so whenever another round follows, the step must accept its own outputs. A value that never changes need not be passed along; read it from around the step instead:

```
Power(base, n) = {
    Step(x) = x * base
    Step(1).repeat(n)
}

Power(2, 10)
```

**Result:** `1024`

[Open in Playground](https://katlang.org/#1/_YFjQBXKA13d)

### Looping While a Condition Holds

`while` repeats a step as long as a condition holds. The step's **last output** is the condition, and the outputs before it are the state:

```
Countdown = x - 1, x > 1
Countdown(5).while
```

**Result:** `1`

[Open in Playground](https://katlang.org/#1/-ohsxzGtxQ)

Read `Countdown` as "while `x > 1`, replace `x` with `x - 1`": starting from 5, the state becomes 4, 3, 2, and 1, and at 1 the condition `x > 1` is `false`, so the loop stops with `1`. Each round evaluates the **condition first**. If it is `false`, the loop returns the current state without computing the other outputs; if it is `true`, the other outputs become the next state. So the condition protects the step from a computation that would fail:

<!-- spec:loop-while-condition-first-skips-transition -->
```
Step(x) = 10 / (x - 1), x > 1
Step(1).while
```

**Result:** `1`

[Open in Playground](https://katlang.org/#1/-oP_I3a_FU)

The condition is `false` for the starting state, so `10 / (x - 1)` is never evaluated. Only the other output rows are skipped: everything the condition's own row computes still runs. The condition must be a Boolean.

Two more examples: how many years it takes 5% interest to double 1000, and how many steps the Collatz sequence needs to get from 27 down to 1:

```
Grow(years, balance) = years + 1, balance * 1.05, balance < 2000
Collatz(n, steps) = if(n mod 2 == 0, n / 2, 3 * n + 1), steps + 1, n != 1

Grow(0, 1000).while[0]
Collatz(27, 0).while[1]
```

**Results:**
```
15
111
```

[Open in Playground](https://katlang.org/#1/_op5PCgw5qc53wP)

A loop whose condition never becomes `false` runs forever, so check the condition carefully. To transform a known collection, a pipeline with `map`, `filter`, and `reduce` is usually clearer than a loop; loops are for state that evolves step by step.

### Which Calls Are Steps

The loop must see the call itself, written with its argument list: `Increment(0).repeat(5)`, `0.Increment().repeat(5)`, and `while(Countdown(5))` all work, and so does a call through a parameter, as in `Run(step, start) = step(start).while`. A parameter passes along a written call it receives, so a loop can sit inside a helper:

```
Countdown = x - 1, x > 1
Loop(s) = s.while

Loop(Countdown(5))
```

**Result:** `1`

[Open in Playground](https://katlang.org/#1/-ChsxyVJy)

Anything else is an error: a plain value (`repeat(5, 2)`), a property that holds only the result of a call (with `Start = Increment(0)`, `Start.repeat(5)`), an algorithm without a call (`Increment.repeat(5)`), and a dot call without its parentheses (`0.Increment.repeat(5)`). A brace algorithm is given a name first, so that it can be called:

```
AddTen = { x + 10 }

AddTen(0).repeat(3)
```

**Result:** `30`

[Open in Playground](https://katlang.org/#1/-unhYCkUi-U_1EgQjL3)

Any callable can be a step, a conditional algorithm or a built-in operation included: each round calls it with the current state, exactly as a direct call would. Clauses give a step a natural base case:

<!-- spec:loop-step-family-while -->
```
Countdown(0) = 0, false
Countdown(n) = n - 1, true
Countdown(3).while
```

**Result:** `0`

[Open in Playground](https://katlang.org/#1/_dIbJazh6U)

Each round calls `Countdown` on the state, and the matching clause's outputs form the next state and the condition, so the state becomes 2, 1, and 0, where the first clause returns `false`.

---

## Organizing Programs

### Local Definitions

An algorithm's body may be written in braces, with definitions of its own, its local helpers, followed by its output:

```
Loan(principal, rate, years) = {
    MonthlyRate = rate / 12
    Months = years * 12
    principal * MonthlyRate / (1 - (1 + MonthlyRate) ^ -Months)
}

Loan(200000, 0.06, 30).round(2)
```

**Result:** `1199.10`

[Open in Playground](https://katlang.org/#1/_pBon2X2tLrJpF)

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

[Open in Playground](https://katlang.org/#1/_q5on2X2s4Im)

Every call of an algorithm works out its local properties afresh. Inside one call a local property has one value, however often that call reads it; call it to calculate it again:

```
Fixed(i) = {
    T = tick()
    T + T
}
Fresh(i) = {
    T = tick()
    T() + T()
}

[1, 2].map(Fixed)
[1, 2].map(Fresh)
```

**Results:**
```
[2, 4]
[7, 11]
```

[Open in Playground](https://katlang.org/#1/_Dn2cNwA1w1c)

Each call of `Fixed` runs `tick()` once and reads that one `T` twice; each call of `Fresh` runs it twice. This matters most for random numbers: a helper `Roll = randomInt(1, 7)` inside `Trial(i)` gives each call of `Trial` one roll, which every use of `Roll` in that call reads.

### How Names Are Found

KatLang looks up a name starting in the algorithm where it is written and then in each enclosing algorithm, outward; the first algorithm that declares the name, as a property or as a parameter, provides it. A nested definition therefore hides an outer one with the same name:

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

[Open in Playground](https://katlang.org/#1/-mNAIAN1Kj)

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

[Open in Playground](https://katlang.org/#1/-KDn5yYWgz0)

A property may not reuse the name of a parameter of its own algorithm or of an enclosing one; rename one of the two. (The top-level `v` above is allowed, because `Outer` does not enclose it.) After your own definitions come the built-in names such as `sum`, `sqrt`, and `if`, so a definition of your own with the same name takes precedence over a built-in one. A name that is found nowhere becomes an inferred parameter, or is an error in an algorithm with an explicit parameter list.

Handing on follows the same search. When a formula is used inside an algorithm that already has a parameter of the needed name, its own or one of an algorithm around it, that parameter is handed on and nothing new is added:

```
Area = width * height
Report(width, height) = {
    Doubled = Area * 2
    Doubled + 1
}
Report(3, 4)
```

**Result:** `25`

[Open in Playground](https://katlang.org/#1/_NJgPDUY9n)

`Area` needs `width` and `height`, and `Doubled` is written inside `Report`, whose parameters have those names, so `Area` receives Report's `width` and `height`.

### Algorithms as Containers

An algorithm can also be a container that groups related definitions. Its members are reached with a dot:

```
Physics = {
    G = 9.81
    FallTime(h) = sqrt(2 * h / G)
}

Physics.G
Physics.FallTime(20).round(3)
```

**Results:**
```
9.81
2.019
```

[Open in Playground](https://katlang.org/#1/_NFqfyM0PrmyRToe4h)

The dot follows the rule of [Members](#members), and the next program shows both of its cases. (The word `public` in it matters only for `open`, the subject of the next section.)

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

[Open in Playground](https://katlang.org/#1/_bpKyYVuOP-D)

`Obj` has its own member `B`, so `Obj.B(5)` calls that member with `5`. The number `3` has no members, so `3.B(5)` is the call `B(3, 5)`.

The member rule also affects inferred parameters. In `Area = shape.V * 2`, the argument for `shape` might have no member `V`, and then `shape.V` would be the call `V(shape)`; so when nothing named `V` is defined, `V` becomes a parameter as well: `Area(shape, V)`. To keep `V` out, write the parameter list: `Area(shape) = shape.V * 2`.

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

[Open in Playground](https://katlang.org/#1/_Ih6qNzbT2DJ)

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

[Open in Playground](https://katlang.org/#1/_bmpyhh-bvN)

After `open Lib`, `Area` could be used on its own, but `Helper` could not. A few rules keep `open` predictable:

- `open` comes first in its algorithm, before any definitions and output rows, and one `open` lists all of its targets: `open Geometry, Physics`.
- A target names an algorithm that takes no parameters: a name, a dotted path of public members such as `open Geometry.Shapes`, a brace algorithm, or a module URL (next section). A misspelled target is an error.
- Opened names never override other names: your own definitions and the built-in names are found first.
- Two opened algorithms may both have a name; writing that name alone is then an error, because it does not say which one you mean. Write `A.X` instead.
- `open Math` makes the members of `Math` available under their own names, such as `Sqrt(16)` and `Pi`.

Here both libraries define `X`, which is harmless because the program names each `X` with its library:

```
open A, B
A = {
    public X = 1
    public P = 10
}
B = {
    public X = 2
    public Q = 20
}

P + Q + A.X + B.X
```

**Result:** `33`

[Open in Playground](https://katlang.org/#1/_Gh6qR2rlaK9M)

### Loading External Algorithms

A program can load an algorithm from a URL with `load` and use its members. Here it loads a small vector library that katlang.org hosts:

<!-- spec:skip module loading needs a host-configured network downloader -->
```
Vec = load('https://katlang.org/libraries/plane-vec.kat')

Vec.Add(Vec.Vector(1, 2), Vec.Vector(3, 4))
Vec.Magnitude(Vec.Vector(3, 4))
```

**Results:**
```
(4, 6)
5
```

[Open in Playground](https://katlang.org/#1/_vI2MbnywRYe4cWv59CLo5fno98bVuJbHTIxeE4ymadFd6LYF21nTe9qhnTsKY)

`open` with a URL opens the loaded algorithm directly, so its public members need no prefix:

<!-- spec:skip open 'url' needs a host-configured network downloader -->
```
open 'https://katlang.org/libraries/plane-vec.kat'

Add(Vector(1, 2), Vector(3, 4))
Vector(3, 4).Magnitude
```

**Results:**
```
(4, 6)
5
```

[Open in Playground](https://katlang.org/#1/_Kh6r4oZ0AsjoMKHNce5nOQ-xd7AtoLF83iMzHChbpRT3iZeJ2Y)

A loaded algorithm is called a **module**, and it is self-contained: its names mean what they mean inside the module itself, or the built-in names, never what the loading program defines. One address is one module, however often it is loaded, and a URL is fixed text in single quotes, never computed.

Loading is off unless the program that runs your code allows it, and a module URL must use `https`. The playground allows `katlang.org` and its subdomains; the command-line tool, with `--allow-loading`, allows any host on the public internet, and refuses an address on your own computer or network.

---

## Formulas and Aliases in Depth

[Formulas That Use Formulas](#formulas-that-use-formulas) showed how a formula hands its inputs on to the formulas it uses. This chapter shows the other ways to define one algorithm through another and the rules behind them, and it ends with how several Grace markers combine.

### Aliases, Forwarding, and Explicit Calls

There are four ways to define a formula through another one, and they are four different things:

<!-- spec:alias-forwarding-and-explicit-call -->
```
Double(x) = x * 2
Other(y) = y * 2

Alias = Double
Forward(x) = Double
Explicit(x) = Other(x)
Formula = Double + 1

Alias(5)
Forward(5)
Explicit(5)
Formula(5)
```

**Results:**
```
10
10
10
11
```

[Open in Playground](https://katlang.org/#1/_sKDdcE59Gc)

- `Alias = Double` is an **alias**: its whole body is the name of an algorithm, and it has no parameter list of its own, so it is `Double` under another name, with Double's parameters.
- `Forward(x) = Double` is **forwarding by name**: `Forward` has its own parameter list, and `Double` receives the parameter of the same name. Nothing is added to the list and nothing is renamed: `Bad(x) = Other` is an error, because `Other` needs a `y` and `Bad` has none.
- `Explicit(x) = Other(x)` is an **explicit call**: the arguments are passed exactly as written, so the names do not have to match.
- `Formula = Double + 1` *uses* `Double` in an expression, so Double's input becomes an input of `Formula`: it means `Formula(x) = Double(x) + 1`.

Forwarding matches parameters by name, never by position, so `Forward(x) = Double` and `Forward(x) = Double(x)` agree only when the names do:

```
Sub(y, x) = y - x
ByName(x, y) = Sub
Written(x, y) = Sub(x, y)

ByName(10, 3)
Written(10, 3)
```

**Results:**
```
-7
7
```

[Open in Playground](https://katlang.org/#1/_Rj9s15v-ZoYc-HoL_RJPr3T92jD2tjuWvj2aXG2CeJ7zPi)

`ByName` gives its `y` to Sub's `y` and its `x` to Sub's `x`, so `ByName(10, 3)` is `3 - 10`. `Written` passes its arguments in the written order.

### Value or Algorithm?

Whether a formula used in an expression is handed the inputs depends on what the expression does with it. Where its value is needed, as in arithmetic, a comparison, a list, an `if`, or a built-in operation's collection or value argument, it is called with them. Where it is passed on as an algorithm, to your own algorithm or as the callback of `map`, `filter`, or `reduce`, it is passed as it is:

<!-- spec:formula-lifting-follows-the-consumers-role -->
```
Inc(x) = x + 1
Apply(f) = f(10)

Values = [Inc, Inc * 2]
Kept = Apply(Inc)
Branch = if(true, Inc, 0)

Values(4)
Kept
Branch(4)
```

**Results:**
```
[5, 10]
11
5
```

[Open in Playground](https://katlang.org/#1/_AnVjuJepGnS)

`Values` and `Branch` take the input `x` of `Inc`, while `Kept` passes `Inc` itself to `Apply` and takes no input. An `if` branch is handed its inputs even when it is not chosen, but it is still evaluated only when chosen. This is also why a conditional algorithm takes a formula in braces ([Rules for Clauses](#rules-for-clauses)): each of its arguments is a value.

### Every Callable Receives Its Inputs the Same Way

Your own formulas and the built-in operations, Math functions included, are not the only callables that hand on their inputs: members reached with a dot or through `open` and conditional algorithms do the same. A built-in operation's inputs take the names of its own parameters, and a conditional algorithm's inputs are named by the parameters its clauses use:

<!-- spec:formula-lifting-is-one-law-for-every-callable -->
```
Lib = {
    public Inc(x) = x + 1
}
E(0) = 100
E(n) = n
Total = count + 0
Next = Lib.Inc + 0
Fam = E + 1

Total((1, 2, 3))
Next(4)
Fam(0)
```

**Results:**
```
3
5
101
```

[Open in Playground](https://katlang.org/#1/_uxqcQ58K_y)

`Total = count + 0` means `Total(collection) = count(collection) + 0`, and `Fam = E + 1` means `Fam(n) = E(n) + 1`, because the general clause of `E` names its input `n`. A conditional algorithm whose clauses name no input, such as `S(1) = 1` with `S(-1) = -1`, cannot be used this way: call it with an explicit argument instead.

<a id="aliases-of-any-function"></a>

### Aliases of Any Algorithm

An alias works for every algorithm, not only for your own formulas: built-in operations, Math functions, and conditional algorithms can be aliased too. The alias is the same algorithm under another name, so it keeps everything that algorithm does:

<!-- spec:alias-of-a-builtin-is-the-builtin -->
```
C = count
I = if
M = map
Bad(x) = x / 0

C([1, 2, 3])
I(true, 1, 1 / 0)
M([], Bad)
```

**Results:**
```
3
1
[]
```

[Open in Playground](https://katlang.org/#1/_Wo_O2SvCrNm)

`C([1, 2, 3])` is exactly `count([1, 2, 3])`. `I` keeps the rule of `if` that only the chosen branch is computed, and `M` keeps the rule of `map` that the callback runs only for the elements it is given, so `M([], Bad)` never calls `Bad`. An alias also shares its algorithm's members, so with `P = Physics`, `P.G` is `Physics.G`. Used alone, an alias gives the same value as the name it stands for, worked out once and shared by both names.

### Naming a Received Algorithm

A definition whose only row is a parameter of an enclosing algorithm gives that parameter a second name. `A` below is whatever algorithm `f` receives, so `A(9)` calls `Square(9)`, `2.A` is `Square(2)`, and `A` can be passed on like `f` itself:

<!-- spec:runtime-alias-of-a-parameter -->
```
Square(x) = x * x
Apply(f, x) = f(x)
Use(f) = {
    A = f
    A(9), 2.A, Apply(A, 4)
}

Use(Square)
```

**Result:** `(81, 4, 16)`

[Open in Playground](https://katlang.org/#1/_OEHP3IXL4Nb)

Each call of `A` is a fresh call of the algorithm `f` received, with exactly the arguments written there.

### Several Grace Markers

In short, more markers move a name further, and the simplest way to get an exact order is to mark in one direction only: give each name one `~` in front for every earlier-written name that must come after it, or one `~` behind for every later-written name that must come before it.

The exact rule: markers add up. Each `~` in front of a name asks for one position earlier and each `~` behind it for one position later; opposite markers cancel, and markers on several occurrences of a name count together. The total is the name's **weight**, and a name without markers has zero weight. Names that move later take their turns first, starting from the last-written one; then names that move earlier take theirs, starting from the first-written one. So `~~x` requests two positions earlier for `x`, stopping at the end of the list or at a neighbour that moves the same way with at least as many moves left. Equal accumulated weights preserve their original relative order. Names that stand side by side with equal weights form a contiguous run. A contiguous equal-weight run moves as a unit when every parameter outside that run has zero weight. Other moving parameters can split the run while preserving its relative order. The outside name has zero weight in both examples below, so the two marked names stay side by side:

```
Prefixed = s * 100 + ~x * 10 + ~y
Prefixed(1, 2, 3)
```

**Result:** `312`

[Open in Playground](https://katlang.org/#1/-YWEIJE_Fo)

```
Postfixed = s~ * 100 + x~ * 10 + y
Postfixed(1, 2, 3)
```

**Result:** `231`

[Open in Playground](https://katlang.org/#1/-UWQDeLtuj)

`Prefixed` takes its parameters in the order `(x, y, s)`, and `Postfixed` in the order `(y, s, x)`.

When names move in both directions, names that started side by side can end up apart:

```
K = a~ * 1000 + b~ * 100 + ~c * 10 + ~d
K(1, 2, 3, 4)
```

**Result:** `2413`

[Open in Playground](https://katlang.org/#1/-UcWwUbE5iI)

`K` takes `(c, a, d, b)`: `a` stays before `b` and `c` before `d`, but neither pair stays adjacent.

---

## Algorithms Whose Calls Spread

When an algorithm's results are always meant to be used as separate items, you can say so once, in its declaration, instead of writing `*` after every call. Put a star directly after the name or after the parameter list:

```
Point(x, y)* = x, y
Add(x, y) = x + y

Point(1, 2)
Add(Point(3, 4))
[Point(5, 6), Point(7, 8)]
```

**Results:**
```
1
2
7
[5, 6, 7, 8]
```

[Open in Playground](https://katlang.org/#1/_QllC9pQjUGC)

The star does not change the algorithm itself: `Point` still takes two parameters and computes the same value. It changes how calls to it are read: a call that KatLang can see is a call of `Point` is read as if you had written `*` after it, so `Add(Point(3, 4))` is `Add(Point(3, 4)*)`. It spreads wherever a written `*` would: as a whole output row, a whole argument, a list element, an item of a sequence, a selection index, and as the value before a dot call (`Point(1, 2).Add` is `Add(Point(1, 2)*)`).

Everywhere else the call stays one value, for example as an operand of an operator or before a selection. Braces keep the result as one value where it would spread:

```
Point(x, y)* = x, y

Point(1, 2)[0]
count({ Point(1, 2) })
```

**Results:**
```
1
2
```

[Open in Playground](https://katlang.org/#1/-KWUMFbExXEK)

`count(Point(1, 2))` would be an error: the call supplies two arguments where `count` takes one, and the error message names the declaration that made the call spread. Parentheses do not help, because `(Point(1, 2))` is just `Point(1, 2)`.

The marker applies to the calls that KatLang recognizes as calls of the declaration before the program runs. An alias such as `Also = Point` spreads too, while a call through a parameter does not: when an algorithm receives `Point` as `f`, `f(1, 2)` is one value. An algorithm that calls a marked one, such as `W(x, y) = Point(x, y)`, is not marked itself.

```
Point(x, y)* = x, y
Apply(f) = [f(1, 2)]
Also = Point

Apply(Point)
[Also(3, 4)]
```

**Results:**
```
[(1, 2)]
[3, 4]
```

[Open in Playground](https://katlang.org/#1/_XllC4v0nolY)

A marked algorithm cannot be a loop step directly, because its call would spread into the arguments of `repeat`. Call it through an unmarked wrapper instead; inside the wrapper the row spreads, so each round still produces two state values:

```
Fib(a, b)* = b, a + b
Step(a, b) = Fib(a, b)

Fib(0, 1)
Step(0, 1).repeat(10)
```

**Results:**
```
1
1
(55, 89)
```

[Open in Playground](https://katlang.org/#1/_ZH6Zq_Gsotg)

The star must touch the name or the `)` (`A * = 1` is an error), and it goes on every clause of a conditional algorithm or on none. An algorithm without parameters can be marked too (`Origin* = 0, 0`), but only an explicit call `Origin()` spreads: the bare name `Origin` reads a value and is not a call. An alias and a deconstruction cannot carry the star; to make the calls of an unmarked algorithm such as `Pair(x, y) = x, y` spread, declare a marked wrapper: `SpreadPair(x, y)* = Pair(x, y)`.

---

## Captured Calls

`repeat` and `while` take a written call apart instead of running it. A parameter marked `meta` gives your own algorithms the same ability: it lets an algorithm look at a call before deciding what to do with it.

### Capturing a Call with `meta`

Writing `meta` before a parameter name makes the parameter receive the *call* written as its argument instead of that call's value. The call is not run when it is captured; the parameter holds a **call reference**, and `.Invoke()` runs the captured call:

```
Square(x) = x * x
Capture(meta operation) = operation

R = Capture(Square(5))
R.Invoke()
```

**Result:** `25`

[Open in Playground](https://katlang.org/#1/_TkHMMigbT)

Every `.Invoke()` runs the call again, with the same arguments; each argument is still computed only once. A call reference can be stored and passed on:

```
Square(x) = x * x
Capture(meta operation) = operation
RunTwice(r) = r.Invoke() + r.Invoke()

RunTwice(Capture(Square(3)))
```

**Result:** `18`

[Open in Playground](https://katlang.org/#1/_DEHMIdJOiH5wqMJ10iLdS_)

Only a written call can be captured: `Capture(5)` and `Capture(Square)` are errors. `meta` goes before a plain parameter name in a written parameter list. A call reference is used inside the program, so a program cannot output one:

```
Square(x) = x * x
Capture(meta operation) = operation

Capture(Square(5))
```

**Result:** error — a call reference cannot be a program result.

[Open in Playground](https://katlang.org/#1/_bEHMOtS3)

### Looking at a Captured Call's Arguments

`.Arguments` is a view of the arguments supplied to a captured call. `count` tells how many there are, and selection reads one of them:

```
Add(x, y) = x + y
Capture(meta operation) = operation

R = Capture(Add(10, 20))
R.Arguments.count, R.Arguments[0], R.Arguments[1]
```

**Results:**
```
2
10
20
```

[Open in Playground](https://katlang.org/#1/_vyeNRHfhj)

Obtaining the view runs nothing: `count` computes none of the arguments, and selecting an argument computes only that one. A spread among the captured arguments, such as `Pair*`, is the exception: as in a list, it runs as soon as the arguments are counted or read. Spreading the view into another call passes on the original arguments, so an argument the new call never uses is never computed:

```
Add(x, y) = x + y
First(x, y) = x
Capture(meta operation) = operation

R = Capture(Add(5, 1 / 0))
R.Arguments.count, First(R.Arguments*)
```

**Results:**
```
2
5
```

[Open in Playground](https://katlang.org/#1/_u6eM7eVXy)

An argument view is not a list: `.first` and `.last` work, but other collection operations such as `sum(R.Arguments)` are errors.

### Calling a Captured Call's Algorithm

`.Algorithm` is the captured call's algorithm itself, without its arguments. Calling it runs that algorithm afresh with exactly the arguments you give it, while `R.Invoke()` still runs the captured call:

```
Square(x) = x * x
Capture(meta operation) = operation

R = Capture(Square(5))
R.Algorithm(8), R.Invoke()
```

**Results:**
```
64
25
```

[Open in Playground](https://katlang.org/#1/_LkHMMuu6)

It is an ordinary callable, so it can be passed to another algorithm, used as a `map` or `filter` callback, or called with the original arguments through `R.Arguments*`:

```
Square(x) = x * x
Apply(f, x) = f(x)
Capture(meta operation) = operation

R = Capture(Square(5))
Apply(R.Algorithm, 7), [1, 2, 3].map(R.Algorithm), R.Algorithm(R.Arguments*)
```

**Results:**
```
49
[1, 4, 9]
25
```

[Open in Playground](https://katlang.org/#1/_qRB0A4RSf)

Together, `.Arguments` and `.Algorithm` let an algorithm look at a call before deciding what to do with it. `RunIfPositive` runs the captured step as a `while` loop, but only when its starting value is positive:

```
Step(x) = x + 1, x < 3
RunIfPositive(meta operation) = if(
    operation.Arguments[0] > 0,
    operation.Algorithm(operation.Arguments*).while,
    0
)

Step(0).RunIfPositive
Step(1).RunIfPositive
```

**Results:**
```
0
3
```

[Open in Playground](https://katlang.org/#1/_nY_5vRry9Ln-UEKImpWHhWBWjq4RQVVANuM9CHnB6mYOf7pvt6hSyNx0rLN)

`operation.Algorithm(operation.Arguments*)` is itself a written call, of the captured algorithm over the captured arguments, so `while` can take it apart. A call reference is a value, not a written call, so `operation.while` is an error.

---

## Layout and Common Pitfalls

### Line Layout

Each line of a program is an output row or a definition. On one line, items must be separated by commas:

<!-- spec:same-line-slots-need-comma -->
```
1 2 3
```

[Open in Playground](https://katlang.org/#1/0zEks)

This program is rejected: write `1, 2, 3` instead.

KatLang follows one newline rule:

> Newlines separate complete expressions by default. An incomplete expression continues when valid syntax permits it, without consuming a new declaration. Otherwise, an independent expression or declaration begins a new construct. Syntax that cannot stand alone but can legally continue the preceding expression attaches backward. All decisions are syntactic, never based on evaluated values.

Incomplete syntax continues on the next line: end the line with an operator or a comma, or keep a delimiter open. Inside parentheses and brackets, a new line also separates items, as a comma does; a comma cannot follow the last item before a closing delimiter.

```
Total = 1 +
    2
Values = [
    10
    20
]

Total, Values.sum
```

**Results:**
```
3
30
```

[Open in Playground](https://katlang.org/#1/-AOmNl-k4c)

Otherwise, the start of the next line decides. Comments, blank lines and indentation do not affect the choice:

| The next line starts with | Reading | Example |
|---|---|---|
| `.` | Continues a dotted chain | `xs` then `.sum` |
| `,` | Continues a list of items | `P = 1` then `, 2` gives `P` two outputs |
| `+`, `/`, `div`, `mod`, `^`, a comparison, `and`, `or`, `xor` | Continues the expression | `10` then `+ 2` is `12` |
| `*` | Continues as multiplication | `10` then `* 2` is `20` |
| A minus with a space after it | Continues as subtraction | `10` then `- 2` is `8` |
| A minus attached to its operand | Starts a new row | `10` then `-2` is two rows |
| `(`, `[`, `{`, `not`, `~` | Starts a new row | `Add` then `(1, 2)` is two rows, not a call |
| A definition | Starts a definition | Never joins the line before it |

So keep a call's opening parenthesis on the same line as its name. A minus that negates must touch its operand on any line: `3 * -2` works, while `3 * - 2` and a detached `- 2` with no row before it are syntax errors. Each definition starts on its own line: `x = 1 y = 2` is an error. At the end of a line, a star's spacing decides, as the next section shows.

### Spread or Multiplication?

A star at the end of a line is read from its spacing. Attached to the expression before it, `A*` is a spread: the expression is finished. A next line beginning with `.` or `,` continues it, one beginning with an operator such as `+` is an error because a spread cannot be an operand, a matching `)`, `]`, or `}` closes its construct, and an independent expression or definition starts the next row or item. Separated by a space, `A *` is a multiplication that still needs its right operand, which the next line supplies with the usual operator precedence:

```
A = 1, 2, 3
B = 2

A*
B *
3
```

**Results:**
```
1
2
3
6
```

[Open in Playground](https://katlang.org/#1/8ij3RqKH)

The same holds at the end of the program: `A*` alone spreads `A`, while `A *` with nothing after it reports a missing operand. A following definition stays a definition: after `A*` it simply follows the finished spread, and after `A *` it leaves the multiplication with a missing operand. Comments and blank lines change neither reading. On one line, a star followed by an operand always multiplies, whatever the spacing, so a spread followed by another item on the same line needs a comma:

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

[Open in Playground](https://katlang.org/#1/9CjtyF8t)

A definition can end in a spread in either of two spellings. Parentheses (braces work too) close it explicitly and group the items into one value:

```
A = (1, 2)
X = (A*)

X
```

**Result:** `(1, 2)`

[Open in Playground](https://katlang.org/#1/9KkG5LO)

Without the parentheses, `X = A*` followed by the row `X` prints the same `(1, 2)`: the attached star finishes the definition at the end of its line. Only a detached star joins the lines: `X = A *` followed by the row `X` is the one definition `X = A * X`, a valid multiplication but not the one intended, and the program has no output row at all.

### Common Mistakes

- **A misspelled name becomes a parameter.** An undefined name is inferred as a parameter, so a typo shows up as a missing argument ([Undefined Names in the Program](#undefined-names-in-the-program)).
- **A misspelled member falls back to a call.** `Math` has no member `Ceiling`, so `Math.Ceiling(2.1)` means `Ceiling(Math, 2.1)`; as nothing named `Ceiling` is defined, the name becomes a parameter, and the error message suggests `Math.Ceil`.
- **Parameters follow first appearance.** `Ratio = b / a` takes `b` first; use an explicit parameter list or Grace to change the order.
- **A built-in name is not a parameter.** In `PerItem = total / count`, `count` is the built-in operation, which hands on its own input, so the parameters are `PerItem(total, collection)`, and `PerItem(100, 4)` quietly gives `100` instead of `25`: a single number counts as one item. Choose another name, such as `items`, or list the parameters: `PerItem(total, count) = total / count`.
- **Values are not unpacked automatically.** A sequence or list is one argument. Open it with `*`, select its items with brackets (`v[0]`), or unpack it with a pattern parameter.
- **Arithmetic works on single numbers.** `[1, 2] * 2` is an error; use `map` to work on each item.
- **A pattern unpacks only its own kind.** `(x, y)` takes a sequence and `[x, y]` a list. There is no one-item pattern `(x)`: write `x` for a whole value or `[x]` for the element of a one-element list.
- **Collection operations take one collection.** Write `sum((1, 2, 3))` or `[1, 2, 3].sum`, not `sum(1, 2, 3)`.
- **Collecting parameters take separate arguments.** Spread a stored collection into them: `Data*.Mean`.
- **A line-final `*` reads by its spacing.** An attached `A*` is a finished spread; a detached `A *` continues as multiplication with the usual operator precedence, or leaves a missing operand at the end of the program. On one line, separate a spread from the next item with a comma: `A*, B` ([Spread or Multiplication?](#spread-or-multiplication)).
- **Only Booleans are conditions.** `if`, `filter`, `while`, and the logical operators need `true` or `false`; a number is an error.
- **Parentheses group, braces define.** `(n + 1)` is the expression `n + 1`; `{n + 1}` is an algorithm, with `n` as its parameter unless `n` is defined around it.
- **Indentation never groups.** Indentation changes nothing: whether a line continues the one before it depends only on how the two lines end and begin ([Line Layout](#line-layout)). Write a body of several rows in braces.
- **`()`, `[]`, and `{}` are different.** They are the empty sequence, the empty list, and an algorithm without output.
- **Text is written in single quotes only.** `"text"` is an error, and there is no interpolation: `'{x}'` is the plain text `{x}`.
- **A local helper has one value per call.** Write `Roll()` or `randomInt(1, 7)` to roll again within a call ([Local Definitions](#local-definitions)).
- **A conditional algorithm treats its arguments as values.** Put the name of a formula that needs inputs in braces: `Times(3, {Inc}, 0)` ([Rules for Clauses](#rules-for-clauses)).
- **Deep recursion stops with an error.** Use `repeat`, `while`, or `reduce` for long iterations.

### Words in Error Messages

Error messages use a few words of their own:

| In an error message | In this tutorial |
|---|---|
| implicit parameter | An inferred parameter |
| arity | The number of arguments or outputs |
| branch | A clause of a conditional algorithm |
| clause family | A conditional algorithm |
| local-only | A property that depends on its algorithm's parameters, so it can be used only inside that algorithm |
| formula lifting | Handing inputs on to a formula used in an expression |
| bare forwarding | Forwarding by name |
| fell back to a lexical callable | `a.f` became the call `f(a)`, because `a` has no member `f` |
| dotCall | A dot call |
| Illegal in eval | An operation that these values do not allow, such as the `min` of an empty list |
| prelude | The built-in names |
| scalar | A single value, not a sequence or a list |
| signature | An algorithm's parameter list |
| binder | A name in a parameter list or pattern |
| slot | One output, argument, or list item |
| host stack | The memory available for nested calls; reaching its limit means a recursion went too deep |
| open provider | An algorithm named by `open` |
| module elaboration | Loading a module; with the command-line tool, add `--allow-loading` |
| meta parameter, written invocation | A parameter marked `meta` ([Captured Calls](#captured-calls)), such as the step of `repeat` or `while`, which must receive a written call ([Which Calls Are Steps](#which-calls-are-steps)) |
| declaration | A definition |
| callable identity | Which definition an argument names |

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
| `( )` | Call with arguments (`f(1, 2)`) | Postfix |
| `[ ]` | Selection by zero-based position (`value[0]`, `value[0, 1]`) | Postfix |
| `.` | Dot call or member access (`a.f(b)`) | Postfix |
| `*` | Spread: supply the items of a value (`value*`) | Postfix |

Postfix forms bind tighter than every operator above them, `^` included.

### Syntax

| Syntax | Meaning |
|---|---|
| `Name = expression` | Define a property |
| `Name(a, b) = expression` | Define a property with an explicit parameter list |
| `Name(0) = expression` | One clause of a conditional algorithm: a literal in the head, or several definitions of one name, make clauses |
| `Name(a, b)* = expression` | A call of `Name` spreads its results wherever a written `*` would |
| `a, b` | Separate outputs, arguments, or items |
| `(a, b)` | A sequence; parentheses around one expression only group it |
| `[a, b]` | A list |
| `{ ... }` | An algorithm: a brace algorithm, or a body with local definitions |
| `value*` | Spread: supply the items of a value |
| `*name` | Collecting parameter, or a collecting name in a deconstruction |
| `(x, y)` in a parameter list | Sequence pattern: unpack one sequence argument |
| `[x, y]` in a parameter list | List pattern: unpack one list argument |
| `~x`, `x~` | Grace: move an inferred parameter one position earlier or later |
| `x, y = value` | Deconstruction: bind several names at once |
| `Name(meta p) = expression` | `p` captures the written call instead of its value |
| `load('url')` | Load an algorithm from a URL |
| `'text'` | String: raw text on one line, with no escapes and no interpolation; the only way to write text |
| `MinDecimalPlaces = 2`, `MaxDecimalPlaces = 4` | At the top level of the program: the fewest and the most decimal places displayed |
| `# ...` | Comment |

### Built-in Operations

| Operation | Written as | Result |
|---|---|---|
| `if` | `if(condition, a, b)` | `a` when the condition is `true`, otherwise `b`; only the chosen branch is evaluated |
| `range` | `range(start, stop)` | The whole numbers from `start` to `stop`, counting up or down |
| `count` | `xs.count` | The number of items |
| `sum`, `avg` | `xs.sum`, `xs.avg` | The total and the mean of the items, which must be numbers (the sum of no items is `0`) |
| `min`, `max` | `xs.min`, `xs.max` | The smallest and the largest item; the items must be numbers |
| `first`, `last` | `xs.first`, `xs.last` | The first and the last item |
| `contains` | `xs.contains(v)` | `true` when an item equals `v` |
| `filter` | `xs.filter(p)` | The items for which `p(item)` is `true` |
| `map` | `xs.map(f)` | `f(item)` for every item |
| `reduce` | `xs.reduce(f, initial)` | The items combined from left to right by `f(item, accumulator)`, starting from `initial` |
| `order`, `orderDesc` | `xs.order`, `xs.orderDesc` | The items in ascending or descending order; the items must be numbers |
| `distinct` | `xs.distinct` | The items without later duplicates |
| `take`, `skip` | `xs.take(n)`, `xs.skip(n)` | The first `n` items; the items after the first `n` |
| `atoms` | `atoms(value)` | Every number in a nested structure, in one flat list |
| `repeat` | `step(start).repeat(n)` | The state after `n` applications of `step`, starting from the arguments of the written call |
| `while` | `step(start).while` | The state reached when the condition, the last value `step` produces, is `false`; each round checks the condition first |
| `tick` | `tick()` | The run's counter after adding one: `1`, `2`, `3`, … for each time the call actually runs |
| `string` | `number.string` | The number as text (dot form only) |
| `Invoke` | `reference.Invoke()` | Runs the call a `meta` parameter captured (dot form only) |
| `Arguments` | `reference.Arguments` | A view of the captured call's arguments: `count`, `[i]`, `first`, `last`, and `F(reference.Arguments*)` (dot form only) |
| `Algorithm` | `reference.Algorithm` | The captured call's algorithm: pass it on, or call it with new arguments, as in `reference.Algorithm(8)` (dot form only) |
| `Math` | `Math.Sqrt(2)`, `sqrt(2)` | Mathematical functions and constants (see [Math Functions](#math-functions)) |

Operations that produce a collection (`range`, `filter`, `map`, `order`, `orderDesc`, `distinct`, `take`, `skip`, `atoms`) return a list. Built-in names such as `count` and `if` are not reserved: a definition of your own with the same name takes precedence.

### When Things Are Evaluated

| Construct | When it is evaluated |
|---|---|
| A property read by name, `A` | Once; later reads reuse the stored value |
| An explicit call, `A()` or `F(x)` | Every time the call runs; an `A()` before any read also stores `A`'s value |
| A local property | Once in each call of the algorithm that defines it |
| An argument | When its value is first needed, and at most once; never, if it is not needed |
| A spread, `value*` | When the call, list, or selection it is written in gathers its items, before that starts: `if(false, Bad*, 0)` computes `Bad*`. In a call or a selection, spreading a collecting parameter or `.Arguments` passes the arguments on without computing them |
| The branches of `if` | Only the chosen branch |
| The clauses of a conditional algorithm | From the top, each clause's patterns inspect what they test; only the chosen clause's body runs |
| The right operand of `and` and `or` | Only when the left operand does not decide the result |
| The items of a list | When something reads them; counting a written list reads none |
| The items of a sequence | All of them, when the sequence is computed |
| The accumulator of `reduce` | When the reducer reads it; the collection itself is read first |
| A step of `while` | Its condition first, and its other outputs only when the condition is `true` |

### Limits

- A single list or sequence holds at most 100,000 items by default.
- A single string holds at most 1,000,000 characters by default.
- Recursion goes at most 128 nested calls deep by default.

### Command-Line Tool

`katlang eval "<program>"` evaluates a program written on the command line, and `katlang run <file>` one stored in a file. To share a program, add the option `--code-link` to either command: after the results or the error, the tool writes one more line to stderr, `katlang-link: https://katlang.org/#1/...`, a link that opens that program in the playground and runs it.

To get a program back from such a link, use `katlang source "<link>"`: it writes the program's text and runs nothing. To run it, give the link in place of a file: `katlang run "<link>"` runs the program of a code link, and it also runs a program shared from the playground when given that program's link (`https://katlang.org/a/...`), or any KatLang program stored as text at an `https` address. The [command-line guide](https://github.com/katlangorg/katlangnet/blob/main/docs/cli.md) lists every option.

### Keywords

| Keyword | Meaning |
|---|---|
| `true`, `false` | The Boolean values |
| `and`, `or`, `xor`, `not` | Logical operators |
| `div`, `mod` | Integer division and remainder |
| `public` | Make a member available to `open` |
| `open` | Use the public members of other algorithms without a prefix |

`meta` is special only in front of a parameter name in a parameter list; everywhere else it is an ordinary name.
