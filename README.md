# KatLang — Language for Calculations
To learn more read the [KatLang tutorial](http://katlang.org/tutorial) or play with [KatLang online](http://katlang.org).

## Language Specification
The authoritative KatLang specification is defined in [`KatLang.lean`](https://github.com/katlangorg/katlangnet/blob/main/lean/KatLang.lean) using the Lean theorem prover. It is the single source of truth for KatLang's evaluation semantics and language rules over the elaborated program structure (AST shape, evaluation rules, and invariants). Surface syntax and grammar are defined by [`KatLang.ebnf`](https://github.com/katlangorg/katlangnet/blob/main/KatLang.ebnf) together with the reference parser in this repository. Independent implementations should conform to this specification.

If you have ideas for improving or extending the KatLang language — new constructs, better semantics, or clearer language rules — you are warmly welcome to open a discussion or reach out directly. Good ideas are always worth a conversation.

## Use of KatLang .NET parsing and evaluation library
```c#
using KatLang;

var source = """
    NetSalary = {
        SocTax = grossSalary * 0.105
        ChildCredit = numberOfChildren * 250
        NonTaxMin = 550
        TaxableIncome = grossSalary - SocTax - ChildCredit - NonTaxMin
        IncomeTax = TaxableIncome * 0.255
        grossSalary - SocTax - IncomeTax
    }
    NetSalary(1600, 2)
    """;

switch (KatLangEngine.Run(source))
{
    case RunResult.Success s:
        Console.WriteLine(s.ToDisplayString());
        break;

    case RunResult.NoProgramOutput n:
        Console.WriteLine(n.ToDisplayString());
        break;

    case RunResult.ParseFailure p:
        foreach (var error in p.Errors)
            Console.WriteLine(error);
        break;

    case RunResult.EvalFailure e:
        foreach (var error in e.Errors)
            Console.WriteLine(error);
        break;
}
```

## Plain-text output formatting

Formatting is bounded plain-text presentation only — it never re-parses, re-evaluates, or changes values, and the parser and evaluator know nothing about formatter modes. Three built-in formatters share one formatter-neutral value renderer and are selected by stable lowercase ids suitable for persistence (`exact`, `readable`, `concise`); unknown ids fall back to `exact` via `OutputFormatters.GetOrDefault`. Localized display names and UI belong to consuming applications. Rich HTML, ANSI-span, Markdown-document, table, and accessibility-tree models are intentionally outside this string-returning API.

```c#
using KatLang;
using KatLang.Formatting;

var result = KatLangEngine.Run(source);

var exact = OutputFormatters.Exact.Format(result);       // canonical, byte-identical to result.ToDisplayString()
var readable = OutputFormatters.Readable.Format(result); // keeps all (), [] — improves layout
var concise = OutputFormatters.Concise.Format(result);   // hides only provably safe sequence parentheses
```

- **exact** is canonical KatLang display: raw unquoted strings, culture-invariant numbers, `DisplayDecimals`, platform newlines, and the bounded-display contract. It is byte-for-byte `ToDisplayString()`.
- **readable** preserves every sequence parenthesis and list bracket and chooses layout from BOTH preferred line width and structural complexity: a value whose flat text fits can still become multiline when it contains two or more structured children, and a nested multi-pair string/value child renders one pair per line, so nested structure stays visible. Simple flat values remain inline, and independently emitted root outputs are separated by blank lines.
- **concise** may hide sequence parentheses only where line structure and indentation provably carry the boundary; list brackets and the empty sequence `()` always remain visible, and it never invents colons, bullets, headings, labels, or capitalization — `('neto' 1473.8)` can display as `neto 1473.8`, never `neto: 1473.8`. A one-pair child sequence becomes one line; a safe nested multi-pair child becomes an indented pair block (one pair per line) even when it would fit joined, while a root pair sequence may stay flat — structural line grouping only, never dictionary or record semantics. Width alone never forces a structured value flat, so natural nested results need no spread for presentation (spread discards the parent structure, and the formatter never reconstructs it). With zero root spacing it hides root parentheses only when a nested pair block visibly anchors the block, and with zero indentation it retains multiline child parentheses. The string-delimiter policy controls quoting only: under `StringDelimiterMode.Never`, safe raw labels such as `neto` or `net_salary` still participate in delimiter removal, while an ambiguous raw string (empty, whitespace-bearing, comma-bearing, structural-looking, quote-bearing, numeric-looking, control-bearing, or containing invisible Unicode format characters or unpaired surrogates) makes its containing sequence keep canonical parentheses and separators instead of being quoted or altered.

For a natural structured result such as `SalaryExpenses(2000, 1, 0)` emitting `(('neto' 1473.80), ('taxes' 998.36), ('social' 681.80 'income' 316.20 'risk' 0.36), ('total' 2472.16))` — with an explicit `''` row between reports for spacing — `concise` with `NewLine = "\n"`, `RootOutputSpacing = 0`, and `StringDelimiters = StringDelimiterMode.Never` renders both reports:

```text
neto 1473.80
taxes 998.36
  social 681.80
  income 316.20
  risk 0.36
total 2472.16

neto 334.72
taxes 286.06
  social 171.13
  income 114.57
  risk 0.36
total 620.78
```

The single blank line is the program's explicit empty-string row (under `Never` an empty string renders as an empty text run; under `WhenNeeded` it stays visible as `''`, distinct from formatter-added root spacing).
- String content is always preserved verbatim in every mode — underscores are ordinary characters (`net_salary` never becomes `net salary`). Readable and Concise support a configurable string-delimiter policy; `WhenNeeded` quotes empty, whitespace-bearing, numeric-looking, and structurally ambiguous strings, while `Always` quotes every faithfully representable string. Delimiters are presentation around the value, never a content change, and strings that cannot be quoted faithfully (KatLang has no escape syntax) render raw.
- `RunResult.Success.OutputRows` exposes the root-output rows, so separately emitted root outputs stay distinguishable from one sequence value containing the same items.

Per-call options (immutable, shareable):

```c#
var text = OutputFormatters.Readable.Format(result, new OutputFormattingOptions
{
    IndentSize = 2,
    PreferredLineWidth = 100,
    StringDelimiters = StringDelimiterMode.WhenNeeded,
});
```

`OutputFormattingOptions` also covers the newline sequence, the number of blank lines between root-output blocks (`RootOutputSpacing`), and an optional `MaxDisplayLength` that can lower — never raise — the run's display limit.

## Nuget package
https://www.nuget.org/packages/KatLang

License and patent grant details are included in the repository and package files (`LICENSE`, `PATENTS`).

## Licensing

This project is released under the MIT License with an additional patent grant provided by Logics Research Centre SIA.

Please see:
- LICENSE
- PATENTS
- NOTICE
- CODE_OF_CONDUCT.md
- CONTRIBUTING.md

The patent grant covers use and distribution of KatLang, derivative works, and independent reimplementations of the KatLang language that conform to the KatLang specification (`KatLang.lean`). If you are building such an implementation, you are already covered — no permission needed. For uses of the patented techniques outside the scope of KatLang, you are welcome to reach out — Logics Research Centre SIA is open to discussing licensing arrangements. Don't hesitate to get in touch: mikus.vanags@logicsresearchcentre.com

> "Ask and it will be given to you; seek and you will find; knock and the door will be opened to you."
> Matthew 7:7

## Roadmap
Research on possible syntax improvements.
Improve KatLang type system.
Performance improvements.

## Co-funded by the European Union

1.1.1.9 Research application No 1.1.1.9/LZP/3/25/353 of the Activity "Post-doctoral Research" "KatLang: Enhancing a Higher-Order Domain-Specific Language for Problem Solving and Educational Assessment in Mathematics and Physics".

## Authorship and Contributions

KatLang is created and authored by Mikus Vanags and published by Logics Research Centre SIA. Copyright is held by Logics Research Centre SIA and Contributors: contributors keep the copyright in their contributions and license them under the MIT License, with no Contributor License Agreement required (see CONTRIBUTING.md). Contributions from the community are very welcome — whether through ideas, discussions, bug reports, documentation improvements, or code. The full list of contributors is at https://github.com/katlangorg/katlangnet/graphs/contributors.

## Feedback
Contact Mikus Vanags: mikus.vanags@logicsresearchcentre.com

---

> "So whether you eat or drink or whatever you do, do it all for the glory of God."
> 1 Corinthians 10:31

Jesus is Lord.
