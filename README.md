# KatLang — Language for Calculations
To learn more read the [KatLang tutorial](http://katlang.org/tutorial) or play with [KatLang online](http://katlang.org).

## Language Specification
The authoritative KatLang specification is defined in [`KatLang.lean`](https://github.com/katlangorg/katlangnet/blob/main/lean/KatLang.lean) using the Lean theorem prover. It is the single source of truth for KatLang's evaluation semantics and language rules over the elaborated program structure (AST shape, evaluation rules, and invariants). Surface syntax and grammar are defined by [`KatLang.ebnf`](https://github.com/katlangorg/katlangnet/blob/main/KatLang.ebnf) together with the reference parser in this repository. Independent implementations should conform to this specification.

If you have ideas for improving or extending the KatLang language — new constructs, better semantics, or clearer language rules — you are warmly welcome to open a discussion or reach out directly. Good ideas are always worth a conversation.

## Use of KatLang .NET parsing and evaluation library
The simplest embedding call returns a structured result; render it explicitly:

```c#
using KatLang;

var result = await KatLangEngine.RunAsync("1 + 2");
Console.WriteLine(result.ToDisplayString());
```

For explicit success and failure handling:

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

var text = KatLangEngine.Run(source) switch
{
    RunResult.Success s => s.ToDisplayString(),
    RunResult.NoProgramOutput n => n.ToDisplayString(),
    RunResult.ParseFailure p => string.Join(Environment.NewLine, p.Errors),
    RunResult.EvalFailure e => string.Join(Environment.NewLine, e.Errors),
};
Console.WriteLine(text);
```

`RunResult` is a C# `closed` record hierarchy: those four variants are the only ones and no other assembly can add one, so a switch *expression* like the one above needs no catch-all arm — the compiler proves it exhaustive and reports a missing variant (warning `CS8509`, worth promoting to an error in your project). A switch *statement* over the same value compiles without that check, so use the expression form when you want the guarantee. `Result`, `Algorithm`, `Pattern`, `Expr`, `ErrorContext`, and the parameter-pattern hierarchy are closed the same way. `EvalError` is closed too but keeps one internal variant, so classify errors through `KatLangError.Code` rather than by enumerating its variants.

Everything a run can be configured with is one `RunOptions` object — resource limits, cancellation, host operations, module loading, a random seed, and a default display precision. Its configuration is fixed once initialized and safe to reuse across sequential and concurrent runs; the engine keeps no state between calls. Delegate closures and cancellation sources remain host-owned; shared delegates must tolerate concurrent calls. A program's own failures never throw: they are `RunResult` variants carrying structured `KatLangError`s (classify by `Code`, locate by `Span`; `Message` is presentation text). Only host misuse (`ArgumentException` and its subclasses, or `InvalidOperationException` for a configuration that needs `RunAsync`), cancellation (`OperationCanceledException`), and exceptions thrown by your own host operations escape, and `RunAsync` delivers each of them through its task.

```c#
using KatLang;

using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(5));
var options = new RunOptions
{
    // One stop signal for the whole run: source processing and evaluation.
    SourceProcessingCancellationToken = timeout.Token,
    EvaluationCancellationToken = timeout.Token,
    EvaluationLimits = new EvaluationLimits { MaxSteps = 1_000_000 },
    // A host operation is an ambient callable the program references by name.
    HostOperations = HostOperations.Create(
        HostOperation.Create("TaxRate", (_, _) => new Result.Atom(0.255m))),
};

var result = await KatLangEngine.RunAsync("Net(gross) = gross * (1 - TaxRate)\nNet(1600)", options);
if (result is RunResult.Success { Value: var value } && value.AsNum() is { } net)
    Console.WriteLine(net);                       // the structured value
else
    Console.WriteLine(result.ToDisplayString());  // the diagnostics as text
```

`Parser.Parse`/`ParseAsync` run the same complete front end without evaluating — for validation and for editor tooling through `Semantics.SemanticModelBuilder.Build(parseResult)`. `Evaluator.Run`/`RunAsync`/`RunFlat`/`RunFlatAsync` are a lower layer: they evaluate a host-built `Expr` exactly as given, without parsing, module loading, front-end elaboration, or the program's `DisplayDecimals` setting, so they are not source runners. The package ships its XML documentation and is marked trimmable and NativeAOT-compatible, with the trim and AOT analyzers run over it on every build.

`RunResult` and `ParseResult` are library-produced snapshots with readable payloads and deconstruction, not publicly constructible result containers. Use `Result` variant constructors to return values from host operations. The advanced AST is an elaborated semantic representation, not a deeply immutable syntax DTO: `ScopeCtx` describes lexical parent declarations, while runtime activation state stays internal. Host-built AST collections must not be mutated during evaluation or analysis. All four evaluator families support host operations; the `RunFlat` families apply a bounded numeric projection and intentionally discard strings, Booleans, and structure.

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

- **exact** is canonical KatLang display: raw unquoted strings, culture-invariant numbers, the run's effective display decimals (`DisplayDecimals`, or the host default below), platform newlines, and the bounded-display contract. It is byte-for-byte `ToDisplayString()`.
- **readable** preserves every sequence parenthesis and list bracket and chooses layout from BOTH preferred line width and structural complexity: a value whose flat text fits can still become multiline when it contains two or more structured children, and a nested multi-pair string/value child renders one pair per line, so nested structure stays visible. Simple flat values remain inline, and independently emitted root outputs are separated by blank lines.
- **concise** may hide sequence parentheses only where line structure and indentation provably carry the boundary; list brackets and the empty sequence `()` always remain visible, and it never invents colons, bullets, headings, labels, or capitalization — `('neto', 1473.8)` can display as `neto 1473.8`, never `neto: 1473.8`. A one-pair child sequence becomes one line; a safe nested multi-pair child becomes an indented pair block (one pair per line) even when it would fit joined, while a root pair sequence may stay flat — structural line grouping only, never dictionary or record semantics. Width alone never forces a structured value flat, so natural nested results need no spread for presentation (spread discards the parent structure, and the formatter never reconstructs it). With zero root spacing it hides root parentheses only when a nested pair block visibly anchors the block, and with zero indentation it retains multiline child parentheses. The string-delimiter policy controls quoting only: under `StringDelimiterMode.Never`, safe raw labels such as `neto` or `net_salary` still participate in delimiter removal, while an ambiguous raw string (empty, whitespace-bearing, comma-bearing, structural-looking, quote-bearing, numeric-looking, control-bearing, or containing invisible Unicode format characters or unpaired surrogates) makes its containing sequence keep canonical parentheses and separators instead of being quoted or altered.

For a natural structured result such as `SalaryExpenses(2000, 1, 0)` emitting `(('neto', 1473.80), ('taxes', 998.36), ('social', 681.80, 'income', 316.20, 'risk', 0.36), ('total', 2472.16))` — with an explicit `''` row between reports for spacing — `concise` with `NewLine = "\n"`, `RootOutputSpacing = 0`, and `StringDelimiters = StringDelimiterMode.Never` renders both reports:

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

When a rendering exceeds the effective display limit, the string surfaces return the bounded limit notice (or `…`, or an empty string, when even the notice does not fit). A program's genuine output can equal that notice, so overflow is detected structurally, never from the text: `result.RenderDisplay()` and `formatter.RenderDisplay(result, options)` return a `DisplayRendering` whose `Text` is the same string and whose `LimitExceeded` / `LimitError` (a `KatLangError` with code `DisplayLengthLimitExceeded`) report the overflow. Evaluation is unaffected — the run stays a `Success` with its structured value.

```c#
var rendering = OutputFormatters.Exact.RenderDisplay(result);
if (rendering.LimitExceeded)
    Console.Error.WriteLine(rendering.LimitError.Message);   // a diagnostic, never program output
else
    Console.WriteLine(rendering.Text);
```

`ToDisplayString()` and `OutputFormatter.Format(...)` discard the structured rendering status; use `Run`/`RunAsync` followed by `RenderDisplay` when evaluation and rendering status matter. `EvaluateToAtoms`/`EvaluateToAtomsAsync` are the only lossy conveniences: they return the numeric atoms of a successful run (strings, Booleans, and structure are dropped) and throw `KatLangException` otherwise — never use them for display.

The CLI's `run` and `eval` commands render before writing program output. Display overflow returns exit code 1, writes the complete limit notice once to stderr, and leaves stdout empty. Genuine notice-shaped output remains successful stdout output with exit code 0. Ordinary output keeps its terminating newline; programs with no output rows succeed silently. `check` validates source without executing or rendering it, so valid source that would overflow on execution still passes silently.

## Command-line module loading

The `katlang` CLI's `--allow-loading` flag is off by default: without it, source that uses `load` or `open 'url'` is rejected with a diagnostic and nothing is fetched. With it, KatLang hands a load target to the CLI's HTTP transport only after its own checks pass — an HTTPS URL on an allowed host (`katlang.org` and its subdomains); anything else is refused before any request is made. The transport policies below belong to the shipped CLI, not to the KatLang package, whose host-supplied downloader contract is unchanged:

- HTTP redirects are refused rather than followed.
- Each downloaded module is limited to **1 MiB (1,048,576 content bytes)**. This is a fixed CLI transport policy, independent of and intentionally stricter than the library's decoded-source limit: valid source that fits the library limit can still be refused by the CLI. Non-ASCII and non-UTF-8 sources consume the content bytes their encoding requires, including any byte-order mark. An excessive declared `Content-Length` is refused before buffering; a chunked or unknown-length body is refused when a buffer write would exceed the ceiling. The ceiling counts content bytes exposed by `HttpContent`, excluding HTTP headers and chunk framing. No decompression is negotiated or performed. Network read-ahead and the HTTP client's bounded disposal drain are separate from accepted buffer contents.
- Each complete module download has one absolute **15-second cancellation deadline** starting before the request and remaining active through headers and body acquisition. Incoming bytes do not restart it, so both stalled and trickling responses are cancelled. Cancellation is cooperative; bounded synchronous text decoding is not preemptible.

These bounds apply per download. KatLang's `SourceProcessingLimits` (decoded per-module source length, aggregate source, module count, import depth) still apply separately to the text the transport returns. A refused or timed-out download is reported as an ordinary `load: failed to fetch` diagnostic with exit code 1.

## Reproducible randomness

`Math.Random` / `random` and `Math.RandomInt` / `randomInt` are nondeterministic by default: every evaluation draws from fresh entropy. A host can make one evaluation reproducible by supplying a seed:

```c#
var options = new RunOptions { RandomSeed = 42 };
var first = KatLangEngine.Run("Math.RandomInt(1, 7), Math.Random(0, 1)", options);
var second = KatLangEngine.Run("Math.RandomInt(1, 7), Math.Random(0, 1)", options);
// first and second display the same values; any long (0, negative, the extremes) is a valid seed.
```

The direct `Evaluator.Run`, `RunAsync`, `RunFlat`, and `RunFlatAsync` families accept the same `long? randomSeed`, and the CLI exposes it for the evaluating commands:

```
katlang run <file> --random-seed <integer>
katlang eval <source> --random-seed <integer>
```

Each of those evaluator families has exactly one overload per argument count, so positional `null` arguments always select one overload: `Evaluator.Run(expr, null, null, token)` is the limits-and-seed overload, and the host-operation form takes the seed explicitly, `Evaluator.Run(expr, operations, limits, randomSeed, token)` (pass `null` for an unseeded run; a null `HostOperations` argument is rejected).

`--random-seed` takes any signed 64-bit integer as the next token (`--random-seed -5` and `--random-seed +5` are different seeds; `--random-seed=5` is not accepted) and is refused by `check`, which does not evaluate. The seed is host configuration only: KatLang source has no seeding syntax, and a program property named `RandomSeed` is an ordinary property that seeds nothing. A bare `--` ends the options, so a file or source argument that itself begins with two dashes is written after it (`katlang eval -- "--1"`). For a given KatLang version, the same program (loaded module contents and a `DisplayDecimals` property included), the same seed, and the same evaluated KatLang path produce the same random values on every supported platform, through synchronous and asynchronous entry points alike and regardless of internal optimizer strategy. Both random operations, in every spelling, consume one run-scoped stream in evaluation order, so a seed reproduces a stream — it does not memoize calls, and the ordinary rules (left-to-right arguments, lazy `if` branches, the zero-argument property cache for value reads, explicit `A()` re-evaluation and the builtin value slots that demand a property's algorithm directly — `sum(A)`, `if(true, A, 0)`, `A.string` — see the tutorial's caching section) decide which calls draw. The seed is immutable configuration: reusing one `RunOptions` object replays the stream from its beginning for every run, and concurrent runs sharing it get independent streams. The exact stream may change between KatLang versions when the generator, a sampling algorithm, or evaluation semantics deliberately change; KatLang randomness is not cryptographically secure. The internal generator contract (a SplitMix64 stream with exact bounded-rejection sampling) is documented in `docs/design/seeded-randomness-2026-09.md`.

## Default display decimals

A program's top-level `DisplayDecimals = n` property (an integer from 0 through 99) sets how many digits after the decimal point its displayed numbers show. A host can supply a DEFAULT for programs that declare no such property:

```c#
var options = new RunOptions { DefaultDisplayDecimals = 3 };
KatLangEngine.Run("1 / 7", options).ToDisplayString();                      // 0.143
KatLangEngine.Run("DisplayDecimals = 6\n1 / 7", options).ToDisplayString(); // 0.142857: the program's property wins
```

The CLI exposes it for the evaluating commands:

```
katlang eval --display-decimals 3 "1 / 7"
katlang run --display-decimals 6 program.kat
```

A run's effective setting is the program's own `DisplayDecimals` property when it declares one, otherwise the host default, otherwise canonical full-precision display. A declared property always decides: an invalid one (`DisplayDecimals = -1`) still fails the run with its own diagnostic instead of falling back to the default. The default is display-only host configuration, not a KatLang property — nothing is added to the program, so name resolution, diagnostics, and editor tooling see the source as written — and it is never evaluated: it consumes no evaluation budget, draws no random value, invokes no host operation, and changes no value, atom, comparison, or control flow. Every rendering surface of the result uses the same effective setting with the same rounding (midpoints away from zero), special-value spellings, and display-length bound: `ToDisplayString`, `RenderDisplay`, and the `exact`/`readable`/`concise` and custom formatters. `RunOptions.MaxDisplayDecimals` is the shared upper bound; a default outside 0 through 99 throws `ArgumentOutOfRangeException` when the options object is initialized, and the CLI reports it as a usage error — values are rejected, never clamped. Like `--random-seed`, `--display-decimals` takes its value as the next token (`--display-decimals=2` is not accepted, and a leading sign or zeros such as `+2` or `02` spell the same integer) and is refused by `check`, which does not evaluate.

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
