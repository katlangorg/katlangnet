# Using KatLang from .NET

The [KatLang NuGet package](https://www.nuget.org/packages/KatLang) parses, checks and runs KatLang programs in .NET 11 applications, and gives editor tooling a semantic model of each program. This guide describes the host API. The language itself is taught in the [tutorial](https://katlang.org/tutorial), and the `katlang` tool has its own [command-line guide](cli.md).

```text
dotnet add package KatLang
```

## Contents

1. [Running a program](#running-a-program)
2. [Configuring a run](#configuring-a-run)
3. [Parsing, editor tooling and the evaluator layer](#parsing-editor-tooling-and-the-evaluator-layer)
4. [Plain-text output formatting](#plain-text-output-formatting)
5. [Loading modules safely](#loading-modules-safely)
6. [Reproducible randomness](#reproducible-randomness)
7. [Decimal places: minimum, maximum, source and host](#decimal-places-minimum-maximum-source-and-host)
8. [Observing intermediate property values](#observing-intermediate-property-values)
9. [Code links](#code-links)
## Running a program

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

var result = KatLangEngine.Run(source);
IReadOnlyList<KatLangError>? errors = result switch
{
    RunResult.Success or RunResult.NoProgramOutput => null,
    RunResult.ParseFailure p => p.Errors,
    RunResult.EvalFailure e => e.Errors,
};

if (errors is null)
{
    Console.WriteLine(result.ToDisplayString());   // program output: intentional, written as is
}
else
{
    foreach (var error in errors)
        Console.Error.WriteLine(error.ToTerminalSafeString());
    Environment.ExitCode = 1;
}
```

`RunResult` is a C# `closed` record hierarchy: those four variants are the only ones and no other assembly can add one, so a switch *expression* like the one above needs no catch-all arm — the compiler proves it exhaustive and reports a missing variant (warning `CS8509`, worth promoting to an error in your project). A switch *statement* over the same value compiles without that check, so use the expression form when you want the guarantee. `Result`, `Algorithm`, `Pattern`, `Expr`, `ErrorContext`, and the parameter-pattern hierarchy are closed the same way. One `Result` variant, `Result.CallReference` (the run-scoped value a `meta` parameter captures, and its argument view `R.Arguments`), never reaches a host — every run result, host-operation argument and display boundary refuses it — so a host switch names it only to stay exhaustive. `EvalError` is closed too but keeps one internal variant, so classify errors through `KatLangError.Code` rather than by enumerating its variants.

Write diagnostics with `KatLangError.ToTerminalSafeString()`. A diagnostic can quote the program's source text and string values verbatim, so `Message`, `KatLangError.ToString()` and the text of a failed `RunResult.ToDisplayString()` are diagnostic data, not terminal-safe output: printed raw, a hostile program could send terminal control sequences or forge extra diagnostic lines. `ToTerminalSafeString()` keeps the familiar `[line:column] message` text and KatLang's own line breaks but shows every control, invisible format or bidirectional character, Unicode line separator and unpaired surrogate inside the quoted text as a visible `\uXXXX` escape — it is what the `katlang` CLI prints for each diagnostic. It is for terminals and plain-text logs; a graphical, HTML or JSON presentation applies its own escaping to `Message`, and code classifies errors by `Code`, never by message text. Successful program output is the program's intended data and is never sanitized.

## Configuring a run

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
{
    Console.WriteLine(net);                       // the structured value
}
else
{
    IReadOnlyList<KatLangError>? errors = result switch
    {
        RunResult.Success or RunResult.NoProgramOutput => null,
        RunResult.ParseFailure p => p.Errors,
        RunResult.EvalFailure e => e.Errors,
    };
    if (errors is null)
    {
        Console.WriteLine(result.ToDisplayString());
    }
    else
    {
        foreach (var error in errors)
            Console.Error.WriteLine(error.ToTerminalSafeString());
        Environment.ExitCode = 1;
    }
}
```

## Parsing, editor tooling and the evaluator layer

`Parser.Parse`/`ParseAsync` run the same complete front end without evaluating — for validation and for editor tooling through `Semantics.SemanticModelBuilder.Build(parseResult)`, which models every parse result: a program whose module is missing (no downloader, or a load that failed) keeps its `load` directives in a provisionally elaborated tree, and the names that module could supply are classified as indeterminate rather than as errors. `Evaluator.Run`/`RunAsync`/`RunFlat`/`RunFlatAsync` are a lower layer: they evaluate a host-built `Expr` exactly as given, without parsing, module loading, front-end elaboration, or the program's `MinDecimalPlaces` / `MaxDecimalPlaces` settings, so they are not source runners. The package ships its XML documentation and is marked trimmable and NativeAOT-compatible, with the trim and AOT analyzers run over it on every build.

`ParseResult.Diagnostics` keeps the first `SourceProcessingLimits.MaxDiagnosticCount` diagnostics in reporting order (1000 by default). If any are omitted, it adds one unpositioned `DiagnosticCountExceeded` entry with the highest omitted severity. `RunResult.ParseFailure.Errors` contains only the error-severity entries of that list, so it includes the marker only if an error was omitted. A conditional branch that loads modules on demand applies the same bound when selected. If materialization fails, its evaluation error carries the error messages.

Every diagnostic has a `Severity`, and only an error blocks: `ParseResult.HasErrors` is true exactly when the list holds an error, and the engine runs a program whose only diagnostics are warnings. KatLang reports one warning, `DiagnosticCode.UnreachableClauseAfterCatchAll`, on a clause written after a catch-all clause of the same conditional algorithm (`F(x) = …` followed by `F(0) = …`): the later clause is kept, and no call ever selects it. The warning underlines the later clause's head and names the catch-all and its line. Warnings are in `ParseResult.Diagnostics`, so parse the source to show them; a `RunResult` carries errors only.

`RunResult` and `ParseResult` are library-produced snapshots with readable payloads and deconstruction, not publicly constructible result containers. Use `Result` variant constructors to return values from host operations. The advanced AST is an elaborated semantic representation, not a deeply immutable syntax DTO: `ScopeCtx` describes lexical parent declarations, while runtime activation state stays internal. Host-built AST collections must not be mutated during evaluation or analysis. All four evaluator families support host operations; the `RunFlat` families apply a bounded numeric projection and intentionally discard strings, Booleans, and structure.

## Plain-text output formatting

Formatting is bounded plain-text presentation only — it never re-parses, re-evaluates, or changes values, and the parser and evaluator know nothing about formatter modes. Three built-in formatters share one formatter-neutral value renderer and are selected by stable lowercase ids suitable for persistence (`exact`, `readable`, `concise`); unknown ids fall back to `exact` via `OutputFormatters.GetOrDefault`. Localized display names and UI belong to consuming applications. Rich HTML, ANSI-span, Markdown-document, table, and accessibility-tree models are intentionally outside this string-returning API.

```c#
using KatLang;
using KatLang.Formatting;

var result = KatLangEngine.Run(source);

var exact = OutputFormatters.Exact.Format(result);       // canonical, byte-identical to result.ToDisplayString()
var readable = OutputFormatters.Readable.Format(result); // keeps all (), [] — improves layout
var concise = OutputFormatters.Concise.Format(result);   // uses spaces and indentation where the layout permits
```

- **exact** is canonical KatLang display: raw unquoted strings, culture-invariant numbers, the run's effective decimal places (the program's `MinDecimalPlaces` / `MaxDecimalPlaces` settings, each composed with the host setting of the same name described below), platform newlines, and the bounded-display contract. It is byte-for-byte `ToDisplayString()`.
- **readable** preserves every sequence parenthesis and list bracket and chooses layout from BOTH preferred line width and structural complexity: a value whose flat text fits can still become multiline when it contains two or more structured children, and a nested multi-pair string/value child renders one pair per line, so nested structure stays visible. Simple flat values remain inline, and independently emitted root outputs are separated by blank lines.
- **concise** uses spaces to join scalar sequences that fit on one line. A nested sequence with two or more string/value pairs can use an indented block with one pair per line. These layouts preserve string content verbatim, including embedded punctuation, repeated spaces, and empty strings. The quoting policy still applies. For example, `('social tax', 3)` displays as `social tax 3` under `Never` and as `'social tax' 3` under `WhenNeeded` or `Always`. With `Never`, different values can produce the same display text. List brackets and the empty sequence `()` stay visible. Multiline strings, width, and nesting can require sequence delimiters. At zero root spacing, a multiline root sequence can use a block without parentheses when an indented pair block anchors it.

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
- String content is always preserved verbatim in every mode — underscores are ordinary characters (`net_salary` never becomes `net salary`). Readable and Concise support a configurable string-delimiter policy; `WhenNeeded` quotes empty, whitespace-bearing, numeric-looking, and structurally ambiguous strings, while `Always` quotes every faithfully representable string. Delimiters are presentation around the value, never a content change, and strings that cannot be quoted faithfully in the formatters' single-quote delimiters (a single-quoted KatLang string has no escapes, so a string containing `'`, a line feed or a carriage return) render raw.
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
    Console.Error.WriteLine(rendering.LimitError.ToTerminalSafeString());   // a diagnostic, never program output
else
    Console.WriteLine(rendering.Text);
```

`ToDisplayString()` and `OutputFormatter.Format(...)` discard the structured rendering status; use `Run`/`RunAsync` followed by `RenderDisplay` when evaluation and rendering status matter. `EvaluateToAtoms`/`EvaluateToAtomsAsync` are the only lossy conveniences: they return the numeric atoms of a successful run (strings, Booleans, and structure are dropped) and throw `KatLangException` otherwise — never use them for display.

## Loading modules safely

KatLang source can import other KatLang source with `Lib = load('https://…')` or `open 'https://…'`. Loading is **off by default**: `RunOptions.DownloadCode` is `null`, the library contains no network transport, and a program that loads anything gets a diagnostic while nothing is fetched (editor tooling still analyzes the rest of it). A host opts in by supplying the downloader, and with it takes on the security of the transport:

- **KatLang checks every load target before calling your downloader.** The target must be an absolute `https` URL without user information (`user:password@`), whose host is a valid DNS name or an IP literal, and whose host is allowed. `RunOptions.AllowedHosts` (default: `katlang.org`) admits a DNS name and its subdomains by whole labels — `sub.ex.com` under `ex.com`, never `notex.com` or `ex.com.evil.net` — and an IP literal only exactly. Names are compared in their ASCII (IDNA) form, so letter case and Unicode or punycode spellings of one name match; a trailing-dot spelling does not; any port of an allowed host is admitted. A refused target never reaches the downloader.
- **A host that means to admit every host says so explicitly**, with `RunOptions.AllowAnyHost = true` instead of a list. It is off by default, so a host that does not set it behaves as before, and it is the only way: no entry of `AllowedHosts` means "every host", and a wildcard entry such as `*` admits nothing. It lifts the host list and nothing else — a target must still be `https`, carry no user information and name a valid DNS name or IP literal — and it cannot be combined with a list (`ArgumentException` where the parse or run begins). With every host admitted, your downloader is the only barrier between a program and the network it runs in: a program can name a loopback, private or link-local address, or an internal host name. Set it only with a downloader that resolves the host itself, refuses the addresses it must not reach, and connects only to an address it checked.
- **Your downloader receives one canonical URL per module** — `https`, the ASCII host, a non-default port, the escaped path and query, no fragment. It is also the module's identity: equivalent spellings share one download, load cycles are detected on it, and diagnostics name it — query string included, so a module URL is no place for a secret.
- **KatLang cannot see what that URL fetches.** Redirects, DNS answers, and the address a name resolves to happen inside your downloader, so `AllowedHosts` restricts the host name written in source and is not an SSRF defense by itself. Refuse redirects (or re-validate them), apply any address policy you need, and bound time and response size in the downloader. An exception it throws becomes a `load: failed to fetch` diagnostic quoting its message (or naming its type when the message cannot be read); `SourceProcessingCancellationToken` is passed to it and stays authoritative.
- **The same rules apply at every depth.** A module's own loads — nested modules, and modules a conditional branch loads only when evaluation selects it — pass the same checks against the same allow-list, observe the same cancellation, and draw on the same run budget.
- **Work is bounded.** `SourceProcessingLimits` bounds each source text, the total source a run elaborates, the import depth, and the number of module downloads per run. Every downloader invocation counts, including cancellation after it starts, so a program cannot re-request unreachable or oversized modules without limit. A module the run already loaded is not downloaded again and is elaborated once, but every further splice of it still counts toward the total source, so the limit bounds the program as written. Re-evaluations of one parsed tree share its remaining loading budget.
- **Check `ParseResult.HasErrors` before evaluating its `Root`.** A parse with errors produces a recovery tree for diagnostics and editor queries. Direct evaluation can download modules and then throw `InvalidOperationException` when a deferred branch needs to compile.
- **Choose a source token for the lifetime of a retained tree.** A deferred branch uses the `SourceProcessingCancellationToken` supplied to `Parser.ParseAsync`. Once cancelled, that token still permits reuse of an already compiled branch. Selecting a branch that still needs compilation throws `OperationCanceledException` carrying the parse token, even with a fresh evaluation token. Parse again with a live token to compile further branches.
- **Loaded code runs with the run's capabilities, in its own scope.** A module is elaborated and evaluated as part of the program: it can call every host operation the run registers. Its names resolve in the module itself and then the built-in names (builtins, `Math`, the run's host operations) — never in the importing program, so an importer's definitions (a local `sum`, a property named like a module input) cannot change what a module computes, and a module cannot read an importer's names. A name the module does not define is a parameter of the module member that uses it, supplied by the importer as an argument. One canonical URL is one module per program: every load and `open` of it shares one set of member results. Allow only hosts whose code you would run yourself. Any front-end error, including invalid downloaded source, stops the run before evaluation starts, so no host operation runs.

```c#
using System.Net;
using System.Net.Http;
using KatLang;

using var http = new HttpClient(new SocketsHttpHandler { AllowAutoRedirect = false, UseCookies = false })
{
    Timeout = TimeSpan.FromSeconds(15),
    MaxResponseContentBufferSize = 1024 * 1024,
};
var options = new RunOptions
{
    AllowedHosts = ["modules.example.com"],
    DownloadCode = async (url, token) =>
    {
        using var response = await http.GetAsync(url, token);
        if (response.StatusCode != HttpStatusCode.OK)
            throw new HttpRequestException($"HTTP status {(int)response.StatusCode}");
        return await response.Content.ReadAsStringAsync(token);
    },
};
var result = await KatLangEngine.RunAsync(source, options);
```

## Reproducible randomness

`Math.Random` / `random` and `Math.RandomInt` / `randomInt` are nondeterministic by default: every evaluation draws from fresh entropy. A host can make one evaluation reproducible by supplying a seed:

```c#
var options = new RunOptions { RandomSeed = 42 };
var first = KatLangEngine.Run("Math.RandomInt(1, 7), Math.Random(0, 1)", options);
var second = KatLangEngine.Run("Math.RandomInt(1, 7), Math.Random(0, 1)", options);
// first and second display the same values; any long (0, negative, the extremes) is a valid seed.
```

The direct `Evaluator.Run`, `RunAsync`, `RunFlat`, and `RunFlatAsync` families accept the same `long? randomSeed`, and the `katlang` tool takes a seed with `--random-seed` (see the [command-line guide](cli.md#reproducible-randomness)).

Each of those evaluator families has exactly one overload per argument count, so positional `null` arguments always select one overload: `Evaluator.Run(expr, null, null, token)` is the limits-and-seed overload, and the host-operation form takes the seed explicitly, `Evaluator.Run(expr, operations, limits, randomSeed, token)` (pass `null` for an unseeded run; a null `HostOperations` argument is rejected).

The seed is host configuration only: KatLang source has no seeding syntax, and a program property named `RandomSeed` is an ordinary property that seeds nothing. For a given KatLang version, the same program (loaded module contents and the root's `MinDecimalPlaces` and `MaxDecimalPlaces` settings, which the engine evaluates in that order after the output whatever the host settings are, included), the same seed, and the same evaluated KatLang path produce the same random values on every supported platform, through synchronous and asynchronous entry points alike and regardless of internal optimizer strategy. Both random operations, in every spelling, consume one run-scoped stream in evaluation order, so a seed reproduces a stream — it does not memoize calls, and the ordinary rules (explicit spreads when a call's arguments are formed, then each argument when its value is first needed — an unneeded argument never draws; lazy `if` branches, one evaluation per run of each zero-parameter property however its value is consumed — `A`, `sum(A)`, `A.sum`, `if(true, A, 0)`, and `A.string` all see the same draw — and a fresh evaluation for every explicit `A()`) decide which calls draw. The seed is immutable configuration: reusing one `RunOptions` object replays the stream from its beginning for every run, and concurrent runs sharing it get independent streams. The exact stream may change between KatLang versions when the generator, a sampling algorithm, or evaluation semantics deliberately change; KatLang randomness is not cryptographically secure. The internal generator contract (a SplitMix64 stream with exact bounded-rejection sampling) is documented in [`docs/design/seeded-randomness-2026-09.md`](design/seeded-randomness-2026-09.md).

## Decimal places: minimum, maximum, source and host

Three different things are easy to confuse. PRECISION is how exactly a number is calculated: KatLang computes in IEEE 754 Decimal128, 34 significant digits, and nothing in this section changes it. The MAXIMUM of displayed decimal places limits how many digits after the decimal point are SHOWN; the MINIMUM says how many are shown at least. Both are presentation only — they never change a value, its Decimal128 representation, a comparison, `.string`, or any intermediate result.

Each of the two settings is an integer from 0 through 99 and can come from two origins:

- the SOURCE setting: a program root's own top-level `MinDecimalPlaces = n` or `MaxDecimalPlaces = n` property;
- the HOST setting: `RunOptions.MinDecimalPlaces` / `RunOptions.MaxDecimalPlaces` (the CLI's `--min-decimal-places` / `--max-decimal-places`, or a host application's display setting).

Each setting composes independently with its counterpart of the same name: an absent one imposes nothing; one present is the effective value; both present give the SMALLER of the two; neither leaves that setting absent. Neither origin overrides the other: a host maximum of 5 shows a `MaxDecimalPlaces = 7` program with at most 5 places, while a host maximum of 10 leaves it at 7. A shared program therefore carries its display intent to every host, and a host can still ask for less. And neither setting supplies a value for the other: with only a minimum set nothing is rounded, with only a maximum set nothing is padded.

With at least one effective setting present, a finite number is displayed like this: rounded to the maximum when there is one (midpoints away from zero), written with the fewest decimal places that represent it exactly — so zeros stored at the end of the decimal part are removed — and padded with zeros up to the minimum, whole numbers included. It has no decimal point when it has no decimal places, and it keeps its sign, also for a zero and for a value that rounds to zero. `NaN`, `Infinity` and `-Infinity` keep their spellings. With no setting from either origin, display is canonical: a number shows the digits it carries, so `2.5000` stays `2.5000`.

| Value | min 2 | max 4 | min 2, max 4 | min 2, max 2 | min 0 |
|---|---|---|---|---|---|
| `10` | `10.00` | `10` | `10.00` | `10.00` | `10` |
| `2.5000` | `2.50` | `2.5` | `2.50` | `2.50` | `2.5` |
| `1.234567` | `1.234567` | `1.2346` | `1.2346` | `1.23` | `1.234567` |
| `0.125` | `0.125` | `0.125` | `0.125` | `0.13` | `0.125` |
| `9.9996` | `9.9996` | `9.9996` | `9.9996` | `10.00` | `9.9996` |
| `-0.004` | `-0.004` | `-0.004` | `-0.004` | `-0.00` | `-0.004` |

A fixed number of places is written by setting BOTH to the same value — 2 and 2 for money:

```c#
var money = new RunOptions { MinDecimalPlaces = 2, MaxDecimalPlaces = 2 };
KatLangEngine.Run("19.99 * 3, 1200, 1 / 7", money).ToDisplayString();   // 59.97, 1200.00, 0.14 (one per line)

var atMost3 = new RunOptions { MaxDecimalPlaces = 3 };
KatLangEngine.Run("1 / 7", atMost3).ToDisplayString();                        // 0.143: the host maximum alone
KatLangEngine.Run("MaxDecimalPlaces = 6\n1 / 7", atMost3).ToDisplayString(); // 0.143: min(6, 3)
KatLangEngine.Run("MaxDecimalPlaces = 2\n1 / 7", atMost3).ToDisplayString(); // 0.14:  min(2, 3)
KatLangEngine.Run("MaxDecimalPlaces = 6\n1 / 7").ToDisplayString();          // 0.142857: the source maximum alone
KatLangEngine.Run("MinDecimalPlaces = 2\n10, 1 / 8", atMost3).ToDisplayString(); // 10.00, 0.125: source minimum, host maximum
```

**Consistency.** An effective minimum above the effective maximum is an error; it is never repaired by clamping, swapping, or dropping a value. Where it is reported depends on where the conflict is:

| Case | Reported as |
|---|---|
| Two CLI options that contradict each other (`--min-decimal-places 5 --max-decimal-places 3`) | a usage error at command-line parsing, before the source is read |
| `RunOptions.MinDecimalPlaces` above `RunOptions.MaxDecimalPlaces` | `ArgumentException` from `KatLangEngine.Run` / `RunAsync` before parsing or evaluation — never a source diagnostic |
| A program's own pair (`MinDecimalPlaces = 5` with `MaxDecimalPlaces = 3`) | `RunResult.EvalFailure`, `IllegalInEval`, whatever the host settings are |
| A conflict only across origins (a program declaring only `MinDecimalPlaces = 4`, run with only a host maximum of 2) | `RunResult.EvalFailure`, `IllegalInEval`, naming both values and where each came from, positioned at the program's declaration |

Two complete, self-consistent pairs never conflict, so the last row arises only from PARTIAL settings. `RunOptions` checks each value's range (0 through 99, `RunOptions.DecimalPlacesLimit`) when the options object is initialized and throws `ArgumentOutOfRangeException` — values are rejected, never clamped — while the PAIR is checked where a run begins, so the order in which the two properties are initialized never matters.

`null` (or no CLI option) means NO host setting — never zero places, and never a reason to ignore the program's own; `0` is a real setting, and so is `99`: any present setting selects the value-based display above, so `--min-decimal-places 0` shows `2.5000` as `2.5` where no option shows `2.5000`. The source settings are read by `KatLangEngine` (and so by the CLI and hosts built on it), never by the raw `Evaluator.Run*`: after the program's output has succeeded, the engine performs one ordinary zero-parameter read of the root's own `MinDecimalPlaces` and then one of its `MaxDecimalPlaces`, in the same run — same budget, random stream, property cache, host operations and cancellation token — whatever the host settings are. Those reads are evaluation: each can trace, draw, spend steps, be cancelled, or fail (a failing first read stops the run before the second), and an invalid value (`MaxDecimalPlaces = -1`, `100`, `1.5`, `1 / 0`) fails the run with its own diagnostic whatever the host supplies. Only the root's own declaration is a setting; a nested, opened, member, module or parameter `MinDecimalPlaces` / `MaxDecimalPlaces` is an ordinary binding. A host setting is display-only host configuration, not a KatLang property — nothing is added to the program, so name resolution, diagnostics, and editor tooling see the source as written — and it is never evaluated: it consumes no evaluation budget, draws no random value, invokes no host operation, and changes no value, atom, comparison, or control flow. Every rendering surface of the result uses the same effective pair with the same rounding, special-value spellings, and display-length bound: `ToDisplayString`, `RenderDisplay`, and the `exact`/`readable`/`concise` and custom formatters.

A host whose display setting changes after a run does not have to run the program again: `RunResult.WithHostDecimalPlaces(min, max)` replaces both host settings of a completed result without evaluating anything and returns what a run made with them would have returned — a `Success` that shares the root, value, atoms and output rows, or the `EvalFailure` above when the new effective pair conflicts (every other result is returned unchanged). Keep the original `Success` and re-apply from it:

```c#
var completed = KatLangEngine.Run("MinDecimalPlaces = 2\n19.99 * 3, 1 / 7");
completed.WithHostDecimalPlaces(null, 4).ToDisplayString();   // 59.97, 0.1429
completed.WithHostDecimalPlaces(null, 2).ToDisplayString();   // 59.97, 0.14
var conflict = completed.WithHostDecimalPlaces(null, 1) is RunResult.EvalFailure; // true: the program's minimum 2 exceeds the host maximum 1
```

## Observing intermediate property values

A host that wants to show the intermediate results of a calculation — a calculator's or an editor's "Price = 200, VAT = 42" panel — sets `RunOptions.ObservePropertyValues`. The run then also returns, as `RunResult.PropertyObservations`, the values its ordinary evaluation PUBLISHED for the program's root properties, in the order it published them, each with the property's name and declaration span:

```c#
var source = "Price = 200\nVAT = Price * 0.21\nTotal = Price + VAT\nUnused = 6 * 7\nTotal";
var result = KatLangEngine.Run(source, new RunOptions { ObservePropertyValues = true });
foreach (var observation in result.PropertyObservations ?? Enumerable.Empty<PropertyValueObservation>())
{
    var text = observation.Status == PropertyValueStatus.Available
        ? result.RenderPropertyValue(observation).Text   // decimal places and length bound of the run
        : "(not displayable)";                           // Withheld values have no public snapshot
    Console.WriteLine($"{observation.Name} {observation.DeclarationSpan}: {text}");
}
// Price [1:1, 1:6): 200
// VAT [2:1, 2:4): 42.00
// Total [3:1, 3:6): 242.00
```

Observation is passive: it never evaluates anything, so `Unused` is not calculated and has no entry, and values, errors, evaluation order, host operations, random draws, resource accounting and cancellation are exactly those of the same run without it. An entry is the value the run's zero-parameter property cache published — the property's outermost successful read, or an explicit zero-argument call such as `A()` that ran before any read and so established the value every later read reused; a later explicit call is fresh and adds no entry, and re-entrant evaluations, nested and imported declarations are not observed. The snapshot is therefore not a calculation history, and a property without an entry must not be shown as "never calculated". A failed run (`RunResult.EvalFailure`) still carries what was published before it failed; a `ParseFailure` and a run without the option carry `null`; cancellation propagates as before. A value containing a run-internal call reference is `Withheld` and exposes no value. A lazy list can be shown once its length is settled and every position has a completed, export-safe value, even if the program selected the positions one at a time. An empty list with a settled length can be shown immediately. An unsettled `filter`, an unread or failed position, or a cycle keeps the observation `Withheld`. The declaration spans are coordinates in the source that run evaluated: correlating them with an editor's document version is the host's job, for example through `SemanticModel.FindResolutionAt` on the same text. The snapshot is ancillary data and takes no part in `RunResult` equality.

## Code links

A code link carries a KatLang program in a katlang.org URL, `https://katlang.org/#<format>/<payload>`: opening it shows the program in the KatLang Playground and runs it there. The link holds the source itself, compressed, in the URL fragment, so nothing is stored on a server or sent to one, and anyone who has the link can read the program. `KatLang.CodeLink` makes and reads these links in .NET, with no JavaScript and no dependency:

```c#
using KatLang;

// Making a link.
var text = CodeLink.Encode("100 - 3 * 5 ^ 2") switch
{
    CodeLinkEncoding.Link link => link.Url,   // https://katlang.org/#1/4MWjDBlNE4PH
    CodeLinkEncoding.EmptyProgram => "There is no program to link.",
    CodeLinkEncoding.SourceTooLong tooLong => $"The program is {tooLong.SourceLength} code units long.",
    CodeLinkEncoding.PayloadTooLong tooLong => $"The link's payload would be {tooLong.PayloadLength} characters long.",
};
Console.WriteLine(text);

// Reading one, with every check a reader makes before it opens a link.
switch (CodeLink.DecodeLink("https://katlang.org/#1/4MWjDBlNE4PH"))
{
    case CodeLinkDecoding.Program program:
        Console.WriteLine(program.Source);    // 100 - 3 * 5 ^ 2
        break;
    case CodeLinkDecoding.Refused refused:
        Console.Error.WriteLine($"Not a usable code link: {refused.Reason}.");
        break;
}
```

- **`CodeLink.Encode(source)`** returns a `CodeLinkEncoding`: a `Link` with its `Format` (`CodeLink.CurrentFormat`, 1), `Payload`, `Fragment` and `Url`, or the reason the program has no link. That is `EmptyProgram`, `SourceTooLong` (over `CodeLink.MaxSourceLength`, 20,000 UTF-16 code units; such a program is not encoded) or `PayloadTooLong` (over `CodeLink.MaxPayloadLength`, 1,970 characters, which keeps a link under 2,000 characters). The source is encoded exactly as given, as UTF-16 code units, with nothing normalized: line breaks, tabs, trailing spaces and unpaired surrogates are part of the program. `Url` is the link on `CodeLink.CanonicalBaseUrl`; a site on another origin appends `#` and the `Fragment` (`1/<payload>`) to its own base URL.
- **`CodeLink.DecodeLink(link)`** and **`CodeLink.Decode(format, payload)`** return a `CodeLinkDecoding`: a `Program` with its `Source`, exactly as the link carries it, or `Refused` with a `CodeLinkRefusal`, the first check that failed. The link's fragment must be a format number, `/` and the payload (`NotACodeLink` otherwise, as for links in the earlier `#code/` format); the format must be one this KatLang reads (`UnsupportedVersion`: a link from a newer KatLang, or a changed one); the payload must not be empty or longer than the limit (`EmptyPayload`, `PayloadTooLong`); it may hold only the characters a payload uses, and nothing is percent-decoded or trimmed, because no payload character ever needs it (`InvalidCharacter`); it must decode to a program within the source limit whose check value matches (`Damaged`, `SourceTooLong`); and that program must encode back to the same payload in that format (`NotCanonical`).
- **`CodeLink.TryGetPayload(link, out format, out payload)`** reads a link's format number and payload without decoding it, and is `false` for a link that is not a code link. It reads only the fragment: which origins, paths and queries may carry a code link is the host's own route policy.

The payload is KatLang's own code-link format, specified in [`docs/design/code-link-format.md`](design/code-link-format.md). The number before it names the format (`1`); the payload carries the compressed program and a 12-bit checksum in the URL-safe alphabet `A–Z a–z 0–9 - _`. The compression model starts with KatLang's vocabulary and tutorial examples. The checksum and canonical encoding detect many copying errors, although an edit can produce a valid link to a different program. For `100 - 3 * 5 ^ 2`, the payload takes 12 characters, down from 24 with lz-string. A new format is introduced only by the owner's decision. It gets the next number, `Encode` writes it, and readers keep opening links in every earlier format.

Decoding is bounded whatever the payload: the work is linear in the program length the stream announces, which may not exceed 60,000 bytes, and reading stops at the first byte that cannot belong to a link. Both results are C# `closed` hierarchies produced only by the library, like `RunResult`. A code link is a host and tooling format, not KatLang syntax: nothing here parses or runs a program, and a decoded program is input like any other, to be run with the limits you would give any program you did not write.
