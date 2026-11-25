# KatLang conformance cases

Author shared language regressions in [features/](features/). The .NET test suite reads these JSON files directly. Lean checks the same expectations for programs its model covers. A Rust runner can read the files with a JSON parser and run the same programs independently of .NET.

## Adding a case

Add one object to the array in the relevant feature file. Give it a unique, stable kebab-case `id` and a `category` from the [manifest](cases.json). Write the complete program in `source` and explain the intended behavior in `explanation`. Take the expectations from the language rule. A new feature file also needs an entry in the manifest's `files` array. CI checks that every feature file is listed exactly once.

For example, [spread-and-empty-values.json](features/spread-and-empty-values.json) contains this regression. Spreading the empty sequence supplies zero arguments to a function that requires one.

```json
{
  "id": "fixed-empty-spread-zero-items",
  "category": "empty-visible-vs-spread",
  "source": "F(a) = a\nF(()*)",
  "outcome": "EvalError",
  "expectedErrorCategory": "arity",
  "expectedErrorPayload": { "kind": "arity", "names": [], "counts": [1, 0] },
  "includeInGeneratorPrompt": true,
  "explanation": "Spreading `()` contributes zero items, so `F(()*)` supplies no arguments and the one-parameter call fails."
}
```

## Running the cases

Read `cases.json` as UTF-8. In schema version 3, `files` lists JSON paths relative to the manifest. Read each array in the listed order. Run every case and each of its probes as a fresh, standalone program with the default settings. Report failures by case ID and, for a probe, its zero-based index.

| Outcome | Required comparison |
| --- | --- |
| `Evaluates` | Parse and evaluate successfully. Compare `expectedRaw` (the result structure) and `expectedEmittedCount` (the number of top-level items emitted). Then apply any `displayChecks` to the completed result. |
| `EvalError` | Parse successfully, then compare the innermost evaluation error with `expectedErrorCategory`. When present, also compare `expectedErrorPayload.kind` and the ordered `names` and `counts` arrays. For `arity`, the counts give the expected or minimum cardinality followed by the supplied count. |
| `ParseError` | The front end rejects the source. Require at least one error diagnostic with `expectedDiagnosticCode`. When `expectedParseDiagnosticFragment` is present, also require a diagnostic message containing that exact substring. |

In raw results, numbers use invariant text, Booleans use `true` or `false`, and strings carry single quotes. `S[...]` represents a sequence and `L[...]` a list, with items separated by a comma and a space. For example, `take-single-survivor` produces `L[S[1, 2]]` and emits one item.

### Checking display after evaluation

Omit `displayChecks` for an evaluation-only case. To check formatting, render the same completed result for each entry and compare its `text` with LF between output rows. Each entry supplies its own host settings. An omitted or null `minDecimalPlaces` or `maxDecimalPlaces` leaves that host setting unset. The program's own decimal-place settings still apply. Include at most one check per settings pair.

For example, [division-decimal-quotient](features/decimal-arithmetic.json) evaluates `1 / 3` once. Its display checks include `{"maxDecimalPlaces": 2, "text": "0.33"}` and `{"maxDecimalPlaces": 4, "text": "0.3333"}`. Both renderings use the same full-precision value.

A check containing only `text` verifies output with default host settings. Include one for every successful case linked to the tutorial or selected for the generator prompts, so the published example has an explicit expected result.

### Other observations

Optional expectations apply wherever they appear:

- Each `probes` entry contains a `source` program and an `expectedNeutral` string. Compare the observed result as `ok raw=<raw> n=<emitted count>` or `err <category>`.
- `expectedCachePublications` maps case-sensitive binding names to the number of entries published by the completed run, including runs that end in an evaluation error. Check the counts and their total. A zero watches an unpublished name, an empty object requires zero publications, and an absent field requests no cache observation.

`notes` provides maintainer context. `includeInGeneratorPrompt` selects examples for the two generator prompts. `leanExclusionReason` explains a limit of the Lean comparison. Surface runners still execute those cases, including decimal arithmetic and parser diagnostics. The .NET adapter derives Lean inputs from the elaborated source. Any exceptional `leanProgramOverride` requires a `leanOverrideReason`.

From the repository root, the focused .NET check is:

```powershell
dotnet test ./dotnet/tests/KatLang.Tests/KatLang.Tests.csproj --filter "FullyQualifiedName~LanguageSpecRunnerTests|FullyQualifiedName~PortableConformanceTests"
```

When a shared case changes, review and regenerate its affected Lean and documentation artifacts using the [validation guide](../docs/testing-and-validation.md#regenerating-generated-artifacts). The [executable specification guide](../docs/design/executable-language-spec.md) describes each consumer.
