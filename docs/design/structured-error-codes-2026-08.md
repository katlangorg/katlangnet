# Structured error codes at the engine/host boundary (M5, v0.8.186)

Architecture-review finding M5: structured error identity was erased at the
public facade — `KatLangError.FromEvalError` rendered the structured
`EvalError` to prose and discarded the record, and `Diagnostic` exposed only
message, severity, and span — so hosts (and many tests) classified failures by
English message substrings. This change makes classification a stable,
machine-readable contract. It is purely additive host metadata: no message,
severity, span, recovery, evaluation-semantics, or Lean change.

## The host contract

A host classifies every library-produced error without examining `Message`:

```csharp
var result = KatLangEngine.Run(source, options);
if (result is RunResult.EvalFailure failure)
{
    var error = failure.Errors[0];
    if (error.IsResourceLimit)
    {
        // Which limit? The per-kind code names it.
        Report(error.Code); // e.g. KatLangErrorCode.EvaluationStepLimitExceeded
    }
    else if (error.Code == KatLangErrorCode.UnknownName)
    {
        // A program error the user can fix; error.Source is the original
        // structured EvalError (context wrappers included) when more detail
        // than the family is needed.
    }
}
else if (result is RunResult.ParseFailure parseFailure)
{
    // Front-end errors carry the same-named facade code as the diagnostic
    // family; Source is null for them.
    var loadProblem = parseFailure.Errors.Any(
        e => e.Code is KatLangErrorCode.LoadFetchFailed or KatLangErrorCode.InvalidLoadedSource);
}
```

`Message` stays the human-readable rendering and is NOT the classification API.

## Public surface added

- `enum DiagnosticCode` — one value per front-end diagnostic family (lexical,
  syntax, declarations, open declarations/targets/forms, clause-family
  consistency, grace/collect markers, spread placement, the `if` arity gate,
  undeclared identifiers, structural preflight, source-processing limits,
  module loading, internal invariants). `Unspecified = 0` is reserved for
  externally constructed diagnostics.
- `Diagnostic.Code : DiagnosticCode` — init-only, NOT positional. The
  positional constructor and `Deconstruct` shapes are unchanged, so existing
  external construction keeps compiling. The code deliberately participates in
  record equality/hashing and the synthesized `ToString`, and `with` copies
  preserve it (pinned by `DiagnosticCodeTests`).
- `enum KatLangErrorCode` — the unified facade classification covering both
  evaluation families and front-end families (shared families such as
  `BadOpenForm`, `ArityMismatch`, `DuplicateProperty`, `BranchArityMismatch`,
  `AstDepthLimitExceeded` appear once).
- `KatLangError.Code : KatLangErrorCode`, `KatLangError.Source : EvalError?`,
  `KatLangError.IsResourceLimit : bool`.
- `EvalError.Code : KatLangErrorCode` — the one authoritative variant→family
  mapping (fail-loud on an unmapped future variant: since September 2026 a
  compile error, the switch being exhaustive over the closed `EvalError`).
- `EvalError.IsResourceLimit` — the pre-existing internal classifier promoted
  to public, semantics unchanged.

`Source` is reference-preserving, not a deep-freezing adapter. It exposes the
same already-public `EvalError` object returned by the evaluator API, including
the pre-existing backing identity of any `IReadOnlyList<T>` payload supplied to
that error. It exposes no host exception or private loader/cache object, and no
active run state depends on a returned error after projection.

## Mapping rules

- **Evaluation errors.** `EvalError.Code` maps every concrete variant; the only
  deliberate grouping is `ArityMismatch` ∪ `VariadicArityMismatch` ∪
  `BadArity` → `KatLangErrorCode.ArityMismatch` (one host-facing
  "supplied items don't fit the shape" family, still distinguishable through
  `Source`). `WithContext` wrappers resolve to the innermost error's family, so
  common classification never unwraps; `Source` preserves the full wrapped
  chain by reference. The mapping is pinned reflection-complete by
  `KatLangErrorCodeTests` — a new `EvalError` variant fails the suite until it
  gets an explicit mapping decision.
- **Front-end diagnostics.** `KatLangError.FromDiagnostic` maps
  `Diagnostic.Code` name-preservingly onto `KatLangErrorCode` (mechanically
  pinned over the whole enum). `Unspecified` and undeclared numeric values map
  to `KatLangErrorCode.Unspecified` — the explicit compatibility state for
  host-created diagnostics. A declared future family with no explicit facade
  mapping fails loudly. KatLang-produced diagnostics never carry it: the
  reporting funnels take the code as a required parameter, and the family
  corpus in `DiagnosticCodeTests` sweeps representative sources for every
  source-reachable family.
- **Resource limits.** The classified set is exactly the nine evaluation
  resource-limit families (runtime depth, steps, stack headroom, per-collection
  and cumulative items, per-string and cumulative string units, display,
  weighted structural AST depth at the evaluation gates). `AstCycleDetected` is
  malformed host input, not a limit. Front-end source-processing limits are
  diagnostics, never evaluation outcomes, so they are not `IsResourceLimit`
  (unchanged from the internal classifier). **Cancellation is not a resource
  limit and not an error value at all**: a cancelled run throws
  `OperationCanceledException`, per the established cancellation contract.
- **Distinct parser budgets.** `NestingTooDeep` (the cumulative weighted
  budget, which carries module-loader stack debt) and `ExpressionChainTooDeep`
  (the per-chain operator budget) are separate families because the module
  loader treats only the former as a position-dependent nesting rejection.

## Stability expectations

Enum member names AND numeric values are stable public contract: never
renumbered, renamed, or removed; new families are appended. Hosts may persist
the numeric values. Both value tables are pinned by
`KatLangErrorCodeTests.DiagnosticCodeValues_AreStable` /
`KatLangErrorCodeValues_AreStable`.

Only KatLang-produced diagnostics and errors are guaranteed a non-default
code; externally constructed diagnostics (and errors projected from them)
legitimately carry `Unspecified`.

## Compatibility

The additions are ABI-compatible and preserve the existing positional
`Diagnostic` constructor and three-component `Deconstruct`, so existing source
using those shapes continues to compile. They are not behaviorally invisible:
because `Code` is an init-only property on a record, it participates in
`Diagnostic` equality and hashing, and the synthesized `ToString()` now prints
the code. Reflection and serializers also see the new public property. Those
changes are deliberate—the code is semantic identity—but release notes must not
describe record equality, hashing, `ToString()`, reflection, or serialization
behavior as unchanged.

## Metadata survival

The code travels intact through: lexer→parser diagnostic seeding, front-end
aggregation, the module loader's `[while loading …]` re-wrap (presentation
prefix only; the code is copied), `KatLangError.FromDiagnostic` /
`FromEvalError`, `RunResult` variants (including `NoProgramOutput.Diagnostic`),
and the sync/async engine paths (pinned by an async/sync classification-parity
test). The loader's nested-parse triage (`HasStructuralBudgetDiagnostic`) now
classifies by structured codes instead of message substrings — the one
pre-existing production message classification, migrated with byte-identical
output.

## Executable specification

`SpecCase.ExpectedDiagnosticCode` pins the structured family of every
parse-error spec case (schema-required for `SpecOutcome.ParseError`, so new
cases cannot regress to message-only expectations). The existing
`ExpectedParseDiagnosticFragment` assertions are retained unchanged. No
generated artifact changes: parse-error cases are C#-only (Lean has no surface
parser) and the generator blocks do not emit the code field.

## Downstream adoption (not in this change)

- **KatLang.CLI** consumes the published package (`KatLangVersion` 0.8.181)
  and performs no message-based classification today (it branches on
  `RunResult` variants). When it next adopts a package ≥ 0.8.186 it can use
  `KatLangError.Code` / `IsResourceLimit` for a finer exit-code taxonomy if
  one is ever wanted.
- **KatLangWeb** (`KatLang.Api`) can replace its limit-kind message matching
  with `error.IsResourceLimit` + a switch over `error.Code` (per-limit-kind
  codes exist precisely so hosts can report which limit was hit), and classify
  load failures via the `Load*`/`InvalidLoadedSource` families.

## What deliberately did not change

Message wording, punctuation, and formatting; spans; severities (every
KatLang-produced diagnostic remains `Error`); context stamping; parser
recovery; CLI output and exit codes; evaluation semantics; Lean. The legacy
prose-context formatting branches inside `KatLangError` (reachable only via
host-constructed `EvalError.WithContext(string, …)` values) remain as
rendering compatibility, not classification. (Since September 2026 that string
constructor — a `TextErrorContext` — is also the ONE host channel for attaching
context: `ErrorContext` is a `closed` hierarchy, so a host constructs the
built-in structured contexts or free text, never a context type of its own.)
The ~288 existing message-substring
test assertions continue to pass and continue protecting wording; migrating
them to codes is deliberate follow-up work, not part of M5.

### Host prose contexts (retained compatibility, re-verified 2026-11-15)

- **Arbitrary text** in a `TextErrorContext` remains supported host context.
  The ordinary fallback is `{text}: {inner message}`; tailored error shapes can
  take precedence. Text never changes the code.
- **Three prose shapes are special.** `KatLangError.FromEvalError` (and so
  `ToTerminalSafeString`) recognizes text that starts exactly with
  `while evaluating property `, `while evaluating call to ` or
  `while evaluating dotCall .` (then `{member} of {receiver}`). For these it
  uses the same per-shape message builders as structured contexts. This covers
  an immediate inner missing output or arity mismatch, and dot-call unknown name
  when the missing name matches the member. For example,
  `WithContext("while evaluating call to F", new MissingOutput())` renders
  `Cannot call 'F' because it has no defined output.` followed by the output hint.
- **Evaluator production appears migrated to structured contexts.** The current
  source search found no evaluator producer of these prefixes as text. Runs use
  structured `PropertyEvaluationContext`, `CallContext` and `DotCallContext`. The
  evaluator's own text contexts (map/reduce/filter callbacks, empty-collection
  selection, sequence metadata, binary operands, meta binding) use other text.
  The inherited 2026-11-15 probe recorded only test callers constructing these
  frames. That intentionally failing run (some chain tests caught the probe
  exceptions) and the source search are evidence, not a proof over all programs
  or green validation. The route remains live: public
  `EvalError.WithContext(string, …)` / `TextErrorContext(string)` plus public
  `FromEvalError` reach it, and `KatLangErrorLegacyContextTests` pins it.
- **The two forms are not interchangeable for every inner error.** Structured
  call rendering requires `Evaluator.IsOwnForBlame`; dot-call rendering requires
  that or the `.string` intrinsic case (`string` with `IsSelectedMemberOutput`
  false). The legacy arms skip the blame gate and the legacy dot-call arm passes
  `isSelectedMemberOutput: false`; neither fact is recovered from prose. A
  run-produced nested missing output under call or non-intrinsic dot-call prose
  still names the callee or member, where the structured frame renders
  `{context}: Algorithm has no defined output.` followed by the output hint.
  A selected member named `string` under `.string` prose gets the intrinsic's receiver-only
  wording, where the structured frame names the member.
- **Signature checks do not guard this.** The recognizers are private and change
  only message text, so `PublicApiBaseline.txt` would not change if they were
  removed or altered. The rendering tests are the guard. Retiring the route would
  be a release-noted public behaviour change, not a dead-code cleanup.
