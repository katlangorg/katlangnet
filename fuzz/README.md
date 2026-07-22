# KatLang parser fuzzing

Coverage-guided fuzzing harness for the **raw** KatLang parser, targeting:

```csharp
Parser.ParseSyntax(source)   // the raw syntax boundary, before front-end elaboration
```

## Targets (`KATLANG_FUZZ_MODE`)

One harness, several targets. The environment variable selects which one the libFuzzer loop
drives; every target has a matching deterministic replay subcommand.

| `KATLANG_FUZZ_MODE` | Target | Replay subcommand |
|---|---|---|
| *(unset)* | `Parser.ParseSyntax` — the raw parser | *(paths only)* |
| `frontend` | `FrontEndPipeline.Process` — the elaborated front end | `frontend-replay` |
| `evaluator` | the terminating evaluator subset | `evaluator-replay` |
| `metamorphic` | trusted program **pairs** under a declared relation | `metamorphic-replay` |

The first three feed arbitrary bytes to the language as source text. The fourth does not —
see [Operational-metamorphic fuzzing](#operational-metamorphic-fuzzing).

`ParseSyntax` is the target because it is the pure parser: it does **not** run load
elaboration, parameter detection, implicit-argument resolution, evaluation, or any
network path. We deliberately do not fuzz `Parser.Parse` (which adds the front end),
the evaluator, or module loading.

The harness uses [SharpFuzz](https://github.com/Metalnem/sharpfuzz) (2.3.0) with the
libFuzzer engine via the `libfuzzer-dotnet` fork-server driver.

## Layout

```
fuzz/
  KatLang.ParserFuzz/
    KatLang.ParserFuzz.csproj   # standalone harness; NOT in KatLang.slnx
    Program.cs                  # libFuzzer entry point + byte->source decoding
    FuzzInvariants.cs           # the three post-parse invariants
    Replay.cs                   # deterministic replay mode (no fuzzing loop)
    Testcases/                  # tracked seed corpus (many tiny inputs)
    Metamorphic/                # operational-metamorphic target (case model, relations,
                                #   decoder, templates, executor, comparator, replay)
    MetamorphicTestcases/       # tracked metamorphic seeds (template payloads, not sources)
  katlang.dict                  # libFuzzer dictionary of KatLang fragments
  run-campaign.sh               # WSL-side: build driver + run libFuzzer
  README.md                     # this file
  artifacts/                    # gitignored: publish output, corpus, crashes, logs
scripts/
  fuzz-parser.ps1               # Windows-side orchestration (publish + instrument + run)
```

The harness project stays outside `KatLang.slnx`, with one deliberate exception: the
self-contained `Metamorphic/` folder is compiled into `tests/KatLang.Tests` as shared source
(`<Compile Include="..\..\fuzz\KatLang.ParserFuzz\Metamorphic\*.cs" />`), so
`MetamorphicFuzzHarnessTests` exercises exactly the decoder, template, executor, comparator,
and replay driver the campaign runs instead of a second copy. Nothing else in `fuzz/` is part
of normal validation.

## Invariants

After every parse the harness asserts three properties (a violation throws and is
recorded as a crash). Ordinary parser **diagnostics are expected and are not failures** —
the harness never asserts that malformed input is rejected.

1. **Diagnostic spans are well-formed and in bounds.** Every diagnostic span has
   line/column `>= 1`, an end not preceding its start, a line within the source, and a
   column within the line's width (allowing the one-past-end EOF position). The check
   reproduces the lexer's exact bookkeeping: a line boundary is `\n` only, `\r` is
   transparent, and every other character advances the column by one — so CRLF,
   lone-CR, empty input, and EOF spans do not produce false positives.
2. **AST traversal is total and terminates.** The full raw AST (every algorithm,
   property, branch, pattern, expression, and nested block) is walked via the shared
   `AstWalker`, without assuming the program is semantically valid.
3. **No forbidden internal node.** The surface parser must never produce
   `Expr.SequenceConstruct` — an internal-only sequence-join node with zero legal
   surface origin sites (see `AGENTS.md` and `Ast.cs`).

## Prerequisites

* **.NET 10 SDK** on Windows (to publish/instrument the harness).
* A **WSL distro with `clang`** (e.g. Ubuntu). WSL runs the actual libFuzzer campaign.
* Internet access on first run, to fetch the `libfuzzer-dotnet` driver source and, if
  missing, the `sharpfuzz` tool.

### Why WSL?

libFuzzer needs the native `libfuzzer-dotnet` driver, which is built with
`clang -fsanitize=fuzzer`. This machine has no native Windows clang, but its WSL Ubuntu
already has clang. To avoid needing .NET inside WSL, the harness is **cross-published
self-contained for `linux-x64`** on the Windows side (it bundles the .NET 10 runtime),
so WSL only builds the tiny C driver and runs the campaign.

## Running a campaign

From the repo root (Windows PowerShell 5.1):

```powershell
powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1
```

Defaults match the standard bounded campaign: `-MaxTotalTime 600` (10 min),
`-MaxLen 16384` (16 KiB), `-Timeout 5` (per input), `-RssLimitMb 2048` (~2 GiB).
Useful switches: `-FreshCorpus` (clear the writable corpus first), `-SkipBuild` (reuse
an existing publish + instrumentation), `-Distro <name>` (pin a WSL distro).

The script:

1. `dotnet publish` the harness self-contained for `linux-x64` into
   `fuzz/artifacts/publish-linux`.
2. Instruments `KatLang.dll` with the `sharpfuzz` global tool (installs it if missing).
3. Runs `fuzz/run-campaign.sh` in WSL, which builds/caches the `libfuzzer-dotnet` driver
   and launches libFuzzer with the seed corpus + dictionary.

New coverage-increasing inputs land in `fuzz/artifacts/corpus` (the writable corpus);
the tracked `Testcases/` seeds are read-only. Crash/timeout artifacts are written to
`fuzz/artifacts/crashes/`. Everything under `fuzz/artifacts/` is gitignored.

### Manual / Linux-native equivalent

If you already have a Linux box with .NET 10 + clang, publish + instrument there and run
the driver directly:

```bash
dotnet publish fuzz/KatLang.ParserFuzz -c Release -r linux-x64 --self-contained -o out
sharpfuzz out/KatLang.dll
# build the driver once:
curl -fsSL https://raw.githubusercontent.com/Metalnem/libfuzzer-dotnet/master/libfuzzer-dotnet.cc -o d.cc
clang -fsanitize=fuzzer d.cc -o libfuzzer-dotnet
./libfuzzer-dotnet --target_path=out/KatLang.ParserFuzz \
  -max_len=16384 -timeout=5 -rss_limit_mb=2048 -max_total_time=600 \
  -dict=fuzz/katlang.dict -artifact_prefix=crashes/ -print_final_stats=1 \
  corpus fuzz/KatLang.ParserFuzz/Testcases
```

## Reproducing a finding (no fuzzing loop)

The harness has a deterministic **replay mode**: pass one or more files/directories and
it parses each once with the invariants enabled and no fuzzing engine. This is the
triage reproducer and a cross-platform smoke test that works on plain Windows .NET 10:

```powershell
# replay the whole seed corpus (expect: "0 failure(s)")
dotnet run --project fuzz\KatLang.ParserFuzz -- fuzz\KatLang.ParserFuzz\Testcases

# replay recorded crash artifacts
dotnet run --project fuzz\KatLang.ParserFuzz -- fuzz\artifacts\crashes
```

Minimize a crashing input with libFuzzer before triaging:

```bash
./libfuzzer-dotnet --target_path=out/KatLang.ParserFuzz -minimize_crash=1 \
  -exact_artifact_path=min -runs=100000 crashes/crash-<hash>
```

## Seed corpus & dictionary

`Testcases/` holds many tiny inputs — both valid and intentionally invalid — spanning
every grammar area: numbers (decimals, exponents, digit separators, malformed forms),
strings (incl. unterminated and Unicode), identifiers, operators and precedence,
parentheses/braces/exact-list brackets and their empty/nested forms, comma vs adjacency,
newline/CRLF/lone-CR boundaries, comments, property/`public`/`Output =` definitions,
ordinary and conditional clause definitions, calls/brace-calls, dot-calls and
leading-dot continuation, `open` declarations, `:` indexing, `~` grace, `...` spread,
deconstruction and movable-rest patterns, and malformed delimiter/semicolon/unexpected-
character mixtures. Keep new seeds small and reviewable; do not commit generated corpora
(they belong in `fuzz/artifacts/corpus`).

`katlang.dict` lists KatLang keywords, operator spellings, paired delimiters, and a few
common definition/call/open shapes so the mutator can reach deeper grammar states.

## Depth-limit probing (`DepthProbe.cs`)

A process-isolated depth probe characterizes the parser's recursion boundaries per
grammar family (parentheses, lists, braces, mixed delimiters, calls, prefix `-`/`not`,
right-associative `^`, clause-head patterns, and malformed/unclosed variants). Because a
deep parse can trigger an uncatchable `StackOverflowException`, the dangerous parse runs
in a **child** process; a **parent** coordinator uses exponential + binary search to find
each family's boundary and records results under `fuzz/artifacts/depth-probe/`. Running
each family in `parser`-only vs `parser+invariants` mode isolates a genuine parser
overflow from an AST-walker overflow.

```powershell
# characterize on Windows (writes depth-probe-windows.json + a table)
dotnet run --project fuzz\KatLang.ParserFuzz -- probe --out fuzz\artifacts\depth-probe\depth-probe-windows.json --platform windows
# a single isolated parse (child mode): FAMILY DEPTH MODE MAXBYTES
dotnet run --project fuzz\KatLang.ParserFuzz -- probe-child paren 5000 invariants 4000000
```

Cross-platform (Linux) probing runs the self-contained publish under WSL (see
`scripts/fuzz-parser.ps1` for the publish step, then invoke the apphost's `probe`
subcommand). The parser now bounds recursion via `Parser.MaxNestingDepth`, so every
family is `success-through` (a structured "nesting is too deep" diagnostic, never a
crash) on both platforms.

The **near-boundary** campaign fuzzes around the recursion limit with generated
(untracked) seeds at depths near `Parser.MaxNestingDepth` plus a larger `-max_len`
(e.g. 64 KiB); the nesting diagnostic is an ordinary result, not a crash. Seeds live in
`fuzz/artifacts/nearboundary-seeds/` and are not tracked.

## Operational-metamorphic fuzzing

`KATLANG_FUZZ_MODE=metamorphic` (source: `KatLang.ParserFuzz/Metamorphic/`).

### What it is, and how it differs from evaluator fuzzing

The raw, frontend, and evaluator targets take one arbitrary byte string, treat it as KatLang
source, and assert *properties of a single run* (no crash, well-formed spans, plain/counted
agreement). They can only find defects that make one program misbehave visibly on its own.

The metamorphic target asks a different question: **do two programs that must mean the same
thing also behave the same way, and cost the same?** That catches a class the single-run
targets structurally cannot — a form that computes the right answer while charging the wrong
amount of work, or that crosses a resource boundary its equivalent form does not. (The
duplicate dotted-receiver materialization recorded in `SEMANTIC-ALIGNMENT.md` is exactly that
shape: correct values, doubled item accounting.)

Consequently the fuzz input is **not a program**. A metamorphic testcase is

```
a trusted template  +  mutation parameters  +  execution policy  +  a declared relation
```

and the bytes only choose the parameters. Equivalence is guaranteed by how the template
*constructs* the pair, never by rewriting an arbitrary mutated program — a textual rewriting
of unknown source would make every mismatch ambiguous between "the language is wrong" and
"the rewriting was not meaning-preserving".

### Registered families

Every family is one entry in `MetamorphicFamilyRegistry`, declaring its stable id, payload
dimensions, supported limit modes, precondition validator, template builder, relations, Lean
representability, and fingerprint features. Nothing dispatches on source text.

| Family id | Group | Left / right |
|---|---|---|
| `dotted-collection-call` | dotted-builtin | `count(range(1, N))` / `range(1, N).count` |
| `dotted-collection-builtin` | dotted-builtin | `F(R, suffix…)` / `R.F(suffix…)` |
| `user-extension-call` | dotted-user | `MmF(R, suffix…)` / `R.MmF(suffix…)` |
| `dotted-chain` | dotted-chain | nested ordinary calls / the equivalent dotted chain |
| `builtin-callback-wrapper` | callback-wrapper | `Rows.map(count)` / `Rows.map(MmWrap)` |
| `optimizer-generic-parity` | optimizer | one source with optimizations **on** / the same source with them **off** |
| `cached-property-reuse` | cache | a reused zero-argument property / the independently rebuilt form |
| `entry-point-parity` | entry-point | one source through **two runtime entry points** |
| `budget-law` | budget | resource-budget laws: boundary sweeps, neutrality, failed reservations, isolation |

The first five compare two *programs*. Phase 3's four compare two *executions*: same program (or two trusted
equivalent programs) under a different optimizer policy, a different entry point, or a different budget. That
is why Phase 3 added a per-side **execution profile** rather than more templates.

**Phase 1 family.** `count(range(1, N))` against `range(1, N).count`. KatLang's `range` is
**inclusive** and counts downward when `start > stop`, so it always yields at least one element:
there is no empty range, `range(1, 1)` is the smallest form, and `range(1, 0)` descends to two
items.

**Group A — dotted collection builtins.** Seventeen builtins whose first fixed parameter is the
receiver (the sixteen `BuiltinRegistry` collection builtins plus `atoms`), crossed with twelve
receiver value shapes covering atoms, strings, sequences, exact lists, the empty sequence, the
empty list, singletons, nested lists, lists of sequences, and sequences of lists. The suffix
dimension covers every suffix kind the table declares:

* **none** — `count`, `sum`, `first`, `last`, `min`, `max`, `avg`, `order`, `orderDesc`,
  `distinct`, `atoms`, written as `F(R)` / `R.F`;
* **whole-number boundary variants** — `take`/`skip` at `0`, `1`, `count-1`, `count`, `count+1`,
  and a negative, each derived from the *receiver's own* item count;
* **value arguments** — `contains` against an atom, a string, an exact list, and the empty
  sequence;
* **callback arguments** — `map`/`filter` with two user callbacks and a builtin-as-callback;
* **reducer plus initial value** — `reduce` with a user reducer at two initial accumulators, and
  with the two-argument `contains` builtin over a list accumulator.

Deliberately **excluded**: `if`/`while`/`repeat` (control flow, not receiver-first) and `range`.
`range` parses and evaluates fine in dotted form — `1.range(5)` is `[1, 2, 3, 4, 5]` — but its
first parameter is a scalar range *bound* rather than a collection, so a `receiver.range(…)` pair
would not be an instance of the Group A receiver contract. It is a different shape, not an
unparsable one.

**Group B — user-defined extension calls.** Eighteen reviewed function bodies (return the
receiver, inspect its count, index into it, wrap it in a list, spread it, call a collection
builtin, emit multiple outputs, return an exact list, return a sequence, chain dotted calls, …)
with zero, one, or two suffix parameters. The receiver is a property bound to a compact
collection construction, so evaluating it twice would be visible as doubled materialization.

**Group C — bounded dotted chains.** Twelve fixed link lists of two or three links. Both members
are generated from the **same ordered link list** — the dotted form appends `.F(suffix)` per
link, the ordinary form wraps `F(inner, suffix)` per link — so the ordinary equivalent is never
recovered by reparsing or rewriting dotted source.

**Group D — builtin callback versus user wrapper.** Consumers `map`, `filter`, and `reduce`
against direct builtin callbacks and equivalent user wrappers, over nine input shapes chosen to
put non-scalar values (nested lists, sequence rows, strings, empty rows) first, because those are
what expose accidental rematerialization.

### Phase 3: comparing two EXECUTIONS of one program

Phase 1 and Phase 2 vary the program and hold the execution fixed. Phase 3 does the opposite. A case
therefore carries a per-side **execution profile** — entry point, limits, optimizer policy — plus a
**run plan** (what, if anything, is interposed between the two observations), an **execution order**,
and an **evidence gate**. Every one of those defaults to the Phase 1/2 value, so a Phase 1 or Phase 2
case is exactly the case it always was: both sides observed through `Evaluator.RunCountedObserved`
under one shared limits instance and one shared optimizer policy, run sequentially, left first, with
no evidence requirement (pinned by
`MetamorphicPhase3FamilyTests.EveryLegacyParameterPoint_KeepsItsExactPrePhase3ExecutionShape`).

#### Group A — optimized versus generic

One trusted source run twice: optimizations **on** as the left member, **off** as the right. Direction
is fixed and recorded (`direction=optimized-left`), so the inequality always reads "left never exceeds
right"; what the payload varies instead is the **execution order**, because a relation that only holds
when a policy runs on a clean process is a state leak rather than an optimization.

**Optimizer-hit proof.** A case is *not* classified as optimizer-versus-generic unless the optimized
run is measured to have taken the intended path. The evidence comes from the runtime's own
`LoopOptimizationDiagnostics` and `SequencePipelineDiagnostics`, attached through two optional
parameters on the internal `Evaluator.RunCountedObserved` — the same channel the internal
`Evaluator.Run` overloads already expose. They are write-only counters incremented through a
null-conditional call, so supplying one cannot change optimizer eligibility, evaluation order, or any
result (pinned by `ObservedExecution_DoesNotChangeSemanticsOrCounters`). No public API changed.

Seven paths are distinguished, and the 28-entry source table exercises all of them:

| Path | Meaning |
|---|---|
| `OptimizedLoopSelected` | a loop plan was selected and entered |
| `PlannedExpressionExecuted` | a planned expression really ran inside that plan |
| `GenericExpressionInsideOptimizedLoop` | the plan was selected but the body fell back per expression |
| `LoopFallbackExecuted` | the optimizer was consulted and declined |
| `GenericLoopExecuted` | the generic loop ran *after* a recorded fallback |
| `LoopShortCircuited` | the loop returned before the optimizer was consulted at all |
| `FusedPipelineExecuted` / `PipelineFallbackExecuted` | sequence-pipeline fusion hit, or fell back |

`LoopShortCircuited` is separate from `GenericLoopExecuted` on purpose: `RepeatLoopCounted` returns the
initial state when the count is zero, *before* the optimizer flag, the shape check, or the state-slot
check are reached, so nothing records a fallback. Collapsing the two would let the zero-iteration
template claim it exercised a fallback it never reached. Proving that an outer loop *wrapper* ran is
explicitly not enough, which is why `LoopExecutions` alone is never a requirement.

**Limit policy.** Only budgets that cannot bind differently on the two sides are generated (`Default`,
`PerCollectionItems`, `Generous`). A cumulative budget derived from the optimized side's own measurement
is below what the generic side legitimately materializes, so the generic run would stop at a limit the
optimized run cleared — a difference in execution policy, not in optimizer setting, and exactly the
false mismatch Phase 2 already documents for fused chains. The per-collection ceiling *is* kept, because
the runtime explicitly promises it is optimizer-independent (`EvaluationBudget.CheckCollectionSize`
exists so a fused pipeline rejects the same collection size a generic one does).

#### Group B — cached versus rebuilt

A program that reuses one zero-argument property against a rebuilt form that binds a *distinct* property
per use. Both are generated from one (value, use) pair and one reuse count, so the rebuilt side is the
cached side with the single binding replicated — deliberately **not** an inlined expression, which would
remove the property-access machinery from one side and make the comparison about something else. The
cached side must record at least `uses - 1` cache hits and the rebuilt side none at all, which turns
"distinct names cannot share an entry" from an argument into a measurement.

One entry in the table is there because it was **measured not to cache**: a bare property reference in an
ordinary call *argument* position (`sum(MmA)`) records no cache request at all, while the same property
as a dotted receiver (`MmA.sum`) does. Values are identical either way, so this is a missed reuse rather
than a defect — the repository documents the cache as something property-style access *may* use — and the
template says so instead of claiming reuse it demonstrably does not get
(`ArgumentPositionPropertyReference_DoesNotConsultTheCache`).

Cumulative budgets are **rejected** by name (`rebuilt-form-does-not-share-the-cumulative-budget`) for the
same reason Group A excludes them. Per-*object* ceilings are kept: both forms build the same individual
collections and strings, so those boundaries genuinely coincide.

#### Group C — entry-point parity

One source through two of eight registered surfaces:

| Surface | Projects |
|---|---|
| `evaluator-run-counted-observed` | outcome, structured error, value, emitted count, **counters** |
| `evaluator-run-counted` | outcome, structured error, value, emitted count |
| `evaluator-run` | outcome, structured error, value (no emitted count at all) |
| `evaluator-run-flat` | outcome, structured error, host atoms |
| `evaluator-run-counted-with-top-level-property` | the above, plus the `DisplayDecimals` channel |
| `engine-run` | outcome, value, emitted count, host atoms, rendered text |
| `engine-evaluate-to-atoms` | outcome, host atoms |
| `engine-evaluate-to-string` | outcome, value, emitted count, host atoms, rendered text |

A pair is compared on the **intersection** of what both surfaces project, so "these two entry points
agree" can never quietly mean "neither could tell", and the registry refuses a pair whose intersection
is only the outcome. The facet declarations were read off the production signatures rather than assumed:
`Evaluator.Run` really has no emitted count, and the engine's public `KatLangError` really keeps a
formatted message and a span rather than the structured `EvalError`, so **no engine surface claims the
structured-error facet**. Only the observed evaluator entry point hands back a budget, so every other
pair declares `NotCompared` rather than comparing two zeroes.

**Rendering.** `KatLangEngine.EvaluateToString` is **not** `Run(...).ToDisplayString()` for a successful
program — it is documented to return space-joined host atoms on success and the structured diagnostic
rendering otherwise. Asserting blanket string equality would assert something the runtime never
promised. Each observation therefore records which **projection** produced its text, and rendered text
must be exactly equal wherever the two projections coincide (every failure, and every same-surface
repeat) while the strict length bound is checked on both sides always. The `engine-evaluate-to-string`
adapter performs two independent engine invocations sharing one immutable `RunOptions` — one for the
text, one for the structured outcome the text surface does not expose — which is itself the "independent
runs reusing one configuration agree" property.

**Limits** are held at the default or comfortably generous. Resource-failure coverage comes from source
templates that exceed the always-on ceilings on their own, because the engine surfaces additionally bound
the host-atom projection by the per-collection ceiling while `RunCounted` does not; tightening that
budget would compare two genuinely different contracts rather than two entry points.

#### Group D — budget laws

Not arbitrary limit sweeps: every case knows which resource it exercises and where the boundary came
from. Seven dimensions, and exactly **one limit varies** between the two members:

| Dimension | Boundary from | One below the boundary |
|---|---|---|
| depth (`MaxDepth`) | measured `PeakDepth` | `EvaluationDepthExceeded` |
| steps (`MaxSteps`) | measured `ConsumedSteps` | `EvaluationStepLimitExceeded` |
| per-collection (`MaxCollectionItems`) | bounded deterministic search | `CollectionSizeLimitExceeded` |
| cumulative items (`MaxMaterializedItems`) | measured `MaterializedItems` | `MaterializationLimitExceeded` |
| per-string (`MaxStringLength`) | bounded deterministic search | `StringSizeLimitExceeded` |
| cumulative strings (`MaxMaterializedStringChars`) | measured `MaterializedStringChars` | `StringMaterializationLimitExceeded` |
| rendered output (`MaxDisplayLength`) | measured rendered length | a **bounded truncated rendering**, not an error |

Four boundaries are read straight off the run's own `EvaluationBudget`, which makes them exact rather
than estimated: a run that charged `S` steps succeeds at `MaxSteps = S` and fails at `S - 1`, and a run
that reserved `M` item slots fails at `M - 1` on its last reservation (both budgets check before moving
any counter, so a rejected reservation leaves the total untouched). The two per-*object* ceilings are not
accumulated anywhere, so they use a deterministic exponential-then-binary probe with a fixed ceiling and
a fixed 32-probe budget. That search *assumes* monotonicity but never asserts it — whatever it finds is
verified by the below/at/above executions the law performs, so a violation surfaces as a mismatch rather
than as a silently wrong boundary. Nothing allocates from an encoded integer and no unbounded search runs.

**Holding the policy constant matters.** Configuring any step budget switches the loop optimizer off, and
either string budget switches the sequence-pipeline optimizer off (`Evaluator.CreateRootCtx`). Those
dimensions therefore *measure* under a deliberately non-binding limit of their own kind, so the
measurement describes the same execution the sweep will run.

**Stack sufficiency is deliberately absent.** The host-stack backstop can only stop a run earlier than
the deterministic depth limit and is machine-dependent, so it is never a boundary: a case that hits it is
rejected with its own reason (`platform-dependent-stack-backstop`) rather than compared. The depth
dimension tests the deterministic `MaxDepth` limit only.

The five laws:

* **`BoundarySweep`** — left at the boundary, right at boundary + offset. A negative offset is the exact
  failure law (`SameResourceBoundary`: at the boundary must succeed, one below must stop with the
  dimension's own structured error, or — for rendering — return a bounded, *different* text). A
  non-negative offset is `MonotonicSuccess` plus `IdenticalWork`, because a limit that does not bind must
  not change the work either.
* **`InBudgetNeutral`** — the dimension's baseline policy against a comfortably generous limit, requiring
  `SemanticEqual` **and** `IdenticalWork`. Identical work here includes the recorded **optimizer path**,
  which is how the law proves the generous limit did not quietly switch an optimizer off.
* **`FailedReservationStability`** — control run, then a run at boundary − 1 that must genuinely fail (the
  executor rejects the case if it does not), then the control run again, requiring `IndependentRunStable`.
  The rendering dimension is rejected by name here: a display limit bounds the output, it does not fail a
  reservation.
* **`RunIsolation`** — the same control run repeated after interleaved unrelated runs, or observed from a
  bounded set of **distinct coexisting threads** sharing one immutable limits/options instance. Results are
  collected **by index, never by completion order**, and the lowest differing index is reported, so a leak
  is a deterministic mismatch rather than a flaky pass. No timing is asserted. See
  [Why the threaded plan hands the evaluator over](#why-the-threaded-isolation-plan-does-not-overlap)
  for why the threads do not evaluate simultaneously *inside the fuzzing loop*.
* **`EquivalentFormBoundaryParity`** — two trusted Phase 1/2 equivalent forms at the *same* derived limit.
  Applied only where the declared relation is exact: a dotted **builtin** link charges one extra step and
  one extra depth level than its ordinary spelling, so such a pair may sweep only the materialization and
  rendering dimensions (`equivalent-forms-do-not-share-a-work-boundary`). Fused chains are absent
  entirely — their materialization relation is directional by design, so requiring a shared boundary would
  contradict what Phase 2 established.

### The dotted rewrite contract, and structural-member exclusion

`A.F(B, C)` means `F(A, B, C)`: the receiver is supplied as **one leading argument boundary**,
never `F(A..., B, C)`. Templates therefore never introduce a spread when building the dotted
form; the one spread body Group B generates places the spread identically in the **suffix** of
both members, because a spread receiver has no dotted spelling at all.

Dotted **structural member access** (`Object.Value`, where `Value` is a member of an algorithm
rather than a callable rewrite) is a different language construct and is out of scope. Every
receiver in the tables evaluates to an ordinary `Result` value — never a block with exposed
members — which is what makes `.F` an extension-style call. Tests assert this directly: every
receiver evaluates to a value, and no generated source contains `public `.

### Callback-wrapper preconditions, and why similar-looking pairs are rejected

KatLang's flat-callback binding is receiver-specific and is **not** ordinary function-call
argument binding. A consumer supplies a fixed number of values per invocation, and only a wrapper
that binds exactly those values positionally sees what the direct builtin sees. Two projections
are therefore **rejected**, not compared:

* **Rest** (`MmWrap(xs...)`) — a rest parameter *collects* the supplied slots into an exact list,
  so the wrapper receives `[element]` where the builtin receives `element`. Measured:
  `[[1, 2], [3]].map(count)` is `[2, 1]` while the rest wrapper gives `[1, 1]`. That is correct
  language behaviour and a false equivalence, not a defect.
* **Arity-mismatched** — a flat multi-parameter callee first opens a lone *sequence*-valued
  element into row slots and arity-errors on other kinds, so it matches neither a one-value nor a
  two-value consumer.

Both are still *generated*, so the rejection path is exercised and counted, and both have
dedicated tests proving the non-equivalence they guard against.

**Algorithm/value duality** is preserved: the callback is written as a NAME on both sides, so the
builtin's callable-algorithm channel is used by both and no algorithm-only argument is forced
into a value. A materialization difference between the two forms would mean a prepared callback
value was reconstructed through `Result → Expr → evaluator` — a production operational defect,
never a reason to weaken the relation.

### Declared relations

* **Semantic — `SemanticEqual`** (all families). Success/failure outcome, neutral structural
  value, emitted count, innermost structured error kind, and — for resource limits, whose
  payloads are machine-independent counts — the structured payload. Error *prose* and source
  context are deliberately excluded: they may legitimately differ between two spellings of one
  call. A resource-limit stop stays distinguishable from an ordinary semantic failure.
* **`ExactMaterializationEqual`** (Phase 1 family, Group A, Group D). Exact equality of
  materialized collection-item slots and materialized string UTF-16 units, plus the same
  resource-limit verdict. Steps and peak depth are recorded but are **not** failure conditions:
  a dotted zero-argument link charges one extra step, and a user wrapper adds a whole invocation.
* **`ExactObservedWorkEqual`** (Group B). Everything above *plus* exact steps and peak dynamic
  depth — declared only because the repository already establishes that contract
  (`OperationalMetamorphicTests.UserExtensionCall_ChargesTheSameInBothForms` asserts
  `EvaluationSteps`). The committed exhaustive family sweep
  (`MetamorphicPhase2FamilyTests.UserExtensionCall_AgreesOnExactWorkAtEveryParameterPoint`)
  verifies exact observed-work equality for every accepted user-extension parameter point.
* **`MaterializationNeverIncreases`** (Group C, where fusion is **effectively eligible**). The
  dotted spelling is the one the sequence-pipeline optimizer can **fuse**; the nested ordinary
  form is not. A fused pipeline materializes nothing and is documented to charge less while still
  enforcing the same single-collection ceiling, so equality there would forbid fusion. The
  inequality still catches the failure mode that matters — a dotted form doing *more* work than
  its ordinary equivalent, which is exactly how the duplicate dotted-receiver defect presented.

  Eligibility is the **runtime's own gate**, not the optimizer flag alone. `Evaluator.CreateRootCtx`
  computes `loopOptimize = !budget.HasStepLimit` and
  `sequenceOptimize = loopOptimize && !budget.HasConfiguredStringLimit`, and `EvaluationBudget`
  sets `HasConfiguredStringLimit` when *either* string limit was configured — so any string or
  step budget, however generous, switches fusion off for the whole run. One helper owns that rule
  (`MetamorphicLimitPolicy.SequencePipelineFusionCanApply`) and both the relation selector and the
  tests read it, so an approximate copy cannot drift in. Wherever fusion is ineligible — the
  optimizer-off policy and the string-limit modes alike — the relation returns to exact equality,
  measured 144/144. This is why `Generous` configures only the *item* budgets: a generous string
  budget would silently make it a different execution policy from the default it mirrors.

  For the same reason, Group C **rejects** cumulative-item limit modes while optimizations are on
  (`fused-chain-does-not-share-the-cumulative-item-budget`): a fused pipeline deliberately does
  not consume that budget, so the two spellings genuinely cross it at different points. The
  per-collection ceiling *is* enforced identically and stays comparable.

Phase 3 adds five more, all declared for the same reason: the relation must match the pair.

* **Semantic — `SameStructuredOutcome`** (entry-point parity). Agreement on every facet **both**
  surfaces project, and nothing else. Demanding `SemanticEqual` would compare fields one surface cannot
  produce and pass on two `null`s.
* **Semantic — `MonotonicSuccess`** (boundary sweeps at or above the boundary). One-directional: if the
  left member succeeded, the right member at a larger effective limit must also succeed and agree on
  every shared facet. A left member that did not succeed places no obligation, which is what makes this
  a monotonicity law rather than an equality.
* **Semantic — `SameResourceBoundary`** (one below the boundary). The left member must succeed *at* the
  derived boundary and the right member must stop the way the case **declared** — with the dimension's
  structured resource error, or with a bounded truncated rendering. Both the stop kind and the expected
  error live on the case, so a new dimension adds data rather than a comparator branch.
* **Semantic — `IndependentRunStable`** (failed-reservation stability, run isolation). Two independent
  executions must be indistinguishable in *every* recorded respect — semantics, projections, counters,
  optimizer path, cache profile. Any difference at all means run state survived a run boundary.
* **`WorkNeverIncreases`** (Groups A and B). The **left** member never charges more materialized items,
  string units, or steps than the right. The opposite direction from Group C's
  `MaterializationNeverIncreases`, because here the member permitted to do less is the left one: an
  optimized run against the generic run of the same source, and a cached run against the rebuilt form.
  Peak dynamic depth is deliberately excluded — an optimized loop plan reaches a different nesting
  profile than the generic interpreter by design, so it is recorded and reported but never a failure.
* **`IdenticalWork`** (in-budget neutrality, isolation, at/above boundary sweeps). Materialized items,
  string units, steps, peak depth, **and** the recorded optimizer and cache evidence all equal.
* **`NotCompared`** — declared where at least one surface cannot report counters at all, so the case is
  a purely semantic comparison and says so rather than pretending equality.

**One qualification applies to every operational relation above.** Operational counters are
compared only when **both executions complete**. When either side stops at a structured resource
limit, semantic outcome, resource-limit kind, and structured payload remain comparable, but
partial work counters are not: an aborted run's counters are the prefix recorded at the abort
point, and two equivalent forms may legitimately have done different preparatory work before
reaching the same limit (`reduce(R, contains, [1, 2])` materializes its initial accumulator before
forcing `R`; the dotted form prepares the receiver first and stops earlier). Ordinary,
non-resource semantic failures are **not** exempt — their counters are compared exactly like a
successful run's. The gate is `MetamorphicComparator.WorkIsComparable`, and
`MetamorphicPhase2FamilyTests.OperationalCounters_AreComparedUnlessAResourceLimitAbortedARun`
pins all three cases. The fingerprint records which side of the gate each case landed on
(`work=compared` / `work=partial`), so a campaign summary shows how much of its coverage reached
the work comparison.

Observations come from the run's own `EvaluationBudget`, obtained through
`Evaluator.RunCountedObserved`. Nothing re-evaluates, nothing rebuilds a value, there are no
static counters, each side gets a fresh budget and a fresh zero-argument property cache, and
the executor verifies afterwards that observing left every counter untouched. The two sides
deliberately *share* one immutable `EvaluationLimits` instance, because "reused limits carry no
run state" is one of the properties worth exercising.

### Limits are measured, not modelled

Phase 1 could compute its single family's item total from the range bounds. Phase 2 spans every
builtin, receiver kind, chain, and callback, so a closed-form model would be a second
implementation of the evaluator's accounting. Instead the left member is run once with **default**
limits and its own run-scoped budget is read, and limits are then placed relative to those real
totals — just below, exactly on, just above, and comfortably clear. No zero-valued configuration
is ever used to infer zero work.

### Payload backward compatibility

Bytes 0–5 are the common prefix and keep their exact Phase 1 meaning; family-specific dimensions
are **appended** at byte 6 and beyond, never overloaded onto an existing byte. A payload of
**six bytes or fewer is a version-zero payload** and always decodes to the Phase 1 family with
the Phase 1 tables — Phase 1's family table had a single entry, so byte 0 could not select
anything else, and forcing the family for short payloads reproduces that exactly. Reaching a
Phase 2 family requires a seventh byte. The Phase 1 limit-mode table stays frozen at four
entries for that family even though later families support seven, so byte 2 cannot change meaning
either. Tests pin this: the Phase 1 decoder is reimplemented as an oracle and checked against
every byte value at every position, and every tracked Phase 1 seed is asserted to decode to the
same case and re-encode to the same six bytes.

Phase 3 kept the same discipline. Its four families were **appended** at registry indices 5–8, its
dimensions are appended at byte 6 and beyond, and it added one new limit mode (`FamilyDerived`,
used only by `budget-law`, which derives both sides' limits itself and reads the primary offset byte
as the *boundary* offset). No existing family's supported-mode list, dimension size, or byte meaning
changed, so `ShortPayloads_NeverSelectAPhase3Family` and
`EveryLegacyParameterPoint_KeepsItsExactPrePhase3ExecutionShape` hold by construction. The Phase 3
additions to the case model are all `init` properties whose defaults are the Phase 1/2 values, so a
legacy case is not merely decoded the same — it is *executed* the same.

What appending a family *does* change is the meaning of byte-0 values at or above the old family
count for payloads **longer than six bytes**: the family index is a modulus over the registry, so a
seven-byte payload whose first byte was `5` used to wrap to index 0 and now reaches the first Phase 3
family. That was equally true when Phase 2 appended to Phase 1's single-entry table. It is why every
tracked seed carries a first byte inside the family range, why version-zero payloads force index 0
unconditionally, and why the registry's first five entries are pinned by identity *and* order
(`TheFirstFiveRegistryEntries_KeepTheirExactIdentityAndOrder`). Untracked campaign corpora under
`fuzz/artifacts/` are regenerated scratch data and carry no compatibility claim.

### Why Lean is not an operational oracle

Lean is the authority on what a KatLang program **means**, not on what the C# runtime
**does**. `lean/KatLang.lean` models an unbounded evaluator with no fuel, no budget, and no
notion of an allocated item slot, and adding operation counters to it would make the formal
specification depend on a machine property it does not describe. So both members of a pair are
ordinary Lean-representable programs whose *semantics* the existing differential corpus already
pins — while the operational half of the relation is a C#-to-C# comparison only. No Lean
change is part of this layer.

### Running it

```powershell
# 300-second smoke campaign (exports the curated seeds, then runs libFuzzer under WSL)
powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 -Mode metamorphic `
  -MaxTotalTime 300 -MaxLen 4096 -Timeout 5 -RssLimitMb 2048
```

`-Mode` forwards `KATLANG_FUZZ_MODE` into WSL through `WSLENV` and gives the target its own
`fuzz/artifacts/corpus-metamorphic` and `fuzz/artifacts/crashes-metamorphic` directories, so no
other campaign's corpus is touched.

Deterministic replay (no fuzzing loop, works on plain Windows .NET 10):

```powershell
# replay every curated seed; each case runs twice, so non-determinism is itself a failure
dotnet run --project fuzz\KatLang.ParserFuzz -- metamorphic-replay fuzz\KatLang.ParserFuzz\MetamorphicTestcases

# replay one payload straight from a mismatch report
dotnet run --project fuzz\KatLang.ParserFuzz -- metamorphic-replay --payload 000401010100

# replay recorded crash/corpus artifacts, whose CONTENT is the raw payload
dotnet run --project fuzz\KatLang.ParserFuzz -- metamorphic-replay --raw fuzz\artifacts\crashes-metamorphic
```

### Seeds

`KatLang.ParserFuzz/MetamorphicTestcases/seeds.txt` is the tracked corpus (127 seeds: 13 Phase 1,
42 Phase 2, 72 Phase 3). A metamorphic seed is a **template payload**, not a source file — storing
sources would duplicate text the template regenerates deterministically — so each line is
`family=<id> bytes=<hex> desc=<note>`. The declared family is redundant on purpose: replay
checks it against the family the payload decodes to, so a stale seed is reported instead of
silently replaying a different case. `metamorphic-seeds OUTDIR MANIFEST` materializes the raw
payload bytes as a libFuzzer seed corpus.

Eight seeds are deliberately **rejected** cases, so replay exercises and reports the rejection path
rather than only the happy one: the two non-equivalent callback projections, the two cumulative
budgets a cached and a rebuilt form cannot share, a per-collection ceiling that stops a run before it
can fuse, a malformed source aimed at an evaluator surface, a display limit asked to fail a
reservation, and an equivalent-form pair asked to share a work boundary it does not have.

### Phase 4: running and triaging a full campaign

The families and relations are what make a finding meaningful; this section is the procedure that
turns a long run into reviewable evidence.

**Inventory.** Nine families in four groups plus the Phase 1 pair, five semantic relations, six
operational relations, eight runtime surfaces in eight reviewed pairs, five budget laws, and seven
resource dimensions. `MetamorphicPhase4ReadinessTests` asserts that a deterministic stratified
sample reaches every one of them, so "the campaign covered X" is a measured claim rather than an
assumption. Set `KATLANG_METAMORPHIC_READINESS_REPORT` to a path to have the distribution written
out.

**Staged campaign.** Each stage must be clean before the next one starts. Preserve the previous
corpus by RENAMING it first (`fuzz/artifacts/` is gitignored, and `-FreshCorpus` deletes the
writable corpus), then run fresh:

```powershell
# Stage A — smoke. Everything reachable, nothing unexplained, throughput and RSS sane.
powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 -Mode metamorphic `
  -MaxTotalTime 300 -MaxLen 12288 -Timeout 5 -RssLimitMb 2048 -FuzzerSeed 40001 -FreshCorpus

# Stage B — main.
powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 -Mode metamorphic `
  -MaxTotalTime 1800 -MaxLen 65536 -Timeout 5 -RssLimitMb 2048 -FuzzerSeed 40002 -FreshCorpus

# Stage C — independent confirmation: a fresh corpus, the same seeds, a DIFFERENT engine seed.
powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 -Mode metamorphic `
  -MaxTotalTime 1800 -MaxLen 65536 -Timeout 5 -RssLimitMb 2048 -FuzzerSeed 40003 -FreshCorpus
```

`-FuzzerSeed` forwards libFuzzer's `-seed` through `WSLENV` exactly as `-Mode` forwards the target.
It is what makes Stage C an independent sample rather than a second draw from the same stream, and
what makes any stage reproducible. Zero (the default) leaves the engine to choose, as before.

**Replay every corpus twice.** A corpus is only evidence if it replays; replaying it twice is what
catches a case that is stable within a run but not across runs. Replay is not a second
implementation — it decodes, builds, executes, and compares through the same code the campaign
ran, and internally runs each case twice as well:

```powershell
dotnet run --project fuzz\KatLang.ParserFuzz -- metamorphic-replay --raw fuzz\artifacts\corpus-metamorphic
```

**Merging** uses libFuzzer's own workflow — there is no corpus-management layer here. Merge into a
fresh directory, then replay it before trusting it:

```bash
"$HOME/katlang-fuzz/libfuzzer-dotnet" --target_path=<publish>/KatLang.ParserFuzz \
  -merge=1 <merged-dir> <corpus-b> <corpus-c>
```

**Retained artifacts.** Corpora are working state, not repository content: nothing under
`fuzz/artifacts/` is tracked. What gets tracked is a *seed* — one line in
`MetamorphicTestcases/seeds.txt` — and a seed is added only when the payload it pins is worth
re-running forever: a reproducer for a fixed defect, a newly covered relation or rejection path, or
a case a reviewer should be able to reproduce by name. Everything else stays in the corpus
directory, and previous phases' corpora are kept by renaming so a campaign can always be compared
against the one before it.

**Counters after an abort are diagnostic only.** When either side stops at a structured resource
limit, its counters are the prefix recorded at the abort point, and two equivalent forms may
legitimately have done different preparatory work before reaching the same limit. Such a pair is
still compared on its whole semantic observation — outcome, resource verdict, error kind, and
structured payload — but not on work. The gate is `MetamorphicComparator.WorkIsComparable`, which
also refuses the comparison when a surface hands back no budget at all rather than comparing two
structural zeroes.

**Is a mismatch semantic or operational?** Read the mismatch CLASS, which the report and the
fingerprint both name:

| Class | Means | First question |
| --- | --- | --- |
| `Semantic` | The two members disagree about what the program MEANS. | Is the equivalence argument actually true? Check the family's template, then compare each minimized member against Lean. |
| `ResourceBoundary` | Host budget policy: one side stopped for a limit the other cleared, or a boundary law's below/at/above shape broke. | Did exactly one dimension vary? Was the boundary derived under the same policy the sweep ran? |
| `Operational` | Same meaning, different amount of work. | Is the declared relation stronger than the runtime's contract — and is the direction right? |
| `Rendering` | A display surface returned different text, or more units than its limit allows. | Did both sides render the same PROJECTION? `EvaluateToString` is not `ToDisplayString()` on success. |
| `StateIsolation` | Two independent executions were distinguishable. | Something outlived a run: a counter, a cache, an optimizer decision, a diagnostic. |

Semantic findings are language findings and belong in Lean's world; the other four are host-policy,
optimizer-accounting, rendering, or state findings, and Lean models none of them.

**Triage classification.** Every crash, timeout, mismatch, or non-deterministic replay is minimized
to a payload, replayed, and classified as exactly one of: decoder, normalization, template,
invalid-equivalence-assumption, precondition, relation-direction, comparator, observation, replay,
fingerprint-only, instrumentation-artifact, optimizer-evidence, cache-evidence, entry-point-adapter,
boundary-search, or state-isolation defect on the harness side; production semantic, optimizer,
cache, entry-point, or resource-policy defect on the runtime side; or an unexpected CLR exception or
genuine unbounded work. A timeout is not automatically a defect and a rejection is never a finding —
but broadening a rejection rule to silence a mismatch is only legitimate after the relation has been
shown invalid independently.

### Current limitations

*Phase 2:*

* Chains are bounded to three links, drawn from twelve fixed link lists — the fuzzer selects a
  chain, it never assembles one.
* Group C claims only a directional operational relation where sequence-pipeline fusion is
  effectively eligible; the exact claim is made wherever it is not (optimizer off, or any
  configured string budget).
* Group C's cumulative-item rejection is deliberately **conservative**: it drops the whole mode
  while optimizations are on, although only the fusible chains actually cross that budget at
  different points. Narrowing it would mean predicting per-template fusion inside the harness —
  a second implementation of the optimizer's own eligibility analysis — so the broad rejection is
  kept and counted by name rather than replaced by a guess.
* Operational counters are not compared when either side aborts on a resource limit (see the
  qualification under *Declared relations*); those cases still compare their full semantic
  observation, including the structured resource-limit payload.
* Group B's exact-work claim covers steps and peak depth only for the shapes in its body table.
* Rest-parameter and multi-parameter callback wrappers are represented as rejections, not as
  trusted equivalences; establishing a trusted rest-wrapper form is future work.

*Phase 3:*

* Groups A and B generate only limit modes that cannot bind differently on their two sides. A
  cumulative budget derived from the cheaper side's measurement would stop the other side for a
  reason that is not a defect, so those modes are rejected by name rather than compared. Varying
  budgets is the budget-law family's job.
* Group A's optimizer sources are a fixed reviewed table of 28 programs with **declared** paths; the
  fuzzer selects a source, it never assembles one. A source whose optimizer shape changes makes the
  case rejected (and the committed sweep fail), never silently compared.
* Group C compares the intersection of two surfaces' facets. Where that intersection excludes
  operational counters — every pair but observed-versus-observed — the case makes no operational
  claim at all. Engine surfaces cannot contribute a structured error kind, because the public
  `KatLangError` does not carry one.
* `EvaluateToString` and `Run(...).ToDisplayString()` are compared exactly only where they render the
  same **projection**, which on current behaviour means every non-success. On success the two return
  different projections by documented contract, and only the strict length bound and per-surface
  determinism are claimed.
* Group D never claims an exact **stack-sufficiency** boundary: that backstop is machine-dependent, so
  a run that hits it is rejected and classified rather than compared.
* The two per-object ceilings (`per-collection-items`, `per-string-length`) use a bounded search that
  *assumes* success is monotone in the limit. The search still never asserts it, but the assumption is no
  longer only spot-checked: `SearchedBoundaries_AreMonotoneAcrossTheirCompleteInterval` executes **every
  limit value of the complete bounded interval** — all 4096/4097 of them — for every registered boundary
  template and **each optimizer policy separately**, using the search's own predicate
  (`MetamorphicBoundaryPolicy.SucceedsAt`), and requires that once a program fits, every larger limit in
  the interval still fits with the same neutral value and emitted count. Roughly 377k executions; it is
  the reason the test suite now takes about a minute and a half rather than half a minute.
* Threaded isolation uses a fixed, small thread count and asserts only observational equality against a
  sequential control. Nothing here asserts timing, throughput, or scheduling.

### Why the threaded isolation plan does not overlap

The fuzzing engine's feedback is edge instrumentation woven into `KatLang.dll`, and that instrumentation
keeps its "previous location" in **one process-wide slot** with no synchronisation and no thread affinity
(`SharpFuzz.Common.Trace.PrevLocation` is a plain `static int`; `SharedMem` is a shared table). Two
evaluations running at the same instant therefore interleave their read-modify-writes of that slot and
stamp edge indices no sequential execution can produce — so **a concurrent run's coverage is a function of
the thread schedule, not of the input**, which is precisely the thing a coverage-guided fuzzer cannot cope
with.

Measured on this repository, replaying the same forty corpus files three times:

| corpus | features, three identical passes | covered edges |
| --- | --- | --- |
| overlapping evaluations | 69237 / 70798 / 68518 | 8 (stable) |
| after the hand-off change | 10147 / 10147 / 10146 | 8 (stable) |
| non-parallel control (unchanged) | 22317 / 22324 / 22329 | 8 (stable) |

Every phantom feature reads as new coverage, so the engine saved the input and mutated around it forever.
That is how a law with only **40 distinct cases** came to hold **2137 of 2820** corpus units — and, worse,
how schedule noise came to occupy the shared feature map that every *other* family's genuine coverage has
to compete for. It is not a decoder-weighting problem: every non-parallel shape stored 683 units for 633
distinct cases (1.08x), while the parallel plan stored 53x.

So the plan now starts that many real, coexisting threads sharing one immutable configuration instance and
hands the **evaluator** over in index order. That still exercises everything the law is about — run state
that is thread-affine, static mutable state, a configuration object that accumulates, a cache or budget
that outlives its run — because each observation happens on a different thread from the one before it.
What it deliberately no longer does *inside the fuzzing loop* is overlap two evaluations in time.
Simultaneous execution did not go away; it moved to `MetamorphicPhase3FamilyTests`, which runs
uninstrumented and can afford it, and which now rendezvouses its workers on a `Barrier` so they overlap on
purpose rather than by luck, across both entry-point classes, both execution orders, repeated A/B/A
rounds, mixed succeeding/failing runs, and cache/budget/diagnostic contamination.
* Still out of scope, as before: Unicode/UTF-16 fuzzing, parser edit-sequence fuzzing, source-size and
  module-download policy, and any exact Lean/C# operational-counter comparison.

### Adding a trusted template later

1. Add a `MetamorphicFamily` value and **append** a `MetamorphicFamilyDefinition` to
   `MetamorphicFamilyRegistry`. Never reorder or remove an entry: index 0 must stay the Phase 1
   family because version-zero payloads resolve there, and a family's index is its byte-0 value.
2. Add a template type next to the others that **constructs** both members and states the
   equivalence argument in its doc comment. Declare its appended dimensions in the registry
   entry; extend the byte layout rather than overloading an existing byte.
3. If a dimension's legal range depends on another (a builtin's suffix-variant count, a
   consumer's callback arity), reduce it in the family's `Normalize` — and make that reduction
   **idempotent**, or `Decode(Encode(p)) == p` breaks.
4. Declare the relations the construction actually justifies. Use an inequality whenever the
   implementation is *permitted* to do less (fusion, caching); exact equality is only for pairs
   that are two spellings of the same work; `ExactObservedWorkEqual` only where the repository
   already establishes that contract.
5. State the family's real preconditions in its validator. A rejected case is counted and
   reported by reason, never silently skipped and never a mismatch.
6. Add curated seeds and extend `MetamorphicPhase2FamilyTests` — its stratified sweep crosses
   each family's own dimensions exhaustively, so a new dimension is covered once the tables list
   it.
