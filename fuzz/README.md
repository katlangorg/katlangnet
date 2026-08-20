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
| `utf16` | difficult **UTF-16 source text**: lexer, parser, spans, line/column | `utf16-replay` |
| `editor` | **editor-tooling semantic model** (`KatLang.Semantics`): classification, hover, symbol lookup, navigation, outline, signatures | `editor-replay` |

The first three feed arbitrary bytes to the language as source text. The last three do not —
see [Operational-metamorphic fuzzing](#operational-metamorphic-fuzzing),
[UTF-16 fuzzing](#utf-16-fuzzing) and [Editor-tooling fuzzing](#editor-tooling-fuzzing).

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
    Utf16/                      # UTF-16 target (tables, decoder, source builder, executor,
                                #   relations, fingerprint, replay)
    Utf16Testcases/             # tracked UTF-16 seeds (payloads in hex, never source text)
  katlang.dict                  # libFuzzer dictionary of KatLang fragments
  run-campaign.sh               # WSL-side: build driver + run libFuzzer
  README.md                     # this file
  artifacts/                    # gitignored: publish output, corpus, crashes, logs
scripts/
  fuzz-parser.ps1               # Windows-side orchestration (publish + instrument + run)
```

The harness project stays outside `KatLang.slnx`, with two deliberate exceptions: the
self-contained `Metamorphic/` and `Utf16/` folders are compiled into `tests/KatLang.Tests` as
shared source, so `MetamorphicFuzzHarnessTests` and `Utf16FuzzHarnessTests` exercise exactly the
decoder, template, executor and replay driver the campaign runs instead of a second copy. `Utf16/`
also pulls in the four harness files it reuses rather than reimplements — `SourceSpanValidator.cs`,
`FuzzInvariants.cs`, `FrontEndInvariants.cs`, `FrontEndFingerprint.cs`. Nothing else in `fuzz/` is
part of normal validation, and none of the shared files may reference SharpFuzz.

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
newline/CRLF/lone-CR boundaries, comments, property/`public` definitions,
ordinary and conditional clause definitions, calls/brace-calls, dot-calls and
leading-dot continuation, `open` declarations, `:` indexing, `~` grace, prefix `*name` collect markers, postfix `expr*` spreading,
deconstruction and movable-collecting patterns, and malformed delimiter/semicolon/unexpected-
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

## Source and module input-size probing (`SourceModuleProbe.cs`)

The Phase-6 measurement backbone for the source/module input-size policy
(`SourceProcessingLimits`). It measures how source text and module graphs become tokens,
AST nodes, diagnostics, and downloader work BEFORE the evaluator runs. Counts (UTF-16
source length, tokens, nodes, diagnostics, module count, aggregate source, import depth)
are deterministic and architecture-independent; elapsed time, GC allocation, and peak
working set are recorded for **calibration only** and are never proposed as public limit
units. No network access — the module probe uses a generative in-memory downloader keyed
by URL.

```powershell
# deterministic source shapes: per-stage counts + amplification ratios (tok/src, node/src,
# post/raw, diag/src) for long/flat, wide, deep, many-declaration, and diagnostic-heavy sources
dotnet run --project fuzz\KatLang.ParserFuzz -c Release -- source-probe --out fuzz\artifacts\perf\source.json
# one big source in an isolated child (peak working set for calibration): SHAPE N
dotnet run --project fuzz\KatLang.ParserFuzz -c Release -- source-probe-child many_funcs 130000
# module-graph scenarios via a fake downloader: chain, wide, diamond, repeat, cycle,
# many-tiny, one-large, aggregate, failed; with default ceilings active
dotnet run --project fuzz\KatLang.ParserFuzz -c Release -- module-probe
# isolated deep-chain no-crash/resource-error validation under production ceilings
dotnet run --project fuzz\KatLang.ParserFuzz -c Release -- module-depth-search --max 5000
```

The full deterministic table records source length, tokens, raw/frontend nodes, diagnostics,
and timing/allocation calibration across 104 rows. In this run the observed ratios reached
1.05 tokens, 1.568 nodes, and 1.02 diagnostics per code unit; these are MEASURED samples,
not universal proof bounds. `frontendNodes = parserNodes` across the included shapes after the
sibling-map cloning and declaration duplicate-scan fixes. The formerly quadratic per-construct
paths were subsequently made linear too: the wide-deconstruction elaboration, and then the
conditional clause-family duplicate check (`many_clauses`: hashed match-equivalence lookup
replacing the all-pairs scan) plus the evaluate-all deconstruction bind (`eval_all_deconstruct`:
one shared run-scoped bind per group). The import loader overflowed the host stack at ~562 transitive levels on the
measured Windows configuration — calibration for the 2 MiB per-source, 64 import-depth, 8 MiB
aggregate, and 256 module-count ceilings, not a cross-platform stack measurement. With those
ceilings active the module probe shows each limit firing structurally and
`module-depth-search` reports "completed through max" (the stack-overflow crash is gone).
Aggregate and module-count totals cover accepted sources; failed downloads and policy-rejected
fetches remain uncharged and may be attempted again, so the probe reports downloader work
separately from accepted-source accounting.
The resource-error boundaries themselves are reproduced deterministically by
`SourceProcessingLimitsTests`, not by byte-fuzz seeds: they require inputs (multi-MiB
source, a fake module graph) outside the byte-fuzz input space, so no new libFuzzer mode
was added.

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

**Limit policy.** Only fusion-neutral modes are generated (`Default`, `PerCollectionItems`,
`Generous`, where generous now configures only the per-collection ceiling). A configured cumulative
item budget disables sequence fusion by production policy; including it in this family would therefore
prevent the sequence sources from satisfying the family's measured optimizer-hit precondition while the
loop sources could remain optimized. Step and string budgets are omitted for the same execution-policy
reason. The per-collection ceiling *is* kept, because the runtime explicitly promises it is optimizer-
independent (`EvaluationBudget.CheckCollectionSize` exists so a fused pipeline rejects the same
collection size a generic one does).

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
never `F(A*, B, C)`. Templates therefore never introduce a spread when building the dotted
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

* **Collecting** (`MmWrap(*xs)`) — a collecting parameter *collects* the supplied slots into an exact list,
  so the wrapper receives `[element]` where the builtin receives `element`. Measured:
  `[[1, 2], [3]].map(count)` is `[2, 1]` while the collecting wrapper gives `[1, 1]`. That is correct
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
  computes `loopOptimize = !budget.HasStepLimit` and `sequenceOptimize = loopOptimize && !budget.HasConfiguredStringLimit && !budget.HasConfiguredMaterializationLimit`.
  `EvaluationBudget` sets the latter flags when either
  string limit or the cumulative item limit was configured — so any string, step, or cumulative-item
  budget, however generous, switches fusion off for the whole run. One helper owns that rule
  (`MetamorphicLimitPolicy.SequencePipelineFusionCanApply`) and both the relation selector and the
  tests read it, so an approximate copy cannot drift in. Wherever fusion is ineligible — the
  optimizer-off policy and those limit modes alike — the relation returns to exact equality, measured
  144/144. This is why `Generous` configures only the fusion-neutral per-collection ceiling: any other
  generous budget would silently make it a different execution policy from the default it mirrors.

  Cumulative-item modes are accepted rather than rejected: configuring that budget itself forces both
  chain spellings through the generic sequence path, so they charge the same cumulative counter. The
  per-collection ceiling remains fusion-neutral and is enforced identically on both strategies.

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
  configured string, step, or cumulative-item budget). Cumulative-item modes are accepted because
  configuring that budget makes fusion ineligible by construction.
* Operational counters are not compared when either side aborts on a resource limit (see the
  qualification under *Declared relations*); those cases still compare their full semantic
  observation, including the structured resource-limit payload.
* Group B's exact-work claim covers steps and peak depth only for the shapes in its body table.
* Collecting-parameter and multi-parameter callback wrappers are represented as rejections, not as
  trusted equivalences; establishing a trusted collecting-wrapper form is future work.

*Phase 3:*

* Group A uses only fusion-neutral modes so every source in its mixed loop/sequence table can still
  demonstrate the declared optimizer hit. Group B rejects cumulative budgets because a limit
  derived from the cheaper cached side can legitimately stop the rebuilt side. Varying budgets is
  the budget-law family's job.
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

## UTF-16 fuzzing

`KATLANG_FUZZ_MODE=utf16` fuzzes **source text**, not programs: the lexer, the parser, parser
recovery, the front end, diagnostics, source spans, and line/column reporting, over UTF-16 that is
hard on purpose — isolated surrogates, combining marks, mixed line endings, zero-width format
characters, NUL, and Unicode separators that look like newlines and are not.

The goal is **not** to make difficult UTF-16 parse. Structured, deterministic rejection is a
perfectly good outcome — most of the space produces diagnostics, and that is the point. What must
never happen is an unexpected exception, an out-of-range or self-inconsistent span, a token that
disagrees with the source it came from, unbounded or position-stuck diagnostics, a non-deterministic
result, or a silently normalized code unit.

### Why the payload is not source bytes

The other three source-text targets decode fuzzer bytes as UTF-8. That cannot work here: **an
isolated surrogate has no UTF-8 form.** Any byte string handed to `Encoding.UTF8.GetString` comes
back as well-formed UTF-16, so the single most interesting input class in this phase would be
unreachable — and a seed stored as a source *file* would be rewritten to U+FFFD by git, an editor,
or `File.ReadAllText`, silently, with the seed still sitting there looking like it tested something.

So the payload selects code units explicitly. It picks a trusted source template, a named run of
code units, a placement, a line-ending encoding and an execution mode; two raw modes build the units
from the payload tail instead — one through a fixed alphabet of difficult units, one from literal
little-endian `ushort` pairs — so an arbitrary or unassigned code unit is still reachable.

```
byte 0  template          25 entries: identifier start/continue, property name, function name,
                          parameter name, number boundary, string literal, backslash in string,
                          unterminated string, line comment, comment at EOF, delimiter adjacency,
                          dotted call, spread, list literal, sequence literal, deconstruction,
                          collecting binding, callback body, conditional clause, multiline body,
                          recovery point, EOF boundary, plus the two raw modes
byte 1  placement         alone, after/before/around an ASCII letter, doubled, tripled, split by a
                          newline, split by punctuation, after a dot, before a spread, at end of source
byte 2  line endings      Lf, Crlf, LoneCr, Mixed, NoNewline, RepeatedBlankLines,
                          TrailingNewline, NoTrailingNewline
byte 3  execution         ParseSyntax, FrontEnd, EngineParse, StringBridge
byte 4  code-unit group   Basic, Latvian, BmpSymbols, Combining, Surrogates, Whitespace
byte 5  member            which entry of that group
byte 6  repeat            1..4 copies
byte 7  filler            which ASCII letter the adjacency placements use
byte 8+ raw tail          48 bytes, read ONLY by the two raw templates
```

Every field is taken modulo its table size, so **every** byte string decodes, including the empty
one. The bounded prefix is **56 bytes** — which is why campaigns run with `-MaxLen 56` rather than a
large round number: nothing past byte 55 can change a case, so a bigger limit only spends the
engine's effort on tails that cannot matter.

### The code-unit model

Source text is a sequence of UTF-16 **code units**, because that is what `string` indexing exposes
and what the lexer classifies. Nothing is normalized to NFC/NFD/NFKC/NFKD, nothing is converted to
scalar values or runes, and no ill-formed surrogate is replaced before the lexer sees it. The builder
assembles a `List<ushort>` and converts to a `string` exactly once, at the end.

The contract this target rests on — written down in `Utf16LexerContractTests`, and nowhere else:

| Question | Answer |
|---|---|
| What indexes a source position? | UTF-16 code units. Token `Position`/`Length` are code-unit offsets. |
| Line and column base | 1-based; `SourceSpan` end positions are **inclusive**. |
| What do columns count? | UTF-16 code units — not scalars, not graphemes, not tab-expanded columns. |
| Surrogate pair | **Two** columns. Neither half is ever an identifier character (`char.IsLetter` is per code unit), so an astral letter lexes as two bad tokens. |
| Combining mark | Its own column, and not an identifier character. Precomposed and decomposed forms are different sources and stay different values. |
| Line break | `'\n'` **only**. |
| `'\r'` | Transparent: advances neither line nor column. A lone CR is *not* a line break — though it does end a string literal and a comment. |
| U+2028, U+2029, U+0085, VT, FF, NBSP | `char.IsWhiteSpace` is true, so they separate tokens and cost one column — but none starts a line. |
| U+200B, U+200D, U+FEFF | Category `Cf`, **not** whitespace: they become bad tokens. A BOM mid-file is a diagnostic, not trivia. |
| Non-ASCII letters | Identifier characters (Latvian, Greek, Cyrillic, ideographic, and letter-like symbols). |
| Non-ASCII decimal digits | Start a number token (`char.IsDigit` is true) that `Decimal128.TryParse` then rejects under the invariant culture. |
| String literals | Single quotes, **no escape sequences at all**; ended by `'`, `'\n'` or `'\r'`. |
| Comments | `#` to `'\n'` or `'\r'`. There is no block-comment form. |

### Invariants

Everything the raw-parser and frontend layers already guarantee is checked by **calling** those
layers (`FuzzInvariants`, `FrontEndInvariants`) rather than restating their rules. What this target
adds is all about the code-unit model:

1. **Forward progress.** The token stream covers the source with strictly increasing offsets, every
   non-EOF token consumes at least one code unit, and the EOF token sits at exactly `source.Length`.
   A lexer that stalled on an isolated surrogate fails here rather than hanging.
2. **No token spans a line break.** Every scan terminates at `'\n'`/`'\r'`, which is precisely what
   makes `Column + Length` a sound end column.
3. **Location cross-check.** Each token's recorded `(Line, Column)` must equal the one recomputed
   from its offset by `SourceSpanValidator.LineColumnAt` — the lexer tracks them incrementally while
   scanning, this derives them from the source, and they must agree. One shared helper, one model,
   used by the raw, frontend and UTF-16 layers alike.
4. **Exact source slices.** Identifier, comment and string-literal token text must be the exact
   source slice (minus `#` or the quotes). This is what catches a normalization or a replacement
   character introduced anywhere on the path.
5. **Bounded diagnostics.** Total diagnostics are bounded linearly in source length, and the number
   sharing one `(line, column)` is bounded by `Parser.MaxNestingDepth`.
6. **Determinism and isolation.** A/A and A/B/A on every input, plus a reversed-order sweep in the
   deterministic tests.

Invariant violations and unexpected CLR exceptions both escape to the fuzzing engine with their
original type and stack. Nothing converts one into an ordinary diagnostic.

A note on that fifth bound, because it is the one that is easy to get wrong. Diagnostics stack at
one position when nested constructs are left open: `[[[[` reports "expected `]`" once per bracket,
all at end of file. Every code unit is consumed the whole time, so this is *not* a stalled recovery
loop, and a bound justified as "the parser must make progress" would be measuring the wrong thing.
An early version of this harness did exactly that, with a ceiling of 16 taken from templates that
never nest; a five-minute campaign refuted it in 14,090 executions. The bound is now one diagnostic
per open construct, and open constructs are capped by the parser's own nesting guard. Forward
progress is established separately and structurally, by the token invariants above.

### Relations

Four trusted relations, each with a named precondition. Where the contract deliberately differs
between two encodings, the relation pins the **divergence** — asserting equality there would be a
false relation, not a stronger test.

| Relation | Claim | Precondition |
|---|---|---|
| `cr-transparency` | LF and CRLF give identical tokens (kind, line, column, length, text), identical diagnostics, and an identical syntax tree. Offsets shift and are deliberately not compared. | The LF encoding contains no CR of the case's own. |
| `lone-cr-not-a-line-break` | Re-encoding every break as a lone CR collapses the source to one line: every token and every span stays on line 1. | Same, plus the source has a line break to re-encode. |
| `trailing-newline-neutral` | Appending a newline to a closed, diagnostic-free program leaves the syntax tree — spans included — unchanged. | The template is a closed program and the case parses cleanly. Never applied to unterminated constructs or a comment running to EOF. |
| `exact-string-preservation` | A valid string literal reaches the evaluator as exactly the code units between the quotes, with `Length` counting code units. | A closed, diagnostic-free single-literal program whose content cannot end the literal. |

`cr-transparency` is a strong claim rather than a structural one *because* `'\r'` advances neither
line nor column and every token scan already stops at `'\n'`: inserting a CR immediately before each
LF cannot change any token's text, length, line or column. That is exactly why the relation compares
spans directly instead of neutralizing them first.

The string bridge is the only path in this target that evaluates anything, and it runs only for a
closed single-literal program. This is not general evaluator fuzzing.

### Seeds and replay

Seeds live in `fuzz/KatLang.ParserFuzz/Utf16Testcases/seeds.txt` — pure ASCII, one reviewable line
per case:

```
template=string-literal bytes=06 00 00 03 04 05 00 00 units=004F ... D83D 0027 desc=isolated HIGH surrogate
```

`template` is redundant on purpose and is checked against the template the payload decodes to.
`units` is optional and, where present, pins the **exact** code-unit sequence in four-digit hex — the
round-trip guard for the seeds whose whole point is one difficult code unit. Malformed metadata is
reported, never silently accepted.

```bash
# replay every tracked seed; each case runs TWICE, so non-determinism is itself a failure
dotnet run --project fuzz/KatLang.ParserFuzz -- utf16-replay fuzz/KatLang.ParserFuzz/Utf16Testcases

# replay one payload straight from a report
dotnet run --project fuzz/KatLang.ParserFuzz -- utf16-replay --payload "06 00 00 03 04 05 00 00"

# replay recorded crash/corpus artifacts, whose CONTENT is the raw payload
dotnet run --project fuzz/KatLang.ParserFuzz -- utf16-replay --raw fuzz/artifacts/crashes-utf16
```

Replay uses the same decoder, builder, executor and relations as the fuzzing loop, prints every
case's exact code units in hex, and treats "the given paths contain no seeds" as a failure rather
than a clean run.

### Running a campaign

```powershell
# Stage A - smoke. MaxLen is the decoder's bounded prefix, not a round number.
powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 `
  -Mode utf16 -MaxTotalTime 300 -MaxLen 56 -Timeout 5 -RssLimitMb 2048 -FuzzerSeed 50001 -FreshCorpus

# Stage B - focused, with a recorded engine seed so the run is reproducible.
powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 `
  -Mode utf16 -MaxTotalTime 1800 -MaxLen 56 -Timeout 5 -RssLimitMb 2048 -FuzzerSeed 50002 -FreshCorpus

# Stage C - independent confirmation: fresh corpus, same seeds, a DIFFERENT engine seed.
powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 `
  -Mode utf16 -MaxTotalTime 300 -MaxLen 56 -Timeout 5 -RssLimitMb 2048 -FuzzerSeed 50003 -FreshCorpus
```

Then replay the whole corpus **twice** and compare, exactly as for the metamorphic target. Retain a
finished corpus by renaming it (`artifacts/corpus-utf16-stageB`) before the next `-FreshCorpus` run;
`artifacts/` is gitignored and the script has no corpus-directory override.

Report `new_units_added` (new-unit **events**) separately from the final corpus size (**net**
growth): `REDUCE` replaces a unit in place, so the two never match and quoting one as the other
overstates coverage. And `cov:` in the libFuzzer log counts edges in the C++ driver shim, **not** in
`KatLang.dll` — the .NET signal is `ft:`.

### Triage

For every crash, invariant failure or non-deterministic replay: keep the raw payload, replay it
deterministically, record the reconstructed code units as four-digit hex, identify the template and
placement, minimize, and classify. Never substitute a printable character for a malformed code unit
to make a reproducer readable — report the code units.

| Class | First question |
|---|---|
| decoder / replay-encoding / template defect | Does the payload still rebuild the same code units? |
| invalid relation or invariant assumption | Does the precondition actually hold, and does the bound measure what it claims? |
| fingerprint defect | Do two genuinely different outcomes share a fingerprint? |
| parser forward-progress defect | Which token offset repeats, and what should have consumed it? |
| lexer / parser / frontend exception | Which code unit reaches which unguarded path? |
| out-of-range span / invalid line-column | Which coordinate convention was assumed, and which one holds? |
| CRLF accounting / lone-CR policy | Is a `'\r'` being counted as a column or as a line? |
| surrogate handling inconsistency | Is one path per-code-unit and another per-scalar? |
| unintended normalization | Where did the code units stop being the source's? |
| string-literal preservation defect | Do the literal's units survive to the evaluated value? |
| diagnostic non-determinism / state isolation | Does A/B/A reproduce it? |

A production fix must preserve or explicitly document the index base, endpoint convention, code-unit
indexing, line/column convention, CRLF treatment, EOF span behaviour and recovery-node span
behaviour. A coordinate-policy change is a design decision to report, not something to apply in
passing — and normalizing source text is never a blanket fix.

### Current limitations

* Only the templates and code-unit tables above are generated. The raw modes reach arbitrary code
  units but not arbitrary *structure*, so deeply nested or very long shapes arrive only by mutation.
* Evaluation is limited to the string bridge. This is not evaluator fuzzing.
* No module loading, no downloader, no network path, in any mode.
* Editor-tooling surfaces (`src/KatLang/Semantics/`) are covered by their own target — see
  [Editor-tooling fuzzing](#editor-tooling-fuzzing).
* The `Unexpected character` diagnostic embeds the offending code unit verbatim, so for an isolated
  surrogate the message string is itself ill-formed UTF-16. Faithful in memory, and U+FFFD at any
  UTF-8 boundary downstream. Pinned by a contract test; changing it is a diagnostic-surface decision,
  not a fuzzing one.

## Editor-tooling fuzzing

`KATLANG_FUZZ_MODE=editor` (source: `KatLang.ParserFuzz/Editor/`).

### What it is

The editor target fuzzes the **semantic model** editor tooling in `src/KatLang/Semantics/`
(`SemanticModelBuilder` / `SemanticModel`) — the layer KatLangWeb builds classification, hover,
symbol lookup, go-to-definition, document-symbol and signature data from. It proves that editor
tooling, over arbitrary and malformed source: never crashes; stays deterministic; returns only valid
UTF-16 source ranges; agrees with the real lexer/parser/front end; never invents a symbol; never
leaks a synthetic helper; keeps comments and strings out of identifier classification; resolves
dotted and ordinary calls to the same callable; and remains isolated across requests and small edits.
A structured "no result", an ordinary diagnostic, or a declined unresolved-`load` request is a good
outcome; an unexpected exception, an out-of-range or self-inconsistent span, a resolution to a
differently named or non-existent symbol, or a non-deterministic result is a defect.

### Registered surfaces (only what exists)

The whole model is built and every core invariant is checked for every case; the surface dimension
selects which query is driven and which observation the fingerprint records. Only surfaces that
actually exist are registered:

| Surface | Driven query |
|---|---|
| classification | `IdentifierResolutions` — classification + occurrence kind per identifier |
| position resolution (hover) | `FindResolutionAt(line, column)` |
| property/signature at position | `FindPropertyAt(line, column)` + `PropertyInfo.Signatures` |
| symbol lookup | `FindResolutions` / `FindDeclarations` / `FindProperties` |
| navigation (go-to-definition) | `IdentifierResolution.ResolvedDeclaration` |
| document symbols / outline | `Declarations` + `PropertyInfos` |
| signature metadata | `PropertyInfo.Signatures` / `GetParameters` |

**Unsupported and therefore not modelled:** there is no completion provider, no active-parameter
signature-help service, and no incremental parser in the repository. Cases that would exercise those
use the nearest real surface instead; the harness invents no product feature to raise coverage.

### Case model, UTF-16 and cursor/edit coordinates

The payload is **not** source text: a frozen 13-byte payload selects a template, a UTF-16 code-unit
group and member to inject into its hole (reusing the Phase 5 UTF-16 tables so isolated surrogates
stay representable), a placement, a line-ending encoding, an execution mode, a cursor placement, and
a bounded edit. Nothing grows with an encoded integer; bytes past the prefix are ignored.

* **Source** is exact UTF-16 code units (`ImmutableArray<ushort>`), built once to a `string`.
* **Coordinates.** `SourceSpan` is 1-based, end-inclusive, columns in UTF-16 code units, `\n`-only
  line breaks with `\r` transparent — the same model the shared `SourceSpanValidator` enforces. The
  cursor is stored as an exact UTF-16 offset for replay and converted to (line, column) for the query
  through that one model; an out-of-range `PastEndOfFile` cursor deliberately queries past the last
  line, whose documented contract is a `null` resolution.
* **Edits** transform the exact code units (insert/delete/replace, add/remove dot/comma/delimiter,
  add/remove one star of the supply marker, LF↔CRLF, complete/break string, token-based rename), and
  the tooling is re-run from a **fresh
  request** on the edited source. There is no incremental editor API in the repository, so the target
  exercises full rebuild after each edit; a fresh request on the *original* source after the edited
  one is processed must reproduce the original result exactly (no stale-source leak).

### Oracles

Layered, and Lean is deliberately not among them:

* **Lexer** — token spans and (line, column), and comment/string token regions the classifier must
  not overlap.
* **Parser / front end** — the AST the model is built from; the model must not invent an occurrence,
  and every occurrence's source slice must equal its reported name.
* **Runtime metadata** — `BuiltinRegistry` supplies the allowed builtin names and fixed-arity plain
  parameter counts; the harness re-declares no arity.
* **Lean** — **not used.** Editor tooling makes no claim about representable KatLang *value*
  semantics; completion, hover, cursors, spans, recovery, and ordering are not modelled in Lean.

### Metamorphic relations and their preconditions

Compared on a span-free **shape signature** (the sorted set of
`(occurrence kind, classification, name, resolved-declaration name)` tuples), so a transform that
legitimately shifts offsets is compared on structure:

* **whitespace-neutral** — duplicating a space that sits strictly between two tokens cannot change
  resolution structure. Skipped when there is no such inter-token space.
* **line-ending-neutral** — LF and CRLF encodings of one assembled source resolve identically.
  Skipped when the source supplies its own `\r` or has no line break.
* **rename** — renaming every occurrence of a uniquely-scoped user symbol to a fresh name reproduces
  the structure with the name mapped, and the old name vanishes. Skipped without a clean model or a
  suitable symbol.
* **unrelated-declaration** — appending a fresh non-shadowing declaration leaves every existing
  symbol's resolution unchanged. Skipped without a clean model.
* **dotted-ordinary** — `F(A, …)` and `A.F(…)` resolve to the same callable declaration (`A.F(B)`
  means `F(A, B)`, receiver as one leading argument boundary). Only on the dotted/ordinary template.

### Synthetic-symbol, list/sequence/collecting-binding and dotted-call policy

Synthetic implementation names (deconstruction `$deconstruct$N` helpers and anything with `$`, all
declaration-span-free) must never surface as an occurrence, declaration, property, hover, or outline
symbol. The list/sequence/collecting-binding and spread distinctions are inherited from the elaborated AST the
model projects and are recorded as a fingerprint dimension; the model reports the receiver of a
dotted call as one leading argument boundary, never a spread.

### Replay and seeds

```powershell
# replay every curated seed; each case runs twice, so non-determinism is itself a failure
dotnet run --project fuzz\KatLang.ParserFuzz -- editor-replay fuzz\KatLang.ParserFuzz\EditorTestcases

# replay one payload straight from a mismatch report
dotnet run --project fuzz\KatLang.ParserFuzz -- editor-replay --payload 0E010000000000060000000000

# replay recorded crash/corpus artifacts, whose CONTENT is the raw payload
dotnet run --project fuzz\KatLang.ParserFuzz -- editor-replay --raw fuzz\artifacts\crashes-editor
```

`EditorTestcases/seeds.txt` is the tracked corpus. Like the metamorphic and UTF-16 seeds it stores a
**template payload**, not source text — `template=<id> bytes=<hex> desc=<note>` — and the declared
template is checked against the one the payload decodes to. `editor-seeds OUTDIR MANIFEST`
materializes the raw payloads as a libFuzzer seed corpus.

### Running a campaign

```powershell
# Stage A - smoke. MaxLen is a small multiple of the 13-byte decoder prefix, not a round number.
powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 `
  -Mode editor -MaxTotalTime 300 -MaxLen 64 -Timeout 5 -RssLimitMb 2048 -FuzzerSeed 70001 -FreshCorpus

# Stage B - focused, with a recorded engine seed so the run is reproducible.
powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 `
  -Mode editor -MaxTotalTime 1800 -MaxLen 64 -Timeout 5 -RssLimitMb 2048 -FuzzerSeed 70002 -FreshCorpus

# Stage C - independent confirmation: fresh corpus, same seeds, a DIFFERENT engine seed.
powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 `
  -Mode editor -MaxTotalTime 300 -MaxLen 64 -Timeout 5 -RssLimitMb 2048 -FuzzerSeed 70003 -FreshCorpus
```

Retain a finished corpus by renaming it (`artifacts/corpus-editor-stageB`) before the next
`-FreshCorpus` run; `artifacts/` is gitignored. Replay the whole corpus **twice** and compare, as for
the other targets. As always, `cov:` in the libFuzzer log counts the C++ driver's edges, **not**
`KatLang.dll`; the .NET signal is `ft:`, and new-unit **events** are not the same as **net** corpus
growth.

### Triage

For every crash, invariant failure or non-deterministic replay: keep the raw payload, replay it
deterministically, record the reconstructed code units as hex, identify the template, surface, cursor
and edit, minimize, and classify as exactly one of — decoder / edit-application / replay defect;
invalid relation; semantic-oracle defect; fingerprint defect; span-validation defect; stale-source
leak; scope leak; synthetic-symbol leak; classification / hover / navigation / document-symbol /
diagnostic-conversion defect; dotted-call disagreement; builtin-metadata drift; list/sequence/collecting-binding
documentation drift; UTF-16 coordinate defect; parser-recovery interaction; unexpected CLR exception.
A structured "no result" is never a finding, and broadening a "no result" to silence a mismatch is
never a legitimate fix.
