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

`KatLang.ParserFuzz/MetamorphicTestcases/seeds.txt` is the tracked corpus (55 seeds: 13 Phase 1
plus 42 Phase 2). A metamorphic seed is a **template payload**, not a source file — storing
sources would duplicate text the template regenerates deterministically — so each line is
`family=<id> bytes=<hex> desc=<note>`. The declared family is redundant on purpose: replay
checks it against the family the payload decodes to, so a stale seed is reported instead of
silently replaying a different case. `metamorphic-seeds OUTDIR MANIFEST` materializes the raw
payload bytes as a libFuzzer seed corpus.

Two seeds are deliberately **rejected** cases (the rest and arity-mismatched callback
projections), so replay exercises and reports the rejection path rather than only the happy one.

### Current Phase 2 limitations

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
* Optimizer policy is a case dimension inherited from Phase 1, not a relation of its own —
  optimized-versus-generic, cached-versus-rebuilt, entry-point parity, general limit
  monotonicity, and frontend/Unicode transformations are all out of scope here.

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
