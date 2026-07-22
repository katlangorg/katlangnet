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

### Phase 1: the one supported family

`dotted-collection-call` — the ordinary receiver-first call against its dotted spelling:

```katlang
Output = count(range(1, N))      # left
Output = range(1, N).count       # right
```

These are equivalent because KatLang *defines* the dotted form as the ordinary call: `A.F(B)`
means `F(A, B)`, and for the fixed-arity collection builtins the receiver fills the single
`collection` parameter. The dotted form is a spelling, not an optimization, so it is legitimate
to demand exact equality rather than an inequality.

`N` is chosen from a small fixed table. KatLang's `range` is **inclusive** and counts downward
when `start > stop`, so it always yields at least one element: there is no empty range,
`range(1, 1)` (one item) is the smallest form, and `range(1, 0)` descends to two items. The
template therefore knows each case's exact cardinality, which is how limits are placed just
below, exactly on, and just above the materialization boundary.

### Declared relations

* **Semantic — `SemanticEqual`.** Success/failure outcome, neutral structural value, emitted
  count, innermost structured error kind, and — for resource limits, whose payloads are
  machine-independent counts — the structured payload. Error *prose* and source context are
  deliberately excluded: they may legitimately differ between two spellings of one call.
  A resource-limit stop stays distinguishable from an ordinary semantic failure.
* **Operational — `ExactMaterializationEqual`.** Exact equality of materialized
  collection-item slots and materialized string UTF-16 units, plus the same resource-limit
  verdict. Evaluation steps and peak dynamic depth are recorded for diagnostics but are **not**
  failure conditions: the repository's established contract for this pair
  (`OperationalMetamorphicTests.DottedAndOrdinaryForms_ChargeExactlyTheSameWork`) establishes
  materialization equality, and nothing claims the two forms share one definition of a "step".

Observations come from the run's own `EvaluationBudget`, obtained through
`Evaluator.RunCountedObserved`. Nothing re-evaluates, nothing rebuilds a value, there are no
static counters, each side gets a fresh budget and a fresh zero-argument property cache, and
the executor verifies afterwards that observing left every counter untouched. The two sides
deliberately *share* one immutable `EvaluationLimits` instance, because "reused limits carry no
run state" is one of the properties worth exercising.

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

`KatLang.ParserFuzz/MetamorphicTestcases/seeds.txt` is the tracked corpus. A metamorphic seed
is a **template payload**, not a source file — storing sources would duplicate text the
template regenerates deterministically — so each line is
`family=<id> bytes=<hex> desc=<note>`. The declared family is redundant on purpose: replay
checks it against the family the payload decodes to, so a stale seed is reported instead of
silently replaying a different case. `metamorphic-seeds OUTDIR MANIFEST` materializes the raw
payload bytes as a libFuzzer seed corpus.

### Adding a trusted template later

1. Add a `MetamorphicFamily` value and its id in `MetamorphicCase.FamilyIdOf`.
2. Append it to `MetamorphicDecoder.FamilyTable` (byte 0 selects it; existing seeds keep their
   meaning as long as the current entries keep their indices).
3. Add a `Build…` method in `MetamorphicTemplates` that **constructs** the pair and states the
   equivalence argument in a comment. If the family needs a dimension the current payload does
   not carry, extend the byte layout — do not overload an existing dimension.
4. Declare the relations the construction actually justifies. Use an inequality (optimized ≤
   generic, cached ≤ rebuilt) whenever the implementation is *permitted* to do less; exact
   equality is only for pairs that are two spellings of the same work.
5. State the family's real preconditions in `CheckPreconditions`. A rejected case is counted
   and reported, never silently skipped and never a mismatch.
6. Add curated seeds and extend `MetamorphicFuzzHarnessTests` (its parameter-space sweeps are
   exhaustive, so a new dimension is covered automatically once the tables list it).
