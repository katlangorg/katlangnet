# KatLang parser fuzzing

Coverage-guided fuzzing harness for the **raw** KatLang parser, targeting:

```csharp
Parser.ParseSyntax(source)   // the raw syntax boundary, before front-end elaboration
```

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
  katlang.dict                  # libFuzzer dictionary of KatLang fragments
  run-campaign.sh               # WSL-side: build driver + run libFuzzer
  README.md                     # this file
  artifacts/                    # gitignored: publish output, corpus, crashes, logs
scripts/
  fuzz-parser.ps1               # Windows-side orchestration (publish + instrument + run)
```

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
