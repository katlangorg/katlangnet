# Seeded randomness (September 2026)

KatLang's random operations — `Math.Random` / `random` and `Math.RandomInt` /
`randomInt` — draw from ONE run-scoped random stream. A host may seed that stream
(`RunOptions.RandomSeed`, the direct `Evaluator.Run*` overloads that take a
`long? randomSeed`, and the CLI's `--seed <integer>`), in which case the run's
random values are reproducible; without a seed the stream starts from fresh
entropy and evaluation stays nondeterministic. This document pins the INTERNAL
stream contract exactly, because a seed makes every raw word the evaluator
consumes observable.

The public contract lives on `RunOptions.RandomSeed`; the compact rule is in
`AGENTS.md` and `docs/design/language-rules/evaluator-and-hosting.md`
(§ Seeded randomness); the implementation is `src/KatLang/Evaluation/RandomSource.cs`
and the two samplers in `src/KatLang/Evaluator.Expressions.cs`.

## 1. Seed → initial state

For a supplied signed `long seed`:

```
state = unchecked((ulong)seed)
```

The bit pattern is the state. There is no absolute value, no sign folding, no
pre-hashing or pre-mixing, no `int` truncation, and no skipped initial word, so
all 2^64 `long` values name distinct streams (`-5` and `5` differ; `-1` starts at
`0xFFFF_FFFF_FFFF_FFFF`; `long.MinValue` and `long.MaxValue` are ordinary seeds).

## 2. The generator: SplitMix64

`SplitMix64RandomSource.NextUInt64()` produces every raw 64-bit word exactly as
published by Vigna (`splitmix64.c`), under unchecked (wrapping) arithmetic:

```
state += 0x9E3779B97F4A7C15

z = state
z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9
z = (z ^ (z >> 27)) * 0x94D049BB133111EB
z = z ^ (z >> 31)

return z
```

- The state is advanced BEFORE mixing; the first output of seed `0` is
  `0xE220A8397B1DCDAF` (the published reference vector).
- Constants: increment `0x9E3779B97F4A7C15`, mixer 1 `0xBF58476D1CE4E5B9`,
  mixer 2 `0x94D049BB133111EB`. Shifts: 30, 27, 31.
- No other SplitMix64 variant (different constants, a mixed seed, a skipped
  word) may be substituted; the repository's deterministic test helpers use the
  same convention, and `RandomSourceTests` pins published known-answer words for
  seeds `0`, `1`, `-1`, `long.MinValue`, and `long.MaxValue`.

## 3. 128-bit composition

```
hi = NextUInt64()
lo = NextUInt64()
return ((UInt128)hi << 64) | lo
```

`hi` is drawn first. Reversing the word order changes every seeded
`Math.RandomInt` result.

## 4. Uniform bounded 64-bit draws

`RandomSource.NextInt64Below(maxExclusive)` returns a uniform value in
`[0, maxExclusive)` for a positive signed 64-bit bound by REJECTING the top
incomplete cycle of the 64-bit range and then reducing modulo the bound —
never plain modulo (which biases every bound that does not divide 2^64) and,
in this implementation, never Lemire multiplication:

```
if maxExclusive <= 0:
    throw ArgumentOutOfRangeException      # before any word is consumed

bound = (ulong)maxExclusive
rejected = (ulong.MaxValue % bound) + 1     # fold bound to zero below
if rejected == bound:                       # bound divides 2^64 exactly
    rejected = 0

do:
    draw = NextUInt64()
while rejected != 0 and draw > ulong.MaxValue - rejected

return draw % bound
```

- A bound of `1` still consumes exactly one raw word and returns `0`. Draw
  consumption is part of the stream contract: skipping the word would shift
  every later value.
- An invalid bound (`<= 0`) fails immediately and consumes nothing.
- Rejection can consume a variable number of words, so removing an earlier
  random call is not a fixed "shift" of the later values.

## 5. The samplers (unchanged by seeding)

Seeding changes where the raw words come from, not how the language values are
formed; both samplers are exactly the pre-seeding algorithms.

`Math.Random(start, end)`:

1. validate — finite bounds, `start < end`, finite range — returning the
   existing error BEFORE any word is consumed;
2. `high = source.NextInt64Below(10^17)`, then `low = source.NextInt64Below(10^17)`
   (high always first);
3. the unit fraction is `(high * 10^17 + low) * 10^-34` in exact Decimal128
   arithmetic — the uniform lattice `{k * 10^-34 | 0 <= k < 10^34}`;
4. scale with the existing `start + fraction * (end - start)`, an accidental
   upper endpoint folding back to `start`.

`Math.RandomInt(start, end)`:

1. validate — whole-number bounds within `±1e34`, `start < end` — before any
   draw;
2. the span is the exact `Int128` difference; the rejected-word count is
   `2^128 mod span` (computed as `(UInt128.MaxValue % span) + 1`, folded to zero
   when the span divides 2^128);
3. the largest accepted word is `UInt128.MaxValue - rejectedWordCount`;
   draw `source.NextUInt128()` until the draw is at or below that word, then
   `start + (draw mod span)`; a unit span still consumes one 128-bit draw.

## 6. Run-scoped lifetime

The stream is run-scoped MUTABLE state, exactly like the budget counters:

```
RunOptions.RandomSeed  (or a direct Evaluator.Run* randomSeed, or CLI --seed)
        ↓
KatLangEngine / Evaluator entry point
        ↓
run-entry funnels (Run, RunCounted*, RunObserved, the *Async twins, PrepareSynchronousRun / PrepareAsyncTwinRun)
        ↓
PrepareAdmittedRun → EvaluationBudget.Create(limits, hostOperations, cancellationToken, randomSeed)
        ↓
EvaluationBudget.RandomSource   (RandomSourceFactory.Create(seed, entropyProvider))
        ↓
every copied EvalCtx shares the budget reference
        ↓
EvalNativeCall / EvalNativeCallAsync → ApplyMathNative(name, args, ctx.Budget.RandomSource)
```

- One source per evaluator run, shared by every nested call, callback, loop
  frame, property evaluation, the engine's `DisplayDecimals` evaluation, and both
  random operations in every spelling; context copies, loop frames, callback
  contexts, and async suspension/resumption never duplicate or reset it.
- `RunOptions`, `EvaluationLimits`, and `HostOperations` hold immutable
  configuration only; no static, thread-local, `AsyncLocal`, or seed-keyed cache
  holds generator state. Reusing one `RunOptions` object for sequential runs
  replays the stream from its beginning; concurrent runs sharing one object get
  independent stream instances initialized from the same seed. No lock exists on
  the source — evaluator access within a run is sequential, even when an async
  continuation resumes on another thread.
- The engine's additional-error evaluation after an evaluable load failure is
  its own run and receives the same configured seed (a fresh stream).
- `Parser.Parse` / `Parser.ParseAsync` ignore `RandomSeed`; the front end, module
  loading, elaboration, and editor semantics never touch the stream.

## 7. Unseeded initialization

An unseeded run (`RandomSeed == null`) constructs the SAME SplitMix64 source,
seeded from the runtime's entropy exactly once at `EvaluationBudget`
construction time (never lazily on the first random call):

```
Span<byte> bytes = stackalloc byte[8]
Random.Shared.NextBytes(bytes)           # exactly once per run
state = ReadUInt64LittleEndian(bytes)    # the full 64-bit state domain
```

`Random.Shared.NextInt64()` is deliberately not used — it cannot return the
whole 64-bit domain. After initialization the evaluator never touches
`Random.Shared` again. The entropy provider is a plain parameter of
`RandomSourceFactory.Create(long? seed, Func<ulong> entropyProvider)`: a supplied
seed never consults it, tests pass a scripted provider, and there is no settable
or ambient default.

## 8. Version-stability policy

For a given KatLang version: the same program (loaded module contents and any
`DisplayDecimals` property included), the same seed, and the same semantically
executed KatLang path produce the same random values on every supported
platform. Synchronous versus asynchronous entry points, optimizer strategies
(planned loops, fused sequence pipelines), and unrelated `EvaluationLimits` that
do not change the program's actual control flow never alter the stream. A seed is
a reproducible stream, not memoization: which calls execute and in what order is
decided by the ordinary evaluation rules (left-to-right arguments, once-only
written arguments, lazy `if` branches, the zero-argument property cache, explicit
`A()` re-evaluation, callbacks in sequence order, output rows before
`DisplayDecimals`).

The exact stream is NOT promised across KatLang versions: it may change when the
generator, a sampling algorithm, or evaluation semantics deliberately change,
and such a change must be release-noted. Host-operation results are the host's
responsibility and outside the guarantee. KatLang randomness is not
cryptographically secure.

## 9. Tests and oracles

`RandomSourceTests` pins §§1–4 and §7 against published SplitMix64 vectors, an
independent BigInteger derivation, and the test-side reference implementation
(`tests/KatLang.Tests/Randomness/ReferenceRandomOracle.cs`, which re-derives
§§2–5 from this document without calling production code). `RandomFractionSamplingTests`
and `RandomIntSamplingTests` script the bounded and 128-bit seams respectively
and keep the pre-seeding mathematical coverage. `SeededRandomnessTests`,
`SeededEvaluationOrderTests`, `SeededOptimizerParityTests`,
`SeededAsyncEvaluationTests`, `SeededConcurrencyTests`, the `SeededStream`
scenario of the concurrency corpus, and the CLI tests pin the public contract;
program-level expectations are derived from the oracle, never captured from the
implementation.
