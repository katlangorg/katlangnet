# Lean-model mutation campaign — pilot (2026-11-22)

Tool: `scripts/run-lean-model-mutants.ps1`. Catalog: `scripts/lean-model-mutants.psd1`.
Results (gitignored, machine-local): `artifacts/validation/lean-model-mutants-*/`.

## 1. What it answers

The generated differential corpora compare C# with the Lean model program by program. A decision of
the model that no corpus program observes is held by no shared program: the model, or C#, could take
the other decision and every generated `#guard` would still pass (a hand-written test on one side
may still pin it there). The 2026-11-20 bug hunt found three such decisions with scratch tools (its
findings F02–F04) and proposed a standing check. This pilot turns that scratch evidence into one
repeatable command and measures it on `main`.

The campaign changes ONE decision of the Lean model at a time and asks whether a `#guard` of the
four generated corpora fails:

| Corpus | Module | `#guard` commands |
| --- | --- | --- |
| LanguageSpec | `lean/LanguageSpecCases.lean` | 740 |
| SemanticExplorer | `lean/SemanticExplorerCases.lean` | 3,230 |
| SEM-2C | `lean/CoreTests/SemanticGeneratedCases.lean` | 910 |
| HostParent | `lean/CoreTests/HostParentDifferential.lean` | 648 |

It is ON DEMAND. It is not a validation level, it is not part of `validate-all.ps1`, and no workflow
runs it; a schedule is an owner decision (section 7). The C#-side counterpart, a Stryker.NET
campaign over the C# evaluator, is `mutation-campaign-2026-08.md`.

The technique is the one this repository already used by hand: a mutated copy of the model in a
scratch Lake workspace outside the tree, elaborated with `lake env lean` (the mutation-sensitivity
notes of `differential-observations.md`, and the hunt's scratch driver). The runner follows
`run-semantic-sweeps.ps1` for its diagnostics directory, its record and its exit rule, and
`validate-all.ps1` for the repository snapshot. What it adds is a catalog with recorded
expectations, a baseline, one verdict per mutant, and the check that the checkout is untouched.

## 2. Running it

From the repository root, with PowerShell 7, git and the Lean toolchain of `lean/lean-toolchain`
(elan) installed:

```powershell
# Do the catalog's anchors still apply to lean/KatLang.lean? (under a second, builds nothing)
pwsh -NoProfile -File ./scripts/run-lean-model-mutants.ps1 -CheckCatalog -Groups hunt-gaps,extension,hunt-controls

# The pilot: baseline, then the ten mutants of the groups hunt-gaps and extension (about 26 minutes)
pwsh -NoProfile -File ./scripts/run-lean-model-mutants.ps1

# Every catalogued mutant (17, about 41 minutes)
pwsh -NoProfile -File ./scripts/run-lean-model-mutants.ps1 -Groups hunt-gaps,extension,hunt-controls

# One mutant (baseline plus mutant, about 4.5 minutes)
pwsh -NoProfile -File ./scripts/run-lean-model-mutants.ps1 -Mutants compare-preevaluate
```

Two more switches serve a specific question:

- `-CorpusRevision <commit>` takes the four corpus modules from that commit and keeps the working
  tree's model: what an earlier corpus made of a mutant. `Expect` is not enforced for such a run.
- The five guards in `scripts/LeanMutationWitnesses.lean` run alongside the corpora. The catalog
  requires the indicated witness failures for each entry that names them: the two mutants of gaps
  G1 and G2, written while those mutants survived the corpora (section 6). `-ControlModules
  <file.lean>,...` adds further controls. Their results appear separately from the corpus verdict.

Every run writes a fresh `artifacts/validation/lean-model-mutants-<UTC time>-<pid>/` directory:
`lean-model-mutants.log` (one line per step), `summary.md` (the table and the failing cases),
`results.json` (every failing guard with its line, case and text, every duration, the input
digests) and one log per build and per corpus. The script fails (nonzero exit) when the baseline is
not clean, when a mutant is Invalid, TimedOut or Inconclusive, when a verdict disagrees with the
catalog's `Expect`, or when the run changed the repository.

## 3. Method

- **Fixture.** Each invocation creates a fresh Lake workspace under the system temporary directory
  or the parent supplied with `-Workspace`. A directory inside a checkout must be git-ignored.
  Two campaigns using the same parent have separate inputs and build caches. The workspace receives copies
  of `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, the four corpus modules and
  `CoreTests/StructuralIdentity.lean` (the host-parent module imports it). The model is written
  there per candidate. The run log records the workspace path for inspection and later removal.
- **Baseline.** The unmodified model is built in the fixture (`lake build KatLang
  CoreTests.StructuralIdentity`) and each corpus is elaborated with `lake env lean <module>` (with
  Lean's limit of 100 errors per module lifted, so a mutant's guard count is complete). Any failing
  guard, error or nonzero exit stops the run before the first mutant.
- **One mutant at a time.** A mutant is a list of literal substitutions on the model text. Each
  anchor must occur exactly once and the result must differ from the model; then the mutated copy is
  built and the corpora are elaborated against it.
- **Verdicts.**

  | Verdict | Meaning |
  | --- | --- |
  | Killed | at least one `#guard` of a corpus fails; each failing guard is mapped to its case |
  | Survived | every corpus elaborates cleanly: no committed guard notices the change |
  | Invalid | an anchor matches zero or several times, the substitution changes nothing, or the mutated model does not build |
  | TimedOut | a step passed its deadline and no guard had failed |
  | Inconclusive | no guard failed, and a corpus reported other errors or Lean ended abnormally |

  Only an error on a `#guard` line with Lean's failed-guard message counts as a failing guard. A
  module with other elaboration errors cannot establish a kill. A timeout alone supplies no killing guard.
  A corpus stopped at its deadline, or one Lean aborted, keeps the guard failures printed before
  that, and the result marks its list as partial.
- **Deadlines.** The baseline has none. A mutant step is stopped after the larger of 240 s and six
  times the same step's baseline time in the same run (`-MinimumTimeoutSeconds`, `-TimeoutFactor`).
- **Isolation.** Before the baseline and after the last mutant the run takes the repository
  snapshot `validate-all.ps1` takes (HEAD, porcelain status, index diff, worktree diff, untracked
  content) and the SHA-256 of the nine source inputs in the checkout, and fails if either differs.
  `results.json` also records the bytes actually tested in the fixture, including older corpora
  selected by `-CorpusRevision` and the separate witness modules. A checkout may start
  dirty; do not edit it while a run is in flight.

## 4. The catalog

`Expect` records the verdict of the last measurement, so a later run notices both a lost guard
(Killed became Survived) and a closed gap (Survives became Killed). `RequiredKillers` names guards
that must be among the failing ones.

| Group | Mutant | Rule of the model | The mutant instead |
| --- | --- | --- | --- |
| hunt-gaps | `select-demand-all-first` (F02) | selection demands and validates selectors left to right | demands every selector before validating a position |
| hunt-gaps | `map-right-to-left` (F03) | `map` calls its callback in collection order | maps the rest before each item |
| hunt-gaps | `compare-preevaluate` (F04) | a comparison chain evaluates each operand once | every link also evaluates all later operands |
| extension | `need04-reference-value-at-once` | NEED-04: a callable-bearing occurrence of a repeated name waits while its group has no value anchor | demands its VALUE at once |
| extension | `need04-pending-before-anchor` | NEED-04, mixed schedule: the first value-only occurrence is demanded before the pending callable VALUEs | pending VALUEs first |
| extension | `take-not-a-retained-reader` | `take` over a retained collector reads positions, count first | the ordinary route: whole collection VALUE, then the count |
| extension | `take-first-element-before-count` | `take` over a retained collector validates its count before any element | demands the first element before the count |
| extension | `decon-target-call-reruns-source` | Q-38: `a()` on a deconstruction target reads the shared right-hand side | the called projection invokes its hoisted source with zero arguments |
| extension | `cache-key-local-as-exported` | a local-only binding's cache key carries its declaring owner's binding context | every binding keyed as exported |
| extension | `cache-key-exported-as-local` | an exported binding's key carries its owning invocation only | every binding keyed as local-only |
| hunt-controls | `while-left-to-right` | a `while` round reads its flag row first | forms every row, flag last |
| hunt-controls | `compare-short-circuit` | a comparison chain evaluates past a false link | stops at the first false link |
| hunt-controls | `repeat-count-first` | `repeat` prepares its supply before its count | count first |
| hunt-controls | `cache-pub-1-off` | CACHE-PUB-1: an explicit zero-supply call can establish the entry | it never does |
| hunt-controls | `view-count-demands` | `count` over an argument view or collector demands no cell | demands every cell |
| hunt-controls | `binary-right-first` | a binary operator evaluates left, then right | right first |
| hunt-controls | `cache-owner-d1-off` | CACHE-OWNER-D1: an explicit owner call binds a fresh context | reuses the read activation |

The three `hunt-gaps` and seven `hunt-controls` substitutions are the hunt's own; all ten anchors
still match the current model. The seven `extension` mutants are new: two per rule for NEED-04,
`take` and the cache key, one for Q-38.

Q-38 has no decision of its own in the model. The rule follows from the elaborated projection
wrapper, which reads the hoisted source `$deconstruct$N` by a property-style read, and from the
general cache law. At the explicit-invocation arm of `EvalBody.zeroArgPropertyCalculation`, the mutant
changes the unpacking helper's one argument from a property read to a zero-supply call. Ordinary
lookup still selects that source binding, and the ordinary invocation law preserves established
entries, including those of other owners with the same synthetic name. Section 6 gives the witnesses.

## 5. Results at `02c39b75`

Measured 2026-11-22 on Windows 11, 16 logical processors, Lean 4.35.0, no other build running.
Pilot run directory `lean-model-mutants-20261122T050702Z-60872`: all 17 mutants with the
control module of section 6, every `Expect` met, exit 0, 41.5 minutes. An
earlier complete run the same day (`lean-model-mutants-20261122T035036Z-55560`) gave the same
verdicts and the same guard counts. These timings precede the switch to run-private fixtures. The
Q-38 prototype removed cache entries by source name. The current catalog instead makes one fresh
call of the resolved source. Its two witnesses fail under that narrower perturbation as well.

**Baseline.** No failing guard in any corpus. LanguageSpec 19.4 s, SemanticExplorer 49.5 s, SEM-2C
25.0 s, HostParent 12.7 s, and 23 s to build the model: about 130 s. (In this run Lake reused the
workspace's build of the unmodified model, so the baseline took 110 s.) The other baselines of the
same corpora that day took 127–137 s, the longest with an empty Lake cache.

**Mutants.** Failing `#guard` commands per corpus; "s" is the mutant's whole step time, including
2.3 s for the control module.

| Mutant | Verdict | LanguageSpec | SemanticExplorer | SEM-2C | HostParent | s |
| --- | --- | --- | --- | --- | --- | --- |
| `select-demand-all-first` | Killed | 1 | 0 | 0 | 0 | 129 |
| `map-right-to-left` | Killed | 3 | 0 | 3 | 0 | 130 |
| `compare-preevaluate` | Killed | 1 | 0 | 0 | 0 | 130 |
| `need04-reference-value-at-once` | Killed | Lean aborted | 0 | 0 | 19 | 295 |
| `need04-pending-before-anchor` | Killed | 1 | 0 | 0 | 0 | 129 |
| `take-not-a-retained-reader` | Killed | 1 | 0 | 0 | 0 | 130 |
| `take-first-element-before-count` | **Survived** | 0 | 0 | 0 | 0 | 132 |
| `decon-target-call-reruns-source` | **Survived** | 0 | 0 | 0 | 0 | 129 |
| `cache-key-local-as-exported` | Killed | 0 | 0 | 0 | 4 | 129 |
| `cache-key-exported-as-local` | Killed | 2 | 0 | 3 | 38 | 131 |
| `while-left-to-right` | Killed | 7 | 3 | 13 | 0 | 129 |
| `compare-short-circuit` | Killed | 1 | 4 | 0 | 0 | 130 |
| `repeat-count-first` | Killed | 2 | 2 | 0 | 0 | 130 |
| `cache-pub-1-off` | Killed | 8 | 2 | 0 | 6 | 129 |
| `view-count-demands` | Killed | 5 | 4 | 0 | 0 | 129 |
| `binary-right-first` | Killed | 8 | 6 | 27 | 3 | 132 |
| `cache-owner-d1-off` | Killed | 4 | 2 | 0 | 0 | 130 |

15 killed, 2 survived, none invalid, none timed out. The repository snapshot and the nine input
digests were unchanged by every completed run of the pilot. Both survivors are killed since three
specification cases were added later the same day (section 6, closing G1 and G2).

### F02–F04 and the corpus import

The hunt's corpus cases are on `main` (`02c39b75`, "Expand C#/Lean differential coverage with 395
bug-hunt cases"; that commit does not touch the model). The same three mutants against the corpora
of its parent (`-CorpusRevision 02c39b75~1`, run `lean-model-mutants-20261122T044747Z-56204`,
baseline clean):

| Mutant | Corpora of `309a68fe` (before the import) | Corpora of `02c39b75` | Killing guards the import added |
| --- | --- | --- | --- |
| `select-demand-all-first` | Survived, 0 / 0 / 0 / 0 | Killed, 1 / 0 / 0 / 0 | `hunt-selection-invalid-position-stops-before-later-selector` |
| `map-right-to-left` | Killed, 0 / 0 / 3 / 0 | Killed, 3 / 0 / 3 / 0 | `hunt-builtin-map-callbacks-run-in-collection-order`, `hunt-exposure-self-contained-property-fresh-in-every-call`, `hunt-exposure-dependent-property-evaluated-per-call` |
| `compare-preevaluate` | Survived, 0 / 0 / 0 / 0 | Killed, 1 / 0 / 0 / 0 | `hunt-comparison-chain-operands-once` |

F02 and F04 are each closed by exactly one guard, the case the hunt named. F03 was already killed
before the import by the three members of `sem2b/v1/sys/tick/callback/map` (SEM-2B tick block,
`efb2d0e0`, which landed after the hunt's base); the import adds three LanguageSpec guards.

### The extension rules

- **NEED-04 group order.** `need04-pending-before-anchor` is killed by one guard,
  `hunt-need-repeated-name-value-contribution-anchors` (`Same(P, tick() + 4)`). No host-parent case
  observes the order. `need04-reference-value-at-once` is killed by 19 host-parent guards in 15
  cases (HP-08g–j, HP-09d, HP-14g–n, HP-14s, HP-14t: the NEED-04 callable-identity cases). Twelve of
  the 19 are cache-publication guards (`cacheTotal`, `cacheEntries`): demanding a reference's VALUE
  publishes an entry the rule never creates, and in most of these cases the value observation stays
  the same. The source corpora guard publications on four pilot cases each, so there the same
  effect is invisible. In LanguageSpec this mutant makes the model demand a cyclic reference,
  which never ends: Lean aborts the module after about three minutes with the interpreter's
  deep-recursion error, and the module's guards are lost. A one-off bisect in the scratch workspace
  found the two programs (`reference-cycle-through-an-open-is-no-alias`,
  `reference-cycle-only-the-final-providers-close-is-no-alias`) and, without them, one failing guard
  (`hunt-need-repeated-name-value-contribution-anchors` again).
- **`take` count first.** The route decision is guarded: `take-not-a-retained-reader` fails
  `selective-collector-take-demands-its-prefix`. The ORDER is not: `take-first-element-before-count`
  survives all four corpora (gap G1).
- **Q-38.** `decon-target-call-reruns-source` survives all four corpora (gap G2). The one corpus
  program that calls a target explicitly, `hunt-cache-deconstruction-call-establishes-target-entry`
  (`a, b = tick(), 20` / `a(), a, b()`), cannot see a second evaluation: `a` reads the entry `a()`
  established and `b()` projects the constant.
- **Exported/local cache key.** `cache-key-exported-as-local` is killed in three corpora (43
  guards). `cache-key-local-as-exported` is killed by ONE case, HP-05a ("an unactivated local-only
  host property keys on the ACCESS context"), four guards. No source program of the three source
  corpora tells it apart; whether one can is open (the difference needs a declaring chain without a
  call-owned activation, which a host-built scope has).

### The hunt's other seven mutants

All seven are killed again, now by more guards than in the hunt's table (for example
`cache-owner-d1-off` 4 / 2 / 0 / 0 against 1 / 0 / 0 / 0), because the hunt's cases and the SEM-2B
tick block have joined the corpora since. They are the positive control of the fixture: the runner
reports kills where kills are known.

## 6. Gaps: missing differential witnesses

A surviving mutant is not a defect in either implementation. It says that no generated corpus
program observes the decision. The pilot found two such gaps, G1 and G2. Both are closed now
(below), so no catalogued mutant survives the corpora. For both survivors a candidate witness was
written from the rule text, run in C#, encoded with the real `LeanAstEncoder`, and elaborated as a
control module in the run of section 5: every guard passes on the unmodified model and fails under
the mutant, so neither mutant is equivalent.

| Gap | Rule | Candidate witness | Expected (C# and Lean agree) | Under the mutant |
| --- | --- | --- | --- | --- |
| G1 | `take` validates its count before any element (NEED-07) | `Prefix(*xs) = xs.take(0)` / `Prefix(1 / 0)` | `[]` | fails |
| G1 | | `Prefix(*xs) = xs.take(tick())` / `Prefix(tick(), tick())` | `[2]` | fails |
| G1 | | `Prefix(*xs) = xs.take('a' + 1)` / `Prefix(1 / 0)` | `TypeMismatch` | fails |
| G2 | Q-38: `a()` never re-runs the right-hand side | `a, b = tick(), 20` / `a(), a(), b` | `1, 1, 20` | fails |
| G2 | | `p, q = tick(), tick()` / `p, p(), q` | `1, 1, 2` | fails |

The first G1 witness is the example `call-by-need.md` gives for the rule. The three G1 witnesses
also fail under `take-not-a-retained-reader`.

How much each gap left open, from a one-off build of the 53 hand-written `CoreTests` modules
against each survivor (66 s per build; baseline clean):

- **G1 was a gap of the differential corpora only.** `CoreTests/SelectiveCollectorReads.lean`
  kills the mutant (five guards), and C# pins the same example in
  `SelectiveCollectorReadTests.AcceptanceTable_Values`. Each side was held by its own hand-written
  test; no generated case held both to one program.
- **G2 survived the four corpora.** The separate hand-written `CoreTests` sweep also passed
  with the pilot's Q-38 prototype. C# pins the rule in `DeconstructionExplicitCallDecisionTests`,
  using a host counter. The pilot did not measure `KatLangArityLaws` against these mutants.

### Closing G1 and G2 (2026-11-22)

Three LanguageSpec cases reuse the witnesses' programs, each with a hand-written expectation of the
rule: the C# runner requires it of C#, and the generated guard in `lean/LanguageSpecCases.lean`
requires it of Lean.

| Gap | Case | Program | Expected |
| --- | --- | --- | --- |
| G1 | `selective-collector-take-zero-demands-no-element` | `Prefix(*xs) = xs.take(0)` / `Prefix(1 / 0)` | `[]` |
| G1 | `selective-collector-take-count-error-precedes-elements` | `Prefix(*xs) = xs.take('a' + 1)` / `Prefix(1 / 0)` | the count's type mismatch, not the element's division by zero |
| G2 | `decon-target-calls-reuse-the-shared-source` | `a, b = tick(), 20` / `a(), a(), b` | `1, 1, 20` |

The single evaluation of the shared right-hand side is observable where a counter is: the G2 case
carries a C# probe that appends `tick()` and expects 2, and the existing host-counter rows of
`DeconstructionExplicitCallDecisionTests` pin one evaluation per shared source under repeated
target calls (`a(), a(), b(), a` inside a call, `p, p(), p(), q()` at the root) on six C# routes.
The Lean corpus guard checks all three values. The campaign control `decon_target_call_twice`
also checks that the run finishes with `EvalState.tickCounter = 1`.

The mutants of the two rules before and after, each run with a clean baseline and an unchanged
repository (corpus guards failed, LanguageSpec / SemanticExplorer / SEM-2C / HostParent):

| Mutant | Corpora of `4bce6327` | With the three cases | Killing guards |
| --- | --- | --- | --- |
| `take-not-a-retained-reader` | Killed, 1 / 0 / 0 / 0 | Killed, 3 / 0 / 0 / 0 | `selective-collector-take-demands-its-prefix` and the two G1 cases |
| `take-first-element-before-count` | Survived | Killed, 2 / 0 / 0 / 0 | the two G1 cases |
| `decon-target-call-reruns-source` | Survived | Killed, 1 / 0 / 0 / 0 | `decon-target-calls-reuse-the-shared-source` |

Runs `lean-model-mutants-20261122T214403Z-39680` (`-CorpusRevision 4bce6327`; the corpora and the
model are unchanged since `02c39b75`), `lean-model-mutants-20261122T213000Z-27536` (the two gap
mutants under the old `Expect = 'Survives'`, which the run reported as "Killed, expected Survives")
and `lean-model-mutants-20261122T213637Z-1524` (all three under the updated catalog, every `Expect`
met, exit 0). Baselines took 103–109 s and each mutant 102–104 s. The catalog now records both former
survivors as `Killed` with these cases as `RequiredKillers` and keeps their control witnesses
required; each witness still fails under its mutant.

Thin margins, recorded so that a later corpus edit does not open them silently: F02, F04,
`need04-pending-before-anchor` and `decon-target-call-reruns-source` each die to one guard,
`take-first-element-before-count` to two, and `cache-key-local-as-exported` to one host-parent case.
`Expect = 'Killed'` makes the runner fail if one of them goes.

## 7. Runtime, attribution and cadence

**Runtime.** One baseline is about 130 s and one mutant about 128 s (22.5 s to build the model,
106 s for the four corpora); the mutant that makes Lean abort costs 295 s. The pilot's ten mutants
take about 26 minutes, all seventeen about 41. Every step is a single Lean process, so more cores do
not help; the hunt measured 4–6 minutes per mutant on a machine shared with other builds.
`-CheckCatalog` takes under a second.

**Attribution.** What a failing run means is decided by its class, not by the exit code alone:

| Outcome | Seen in the pilot | Meaning and next step |
| --- | --- | --- |
| A guard fails under a mutant | 15 mutants | the named cases pin the decision |
| Survived | 2 mutants | no corpus program observes the decision; show a witness (control module), then track a corpus case |
| Killed became Survived | — | a guard was removed or weakened: find it from `RequiredKillers` and the last `results.json` |
| Invalid, anchor | not in the catalog (all 17 anchors match); a scratch catalog with an absent and a 520-fold anchor was reported so | the model changed at that site: re-derive the anchor, re-measure the entry |
| Invalid, build | not in the catalog; a scratch mutant calling an undefined operation was reported so | the substitution no longer type-checks, or a proof inside `KatLang.lean` rejects it |
| Lean aborted / TimedOut | 1 mutant, in one corpus: aborted after about 180 s, and TimedOut when the same mutant ran with a 60 s deadline | the abort and case bisection identified recursion in this example. A deadline alone cannot distinguish a loop from a slow host. |
| Baseline not clean | — | the candidate itself fails a guard: not a campaign result; run the Lean phase |

**Recommendation.** Keep the campaign on demand, with these triggers:

1. After a change to `lean/KatLang.lean`: `-CheckCatalog` (under a second). For every anchor it
   reports stale, re-derive it and run that mutant (4.5 minutes each). The model changed in 30
   commits in the 30 days before this pilot, so anchors will go stale regularly; that is catalog
   upkeep, not a semantic signal.
2. When corpus cases are added to close a gap, or removed: the mutants of that rule, before and
   after (`-CorpusRevision` gives the "before" without a second checkout).
3. Before a release, beside the full test tier: the default groups (26 minutes).
4. `hunt-controls` (15 more minutes) only when the runner, the corpus generators or the encoders
   change: it checks the fixture, not a gap.

Not on every pull request: the default set alone is close to the Lean job's 30-minute limit, and
most failures would be stale anchors. If standing automation is wanted, the two forms that fit the
measurements are (a) `-CheckCatalog` as a step of the Lean validation job, which keeps the anchors
honest at the commit that moves them for under a second, and (b) a weekly scheduled workflow on the
pattern of `semantic-nightly.yml` running the default groups and uploading the run directory when it
fails. Nightly is not warranted by seventeen hand-picked mutants. Both are owner decisions and
neither is part of this pilot.

**Growing the catalog.** A mutant costs about two minutes, so thirty fit in an hour. Add one when a
hunt or a review finds a decision that may be unobserved, or when a rule gets a decision of its own
in the model. Prefer a mutant that changes an existing decision; record it when a statement had to
be added (Q-38). Remove a mutant that is shown equivalent.

## 8. Limitations

- The catalog is seventeen hand-picked mutants. It is not a mutation score and supports no
  statement about the decisions it does not list.
- Anchors are literal text. An edit near a catalogued site makes the mutant Invalid until its anchor
  is re-derived; it is never applied to a different place, because every anchor must match once.
- Only the four generated corpora are run. A mutant that only the hand-written `CoreTests` guards or
  the `KatLangArityLaws` proofs reject counts as Survived here (G1 was such a case until its corpus
  cases were added).
- The campaign perturbs the Lean model only. A kill shows that a case pins that decision to an
  expectation the C# runners assert too; it says nothing about C#-only machinery (the front end, the
  optimizer, async routes, host operations).
- A killed mutant has at least one witness. One witness does not show that the rule is pinned in
  every position it applies.
- When Lean aborts or is stopped in a module, the guards after that point are lost and output still
  buffered is not seen, so that module's list is a lower bound. Finding the program a mutant loops
  on is manual.
- A deadline bounds time, not memory. The one aborting mutant held about 2 GB.
- Runtimes are from one quiet desktop; a hosted runner was not measured.

## 9. Follow-ups

1. **G2 (Q-38):** done 2026-11-22, `decon-target-calls-reuse-the-shared-source` (section 6).
2. **G1 (`take` count first):** done 2026-11-22, `selective-collector-take-zero-demands-no-element`
   and the precedence case `selective-collector-take-count-error-precedes-elements` (section 6).
3. **Exported/local key:** decide whether a source program can distinguish
   `cache-key-local-as-exported`; if one can, add it, otherwise note the mutant as host-only.
4. **Cadence:** the owner decisions of section 7 (`-CheckCatalog` in the Lean job; a weekly
   workflow).
5. **Runner:** per-case isolation for a mutant that makes Lean abort, and an optional stage that
   also builds the hand-written `CoreTests` modules, so a survivor is classified in one run.
6. **Catalog:** areas the hunt attacked that have no mutant here (the dot route's declared-first
   order, aliases, META capture, open provider identity) are the candidates for the next entries.

## 10. Maintaining the catalog

- An entry is `Name`, `Group`, `Rule`, `Change`, `Expect`, optional `RequiredKillers`, `Witnesses`, `Note` and
  `Gap`, and `Edits` (`Find` / `Replace` here-strings). Copy the anchor from the model with enough
  surrounding lines to be unique, then run `-CheckCatalog`.
- Measure a new or changed entry with `-Mutants <name>` and record its verdict in `Expect`. Leave
  `Expect` empty only while an entry is being developed: an empty value accepts Killed and Survived.
- After a corpus case closes a gap, the run fails with "Killed, expected Survives". Change the entry
  to `Killed`, name the new case in `RequiredKillers`, and move the gap out of section 6.
- Never edit `lean/KatLang.lean` to try a mutant. The runner's copy lives in the scratch workspace,
  and the unmodified model is written back there when a run ends.
