# R-1 open-target admissions: owner decision brief (November 27, 2026)

**Owner decision requested.** When a retained cell consumes a name selected through opens, should its
input record include the target steps required to reach that selection? We recommend recording the
admitted local-only steps of every consulted level, including targets that offered no such name.
PROP-08 currently records only the open-provided member's admission on this route. HP-20h/i and
`R1_AnOpenTargetsLocalOnlyPathStep_IsNotRecorded_OpenTargetQualification` pin that policy.
[Constitution, PROP-08](../constitution/constitution.md) · [Formal correspondence ledger, R-1 (QUALIFIED)](formal-correspondence-ledger.md).

Shared Agents task `97b49ca24ca54a51ba0c66e34aadac60` (completed execution
`38f632c9249d47b9b06d9522f8232716`) reports the two read orders and the detached direct refusal.
Its independent review leaves the unrelated target question for the owner. The published commit
`c9116ed6` and triage baseline `ad04bd3a` (0.9.0) are both ancestors of the reviewed main,
`662b2435`. The returned-callable investigation has its own task.

Classification (`dotnet/src/KatLang/SEMANTIC-ALIGNMENT.md`, the exposure-enforcement row): an approved rule
changes the observable outcome of misclassified and host-built trees, so it needs Lean first, then the C#
twins and parity tests.

## The qualification

`c9116ed6` records the admitted access of a local-only member that an `open` PROVIDES. The lexical lookup
reports the admission (Lean `ResolvedProperty.openRefusal`, C# `ResolvedLexicalProperty.OpenProvider`).
The evaluation that consumes the selection then notes it (`noteOpenAccess` / `AdmitOpenAccess`). The
member steps of an `open` TARGET's path are access-checked as well, but by the level's open resolution,
and those admissions are not noted:

```
Cap(meta r) = r
F(y) = {
  open Box.Sub
  Box = {
    public Sub = {
      public G(x) = x + 1
      y
    }
    0
  }
  A = Cap(G(0)).Algorithm
  P = A(5) + 0
  A(5), P
}
F(1)
```

`Sub` is local-only through its output row. `G` captures nothing. Correctly classified, `F(1)` is
`(6, 6)`. With `P` falsely exported, the reuse of `A`'s cell is not refused in either row order. Yet
`P = G(5) + 0`, the sibling's own use, is refused at the step: `LocalOnlyProperty` naming `Sub` of
`Box`. No wrong value is known, but the reuse admits an access that the exposure law forbids to the reader.

## Trace: where the target admissions are made, and which lookups consult them

**Lean.** `lookupLexicalPropertyNoted` calls `lookupLexicalPropertyRaw`. When the owner walk misses, that
calls `lookupOpenPropertiesInChain`, then `lookupOpenProperties` for the head level, then
`lookupOpenPropertiesInParentChain` for each enclosing level over `Algorithm.forOpens`, until a level
decides. At each consulted level, `lookupOpenProperties` pushes the level as the site and calls
`resolveAllOpens`. After skipping repeated written keys, it validates the open forms, then calls
`resolveOpen` in written order. The first failure ends the lookup before selection. Each success
produces a `ResolvedOpen` with the display key, original expression and library. Two paths make
target-step checks with `memberAccessible?`:

- `resolveAlgForOpen` (the `.dotMember` arm) checks each dotted step;
- `openStructure` / `openNavigateWith` checks each step of a crossed transparent reference's static path
  (`open L` with `L = Box.Sub`), in the consulted level's context.

After resolution, targets with the same semantic provider identity count as one offer, named by its
first occurrence. A unique public offer is checked at the reading site and carries `openRefusal`.
Multiple public offers yield `ambiguousOpen` before any offered member is access-checked. Lean
re-resolves every consulted level on each lookup. The judgment is
state-free (`MemberSettled.sf_lookupOpenProperties`). `noteOpenAccess` notes the member alone
(`memberAccessActivation?`).

**C#.** `LookupLexicalNoted` calls `LookupLexicalRaw`, then `LookupLexicalStructural`. On a miss, it calls
`LookupOpensInChain`. That uses `LookupOpens` with `HeadOpenLevel` for the head level, and
`LookupOpensInParentChain` with `EnclosingOpenLevel` for enclosing levels. A level state takes its
memoized providers (`MemoizedOpenLevel`: the activation's `OpenLevel` or the scope's `StaticOpenLevel`,
for the same level object, the same run, and `ResolvedOpenLevel.AnswersWatermark`). Otherwise it resolves
them: `ResolveOpenLevel`, `ResolveAllOpens`, `ResolveOpen`, then `ResolveAlgForOpen` and
`ResolveOpenPropAccess` for each dotted step, or `OpenStructure` for each reference step. Each step goes
through `IsAccessibleFrom(…, noteAdmission: false)`. C# uses the same two deduplication stages.
Each `ResolvedOpen` retains the display name, expression and library. The published `ResolvedOpenLevel`
contains the identity-deduplicated providers and the resolving watermark. A failure is returned directly.
`SelectOpenHit` checks the uniquely offered member without a note
and carries `OpenProvider`. `LookupLexicalNoted` then calls `AdmitOpenAccess`, `IsAccessibleFrom`,
`AdmitMemberAccess` and `AliasCellInputs.Note`, for the member only.

- A memo for the same level and run answers readers at or below its verified watermark. It can
  answer a higher watermark if the level's chain contains no activation with a serial in the
  half-open interval between the two watermarks. It can then raise the verified bound.
- In the direct-use witnesses, detaching `F` removes the activation needed by `Sub`. A warm memo
  from the attached read cannot answer. Resolution in the detached context fails at `Sub`.
- The retained cell in these witnesses computes reattached. Its consuming read can use the memo.

**Cold and memoized levels, observed.** All four C# routes give the same counts.

- COLD: no row reads through `F`'s opens before the cell exists. One resolution, two consultations, one
  reuse. The resolving consultation is the supply-time classification of the callee `G`
  (`ReferenceReachesRuntimeAlias`: a raw `LookupLexicalRaw` with the input record removed). The consuming
  `.Algorithm` projection (`LookupLexicalNoted`) then reads the memo.
- MEMOIZED: the row reads `G(1)` first. One resolution, three consultations, two reuses. Every
  consultation by the cell's computation is a reuse.

So the lookup that would have to note an admission usually does not run the access check at all, and the
consultation that runs it is a raw re-read that must record nothing. That is the defect class the review
of `c9116ed6` found.

**Who consumes a selection.** The callers of `LookupLexicalNoted` / `lookupLexicalPropertyNoted`: the callable
and value lookups, a supplied name's projection, a receiver head, the `.string` receiver, and an alias's
static step and route decision. The following are re-reads that consume nothing: `WrittenCalleeBinding`,
`ReferenceReachesRuntimeAlias`, `DotPathReachesRuntimeAlias`, the planner's `ResolvesToBuiltinAlgorithm`
(inside a retained computation it already declines an activation-dependent open hit), and the front end's
promotion probe.

## Which admissions are dependencies of the retained computation

A lookup that consults a level succeeds only if EVERY target of that level resolves in the reading
context, because resolution is fail-fast and precedes selection. Each target step's access check reads the
owner activations it requires (`memberAccessActivation?` over the step's container). So:

1. Every admitted local-only step of every target of every CONSULTED level is an input of the selection,
   through the least owner activation that it requires. The consulted levels run from the head outward up
   to and including the deciding level. Unrelated targets count (HP-22i: `G` from `Other`, refused at
   `Sub`), and so do levels consulted without deciding (HP-22k).
2. A level beyond the deciding one is never consulted, so it is no input (HP-22r).
3. A name the owner walk finds consults no open, so no admission is an input (HP-22m).
4. An exported step needs no activation (HP-22p, HP-22q). Merely opening a runtime reference's
   own namespace adds no read. Any local-only prefix actually checked while resolving a path still counts.
5. A failed lookup delivers an error to its caller. The recommendation preserves that error and
   records no target admissions from that lookup. This is a policy choice. An attached failure can
   differ from a detached reader's own failure because the latter can fail earlier (HP-22n/o).
6. An admission through an activation that the cell's own computation created is the cell's own work,
   not an input (the existing `CellInputs` watermark rule).
7. The provided member's own admission is already recorded.

For a successful open selection this follows E-18 (3), which charges the reader for the target
walks of all consulted levels. Static exposure can conservatively charge a declaration's own dotted
opens even when a lookup never reaches them. A runtime note requires an actual consumption.
[Open, exposure, and accessibility](language-rules/ownership-and-lookup.md#open-exposure-and-accessibility-k1-08).

**When to record them.** Record them where the selection is CONSUMED inside a retained cell's computation, as
the member is now. Never record them in the resolution, because a memoized level and a raw re-read would
diverge. Visit levels nearest first, distinct written targets in resolution order, each path's checks
in traversal order (including checks inside references), then the provided member. Two differently
written targets may resolve to the same provider. Preserve admissions from both walks before merging
their offers. A repeated written key makes only one walk. That is the order in
which a detached direct evaluation meets them, so a refusal names the step that the reader's own use
names. Record them from facts carried by the resolved level (C#: computed with the providers and memoized
with them; Lean: returned by the state-free lookup), so a cold and a memoized level record the same thing.

## Witnesses (current outcomes, Lean and C# alike)

`HP-22a…s` of `HostParentDifferentialCorpus` (generated guards in `lean/CoreTests/HostParentDifferential.lean`;
`lake build CoreTests` passed) and `DetachedExportedEvaluationTests` § 5d on the optimized, generic, async
and genuinely suspending routes. "Mis" means `P` falsely exported. "Direct" is the mis-exposed sibling's own
use `P = G(5) + 0`.

| Witness | Classified | Mis, `A` read first | Mis, `P` first | Direct |
| --- | --- | --- | --- | --- |
| `open Box.Sub` (HP-20h, HP-20i, HP-22a) | `(6, 6)` | `(6, 6)` | `(6, 6)` | `LocalOnlyProperty` `Box`.`Sub` |
| `open L`, `L = Box.Sub` (HP-22b–d, HP-22s) | `(6, 6)` | `(6, 6)` | `(6, 6)` | `LocalOnlyProperty` `Box`.`Sub` (at `L`'s row) |
| memoized level, the row reads `G(1)` first (HP-22e, HP-22f) | `(2, 6, 6)` | `(2, 6, 6)` | `(2, 6, 6)` | `LocalOnlyProperty` `Box`.`Sub` |
| unrelated local-only sibling `open Box.Sub, Other`, `G` from `Other` (HP-22g–i) | `(6, 6)` | `(6, 6)` | `(6, 6)` | `LocalOnlyProperty` `Box`.`Sub` |
| consulted, non-deciding level: `F` opens `Box.Sub`, the root opens `Other` (HP-22j, HP-22k) | `(6, 6)` | `(6, 6)` | `(6, 6)` | `LocalOnlyProperty` `Box`.`Sub` |
| failing sibling `open Other, Lib.Inner`, `Inner` capturing `Lib(p)`'s `p` (HP-22l) | `LocalOnlyProperty` `Lib`.`Inner`, both orders | — | — | — |
| lexical shadowing by `F`'s own `G` (HP-22m) | `(6, 6)`, both orders | — | — | — |
| ambiguity (host tree where `Sub` and `Other` both offer `G`, HP-22n/o) | host-supplied local-only `P` gives `AmbiguousOpen` `G` | `AmbiguousOpen` | `AmbiguousOpen` | `LocalOnlyProperty` `Box`.`Sub` (attached: `AmbiguousOpen`) |
| exported step, direct and through `L` (HP-22p/q) | `(6, 6)`, both orders | — | — | — |
| nearer deciding level (`Mk` opens `Other`, HP-22r) | `(6, 6)`, both orders | — | — | — |

The C# tests also pin the following: `open Other, Box.Sub` (the step refusal moves to that span); the
open-level counts above; an attached, correctly classified sibling `Q` through the step, the reference and
the unrelated target in both orders; and, for every genuinely exported control, the value, ticks and
alias cells of the same run with detachment disabled. For the ambiguity, a host renames a member
after a clean parse. The test supplies the exposure flags of that tree. For the failing sibling
and ambiguity in `A`-first order, the suspending cache is installed and the error precedes its
first access. The `P`-first runs reach that cache and suspend.

## Candidate rules

| Rule | What is recorded | Outcome on the witnesses | Assessment |
| --- | --- | --- | --- |
| A: keep the qualification | the provided member only (today) | mis-exposed successful reuses keep `(6, 6)`, or `(2, 6, 6)` with the priming read | No additional work. The reader's own use still fails at the target step |
| B: the providing target's path | the steps of the target that provides the selected name | refuses `open Box.Sub`, `open L` and the memoized level; leaves the unrelated sibling (HP-22g/h) and the consulted non-deciding level (HP-22j) unrefused | Records less than fail-fast resolution reads and less than E-18 charges, so the gap remains. It needs per-provider admissions, and an ambiguity has no providing target |
| **C: every admission of every consulted level, at consumption (recommended)** | target steps on a consumed selection, followed by the provided member | the table below | Follows E-18 (3) on successful selections. Cold and memoized levels supply the same facts. Lean keeps a state-free lookup |
| C′: note during resolution | whatever a resolution checks | C# notes nothing on these witnesses: in both cold orders the resolving consultation is the classification probe, with no input record, and a memoized level runs no check. Where a consuming read does resolve, the note also lands before a failed selection (see C2) | The outcome depends on which read happens to resolve the level first, and on the route. Impossible in Lean's state-free lookup. It reintroduces the unused-selection defect class of `c9116ed6` |
| C2: also record admissions on a failed selection | checked target steps before an ambiguity | predicts `LocalOnlyProperty` `Box`.`Sub` for the falsely exported `P` in HP-22n | A target refusal can take precedence over the ambiguity from the reattached computation. Static ambiguity contributes no selected member, and the source front end diagnoses this written ambiguity |

## Recommended rule: C

**Rule.** Inside a retained runtime-alias cell's computation, an evaluation that consumes a lexical
selection made through the opens records the following as input reads:

- every admitted access of a local-only member step of every target of every level the lookup consulted,
  from the head outward through the deciding level, for dotted target steps and for the steps of crossed
  transparent references alike;
- then the provided member's admission, as today.

Each read goes through the least owner activation the step requires. The refusal it gives a reader
that detaches that activation is the step's own: `LocalOnlyProperty` naming the step's receiver as
written and the step's member, as the reader's own resolution reports it.

The admissions are carried from the resolution to the consumer:

- In Lean, `resolveOpen` would return the provider and the ordered target admissions. Gather the
  admissions before `resolveAllOpens` deduplicates `ResolvedOpen.lib`. A level that misses the
  name must return its admissions alongside the miss so the parent-chain walk can carry them to a
  later hit. `noteOpenAccess` would note the combined list in order after a successful selection.
- In C#, the resolved level state computes them with its providers and memoizes them with the providers.
  `LookupLexicalRaw` accumulates the consulted levels' admissions, and `AdmitOpenAccess` notes them first.

A raw re-read records nothing, and neither does a failed lookup (an ambiguity, a refused or never-passing
target, an unknown name), nor a name the owner walk finds. The reuse judgment, the served watermark, the
late refusal and the demand-decides rule are unchanged.

**Exact outcomes the owner would approve.** Spans are `(line, column)` in the witness source. Lean
carries the same structured payload without spans.

| Witness | Classified | Mis, `A` read first | Mis, `P` first |
| --- | --- | --- | --- |
| HP-20h / HP-20i, `open Box.Sub` | `(6, 6)` | `LocalOnlyProperty` `A` of "an enclosing call" (the reuse, before the channel runs) | `LocalOnlyProperty` `Sub` of `Box` at the target `Box.Sub` (3:8–3:15) |
| HP-22b / HP-22c, `open L` | `(6, 6)` | `LocalOnlyProperty` `A` | `LocalOnlyProperty` `Sub` of `Box` at `L`'s row `Box.Sub` (12:7–12:14) |
| HP-22e / HP-22f, memoized level | `(2, 6, 6)` | `LocalOnlyProperty` `A` (after the row's `G(1)`) | `LocalOnlyProperty` `Sub` of `Box` (3:8–3:15) |
| HP-22g / HP-22h, unrelated local-only sibling | `(6, 6)` | `LocalOnlyProperty` `A` | `LocalOnlyProperty` `Sub` of `Box` (3:8–3:15; 3:15–3:22 for `open Other, Box.Sub`) |
| HP-22j, consulted non-deciding level | `(6, 6)` | `LocalOnlyProperty` `A` | `LocalOnlyProperty` `Sub` of `Box` at `F`'s target (5:8–5:15) |
| every direct use (HP-22a, d, i, k, o) | — | — | unchanged: `LocalOnlyProperty` `Sub` of `Box` |
| HP-22l failing sibling | `LocalOnlyProperty` `Inner` of `Lib` in both orders, with or without detachment | — | — |
| HP-22n ambiguity | host-supplied local-only `P` gives `AmbiguousOpen` `G` [`Box.Sub`, `Other`] | same ambiguity | same ambiguity |
| HP-22m/p/q/r/s and the attached `Q` controls | `(6, 6)` in both orders | — | — |

The cold order's refusal equals the sibling's own direct use. That is R-1's principle: a reader is
refused the cell exactly as its own use would be. Effects that the cell's computation makes before the
consuming lookup still run once, as for the open-provided member today. A warm reuse is refused before
the channel runs.

**Compatibility.**

- For the successful witnesses whose access requires `F`, the front end charges the walk and the
  local-only reader runs attached. Exported controls either consult no restricted step or stop at a
  nearer level. This supports the expectation of compatibility for correctly classified programs.
- Not proved for all programs: R-1 still does not claim that the notes are all the input reads, and
  exposure stays an input of Lean (Q-59).
- Misclassified and host-built trees change exactly as in the table. The pins that would flip are
  HP-20h/i, HP-22b/c/e/f/g/h/j, the C# qualification test, and the mis-exposed reuse assertions of § 5d.
- No public API or diagnostic wording changes. The refusal is the existing `LocalOnlyProperty` with
  the step's payload, at a new place: the consuming read inside the cell's computation.

**Repeated work.**

- A cold C# resolution already walks the target paths. It must also save each admitted step's least
  owner serial and its diagnostic (receiver, member, exposure and source span). Even a raw lookup
  can populate the memo for a later retained computation. This adds storage proportional to the
  number of admissions until the level state is released. Unmemoized host levels repay this cost
  when consulted. Watermark rejection can also require a new resolution.
- An accepted memo avoids repeating target resolution and owner walks. Outside a retained computation
  the consumer can skip replay. Inside one, carrying the consulted levels and replaying their entries
  costs up to one gated note per admission per consumed lookup, stopping at the first refusal. A note
  that lowers the least recorded serial can propagate to dependent cells. Rule B could replay just the
  providing path but would omit the dependencies exposed by HP-22i/k.
- Lean already re-resolves consulted levels. Returning and combining their admissions adds work and
  space proportional to the evidence carried even though the lookup stays state-free. The current
  counters distinguish consultation, reuse and resolution. They do not measure a proposed policy's cost.

**Implementation outline (after approval; not started).**

1. Lean first. The state-free lookup returns the consulted levels' target admissions (activation and
   refusal), and `noteOpenAccess` notes them before the member. Restate `sf_lookupOpenProperties` and its
   neighbours, and the navigation and member-route laws stated over raw lookups. The `RetainedCellReuse`
   law families cover the new writers as `noteCellInput` steps.
2. C#: `ResolvedOpenLevel` keeps its local-only target admissions. `LookupLexicalRaw` carries the
   consulted levels' admissions to `AdmitOpenAccess`. `ResolvesToBuiltinAlgorithm` declines a selection
   that carries them when planning inside a retained computation. `ResolvedLexicalProperty` is a `readonly record struct` on recursion spines, so
   carry the admissions in one reference and run the stack suites.
3. Flip the pins listed above to the approved outcomes. Regenerate the HP and MayCaptureCalls
   artifacts. Update the ledger rows R-1 and E-22, `evaluator-and-hosting.md` § Detached evaluation of
   exported properties, `ownership-and-lookup.md`, the PROP-08 host contract, and the Constitution
   records. Close R-1's open-target qualification.

## Verification and limits

Run on the final candidate (log paths in the task report):

- the 4 new § 5d tests and the existing qualification test, on four routes each (20 runs);
- the `HostParentDifferentialTests` class, the `MayCaptureCallsLeanArtifactTests` class and
  `MaintainedDocumentationConsistencyTests`;
- `lake build CoreTests` and `lake build KatLangArityLaws`, over the regenerated
  `HostParentDifferential.lean` and `MayCaptureCallsCorpus.lean`.

The recommended outcomes are not executed: no rule is implemented. The only evidence for them is that
each one equals an outcome observed today, either the sibling's own direct use or the existing reuse
refusal of HP-20a. The reason for the two consultations comes from the code path together with the counts. It
was not observed with instrumentation.
