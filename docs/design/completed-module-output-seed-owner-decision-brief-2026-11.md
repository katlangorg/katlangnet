# Reusing the output seed of a completed module that a branch holds

**Owner decision requested, November 27, 2026. Prefer A2 for repeated member reads, subject to Q1 and Q2. Defer B.** A2 redirects the superseded resolved root R to the classified view C at the same sealed table T and scope K. It reuses the existing whole-summary entry. On the 4,000-member output-row layout the first selection over earlier content costs 77,216 KiB, then about 370 KiB per selection. Current policy spends about 61,760 KiB each time. A1 retains only the settled output seed for the new entry and needs a separate check on the views used to compute it. It is materially cheaper in live memory when branches hold modules without reading members. Owner approval of A2 should include that retention cost. B would move work and retention to first publication, including modules never read again. All three are proposals.

The brief cites triage task `fe76f3feff744f8ea0e0fa3b95a6527d` at `35270a2b`. The historical measurements quoted here are from the archived review of the subsequent branch-owned repair, task `2e5c2fa9218b44aaaa1ff39266f9d2d1`, commit `7de84650`. This investigation started on clean `main` at `22dd3dd49714adcac9cbc50a2dff89bc5953164e`. [Current module rule](language-rules/evaluator-and-hosting.md#source-loading-and-deferred-modules) · [Lean/C# alignment](../../dotnet/src/KatLang/SEMANTIC-ALIGNMENT.md) · [Pinning tests](../../dotnet/tests/KatLang.Tests/CompletedProviderSummaryTests.cs)

These options concern C# front-end work sharing. Lean does not model the exposure summary or deferred module lifecycle. The acceptance criteria are identical values, exposure metadata, diagnostics and resource charges.

## Where the cost comes from

In `G(n) = { L = load('lib')  …  L.F(n) }`, two exposure requests read the module. Each selected branch is a materialization with its own summary memo.

1. **The property's output seed.** The branch level's summary walk asks `CollectSharedAlgorithmSummarySeed` for the output seed of `L`'s value. That value is the RESOLVED module root R the loader hands to the unit (`ModuleUnitRegistry`). `ChildContext` places R at its own publication: the sealed table T of the operation that completed the module, key K. Exposure has since replaced T's view at K by the CLASSIFIED view C and marked R as the superseded view (`MarkSupersededModuleView`). The request is not exact, so `GetAlgorithmSummary` never keeps it. `CollectScopeBodySummary` walks every member to reach the sibling fixed point that the output rows and opens read.
2. **The member path.** The charge of `L.F(n)` asks for C at its exact completed context. That is `Key(null, K)` in the asking unit's table and `Key(T, K)` at the module's publication. These requests can be kept.

Since 7de84650 a user module with no opens and no output rows skips request 1 (`SummaryMemo.HasEmptyCompletedModuleOutput`). Its seed is empty by construction. In the measured member-read layouts with output rows or opens, request 1 leaves contextual results in the memo. At 40 members, the keep window of request 2 recorded 40 taints per later selection, each a contextual hit on a result from request 1. These selections traverse members twice and publish no entry. A branch with no member read has only the first request.

The probe recorded these facts (scratch probe build of `22dd3dd4`; its output is in the investigation artifacts):

| Fact | Observed |
| --- | --- |
| Context of request 1 | sealed table T of the completing unit; T names C, R carries the superseded mark for T and K; `ModuleUnitRegistry.HasCompleted(R)` |
| R against C | every member body is a distinct object (41 of 41 at 40 members), with the same declaration and the same `Property.Exposure`; output rows are the same objects; open rows are rewritten copies |
| Settled output seed of a module root | `SettledAtPrelude`: no references, no visible names, only required names and owner-qualified parameters. **Empty in every measured layout**, including a lifted root parameter (`q + 1`), a root elaborated to a callable alias (`public K = q + 1` / `K`) and a clause family row |
| Static ledger | identical work, metadata, peak and storage units at every selection, for the baseline, the non-strict A1 prototype and A2, shared or unshared (1,000 members, four layouts). Walks over sealed facts charge nothing; the aggregate source charge is untouched |
| Ownership | `OwnerQualifiedParameter` and `SummaryReference.ContentKey` distinguish owners by reference. With `public FB(x) = T2.Q(x) + Helper(x)`, request 1 binds `FB`'s escaping references to R's `FB` node. Request 2 receives these contextual results, so C's member summary can already carry R's owner nodes within a materialization. The window rejected that summary. Values and exposure metadata agreed on this witness. |

The last row constrains every option. A kept summary must be computed over **one view** of the module. Otherwise later adopters receive owner identities that their own computation would not produce, and the verifying mode cannot always tell: a verifying adopter that walks R first mixes in the same way.

## Measured cost

Release harness on Windows x64, fixed in-memory downloader, six selections, KiB allocated on the materializing thread. Members are `public F_i(x) = Helper(x) + i`, at 1,000 / 4,000 members. Layouts follow `CompletedProviderSummaryTests.Owned`: each branch opens `tiny`, holds `L = load('lib')` and reads `L.F_i(n)`. Values were identical in every run and mode.

| Layout | Today (HEAD), later selections | A1 strict | A2 |
| --- | --- | --- | --- |
| No opens, no rows (control) | 20,218 / 76,959 once (keeps), then 237 / 370 | 20,282 / 77,209 once, then about 237 / 370 | 20,282 / 77,208 once, then about 237 / 370 |
| Output row `F0(3)` | **16,298 / 61,760 every selection**, nothing kept | 16,469 / 62,239, 20,287 / 76,651, then 237 / 370 | 20,287 / 77,216 once, then 237 / 370 |
| Module opens `tiny2` | **16,298 / 61,760** | 16,470 / 62,616, 20,286 / 77,213, then 243 / 375 | 20,288 / 77,214, then 242 / 376 |
| Opens, member reads `Z` | **16,308 / 61,770** | 16,481 / 62,251, 20,299 / 76,663, then 244 / 377 | 20,300 / 77,227, then 244 / 377 |
| Output row, parse completed the module | 18,703 / 71,403 at selection 0, then 16,297 / 61,760 | 18,873 / 72,014, 20,285 / 77,214, then 237 / 370 | 22,690 / 86,613 at selection 0, then 237 / 370 |
| Source report layout (`L.F_i(n)` only) with `F0(3)` | 16,228 / 61,686–62,061 | — | 20,216 / 77,141, then 167 / 297 |
| Branch opens the module (`open 'lib'`), module with a row | 371 / 597 (already cheap) | unmeasured | 370 / 597 |

The historical source layout measured 15,851 / 60,558–60,796 KiB with `F0(3)` and 19,893 / 75,859 KiB for the plain module's keeping selection. A second Release run paired allocation with traversal counters in separate processes on current `main`, using four branches and the second of two rounds. The source layout with `F0(3)` cost about 16,227 / 61,686 KiB at each later selection with sharing enabled or disabled. With an open and a member read it cost about 16,297 / 61,759 KiB. Both made 2,003 / 8,003 member evaluations per later selection, with zero keeps or adoptions. The plain source layout made those same evaluations at selection 1, kept two entries for 20,149 / 76,885 KiB, then made one member evaluation at selections 2 and 3. Without sharing it repeated 2,003 / 8,003 evaluations.

**Retained memory** (heap after full collection with the program alive, shared minus unshared, 1,000 / 4,000 members): today 1,438 / 5,585 KiB for the plain layout's three entries and 0 for modules with rows or opens. A2 and A1 strict retain 1,439 / 5,586 KiB for those modules, the same as the plain layout. A1's own entries hold an empty seed and a key. The non-strict A1 prototype retained 1,494 / 5,805 KiB because its kept member-path entry held seeds computed over R.

**Retention without a member read.** Four branches held `L = load('lib')` but returned `W(n)` from `tiny`. At 4,000 members current policy allocated about 47,781 KiB per later selection with `F0(3)` and 47,779 KiB with an open. A1 strict and A2 both reached about 136–138 KiB. A2 published one whole-summary entry. After full collection its live heap exceeded the current-policy process by 3,100.4 KiB with the output row and 3,100.5 KiB with the open (about 796 KiB in either 1,000-member case). A1 strict was within 1 KiB of current policy in all four comparisons. These are differences between processes with the program alive. A1's separate output store is outside the prototype's whole-summary entry count.

## Options

### A0. A constant empty seed for every completed exact module root

This generalizes the 7de84650 shortcut. It would use no new storage for an output seed. No A0 prototype was measured. Exactness requires every successfully completed, eligible module root to settle to an empty output seed. The representation can retain required names and owner-qualified parameters. The seven probe logs show 88 empty seed observations, including repeated requests. They do not establish the invariant. Keep this option deferred.

### A1. An output-seed-only entry for the exact root, sealed table and scope

This is the source report's proposal. Key `(R, T, K)` by reference. Eligible when no keep window is open, `ModuleUnitRegistry.HasCompleted(R)`, T is sealed, not failed and not the asking unit, `T.Facts(K)` holds a non-provisional body under a completed inherited chain (`HoldsInheritedCompletedBody(K, C)`), and either T names R itself or R carries T's superseded mark for K. The entry stores the output seed only, with the walk's context-independence flag. It is computed inside a keep window, stored only when that window kept every condition and the seed carries no anchored reference, staged by the attempt and published with its unit. Adoption hands out a clone and records context use when the computation used it.

Three requirements follow from the facts above.

- **Dependency views.** R and its members are inputs to the walk, while T names C and C's member views. `NoteProviderWindowBody` consequently taints an R walk. Even the prototype labelled *strict* accepts the same declaration anywhere in T below the root check, without establishing ancestry or exact occurrence. `CompletedStaticStructures.Child` has view-specific paths for ambiguous definitions and projected occurrences. Safe A1 needs an exact R-occurrence to sealed-occurrence correspondence for every differing dependency. Refuse the entry if any pair is ambiguous, provisional or uses an attempt-specific representative. Same declaration, name, URL or source text is insufficient.
- **No view mixing.** The first prototype allowed R-window results to satisfy C windows, publishing C's member-path entry with R's owners. Strict A1 separated the two classes of windows. Its R-window set is shared by all R windows in the memo. Any production version must also establish compatibility between the exact roots, tables, scopes and dependencies of two R windows before treating a memo hit as verified.
- **Origins and verification.** Compare the R output against an independent unshared R walk. A settled root seed contains no anchored reference, so its clone needs no origin translation. Dependency lookups must still select the same provider declaration and origin key, including through opens. Preserve owner-qualified names and context use. Check cancellation on the hit path and publish staged seeds only with a successful unit.

With a member read, strict A1 reaches steady state on the third selection over earlier content. The non-strict prototype spent about 69,869 then 55,613 then 370 KiB at 4,000 members with `F0(3)`, but published mixed owner identities. For the held-only layouts, strict A1 reached steady state on the second selection over earlier content.

### A2. Answer the superseded root through the exact request for the classified view (recommended)

For the proposed redirect, check the registered R, its publication and superseded-view identity, the sealed successful T, K, and `HoldsInheritedCompletedBody(K, C)` before substituting. When T already names R, the ordinary exact request can use R itself. A2 can then return a clone of `GetAlgorithmSummary(C, exactContext: (T, K)).OutputSeed`. The scratch redirect handled only a superseded `Algorithm.User` module. Its alias-root witness therefore exercised the ordinary path. The prototype left the inherited-chain test to `CompletedProviderKey`, which runs after the body has been selected and the memo consulted. A refused keep does not undo substitution. Establish Q1 and Q2 on every redirected path, including an ineligible dependency or a contextual memo hit, or use the original R path for that case.

- **Dependency views.** Reuse the existing strict keep window for C. Unverified contextual memo hits, attempt-specific representatives and provisional body reads prevent publication. A pre-window memo hit can still supply a result to the current computation. An independent comparison must cover it as well.
- **Provider and origin identities.** Preserve each open selection's kind, target scope, `OpenProviderIdentity` and declaring level at the lookup occurrence. Preserve each pending reference's head and member path, bound owners, open path and selection. `StoredForm` strips resolution-local requirement views. At adoption the same key in a foreign sealed table acquires the adopter's requirement view, while an origin relative to the computing unit maps to the adopter's own unit. A settled root output has no anchored references. The whole-summary entry also contains member seeds, which can have them.
- **Ownership.** The `FB` witness exercises member seeds with bound owners. A settled root output can carry owner-qualified parameters despite having no pending references. The effect of replacing one of those owners is an open obligation (Q2).
- **Failed and cancelled attempts.** Keep entries local to the attempt until `ModuleUnits.Publish` runs under the loader gate. A refused, cancelled or abandoned attempt drops its staged entries and leaves previously published ones visible. A retry uses the last successful registry. A1 would need the same boundary for its additional store, including its isolation tests.

With a member read, the first selection over earlier content keeps the summary (20,287 / 77,216 KiB for the output-row layout). Later selections cost about 237 / 370 KiB. When the parse completed that module, selection 0 pays 22,690 / 86,613. The measured ledger is identical across modes for the tested layouts. The held-only result above shows the extra memory cost of retaining C's member seeds.

### B. Keep a unit's own summary when it first publishes (separate decision)

Today the selection that completes the module keeps nothing. Its contexts are its own, so `HoldsInheritedCompletedBody` refuses them. The next selection summarizes the module again and keeps it; with A2 this covers rows and opens too. B would stage, at the first selection, what that selection already computed over R in its own table, so the second selection would adopt.

- **Savings.** The keeping selection: 20,218 → about 237 and 76,959 → about 370 KiB per module completed by a branch and selected again.
- **Costs.** The plain layout's keeping selection minus an unshared selection is 3,926 / 15,204 KiB. This is a proxy for current staging overhead. B's separate owner correspondence and origin handling have no measured upper bound. Today's three-entry steady state (1,438 / 5,585 KiB live) gives a retention comparison for a module selected only once. B's own first-publication entry count and retention are unmeasured.
- **Re-anchoring.** Origins at the computing unit's table must remain T for `Key(T, K)` adopters but must become the adopter's unit for `Key(null, K)` adopters. `Entry.ComputedBy` maps the computing table to the adopter's unit, so B needs two stored forms or key-aware re-anchoring.

## Proof obligations

**Q1 (A2, retargeting at a module root).** Show that independent R and C walks preserve required names, owner-qualified parameters, context dependence and all provider and origin selections used to derive them. `Retarget` and `RetargetProjection` check declaration identity, and `RewriteDotCall` preserves stored dot-edge facts. Neither establishes equality of every child context. `ChildContext` reads carried publications, `Child` can disambiguate by exact view, and exposure can attach a new `DeferredRegion` to a provisional branch. Compare the old R walk with the redirected result in a fresh unshared memo over equivalent lookup facts, including opens, alternate occurrences, reach projections and provisional dependencies. Compare exact owner identities, or use an explicitly justified occurrence mapping. End-to-end equality on empty outputs cannot discharge Q1.

**Q2 (A2, ownership).** Module hygiene places a module's lexical root at the prelude. `TryResolveRequirement` first tests the exact owner against the supplied bound-owner set and calls `NoteMembership(owner, bound)`. Only an unbound owner reaches the chain lookup. Even two absent owners produce footprints indexed by different objects. Establish that substitution preserves membership answers, off-chain handling, subsequent settlement reuse and ledger charges at every consumer, or prove that eligible settled outputs carry no differing owner. The probe found none. Hygiene alone does not prove this obligation.

**R (B, retargeting a whole summary).** Retain an occurrence-specific correspondence from each original body and scope to its final sealed view, including branches and reach projections. A shared body may have several occurrences. Rebuild every owner-qualified parameter, bound-owner reference and derived content key against the correct final owner. Preserve every selected provider, reference path, key, binding region, origin role and context-use decision. Exclude provisional dependencies, later `CompleteLookups` overrides and attempt-local representatives. Verify the staged whole summary against fresh unshared walks of the sealed body for both `Key(T, K)` and `Key(null, K)`, including re-anchoring where the computing table plays two roles. A changed selection, requirement, diagnostic or ledger charge is a semantic difference and rules that entry out. B also needs cancellation and failure isolation after retargeting and before publication.

## Compatibility evidence

The investigation built each scratch alternative into the test project through an MSBuild targets override. The original runs covered six classes (509 tests each): `CompletedProviderSummaryTests`, `CompletedModuleSpliceTests`, `DeferredInlineOpenTargetExposureTests`, `DeferredAttemptCacheRetentionTests`, `DeferredMaterializationCancellationTests` and `DeferredRegionSourceAccountingTests`. Under A2 and strict A1, 502 passed. Seven deliberately pin the current policy's cost and failed under each alternative. The review extended the alternating-URL cases to four selections of each module and added a post-refusal publication assertion.

| Test | Pins | A2 | A1 strict |
| --- | --- | :-: | :-: |
| `BranchOwnedModuleWithOutputOrOpens_SummarizesBothViewsAtEverySelection_AndKeepsNothing` (5 layouts) | both views walked at every selection, nothing kept | flips | flips |
| `BranchOwnedModuleWithOpensOrOutput_UsesTheOrdinaryOutputSummary` (2) | every selection evaluates at least the width | flips | flips |
| `OutputSeedWitnesses_AreTheSameWithAndWithoutTheShare` (14 witnesses) | values, exposure metadata and downloads equal shared, verified and unshared | – | – |
| `AttemptsHoldingAModuleWithAnOutputRow_PublishNothingWhenRefusedOrCancelled` | refused and cancelled attempts publish nothing; reference diagnostics | – | – |
| `ABranchThatCompletesAModule_KeepsNothingOfItsOwn_AndTheNextSelectionKeeps` | today's first-publication policy | – | – (flips under B) |
| Other compatibility cases, including `AdoptedSummaries_AreTheOnesEachMaterializationWouldCompute` | corpus equality, isolation, census, cancellation | – | – |

The sharing-disabled witnesses compare values, exposure metadata of materialized bodies and total fetch counts. Distinct URLs serving identical text exercise declaration separation, and two modules opening different providers of `Z` make selection observable in the result. In the measured programs the settled output was always empty, so these end-to-end observations cannot distinguish exact reuse from returning an empty seed. The current verifier checks adopted entries. It does not compare the substituted root with an independent original walk. Strict A1's experimental second store also needs its own publication and rollback observation.

## On owner approval

- **A2.** Accept the whole-summary retention cost for held-only branches before approving a redirect. Require Q1 and Q2 for every eligible shape. Keep other shapes on the existing path. Test cheap eligibility conditions before computing a context (the prototype added about 0.3% to the plain layout's keeping selection). After a policy change, update the seven cost pins, the rule, the alignment manifest and the class remarks.
- **B, if approved later:** build the R→C node mapping during `RetargetTree`, stage both stored forms with the attempt, and pin its first-selection cost and its retention.
- A production change touches exposure and caching, so it is V3 on the final tree: one fast-tier .NET phase, one `Tier=Slow` run of the classes AGENTS.md names for exposure and deferred branches and for run caches and identity-keyed stores, and all seven Lean targets.

## Verification of this decision brief

The deliverable is V1. It adds tests in `CompletedProviderSummaryTests` and design documentation. From the repository root, build `dotnet/tests/KatLang.Tests/KatLang.Tests.csproj` and `dotnet/tests/KatLang.CLI.Tests/KatLang.CLI.Tests.csproj`. Run `dotnet test <project> --no-build --filter <filter>` with `FullyQualifiedName~KatLang.Tests.CompletedProviderSummaryTests.|FullyQualifiedName~KatLang.Tests.LanguageSpec.MaintainedDocumentationConsistencyTests.` for the library tests and `FullyQualifiedName~CliApplicationTests.MaintainedDocs_NeverNameTheRemovedSeedSpelling` for the CLI tests. Run `git diff --check` and check the untracked brief as well.

Local measurements, probes, prototype sources and test logs are under `artifacts/validation/outseed/`. The paired reviewer run used `HARNESS_SHARE=Shared` and `Unshared` in separate Release processes: `dotnet KatLang.Benchmarks.dll <alloc|counters> <report-prop|report-prop-out|owned-open> <1000|4000> 4 2`. The held-only run used `retained` with `held-only-out` and `held-only-open`. `review/commands.log` records the exact invocations and library fingerprints. These are single-machine allocations and live-heap comparisons. No latency measurement or formal equivalence proof was performed.
