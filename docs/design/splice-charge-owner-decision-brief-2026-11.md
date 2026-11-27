# Charging shared module imports against the aggregate

**Owner decision requested, November 27, 2026. Recommend C′.** Keep the existing source charge. At each cache-hit splice, charge the sum of the source lengths of the distinct canonical modules in the cached view, including the module itself. A diamond then counts its shared dependency once within that splice. Each subsequent materialization pays again for the closure whose units it may visit. For the 25-module Fibonacci case, this reduces the aggregate from 12,078,961 to 29,714 UTF-16 code units. A directly spliced leaf keeps exactly its current charge.

The decision turns on which shared work survives. The existing front end can reuse a wide dependency's contents, but a new materialization still visits its distinct nested units. Charging only the directly spliced module (C) would charge a fixed 59 units in a control where each warm selection visits 3, 6 or 10 census units. C′ gives a conservative bound without multiplying a dependency by the number of paths to it. Its cost is that a wrapper over one wide library can still reach the cap even when the library's width adds little measured work.

The finding was `modules-deferred-splice-weight-exponential` in the November 21 performance investigation at `8947d21e`. Reviewed on `main` at `512a0c1c`. The live Constitution assigns source admission to host policy. MOD-09 preserves identity by canonical URL and says “Every cache-hit splice is still charged.” Production continues to use its documented charge pending the owner's decision. [Current rule](language-rules/evaluator-and-hosting.md#source-loading-and-deferred-modules) · [MOD-09](../constitution/constitution.md#mod-09--one-module-per-canonical-url-per-compiled-program-every-load-and-every-open-of-it-is-the-same-declaration) · [Lean/C# alignment](../../dotnet/src/KatLang/SEMANTIC-ALIGNMENT.md)

## Current accounting and prior repairs

`ModuleLoader.FetchAndSpliceAsync` reserves each downloaded text accepted for parsing. On successful completion it caches the increase in the aggregate over the module's entire walk. `ProcessLoadAsync` reserves that cached weight on each subsequent admitted splice. For a successful walk, `W(m) = length(m) + Σ W(target)` over the load occurrences the walk actually spliced. A load inside a deferred clause enters the account when the clause materializes. A series of `d` diamonds has `2^d` paths to its deepest shared leaf, although the resolver downloads that leaf once.

| Earlier change | Effect on today's accounting |
| --- | --- |
| Q-31/Q-32, October 6 | One prelude-rooted declaration per canonical URL. Sharing that declaration retained the charge at each splice. |
| Audit F4, November | An unpublished deferred attempt releases splices in its own and unfinished nested ledgers. Parsed source and completed nested frames keep their charges. Eager cancellation has its own frame rollback. |
| Deferred lookup-cache take-back, November 17, and completed-content sharing, November 23–25 | Less retained and recomputed work per materialization. The cache-hit reservation still uses the original transitive weight. |

The existing `DiagnosticBudgetTests.SpliceWeight_IncludesEverythingTheModulesOwnLoadsCharged` covers a parent that loads its child twice. The new tests distinguish multiplicity at several depths, exercise a deferred splice of an eagerly resolved DAG, and pin a written dependency excluded from the splice.

## Source, occurrences and work

The downloader served a deterministic in-memory map on Windows x64. Source sizes below are ASCII file bytes, with no BOM. The **declared** column includes the root and all supplied module texts, even unselected ones. **Resolved modules** counts only downloaded module bytes, once per canonical URL, excluding the root. The host charges `string.Length` in UTF-16 code units. The ASCII figures agree numerically with those lengths. For non-ASCII source they can differ. `MaxAggregateSourceLength` defaults to 8,388,608 **code units**.

**Sites (hits)** gives the number of actual load occurrences processed and, in parentheses, how many were cache hits. **Paths** counts all root-to-module occurrences in the unfolded graph, including the first occurrence of each module. **Allocation** is a work proxy measured as the median of three warmed Release runs on the parse route, or the engine route for selections. It includes work outside module elaboration. The separate stage counters below measure elaboration directly.

| Case | Declared B | Resolved modules B | Sites (hits) | Paths | Allocation MiB | A, full-run code units |
| --- | --: | --: | --: | --: | --: | --: |
| One module | 63 | 13 | 1 (0) | 1 | 0.3 | 63 |
| One URL twice in one scope | 145 | 13 | 2 (1) | 2 | 0.4 | 158 |
| `open 'm', 'm'` | 121 | 13 | 2 (1) | 2 | 0.4 | 134 |
| One URL in 8 scopes | 659 | 13 | 8 (7) | 8 | 0.8 | 750 |
| Two URLs, identical text | 170 | 26 | 2 (0) | 2 | 0.4 | 170 |
| Diamond, two parents of one leaf | 245 | 145 | 4 (1) | 4 | 0.6 | 258 |
| Branch is the only loader | 112 | 13 | 1 (0) | 1 | 0.6 | 112 |
| Branch after an eager load | 181 | 13 | 2 (1) | 2 | 0.7 | 194 |
| 8 distinct selected branches | 757 | 13 | 8 (7) | 8 | 2.2 | 848 |
| One branch selected 8 times | 150 | 13 | 1 (0) | 1 | 0.7 | 150 |
| Unselected branch | 111 | 0 | 0 (0) | 0 | 0.5 | 98 |
| Fibonacci DAG, 17 modules | 1,775 | 1,726 | 32 (15) | 4,180 | 2.3 | 257,053 |
| Fibonacci DAG, 24 modules | 2,566 | 2,517 | 46 (22) | 121,392 | 3.4 | 7,465,184 |
| Fibonacci DAG, 25 modules | 2,679 | 2,630 | 48 (23) | 196,417 | 3.5 | 12,078,961 |
| Fibonacci DAG, 31 modules | 3,357 | 3,308 | 60 (29) | 3,524,577 | 4.2 | 216,749,245 |
| Duplicate-edge chain, 18 modules | 1,843 | 1,794 | 35 (17) | 262,143 | 2.2 | 15,336,006 |
| Diamond ladder, 49 modules | 3,816 | 3,767 | 65 (16) | 262,141 | 5.5 | 15,991,744 |
| Layered library, 19 modules | 7,806 | 7,755 | 172 (153) | 262,144 | 4.5 | 16,188,104 |
| Chain / star of 33 modules | 2,212 / 2,074 | 2,161 / 508 | 33 (0) | 33 | 3.6 / 2.7 | 2,212 / 2,074 |
| Eager DAG plus selected branch, 23 modules | 2,854 | 2,705 | 45 (22) | 150,048 | 4.1 | 10,277,799 |
| Library in 69 eager scopes | 127,214 | 121,780 | 69 (68) | 69 | 133.5 | 8,408,254 |
| Same library behind 69 importer modules | 131,351 | 127,556 | 138 (68) | 138 | 138.0 | 8,412,391 |
| Same library in 80 selected branches | 129,900 | 121,780 | 80 (79) | 80 | 190.5 | 9,750,520 |

Full-run totals and allocations above come from an instrumented build with a raised cap. The stock build refused the 25-module case at the `m22` splice of 4,613,664 units, which would bring the aggregate to 12,078,961. It refused the 23-module eager-plus-deferred case during selection after a clean parse, and the 80-branch library at its 69th selection. The 31-module total exceeds the stock ceiling by calculation. Its default-limit verdict was not separately recorded. A full-run total can exceed the attempted total of the first refused splice.

For all 13 small controls, the instrumented charge equalled the smallest admitting stock limit found by binary search. Median allocations differed by at most 0.19%. Across the larger recorded campaign, 147 successful route runs covering 117 distinct programs matched the model. One further program exceeded even the raised cap. Its final attempted total matched the prediction, while its committed total stopped below the cap. The four alternative prototypes each matched the model on 17 programs.

## Which work repeats

From 5 to 31 Fibonacci modules, measured parse allocation rose from 0.83 to 4.16 MiB. The charge rose from 726 to 216,749,245 code units. This establishes the disparity on that family. Import-path multiplicity alone says little about the work of other module shapes.

Marginal allocation per additional opening scope or materialized branch, in **KiB**:

| Route and range | 20-unit module | 1,000 members | 4,000 members | 16,000 members |
| --- | --: | --: | --: | --: |
| Eager parse, 256 to 1,024 scopes | 62.9 | 64.2 | 58.5 | 62.5 |
| Semantic model construction alone, same scopes | 7.1 | 7.0 | 6.2 | 5.3 |
| Engine evaluating each eager scope, 1 to 256 scopes | 69.0 | 79.9 | 89.1 | 69.7 |
| Engine, branches opening the library, 1 to 64 | 248.6 | 449.8 | 684.6 | 2,101.6 |
| Engine, branches opening a small wrapper over the library, 1 to 64 | — | 251.3 | 263.4 | 261.8 |

The eager slopes show no consistent width-proportional increase across the sampled libraries. Direct deferred splices do show one. Above the small-module baseline, the two larger libraries cost 3.67 and 3.75 allocation bytes per source code unit per additional branch. Each observation includes parsing the larger calling program and evaluating its extra branch. The wrapper samples show little sensitivity to the **width of one leaf**. These allocation differences do not isolate a cost at the second splice or establish that transitive work is zero.

An independent control varied the **number of distinct nested modules** while holding the root at 298 code units and the directly spliced module at 59. The root eagerly loads `top`. Three separate branches open it. `top` holds one hub, which holds one, four or eight different leaves with identical text. The production loader used a synchronous in-memory downloader and the default limits. Each branch materialized with a fresh `FrontEndTraversalObservations` instance.

| Distinct leaves | Downloads during eager parse | Eager loader expansions / signature bodies | Warm census units / completed view reuses per selection | Warm gate edges / admission edges | A charge per selection | C | C′ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 3 | 19 / 13 | 3 / 5 | 5 / 98 | 133 | 59 | 133 |
| 4 | 6 | 31 / 19 | 6 / 8 | 5 / 98 | 319 | 59 | 319 |
| 8 | 10 | 47 / 27 | 10 / 12 | 5 / 98 | 567 | 59 | 567 |

The second and third selections each gave the displayed warm counts and made zero downloads. `CompletedModuleCensusReuses` counts distinct completed declarations in the census. `CompletedModuleViewReuses` includes reuse in the gate, load check and admission measure. `StaticStructureAdmission.MeasureLoadedBody` follows nested units. `SharedBodyCensus.OfLoadedBody` processes the stored bodies and nested edges of each census unit. These visits survive reuse of the inner member trees. Source units remain a conservative proxy for that work. [Admission measure](../../dotnet/src/KatLang/StaticStructureAdmission.cs) · [Shared-body census](../../dotnet/src/KatLang/SharedBodyRegions.cs) · [Materialization observation method](../../dotnet/tests/KatLang.Tests/CompletedModuleSpliceTests.cs)

## Options

All figures are aggregate UTF-16 code units. Bold totals exceed the default limit. Prototype comparisons used the same programs and downloader.

| Case | A. today | B. deduplicate, every re-splice free | B′. deduplicate eager re-splices only | C. own text | **C′. distinct resolved closure** |
| --- | --: | --: | --: | --: | --: |
| Fibonacci DAG, 25 modules | **12,078,961** | 2,679 | 2,679 | 5,083 | 29,714 |
| Fibonacci DAG, 31 modules | **216,749,245** | 3,357 | 3,357 | 6,439 | 47,189 |
| diamond ladder, 49 modules | **15,991,744** | 3,816 | 3,816 | 5,420 | 31,847 |
| layered library, 21 modules | **64,752,392** | 9,525 | 9,525 | 62,598 | 295,319 |
| eager DAG + branch re-opening its top, 23 modules | **10,277,799** | 2,854 | 2,981 | 5,432 | 30,699 |
| 4,000-member library in 69 scopes | **8,408,254** | 127,214 | 127,214 | **8,408,254** | **8,408,254** |
| 4,000-member library in 1,024 scopes | **124,787,543** | 206,603 | 206,603 | **124,787,543** | **124,787,543** |
| library opened by 80 selected branches | **9,750,520** | 129,900 | **9,750,520** | **9,750,520** | **9,750,520** |
| small module over the library, 256 selected branches | **31,223,734** | 148,669 | 169,834 | 169,834 | **31,223,734** |

- **A. Retain the unfolded charge.** Keeps every present boundary and needs only documentation. The 25-module case remains refused although its 48 written sites require 25 downloads.
- **B. Count admitted source alone.** Frees every cache hit. It removes the source-aggregate bound on repeatedly materializing a branch over the same completed library.
- **B′. Free eager hits and charge each deferred hit its own text.** Admits wide eager reuse and keeps the direct-leaf protection. It would amend MOD-09's every-hit qualification and misses the increase in warm nested-unit visits.
- **C. Charge accepted source plus the direct module text at each hit.** A small change that retains the charge on every splice. It protects direct width and removes path multiplication, but a fixed-length wrapper can represent different amounts of repeated work, as the control shows. Its total can still grow as the product of site count and direct module size.
- **C′. Charge accepted source plus the distinct resolved closure at each hit.** A view with many paths to one leaf pays for that leaf once within the hit. A later hit contributes the same closure again. This preserves protection for direct width and nested-unit visits. It remains conservative for a small wrapper over one wide leaf, for wide eager reuse, and for repeated selections where much of the work has already been shared.

## Proposed contract for C′

1. Retain today's charge for the root and for **each download accepted for parsing**, including retried uncached source. All reservations use UTF-16 code units and the existing single aggregate limit.
2. For each successfully cached module, define its closure as its own canonical URL plus the union of the closures of targets actually spliced while building that cached view. Sum the accepted source length for each canonical URL in the set once. Two distinct canonical URLs contribute separately even if their contents match. An unselected directive contributes nothing, even if another part of the program has already loaded its URL. A later branch materialization charges its own loads.
3. At an eager or deferred cache hit, reserve that closure sum once after the existing admission and cycle checks. A refusal reports `AggregateSourceLengthExceeded` at the existing source site with the new quantity and attempted total, and uses the existing missing-module recovery. Describe the quantity as “UTF-16 code units of distinct resolved module source”. The reservation precedes use of the view.
4. Keep the present rollback boundaries. An unpublished deferred attempt releases its own and unfinished nested frames' splice charges. Admitted downloads and completed nested frames keep theirs. Eager cancellation releases the abandoned frame's reservations as today. A later hit on a previously completed module still pays, including after an unpublished attempt. This proposal gives no prepayment credit.

For every completed view, `own length ≤ distinct closure length ≤ current unfolded weight`. With the same downloader responses, walk and publication history, each reservation on a previously admitted trace still fits. A refusal may disappear, move later, or expose another existing limit. The aggregate is a source-admission bound. Other limits, cancellation, and per-materialization work accounting continue to apply.

## Compatibility evidence

The stock baseline passed the 831 pre-existing tests in 12 selected accounting and module-identity classes plus the initial nine new test cases. The table records changes observed in scratch prototypes. The prototypes kept the original diagnostic wording. “Wording only” identifies a separate text assertion to update for the proposed wording.

| Test | B | B′ | C | C′ |
| --- | :-: | :-: | :-: | :-: |
| `DiagnosticBudgetTests.SpliceWeight_IncludesEverythingTheModulesOwnLoadsCharged` | flips | flips | flips | flips |
| `DeferredRegionSourceAccountingTests.UnfinishedNestedModules_ReleaseTheirSplicesAndKeepParsedSource` (both rows) | flips | flips | flips | – |
| `SourceProcessingLimitsTests.CachedRepeatedModule_IsDownloadedOnce_ButEverySpliceChargesTheAggregate` | flips | flips | wording only | wording only |
| `DiagnosticBudgetTests.DistinctScopeSplices_EachChargeTheAggregate_AndStopAtItsLimit` | flips | flips | – | – |
| `ModuleLawPostCommitReviewTests.SharedDeclarations_DoNotRefundWrittenSpliceSourceCharges` | flips | flips | – | – |
| `DeferredRegionSourceAccountingTests`: `TransientFetchFailures_…`, `CancellationDuringADownload_…`, `AttemptAbandonedDuringTheCompile_…`, `Residual_SiblingCompletedByACancelledAttempt_…` | flip | – | – | – |
| `CompletedModuleSpliceTests.ALowAggregate_RefusesTheSameSplice_InEveryMode` | flips | – | – | – |
| **Existing tests flipped** | 11 | 6 | 3 | 1 |

Under C′, the existing numerical change is `DiagnosticBudgetTests.SpliceWeight_IncludesEverythingTheModulesOwnLoadsCharged`. Its outer module names the inner one twice. Its first walk still charges both written loads, but a later splice of the outer module charges the inner text once. The two unfinished-nested-module rows continue to verify their existing totals. The compatibility table for the new tests gives the results to use if the owner selects a different policy.

| Test | Pins | Today (A) | B | B′ | C | C′ |
| --- | --- | --: | --: | --: | --: | --: |
| `ImportDag_ChargesTheGraphUnfoldedIntoATree` | Smallest admitting total of a depth-3 diamond ladder; the refused splice and its quantity | 1,855 (`t2` re-splice of 781) | 792 | 792 | 1,027 (111) | 1,560 (499) |
| `SharedLeaf_IsChargedOncePerImportPath` (depth 1–4) | Code units charged per code unit of the shared leaf | 2, 4, 8, 16 | 1 | 1 | 2, 2, 2, 2 | 2, 3, 4, 5 |
| `DeferredSelection_ReSplicingTheEagerImportDag_ChargesItsUnfoldedWeightAgain` | Run total at the selection, a clean parse below it | 1,700 (parse 919) | 637 | 748 (parse 637) | 872 (parse 761) | 1,405 (parse 906) |
| `DistinctUrlsWithIdenticalText_AreTwoDownloads_AndNoSplice` | Identity is the URL; two source charges, no splice | 139 | same | same | same | same |
| `SelectedBranches_EachChargeTheModuleAgain_SoRepeatedMaterializationStaysBounded` | The deferred bound | 302 | **278, bound lost** | 302 | 302 | 302 |
| `UnselectedBranch_DoesNoSourceWork` | No download and no charge for an unselected branch | root only | same | same | same | same |
| `ReSplice_ExcludesAnUnselectedDependencyAlreadyCachedElsewhere` | A dependency named only in a deferred clause was downloaded elsewhere. Its non-ASCII text is charged in UTF-16 units | 376 | 281 | 281 | 376 | 376 |

The thresholds are for complete runs. Where B makes a final splice free, one unit below the threshold can now fail during an earlier download. `ModuleIdentityTests.CanonicalAliases_AreOneDeclaration_AndOneFetch`, `DistinctCanonicalUrls_AreDistinctDeclarations_EvenWithIdenticalBytes`, and `ModuleLawPostCommitReviewTests.ManyHolders_CostOneModuleAcquisitionAndOneElaboratedMember` cover identity independently of the quantity charged.

## On owner approval

- Compute the closure from successfully spliced module identities and accepted source lengths in the existing fetch/cache path. `CachedModule.LoadTargets` also contains deferred written targets for cycle checking and cannot supply this set. Avoid rewalking a closure on every hit. Cache its total with the completed view and bound construction and storage by the module-count limit.
- Pin the C′ column, the eager and deferred refusal sites, UTF-16 units, unchanged downloader/cycle/rollback behavior, and the actual default-limit results of the shared-DAG cases. Keep hand-written expected totals for the small fixtures. Verify that all counters and diagnostics for other limits retain their established behavior.
- Update the source-loading rule and summary, `docs/dotnet.md`, the source-processing alignment row and the rationale in the loader, source-limit and diagnostic XML comments. On **MODA**, record the owner's contract and resulting revision in the live Constitution, with the aligned docs and test names. Lean has no loading or source-budget model. A production accounting change requires V3 on the final tree, including its affected slow-tier classes and all seven Lean targets.

## Verification of this decision brief

This is V1. The deliverables are documentation and one compatibility test class. The focused test projects build their dependency closures. Run the compatibility class, the module-identity and source-accounting witnesses above, the maintained-document checks and the CLI documentation guard. The review records the exact filters, counts and exit codes with the handoff. The stock and prototype measurements, generators, probe source, compatibility logs and review records are local investigation artifacts under `artifacts/validation/splice-charge-decision-2026-11-27/`. The prototype results describe alternative policies and are separate from final-candidate validation.
