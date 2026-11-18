# Lazy storage for KatLang ranges

**Decision, 18 November 2026. Keep the stored range on `main`.** Computing a range's numbers by index removes about 4 MB per 100,000-item numeric query. The proposed hybrid also changes a successful KatLang run into a division error when a host operation inspects its arguments. This meets the brief's stop condition. The measurements below are from experiments. The deliverable is this design report.

## An observable difference

A .NET host can register this operation through the public API.

```csharp
var same = HostOperation.Create("SameObject",
    (args, _) => new Result.Bool(ReferenceEquals(args[0], args[1])),
    "left", "right");
var options = new RunOptions { HostOperations = HostOperations.Create(same) };
```

```katlang
R = range(1, 3)
if(SameObject(R[0], R.take(1)[0]), 3, 1 / 0)
```

The stored range returns **3**. The proposed hybrid returns **DivisionByZero**. The stored `take` copies the original item reference. The hybrid gives the slice its own atom table. Each list has a stable first item, but the host receives two different objects and selects the other branch. The public types, integer values and ordinary KatLang `==` are identical in this example.

The review replayed the observer against the baseline Release assembly, the proposed assembly in both modes, and the two scratch alternatives. The exact two-line example also parsed with zero diagnostics and returned the structured outcomes above on the selected checkout and the archived hybrid. The following results used a cached `R`, an identity mapper, a predicate accepting every item, and a reducer returning the first item.

| Comparison with the source item | Stored | Fresh box on each read | Memo shared with slices and callbacks | Hybrid |
| --- | --- | --- | --- | --- |
| Another read of the same position, or the corresponding item of `[R*]` | Same | Different | Same | Same |
| Item forwarded by `take`, `skip`, or `distinct` | Same | Different | Same | Different |
| Item kept by `filter` or returned by the identity mapper or reducer | Same | Different | Same | Different |
| First argument received by a mapper, compared with `R[0]` inside the callback | Same | Different | Same | Different |

This also matters to a host examining a completed result containing both the original and the derived list. No host mutation, concurrency, reflection or special numeric value is needed. The recorded source, options and outcomes are identified under **Reproduction** below.

## Representations

On this x64 runtime a `Result.Atom` occupies 32 bytes, an array slot 8 bytes and a `Decimal128` 16 bytes. An inclusive range has at least one item. An empty slice is a separate case.

| Storage | Construction and retained space | Access | Identity and implementation cost |
| --- | --- | --- | --- |
| Stored control | About 40 B per item, including the reference array | Array lookup, zero allocation | One atom per originating position. Copying a position into another value can retain that exact atom. |
| 1. Bounds, direction and count | Constant space in the list | One integer calculation and a 32 B atom for each boxed read. Direct numeric reads allocate nothing. | Small indexed view. Even two reads of the same slot can disagree under `ReferenceEquals`. |
| 2. Bounds plus a per-range memo | Constant at construction. The prototype allocates an 8 B × count table on first boxed access, then 32 B per touched position. A chunked table trades one large allocation for a directory and touched chunks. | Numeric reads allocate nothing. A boxed read calculates and publishes the atom once, then reuses it. Racing first readers may allocate losing candidates. | The canonical box must belong to the **originating position**. Slices need source offsets and every forwarding consumer must use that box. Concurrent publication and the lifetime of retained slices require care. |
| 3. `Decimal128[]`, boxed on demand | 16 B per item up front, about 1.6 MB at 100,000. A stable-box table adds the cost above. | Direct numeric lookup. Boxing costs 32 B on every access, or once per position with a memo. | Handles irregular numeric sequences, at the cost of building and retaining the array. For a unit-step range, its contents are computable from the index. Same forwarding and public-view issues as options 1 and 2. Estimated, no timing run. |
| 4. Run-scoped small-integer atoms | With stored lists, still 8 B per list slot plus the bounded table, its atoms, and uncached items. A formula-backed list can omit the slot array. | A hit reuses an atom, a miss needs an allocation or memo. The table lives until the run ends. | Requires a bound, concurrency policy and exact numeric representation. Equal integers from independent ranges now share a reference. A table restricted to canonical range integers still changes that observation. Estimated, no timing run. |

Two box policies were also combined experimentally. The **hybrid** published one atom per position for public and ordinary item reads, in chunks of 256. For a 100,000-item range the first boxed read allocates a 391-reference directory, one chunk and the atom. Numeric reducers read numbers directly. Callback iteration used a fresh atom, and slices and `distinct` constructed independent range views. A **kept-item variant** retrieved accepted `filter` items from the source memo after testing the predicate. That improves repeated filtering of one range, but leaves predicate arguments and the other forwarding operations distinguishable.

**Option 2 is the candidate for a further experiment if the owner pursues lazy storage.** Keep the numeric path for consumers that only read numbers. Give selection, slices, callbacks, filter output, structural binding, host operations and result export the original atom wherever the stored engine forwards it. The scratch memo prototype shares a root table with offset slices. A small slice can then keep all boxes touched through that root alive. An alternative is to copy just the slice's canonical references, as the stored builtin does. This costs one array and the selected boxes, but bounds what the slice retains. A public array-backed view materialized on first public access is another way to preserve the BCL collection behavior described below. These choices have different retention costs. The fast hybrid's timings cannot establish the performance of a version that satisfies the whole contract.

## Identity and traversal audit

The decisive question at each use is whether it computes a number or hands an existing object to another consumer.

| Consumer | Consequence of fresh boxing | Required guarantee |
| --- | --- | --- |
| `Result.ValueComparer`, `SharedValueComparer`, `EqualsSingleWalk`, `EqualsInOperationWalk`, repeated-name VALUE comparison | Equal numeric leaves still compare by `Decimal128.Equals`. A reference hit saves a scalar comparison. The charged parent walk counts a child inspection before the leaf comparison. Changing an atom reference alone changes cost, not the pure-language verdict or its structural units. | Preserve numeric bits, structure identities, traversal order and charged inspections. |
| `ReferenceClasses`, `CommittedReferenceClasses`, unequal-pair and node-hash memos, shared-value graph complexity guards | Nonempty structured nodes enter the structure memos. A numeric leaf has no descendants or class entry. Fresh boxes can increase allocation without adding class entries or changing the distinct-node work bound. | Keep the list node and its sharing. Changing a canonical list into a newly allocated list elsewhere can change how often a structural walk expands it. |
| Structural hashing and numeric set membership | `TryHashLeaf` folds the numeric value. A range contains each whole number between its endpoints once. Scanning flat numbers in `contains` and hashing them in `distinct` contributes no nested structural units. | Preserve the hash of the same value within a process, the first representative, output list identity and reservation. Test nonintegers, specials and the exact integer endpoints. |
| `NormalizeCore`, `NormalizeFrame.Accept`, host-result admission | `Accept` compares a normalized child with a second read of its source slot. With a fresh box that comparison fails and a canonical list is rebuilt. This changes observable sharing and retained space. Admission also inspects nested structure against the run budget. | Return the same box on reread, preserve the identity of an already-normal root, and continue to account for the same inspections. |
| `RecordGraphEquality` and `AstStructuralPreflight` | Both walk program structure. Neither enumerates the runtime items of a range. | No extra AST node, expansion or budget is needed. |
| `ZeroArgPropertyResultCache`, local/environment keys, `NeedCell`, deconstruction and loop/site memos | Their keys identify bindings, scopes, cells, syntax or property cache entries. They do not key a lookup on a number box. Their **payloads** can expose the cached list and a selected item together. Root property observations can also return the exact published value. | Preserve object sharing at the read, transport and publication boundaries. Cache hits must see the same originating range. |
| Host-argument, run-export and property-observation call-reference scans | A number cannot contain a call reference. The walks memoize structures and count slot inspections, not distinct atoms. Walking a memoized range can box every visited item. Skipping the walk wholesale can omit existing work charges or cancellation checkpoints. | Keep the same logical scan, including the current gating, nested charges, scan order and export checkpoint schedule. |
| Indexing, `first`/`last`, spreads, list patterns, deconstruction, `take`, `skip`, `distinct` | The stored engine carries the actual element. Equal new atoms are distinguishable across results, even when each list independently has a stable indexer. | Preserve each originating reference wherever it is forwarded. A slice still owns a distinct result list according to the existing construction rule. |
| `CollectionIterationItems`, generic and async `map`/`filter`/`reduce`, fused receiver adapter | The original callback receives the source item. `filter` can read the position again for its result. Fresh boxes can change callback returns, effects, errors and subsequent charges. Existing value/counter parity tests can pass without exercising a reference-observing host. | Use the same canonical atom when the source is an existing range. `FilterCountSourcePlan.DirectRange` streams a written range directly. Its per-predicate allocation is no precedent for replacing the exposed item of a cached receiver. |
| Numeric folds, `atoms`, flattening, formatting and display | `count` needs the count only. Numeric folds and the host atom projection consume numbers. `order` and `atoms` already construct result number objects. The three formatters render values, and `StructuredLayoutRenderer` caches layout by the items-view object. | Keep element order, quantum, sign, formatting limits and one stable view. Reading numbers directly must preserve every check and error. |
| CLR hosts and the public collection | Delegates, consumers of `RunResult` and host reference-keyed collections can distinguish equal boxes. The public `ICollection<T>.CopyTo` contract includes valid covariant destinations. `IList<Result>.Contains` and `IndexOf` search for a numeric value by record equality. | Preserve host verdicts, index and enumeration protocols, and valid copies. An arithmetic search must reject wrong kinds, fractions, infinities, NaNs and out-of-range integers without rounding them into a valid slot. |

Source anchors include the [value and normalization walks](../../src/KatLang/Result.cs), [reference classes](../../src/KatLang/ReferenceClasses.cs), [collection builtins](../../src/KatLang/Evaluator.Builtins.cs), [call-reference scans](../../src/KatLang/Evaluator.CallPlans.cs), [property observations](../../src/KatLang/Evaluation/Caching/RootPropertyObservationSink.cs) and [sequence optimizer](../../src/KatLang/Optimizations/Sequences/SequencePipelineOptimizer.cs).

## Public collection, budgets and Lean

`Result.ListValue.Items` and `Deconstruct` expose one read-only view per list. On the tested runtime the concrete view for a stored range is `ReadOnlyCollection<Result>`. CLR record equality observes that view's identity. A `with { }` copy shares the view and has the same record hash. Structural KatLang equality and hashing use the element values. Any mutable memo must stay out of both kinds of hash. The generated public API baseline describes signatures and cannot detect a change in the reference supplied to a host operation.

Both the stored range and the hybrid reject mutation through `IList<Result>`. A second public probe allocated a `Result.Atom[]` with room for every element and called `((ICollection<Result>)list.Items).CopyTo(array, 0)`. The stored range filled it successfully. All three experimental views used `AsSpan<Result>` over the covariant destination and threw `ArrayTypeMismatchException`. The non-generic `ICollection.SyncRoot` also returned a `Result[]` on the stored view, the `ReadOnlyCollection<Result>` on the hybrid, and the prototype's `RangeItemsView` on fresh and memo. This last observation describes .NET 11 on this machine. Changing the atom policy alone cannot restore the collection's public behavior. The [public surface baseline](../../tests/KatLang.Formatting.PublicApi.Tests/PublicApiBaseline.txt) and its runtime behavior are those of the stored implementation in the delivered tree.

`BuildInclusiveRangeChecked` obtains the inclusive count after evaluating and validating the bounds, then calls `ReserveCollection` before list construction. `TryReserveCollection` checks continuation, the per-collection limit, then the cumulative materialization limit before adding that count. Every representation must retain that reservation at the call, plus each derived collection's own existing reservation. This includes elided collections on the fused route. Deferring only the cumulative charge would let `count(range(1, 6))` succeed under `MaxMaterializedItems = 5` and move work to arbitrary host reads, potentially after the run. The separate per-collection ceiling would still reject a million-item range. Changing either policy needs its own owner decision. [Range construction](../../src/KatLang/Evaluator.cs) · [Budget](../../src/KatLang/Evaluation/EvaluationBudget.cs) · [Limits](../../src/KatLang/EvaluationLimits.cs)

Lean's `inclusiveRange` constructs a `List Int` by adding or subtracting an index from the start. Bounds and steps are inclusive in both directions. Lean has no CLR reference identity, Decimal128 quantum or host allocation counter. On the C# side an admitted whole-number bound is canonicalized, including unsigned zero and the exponent required at ±10³⁴. An index formula must match the existing stepping enumeration bit for bit. Pure Lean/C# correspondence cases can agree throughout while a host callback still changes a KatLang verdict. [Lean definition](../../lean/KatLang.lean#L4265)

## Measurements

### Setup

All comparisons used Windows x64, .NET 11.0.0, Release, and the sources of local `main` at `bb1314f2`, which includes `25e8635c`. The scratch baseline matched all 242 tracked evaluator, benchmark, global SDK and version files compared with the selected checkout. Baseline and hybrid used the repository's BenchmarkDotNet 0.14.0 jobs for `SequenceBuiltinLargeListBenchmarks`, `SequencePipelineStage2Benchmarks`, `SequencePipelineLargeListBenchmarks` and `SequencePipelineRepeatedBenchmarks`. Measurements ran one process at a time, alternating baseline and hybrid and reversing the order of the large/repeated pipeline modes. The Stage 2 suite has its own fixed mode ordering. Fresh, memo, memo and fresh then ran the same four classes and checked-in scenario sources, with 27 completed cases per pass. The prototype's process switch exists only in the scratch assembly.

A separate Release harness parsed once per process, warmed each prepared root, and measured repeated evaluations. Its TSVs record median/minimum time, allocation, Gen0/1/2 collections and `GC.GetTotalPauseDuration()`. The tables giving harness medians average the two mirrored process medians. GC and allocation figures are per evaluation. Harness MB are decimal. BenchmarkDotNet uses binary memory units and reports collections per 1,000 operations.

### Whole-program measurements

BenchmarkDotNet mean time in milliseconds. Each cell spans the completed sessions for that representation. The stored column includes the review run against the selected checkout and the earlier alternating baseline series. The two prototype columns each use two sessions.

| Prepared method and pipeline mode | Stored | Fresh | Memo | Hybrid |
| --- | ---: | ---: | ---: | ---: |
| RangeCount100k | 7.28–9.15 | 0.036–0.041 | 0.026–0.030 | 0.020–0.034 |
| Take100k | 10.1–10.4 | 0.034–0.060 | 0.035–0.062 | 0.041–0.042 |
| Skip100k | 8.60–10.9 | 0.048–0.049 | 0.028–0.042 | 0.026–0.044 |
| Distinct100k | 14.9–18.3 | 17.4–19.2 | 10.4–12.1 | 0.028–0.030 |
| Order100k | 55.2–63.1 | 47.3–56.2 | 47.0–54.8 | 47.9–49.0 |
| OrderDesc100k | 36.5–41.0 | 30.9–33.8 | 29.9–37.1 | 30.6–31.0 |
| Sum100k | 9.06–10.6 | 1.91–2.05 | 1.57–4.65 | 1.54 |
| Avg100k | 9.66–11.8 | 3.94–4.68 | 3.73–4.51 | 3.52–4.07 |
| Min100k | 10.1–12.1 | 2.76–4.16 | 2.25–3.26 | 3.31–3.36 |
| Max100k | 9.14–10.2 | 2.69–2.72 | 2.32–2.52 | 2.71–3.31 |
| MapSum100k | 82.6–101 | 69.7–78.5 | 81.0–94.1 | 69.2–93.5 |
| CheapFilterCount100k, generic | 65.9–92.5 | 48.0–58.0 | 62.9–65.2 | 50.7–55.0 |
| CheapFilterCount100k, optimized | 46.0–49.7 | 43.5–44.5 | 45.5–47.5 | 46.0–52.8 |
| RepeatedFilterCount100k, generic | 1,429–1,615 | 1,244–1,347 | 1,623–1,756 | 1,307–1,362 |
| RepeatedFilterCount100k, optimized | 1,357–1,630 | 1,377–1,779 | 1,251–1,313 | 1,416–1,497 |
| RepeatedShortFilterCount, generic | 1,348–1,511 | 1,145–1,364 | 1,160–1,176 | 1,163–1,228 |
| RepeatedShortFilterCount, optimized | 1,395–1,720 | 1,231–1,540 | 1,253–1,270 | 1,467–1,469 |
| FilterCountEvenRange, generic | 6.93–7.62 | 6.06–8.87 | 6.61–6.96 | 6.26 |
| FilterCountEvenRange, optimized | 6.18–7.70 | 6.01–7.86 | 5.77–6.49 | 6.53 |
| SquareFreeFilterCount1000, generic | 20.6–22.8 | 18.7–20.3 | 18.8–19.7 | 19.1 |
| SquareFreeFilterCount1000, optimized | 19.9–23.6 | 18.3–19.5 | 17.4–24.5 | 19.1 |
| SquareFreeFilterCount10000, generic | 473–488 | 444–507 | 458–484 | 458 |
| SquareFreeFilterCount10000, optimized | 470–481 | 489–546 | 445–470 | 450 |
| SquareFreeRepeatCount1000, generic | 22.8–23.1 | 20.4–21.0 | 20.2–21.1 | 22.0 |
| SquareFreeRepeatCount1000, optimized | 22.7–22.8 | 21.9–26.0 | 20.9–21.8 | 21.7 |
| SquareFreeRepeatCount10000, generic | 522–617 | 459–479 | 467–519 | 494 |
| SquareFreeRepeatCount10000, optimized | 494–585 | 540–714 | 463–469 | 492 |

Over the earlier baseline sessions `RangeCount100k` took 7.3–8.2 ms and allocated 3.82–3.89 MiB. `Sum100k` took 9.1–12.0 ms. In the alternating hybrid sessions these fell to 20–34 µs / about 9.4 KiB and 1.54 ms / about 9.5 KiB respectively. The direct number reads matter as well as eliminating construction. Without those reads, the scratch fresh prototype allocated 6.39 MB for `sum` and the memo prototype 4.01 MB. This reproduces the materialized-source cost identified in `a375dd4d`. It does not repeat that commit's CPU sampling or dummy-allocation experiment.

### Garbage collection and retention

| Workload and storage | Median time (ms) | Allocated (MB) | Gen0 / Gen1 / Gen2 per run | Pause (ms/run) |
| --- | ---: | ---: | --- | ---: |
| `sum` of 100k, stored | 10.26 | 4.021 | 0.51 / 0.50 / 0.25 | 2.51 |
| Same numeric query, fresh / memo / hybrid | 2.50 / 2.40 / 2.75 | 0.010 each | 0 / 0 / 0 each | 0 each |
| 20 separate 100k ranges, stored generic pipelines | 2,023 | 2,252 | 274.67 / 31.25 / 19.92 | 253 |
| Same, fresh | 1,544 | 2,248 | 267.83 / 20.50 / 10.25 | 154 |
| Same, memo | 1,970 | 2,232 | 276.25 / 71.46 / 32.04 | 486 |
| Same, hybrid | 1,516 | 2,248 | 267.83 / 20.50 / 10.25 | 148 |
| **20 pipelines over one cached range**, stored generic | 1,343 | 2,157 | 257.92 / 4.92 / 2.92 | 59 |
| Same, fresh | 1,404 | 2,248 | 267.83 / 20.67 / 10.33 | 148 |
| Same, memo | 1,495 | 2,156 | 257.58 / 6.08 / 2.83 | 131 |
| Same, hybrid | 1,418 | 2,248 | 267.83 / 20.67 / 10.33 | 132 |
| Same, hybrid keeping accepted source boxes | 1,312 | 2,219 | 264.75 / 3.50 / 2.42 | 54 |
| 2,000 × 1,000, stored generic | 1,675 | 2,244 | 268.25 / 0.21 / 0 | 111 |
| Same, fresh | 1,761 | 2,260 | 270.17 / 2.63 / 0.04 | 97 |
| Same, memo | 2,146 | 2,244 | 268.25 / 3.38 / 0.04 | 173 |
| Same, hybrid | 1,788 | 2,260 | 270.17 / 2.21 / 0.04 | 102 |

The shared-range control reproduces the direction of `69c5fde1`. On the stored generic route, sharing the source reduced Gen2 from 19.92 to 2.92 per run and pause from 253 to 59 ms. The hybrid saved collections on the separate ranges but gave up much of that saving when the source was shared. Keeping only the accepted boxes recovered the shared case and raised the short-range median from 1.79 to 2.12 seconds. It still failed to address callback argument identity.

A second shared-range control used BenchmarkDotNet with three warmups and six timed evaluations per process, in two processes per storage policy. Each evaluation had a new run cache and disabled sequence-pipeline optimization. All returned 1,000,000. Time spans the two process means. Collection counts average the two MemoryDiagnoser reports. Pause averages all 12 timed evaluations, measured inside the workload. The shared-control runs used a 100,000-item effective limit throughout.

```katlang
IsEven(n) = n mod 2 == 0
R = range(1, 100000)
K(k) = R.filter(IsEven).count + k * 0
map(range(1, 20), K).sum
```

| Storage | Mean time (s) | Allocated (GiB) | Gen0 / Gen1 / Gen2 per run | GC pause (ms/run) |
| --- | ---: | ---: | --- | ---: |
| Stored | 1.79–1.91 | 2.01 | 257.0 / 4.0 / 2.0 | 89.7 |
| Fresh | 2.08–2.84 | 2.09 | 267.0 / 19.0 / 9.0 | 220.1 |
| Memo | 2.00–2.57 | 2.01 | 256.0 / 7.0 / 6.0 | 154.0 |

The Stage 2 GC harness exercised the same five prepared benchmark methods in generic and optimized modes on all three representations. Each of the six processes ran three warmups and eight timed evaluations per method and mode. The two stored runs bracketed the four prototype runs. All ten method/mode results agreed in every process. One workload is shown here. The six TSVs contain the other nine, including their allocation and pause measurements.

| `SquareFreeFilterCount10000`, generic | Median time (ms) | Allocated (MiB) | Gen0 / Gen1 / Gen2 per run | GC pause (ms/run) |
| --- | ---: | ---: | --- | ---: |
| Stored | 533 | 184.7 | 23.12 / 0.00 / 0.00 | 12.5 |
| Fresh | 479 | 184.8 | 23.12 / 0.25 / 0.00 | 6.9 |
| Memo | 477 | 184.7 | 23.12 / 5.25 / 4.06 | 12.7 |

At 100,000 items the retained-heap probe measured 4,000,072 B for an untouched stored range and 120 B for the untouched hybrid. After a full public traversal, those estimates were 3,956,552 B and 3,969,136 B. The flat-table memo prototype went from 136 B to 3,956,640 B. The fresh prototype retained no boxes after the traversal within the resolution of the heap measurement. The raw post-GC delta on that run was −43,384 B, which is measurement noise. Per-access allocation still occurred.

### One million items

On production settings the exact program `R = range(1, 1000000)` followed by `R.count + R.count` failed at line 1, column 5 on the baseline, stored control and hybrid. It requested 1,000,000 items against the fixed per-collection ceiling of 100,000. Setting a higher host limit cannot raise that ceiling.

The supported workload retained ten independent 100,000-item ranges, reading each with `sum`, `filter(IsEven).count` and `max`. On the generic route the stored / fresh / memo / hybrid medians were 790 / 826 / 1,297 / 723 ms, with GC pauses of 58 / 60 / 282 / 53 ms. This exercises one million retained positions in ten lists.

To measure one retained list of the requested size, a separate scratch build raised only the hard per-collection ceiling to 1,000,000 relative to the prototype. It ran the two representations and the stored control in mirrored order. The selected checkout kept its ordinary ceiling. `ThreeBuiltins` read one cached list via `R.count + R.sum + R.max` and returned 500,002,500,000. `ThreePublicPasses` retained the public list, enumerated every item three times and returned 1,500,001,500,000. Each table entry covers two fresh processes. Time spans their BenchmarkDotNet means. Allocation, collections and pause are measured inside the workload across their 12 timed evaluations.

| Reads of the same list | Storage | Mean time (ms) | Allocation per run | Gen0 / Gen1 / Gen2 per run | GC pause (ms/run) |
| --- | --- | ---: | ---: | --- | ---: |
| `ThreeBuiltins` | Stored | 427.3–531.0 | 46.16 MiB | 3.00 / 2.00 / 1.00 | 73.79 |
| `ThreeBuiltins` | Fresh | 71.3–202.0 | 15.1 KiB | 0.00 / 0.00 / 0.00 | 0.00 |
| `ThreeBuiltins` | Memo | 80.5–86.6 | 15.1 KiB | 0.00 / 0.00 / 0.00 | 0.00 |
| `ThreePublicPasses` | Stored | 441.2–507.2 | 46.16 MiB | 3.00 / 2.00 / 1.00 | 92.39 |
| `ThreePublicPasses` | Fresh | 99.9–182.1 | 91.56 MiB | 11.00 / 0.00 / 0.00 | 1.89 |
| `ThreePublicPasses` | Memo | 183.1–197.3 | 38.16 MiB | 3.00 / 3.00 / 0.00 | 46.45 |

The numeric queries can read the million positions without a table of boxes. The public scans allocate a new atom on every visit in fresh mode. The memo pays for a table and the canonical boxes on the first pass, then reuses them. The ordinary 100,000-item ceiling still decides admission in production.

### Fusion

Savings are `100 × (1 − optimized time / generic time)` for the two means in the same session. Positive values mean fusion took less time. Negative values mean it took longer. `RepeatedShortFilterCount` runs 2,000 ranges of 1,000 items.

| Program | Stored | Fresh | Memo | Hybrid |
| --- | ---: | ---: | ---: | ---: |
| CheapFilterCount100k | +27.0% to +46.3% | +9.3% to +23.3% | +27.1% to +27.6% | +4.0% to +9.2% |
| RepeatedFilterCount100k | −14.1% to +15.0% | −43.0% to −2.2% | +19.1% to +28.8% | −9.9% to −8.3% |
| RepeatedShortFilterCount | −13.8% to −0.1% | −12.9% to −7.5% | −9.5% to −6.5% | −26.3% to −19.5% |
| FilterCountEvenRange | −1.1% to +10.7% | +0.8% to +11.4% | +6.8% to +12.7% | −4.4% |

Fusion still elides a filtered list, its kept slots, and their GC costs. The cheap, repeated, short and shared controls give different tradeoffs. Timing of an identity-changing representation cannot justify retiring the optimizer. A decision about fusion needs the same measurements over a compatible range.

### Reproduction and measurement limits

The Release jobs use prepared roots and the original iteration counts. Full tables with all method means, errors, allocations and available GC columns are under `artifacts/validation/lazy-range-design/` on the measuring machine.

| Evidence | Location under that directory |
| --- | --- |
| Baseline jobs, alternating baseline and hybrid jobs | `baseline-main/`, `bdn-base/`, `bdn-impl/`, including their `.load.txt` samples and per-class CSVs |
| Fresh and memo prototypes on the same durable jobs | `review/{fresh,memo}-{1,2}.bdn/results/` and matching load, log and exit records |
| GC harness, short and retained workloads, alternate kept-box variant | `harness-round1.tsv`, `harness-round2.tsv`, `progress.txt` |
| Public host and collection probes | `review/host-{baseline,stored,candidate,fresh,memo,returned-main}.log` |
| Selected-main jobs and normalized source comparison | `review/shared-main-{1,2}.bdn/results/`, matching logs, and `review/source-check.txt` |
| Exact single-million scratch jobs and 100k shared controls | `review/million-{off,fresh,memo}-{1,2}.bdn/results/` and matching logs with per-iteration counters |
| Stage 2 GC harness on all five methods, both modes | `review/stage2-{off,fresh,memo}-{1,2}.tsv` and `review/stage2-gc-load.txt` |
| Exact two-line host example, normal public API | `review/minimal-{returned-main,hybrid}.log` |

The scratch source and harness are under `C:\Temp\lazyrange\`. The host observer is `review-host-surface/Program.cs`. The prototype project is `proto/benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj`. The durable filters are `*SequenceBuiltinLargeList*`, `*SequencePipelineStage2*`, `*SequencePipelineLargeList*` and `*SequencePipelineRepeated*`. The scratch process variable `KATLANG_LAZY_RANGE` selects `fresh` or `memo`, with the numeric paths enabled. In the review's direct comparison the optional range-specific `distinct` path was off for both. The earlier harness measured it separately. The hybrid's `distinct` path was on. The supplemental runner is `review-host-surface/review-extended.ps1`. Its `review-shared` benchmark project references the actual checkout. The single-million jobs use `review-single-million` with the raised ceiling, the same `run-bdn.ps1` Release runner and a separate matching stored control.

Background load in the earlier durable comparisons ranged from 4% to 27% CPU before launch. The four full fresh/memo review jobs started at 3.2–11.4% CPU. The full selected-checkout job started at 19.2%. The six single-million jobs started at 26.2–58.9%. The second stored shared-range control started at 95.2% CPU with 0.7 GiB free. All 12 review jobs and their load samples are included. Elapsed times and pauses in the shared and single-million comparisons are sensitive to that load.

Stored controls running the same logic varied by up to 38% in some harness timings. The first baseline repeat-pipeline series includes fused samples of 3.235 s (100k) and 1.979 s (short). These remain in the logs. The timing table uses the alternating series and the separately identified review sessions. Earlier harness rows overlapping builds and the baseline builtin run overlapping a busy Python process were remeasured. Allocation, repeated samples and GC counts carry more weight than small timing differences here. The prior reports' `generic-pipeline-gc/` logs were unavailable on this machine.

## Scope and release decision

A numeric backing could also serve irregular results such as `atoms` or `order`, which already build new number atoms. A `map` result can be mixed or can forward its input, and its callback can have effects or fail. Changing its storage cannot defer that callback or discard an observable reference. A filtered view of range positions would need to run the predicate in its original order, preserve its errors, return the source atoms and bound retention of its source.

The V3 candidate's prior .NET and Lean suites passed, including its differential, concurrency and allocation tests. The new host witness exercises a behavior those checks missed. The review retained the measurements and withdrew the production and test changes. The final V0 change is this report. Production continues to use the stored representation, with its existing API, Lean model, accounting and fusion behavior.
