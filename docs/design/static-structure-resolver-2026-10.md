# B3: one static-structure resolver for the M4★ front end, with A1

Current isolated candidate (2026-10-30): Q1–Q7 are the consolidated production structural
authority for detection, resolution, editor analysis and exposure. The independent acceptance
review accepted the architecture and the earlier exhaustive V3 evidence, with three integration
blockers F1–F3. Their corrections pass fresh validation on the final frozen executable source.
V3 passes under the explicitly approved exhaustive 44-batch procedure in both modes; the canonical
core attempts timed out and remain INCOMPLETE. The final Gate D/B3-2★ verdict, including the
independent read-only delta review, is recorded in
`experimental/features/alias-unify-1-b32-final-corrections-2026-10-30.md`.

The approved V3 procedure first attempts canonical ordinary and forced full-host validation.
After a 900-second timeout without unresolved correctness failures, the owner-approved 44-batch
fallback preserves all original 42,325 core cases, 542 whole collections and deferred theory rows
in both modes, plus added regressions, solution builds, CLI/API, all seven Lean targets and
generated/specification checks. Each host retains 900-second/6-GiB bounds and exact identity and
fingerprint verification. Cross-class co-residency, process-state lifetime and contention differ
between batches; that residual limitation remains explicit. This approval is scoped to this
candidate, not a general validation-policy change.

B3-5★ (November 2026, § 10) replaced Q8's processing order and on-demand processing with signature
selection: every inferred signature and link class is selected jointly before the rewrite, and Q9's cells complete
from the selected endpoints. B2 is not adopted; X-04 is plain A-agree with R1 origins (owner direction 2026-11-05, superseding B of 2026-11-03): lifting cycles are completed simultaneously, and one that does not settle is refused.

## 1. Owner decisions (2026-10-27)

- **A1.** Reject statically detected self-dependent implicit-parameter inference with a deterministic compile-time
  diagnostic.
  - Preserve ownership-first name resolution.
  - Classification must not depend on declaration order or expression traversal order.
  - Reject as little as possible, and keep resource bounds.
- **B3.** Replace the structural reasoning that parameter detection and alias resolution each duplicate with one
  authoritative, demand-driven, memoised computation.
  - Preserve M4★, OD-B–OD-E and NEED-04.
  - Remove inconsistent structural verdicts, fragile sibling-processing dependencies and host-stack-depth
    amplification.
  - Preserve non-alias behavior, diagnostic order, lazy evaluation and resource guarantees.
- **B2 is a fallback only.** No narrowing of M4★ semantics without explicit owner approval. If B3 meets a fundamental
  obstacle, document it and stop for a decision.

Background: `artifacts/validation/alias-unify-1-impl/handoff/owner-decision-brief.md` and `status-handoff.md`
(git-ignored).

## 2. Why B3

Since M4★, static structure depends on inference, and inference depends on static structure:

- structure means alias status (OD-C/OD-D), `open` providers and receiver members;
- inference means which free names are inputs, and whether a dot edge's fallback is certain (Q-75).

Before B3-2★, the front end computed these in two places:

- the parameter detector (`ParameterDetector` / `ElaboratedScopeLookup`, with the input "decider");
- implicit-argument resolution (`ImplicitArgumentResolver`), whose static chases, miss refinement and alias formation
  run in the order fixed by a static sibling-order channel (`PropertyDependencyGraph`, `SiblingOrderLookup`), with
  on-demand processing (`PropertyLoop.EnsureOnDemand`) as the fallback.

Fourteen review rounds found those superseded authorities disagreeing:

- the navigated-body defect;
- reads the channel cannot order, which nest on the host stack until `DemandDepthBudget` refuses;
- answers that depend on declaration order;
- the self-dependent class (owner question (b)), which has no consistent or affordable answer.

B3 computes every structural fact once, by demand, in one engine. Both passes, and the editor, read the same answer.

## 3. The engine (stage B3-0)

`StaticQueryEngine<TKey, TValue>` solves pure equations over a pointed information order. One engine serves one
front-end operation; keys preserve declaration/body identity. This is an implementation protocol, not an additional
language rule. It does not decide X-04 sibling lifting cycles.

**Ordinary equations.** `reader.Read(k)` always returns the current lower bound, initially `Initial(k)`, and subscribes
the running query to changes of that key. `Complete(value)` publishes its ordinary equation's answer. Every strict
change must satisfy the definition's `IsRefinement`; equality is supplied separately. Computations are deterministic
and monotone. Reading Unknown permits a definite answer only when all refinements agree (branch agreement).

**Reference equations.** `return reader.Follow(k)` declares that this query's entire equation is one definite
reference step to k. It does not return a context-dependent cycle Boolean. There is at most one successor, and once
declared it can never be withdrawn or rewired. Ordinary guards must establish that successor conclusively first.
With an Unknown guard, read alternatives ordinarily and apply branch agreement; do not speculate a path edge.
A definition may move from an ordinary Unknown answer to a confirmed path once its guard is decided.

The definition supplies one `PathCycleValue`, the OD-D refusal verdict. Consumers interpret refusal at the queried
body's own identity. Union-find representatives are graph bookkeeping only, never algorithm identities or open
provider identities. Acyclic paths transport the exact terminal answer; brace/carrier boundaries are explicit
terminal equations under M4★, not reference edges.

**Graph cycle classification.** Confirmed reference edges form a growing functional graph (outdegree at most one).
Each weak component is either an open tree with one sink or a closed component with one directed cycle. A new edge
from that sink closes a directed cycle exactly when its endpoints are already in the same weak component. Disjoint
sets with size merging and iterative path halving detect this independently of evaluation ancestry. Linked member
lists seed refusal once per newly cyclic entry, including new tails into an already closed component. Ordinary
dependencies never participate in this cycle test.

Thus A follows C, C follows A, and A also reads B which follows C: all three are refused even if the irrelevant B
read runs first. Conversely A follows B and B *ordinarily reads* A has no pure reference cycle and remains Unknown
without another deciding fact. A1 later rejects unresolved inference decisions; it does not relabel every dependency
cycle as OD-D refusal.

**Fixed point and finality.** An iterative FIFO worklist computes newly reached equations and propagates changes to
every ordinary reader and reference predecessor. Queue membership is deduplicated; independent discoveries are
batched. Ordinary subscriptions are replaced on recomputation, so obsolete branches leave no stale dependencies.
Values stay in place; there are no provisional result owners, chase frames, suspension recipes or invalidation logs.
No new key becomes final until the entire worklist is quiescent. The resulting reachable closure is cached; later
demand roots can add incoming edges but cannot alter an already final closure under the purity contract.
At successful quiescence every ordinary edge joins final entries and has no future reader, so the engine unlinks
the edges created by that call (bounded O(E) work, cancellation checked per entry and edge); path and component
state is kept for later OD-D detection, and the logical dependency/storage charge is not refunded.

Starting at bottom and applying monotone equations fairly computes their least information fixed point, with
refusal seeds exactly for confirmed path cycles. This justifies scheduling independence *under the definition
contract*. Runtime checks reject observed non-refinements and unstable successors; they cannot prove arbitrary
callbacks pure, globally monotone or sound on unobserved alternatives. Real Q1–Q7 definitions must establish those
properties, including stable identity and stratum, at B3-2★. Independent synchronous whole-graph/path-walk oracles
test the protocol using different algorithms; they are not a proof of the unfinished real queries.

**Limits and cost.** `MaxEvaluations` bounds worklist events plus explicitly charged local certificate and adapter work,
and one unit per exposure settlement frame of the unit the operation admitted (below);
`MaxReads` bounds all reader calls (including duplicates),
`MaxEntries` bounds engine discovery and admitted auxiliary live records, and `MaxRefinements` bounds strict changes per key. Reaching a bound
raises `StaticQueryLimitExceededException`. Cancellation is checked before/after callbacks and throughout engine,
subscription, component and propagation loops; its original token is retained. Reader failures are sticky even if
a callback catches them. Any failed/cancelled solve permanently faults the engine; no partial facts are usable.
Production consumers must supply finite operation-scaled limits and map bound failures to the existing resource diagnostic.
The default limits are for the unconsumed foundation, not production resource policy.

For V keys, maximum refinement height H and E distinct observed dependency edges, worklist events are O(V + H E),
reference analysis is O(V α(V)), and resident graph space is O(V + E). Each entry is classified cyclic at most once.
Total work also includes R, the reader/subscription work across callback reruns, plus the callbacks' own bounded
work. R can be quadratic: a wide callback may rescan its inputs as a chain refines one fact at a time. FIFO removes
the simpler independent-input rescan pathology, but does not prove universal FE-1 linearity. Allocation churn is
O(R), even with linear resident space. B3-2★ must use bounded fan-in/shared aggregates or demonstrate equivalent
bounds on its actual equations; use the read limit as a terminal resource bound, not a substitute for that analysis.
The engine uses no host recursion. Callbacks must cooperate with cancellation and remain bounded between reads.
Statistics expose events, computations, reads, value changes, path edges/cycles, queue peak, entries and
ordinary dependencies (the edges the latest subscriptions charged, still counted after final edges are unlinked) for
regression and complexity checks.

**Gate C private integration (2026-10-29).** Closed namespace observers use a second FIFO queue, run only
when ordinary work is quiescent; an observer that unlocks ordinary work yields to that work before the next
observer. This coalesces intermediate closures without changing initial facts, refinement order, `Follow`
equations or language identity. It is not a richer identity domain or a solution to Q8/X-04.

**Decision observers (S-10 N1, 2026-11-08).** The receiver-expansion verdict (`ReceiverExpansionVerdict`, ordinary
and open; static-structure query contracts, receiver expansion) is a closure observer that DECIDES structure, while
the namespace certificates over-approximate structure that is still undecided. Decision observers have their own FIFO
queue, drained before the other closure observers (`IsDecisionObserver`); ordinary work still settles before each
observer. This is scheduling only. Measured on the production route: a ring of N member-path bodies
(`Ai = Bi; Bi = { public M = C(i+1) ⏎ 0 }; Ci = Ai.M.abs`) cost 61·N² certificate work and ~3.5× reads per doubling
when every `.abs` certificate ran over the whole undecided ring before the verdicts; with the precedence every
counter doubles with N. The verdict walk itself:
- uses decided inputs, head bindings and members for every concrete step, expanding an Unknown End in place. An
  observer can discover new ordinary queries, so quiescence on entry does NOT prove a terminating End already decided.
  Instead, a repeated VALID record proves that the deterministic expansion repeats without consuming a member below
  that record. Every still-valid ancestor reaches that repeat before returning to its own continuation; each one's
  End therefore diverges too. Those bodies are remembered per stratum and binding
  mode, one persistent ledger slot each, and a later walk that expands one of them in place with members pending stops
  with Yes. Later walks share these proved divergent suffixes, keeping measured aggregate work linear in admitted
  source (`ReceiverExpansionCostTests`: ring, readers into a ring, independent loops,
  bare and member-path chains, the first-expansion ring, three sizes each). A walk
  blocked on an undecided input, binding or member query records that QUERY for every still-valid ancestor. Reuse
  reads it through the ordinary reader and returns Unknown while it remains undecided; refinement schedules the
  reader, which then walks again. Decided prefix guards cannot change, and no member below a saved record was
  consumed, so the blocker is independent of the caller's continuation. An Unknown End alone is never a blocker.
  A chain into an undecided A1 witness formerly took 1,632 / 6,336 / 24,960 verdict walk steps at 16 / 32 / 64 bodies;
  sharing its blocker makes these 192 / 384 / 768. Namespace-certificate work for this rejected unit was already
  superlinear at the baseline and remains a separate cost; these figures concern the added receiver-expansion work.
- charges every member push, record, invalidation and member step as one adapter work unit through the operation
  ledger (which also observes cancellation), and holds its member stack and records in a temporary lease released on
  every exit. A blocked recipe charges three persistent slots per body/mode, and both memo-publication loops charge
  each visited record. `ReceiverExpansionNav` charges its member path the same way.
- is consulted only when the first-expansion recipe's cycle is decided without a pending return. A return the recipe
  proves never creates the summaries, so a ring of first expansions (`Xi = X(i+1).abs`) keeps exactly its unfixed
  cost (the historical candidate read the summaries while the recipe was still Unknown and was quadratic there).

**Deferred open presence (November 2026).** Q1's opened binding of a name reads the level's closed member index
(`OpenMemberIndex`, one per distinct provider sequence) and, while that index is Unknown, the name's presence
witnesses: a range tree of 2K − 1 queries over the level's K targets, whose leaves decide known presence before the
list settles. Every key starts Unknown, so each name's first read found the index still settling and built its own
tree, though the one index settled a few rounds later: N names under K opens made N(2K − 1) witness entries, and a
target repeated K times added each leaf's preserved-presence certificate over every earlier position (O(N·K²)
certificate work). `open L0` written 48 times with 64 names exhausted the program-scaled work bound (814,080) and was
refused as `StaticStructureLimitExceeded`. The witnesses are now behind a decision observer, `DeferredOpenPresence`:
it runs once ordinary work is quiescent, answers from the index when the index has settled, and reads the witnesses
only while it has not. Scheduling only: the index's answer is the conclusive one the witnesses refine to. Measured on
detection of one body (Release harness): K = 128, N = 256 inferred names went from 141,567 evaluations, 70,913 entries
and 51 MB to 10,623, 5,633 and 6.4 MB, and the 48-fold repeat with 64 names from refusal to 2,630 evaluations and
2,579 certificate units (about 53 per written target, none per name). A level whose index waits on its own names (a
provider whose structure depends on whether one of the level's opened names is an input) still builds witnesses for
the names whose deferred presence runs before it settles (K = N = 128: 33,924 witness entries, before 34,441).
`OpenLevelPresenceReuseTests`, `StaticStructureWitnessTests`.

The production admission policy is deterministic for equivalent source, configured resource policy and
compilation phase. `SourceProcessingLimits.MaxStaticStructureBytes` may lower the fixed 1-GiB ceiling;
values must be positive, larger requests clamp to the ceiling, and null selects that ceiling. No GC
or machine-memory report changes it. Source admission bounds distinct nodes at envelope/32 and edge
work at envelope/8. For F = admitted distinct nodes + edges, limits remain 16,384 + 1,024F work,
65,536 + 4,096F reads, four refinements, and min(envelope/1,024, 4,096 + 128F) entries.
Multiplications saturate safely before overflow. Source parser/engine entries inherit RunOptions'
immutable source policy, including eager and deferred modules; standalone host semantic analysis
accepts the same policy through its additive Build overload. Each admission is an operation, not
a mutable process-wide budget. The default 1-GiB envelope allows 1,048,576 entries and 16,777,216
ledger slots; operation-scaled limits can be tighter. This retains the measured conservative
1-KiB entry and 64-byte metadata accounting, with ample room above the 1,000/2,000-property
witnesses; it is not a total-process heap guarantee. Hosts needing less memory set lower limits.

**Measured program-size ceiling (2026-11-14, `897887a1`).** Because a host can only lower the
envelope, these two caps are an absolute program-size ceiling; the refusal says so ("The program
exceeds the host's static-structure envelope (at most 1 GiB; a host may only lower it)."). The
operation's work bound is not such a cap — it scales with the admitted nodes and edges and does not
move with the envelope — so since November 2026 its refusal ends with its own sentence instead ("This
bound scales with the size of the analyzed program (16,384 + 1,024 per node and edge) rather than
with the host's static-structure envelope, so no envelope setting raises or lowers it."). The read
bound scales the same way, and its refusal says so with its own figures ("This bound scales with
the size of the analyzed program (65,536 + 4,096 per node and edge) rather than with the host's
static-structure envelope, so no envelope setting raises or lowers it."). Signature selection's
enumeration limit is a constant, so its refusal says that ("This limit is fixed: the count doubles
with each .Algorithm link classified together, and 2^62 or more is refused whatever the size of the
program or the host's static-structure envelope, so no host setting raises or lowers it."). The
entry cap is the envelope's part of a mixed bound, min(envelope/1,024, 4,096 + 128F), and an
entry-bound refusal explains the part that set it (`StaticQueryLimits.ProgramScaledEntries`, decided
at admission; the threshold is the same either way). While the envelope's part is the smaller, or
the two are equal, that is the envelope sentence. While the program's part is strictly the smaller
(under the default envelope, for every F below 8,160) it is "This bound scales with the size of the
analyzed program (4,096 + 128 per node and edge) and is below what the host's static-structure
envelope allows (one entry per KiB), so no envelope setting raises it." It does not say "or lowers":
a host that lowers the envelope far enough makes the envelope's part the smaller. The four
refinements per query are a constant, and their refusal says so ("This limit is fixed: no static
query may refine its answer more often, whatever the size of the program or the host's
static-structure envelope, so no host setting raises or lowers it."); the production fact order
changes a fact at most twice, so only a definition of greater height reaches that limit. A
namespace certificate holds its record count in a 32-bit integer, a fixed ceiling with a sentence of
its own that is never reached: each count is first charged to the callback graph's entry bound,
which is lower (`StaticStructureQueries.NamespaceCertificateTotal`). `StaticStructureConsumerTests`
pins every sentence, both sides of the mixed bound and the fixed limits, from counts and small
graphs only. Method:
a scratch harness outside the repository ran one `KatLangEngine.Run` per fresh process (Release,
Windows x64, .NET 11.0.0 workstation concurrent GC, no heap limit) and reported peak working set /
peak commit in MiB (bytes divided by 1,048,576); entry counts came from the same source with a scratch counter on `StaticQueryEngine`
entry creation. Entries are exactly linear per declaration kind, and the same at `a4b545e8`: an alias
row `A{i} = A{i + 1}` (closed by `A{N} = 42`, output `A0`) costs 36 entries (36N + 86), a call row
`C{i} = F({i})` beside `F(x) = x + 1` costs 11 (11N + 77), a constant row `P{i} = {i}` costs 3
(3N + 73). The audit's figure of about 26 per alias row is not reproduced by this spelling (the
audit's spelling is not recorded); per-row costs depend on the exact shape.
- Alias rows reach the entry cap. 29,124 rows (443,782 characters) are accepted at 624 MiB peak
  working set (605 MiB commit). 29,125 rows are refused with "The static queries exceeded their entry
  bound (1048576)." at 589 MiB (565 MiB), and 40,000 at 565 MiB (543 MiB).
- Call rows reach the ledger first, at about 183 slots per row. 91,660 rows (1,627,675 characters)
  are accepted at 1,325 MiB (1,340 MiB); 91,661 are refused with "The static operation exceeded its
  metadata storage bound (16777216 slots)." at the same peak. 70,000 rows are accepted at 937 MiB
  (920 MiB). From 95,319 rows the entry cap refuses first (100,000 rows: 1,068 MiB, 1,075 MiB).
  Since `0b78ed31` (2026-11-15) a call row costs about 195 slots: 86,019 rows are accepted and 86,020
  are refused by the same metadata bound (re-measured on `77ac0578`; the bisect is below).
- Constant rows reach neither bound inside the 2-MiB source ceiling. 136,000 rows (2,089,782
  characters, about 408,000 entries) are accepted at 1,173 MiB (1,172 MiB), and 120,000 rows at
  1,062 MiB, so other front-end and run state dominates there.

These witnesses do not contradict the conservative 1-KiB entry and 64-byte slot accounting.
Under `DOTNET_GCHeapHardLimit` the largest accepted alias program completes with a 512-MiB managed
heap limit but not with 384 MiB. The largest accepted call-row program and the ceiling-size constant
program complete with 768 MiB but not with 512 MiB. Default-GC process peaks include heap headroom:
88,988 call rows peaked at 1,469-1,473 MiB in three runs. These heap-limit experiments establish that
the measured programs can complete with a smaller managed heap; they neither measure bytes per
query nor prove a live-memory bound for every program. The envelope remains structural accounting,
not a process-memory guarantee. A refusal costs about what acceptance costs, because the operation
has done its work up to the bound.

**Front-end memory since SEC-S1 (2026-11-16).** The `fe-mem` probe (`Parser.Parse`, 2-GiB heap hard
limit, peak job commit; .NET 11.0.0) bisected over the first-parent history from SEC-S1 (`25cf9962`)
to `5d756643` finds ONE step over 10%: this resolver's introduction, `04225cf7`. A ceiling-size
constant-property source (`dense_props`, 136,430 rows) went from 452 to 1,222 MiB (SEC-S1 itself: 460
MiB on .NET 11.0.0, 443 on RC2), retained 64.5 → 148 MiB and allocated 2.0 → 3.5 GiB; `dense_funcs`
405 → 1,114 MiB; `wide_decon` went from accepted (1,213 MiB) to refused by the entry bound. Later
commits only drifted (`c85254fa` +7%, 1,356 MiB at `96133491`, 1,240 after `bed42cf5`, 1,262 MiB at
`5d756643`). The step is live state, not collector headroom: with a forced full collection every
50 ms the live peak rose 188 → 718 MiB (655 at `5d756643`). Live-heap histograms (ClrMD, at the live
peak, inside the resolution) put about 2 KB per body on this resolver: two query entries (152 B
each), the lookup level (192 B), the body syntax with its member index, parameter set and input graph
(about 1 KB), contexts, publications and keys; the operation's source, detected and resolved views
(3–4 tree generations live at the peak, 1–2 before); and the resolver's per-level state. The result
retains the completed facts (`BodyFacts` with their keys and tables, about 650 B per body). That is
the price of the design — queries read the admitted source, views are publications, completed facts
are published for deferred modules, tooling, exposure and diagnostics — and it stays. What was not intended, and was removed
without changing any result, diagnostic, charge or counter: a write-only per-level entry table in the
resolver (its reader went in `c85254fa`), empty per-body tables (Q4 member index, written parameters,
input-graph name uses, completed members and parameters), one completed publication per body instead
of one per table, and the resolution run kept reachable by its tier-0 frame while `CompleteLookups`
built the completed facts. On `dense_props` the live peak fell 655 → 545 MiB, the smallest completing
heap hard limit 704 → 576 MiB, the retained result 151 → 140 MiB and the probe's peak commit 1,262 →
1,132 MiB; on `dense_funcs` the live peak fell 490 → 458 MiB and the limit 544 → 512 MiB, while its
default-GC peak commit rose 1,059 → 1,091 MiB with two gen-2 collections fewer (10 → 8). Default-GC peaks follow
collector scheduling by several percent either way, so heap-limit runs are the regression measure.
The harness above, re-run on `5d756643` and after these trims (three runs each, commit MiB): alias
29,124 rows 744–746 → 589–734, call 70,000 rows 1,025–1,032 → 864–945, constant 120,000 rows
1,038–1,046 → 895–933, constant 136,000 rows 1,163–1,187 → 1,232–1,236 (one gen-2 collection more).
On `5d756643` already, before these trims, 91,660 call rows are refused by the metadata bound, so the
call-row boundary above is historical for `897887a1`. A ceiling-size `wide_decon` stays refused by the
entry bound (about 1.0 GiB); the envelope's formulas are unchanged. Bisect table, logs and histograms:
`artifacts/validation/front-end-memory-growth/` (local only).

**Call-row boundary bisect (2026-11-17).** The same harness, one fresh Release process per run, bisected the
first-parent commits from `897887a1` to `5d756643`. The boundary holds through `11bde9c0` (91,660 rows accepted,
91,661 refused, as at `897887a1`) and moves with the next commit, `0b78ed31` ("Reuse selected lifting dependencies
with ordered rewrite checks", 2026-11-15), to 86,019 accepted and 86,020 refused; main at `77ac0578` is unchanged.
That is about 12 more slots per call row (16,777,216 / 91,661 ≈ 183.0 before, 16,777,216 / 86,020 ≈ 195.0 after).
The commit removed the rewrite's second dependency walk, whose charges went with it, and added the rewrite-side
record of the selection invariant, `ImplicitArgumentResolver.OpenBodyLiftLog`, which every open body's rewrite
allocates whether or not it lifts anything: 4 slots for the log and its lists, then slots per row marker, per
rewritten node frame and per list growth. Charging it is deliberate. §10.1 item 3 and the commit message say the
log "charges its allocated storage and comparison work to the static ledger", which is the rule above (storage is
charged where it is allocated), and the commit's pins bound the charges' linearity, not an absolute charge
(`DottedCallSiteLedgerTests`). The SEMANTIC-ALIGNMENT row it touched (lookup, ownership and open; signature
construction is C#-only) needs no Lean change. The charge and the bound stay as they are; only the ceiling it moved
went unrecorded until now.

**Follow-up trims (2026-11-17, implementation only).** Three more per-body objects went. Exposure gives a user body
with output rows the shared empty arrays for its empty opens and properties, instead of two empty lists of its own; a
body without rows and an alias keep theirs, because their record equality rests on them. An input-graph node creates
its child and parent lists with its first edge. The resolver no longer builds the per-index entry table that both
callers of `BuildPropertyEntries` discarded. No result, diagnostic, record equality, ledger charge or counter changed:
a differential over 15,653 programs taken from test literals compared the diagnostics with spans, the normalized
elaborated trees, the record-equality matrix of the root's bodies and the ledger's work, adapter work, metadata, peak
and current storage, and found them identical; so were the probe's `fe-mem-diff` hashes of 461 inputs. A shared empty
PARAMETER-PATTERN list was measured and rejected: that list is an identity input of FE-3's signature composition and
bundle sharing, and sharing it merged compositions and bundles, which lowered the ledger's work and storage charges on
40 of those programs. `fe-mem` `Parser.Parse` at 2 Mi (Release, medians of three, MiB): `dense_props` retained
139.6 → 131.3 and allocated 2,550 → 2,515 (opens and properties: 8.3 retained, 20 allocated; input-graph lists: 8
allocated; entry table: 5–8 allocated); `dense_funcs` retained 143.9 → 138.0 and allocated 2,388 → 2,368 (its closed
bodies build no input graph, so that trim does not reach it). The smallest completing heap limits stay 576 and 512 MiB,
and the default-GC peaks move within their noise. The probe's census mode, broken since `04225cf7` (it ran detection
and resolution without an admitted operation), works again, and `FrontEndMemoryProbeCensusProcessTests` runs it for
every shape. Logs: `artifacts/validation/front-end-memory-follow-ups/` (local only).

**Intermediate-tree trims (2026-11-18, implementation only).** Three allocations of the detector's and the resolver's
intermediate trees went. The detector gives a body with output rows and no property the shared empty array instead of
an empty list of its own (`AstHelpers.SharesEmptyPropertyList`, the rule of the exposure trim above: a body without rows
keeps its list); the resolver adds its processed properties to the list the body keeps instead of filling an array and
copying it, and gives a property-less body the same shared array where that rule allows it (a lone-callee completion
and a runtime-target alias keep a list of their own, since an alias compares its row structurally); and
`BuildPropertyEntries` returns one shared empty read-only map for a level without properties, in both passes, instead
of an empty dictionary per leaf level (both callers only count it and copy it into a signature map). The 2026-11-16
census had also shown an empty frozen member table and parameter set per body. Since `1222b63f`,
`CompletedStaticStructures.BodyFacts` shares both empties. On `5fee88d9`, the 2 Mi `dense_props` census records
136,497 body facts and neither empty type ranks among its top 200 retained types by bytes.
The baseline and candidate differential outputs matched on 15,756 test-literal inputs. Checks included diagnostics,
ledger charges, normalized detected and resolved trees, and pairwise record equality for up to 80 sampled bodies
per intermediate or exposed tree and up to 40 root property values. The `fe-mem-diff` hashes of 461 inputs also
matched. `fe-mem` `Parser.Parse` at 2 Mi (Release, medians of three,
one process per run, MiB allocated): `dense_props` 2,513.5 → 2,443.1 (detector 16.3, resolver 30.5, entry maps 18.7,
each measured alone), `dense_funcs` 2,367.7 → 2,323.7 (13.1, 16.1, 14.5); retained 131.3 and 138.0 unchanged (these
trees die before the result). Logs: `artifacts/validation/small-follow-ups-2026-11-17b/` (local only).

**The same frame in a deferred unit (2026-11-17).** A materialization built its unit's completed facts
beside its resolution run, as the eager entry did before the trim above:
`ImplicitArgumentResolver.ElaborateStructuralDeferredBranch` held the run in a local across
`CompleteLookups`, and a materialization runs that method once, unoptimized. The run now ends in
`ResolveDeferredBranchInRun` first (the calls and their order are unchanged). Measured on an
instrumented copy of the engine (a hook at the start and end of the unit's `CompleteLookups`, a weak
reference to the run, a forced full blocking collection at each hook; Release, .NET 11.0.0,
non-concurrent workstation collector) for a clause branch that opens a one-member module and holds
dense constant properties. A branch is a unit under the materialization's own static bound, so its
ceiling is lower than a document's: 71,886 rows (1.2 M UTF-16 units) is the largest size tried that
completes, and 74,827 rows (1.25 M) is refused by the metadata bound (16,777,216 slots). At 71,886
rows the live heap at the start of `CompleteLookups` fell 510.8 → 459.8 MiB and at its end 564.6 →
513.6 MiB, with the run reachable before the split and unreachable after it (three runs each, equal to
0.1 MiB); for parameterized rows (`F{i}(x) = x + {i}`, 42,586 rows) 383.7 → 361.7 and 421.3 → 399.3
MiB. That is what the split buys: 6–10% less reachable while the facts are built. It does not lower
the materialization's own live peak, which is not in that window: sampled with a forced collection
every 25 ms, the peak is 694 MiB before and after, about 30 s after `CompleteLookups` ends and 2 s
before an 80 s sampled run returns. The resolution frame has ended by then in both builds. The stage
measurements below locate the corresponding peak on `c6d5c8d0` (measured as `cafe9fc1`, the same
patch on an older parent). Harness and logs are in
`artifacts/validation/deferred-branch-open-crash/part-b/` (local only).

**The live peak of a deferred unit (2026-11-18).** On `c6d5c8d0` (measured as `cafe9fc1`, the same
patch on an older parent), six sampler-only runs of 71,886 constant rows peaked near the end of
`StaticStructureOperation.Freeze` (682.5–683.7 MiB above the pre-run live heap). With 42,586
parameterized rows the boundary measured 570.7–570.8 MiB there. At
the constant-row peak, 480.2 MiB survived materialization. The published continuation dominated
322.0 MiB when materialization returned. The peak dump also shows 134.1 MiB held by the exporting
operation, 45.6 MiB exclusive to the preceding snapshot and 2.0 MiB held by the finished collision
validator. Taking back the attempt's lookup-cache entries released another 21.7 MiB. All four body
generations had direct stack references at the peak and surviving heap paths after the compile frame
returned. For constant and parameterized rows respectively, the deferred parse retained 224.8 and
202.2 MiB before selection. The eager twins retained 65.6 and 60.1 MiB. Their sampled peaks were
283.3–284.8 and 203.3–214.9 MiB. After either one or two selections the deferred results retained
480.2 and 410.1 MiB. The eager tree keeps the provisional branch. Its operation retracts provisional
resolved publications before freezing the placeholder's structural metadata. At full size the new
units inherit 81.05 and 101.08 persistent slots per row, respectively. `Freeze` itself adds 32.00
and 56.00 slots per row, including 26.00 for the parameterized rows' input graphs. The units finish
at 228.06 and 268.09 slots per row, against 105.05 and 101.09 for the eager twins. The metadata
bound first refuses 73,567 and 62,587 rows, respectively. The twins first hit the source-length
limit at 122,070 and 88,306. The result tree, completed facts and published continuation account for
the largest share under the current design and stay; that measurement trimmed nothing. Two holders
that outlived their last use were trimmed on 2026-11-19, measured on `3fba28fe` with three readings
at the hook after `Freeze` per build. Before either trim the hook read 677.4 MiB for constant rows
and 565.6–566.8 MiB for parameterized rows. **A:** the collision validator runs in a frame of its
own (`DeferredModuleRegion.ValidateParameterPropertyCollisions`), so it ends with its visit and not
with `CompileLoadedBody`. Alone it reads 675.4 and 543.5 MiB. **B:** an attempt that reaches the freeze takes its
lookup-cache entries back just before `Freeze`, and the cache refuses a write from then until the
attempt ends (`OpenMemberIndexCache.AttemptWrites.TakeBackBeforeFreeze`). No access to the four
tables was observed between that point and the former take-back, on both shapes at full size and on
fourteen attempt-ending cases. Alone it reads 655.7 and 552.8–554.1 MiB. Together they read
651.1–653.7 and 530.8 MiB, 24–26 and 35–36 MiB below the baseline. On an 8 MiB heap-limit grid
(`DOTNET_GCHeapHardLimit`, each endpoint run three or four times) the smallest limit that completed
every run moved from 696 to 664 MiB for constant rows and from 592 to 568 MiB for parameterized
rows, and the largest that failed every run from 680 to 656 and from 584 to 552 MiB. A grid point
between them flipped in two of those four brackets: 688 MiB completed one of four baseline runs for
constant rows, and 560 MiB one of four runs with both trims for parameterized rows. A alone gave
688 and 576 MiB (failing at 680 and 560; 568 completed one of four), B alone 672 and 592 MiB
(failing at 656 and 576; 664 completed two of four and 584 three of four). Values, diagnostics and
the cache's table counts were identical before and after. Stage tables, heap paths and charge sites
of the 2026-11-18 measurement are in `artifacts/validation/deferred-materialization-peak/`, the
before and after readings in `artifacts/validation/deferred-materialization-peak-ab/` (both local
only).

Open-level entries grow with providers × DISTINCT opened names read (P × D), not P². For one block
that opens P one-member providers and sums D ≥ 4 distinct opened names, entries are exactly
73 + 13P + D(2P + 17) (measured for P = 16 to 128 and D = 4 to 64): two per provider and distinct
name. Reading one name D times adds about 6 entries per occurrence, independently of P. Unread
provider members add only their own 3 entries each, with no provider-by-member term. A program
reaches P² only by reading P distinct names through P providers.

A numeric, token-free ledger enforces the same envelope in conservative 64-byte bookkeeping
slots (`MaxStorageUnits`): entries, actual subscriptions, the maximum read buffer, certificate-local graphs
and simultaneous temporary sets, input indexes, contextual adapters, completed projection and snapshot work,
and formula-lifting storage, charged where it is ALLOCATED and never per logical read: 4 slots per signature
pattern a flat template (on an intern miss) or a composed owner head copies
(`ImplicitSignatureTemplateInterner.SignatureStorageUnits`), 2 per synthesized argument of a bundle the resolver
builds (`ImplicitArgumentResolver.BundleStorageUnits`; a shared bundle is charged once). The weights follow the
≈335 B per logical lifted item measured on a distinct-name lifting chain, whose links each copy their callee's
local head (Θ(N²) physical); FE-3's K owners over one L-wide tail stay O(K + L) (`LiftingChainAdmissionTests`).
Slot counts are a conservative accounting policy, not a byte-exact heap theorem; source/runtime/editor work
has separate policies. Arithmetic clamps before multiplication to prevent Int64 overflow. Resource refusal
is `StaticStructureLimitExceeded`, never A1. A failed solve/active publication invalidates unsealed facts, cached provider reads and future export.
Successful sealing releases the producer ledger; later producer cancellation/fault cannot invalidate immutable
completed facts or previous continuations. Cancelling an independent export discards that copy and does not
poison its source solve. No failed solve, cancelled copy or unfinished unit can export a continuation.

Exposure settlement is charged as WORK, not storage (2026-11-16): one unit per settlement frame of the unit
the operation admitted (`PropertyExposureResolver.SettlementFrameWork`; an eager compilation's frames to its
admission operation, a deferred unit's to its materialization). The frame count measures work independently of retained
storage and can outgrow the source: quadratic for a member chain whose links own parameters, exponential when a
link reads two members below it. The charge counts against 16,384 + 1,024F and so does not move with the
envelope. Exposure runs before the unit is sealed, so the ledger is still the producer's; a standalone analysis
of a sealed or host-built tree has no operation and is not charged. Measured: the written chain
`P{i} = { public A(x) = P{i-1}.A(1) + 1 }` (F = 20D + 181, D² frames) is refused from 20,392 links, and a chain
whose members each call the two links below from 25 (`language-rules/evaluator-and-hosting.md`, SETTLEMENT FRAME
CHARGE; `ExposureSettlementFrameChargeTests`).

Frozen state shares immutable syntax/member indexes and persistent maps. New syntax graphs are completed
before export so a failed later unit cannot add unrecorded lazy storage to a previous snapshot. Retained
admission counts unique frozen entries and completed projections, excluding discarded operation-local
wrappers; it is distinct from cumulative allocation/work. Copies contain no producer engine or token.
Measured provider/name and contextual-body products can still require quadratic numbers of logical facts;
Gate C establishes finite enforcement and the measured families, not universal FE-1 linearity. See
`experimental/features/alias-unify-1-b32-gate-c-2026-10-29.md`. The superseded structural authorities are deleted; final Gate D acceptance follows the current gates above.

## 4. Query catalog (stages B3-1 to B3-5)

The stratum (OD-D's lower, final and formation readings) is part of a key. A lower stratum never reads a higher one;
the definitions assert this.

| Query | Value | Reads | Replaces |
| --- | --- | --- | --- |
| Q1 `Binding(scope, name, stratum)` | A declaration, a parameter (written or inferred) of an owner, an opened member with its provider identity, ambiguous, unbound, or Unknown | `IsInput` of each owner on the walk (inputs are owner-walk parameters), `OpenProviders` | The detector's and resolver's lookups (`ElaboratedScopeLookup` owner walk, `DirectDeclaration`, `StaticOpenedDeclaration`, `MayInferParameter`, `IsInferredByAnEnclosingBody`) |
| Q2 `OpenProviders(level, stratum)` | Ordered provider list (Q-19 identity) | `TargetWalk` of reference targets (OD-C) | `GetResolvedOpenProviders(stratum)`, `StaticOpenProvider`, `StaticChaseMemos.OpenProviderOf` |
| Q3 `TargetWalk(body, stratum)` | A static algorithm, a carrier, a runtime reference, not static, refused (OD-D), or Unknown | Ordinary `Binding`/`Members` reads; conclusive next walk via `Follow` (§ 3) | `ChaseStaticStructure`, `StaticReferenceStructure`, `StaticCycleCheck`, `StaticStructureMemo` / `StaticChaseMemos.Structures`, `AliasStructureCell`, `SuspendChase` / `TakeSuspendedChase` |
| Q4 `Members(structure)` | Declared members (any visibility), branch-only marks | — | `TryLookupProperty`, `DeclaredMember` |
| Q5 `MissSelection(edge)` | Never / MAY / MUST | The receiver's `TargetWalk` / `Members`; whether a link body keeps an input (`Signature`) | Detection's stamp and the resolver's refinement (`MissSelectionOf`, `ReadReceiver`, `ReadDeclaration`, `CertainMissDecidesALift`, `StaticFallbackCalleeKind`, `ProvisionalMiss`, `CertainFallbackReports`) |
| Q6 `IsInput(body, name)` | Yes / No / Unknown | `Binding`, `MissSelection` of the edges whose fallback is the name | The decider (`InputDecider`, `InferredInputDecisions`, `AgreesWith`, repeated passes, tentative forget/settle, `SuspendWalk` / `TakeSuspendedWalk`) |
| Q7 `Inputs(body)` | Ordered inputs (first semantic occurrence plus Grace movement) | `IsInput` of each candidate | The detector's collection order |
| Q8 `Signature(body)` | The selected signature: inputs plus the parameters formula lifting adds (B3-5★, § 10) | `Inputs`, the role classifier (`FormulaLiftingRoles`, kept), `Signature` of callees through aliases | Replaced at B3-5★ by signature selection: processing order and its repairs (`PropertyLoop`, `SiblingOrderLookup.RefinedMiss` / `OwnedMemberSibling` / `OpenedSiblingProvider`, soft preferences, `EnsureOnDemand`, `ProcessedFormOnDemand`, `DemandDepthBudget` nesting) are deleted |
| Q9 `AliasTarget(body)` | Reference(target), carrier(target), runtime, or no alias | `TargetWalk` (formation stratum), `Signature` | `TryCompleteLoneCalleeRow`, `RuntimeAliasRow`, `AliasTargetCell` / `PendingTargetOn` (B3-5★: completed from the selected endpoints, through region aliases) |

**Consumers (production Q1–Q7; Q8/Q9 consolidated at B3-5★, § 10).**

- The detector rewrites names from Q1/Q7 and stamps Q5.
- The resolver reads Q1–Q7 and selects Q8 before its rewrite (B3-5★, § 10); there is no processing order.
- Exposure, the editor model and the provenance finalizer read the same answers.

**Queries never report.** Diagnostics stay with the passes, at their current sites and in their walk order, so report
order is preserved wherever answers are unchanged.

## 5. A1 inside the model

- **Unknown means self-dependent.** A decision `IsInput(body, name)` is left Unknown by the least fixed point exactly
  when it depends on itself through no well-founded reasoning. Examples: `x` is an input iff `y` is not and vice versa
  (two consistent answers); `m` iff `n` and `n` iff not `m` (none); the positive loop `a` iff `a`.
- **Rejection.** A body with any Unknown decision gets exactly one diagnostic.
  - Production diagnostic: `DiagnosticCode.SelfDependentInferredParameters` and the corresponding public
    `KatLangErrorCode` member (both already appended in the API baseline).
  - It is placed at the body's definition name and lists the undecided names in first-occurrence order.
  - Diagnostic form: "The parameters inferred for 'P' depend on themselves: whether 'x' is a parameter depends on the
    answer itself. Declare P's parameters explicitly, or remove the dependency."
  - The body publishes no inference, and dependent lifts are suppressed. The operation is already rejected, so this
    avoids cascading errors.
- **Diagnostic recovery after A1 (F4, 2026-10-31).** A1 stays a rejection: the unit (the eager program or one deferred
  branch) is never forwarded, exposure-settled, frozen or published, and is never evaluated.
  - Independent errors are still reported where the detected tree alone establishes them: the parameter/property
    collision rule runs over the detected tree, after detection's own reports
    (`ParameterPropertyCollisionValidator.ValidateAfterSelfDependentInference`, from `FrontEndPipeline` and
    `DeferredModuleRegion.CompileLoadedBody`). A detected signature holds the written parameters and the inputs Q6
    decided Yes; an undecided input is absent and forwarding only appends, so every collision found holds for any
    completion. A collision only an undecided input or a forwarded parameter could cause is not reported, and the
    walk records no completed bindings on deferred regions.
  - Deliberately suppressed, because they read signatures, targets or forwarding outcomes the undecided inputs
    leave open: implicit-argument resolution and its reports (`UnforwardableParameter`, `UnforwardableCallable`,
    `UnliftableClauseFamily`, …), the `open` provider rule (`UnresolvedOpenTarget`, `IllegalInOpen`, …), the
    inferred-parameter output rule (its message lists the completed signature) and exposure settlement.
  - Recovered reports use the same bag (budget, prefix law, marker) and the same phase order as an ordinary run; a
    provisional elaboration still withholds them.
  - Editor tooling inspects the erroneous, non-evaluable detected tree; its sealed completed facts keep the
    A1-affected entries unavailable (`A1DiagnosticRecoveryTests`).
- **Order independence.** The least fixed point is unique, and path-step returns are structural facts.
- **Minimal rejection.** Branch agreement decides any decision whose answer does not actually depend on the unknown.
  For example, `a` iff (`a` or true) is decided Yes.
- **Escape hatch.** An explicit parameter list makes the body closed, so it infers nothing.
- **Expected outcomes for the witnesses** (owner-decision brief § A.3):
  - A.3.1 (two answers), A.3.2 (no answer) and A.3.3 (one answer reachable only through a self-read): rejected.
  - Every body whose decisions do not read themselves keeps its current signature.

## 6. Preserved guarantees

| Guarantee | How B3 keeps it |
| --- | --- |
| Ownership-first lookup | Q1 is the one implementation of the six ordered rules: owner walk (written and inferred parameters, properties, prelude), then opens per level. Identity never depends on spelling. |
| M4★, OD-B–OD-E | Encoded once, in Q3/Q9. NEED-04, the evaluator and Lean are untouched: this is front-end only. |
| Non-alias behavior and report order | Passes keep their walks and report sites; differential runs over the saved probe corpora at every stage. |
| Laziness | Front-end only; no runtime change. |
| Resource bounds | One memo per operation; module units once per operation (Q-32); iterative worklist/graph loops; finite operation-scaled work/read/entry/refinement bounds and cancellation. Actual query callback and fan-in costs must satisfy § 3. |
| Deferred units | A deferred branch runs with its own engine, which reads the eager operation's final answers for keys outside the unit. |

## 7. Stages and exit criteria

Each stage switches one whole capability and deletes the mechanism it replaces in the same stage, so the front end is
never partly on two models for one capability.

| Stage | Work | Exit criteria |
| --- | --- | --- |
| **B3-0** (done) | Engine core | Least fixed point over random three-valued circuits in every demand order; deep chains without host recursion; models of the A1, OD-D and navigated-body witnesses; limits |
| **B3-1** | Key model and AST adapters: scope and level identities shared by detector, resolver and editor; module and deferred units | Unit tests on identity and sharing (DAG, module splices) |
| **B3-2** | Q1–Q4. The detector's static chases and the resolver's static reads switch to them, and their memos and suspension machinery are deleted. | Navigated-body witnesses (`probe-cases-r9h.txt`): `strata0-get` = 42, `strata0-ambiguous` = static `AmbiguousOpen`. All alias and ownership suites pass. |
| **B3-3** | Q6–Q7 plus the A1 diagnostic. The decider is deleted. | A.3.x witnesses rejected in every order. HEAD signatures for every non-self-dependent body (differential over all saved probe corpora). |
| **B3-4** | Q5. The resolver refinement and deferred checks are deleted where subsumed. | Round-12/13 refinement witnesses |
| **B3-5** | Q8–Q9. Processing order, the channel's repairs, soft preferences, on-demand processing and demand nesting are deleted (done as B3-5★, § 10). | Round-14 witnesses: no `AstDepthLimitExceeded` on the K = 40 chains, order-independent results. Rounds 12–13 witnesses. |
| **B3-6** | Editor and exposure consumers; `AGENTS.md`, `ownership-and-lookup.md`, `SEMANTIC-ALIGNMENT.md`; spec cases; A1 public code and the API baseline | Editor suites, spec artifacts |
| **B3-7** | Mutation runs, differential tests within the suite, full V3 (one ordinary `-Phase DotNet`, one `-Phase Lean`; local execution only when requested) | All green |

## 9. Stage soundness (B3-1, 2026-10-28)

### 9.1 Identity: implemented and tested (`src/KatLang/StaticKeys.cs`, `StaticKeyTests`)

- **One key per written body across passes.** Every written `User`/`Conditional` body keeps its `DeclarationIdentity`
  through detection and resolution: the passes rewrite with `with`, and alias formation passes the written body's
  identity on to the `Algorithm.Alias`. No provenance map is needed.
- **Scope keys.** `StaticScopeKey` interns the declaration chain that `OpenProviderIdentity` already compares.
  - The detector's levels (`ElaboratedPropertyScope`), the resolver's chains (`DeclaringOwners`) and its levels
    (`ResolverLevel`) map to the same key.
  - Key equality is exactly provider-identity equality; an exhaustive pairwise test checks this.
  - A loaded module has one key wherever it is held.
  - A body shared by two contexts (a host DAG) has one key per context.
- **Deferred units.** Their runs build levels on the eager chain, so the same rule gives the same keys. B3-2★ tests
  this on real deferred branches.
- **Query keys.** `StaticQueryKey` gives one key type for every query family. Scopes and expression nodes compare by
  reference: an `Expr` record's own equality is structural, so two equal edges written twice are two questions.

### 9.2 The Q1/Q3/Q5/Q6 cycle

The reads between queries:

| Query | Reads | Why |
| --- | --- | --- |
| Q6 `IsInput(b, n)` | Q1 `Binding(b, n)` | Whether `n` is unbound after the owner walk and the opens |
| Q6 | Q5 | For the edges whose fallback name is `n` |
| Q5 | Q3 / Q4 | The receiver's structure: a navigated body, a reference's target, a runtime row |
| Q3 | Q1 | Row heads and path steps |
| Q3 | Q6 | A head naming an input of the body or of an enclosing body is a runtime reference, and a navigated body's own input stops a walk (the navigated-body defect) |
| Q1 | Q6 | Inferred inputs are owner-walk parameters, so an enclosing body's input shadows a nested body's opens |
| Q1 | Q2 | `open` providers |
| Q2 | Q3 | OD-C: a static reference opens its target |

So **{Q1, Q2, Q3, Q5, Q6} is one strongly connected capability**; Q4 and Q7 hang off it. Consequences:

1. **The planned B3-2 (Q1–Q4 without Q6) is unsound.** Its Q1/Q3 would have to read input decisions from the old
   decider, whose answers come from the old chases. That is two authorities for one fact, which recreates the
   detector/resolver disagreement. **B3-2 and B3-3 are therefore one stage, B3-2★ (static structure and inference).**
   - It covers Q1–Q7 and A1.
   - In one step it switches all of parameter detection's static chases and input decisions, and the resolver's static
     structural reads: alias formation's OD-D verdicts and static targets (`TryCompleteLoneCalleeRow`,
     `IsCyclicReferenceChase`), its open providers, and the structure half of its miss refinement.
   - The decider and both chase implementations are deleted in the same stage.
   - Acceptance is the union of the old B3-2 and B3-3 criteria.
2. **A1 belongs to this SCC's fixed point.**
   - A body is rejected exactly when one of its input decisions stays Unknown.
   - A pure path return is an OD-D refusal, a definite answer.
   - A dependency cycle that no input decision reads cannot reject anything.
3. **Q8 joins the SCC through link bodies.** Whether an `.Algorithm` link body is a calculation or a runtime reference
   depends on what formula lifting leaves it (META-S3-2), and the resolver's MAY→MUST refinement reads that.
   - B3-2★ keeps that refinement, reading engine structure instead of its own chase. That is today's documented split
     between detection's verdict and resolution's refinement, not a second authority.
   - The refinement moves with Q8; old stages B3-4 and B3-5 merge as B3-5★.
4. **Owner decision needed before B3-5★** (decided 2026-11-03: (b), X-04 = B; superseded 2026-11-05 by simultaneous completion, § 10.1). Inside a sibling cycle, today's rule is the documented processing-order
   fallback (X-04): members are processed in declaration order, and the first one reads the others' unprocessed
   signatures. A least-fixed-point Q8 changes that observably. The order-independent choices are:
   - (a) the least fixed point over lifted-parameter sets, where each member of the cycle gets the union;
   - (b) rejecting lifting cycles the way A1 rejects self-dependent inference.

   Neither A1 ("implicit parameter inference") nor B3 ("preserve existing non-alias behavior") decides this.
5. **Monotonicity.** Every edge in the SCC is a three-valued read with branch agreement.
   - A binding whose input decision is Unknown is itself Unknown, unless both branches select the same declaration.
   - Input-ness is "unbound and used" or "a certain fallback"; three-valued negation is monotone.
   - OD-D's lower and final readings are stratified (the stratum is part of the key; the final reading reads the lower
     one), so no cycle crosses strata.
   - An ambiguous open (two providers) is a definite value.

   No non-monotone selected rule was found. This is an analysis, not yet a proof on real queries; B3-2★ adds
   order-permutation tests per query.

   Correction (S-10 F3, November 2026): that statement was false for the open stratum. `P5 = { open P3 ⏎ Z }`,
   `P6 = P6`, `P3 = P6.Algorithm` (K01) answered `Missing` for the open structure of P3 and later, once the
   receiver-return guard turned true, P3's own structure, which `IsRefinement` forbids (a host exception in some
   declaration orders). Two causes: the open branch of `WrittenRowTarget` answered `Missing` for every row that is no
   reference (a member miss or a head that is no static path), and the open stratum's guard found receivers through
   opens while the open target itself resolves directly (Y1, a head only an open provides). The fix answers the
   own-namespace fact for a row that is no reference (Lean `openStructure`), keeps a miss's terminal in the fact so
   completion can tell a reference (unresolved) from a body that is its own namespace (`CompletedMiss`), and makes the
   open stratum's receiver expansion follow direct bindings (`OpenReceiverExpansionCycle`/`Step`/`Nav`/`End`/`Verdict`
   read `OpenHeadBinding`). Agreement argument: whenever the direct guard will become true, the non-pending branch
   answers Unknown or exactly the pending arm's own-namespace fact (a row that is no static path names no expansion
   target; a direct miss stops the direct chain, which then cannot return; a hit on every step passes only declared
   members, which a returning lone row does not have). This is still an argument, not a proof; the evidence is the
   41,472-program × 24-order sweep and `OpenLoneDotRowProviderTests`.

   Correction (E-18 owner decision Q3, 2026-11-14): the open branch of `WrittenRowTarget` keys the BLOCK head of a
   reference's row under the reference (`DirectPath`, `blockHeadUnderScope`), where the evaluator's `OpenStructure`
   wires it and where the value reading of the same row already keyed it. It was keyed at the root, as a block
   written as an open TARGET is, so `open L` with `L = { … }.Sub` selected nothing statically. A block written as an
   open target stays rooted at the prelude. `ExposureAccessCheckTests`, `SemanticModelTests`.
6. **Editor.** The editor reads the published elaborated tree: formed aliases carry their targets, and inputs are
   `Param` nodes. B3-2★ must list every `ElaboratedScopeLookup` chase entry point the editor still calls. Any that
   remains reads the front end's engine through the parse result, never a third chase.

### 9.3 Revised stages

| Stage | Content |
| --- | --- |
| **B3-0, B3-1** | Done |
| **B3-2★** | Q1–Q7 and A1, as above. The scale: `ElaboratedScopeLookup` (2,730 lines), `ParameterDetector` (3,568), `ImplicitArgumentResolver` (6,630) and `PropertyDependencyGraph` (4,322) together hold the mechanisms it replaces. The list is in the B3-1 checkpoint report. |
| **B3-5★** | Q8/Q9, the miss refinement and the processing order, after the owner decision in § 9.2(4) — done (§ 10) |
| **B3-6, B3-7** | Unchanged |

## 8. Risks

- **Monotonicity.** Every query definition must be monotone and must apply branch agreement. Limits can detect some
  failures to converge, but cannot certify monotonicity. Each query needs independent oracle and permutation tests;
  dependency-only circuit tests alone do not validate OD-D path-context handling.
- **Callback cost.** Batching reads alone does not bound repeated wide scans. Real queries must establish the R/fan-in
  bound in § 3; FE-1 complexity tests read `Statistics`, including total reads and allocation cost.
- **OD-D strata.** The lower, final and formation readings must keep their exact current meaning. Port them with the
  existing OD-D regression classes as the oracle.
- **Size.** `ElaboratedScopeLookup`, `ParameterDetector` and `ImplicitArgumentResolver` are large. The stage gates
  above are the protection against a half-migrated capability.
- **Obstacle protocol.** A fundamental obstacle, such as a selected rule that is not monotone in any information
  order, is to be documented here and stopped for an owner decision. It must not be worked around by narrowing M4★.

## 10. B3-5★: signature selection (November 2026)

Owner decisions (2026-11-03): X-04 = B, CG4 = A-agree; § 9.2(4)'s option (b). **Superseded for X-04 on 2026-11-05: plain
A-agree with R1 origins (§ 10.1).** CG4 stays A-agree. The design below stands, with the closed gate's lifting branch
replaced as § 10.1 says.

### 10.1 Simultaneous completion and origins (owner direction 2026-11-05)

Normative text: `docs/design/language-rules/ownership-and-lookup.md` § Recursive parameter inference. Mechanics:

- **Rounds.** `SignatureSelector.Complete` iterates `F^{k+1}_i = C(i, F^k)` from the closed gate. The state is every
  member's pattern tree and X-02 flag, compared structurally (`SamePatterns`), never by object. Brent's rule keeps two
  detector snapshots, so a repetition at distance above one is found without a history table; a composition is a pure
  function of the state, so that repetition proves non-settling. The rounds are SEMI-NAIVE (2026-11-14, audit of
  `a4b545e8`): round one recomposes every member, and a later round only the in-component readers of the members whose
  fact object changed in the round before, in ascending position; every other member keeps its fact, which is exactly what
  recomposing it would return, since its reads are the same objects and the equation memo returns one fact per exact
  inputs. Settlement compares only the changed members with their previous facts, and the repetition detector keeps one
  snapshot and a count of the members that differ from it structurally, updated for changed members alone. So a ring whose
  names travel one member per round costs its rounds once, not once per member. Each recomposition is charged its
  composition's work before it runs; the storage of a NEW fact (round lists stay in the run's template interner) is
  charged before it is composed, and a recomposition that finds its fact retains and is charged no storage.
- **One object per reading.** `EvaluateEquation` keeps one fact per equation per exact lifted inputs, and `Sealed` keeps
  one sealed result per exact settled facts, both hashed by the identities they compare (a lookup costs its inputs, never
  the readings already stored). A table or joint region that reads a component again therefore gets the same objects, and
  a selected reader's composition and the rewrite agree by reference.
- **Sealing.** `SealCompletion` (`ImplicitArgumentResolver.CycleOrigins.cs`) runs inside `Complete`, before any reader
  composes: readers must lift final records. It derives origins by the first-provider law, builds final lists, recomposes
  every member from them with the real law, and requires the same structure and origin content. `Composition`, including
  X-02's `Unrecovered`, comes from that recomposition.
- **Carrier.** The capture record. A determined capture holds its origin's record, or a kind-correct view with
  `ParameterDeclaration.OriginalDeclaration` when the kinds differ. A cycle capture is a generated record with no span whose
  note carries `ParameterCycleOrigin`. Identity of a source: `ParameterOriginKey`. Templates intern by record, so origins
  need no side table and no extra publication step; they are published by what publishes the signatures, on success only.
- **Contexts.** A body served to several contexts is one record, so a cycle's members are named relative to the innermost
  body declaring them all: that holds in every context the record reaches. Origins follow the same projections as the body.
- **Member metadata.** Captures with the same semantic cycle-member set share one immutable member array and its paths,
  interned within the seal by equation identities. Each capture keeps its own sources. Temporary keys and path preparation
  are admitted to the ledger, and joined path text is charged in work and storage before allocation; a returned array
  retains no interning cache, operation or token.
- **Settled cycles without a source.** Q-04 can make a callee stop lifting after its name entered a cycle, so a settled
  cycle can have no reachable source. The descriptor then has no roots: nothing is invented and nothing is refused.

  Complete witness (`CycleOriginConsumerTests.RootlessLater`; `RecursiveOriginOracleTests` derives the same rounds on its
  own model, and `HasSharedCycleOrigin` with an empty `OriginSpans` is what the semantic model reports for `A` and `B`):

  ```katlang
  P(n) = n
  Q(k, *n) = 0
  Outer(k) = {
      public C = D + P
      0
  }
  A = B + Outer.C
  B = A + 0
  D = E + P
  E = Q + A
  0
  ```

  | State | A | B | C | D | E | What changed |
  | --- | --- | --- | --- | --- | --- | --- |
  | closed gate | () | () | (n) | (n) | (k, \*n) | `P` and `Q` are the only lifted callees |
  | round 2 | (n) | () | (n) | (k, \*n) | (k, \*n) | `A` lifts `C`; `D` lifts `E`, whose `*n` claims the name before `P` |
  | round 3 | (n) | (n) | (\*n) | (k, \*n) | (k, \*n) | Q-04 drops `k` from `D`'s list in `C`, so `C` accepts zero arguments |
  | round 4 | (n) | (n) | (\*n) | (k, \*n) | (k, \*n) | `A` no longer lifts `C`; it keeps `n` from `B`; settled |

  The provider graph of the settled state is what R1 reads. `A`'s only provider of `n` is `B` and `B`'s is `A`, so the
  first-provider cycle is {A, B}, and neither has an edge leaving it: the root set is empty. History is not a provider: `P`
  brought the name in through `C`, but `C` is inert in the final graph. `C`, `D` and `E` have the determined origin `Q.n`.
  A reader such as `R = A + 0` holds the same record, an earlier rootless origin adds no root to a later cycle, and reports
  say that no source declaration supplies the name. Such members depend on the enclosing parameter that filtered the callee.
- **Provisional violations.** The X-02 flag is state, not a refusal. Both programs below start from `C1(a, *p) = a` and
  `C2(b, *q) = b`, with `B = A + 0` (`!` marks the flag):

  | State | `A = if(tick() > 2, 0, B + C1 + C2)` | B | `A = if(tick() > 2, 0, C1 + C2 + B)` | B |
  | --- | --- | --- | --- | --- |
  | closed gate | (a, \*p, b, q)! | () | (a, \*p, b, q)! | () |
  | round 2 | (a, \*p, b, q)! | (a, \*p, b, q) | (a, \*p, b, q)! | (a, \*p, b, q) |
  | round 3 | (a, \*p, b, q) | (a, \*p, b, q) | (a, \*p, b, q)! (settled) | (a, \*p, b, q) |
  | round 4 | (a, \*p, b, q) (settled) | (a, \*p, b, q) | | |

  `KeepFirstCollectingCapturePerLevel` makes the later collector plain in the recovered list. Read first, that list binds
  `q` as a plain name, so `C2`'s `*q` is a repeat of a bound name and contributes nothing: the composition is valid and the
  flag clears. Read last, `C1` and `C2` have already composed both collectors, so the reader's plain `q` adds nothing and
  the flag stays: `InvalidCollectingBinding` at the `C2` reference, on every route, with no evaluation.

**Design.** Implicit-argument resolution has two phases.

1. **Analysis** (`ImplicitArgumentResolver.SignatureAnalysis.cs`): the same recursion the rewrite makes, writing
   nothing the rewrite reads. One **equation** per written open body per declaring context (D1a): the body's own
   patterns and its value-role references in written order, each with its static callee identity
   (`ResolveStaticCallable`, every reference row followed to its Q3 endpoint) and, where a link's class decides
   whether the read is a value read, that link as its guard. The walk is the ONE formula-lifting role walk
   (`WalkLiftingRoles<TSink>`), instantiated by the analysis (`EquationSink`) and by the preselection
   potential-lift reachability of output spreading (`PotentialLiftSink`); the rewrite reads each body's lifted
   dependencies from its selected composition and never walks its rows again to collect them. DAG safety: regions are memoized by `AnalysisRegionKey` (node, free-name
   identities, forwardable and collecting names, closed spec, opens), which refines the rewrite's region key, and a
   path-sensitive context the analysis served from another context's analysis is mapped to that counterpart
   (`SignatureKeyAliases`).
2. **Selection** (`SignatureSelection.cs`, `SignatureSelector`): rule G6 over the equations. A guard vector
   classifies every link; Φ_B evaluates the active read graph dependency-first, a cyclic component by the closed
   gate (every member read as declaring nothing: no lifting inside the cycle gives its unique non-lifting meaning,
   Lemma B1, and a lifting read inside it makes it a genuine lifting cycle, completed as § 10.1 says); a vector is consistent
   when every link evaluates to its class and every body has a meaning, grounded when every nonempty set of its
   calculation links is refuted (three-valued, U1). G6 selects the unique grounded consistent vector; otherwise the
   group is refused by category (`SignatureSelectionOutcome`: Ambiguous, Contradiction, UngroundedOnly,
   Undetermined, NonSettling; readers of a refused group are Blocked and not reported again). Components are an
   optimization only: a dependency-first local pass, then joint regions — every failed component with the closure of
   its readers, regions whose dependency cones meet merged — solved over their cones by persistent
   alternative-carrying stratification in two phases (`SolveRegion`, 2026-11-14, audit of `a4b545e8`, finding 1.8).
   Phase 1 carries every component of the cone the local pass settled by its selected reading alone and enumerates the
   failed components; phase 2 enumerates the whole cone, reusing phase 1's tables, only when phase 1's outcome is
   NonSettling or Contradiction and a settled component of the cone has another reading that is not refuted. That is
   exact: a settled component reads only settled ones, so along their selected readings its table is its local one,
   whose only grounded row is the selected one and which has no undetermined row; an alternative carrying another of its
   rows is ungrounded or meaningless for good, so it adds no grounded or undetermined row and can change only a
   refusal's category, never a selection. A joint region the ledger cannot afford is still refused as
   `StaticStructureLimitExceeded`; what is no longer paid is the product of the readings of settled components. All work
   and storage are charged to the operation's ledger (`StaticQueryResourceBudget`; a table charges its 2^dimensions
   classifications before evaluating any).
3. **Rewrite**: declarations in their elaborated order over the selected signatures. The rewrite never recomposes a
   signature (`SelectedLifting`); `RequireSelectedComposition` checks, by reference and in O(recorded rewrite DAG + dependencies),
   that the body's rows, once rewritten, lifted exactly the callees the selection composed from, each callee's FIRST
   lift in the composed order and with the composed signature object (each lift is decided by the rewrite itself,
   never read from the composition). The rewrite logs its lifts where it makes them (`OpenBodyLiftLog`), inserting a
   dot edge's receiver lifts before its argument lifts and a hoisted deconstruction right-hand side's before its
   row. Memo hits link the already recorded segment at their own position; comparison visits each segment once in
   role-walk order, so sharing never disables order or first-signature checks and never expands logical paths. The
   log charges its allocated storage and comparison work to the static ledger. No AST is walked again and no wide
   signature is flattened (`SelectionInvariantLiftLogTests`, negative cases, exact DAG-work pins and host-DAG/tree
   comparisons across receivers and hoisted sources). Its mirror, THE REACH INVARIANT
   (`RequireEveryAnalyzedBodyRewritten`, S-10), checks the other direction once the rewrite (eager, or a deferred
   unit's) completes: every body the analysis recorded, open or closed, has a resolved view — processed in that
   context or served through a region alias — so "the same recursion the rewrite makes" (item 1) is enforced, not
   assumed. Its counterexample was S-10 F1: the analysis recorded the bodies of a block written in a preserved bare
   root row (`{ public K = … ⏎ 0 }.K`), while the rewrite returned the row unchanged, so the evaluator ran `K`'s raw
   body (a wrong value, the wrong callable blamed, or a lost front-end error). The root clause now keeps the row and
   processes its block head (`WithProcessedBlockHead`), and a skipped body is an internal failure, never a program's
   result. The resolver's region key (`AlgorithmRegionKey`, through `FreeReferenceNames`) also counts a body's own
   `open` heads, never removed by the level's declarations, as detection's `RegionFreeNames` does (S-10 F2), so one
   shared body whose open heads select different callees under two parents gets one signature per parent on the
   name-resolved route too. Region memo hits are recorded as **region aliases**
   (`StaticStructureOperation.AliasResolvedRegion`): resolved views and pending target and structure cells below a served
   context are read through its counterpart (`ResolvedView`, `RegionCounterpart`); a served context's completed facts
   are its own (contextual identity, receiver, open, providers) over the counterpart's processed view, and every context
   below it is a lazy **projection** of its counterpart (`CompletedStaticStructures`; independent review checkpoint 3b,
   finding 1; checkpoint 4): one key per context by every route (`CompleteLookups` pairs the compilation's own keys
   with their counterparts definition by definition), selections inside the region re-based onto the occurrence and
   re-declared there, members that restart outside it (module roots) kept, and the view exposure gave that occurrence
   (`RetargetTree` walks each exposed node beside the view it was copied from — so a copied member, branch body or inline
   block, deconstruction rows included, finds its context through its original — and records a view, level by level, only
   where exposure copied the occurrence); projected facts are recomputed only when their counterpart's facts or their own
   view change; the walks over members, providers, counterparts (a current entry's validation included) and ancestors
   are charged, and so are the declaring
   chains a reach records and a projection re-declares (the body index walks each owner once per build and checks a
   context against reaches only inside a served region);
   continuations carry the aliases to deferred units (`EarlierResolvedView`), and a later unit inherits the projections
   made before sealing.

Refusals take A1's recovery route (`FrontEndPipeline.RecoverAfterSelfDependentInference`, and the deferred-unit
equivalent in `DeferredModuleRegion`). Deleted: `PropertyLoop`, `PendingProperties`, `DemandDepthBudget`, on-demand
processing (`EnsureOnDemand`, `ProcessedFormOnDemand`), the mutable signature map's pending/current members, the
open-provider snapshots, `PropertyDependencyGraph`'s order channel (`SiblingOrderLookup`, `RefinedMiss`, soft
preferences, `SettleSoftCycleConsumers`, `CyclicIndices`), and `PropertyProcessingOrderTests`.

**Evidence.** Research outcomes carried forward as tests (`SignatureSelectionTests`): D06 = 5, D15 = 4, ReadQ
(7, 7, 8, 100, 100, 100), the FU7 example (100, 7, 0), deferred 10/11, case H's module reuse. The independent oracle
(`SignatureSelectionReviewRegressionTests`): rule G6 applied to whole random equation systems agrees with the
selector on every system (six seeds × 500, each system also with independent, locally settled self-rings inside its joint
cones), and two mutation controls show it can fail (guard-blind rounds, and rounds that skip a member whose read changed);
W14u selects jointly in 120 of its 720 declaration orders, and still with 7, 16 or 32 settled rings read by its reader
(formerly refused by the ledger from 7). Independent
read-only reviews (Codex, gpt-6.1-sol at maximum effort): checkpoint 1 (plan) and checkpoint 2 (implementation) each
required changes, all resolved; their reports are under
`artifacts/validation/alias-unify-1-b35-production/review/` (git-ignored).
