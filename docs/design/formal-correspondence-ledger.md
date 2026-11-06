# Formal correspondence ledger

The one tracked status of what is proved, about what. Older labels (R4, R6, CF-4, R7, FG-H1) are kept only where they name a
live claim. A theorem name is not a proof of a broader claim, and a stale paragraph is not evidence that a theorem is missing:
read the statement. Last reconciled 2026-11-06 at the SC-1 / FC-AC review.

**Evidence categories.** *Production Lean*: a kernel theorem about the definitions of `lean/KatLang.lean`, with its production
instance discharged. *Conditional*: a kernel theorem whose named premises are not all discharged for production. *Reference
kernel*: a kernel theorem about `KatLangArityLaws/SignatureCompletion.lean`, a front-end model, not the evaluator and not C#.
*Guard*: an executable Lean check. *C# differential*: native code compared with Lean on a stated finite corpus. *C# test*:
native tests with no Lean counterpart. *Source*: inspection only. *Open*: well specified and unproved.

**The boundary.** A Lean theorem is about Lean. Agreement with C# is finite executable evidence. There is NO machine-checked
bridge from any C# source to any Lean term in this repository: no extraction, no formal C# semantics, no translator. Every row
that reaches C# is therefore tested correspondence over a trusted boundary. Universal verification of the C# compiler and
runtime is not established and is not claimed by anything here.

## Evaluator and heap

| Id | Proposition, domain | Definition concerned | Result | Premises and their status | Category | Remaining bridge |
| --- | --- | --- | --- | --- | --- | --- |
| E-1 | Production operation completes with `r` iff the fuel core does; a completed outcome is its body over production. All calls, all entry states | `evalUnbounded`, `evalFuel`, `evalStep` | `production_completes_iff`, `production_unfolds`, `invariant_transfer` (`EvaluatorCore.lean`) | None. The converse of unfolding needs finite use of recursive answers: `production_eq_of_finite`, for row readers and the activated-body boundary only | Production Lean | Converse unfolding in general; a kernel proof that a program diverges |
| E-2 | Existing cells keep suspension, completed VALUE and prepared supply. All operations, all entry states | `Disciplined`, `evalUnbounded` | `productionDiscipline_holds` (`EvaluatorDiscipline.lean`) | None | Production Lean | None for Lean |
| E-3 | Completed CALLABLE, recorded callee and receiver survive an operation | `LinkKept` | `evalUnbounded_linkDisc` (`EvaluatorMemoLinks.lean`) | Entry-state preservation only; no in-flight first-writer law | Production Lean | None for this statement |
| E-4 | Published cache entries survive; the active owner set is restored | `CacheKept`, `ActiveKept` | `cache_entries_survive`; `owner_set_restored` (`EvaluatorCacheLaws.lean`) | Survival: none. Restoration: COMPLETED runs only (an incomplete inner run may leave its mark) | Production Lean | Key injectivity; no self-publication of a reentrant run |
| E-5 | Every stored need address is inside the heap. Every operation, every outcome | `Inv`, `CallPre`, `CallPost` | `production_sound_all` (`AddressInvariantProduction.lean`) | From an `Inv` state meeting `CallPre`; holds of `EvalState.empty`. Older FG-H1 lemmas in `HeapAddressValidity.lean` are CONDITIONAL on `SpreadSound`/`ChannelsSound`, which are false over `StateValid`, and are not this result | Production Lean | `runResultM`-level instance (E-6) |
| E-6 | Public run ≡ public composition over the core | `runResultM` | `public_bridge`, `public_fuel_cases` (`PublicRunBridge.lean`) | Parametric in the `partial`, kernel-opaque prefix (identification, validation, wiring): nothing is claimed about what those do | Conditional | Totalizing that prefix (Tier 2, R7-FU-01) |
| E-7 | `while` row control at production (CF-4) | `whileVerdictSlots`, `evalAlgOutputSlots`, `formOutputRow` | `whileVerdictSlots_production`, `production_cf1_false_skips_earlier_rows` and siblings (`WhileRoundProduction.lean`) | Row control is premise-free for checked bodies. The round's dispatch equations keep a completion premise; `FuelReached` for binder/family channels is not proved | Production Lean + Conditional | `FuelReached` for those channels; local-only cache key stability across rows |
| E-8 | Binder order, repeated names, correspondence | `bindNeedPatterns`, `NeedBinder` | `BinderTrace.lean`, `FamilyDispatch.lean`, `BinderCorrespondence.lean`: production runs. R4, `RepeatedNameLaws.lean`, `NestedRepeatedNames.lean`: under completed/Ready and identity-domain premises, with a production stability instance for the binder channels on such cells. R6, `SupplyCorrespondence.lean`: over two READY supplies | The R4/R6 premises are NOT discharged for suspended cells; a suspended argument and its Ready value are not equivalent, by design (CALLABLE and META differ) | Production Lean + Conditional | Suspended-cell correspondence under VALUE agreement: stays a stated premise |
| E-9 | Algebra corresponds to production | `CoreArityAlgebra.bindPats`, `needLevelSources` | `algebra_binder_is_the_production_allocation` | All algebra heads and supplies; the equality explicitly checks at most one collector and the production cardinality gate. ALLOCATION only: the algebra models no repeated-name agreement, structural/literal patterns or VALUE demand | Production Lean (allocation) | Binder-result correspondence: not claimed |
| E-10 | Lean evaluator and C# evaluator agree | `Evaluator.cs`, `eval` | `SemanticExplorerCases`, `LanguageSpecCases`, `HostParentDifferential` | Generated corpora with derived ASTs | C# differential | Universal claim: OPEN, needs a formal implementation bridge |

## Signature completion (SC-1)

The kernel is `lean/KatLangArityLaws/SignatureCompletion*.lean`. Its table of native pieces is at the head of `SignatureCompletion.lean`.

| Id | Proposition, domain | Definition concerned | Result | Premises | Category | Remaining bridge |
| --- | --- | --- | --- | --- | --- | --- |
| S-1 | A selected answer: every equation is the composition law over the selected active reads; links classified by nonemptiness; every support set refuted; no other grounded or undetermined reading. All well-formed systems, all bounds | `select`, `composeWith` | `select_obligations` (`Obligations`) | `System.WellFormed` only | Reference kernel | Native: S-8 |
| S-2 | Publication exposes only a result carrying its obligations; a refusal or exhaustion publishes nothing | `publish`, `Completed` | `publish_refused`, `publish_exhausted` | Well-formed | Reference kernel | C#: `RecursiveInferenceLifecycleTests`, `Exhaustion_IsNeverTheSemanticRefusal` |
| S-3 | Ordered shape: own list first and unchanged, then first occurrences in written reference order, Q-04 names excluded, kinds kept, META lifted ordinary; a group of new names lifts whole; lifted callees are a subsequence of the references | `composeFact`, `liftedFrom` | `composeFact_ordered`, `missingPattern_whole`, `liftedFrom_sublist` | No X-02 flag on the fact; for whole groups: no META, no empty group, names new | Reference kernel | Native: S-8 |
| S-4 | No enumeration selects: renaming keys and callee identities and storing keys in any order gives the renamed outcome; rule G6 reads rows as a multiset | `select`, `rule` | `select_relabel`, `select_storage_independent`, `rule_perm` | Bijective equation-key and injective callee-identity relabelings; storage is a permutation of the renamed keys (`rule_perm` requires a row permutation). No well-formedness premise. Written reference order is kept, and reversing it changes answers (guard) | Reference kernel | Native order invariance: permutation tests and the two oracles |
| S-5 | Acyclic active reads are the composition law in any topological order; no gate lifts, no round runs | `evalVector`, `applyOrder` | `acyclic_agrees`, `acyclic_order_independent` | `Topological`, well-formed | Reference kernel | None in the model |
| S-6 | A non-settling verdict is an exact repeat at distance ≥ 2 and that orbit never settles; a settled state is a fixed point of its round | `completeLoop` (Brent, as native) | `nonSettling_never_settles`, `repetition_never_settles`, `settled_fixed_point` | ONE fixed transition: same system, classification and lower facts. Nothing across changed equations or external facts. No convergence, monotonicity or uniqueness claim: the kernel has a second fixed point in `SignatureCompletionGuards` (`otherFixedPoint`) | Reference kernel | Native loop: S-8 |
| S-7 | Exhaustion is no verdict: a verdict is stable under every larger bound; witnesses show bound 0 with opposite later verdicts. The layers never stick | `select`, `evalVector` | `select_verdict_stable`, `exhausted_decides_nothing`, `no_pending_cell` | Well-formed | Reference kernel | The bound is not the C# ledger; compared with nothing |
| S-8 | The real `SignatureSelector` with the real composition agrees with the kernel: patterns, kinds, flags, refusal categories | `SignatureSelector.Solve`, `SelectSignatures` | `SignatureCompletionBridgeTests`: 299 systems (39 curated, 260 seeded) from real analysis; `#guard renderCorpus bridgeCases == committedOutcomes` in `SignatureCompletionGuards.lean` recomputes the outcomes file | Finite corpus. Mutants through the real selector detected: reversed references 119/299, guards ignored 18/299, links declassified 7/299; in-place rounds detected on the kernel side | C# differential | Universal agreement: OPEN, needs a formal implementation bridge |
| S-9 | Local pass and joint regions equal rule G6 over the whole system | `Solve` | `TheSelector_AgreesWithRuleG6OverTheWholeSystem` (3,000 random systems), S-8 | The kernel states the whole-system rule; native components are an optimization it does not model. A system whose groups refuse by different categories has no compared category | C# test | Proof of the decomposition: open |
| S-10 | Equations are what the source means | `SignatureAnalysis`, `WalkLiftingRoles`, `ResolveStaticCallable` | None | Inputs of S-8, compared for stability only; the two-instantiation role walk and `RequireSelectedComposition` are source and runtime checks | Source + C# test | AST-to-equation extraction is UNMODELED |
| S-11 | Origins (R1), sealing, projections, deferred units | `SealCompletion`, `CompletedStaticStructures` | `RecursiveOriginOracleTests`, `CycleOriginConsumerTests`, `RecursiveInferenceLifecycleTests`, `ASharedBody_HasOneEquation_AndBothContextsReadItsFact` | Origins are sealed after stabilization and are no part of the state (`SamePatterns` ignores records) | C# test | Unmodeled by design |
| S-12 | Resource limits, cancellation, concurrency, host behavior | `StaticQueryResourceBudget` | `AnExhaustedCompletion_IsAResourceRefusal_NeverNonSettling`, `Exhaustion_IsNeverTheSemanticRefusal` | No Lean counterpart | C# test | Not modeled |

The principal theorem dependency audit found at most `propext`, `Classical.choice` and `Quot.sound`; twelve signature theorem checks are pinned by `#guard_msgs` in
`SignatureCompletionGuards.lean`. No `sorry`, `native_decide` or new axiom.

## Acyclicity (FC-AC)

"Acyclicity remains open" named no theorem. These are different graphs, and the answers differ:

| Id | Graph | Status | Evidence |
| --- | --- | --- | --- |
| AC-1 | Host-built ASTs (object references) | Rejected before use, C# only. Lean's inductive `Expr` cannot be cyclic | `AstStructuralPreflight`, host cycle tests. C# test |
| AC-2 | Collector slice edges (cell → slice member) | ACYCLIC. Every edge descends strictly in allocation order, in every `Inv` state; production operations preserve it from `Inv` entries satisfying their structural `CallPre` contract | `collector_path_descends`, `collector_no_cycle`, `production_collector_no_cycle`, `production_collector_no_cycle_from_empty` (`HeapEdgeAcyclicity.lean`). Production Lean |
| AC-3 | All stored need addresses (prepared supplies, values, plans, environments) | NOT ACYCLIC: the conjecture is FALSE. Prepared supply and completed VALUE are written after allocation and can point to younger cells | The final-heap `hasTwoCycle` guard: `P = Capture(Inner(Q))`, `Q = P`, `P == P.Arguments[0]` runs to `true` with a two-cycle `p → a → p` in its final heap (`HeapEdgeAcyclicityGuards.lean`). Guard. C# outcome: `AStoredAddressCycle_IsAValidProgram`; the C# cell graph is not inspected |
| AC-4 | Active VALUE/CALLABLE demand and wait | Cycles are REACHABLE and are the ordinary `demandCycle` failure, so acyclicity is not an invariant. The serial Lean arms raise it on `evaluating`, `preparing` and `projecting` (`KatLang.lean`), guard-pinned. Whether C#'s asynchronous wait-for graph detects every cycle is C#-only and rests on `NeedCell` cycle and cancellation tests; a Lean theorem about serial demand proves nothing about it | Guard + C# test |
| AC-5 | Callable and alias dependencies | Legitimately cyclic: recursion is a language feature. Static alias cycles are refused by their own rules | Guard (`Down`), C# tests |

No proved law depends on AC-3. `Inv` needs validity, not acyclicity, and a stored reference is not a demand. So there is no
residual global acyclicity obligation: AC-2 is proved, AC-3 is refuted, and AC-4 and AC-5 are not invariants. What stays open
about termination is unrelated: no kernel proof of divergence or termination of a specific program.

## Reconciled claims

* "The recursive driver is opaque and whole-run refinement and R7 are open" (`BINDING-ARCHITECTURE.md`): stale. R7 is E-1 to
  E-5. What is left is listed in those rows.
* "Acyclicity remains open" (`EvaluatorDiscipline.lean`, `SEMANTIC-ALIGNMENT.md` FG-H1): replaced by AC-1 to AC-5.
* `demandNeedRecursive`'s wiring as "source/guard evidence" (`CoreArityAlgebra.md`): stale since R7; the driver is a body of the
  total core. The `partial` definitions that remain are the validation, provenance and wiring prefix of E-6 and name lookups
  outside the evaluator core.

## Maintaining this ledger

A change to a row's definition or premise updates the row in the same change. The bridge has its own regeneration flow:
`KATLANG_REGENERATE_SIGNATURE_COMPLETION_BRIDGE` rewrites the inputs from the real analysis, and `lean/SignatureCompletionBridgeEmit.lean`,
the only writer, rewrites the outcomes. A native answer is never an input to the outcomes file.
