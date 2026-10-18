# Binding architecture ownership

Lean R5 (2026-10-15) extracts total supply and collector-demand control without changing
this C# implementation. `NeedSupply` is the one concrete `EvalM` formation core, with only
computed-spread evaluation injected. `NeedDemand` sequences collector VALUE demands and
publishes completion into the current cell. The total public entry points specialize these
helpers; recursive evaluator callers install the same helpers through the thin partial
`demandNeedRecursive` driver. `KatLangArityLaws/NeedControl.lean` proves formation provenance,
ordered exact-list materialization, failure-state retention, memo publication and qualified
heap invariants. The driver and expression evaluator remain opaque; whole-run heap refinement
and R7 remain open. S5 (2026-10-18) proves the binder's correspondence over formed supplies
(`KatLangArityLaws/SupplyCorrespondence.lean`) and Q-28's repeated-name laws
(`KatLangArityLaws/RepeatedNameLaws.lean`), both under stated premises. These are Lean theorems; C# behavior is supported by tests.

## Canonical runtime

Model-C acquisition is centralized in `Evaluator.Needs.cs` and `Evaluation/NeedCell.cs`. Ordinary calls, conditional families, callbacks and generic loop steps share suspended or Ready cells and the inspecting `BindAcceptedNeedPatterns` core after the caller or `BindNeedPatterns` validates cardinality. Category adapters select the demands they execute; they do not implement separate memoization or argument-eagerness policies. See `docs/design/language-rules/call-by-need.md` for the full frozen laws.

`FormNeedSupply` suspends ordinary expressions in the caller environment, transfers the exact cell of a parameter reference, opens arbitrary explicit spreads into Ready data, and transfers known collector slices without forcing. Cardinality precedes ordinary demand. The binder traverses written patterns left to right, forces only inspecting patterns, and detects repeated-name conflicts immediately. Structural patterns demand their whole parent before opening Ready children. A collecting binding stores a lazy exact slice; its VALUE materializes the whole eager list once.

## Metadata and executors

`CallableSignature`, `CallableSignatureDiagnostics` and `CallableBindingPlan` are shape/diagnostic data (planner eligibility, editor metadata), never alternate acquisition semantics. A builtin binds its formed supply through its own fixed argument roles (`ApplyBuiltinCountedResolved`, `BindSequenceBuiltinArguments`) without evaluating it. Builtin metadata assigns executed VALUE or CALLBACK roles after spread expansion. Native Math and host operations request their value arguments in their established order after arity.

Every user-pattern-level cardinality decision reads ONE supplied-slot rule, `PatternLevelArity`: each pattern consumes one slot, and a collecting capture at that level consumes none and lifts the upper bound. Its readers are the binder's gates, the zero-argument law (`ParameterPattern.AcceptsZeroSuppliedSlots`), `CallableArityFacts` and `PatternListBindingPlan`. `BindNeedPatterns` is the one binder behind its top-level gate, as in Lean's `bindNeedPatterns`; the zero-supply binding uses it. Every other caller makes that top-level decision itself and then binds through `BindAcceptedNeedPatterns`: an ordinary call (`NeedCallArityError`), a user loop step (`LoopStateArityMismatch`) and a deconstruction report it in their own diagnostic shape, and a clause family's driver checks each clause (a refused count is that clause's non-match). Keeping the gate out of the binder's frames matters, because a literal or structural pattern demands a recursive argument while those frames are on the host stack. Each structural level keeps its one gate inside the binder. Allocation of an accepted level (`NeedSourceRange`, Lean `needSourceAt`) is pure index arithmetic that stays inside the supply for every accepted count.

Callbacks pass produced items as Ready cells, with no invented callable identity. Loops form lazy initial cells and ordinary Ready next-state cells; a step's parameter patterns only bind the incoming cells, and its row supply — read without any pattern-derived flag — is the next state (Q-24); final output materializes the required whole state as ONE value, re-counted at the ordinary result boundary (Q-26). Optimized loops may read Ready values or demand parameter cells through the same funnel, preserving effects, failures and accounting. Sequence-pipeline fusion observes the same terminal state and callback demand rules.

## Identity, ownership and cache

`NeedEnv` and retained lexical activations preserve the caller's parameter addresses. Binding shadows inherited names on every channel. CALLABLE projection obtains identity and owner without VALUE evaluation; invocation is fresh and cannot replace a memoized VALUE outcome. Alias indirection allocates neither a wrapper invocation nor an extra cell. Bare forwarding transfers the source cells or collector slice selected by the existing static name/kind contract.

Property caching is a separate per-run domain: demanded bare `Z` uses the resolved binding cache; demanded explicit `Z()` is fresh once within its cell. Dot fallback injects the original receiver expression as one ordinary leading argument; the receiver creates no new supply or binding policy. Capture, list, spread, selection and structural pattern opening keep their distinct value boundaries.

## Demand state and resources

NeedCell publishes one shared flight before computation, memoizes counted success/failure/cancellation, and checks the active dependency graph before joining. The graph is per run: the run budget's `NeedDependencyGate` guards every edge between that run's cells, so independent runs never contend. Supported entry points cannot demand another run's cells, so a parent cell from another run (the `AsyncLocal` current cell flowing into a nested run that a host operation starts) records no edge. Internal property-cache keys can retain cells through environments and activations, but include run identity and return only values; internal adapters must not replay retained evaluation delegates in another run. Cycles report `DemandCycle` with original provenance; fresh recursive supplies obey ordinary limits. Allocation, transport, joins, memo hits and pure projection add no semantic charge. Existing expression and materialization work is charged when executed. Terminal cancellation or a reached resource limit stops further semantic work without rewriting a completed value.

Lean models the same serial operations in `KatLang.lean`; `CoreTests.ModelC` pins heap sharing and demand order. The production binder (`bindNeedPatterns`, `selectNeedFamilyBranch`) is total, and its cardinality, allocation, minimum and plain-binding laws are theorems (`KatLangArityLaws.lean` § Model-C production binder laws, e.g. `binder_rejects_unaccepted_supply_before_any_effect`, `lone_collecting_head_allocates_one_collector_over_its_supply`). Since R3 it is the `EvalM` specialization of one generic core, and its demand order — event schedule, repeated-name order, first-failure truncation, family search and activation — is proved over the production runs and an external boundary trace (`KatLangArityLaws/BinderTrace.lean`, `FamilyDispatch.lean`), and channel substitution (per channel and in its static, inspecting-position form) and the family/ordinary mode correspondence for every head over the production runs (`BinderCorrespondence.lean`); these are Lean binder theorems, not proofs about this C# binder, whose agreement rests on the differential corpora and tests. The pre-Model-C completed-input binder and its proofs were retired on 2026-10-12; git history keeps them.
