# Binding architecture ownership

## Canonical runtime

Model-C acquisition is centralized in `Evaluator.Needs.cs` and `Evaluation/NeedCell.cs`. Ordinary calls, conditional families, callbacks and generic loop steps share suspended or Ready cells and the inspecting `BindNeedPatterns` binder. Category adapters select the demands they execute; they do not implement separate memoization or argument-eagerness policies. See `docs/design/language-rules/call-by-need.md` for the full frozen laws.

`FormNeedSupply` suspends ordinary expressions in the caller environment, transfers the exact cell of a parameter reference, opens arbitrary explicit spreads into Ready data, and transfers known collector slices without forcing. Cardinality precedes ordinary demand. The binder traverses written patterns left to right, forces only inspecting patterns, and detects repeated-name conflicts immediately. Structural patterns demand their whole parent before opening Ready children. A collecting binding stores a lazy exact slice; its VALUE materializes the whole eager list once.

## Metadata and executors

`CallableSignature`, `CallableSignatureDiagnostics` and `CallableBindingPlan` are shape/diagnostic data (planner eligibility, editor metadata, builtin allocation), never alternate acquisition semantics. `BindCallableArguments` allocates already-prepared items against a builtin signature without evaluating them. Builtin metadata assigns executed VALUE or CALLBACK roles after spread expansion. Native Math and host operations request their value arguments in their established order after arity.

Callbacks pass produced items as Ready cells, with no invented callable identity. Loops form lazy initial cells and ordinary Ready next-state cells; a step's parameter patterns only bind the incoming cells, and its row supply — read without any pattern-derived flag — is the next state (Q-24); final output materializes the required whole state as ONE value, re-counted at the ordinary result boundary (Q-26). Optimized loops may read Ready values or demand parameter cells through the same funnel, preserving effects, failures and accounting. Sequence-pipeline fusion observes the same terminal state and callback demand rules.

## Identity, ownership and cache

`NeedEnv` and retained lexical activations preserve the caller's parameter addresses. Binding shadows inherited names on every channel. CALLABLE projection obtains identity and owner without VALUE evaluation; invocation is fresh and cannot replace a memoized VALUE outcome. Alias indirection allocates neither a wrapper invocation nor an extra cell. Bare forwarding transfers the source cells or collector slice selected by the existing static name/kind contract.

Property caching is a separate per-run domain: demanded bare `Z` uses the resolved binding cache; demanded explicit `Z()` is fresh once within its cell. Dot fallback injects the original receiver expression as one ordinary leading argument; the receiver creates no new supply or binding policy. Capture, list, spread, selection and structural pattern opening keep their distinct value boundaries.

## Demand state and resources

NeedCell publishes one shared flight before computation, memoizes counted success/failure/cancellation, and checks the active dependency graph before joining. Cycles report `DemandCycle` with original provenance; fresh recursive supplies obey ordinary limits. Allocation, transport, joins, memo hits and pure projection add no semantic charge. Existing expression and materialization work is charged when executed. Terminal cancellation or a reached resource limit stops further semantic work without rewriting a completed value.

Lean models the same serial operations in `KatLang.lean`; `CoreTests.ModelC` pins heap sharing and demand order. The separately imported `HistoricalReadyBinding` preserves old completed-input proof statements only and is not authoritative production acquisition or error precedence. No evaluator entry point imports it.
