# Binding architecture ownership

This note locks down binding ownership boundaries before any future `BindingInput` work. See `CALLABLES.md` for the broader callable-surface and binding-plan architecture; this file is narrower and only covers ownership and non-ownership rules.

## Plan-data invariant

`CallableBindingPlan` is data only. It describes callable binding shape. It must not bind, evaluate, dispatch, resolve algorithms, apply dot-call rules, or own runtime semantics.

## Ownership layers

- `CallableSignature`: callable surface metadata.
- `CallableSignatureDiagnostics`: arity facts and diagnostic wording.
- `CallableBindingPlan`: binding shape.
- `FlatVariadicBindingLayout`: plan-derived runtime layout for flat variadic user calls and generic `Algorithm.User` loop-step evaluated-slot binding.
- `BindCallableArguments`: suffix-from-back binding kernel over already-built items.
- `CreateVariadicCapture`: variadic `Result` / `CountedResult` construction.
- Runtime executors: context-specific semantics.

## Runtime executor ownership

Zero-argument property caching and explicit fresh calls are core evaluator semantics, not binding-plan policy. `Fun` is cacheable property-style access; `Fun()` bypasses the zero-argument cache for `Fun` itself, but it does not recursively force nested property references to bypass their own caches. Write nested `()` calls explicitly when nested freshness is intended.

Flat fixed user calls own:

- expression evaluation
- algorithm/value dual channels
- call-site expression boundaries
- explicit spread slot expansion
- counted-param shadowing

Flat variadic user calls own:

- argument item construction
- counted top-level expansion
- algorithm/value error propagation
- dot receiver boundary preservation

Patterned/sequence-value executor owns:

- sequence-value pattern consumes one parent slot
- nested recursive traversal
- singleton sequence-value fallback
- explicit block-to-sequence-value items, including source-backed nested call-site sequence-value levels
- top-level algorithm binding
- nested sequence-value algorithm suppression
- sequence-value variadic capture

Generic loop machinery owns:

- evaluated state slots
- init boundary preservation
- result-slot boundary preservation
- continuation flag splitting
- loop diagnostics

Callbacks own:

- projected callback items
- counted callback input
- reducer accumulator threading
- callback result shape validation

Builtins own:

- sequence source collection
- suffix validation
- callback invocation
- numeric policy
- empty policy
- builtin dot receiver normalization

Conditionals own:

- pattern-based ordered/literal/value-only matching
- counted branch matching
- singleton sequence-value normalization
- future guards, if added later

Optimized loops own:

- optimization-only scalar plans
- fallback equivalence to generic semantics

## Receiver semantics separation

- Ordinary dot-call receiver boundary preservation is call-site syntax/runtime data.
- Builtin sequence receiver normalization and top-level expansion are builtin runtime behavior.
- Neither behavior belongs in a future `BindingPolicy`.

If future models need to carry receiver information, they should carry it as descriptive input data only; they should not decide what receiver semantics to apply.

## Future `BindingInput`

`BindingInput` should start as pure data only.

Good candidates:

- evaluated slot list
- value / algorithm / value-error channels
- explicit sequence-value items
- emitted count
- source/provenance
- receiver-boundary holder flag as descriptive data

`BindingInput` must not decide what to do. Executors consume it; they keep semantic ownership.

### Phase 23 flat variadic executor closure

Flat variadic user-call binding and generic `Algorithm.User` loop-step evaluated-slot binding now share `FlatVariadicBindingLayout`, `BindingInputSlot`, `BindItemsToFlatVariadicLayout`, `BindCallableArguments`, and `CreateVariadicCapture`. This is the intended flat variadic migration boundary for the current architecture.

The remaining differences are executor-owned. User calls still own argument expression evaluation, counted top-level expansion, algorithm/value/error channels, dot-call receiver boundary preservation, callable diagnostics, and `UserCallBindings`. Generic loop binding still owns already-evaluated value-only slots, declaration-order projection of the variadic capture, loop-state diagnostics, and `EvaluatedSlotBindings`.

`TryGetLegacyFlatVariadicBindingLayout` remains for non-`Algorithm.User` loop steps where no `CallableBindingPlan` is available. `VariadicCallItem` remains for sequence builtin binding because builtins own different empty/error policy, suffix preparation, callback invocation, and source collection semantics.

Reopen flat variadic executor consolidation only if a third runtime path needs the same flat variadic policy, a source-argument or environment-binding abstraction lands, a divergence bug appears between user-call and loop flat variadic semantics, Lean exposes source-argument shape semantics, or builtin runtime migration intentionally starts sharing the same input model. Do not introduce `BindingPolicy`, unify `UserCallBindings` with `EvaluatedSlotBindings`, add algorithm channels to loop evaluated slots, or fold builtin `VariadicCallItem` into `BindingInputSlot` as part of this closure.

### Phase 24 generic loop-step executor closure

Generic `Algorithm.User` loop-step binding is at the intended boundary for the current architecture. Shape selection uses `CallableBindingPlan`, flat variadic loop-step binding uses the shared `FlatVariadicBindingLayout` / `BindingInputSlot` / `BindCallableArguments` / `CreateVariadicCapture` path, and patterned loop-step binding remains `ParameterPattern`-based.

The remaining loop behavior is executor-owned: initial state slot boundaries, evaluated state slots, continuation splitting, state update rules, result-slot boundary preservation, final state construction, loop-specific arity diagnostics, and optimized/generic fallback accounting. These rules must not move into `CallableBindingPlan`.

Legacy/non-user loop-step fallback remains defensive when no `Algorithm.User` binding plan is available. Optimized loops remain separate implementation-only paths and should be migrated, if ever, in a dedicated optimizer phase.

Reopen generic loop-step executor migration only if a collection-level `BindingInput`, `BindingPolicy`, or environment-binding abstraction is introduced; optimized-loop shape planning intentionally moves under shared plan queries; or a real divergence bug appears between generic loop-step binding and a shared runtime binding path.

### Phase 25 patterned executor policy closure

Patterned binding is intentionally not migrated to a new policy abstraction yet. `CallableBindingPlan` already describes patterned shape as data: sequence-value nodes, recursive nodes, capture names and sources, top-level versus nested variadics, and arity facts. It must remain non-executable.

The remaining patterned behavior is executor-owned runtime policy: explicit argument evaluation timing, explicit block-to-sequence-value item extraction, top-level algorithm-channel binding, nested algorithm suppression during sequence-value recursion, loop value-only state-slot semantics, counted callback projection, singleton sequence-value scalar fallback, and arity or wrong-shape diagnostic selection.

`ParameterPatternInput` remains separate from `BindingInputSlot`. `BindingInputSlot` stays a narrow flat-variadic slot model and must not grow explicit sequence-value items or counted callback policy.

Reopen patterned executor policy only if a second non-evaluator consumer of patterned binding appears; a real collection-level `BindingInput` model lands for other reasons; `BindingPolicy` has multiple concrete consumers with documented divergence; there is an explicit plan to make `CallableBindingPlan` executable while preserving its data-only invariant; or Lean semantics force a corresponding C# refactor.

### Phase 26 callback binding closure

Callback binding unification is deferred. Callback binding remains executor-owned runtime policy across counted callback evaluation, flat callback parameter binding, patterned callback parameter binding, conditional callback dispatch, map callbacks, filter callbacks, reduce step callbacks, and builtin-as-callback paths. `CallableBindingPlan` may describe callback signature shape, but it does not own callback input shaping or execution policy.

`UsesPatternBinding` remains for now because callbacks, evaluated loop slots, and loop fallbacks still share that runtime helper. Do not partially migrate only the callback call site to `CallableBindingPlan.RequiresPatternedBinding`.

Callbacks receive already-evaluated `CountedResult` values; sequence-value callback items preserve structure through callback item projection; reducer accumulator input is shaped differently from ordinary element input; `EmittedCount` threads through counted callback paths; callbacks do not allow algorithm-channel binding; and callback diagnostics are selected and wrapped by the relevant executor call site. Counted and uncounted binders are not unified now because `CountedResult` versus `Result` is a structural difference, not accidental duplication.

`BindingInputSlot` stays a narrow flat-variadic slot model. Its variadic-slot emitted count is only for flat variadic user-call capture supply. It intentionally lacks explicit sequence-value items, reducer accumulator policy, and callback projection policy, and it should not be widened to support callbacks.

Reopen callback binding unification only if `UsesPatternBinding`'s evaluated-loop-slot and loop-fallback consumers are migrated so the helper can be retired in one coherent pass; a new callback family appears outside the current executor paths; a second non-executor consumer needs the same callback binding logic; a real callback bug requires unification to fix correctly; Lean callback semantics change and force a C# refactor; or a real `BindingPolicy` abstraction already exists with multiple concrete consumers.

### Phase 27 builtin runtime binding closure

Builtin runtime binding integration is deferred. Builtin metadata is already unified: `BuiltinRegistry`, `SequenceBuiltinMetadata`, `CallableSignature`, and `CallableBindingPlan` describe builtin surface shape. The remaining builtin runtime binding stays executor-owned because builtins operate on already-evaluated collected sequence sources, not ordinary pre-evaluation callable argument slots.

`CallableBindingPlan` may describe builtin signatures, but it does not own builtin source collection, receiver normalization, empty policy, numeric validation, callback projection, or diagnostic wrapping. `BindingInputSlot` stays narrow and must not be widened for builtin runtime binding; its variadic-slot emitted count is not a builtin source-collection model, and it intentionally does not carry source-boundary information, empty-policy state, callback projection policy, or dot-call receiver policy. `FlatVariadicBindingLayout` should not be layered onto sequence builtin suffix binding now. Suffix extraction already shares the legitimate primitive `BindCallableArguments`, and another layout would not retire the remaining runtime policy.

The builtin runtime families are plain builtin calls, dot-call builtin calls, sequence builtins, numeric/math builtins, map/filter/reduce higher-order builtins, structural builtins such as `count`, `atoms`, `first`, `last`, `take`, `skip`, `order`, and `distinct`, builtin-as-callback, and dot-receiver normalization. `count` counts item-supply / sequence contents and `atoms` recursively projects atoms; these remain distinct semantic operations. Postfix spread `...` is the one-level boundary-opening mechanism and is not a builtin.

The executor-owned builtin policies are dot-call receiver normalization, receiver boundary preservation, explicit spread expansion from evaluated arguments, source sequence-value construction and null filtering, one-level content projection where applicable, suffix parameter binding through existing shared `BindCallableArguments`, callback shaping for map/filter/reduce, numeric validation, empty-input behavior, builtin shadowing checks, and per-builtin diagnostic context wrapping. Dot-call receiver normalization remains runtime-owned and outside `CallableBindingPlan`; per-builtin diagnostic context remains executor-owned and user-facing.

Reopen builtin runtime binding integration only if a second non-executor consumer of builtin source-collection or empty-policy logic appears; a future `SequenceBuiltinInput` or equivalent substrate is introduced for another reason; `BindingInputSlot` or a successor gains emitted-count and source-boundary representation for another concrete migration; a new builtin family forces redesign; Lean builtin semantics change and require a corresponding C# refactor; or a real builtin binding bug requires unification to fix correctly.

### Phase 29 conditional branch pattern model closure

No `ConditionalBranchPatternPlan` is introduced at this stage. Conditional branches already have a distinct model: `Pattern`, ordered `CondBranch` entries, parser-owned branch arity and output arity validation, evaluator-owned normal and counted matching, and editor-facing branch metadata. This is intentionally separate from `CallableBindingPlan`.

A separate conditional plan is deferred because there is no concrete consumer today. Current diagnostics are parser/runtime owned, editor metadata already exposes conditional branch heads and binders, runtime matching paths differ in meaningful policy, and guard expressions do not exist yet. A speculative plan would duplicate facts already available on `Pattern` / `CondBranch` and blur the boundary between conditional matching and callable binding.

Conditional executor semantics remain executor-owned: ordered first-match selection, literal matching, value-only bindings, sequence-value and nested matching, singleton sequence-value normalization, counted branch matching, conditional callback dispatch, and no-match diagnostics. These must not move into `CallableBindingPlan`. Do not fold conditional branch metadata into `CallableBindingPlan`, add speculative guard fields, normalize away sequence-value shape, or migrate normal/counted/callback matchers through a shared plan without dedicated characterization tests.

Reopen only when a concrete consumer appears, such as accepted guard-expression semantics, an editor/analyzer feature requiring cross-branch shape analysis, diagnostics that need normalized available-pattern descriptions, or a real runtime matcher divergence bug. If a future model is introduced, it must be separate from `CallableBindingPlan`, data-only unless explicitly justified, and must not speculate about guards before guard semantics are designed.

### Phase 22 flat fixed executor decision

Flat fixed user-call binding is intentionally not migrated to `BindingInputSlot` yet. Its policies operate on source arguments, while `BindingInputSlot` is post-expansion slot data. Call-site expression boundaries, explicit spread slot expansion, algorithm/value dual binding, and counted-param shadowing remain executor-owned, and flat fixed user calls currently have no second runtime consumer that justifies extraction.

Reopen this only when another runtime path needs the same flat fixed source-argument policy, a separate source-argument input model exists, Lean or AST semantics make source-argument shape explicit, or a real divergence bug appears. Do not add source-argument or receiver-boundary fields to `BindingInputSlot`, move flat fixed call-boundary policy into `CallableBindingPlan`, or introduce `BindingPolicy` for flat fixed binding as part of this deferral.

## `BindingPolicy` deferred

Do not introduce `BindingPolicy` until there is:

- a path comparison matrix
- parity tests
- at least three consumers
- documented divergence to resolve

Until then, keep policy in the executors that already own the runtime semantics and use shared models only for descriptive shape/layout.

## Lean alignment gate

Observable semantic policy changes require Lean consideration or Lean parity tests. C#-only metadata/data models do not necessarily require Lean changes.

For the detailed Lean/C# semantic ownership and validation decision table, see `SEMANTIC-ALIGNMENT.md`.
