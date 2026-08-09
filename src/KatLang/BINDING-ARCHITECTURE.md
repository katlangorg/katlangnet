# Binding architecture ownership

This note locks down binding ownership boundaries before any future `BindingInput` work. See `CALLABLES.md` for the broader callable-surface and binding-plan architecture; this file is narrower and only covers ownership and non-ownership rules.

## Plan-data invariant

`CallableBindingPlan` is data only. It describes callable binding shape. It must not bind, evaluate, dispatch, resolve algorithms, apply dot-call rules, or own runtime semantics.

## Ownership layers

- `CallableSignature`: callable surface metadata.
- `CallableSignatureDiagnostics`: arity facts and diagnostic wording.
- `CallableBindingPlan`: binding shape.
- `FlatCollectingBindingLayout`: plan-derived runtime layout for flat collecting user calls and generic `Algorithm.User` loop-step evaluated-slot binding.
- `BindCallableArguments`: suffix-from-back binding kernel over already-built items.
- `CollectSegment` / `CreateCollectingCapture`: collecting-binding materialization — the collected segment is ONE exact immutable `Result.ListValue` with emitted count 1 (the `collect` operation; Lean `collectSegment`). No raw-supply counts or forwarding provenance are stored.
- Runtime executors: context-specific semantics.

## Runtime executor ownership

Zero-argument property caching and explicit fresh calls are core evaluator semantics, not binding-plan policy. `Fun` is cacheable property-style access; `Fun()` bypasses the zero-argument cache for `Fun` itself, but it does not recursively force nested property references to bypass their own caches. Write nested `()` calls explicitly when nested freshness is intended.

Flat fixed user calls own:

- expression evaluation
- algorithm/value dual channels
- call-site expression boundaries
- explicit spread slot expansion
- counted-param shadowing

Flat collecting user calls own:

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
- sequence-value collecting capture

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
- The collection-builtin post-binding collection view is builtin runtime behavior.
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

### Phase 23 flat collecting executor closure

Flat collecting user-call binding and generic `Algorithm.User` loop-step evaluated-slot binding now share `FlatCollectingBindingLayout`, `BindingInputSlot`, `BindItemsToFlatCollectingLayout`, `BindCallableArguments`, and `CreateCollectingCapture`. This is the intended flat collecting migration boundary for the current architecture.

The remaining differences are executor-owned. User calls still own argument expression evaluation, counted top-level expansion, algorithm/value/error channels, dot-call receiver boundary preservation, callable diagnostics, and `UserCallBindings`. Generic loop binding still owns already-evaluated value-only slots, declaration-order projection of the collecting capture, loop-state diagnostics, and `EvaluatedSlotBindings`.

`TryGetLegacyFlatCollectingBindingLayout` remains for non-`Algorithm.User` loop steps where no `CallableBindingPlan` is available. `VariadicCallItem` remains as the collection-builtin argument-evaluation carrier because builtins own different empty/error policy, control preparation, callback invocation, and post-binding collection semantics.

Reopen flat collecting executor consolidation only if a third runtime path needs the same flat collecting policy, a source-argument or environment-binding abstraction lands, a divergence bug appears between user-call and loop flat collecting semantics, Lean exposes source-argument shape semantics, or builtin runtime migration intentionally starts sharing the same input model. Do not introduce `BindingPolicy`, unify `UserCallBindings` with `EvaluatedSlotBindings`, add algorithm channels to loop evaluated slots, or fold builtin `VariadicCallItem` into `BindingInputSlot` as part of this closure.

### Phase 24 generic loop-step executor closure

Generic `Algorithm.User` loop-step binding is at the intended boundary for the current architecture. Shape selection uses `CallableBindingPlan`, flat collecting loop-step binding uses the shared `FlatCollectingBindingLayout` / `BindingInputSlot` / `BindCallableArguments` / `CreateCollectingCapture` path, and patterned loop-step binding remains `ParameterPattern`-based.

The remaining loop behavior is executor-owned: initial state slot boundaries, evaluated state slots, continuation splitting, state update rules, result-slot boundary preservation, final state construction, loop-specific arity diagnostics, and optimized/generic fallback accounting. These rules must not move into `CallableBindingPlan`.

Legacy/non-user loop-step fallback remains defensive when no `Algorithm.User` binding plan is available. Optimized loops remain separate implementation-only paths and should be migrated, if ever, in a dedicated optimizer phase.

Reopen generic loop-step executor migration only if a collection-level `BindingInput`, `BindingPolicy`, or environment-binding abstraction is introduced; optimized-loop shape planning intentionally moves under shared plan queries; or a real divergence bug appears between generic loop-step binding and a shared runtime binding path.

### Phase 25 patterned executor policy closure

Patterned binding is intentionally not migrated to a new policy abstraction yet. `CallableBindingPlan` already describes patterned shape as data: sequence-value nodes, recursive nodes, capture names and sources, top-level versus nested variadics, and arity facts. It must remain non-executable.

The remaining patterned behavior is executor-owned runtime policy: explicit argument evaluation timing, explicit block-to-sequence-value item extraction, top-level algorithm-channel binding, nested algorithm suppression during sequence-value recursion, loop value-only state-slot semantics, counted callback projection, singleton sequence-value scalar fallback, and arity or wrong-shape diagnostic selection.

`ParameterPatternInput` remains separate from `BindingInputSlot`. `BindingInputSlot` stays a narrow flat-collecting slot model and must not grow explicit sequence-value items or counted callback policy.

Reopen patterned executor policy only if a second non-evaluator consumer of patterned binding appears; a real collection-level `BindingInput` model lands for other reasons; `BindingPolicy` has multiple concrete consumers with documented divergence; there is an explicit plan to make `CallableBindingPlan` executable while preserving its data-only invariant; or Lean semantics force a corresponding C# refactor.

### Phase 26 callback binding closure

Callback binding unification is deferred. Callback binding remains executor-owned runtime policy across counted callback evaluation, flat callback parameter binding, patterned callback parameter binding, conditional callback dispatch, map callbacks, filter callbacks, reduce step callbacks, and builtin-as-callback paths. `CallableBindingPlan` may describe callback signature shape, but it does not own callback input shaping or execution policy.

Collecting parameter kinds are never discarded on any callback route (July 2026 correction): a flat callee whose top-level parameters include a collecting parameter routes through `BindCountedCallbackParameterPatternList` (Lean `bindCountedCallbackParameterPatternList`), which applies the established flat-callback row expansion to the supplied argument slots and then delegates to the shared `BindCountedParameterPatternList`, so the collecting parameter COLLECTS an exact immutable list — there is no callback-specific collecting algorithm. Only fixed-only flat callees stay on `BindCountedCallbackParams`.

`UsesPatternBinding` remains for now because callbacks, evaluated loop slots, and loop fallbacks still share that runtime helper. Do not partially migrate only the callback call site to `CallableBindingPlan.RequiresPatternedBinding`.

Callbacks receive already-evaluated `CountedResult` values; sequence-value callback items preserve structure through callback item projection; reducer accumulator input is shaped differently from ordinary element input; `EmittedCount` threads through counted callback paths; callbacks do not allow algorithm-channel binding; and callback diagnostics are selected and wrapped by the relevant executor call site. Counted and uncounted binders are not unified now because `CountedResult` versus `Result` is a structural difference, not accidental duplication.

`BindingInputSlot` stays a narrow flat-collecting slot model. It intentionally lacks explicit sequence-value items, reducer accumulator policy, and callback projection policy, and it should not be widened to support callbacks. (It once carried a variadic-slot emitted count for raw capture-supply forwarding; exact list collection made that metadata obsolete and it was removed.)

Reopen callback binding unification only if `UsesPatternBinding`'s evaluated-loop-slot and loop-fallback consumers are migrated so the helper can be retired in one coherent pass; a new callback family appears outside the current executor paths; a second non-executor consumer needs the same callback binding logic; a real callback bug requires unification to fix correctly; Lean callback semantics change and force a C# refactor; or a real `BindingPolicy` abstraction already exists with multiple concrete consumers.

### Phase 27 builtin runtime binding closure

Builtin runtime binding integration is deferred. Builtin metadata is already unified: `BuiltinRegistry`, `SequenceBuiltinMetadata`, `CallableSignature`, and `CallableBindingPlan` describe builtin surface shape. The remaining builtin runtime binding stays executor-owned because builtins operate on already-evaluated collected sequence sources, not ordinary pre-evaluation callable argument slots.

`CallableBindingPlan` may describe builtin signatures, but it does not own builtin source collection, receiver normalization, empty policy, numeric validation, callback projection, or diagnostic wrapping. `BindingInputSlot` stays narrow and must not be widened for builtin runtime binding; it intentionally does not carry source-boundary information, empty-policy state, callback projection policy, or dot-call receiver policy. Collection builtins are ordinary fixed-arity callables (`count(collection)`, `take(collection, count)`): their binder checks the exact argument count directly and applies the post-binding one-level collection view to the bound collection argument — there is no variadic layout, no suffix-from-the-back binding, and no pre-binding opening.

The builtin runtime families are plain builtin calls, dot-call builtin calls, collection builtins, numeric/math builtins, map/filter/reduce higher-order builtins, structural builtins such as `count`, `atoms`, `first`, `last`, `take`, `skip`, `order`, and `distinct`, builtin-as-callback, and dot-receiver injection. `count` counts its one bound collection's viewed items and `atoms` recursively collects atoms through both sequence and list boundaries into one exact list; these remain distinct semantic operations. The spread marker (`value*`) is the one-level boundary-opening mechanism and is not an ordinary builtin call.

The executor-owned builtin policies are dot-call receiver injection, receiver boundary preservation, explicit spread expansion from evaluated arguments, fixed argument-count checking, the post-binding one-level collection view of the bound collection argument, control-argument preparation, callback shaping for map/filter/reduce, numeric validation, empty-input behavior, builtin shadowing checks, and per-builtin diagnostic context wrapping. Dot-call receiver injection remains runtime-owned and outside `CallableBindingPlan`; per-builtin diagnostic context remains executor-owned and user-facing.

Reopen builtin runtime binding integration only if a second non-executor consumer of builtin source-collection or empty-policy logic appears; a future `SequenceBuiltinInput` or equivalent substrate is introduced for another reason; `BindingInputSlot` or a successor gains emitted-count and source-boundary representation for another concrete migration; a new builtin family forces redesign; Lean builtin semantics change and require a corresponding C# refactor; or a real builtin binding bug requires unification to fix correctly.

### Phase 29 conditional branch pattern model closure

No `ConditionalBranchPatternPlan` is introduced at this stage. Conditional branches already have a distinct model: `Pattern`, ordered `CondBranch` entries, parser-owned clause-family diagnostics, shared pre-evaluation branch arity and output arity validation for prebuilt ASTs, evaluator-owned normal and counted matching, and editor-facing branch metadata. This is intentionally separate from `CallableBindingPlan`.

A separate conditional plan is deferred because there is no concrete consumer today. Current diagnostics are parser/runtime owned, editor metadata already exposes conditional branch heads and binders, runtime matching paths differ in meaningful policy, and guard expressions do not exist yet. A speculative plan would duplicate facts already available on `Pattern` / `CondBranch` and blur the boundary between conditional matching and callable binding.

Conditional executor semantics remain executor-owned: ordered first-match selection, literal matching, value-only bindings, sequence-value and nested matching, singleton sequence-value normalization, counted branch matching, conditional callback dispatch, and no-match diagnostics. These must not move into `CallableBindingPlan`. Do not fold conditional branch metadata into `CallableBindingPlan`, add speculative guard fields, normalize away sequence-value shape, or migrate normal/counted/callback matchers through a shared plan without dedicated characterization tests.

Reopen only when a concrete consumer appears, such as accepted guard-expression semantics, an editor/analyzer feature requiring cross-branch shape analysis, diagnostics that need normalized available-pattern descriptions, or a real runtime matcher divergence bug. If a future model is introduced, it must be separate from `CallableBindingPlan`, data-only unless explicitly justified, and must not speculate about guards before guard semantics are designed.

### Phase 22 flat fixed executor decision (superseded by the shared call assembly)

Call argument-slot assembly is now centralized: `BuildCallArgumentInputs` (Lean `collectVariadicCallItems`) serves EVERY callable shape — flat fixed, flat/mixed variadic, patterned, and multi-clause conditional. It evaluates each written slot exactly once, left to right, reifies every non-spread slot as exactly one argument value (with the dual algorithm channel where resolvable), and expands every explicit spread slot by one value boundary BEFORE any arity checking, clause selection, or pattern binding. For a `Capture` or zero-parameter `AlgorithmExpr` sent to a patterned callee, the corresponding prepared-output pass returns both the combined counted value and a read-only explicit-slot view over the same evaluated values; binding never evaluates the expression again or reconstructs the view from the combined value. The July 2026 call-spread repair introduced the shared assembler after an audit found spread expansion implemented in only two of four per-shape assemblers (patterned and conditional callees silently received a spread argument as one closed value).

Per-shape binding after assembly remains executor-owned: flat fixed positional binding, the item-supply prefix/collecting/suffix binder, `ParameterPattern` binding (which additionally consumes the explicit written-item channel for capture and zero-parameter AlgorithmExpr arguments), and conditional branch matching. Counted-param shadowing, dot-call receiver boundary preservation, and algorithm/value dual binding live in the shared assembly and its consumers. Do not reintroduce per-shape argument evaluation loops; changes to slot semantics belong in the shared assembler in BOTH languages.

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
