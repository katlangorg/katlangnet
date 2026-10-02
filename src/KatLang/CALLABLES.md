# Callable signatures and binding plans

`CallableSignature` describes the selected callable's surface, including structural patterns, top-level collecting slots and minimum supplied cardinality. `CallableSignatureDiagnostics` presents that contract. `CallableBindingPlan` is data only: it never evaluates, resolves, dispatches or owns demand mechanics.

Resolution selects ONE identity before supply formation, independent of argument count. A nearer property or parameter completely shadows a prelude builtin. Supply formation suspends ordinary slots and evaluates only arbitrary explicit spreads. Cardinality is checked against that selected identity before ordinary demand. The shared inspecting binder owns ordinary and family patterns, callbacks and generic loop steps (`Evaluator.Needs.cs`; Lean `bindNeedPatterns`).

A plain binder transports its complete NeedCell without forcing. Literal, structural and repeated-name patterns inspect values when reached in written order. Families share one supply across clause attempts and never preforce all candidates. A collector is a lazy exact slice whose VALUE demand constructs one whole eager list. The fixed prefix/suffix allocation rule changes no value boundary or demand order.

Builtin invocation specifies which VALUE/control slots and CALLBACK/step identities it actually uses. `if` demands the condition and selected branch through the ordinary cell mechanism; ordinary `Choose` clauses and user selectors can make the same demands. Empty collections skip callback projection. Actual callbacks receive one Ready argument per element (two for reduce), and no Result is reified as an algorithm.

CALLABLE projection is independent of VALUE completion; invocation is fresh. Captures, scalars and computed/selected values have no invented identity. Aliases resolve to their target identity without a wrapper cell or invocation. Bare forwarding retains the static by-name and source-kind contracts and transfers existing cells/slices; it invokes its target and never returns it. Results are calculation values: Ready cells have no callable channel, a call result projects no identity, and an undersupplied call is an arity failure, never partial application (`ResultValueBoundaryTests`).

Optimized/planned execution preserves this canonical demand protocol, diagnostics, effects and cumulative budget. Metadata can select a safe strategy; it cannot preforce an unused parameter or refund a reached limit. Property-style zero-argument caching remains separate from a cell's at-most-once completion.

See `BINDING-ARCHITECTURE.md` and `docs/design/language-rules/call-by-need.md`. Permanent pins include `ModelCProductionTests`, `NeedCellTests`, the callback and loop parity suites, and Lean `CoreTests.ModelC`.
