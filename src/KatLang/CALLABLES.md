# Callable signatures and binding plans
This note documents the C# implementation architecture for callable signatures, diagnostics, and binding-plan metadata.

## Purpose

KatLang has several places that need to describe a callable without executing it: diagnostics, semantic tooling, builtin metadata, user-call routing, and generic loop-step shape selection. The shared callable models describe that surface and shape once, while runtime executors keep ownership of the language semantics that require evaluated values, algorithm bindings, callback counts, or loop state.

## Core models

`CallableSignature` describes the callable surface: parameter patterns, flattened parameter metadata, parameter source (`explicit`, `implicit`, `builtin`, or `synthetic`), and user-facing display text.

`CallableSignatureDiagnostics` derives callable arity and formatting facts from a signature: min/max top-level argument counts, top-level variadic facts, shared bad-arity formatting, and validation text for multiple top-level variadics.

`CallableBindingPlan` describes callable parameter binding shape: flat fixed captures, top-level variadic captures, prefix/variadic/suffix layout, sequence-value one-slot nodes, sequence-value variadics as nested variadics, and nested recursive parameter patterns.

## Evaluator usage

User-call route and layout decisions use `CallableBindingPlan`; user-call execution still uses the existing binders.

Every callable shape — flat fixed, flat/mixed variadic, patterned, and multi-clause conditional — receives its argument supply from ONE shared assembly stage (`BuildCallArgumentInputs` / Lean `collectVariadicCallItems`): each written slot is evaluated, every non-spread slot is reified as exactly one argument value (with the dual algorithm channel where resolvable), and every explicit spread slot is expanded by exactly one value boundary. Arity checking, clause selection, and pattern binding happen strictly AFTER assembly, so the callee's internal representation never changes the meaning of caller-side spread.

Flat fixed user calls use plan-derived parameter names and the shared flat fixed binding helper over the assembled slots. They preserve call-site expression boundaries: comma arguments are one slot each, explicit spread expressions (`...`) contribute spread items, and ordinary multi-output values remain one slot. Algorithm/value binding semantics remain executor behavior.

The plan-native flat variadic layout is still used for generic loop-step binding. User calls no longer use the strict one-slot variadic path: any top-level variadic now routes to the shared item-supply binder (below). User-call argument-expression evaluation, dot-call boundary preservation, and algorithm/value binding channels remain executor behavior.

Item-supply user calls — any callable with a top-level variadic capture, whether rest-only `G(...x)` or a mixed `F(x, ...y, z)` shape — route to one executor path (`IsDeconstructionUserCallShape` / Lean `Algorithm.usesItemSupplyBinding`). That path collects the call argument stream exactly as supplied, then binds prefix/rest/suffix through the shared `BindParameterPatternList`. A plain sequence-valued or list-valued argument contributes one argument; explicit `...` contributes opened items. The rest binding COLLECTS its assigned slots as ONE exact immutable list (`CollectRest` inside `CreateVariadicCapture`; Lean `collectRest`): zero slots form `[]`, one slot forms `[item]` (never erased), many form `[a, b, ...]`, always with emitted count 1. `G(A)` therefore binds `x = [A]` while `G(A...)` binds `x = [A's items...]` — the two calls differ for every sequence-, list-, and empty-valued argument (the pre-list grouped/spread display coincidence is gone; scalar atoms/strings coincide because spread is total), and a function call never implicitly opens a single sequence or list argument. Forwarding is ordinary list spread: `Forward(...items) = Target(items...)` re-supplies exactly the collected items (`open(collect(xs)) = xs`); no raw-supply counts or forwarding provenance exist. Assignment deconstruction (`x, ...y, z = RHS`) is a separate unpacking receiver (Python-style): the right-hand side is evaluated once into a shared property, and each target binds through an inline `SequenceValueParameterPattern` that opens that single shared value and matches its items element-by-element. The opening view is `Result.structureItems?` / `StructureItems`: a received sequence value or exact LIST value opens to its immediate items, so `x, y, z = A` unpacks a stored sequence value or list `A`, and `x, y, z = A...` supplies the same items (the written spread form passes through a capture boundary first, which agrees except for a singleton list whose lone element is itself openable, such as `A = [(1, 2)]`, where the spread form opens one level further). The rest target then collects its middle items through the same `collect` rule (`x, ...rest = [1, 2, 3]` binds `rest = [2, 3]`; `x, ...rest = 1` binds `rest = []`). This opening is deconstruction-specific and does not leak into calls: it uses the sequence-value parameter pattern, not the item-supply call path, so `F(A)` still passes `A` as one argument. The `(x, ...y, z)` sequence-value parameter pattern likewise opens one received value for parameter/callback-position destructuring; only the sequence-value pattern's scalar-element callback fallback stays strict (callback deconstruction for scalar elements deferred) — flat callbacks with a top-level rest bind through the shared binder (see "Builtins and callbacks" below).

Patterned and sequence-value user calls route through `CallableBindingPlan`, but execution remains `ParameterPattern`-based. That executor owns runtime semantics not represented by the plan, including algorithm/value binding channels, nested sequence-value capture behavior, explicit block-to-sequence-value item handling, singleton sequence-value scalar fallback, and counted callback projection.

## Loop-step usage

Generic `Algorithm.User` loop-step shape selection uses `CallableBindingPlan` to choose patterned, flat fixed, or flat variadic binding. Actual evaluated-slot loop binding still uses the existing runtime helpers.

Non-user loop steps stay on the runtime-specific path. Optimized loops remain separate and keep their existing fallback checks and scalar assumptions.

## Builtins and callbacks

Builtin metadata uses `CallableSignature` and `CallableBindingPlan` where it is safe to describe builtin call shape. A collection builtin is an ordinary FIXED-ARITY callable (`sum(collection)`, `contains(collection, item)`, `take(collection, count)`): `BindSequenceBuiltinArguments` / `bindSequenceBuiltinArguments` collect the ordinary call items (only explicit spread alters argument boundaries) and require exactly `1 + control count` arguments — anything else is an ordinary `ArityMismatch` carrying the fixed signature. `sum(1, 2, 3)`, `sum()`, `count(Values...)` (unless the spread opens exactly one item), and `take((1, 2, 3))` are arity errors; `sum((1, 2, 3))` and `sum([1, 2, 3])` are the valid forms. The bound `collection` argument is then interpreted through the POST-BINDING one-level collection view (`BuiltinCollectionItems` / `builtinCollectionItems`): a lone sequence or exact list opens one outer boundary, any other value is a one-element collection, never recursively — nested collections stay single opaque items. Nothing is ever opened before binding, and no suffix-from-the-back binding remains. What stays builtin-owned is the phase *after* binding: collection extraction shape constraints, control-argument preparation, callback invocation, and result materialization (`MakeCollectionListResult` / `makeCollectionListResult` for the collection-producing builtins, which builds ONE exact immutable list — zero items form `[]`, a single kept item forms `[item]`, sibling boundaries and item internals are preserved raw and never renormalized) and result-count rules (a list result always counts as one value).

`CallableBindingPlan` can describe `Algorithm.User` callback shapes, but callback runtime binding remains executor-owned. Reduce consults the plan only as read-only shape data to detect a top-level variadic accumulator side; the reducer executor still owns accumulator input shaping and binding. Counted callback parameters, sequence-value callback patterns, projection rules, and reducer accumulator behavior stay in the callback executor. Conditional and builtin callbacks intentionally remain outside plan classification because they use orthogonal binding models. A flat callback with a top-level rest parameter binds through the shared prefix/rest/suffix binder (`BindCountedCallbackParameterPatternList` / Lean `bindCountedCallbackParameterPatternList`, which delegates to `BindCountedParameterPatternList`): the callback supply first applies the established flat-callback row convention — when fewer argument slots are supplied than top-level parameters, the final supplied argument opens into its items (matching `callee(S:i)`; exact lists stay opaque) — and the rest then COLLECTS its allocated slots as one exact immutable list. A rest-only map/filter callback therefore keeps each iterated element as ONE collected slot (`[7].map(Collect)` binds `items = [7]`; `[(1, 2)].map(Collect)` binds `items = [(1, 2)]`), and a mixed flat callee opens the lone row (`Rows.map(F)` with `F(x, ...y, z)` agrees with `F((x, ...y, z))`). Reduce supplies element and accumulator callback slots: a genuine rest-only reducer collects `[element, accumulator]`, while a reducer rest before a fixed accumulator collects `[element]`. Future callback migration should introduce a `CallbackBindingInput` / policy model first.

## Conditionals are separate

Conditional branches use `Pattern`, not `ParameterPattern`, and intentionally remain outside `CallableBindingPlan`. `Pattern` owns conditional-specific semantics such as literal matching, ordered branch selection, value-only bindings, singleton sequence-value normalization, no true variadic branch patterns, and separate counted matching helpers. Conditional CALLS still consume the shared assembled argument supply (spread expands into ordinary argument slots before any clause is tried); only branch matching itself is conditional-specific. If richer branch diagnostics, editor branch visualization, conditional guards, or runtime matcher refactoring need a shared shape model, add a separate `ConditionalBranchPatternPlan`; do not fold conditional branches into `CallableBindingPlan`.

## Runtime semantics still owned by executors

`CallableBindingPlan` is a shape model, not an executor. Do not move runtime-only semantics into it by accident. In particular, keep these boundaries explicit:

- Flat variadic user-call argument-expression evaluation and dot-call boundary handling remain executor behavior; the binding kernel and capture construction are shared.
- Patterned/sequence-value execution remains `ParameterPattern`-based.
- Builtin runtime semantics remain custom.
- Callback runtime binding remains custom.
- Generic loop-step binding still uses evaluated-slot loop helpers after user-step shape selection.
- Optimized loops remain separate.
- Conditional branch matching remains separate.
- Zero-parameter property reuse is core evaluator semantics: `Fun` is property-style access and may use the zero-argument cache, while `Fun()` bypasses the zero-argument cache for `Fun` itself. It does not recursively force nested property references to bypass their own caches; write nested `()` calls explicitly when nested freshness is intended.

## Flat variadic executor boundary

Flat variadic user-call binding and generic `Algorithm.User` loop-step evaluated-slot binding share a plan-native flat variadic layout derived from `CallableBindingPlan`. The layout carries the callable signature and variadic parameter name; declaration order comes from the signature.

`BindCallableArguments` remains the shared suffix-from-back binding kernel for prefix binding, variadic middle capture, suffix binding, and arity checks. `CreateVariadicCapture` still owns variadic capture construction and materializes the collected rest as one exact immutable `Result.ListValue` with emitted count 1 (`CollectRest`; Lean `collectRest`). Runtime input construction remains context-specific: user calls build call items from expressions, algorithm arguments, and dot-call boundary flags; loop binding receives already evaluated state slots. Patterned/sequence-value execution remains `ParameterPattern`-based, and callback and builtin binding remain separate runtime-owned paths with their own documented binding rules; they do not use this flat variadic layout.

## Migration boundaries / follow-up areas

Future work should start from characterization tests before moving more execution logic. The current safe boundary is shared surface/diagnostics/shape plus selected user-call and generic user loop-step routing. Any deeper migration must preserve runtime semantics for algorithm/value channels, sequence-value captures, explicit block arguments, counted callback views, loop state slots, builtin sequence rules, and conditional branch matching.
