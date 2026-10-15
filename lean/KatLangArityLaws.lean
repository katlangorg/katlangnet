import CoreArityAlgebra
import KatLang

open KatLang

/-
# KatLangArityLaws

Arity laws over the authoritative value algebra, the total helpers of `KatLang.lean` and the
total Model-C binder.

`CoreArityAlgebra.lean` defines the small paper-facing algebra, while
`CoreArityAlgebraProofs.lean` proves its small laws and executable checks.
This file proves laws over real KatLang `Result` constructors, normalization,
value views and the total helpers of `KatLang.lean`.

EVIDENCE CATEGORIES (R8/X-13, October 2026). Every theorem here is one of:

* a PRODUCTION theorem — about TOTAL definitions of `KatLang.lean` that the evaluator
  calls (value views such as `Result.normalize`, `Result.spreadItems`,
  `Result.projectionItems`, `reCountValueBoundary`; the slot combination `combineOutputSlots`
  and the spread-row view `countedTopLevelValues`; the repeated-spread helpers
  `reopenSpreadItems` / `reopenSpreadLayers` / `spreadSupplyResult`; the selection core
  `selectPosition` / `selectWith` / `selectionResult`; `prepareLexicalDotCallArgs`; the Model-C
  R5 supply/demand control `NeedSupply` / `NeedDemand` and their total public entry points
  (proved in `KatLangArityLaws/NeedControl.lean`); the
  binder `bindNeedPatterns`, its generic core `NeedBinder` and the clause activation
  `needActivateBranch`, and its allocation `needLevelSources`). It says nothing about the
  `partial` evaluator definitions that call those helpers (`evalCounted`, `demandNeedRecursive`,
  `evalResolvedCallCounted`, `callLexicalWithReceiverCounted`, …): that
  a `partial` caller applies a helper is a fact of the source, checked by the CoreTests
  guards and the Lean/C# differential corpora, never a kernel fact;
* a SPECIFICATION theorem — about a Lean specification of a C#-only front-end decision that
  the evaluator never calls (`liftsBareValueReference`, `forwardingSource`,
  `bareForwarding*`, `liftingSlotRole`, `familyLiftingSignature?`, the static alias chase
  `staticAliasTarget?`). It proves the specification, never the C# implementation, whose
  agreement rests on tests;
* a LOCAL theorem — about a helper defined in this file (`captureForArityLaw`,
  `selectionOf`, `selectionTrace`, `plainNeedBinding`, `atomsBuiltinResultForLaw`, the
  C#-shaped `shallowSpreadLayersForLaw` / `shallowSpreadResultForLaw`, …), whose docstring
  names the production definitions it wraps (or, for the C#-shaped ones, the C# source it
  models — no theorem here proves C# code);
* the ALGEBRA CORRESPONDENCE `algebra_binder_is_the_production_allocation` — the paper
  algebra's binder is the production ALLOCATION under its guard, not the binder's result;
* a TRACE theorem (R3, the submodules `KatLangArityLaws/BinderTrace.lean` and
  `KatLangArityLaws/FamilyDispatch.lean`) — about THE production core (`NeedBinder`, the same
  definitions the production binder and dispatcher are) run in a local interpretation defined
  there (`TraceM`, the protected lifting `traced`, the schedule functions `oneEvents` …); it
  speaks of production through `trace_erasure` / `trace_erasure_dispatch`, which erase it to
  the production run exactly, and like every theorem here says nothing about the `partial`
  callers or C#;
* a CORRESPONDENCE theorem (R3, the submodule `KatLangArityLaws/BinderCorrespondence.lean`) — a
  PRODUCTION theorem over the generic core's `EvalM` runs at any capability record, which reads
  the schedule functions of `BinderTrace` (their meaning as the actual invocations is
  `traced_patterns`): channel substitution, its static form, and the family/ordinary mode
  correspondence.

The superseded pre-Model-C Ready binder (completed inputs) and every theorem stated over it
were retired on 2026-10-12 (owner decision; git history keeps them): no theorem here is about
that model.

The PRODUCTION binder's own laws — its top-level cardinality gate before every effect,
its allocation of a level's supply (any lengths), plain binding demanding nothing, and
the arity algebra as its allocation — are proved in § Model-C production binder laws
(FORMAL-07, October 2026), with the production collector and dot-receiver laws after them
(R8/X-13). Its DEMAND ORDER is proved since R3 (October 2026): § The generic binder core
records that the production binder is the `EvalM` specialization of the one generic core
`NeedBinder`, and the submodules `KatLangArityLaws/BinderTrace.lean` and
`KatLangArityLaws/FamilyDispatch.lean` (built by this target through its `globs`) run that core
in an external boundary trace that erases exactly to the production run and prove its
syntax-indexed event schedule — written order, inspection, ready allocation, nesting,
first-failure truncation, the per-occurrence silence of plain non-repeated bindings at any
position, the repeated-name order and verdict (not Q-28's permutation laws), the clause search
and arbitrary-context activation; `KatLangArityLaws/BinderCorrespondence.lean` proves channel
substitution per channel (results depend on the channels only through the cells a run invokes),
its static form (a head invokes its channels only on cells at inspecting positions or on cells
the run allocated) and the family/ordinary mode correspondence for every head (a literal-free
head's ordinary binding is never a non-match); `KatLangArityLaws/BinderGuards.lean` executes
concrete schedules on real heaps. The outcomes of the four opaque helpers stay symbolic there,
and the CoreTests.ModelC / RepeatedNameConstraints guards remain the evaluator-level
witnesses. § Repeated spread over the real model (Q-66 item 4) proves the
repeated-spread laws over `Result` and the production reopening helpers: shallow slot
combination is ordinary capture on canonical slots, the grouped `(A*)*` layer is the stacked
`A**` step, only a lone item opens one more boundary, and repeated spread never flattens (the
`partial` evaluator's routing through those helpers is guard-checked by CoreTests.RepeatedSpread).
The final section, § String interpolation (STR-02), proves the interpolation combinator's laws — left to right,
each hole once, the first failure stops — for every hole channel, and the structural value text.
-/

/--
Paper-facing alias for the real `Result` expression used to normalize
ORDINARY captured item supplies: `Result.normalize (Result.sequenceValue xs)`.

This is `capture : Supply -> Value` — the normalizing value/output capture
boundary (`x = 1, 2, 3`). It is NOT the collecting-binding operation: collecting binding
materializes `collect : Supply -> ListValue` (value-level definition `collectSegment`; in
production, `makeCollectionListResult` on the collector cell's VALUE demand), and the spread
marker is `spread : Value -> Supply` (`Result.spreadItems`). The laws below relate the three
operations at the value level; which operation a receiver applies is the evaluator's (a fact
of its `partial` source, pinned by guards), proved here only for the collector's allocation
over the production binder (`lone_collector_collects_every_supplied_cell`).
-/
def captureForArityLaw (xs : List Result) : Result :=
  Result.normalize (Result.sequenceValue xs)

/-- Every depth of written empty-sequence grouping builds the one canonical `()` (the total
helper the `partial` evaluator's `.emptySequence` arm calls; that call is a source fact). -/
theorem build_empty_sequence_value_is_empty_sequence (depth : Nat) :
    buildEmptySequenceValue depth = Result.sequenceValue [] := rfl

theorem normalize_empty_sequenceValue :
    Result.normalize (Result.sequenceValue []) = Result.sequenceValue [] := by
  simp [Result.normalize]

theorem normalize_nested_empty_sequence :
    Result.normalize (Result.sequenceValue [Result.sequenceValue []]) = Result.sequenceValue [] := by
  simp [Result.normalize]

theorem toItems_sequenceValue (xs : List Result) :
    Result.toItems (Result.sequenceValue xs) = xs := by
  rfl

/-
`captureForArityLaw` is `Result.normalize` after `Result.sequenceValue`.
This alias theorem is intentionally small; capture is the ORDINARY
value/output construction boundary only. Collecting bindings never use it — a collector's
value is `collectSegment` (`make_collection_list_result_is_collect_segment`), and the production
collector's allocation is `lone_collector_collects_every_supplied_cell`. Capture is not raw
grouping: singleton capture collapses, while a singleton collected segment stays `[item]`.
-/
theorem captureForArityLaw_eq_normalize_sequenceValue (xs : List Result) :
    captureForArityLaw xs = Result.normalize (Result.sequenceValue xs) := by
  rfl

theorem capture_singleton (v : Result) :
    captureForArityLaw [v] = Result.normalize v := by
  simp [captureForArityLaw, Result.normalize]

theorem normalize_sequenceValue_singleton (v : Result) :
    Result.normalize (Result.sequenceValue [v]) = Result.normalize v := by
  simp [Result.normalize]

theorem capture_pair (a b : Result) :
    captureForArityLaw [a, b] =
      Result.sequenceValue [Result.normalize a, Result.normalize b] := by
  simp [captureForArityLaw, Result.normalize]

theorem normalize_sequenceValue_pair (a b : Result) :
    Result.normalize (Result.sequenceValue [a, b]) =
      Result.sequenceValue [Result.normalize a, Result.normalize b] := by
  simp [Result.normalize]

/-
The real model interprets a collection builtin's bound `collection` argument
through the POST-BINDING one-level view `builtinCollectionItems` (`count(A)`,
`sum(A)`). This is not arbitrary recursive flattening, and it never alters
argument boundaries BEFORE binding — collection builtins are ordinary
fixed-arity callables (`count(collection)`, `take(collection, count)`), so an
unspread sequence or list is one argument like at every other call boundary.
Call parameter binding never uses this view. Assignment
deconstruction opens its single right-hand side value through a different
mechanism: its unpacking receiver (`.unpacking`, which opens with the
equivalent one-level view `Result.spreadItems`), not the builtin collection
view; in production the unpacking level is `bindNeedLevel` itself
(`nested_unpack_level_is_bind_need_level`).
-/
theorem builtinCollectionItems_sequence (xs : List Result) :
    builtinCollectionItems (Result.sequenceValue xs) = xs := rfl

theorem builtinCollectionItems_nested_pair_opens_one_boundary :
    builtinCollectionItems
      (Result.sequenceValue [Result.atom 1, Result.sequenceValue [Result.atom 2, Result.atom 3]])
      = [Result.atom 1, Result.sequenceValue [Result.atom 2, Result.atom 3]] := rfl

/-- A scalar collection argument is a one-element collection (`count(7)` is 1). -/
theorem builtinCollectionItems_atom (n : Int) :
    builtinCollectionItems (Result.atom n) = [Result.atom n] := rfl

/-
## Segment collection laws (`collect : Supply -> ListValue`)

`collectSegment` is the VALUE-LEVEL definition of collecting-binding materialization. The
production Model-C binder allocates ONE suspended collector cell over the collector's slice of
supply cells
(`lone_collector_collects_every_supplied_cell`, `need_level_sources_around_the_collector`), and
the total `NeedDemand.materialize` helper materializes that cell's VALUE as
`makeCollectionListResult` of the demanded slice values, which IS `collectSegment` at emitted
count 1 (`make_collection_list_result_is_collect_segment`). R5 connects the total public
`demandNeed` collector arm to that helper by kernel theorems (`KatLang.NeedControl.Production.demand_specialization`,
`collector_specialization` and `collector_success` in `KatLangArityLaws/NeedControl.lean`). The
internal partial `demandNeedRecursive` driver's use of the same shell remains source/guard
evidence, pinned by CoreTests.ModelC. Deconstruction and nested structural patterns
open their one value before allocation. The laws below are the value-level exactness
properties of that materialization.
-/

/-- Stable result kind + exact elements: the materialized collection is ALWAYS the exact
immutable list of precisely the assigned items, in order. This is the closed
form of `collect`; length preservation and element exactness are immediate. -/
theorem collectSegment_eq_listValue (xs : List Result) :
    collectSegment xs = Result.listValue xs := rfl

/-- Exact length: collecting never adds, drops, or merges items. -/
theorem collectSegment_length (xs : List Result) :
    (collectSegment xs).projectionItems.length = xs.length := rfl

/-- Zero assigned items collect to the exact empty list `[]` — never the
invisible empty sequence value `()`. -/
theorem collectSegment_empty : collectSegment [] = Result.listValue [] := rfl

/-- No value is an element of its own list payload: an element of `ys` is
structurally smaller than `Result.listValue ys`. -/
theorem mem_ne_listValue {w : Result} {ys : List Result} (h : w ∈ ys) :
    w ≠ Result.listValue ys := by
  intro he
  have hlt : sizeOf w < sizeOf ys := List.sizeOf_lt_of_mem h
  have hsz : sizeOf (Result.listValue ys) = 1 + sizeOf ys := by simp
  rw [he, hsz] at hlt
  omega

/-- Singleton preservation: one assigned item collects to the one-element list
`[v]` — for every value kind, including lists, sequences, `[]`, and `()`. -/
theorem collectSegment_singleton (v : Result) :
    collectSegment [v] = Result.listValue [v] := rfl

-- Structured singleton segments over the real model: the boundary of the one
-- remaining item is preserved exactly, for every structure kind.
example (ys : List Result) :
    collectSegment [Result.sequenceValue ys]
      = Result.listValue [Result.sequenceValue ys] := rfl
example (ys : List Result) :
    collectSegment [Result.listValue ys]
      = Result.listValue [Result.listValue ys] := rfl
example : collectSegment [Result.sequenceValue []]
    = Result.listValue [Result.sequenceValue []] := rfl
example : collectSegment [Result.listValue []]
    = Result.listValue [Result.listValue []] := rfl

/-- A singleton collected segment is NEVER erased to its item: `collect [v] ≠ v`. This is
the load-bearing difference from canonical capture (`capture [v] = v` after
normalization), and what keeps one remaining structured row distinct from the
row's own elements. -/
theorem collectSegment_singleton_ne_item (v : Result) :
    collectSegment [v] ≠ v := by
  intro he
  exact absurd he.symm (mem_ne_listValue List.mem_cons_self)

/-- Open/collect round trip at the VALUE level: the spread view (`open`, `Result.spreadItems`)
of a collected list is EXACTLY the collected items. This is the value-level face of
collecting-parameter forwarding (`Forward(*items) = Target(items*)`, FWD-01): read through
`make_collection_list_result_is_collect_segment`, spreading a materialized collector gives back
its demanded element values. Production forwarding itself transports the collector's own slice
CELLS, unforced (the known-slice arm of the total `NeedSupply.slot`, recognized by
`spreadCollectorSlice?`; `KatLangArityLaws/NeedControl.lean` proves exact reopening and
public `formNeedSupplySourced` specialization; CoreTests.ModelC `sliceTransport`), and the
target's collector then collects exactly the cells supplied
(`lone_collecting_head_allocates_one_collector_over_its_supply`). -/
theorem spreadItems_collectSegment (xs : List Result) :
    (collectSegment xs).spreadItems = xs := rfl

/-- A collected list is one visible value: its `Result.valueCount` is 1, the empty collected
list `[]` included. (That a boundary emits `valueCount` is the evaluator's source fact.) -/
theorem valueCount_collectSegment (xs : List Result) :
    (collectSegment xs).valueCount = 1 := rfl

/-- Collecting the concatenation of two spread views is exactly the list of those items — an
instance of `collectSegment_eq_listValue` (`collect` takes a supply, which records no
provenance; the deconstruction example `first, *rest = 1, [2, 3]*, (4, 5)*` giving
`rest = [2, 3, 4, 5]` is evaluator behaviour, pinned by guards). -/
theorem collectSegment_spread_concat_exact (a b : Result) :
    collectSegment (a.spreadItems ++ b.spreadItems)
      = Result.listValue (a.spreadItems ++ b.spreadItems) := rfl

/-- Collect/open round trip on the list side: re-collecting a spread list's
items reproduces the list exactly (`collect ∘ open = id` on exact list
values, the real-model face of the core `collect_items_list`). -/
theorem collectSegment_spreadItems_listValue (xs : List Result) :
    collectSegment ((Result.listValue xs).spreadItems) = Result.listValue xs := rfl

/-- `collectSegment` normalizes element-wise only: the collected list boundary is
already canonical, so normalization can only touch the stored elements
(the real-model face of the core `collect_normalize_elementwise`). -/
theorem collectSegment_normalize_elementwise (xs : List Result) :
    (collectSegment xs).normalize = collectSegment (xs.map Result.normalize) := by
  simp [collectSegment, Result.normalize]

private theorem map_normalize_id_of_canonical : ∀ {xs : List Result},
    (∀ r ∈ xs, r.normalize = r) -> xs.map Result.normalize = xs
  | [], _ => rfl
  | r :: rs, h => by
      have hr := h r List.mem_cons_self
      have ih := map_normalize_id_of_canonical (xs := rs)
        (fun q hq => h q (List.mem_cons_of_mem r hq))
      simp [hr, ih]

/-- Canonical-supply invariant at the collect boundary: when every supplied
value is already canonical (observable runtime supplies are intended to be; that the
evaluator's construction sites normalize is assumed here, not proved), the collected
list is itself a `Result.normalize` fixed point. `collectSegment` performs no
normalization of its own (`collectSegment xs = Result.listValue xs` stores the
supply unchanged); canonicality of the result comes entirely from the input
invariant. This is the real-model face of the core
`normalize_collect_of_canonicalSupply`. -/
theorem collectSegment_canonical_of_canonical_elements {xs : List Result}
    (h : ∀ r ∈ xs, r.normalize = r) :
    (collectSegment xs).normalize = collectSegment xs := by
  rw [collectSegment_normalize_elementwise, map_normalize_id_of_canonical h]

/-
## Dot-receiver bridge laws (dot-call passes a value)

For extension-call fallback (a structural MISS: `evalDotCallCounted` tries a declared member
first), `receiver.F(args)` is the written call `F(receiver, args)`. What is PROVED here is the
argument PREPARATION: `prepareLexicalDotCallArgs` places the ORIGINAL receiver expression as the
ordinary first slot of the bundle, adding nothing else. Everything after preparation is
`partial` and therefore a fact of the source, executed by CoreTests `DotReceiverSegments` /
`DotCallSemantics` and the Lean/C# differential corpora, not a theorem:
`callLexicalWithReceiverCounted` hands the bundle to the ONE `evalResolvedCallCounted` funnel
every written call uses, and `formNeedSupply` forms one supply cell per non-spread slot. No
dot-call ≡ direct-call evaluator theorem exists (Q-66 keeps the dot-funnel obligation open).

Given those source facts, the ordinary argument laws apply to the receiver unchanged, and the
binder half of each is a production theorem over the cell the receiver forms (§ Production
collector and dot-receiver laws, after the FORMAL-07 section):

- a collecting parameter collects the receiver's ONE cell as exactly one item whatever its
  value (`lone_collector_collects_every_supplied_cell`,
  `lone_collecting_head_allocates_one_collector_over_its_supply`);
- the receiver is ONE cell for arity checking and fixed prefix/suffix allocation — its item
  count never satisfies arity, and the gate fails before any demand
  (`one_cell_supply_fails_two_fixed_patterns_before_any_effect`);
- a FIXED parameter after a collector takes the last cell, the receiver's when it is the only
  one (`collector_before_a_fixed_pattern_takes_all_but_the_last_cell`);
- only the spread marker opens a receiver: `R*.F(args)` is the ordinary spread slot of
  `F(R*, args)` (the C# parser lowers the surface form to that call; preparation keeps a
  host-built spread receiver unopened).
-/

/-- Argument PREPARATION for extension-call fallback: `receiver.F(args)` prepares exactly the
argument bundle of the written call `F(receiver, args)` — the receiver is the ordinary leading
slot. (That the bundle then reaches the ordinary call funnel is a `partial`-source fact.) -/
theorem dot_receiver_is_ordinary_leading_argument (receiver : Expr) (args : OutputBundle) :
    prepareLexicalDotCallArgs receiver (some args) = receiver :: args := rfl

/-- Argument PREPARATION for the argumentless dotted spelling: on extension-call fallback,
`receiver.F` prepares the one-slot bundle of the written call `F(receiver)`. -/
theorem argumentless_dot_receiver_is_the_one_argument (receiver : Expr) :
    prepareLexicalDotCallArgs receiver none = [receiver] := rfl

/-- Argument PREPARATION keeps a spread receiver unopened: `R*.F(args)` prepares the bundle of
the written spread call `F(R*, args)`, the spread slot left for supply formation to open like
every other spread slot (the total `NeedSupply` core, specialized by `formNeedSupply`).
Surface `R*.F(args)` is lowered to that
call by the C# parser, so this concerns host-built trees. -/
theorem spread_dot_receiver_is_ordinary_spread_argument (operand : Expr) (args : OutputBundle) :
    prepareLexicalDotCallArgs (.sequenceSpread operand) (some args)
      = .sequenceSpread operand :: args := rfl

/-- CALLEE-position dot resolution unfolds to the structural projection followed by alias
normalization (DOT-09; Q-18 C-B3): `resolveCalleeAlg` of a dot callee is
`projectNeedStructuralMember`, then `resolveAliasTarget`, and a computed dot value with no
structural member is `notAnAlgorithm`. This is the definition of the total `resolveCalleeAlg`'s
dot arm; both composed functions are `partial`. That the supplied-argument projection
(`projectNeedCallable`'s dot arm, `partial`) agrees with it — the single callable identity in
every position, `(Box.G)(2)` as the member call `Box.G(2)` — is a source fact pinned by guards,
not part of this statement. -/
theorem dot_callee_resolution_is_structural_projection_then_alias
    (receiver : Expr) (name : Ident) (fallback : Expr) (args : Option OutputBundle) (ctx : EvalCtx) :
    resolveCalleeAlg (.dotMember receiver name fallback args) ctx =
      (do
        match <- projectNeedStructuralMember (.dotMember receiver name fallback args) ctx with
        | some algorithm => resolveAliasTarget algorithm ctx
        | none => .error (Error.notAnAlgorithm computedDotCalleeDescription)) := rfl

/-
## Exact collector laws (September 2026)

VALUES STAY VALUES. A collecting parameter collects exactly the items the
binder allocated to it (after fixed prefix/suffix allocation) as ONE exact list
and never inspects or opens an item: every non-spread written argument is ONE item
whatever its value, so a lone sequence, list, `()`, or `[]` is collected as that one
value. Only an explicit spread (the caller's `v*`) or an explicit structural pattern (the
callee's `((*xs))` or `([*xs])`) turns one value into several items.

EVIDENCE. The PRODUCTION Model-C binder binds supply CELLS, never values, and its collector
law is value-blind: `lone_collector_collects_every_supplied_cell`,
`collector_before_a_fixed_pattern_takes_all_but_the_last_cell`,
`lone_collecting_head_allocates_one_collector_over_its_supply` (§ Production collector and
dot-receiver laws), with `need_level_sources_around_the_collector` and
`need_level_sources_without_collector` for every level and length; the collector cell's value is
`make_collection_list_result_is_collect_segment`. That a written argument forms ONE cell, and
that computed spreads allocate Ready cells in opened-item order and known slices transport
their exact addresses, is proved over the total `NeedSupply` core and public `formNeedSupply`
specialization in `KatLangArityLaws/NeedControl.lean`. The partial evaluator's installation of
`evalCounted` remains source/guard evidence, pinned by CoreTests `ExplicitValueOpening` / `ModelC`.
Dot-call and selection add
nothing to the collector: a dot receiver is an ordinary leading slot
(`dot_receiver_is_ordinary_leading_argument`) and a selection's result is the selected value
itself (`select_is_a_value_boundary`). The one law of this section is the spread VIEW that supply
formation reads.
-/

/-- The spread VIEW opens a sequence and a list alike, exactly one level, and an atom gives
itself: `Result.spreadItems`, which the `partial` spread arms of the evaluator read (a source
fact; `Coll((1, 2)*)` and `Coll([1, 2]*)` both supply `1, 2` by supply formation, pinned by
guards). Since Model C a spread of a collecting PARAMETER transports its cells instead
(`formNeedSupplySourced`'s known-slice arm, `spreadCollectorSlice?`). -/
theorem explicit_spread_opens_one_level (items : List Result) (n : Int) :
    (Result.sequenceValue items).spreadItems = items
    ∧ (Result.listValue items).spreadItems = items
    ∧ (Result.atom n).spreadItems = [.atom n] := ⟨rfl, rfl, rfl⟩

/-
## Zero-supply acceptance laws (September 2026)

A callable may satisfy a ZERO-ARGUMENT VALUE DEMAND exactly when an ordinary
call supplying zero arguments can bind it. Both sides read the ONE rule
`ParameterPattern.minimumSuppliedSlots`: every pattern consumes one supplied slot, except
that the (single) collecting capture at that level consumes none. On every signature with at
most one top-level collector — every X-02-valid signature — it IS the production binder's own
count `needMinimumSuppliedSlots` (`binder_minimum_is_the_signature_minimum`).

The laws below pin (1) the rule's values, (2) that a user algorithm accepts zero supplied
arguments exactly when that minimum is zero (the production gate's laws are
`cardinality_gate_accepts_empty_supply_iff_minimum_zero` and
`zero_argument_acceptance_is_the_binder_gate`), and (3) that the demand law
(`zeroArgumentDemandError?`) accepts exactly those callables and reports that
minimum when it does not.
-/

theorem minimum_supplied_slots_empty :
    ParameterPattern.minimumSuppliedSlots [] = 0 := rfl

/-- A collecting parameter contributes ZERO required slots: `Only(*xs)` accepts
an empty supply. -/
theorem minimum_supplied_slots_lone_collector (name : Ident) :
    ParameterPattern.minimumSuppliedSlots
      [.capture { name := name, kind := .collecting }] = 0 := rfl

theorem minimum_supplied_slots_fixed_list (x y : Ident) :
    ParameterPattern.minimumSuppliedSlots
      [.capture { name := x }, .capture { name := y }] = 2 := rfl

/-- `Head(x, *rest)` still requires ONE supplied value — the collector does not
excuse the fixed prefix. -/
theorem minimum_supplied_slots_required_prefix (x r : Ident) :
    ParameterPattern.minimumSuppliedSlots
      [.capture { name := x }, .capture { name := r, kind := .collecting }] = 1 := rfl

/-- `Tail(*rest, z)` likewise requires ONE supplied value. -/
theorem minimum_supplied_slots_required_suffix (r z : Ident) :
    ParameterPattern.minimumSuppliedSlots
      [.capture { name := r, kind := .collecting }, .capture { name := z }] = 1 := rfl

/-- A nested pattern consumes ONE supplied slot whatever it contains, so a
collector INSIDE a group never lowers the outer minimum: `P((*xs))` still needs
one supplied value — a sequence, which the group opens — rather than standing
for none. -/
theorem minimum_supplied_slots_group_is_one_slot (items : List ParameterPattern) :
    ParameterPattern.minimumSuppliedSlots [.sequenceValue items] = 1 := rfl

/-- `G((a, b), *rest)` requires ONE supplied slot: the group's, since the
top-level collector requires none. -/
theorem minimum_supplied_slots_group_then_collector (items : List ParameterPattern) (r : Ident) :
    ParameterPattern.minimumSuppliedSlots
      [.sequenceValue items, .capture { name := r, kind := .collecting }] = 1 := rfl

/-- A collecting-only user algorithm accepts zero supplied arguments (acceptance is the
minimum being zero; the general production statement is
`zero_argument_acceptance_is_the_binder_gate`). -/
theorem accepts_zero_collecting_only
    (name : Ident) (op : List Expr) (props : List PropDef) (out : List Expr) :
    Algorithm.acceptsZeroSuppliedArguments
      (Algorithm.mk none [.capture { name := name, kind := .collecting }] op props out)
      = true := rfl

theorem rejects_zero_required_prefix
    (x r : Ident) (op : List Expr) (props : List PropDef) (out : List Expr) :
    Algorithm.acceptsZeroSuppliedArguments
      (Algorithm.mk none
        [.capture { name := x }, .capture { name := r, kind := .collecting }] op props out)
      = false := rfl

theorem rejects_zero_required_suffix
    (r z : Ident) (op : List Expr) (props : List PropDef) (out : List Expr) :
    Algorithm.acceptsZeroSuppliedArguments
      (Algorithm.mk none
        [.capture { name := r, kind := .collecting }, .capture { name := z }] op props out)
      = false := rfl

/-- A builtin never accepts a zero-argument supply (`sum()` is an arity error);
its rejection stays owned by `evalBuiltinValueCounted`. -/
theorem builtin_never_accepts_zero_supply (b : Builtin) :
    Algorithm.acceptsZeroSuppliedArguments (.builtin b) = false := rfl

/-- ELIGIBILITY EQUIVALENCE. Away from builtins (whose rejection the law
deliberately leaves to `evalBuiltinValueCounted`), the zero-argument value-demand
law accepts EXACTLY the callables that accept zero supplied arguments. -/
theorem zero_argument_value_demand_accepts_exactly_zero_supply_callables
    (a : Algorithm) (h : ∀ b, a ≠ Algorithm.builtin b) :
    acceptsZeroArgumentValueDemand a = Algorithm.acceptsZeroSuppliedArguments a := by
  cases a with
  | builtin b => exact absurd rfl (h b)
  | mk p ps op pr out id =>
      unfold acceptsZeroArgumentValueDemand zeroArgumentDemandError?
      cases Algorithm.acceptsZeroSuppliedArguments (Algorithm.mk p ps op pr out id) <;> simp
  | conditional p op bs id =>
      unfold acceptsZeroArgumentValueDemand zeroArgumentDemandError?
      cases Algorithm.acceptsZeroSuppliedArguments (Algorithm.conditional p op bs id) <;> simp
  | alias p op pr target id =>
      unfold acceptsZeroArgumentValueDemand zeroArgumentDemandError?
      cases Algorithm.acceptsZeroSuppliedArguments (Algorithm.alias p op pr target id) <;> simp

/-- The demand law accepts a collecting-only callable at a named demand site. -/
theorem zero_argument_demand_accepts_collecting_only
    (name propertyName : Ident) (op : List Expr) (props : List PropDef) (out : List Expr) :
    zeroArgumentDemandError? (some (.resolve propertyName))
      (Algorithm.mk none [.capture { name := name, kind := .collecting }] op props out)
      = none := rfl

/-- ... and rejects a required-prefix callable with its true MINIMUM (1), not
the flattened declared capture count (2). -/
theorem zero_argument_demand_rejects_required_prefix_with_minimum
    (x r propertyName : Ident) (op : List Expr) (props : List PropDef) (out : List Expr) :
    zeroArgumentDemandError? (some (.resolve propertyName))
      (Algorithm.mk none
        [.capture { name := x }, .capture { name := r, kind := .collecting }] op props out)
      = some (Error.withContext (CtxMsg.property propertyName) (Error.arityMismatch 1 0)) := rfl

/-- A nested group is ONE required slot, so `P((x, y))` reports 1 rather than
its two flattened captures. -/
theorem zero_argument_demand_rejects_group_with_one_required_slot
    (x y propertyName : Ident) (op : List Expr) (props : List PropDef) (out : List Expr) :
    zeroArgumentDemandError? (some (.resolve propertyName))
      (Algorithm.mk none
        [.sequenceValue [.capture { name := x }, .capture { name := y }]] op props out)
      = some (Error.withContext (CtxMsg.property propertyName) (Error.arityMismatch 1 0)) := rfl

/-
## An inline callable alias has no report of its own (FA-OQ-1, owner decision Option B, 2026-10-10)

An inline block whose one row names a parameterized callable (`{ F }`) is a callable
alias (`Algorithm.alias`): binding indirection, with no signature and no report of its
own. A zero-argument VALUE demand of it is judged on its normalized target (the demanded
algorithm `a`) and REPORTED exactly as its written target reference — a name or a declared
member path, the only alias targets — reports it, whatever the target is: a user
algorithm's arity, a family's `noMatchingBranch`, a builtin's pass-through. A written
block that is NOT an alias keeps the block's own `unresolvedImplicitParams`.
-/

/-- For the same demanded algorithm, the zero-argument demand law gives an inline alias of a
NAME the same verdict and report as the name itself. (That the alias's demanded algorithm is
the name's target is `resolveAliasTarget`'s, a `partial` source fact pinned by guards.) -/
theorem inline_alias_demand_reports_as_its_name_reference
    (p : Option ScopeCtx) (op : List Expr) (props : List PropDef) (name : Ident)
    (id : Option PropertyIdentity) (a : Algorithm) :
    zeroArgumentDemandError? (some (.algorithmExpr (.alias p op props (.resolve name) id))) a
      = zeroArgumentDemandError? (some (.resolve name)) a := by
  cases a <;> rfl

/-- For the same demanded algorithm, the zero-argument demand law gives an inline alias of a
declared MEMBER PATH the same verdict and report as the path itself. -/
theorem inline_alias_demand_reports_as_its_member_reference
    (p : Option ScopeCtx) (op : List Expr) (props : List PropDef) (receiver fallback : Expr)
    (member : Ident) (id : Option PropertyIdentity) (a : Algorithm) :
    zeroArgumentDemandError?
        (some (.algorithmExpr (.alias p op props (.dotMember receiver member fallback none) id))) a
      = zeroArgumentDemandError? (some (.dotMember receiver member fallback none)) a := by
  cases a <;> rfl

/-- The canonical witness: `{ Inc }` with `Inc(x) = x + 1` is Inc's property-context
cardinality `arityMismatch 1 0` — never the written block's `unresolvedImplicitParams`. -/
theorem inline_alias_of_a_required_argument_callable_is_its_arity
    (p : Option ScopeCtx) (op : List Expr) (props : List PropDef) (name x : Ident)
    (id : Option PropertyIdentity) (op' : List Expr) (props' : List PropDef) (out : List Expr) :
    zeroArgumentDemandError? (some (.algorithmExpr (.alias p op props (.resolve name) id)))
      (Algorithm.mk none [.capture { name := x }] op' props' out)
      = some (Error.withContext (CtxMsg.property name) (Error.arityMismatch 1 0)) := rfl

/-- A written block that is NOT an alias reports its OWN inferred parameters (the
block's `Algorithm.params`; `ParameterPattern.captures` is `partial`, so the list is
stated through it rather than computed). -/
theorem written_block_reports_its_own_unresolved_implicit_params
    (x : Ident) (op : List Expr) (props : List PropDef) (out : List Expr) :
    zeroArgumentDemandError?
        (some (.algorithmExpr (Algorithm.mk none [.capture { name := x }] op props out)))
        (Algorithm.mk none [.capture { name := x }] op props out)
      = some (Error.unresolvedImplicitParams
          (Algorithm.params (Algorithm.mk none [.capture { name := x }] op props out))) := rfl

/-
## Implicit-lifting eligibility follows zero-argument acceptance (Q-03, September 2026)

The C# surface pass lifts a bare value-position reference into an implicit
forwarding call exactly when the callee REQUIRES supplied arguments. Lean states that
decision as the SPECIFICATION predicate `liftsBareValueReference` (over the same
`minimumSuppliedSlots` rule as the zero-argument law); the Lean evaluator never calls it and no
Lean model of the C# resolver exists, so these are specification laws — the C# resolver's
agreement rests on `ZeroArgumentReferenceLiftingTests` and CoreTests `PropertyCacheConsumers`.
A callee that accepts zero supplied arguments — no parameter, or only a top-level collector —
is not lifted by the specification. The laws below pin the decision table and relate the
specification predicate to the evaluator's TOTAL eligibility predicates: for a user algorithm,
"lifted" and "cacheable demand" are exact complements (by definition: both read
`minimumSuppliedSlots`), so a reference the specification leaves bare is a demand the
zero-argument law accepts and the cache eligibility predicate admits. No theorem models the
cache lookup itself.
-/

theorem lifting_skips_parameterless_signature :
    liftsBareValueReference [] = false := rfl

/-- `Roll(*xs)` works with no arguments, so the specification does not lift its bare name. -/
theorem lifting_skips_collecting_only_signature (name : Ident) :
    liftsBareValueReference [.capture { name := name, kind := .collecting }] = false := rfl

/-- `Inc(x)` requires its argument, so the specification lifts its bare name. -/
theorem lifting_keeps_required_parameter (x : Ident) :
    liftsBareValueReference [.capture { name := x }] = true := rfl

/-- `Head(x, *rest)` requires ONE supplied value beside the collector: the specification
lifts it. -/
theorem lifting_keeps_required_prefix (x r : Ident) :
    liftsBareValueReference
      [.capture { name := x }, .capture { name := r, kind := .collecting }] = true := rfl

/-- Any lone sequence pattern — a group holding a collector, `H((*xs))`, included — is one
required slot: the specification lifts it (whatever `items` holds). -/
theorem lifting_keeps_grouped_collector (items : List ParameterPattern) :
    liftsBareValueReference [.sequenceValue items] = true := rfl

/-- Q-03 as a SPECIFICATION IDENTITY. For a user algorithm, the specification predicate
`liftsBareValueReference` holds exactly when the evaluator's cache eligibility predicate
`isCacheableZeroArgPropertyAlgorithm` does NOT: lifting and cache eligibility are complements
of ONE rule. Definitional (`rfl`): both sides read `minimumSuppliedSlots`. It proves neither the
C# resolver's lifting decision nor a cache lookup. -/
theorem lifts_bare_value_reference_iff_not_cacheable
    (p : Option ScopeCtx) (ps : List ParameterPattern) (op : List Expr)
    (pr : List PropDef) (out : List Expr) (id : Option PropertyIdentity) :
    liftsBareValueReference ps
      = !isCacheableZeroArgPropertyAlgorithm (Algorithm.mk p ps op pr out id) := rfl

private theorem bool_true_of_not_eq_false {b : Bool} (h : (!b) = false) : b = true := by
  revert h
  cases b <;> decide

/-- Consequently, for a user signature the specification does not lift, the zero-argument
demand law ACCEPTS the callable (never a rejection) and the cache eligibility predicate admits
it (it is never lifted into a fresh call). That the C# resolver leaves such a reference bare,
and that the run cache then serves it, are not stated here. -/
theorem unlifted_bare_reference_is_an_accepted_cacheable_demand
    (p : Option ScopeCtx) (ps : List ParameterPattern) (op : List Expr)
    (pr : List PropDef) (out : List Expr) (id : Option PropertyIdentity)
    (h : liftsBareValueReference ps = false) :
    acceptsZeroArgumentValueDemand (Algorithm.mk p ps op pr out id) = true
      ∧ isCacheableZeroArgPropertyAlgorithm (Algorithm.mk p ps op pr out id) = true := by
  have hc : isCacheableZeroArgPropertyAlgorithm (Algorithm.mk p ps op pr out id) = true :=
    bool_true_of_not_eq_false
      ((lifts_bare_value_reference_iff_not_cacheable p ps op pr out id).symm.trans h)
  refine ⟨?_, hc⟩
  rw [zero_argument_value_demand_accepts_exactly_zero_supply_callables _
    (fun b hb => by cases hb)]
  exact hc

/-
## Automatic parameter forwarding preserves existing bindings (Q-04, decided 2026-09-28)

THE LAW: automatic parameter forwarding must not change what an existing name refers
to. `forwardingSource` (KatLang.lean) is the SPECIFICATION of the C# surface pass's one
forwarding decision (`ImplicitArgumentResolver.ForwardableParameters`; the evaluator never calls
it); these SPECIFICATION laws pin its two halves over arbitrary owner chains (C# agreement:
`AutomaticForwardingBindingTests`, `OwnershipConformanceTests`): forwarding reuses exactly
the PARAMETER binding a written occurrence of the name would denote (and nothing else:
never a property, an opened name, or a builtin), and the parameter it adds when no
binding exists changes the binding of no written name.
-/

/-- Forwarding reuses EXACTLY the parameter binding the owner walk gives a written
occurrence of the name at the referencing body — the same level, and only when that
binding is a parameter. -/
theorem forwarding_reuses_exactly_the_written_parameter_binding
    (chain : List OwnerLevel) (inferring : Bool) (name : Ident) :
    (forwardingSource chain inferring name).reusedLevel?
      = (selectOwnedDeclaration chain name).parameterLevel? := by
  unfold forwardingSource
  cases h : selectOwnedDeclaration chain name with
  | none => cases inferring <;> rfl
  | property level => cases inferring <;> rfl
  | parameter level => cases level <;> rfl

/-- A same-named PROPERTY — a property of an enclosing owner, the root, or the prelude
(a builtin) — is never forwarded as a parameter: the body gets a new forwarded
parameter when it infers its inputs, and nothing when they are closed. -/
theorem forwarding_never_supplies_a_property
    (chain : List OwnerLevel) (inferring : Bool) (name : Ident) (level : Nat)
    (h : selectOwnedDeclaration chain name = .property level) :
    forwardingSource chain inferring name
      = if inferring then .forwardedParameter else .unavailable := by
  unfold forwardingSource
  rw [h]

/-- A name the owner walk does not find at all — an opened or module-provided name, or
one nothing declares — is not forwarded from anywhere either. -/
theorem forwarding_never_supplies_an_undeclared_name
    (chain : List OwnerLevel) (inferring : Bool) (name : Ident)
    (h : selectOwnedDeclaration chain name = .none) :
    forwardingSource chain inferring name
      = if inferring then .forwardedParameter else .unavailable := by
  unfold forwardingSource
  rw [h]

/-- A new forwarded parameter is created only for a name no written parameter
occurrence at the body could denote: never one that would capture an existing
reference to an enclosing parameter. -/
theorem fresh_forwarded_parameter_only_without_a_parameter_binding
    (chain : List OwnerLevel) (inferring : Bool) (name : Ident)
    (h : forwardingSource chain inferring name = .forwardedParameter) :
    elaboratesToParameter chain name = false := by
  unfold forwardingSource at h
  unfold elaboratesToParameter
  cases hs : selectOwnedDeclaration chain name with
  | none => rfl
  | property level => rfl
  | parameter level =>
    rw [hs] at h
    cases level <;> simp at h

private theorem select_from_ignores_forwarded (i : Nat) (level : OwnerLevel) (outer : List OwnerLevel)
    (forwarded : List Ident) (m : Ident) :
    selectOwnedDeclarationFrom i ({ level with forwarded := forwarded } :: outer) m
      = selectOwnedDeclarationFrom i (level :: outer) m := by
  simp [selectOwnedDeclarationFrom]

/-- THE BINDING-PRESERVATION LAW (of the specification). Adding the parameter forwarding creates changes the
binding of NO name: every written occurrence, of that name or any other, selects
exactly what it selected before. (The superseded rule added the lifted name to the
body's name-resolution parameters instead; `CoreTests/ForwardingBindings.lean` keeps
the witness of the rebinding that caused.) -/
theorem forwarded_parameter_changes_no_written_binding
    (chain : List OwnerLevel) (name m : Ident) :
    selectOwnedDeclaration (forwardParameter chain name) m = selectOwnedDeclaration chain m := by
  cases chain with
  | nil => rfl
  | cons level outer =>
    unfold forwardParameter selectOwnedDeclaration
    exact select_from_ignores_forwarded 0 level outer _ m

/-- The declaration-validity specification (`conflictingOwnedNames`, of the C#
`ParameterPropertyCollisionValidator`) still sees a forwarded parameter: a property of the
SAME owner that shares its name is the ordinary parameter/property collision. (The nested-body
case is the same rule over the ancestor levels, pinned by the C# validator tests.) -/
theorem forwarded_parameter_still_conflicts_with_a_same_named_property (name : Ident) :
    conflictingOwnedNames { parameters := [], properties := [name], forwarded := [name] } = [name] := by
  simp [conflictingOwnedNames, OwnerLevel.signature]

/-
## Callable aliases and bare forwarding (FWD-02; binding indirection decided 2026-10-01)

A body whose ONE written row is a bare reference to a callable that declares
parameterized callable structure (`Algorithm.declaresParameterizedStructure`) is not a
formula. An OPEN body is a CALLABLE ALIAS (`Algorithm.alias`), BINDING INDIRECTION: the
alias keeps its own binding — declaration, exposure, zero-argument cache key — while every
callable use resolves to the NORMALIZED TARGET in the alias's own scope
(`resolveAliasTarget`); no wrapper and no inherited signature exist. A CLOSED body — a
written parameter list or a clause branch — is bare forwarding: each of the target's
parameters is supplied from an EXISTING compatible binding of the same name
(`bareForwardingArgument`, `bareForwardingRow`), and a target with no forwarding contract
at all is the front-end error (`bareForwardingRowOf`, narrowed Q-77).

EVIDENCE. Except for the `requiresArguments` / `resolveOpen`, `zeroArgPropertyCacheKey` and
`parameterPatterns` facts, the laws below are SPECIFICATION theorems: about the surface-pass
specification functions (`sourceArgument`, `bareForwarding*`, `forwardingSource`,
`declaresParameterizedStructure`, `liftsBareValueReference`, `liftingSignature?`,
`liftingCalleeKind?`, `liftingSlotRole`) and the static chase `staticAliasTarget?`, none of which
the evaluator calls. The evaluator's alias chase `resolveAliasTarget` is `partial`; no theorem
covers it, and `CoreTests/AliasForwarding.lean` checks it executably. The C# reconstruction
(`BuildPatternArgument`) is shared with formula lifting; in Lean `sourceArgument` is called only by
`bareForwardingArgument`. The laws pin the reconstruction (one argument per top-level
pattern, each capture as its own binding, a collector re-spread, each structural pattern
as its own kind), the bare-forwarding decision (by name, never renamed, never positional,
never added to a closed list, never reshaped from same-named leaves), its distinction from
formula lifting, the alias eligibility (declared structure, never zero-argument
acceptance), and the split between the alias's BINDING and its CALLABLE.
`CoreTests/AliasForwarding.lean` evaluates the trees: every builtin, the user shapes,
families and alias chains through an alias against the direct call.
-/

/-- A fixed capture forwards its binding as ONE argument, `x`. -/
theorem source_argument_fixed_capture_is_its_binding (x : Ident) :
    ParameterPattern.sourceArgument (.capture { name := x }) = .param x := rfl

/-- A collecting capture is rebuilt as the spread of its binding, `xs*` (that the spread then
re-supplies the collected range is supply formation, `partial`; FWD-01, NEED-07/08). -/
theorem source_argument_collector_is_respread (xs : Ident) :
    ParameterPattern.sourceArgument (.capture { name := xs, kind := .collecting })
      = .sequenceSpread (.param xs) := rfl

/-- A list pattern rebuilds a LIST of its items' arguments, at every cardinality. -/
theorem source_argument_list_pattern_rebuilds_a_list (items : List ParameterPattern) :
    ParameterPattern.sourceArgument (.listValue items)
      = .listLiteral (ParameterPattern.sourceArguments items) := rfl

/-- The rebuilt call has the source signature's arity: one argument per top-level pattern. -/
theorem source_arguments_length (patterns : List ParameterPattern) :
    (ParameterPattern.sourceArguments patterns).length = patterns.length := by
  induction patterns with
  | nil => rfl
  | cons pattern rest ih => simp [ParameterPattern.sourceArguments, ih]

/-- A VALID sequence pattern (no singleton, PAT-06) rebuilds a SEQUENCE — the empty
sequence or a capture — never a list and never a bare item: reconstruction keeps the
structural kind. -/
theorem source_argument_sequence_pattern_rebuilds_a_sequence (items : List ParameterPattern)
    (valid : ParameterPattern.isSingletonSequenceItems items = false) :
    ParameterPattern.sourceArgument (.sequenceValue items) = .emptySequence 0
      ∨ ∃ exprs, ParameterPattern.sourceArgument (.sequenceValue items) = .capture exprs := by
  match items, valid with
  | [], _ => exact Or.inl rfl
  | [.capture parameter], valid =>
    cases h : parameter.kind with
    | normal => simp [ParameterPattern.isSingletonSequenceItems, h] at valid
    | collecting =>
      exact Or.inr ⟨[.sequenceSpread (.param parameter.name)], by
        simp [ParameterPattern.sourceArgument, ParameterPattern.sourceArguments, sequenceArgument, h]⟩
  | [.sequenceValue _], valid => simp [ParameterPattern.isSingletonSequenceItems] at valid
  | [.listValue _], valid => simp [ParameterPattern.isSingletonSequenceItems] at valid
  | [.unpacking _], valid => simp [ParameterPattern.isSingletonSequenceItems] at valid
  | first :: second :: rest, _ =>
    exact Or.inr ⟨ParameterPattern.sourceArgument first :: ParameterPattern.sourceArgument second
        :: ParameterPattern.sourceArguments rest,
      by simp [ParameterPattern.sourceArgument, ParameterPattern.sourceArguments, sequenceArgument]⟩

/-! ### Bare forwarding (FWD-02, decided 2026-09-30) -/

@[simp] private theorem parameter_kind_normal_beq_normal :
    (ParameterKind.normal == ParameterKind.normal) = true := by decide
@[simp] private theorem parameter_kind_normal_beq_collecting :
    (ParameterKind.normal == ParameterKind.collecting) = false := by decide
@[simp] private theorem parameter_kind_collecting_beq_collecting :
    (ParameterKind.collecting == ParameterKind.collecting) = true := by decide

/-- Same-name forwarding: `F(p) = p * 2` / `A(p) = F` forwards A's `p` to F's `p`. -/
theorem bare_forwarding_same_name_is_supplied (p : Ident) :
    bareForwardingArgument [.capture { name := p }] [p] [] (.capture { name := p })
      = .supplied (.param p) := by
  simp [bareForwardingArgument, ParameterPattern.topLevelCaptureKind?, bareForwardedBinding]

/-- NO RENAMING, in general: whatever the body's own patterns, enclosing bindings and names, a
callee capture `n` that bare forwarding supplies is supplied by a binding of the SAME name —
`n` itself or its re-spread `n*` — never by a differently named binding. -/
theorem bare_forwarding_never_renames (own : List ParameterPattern) (ownNames : List Ident)
    (captured : List CallableParameter) (parameter : CallableParameter) (argument : Expr)
    (h : bareForwardingArgument own ownNames captured (.capture parameter) = .supplied argument) :
    argument = .param parameter.name ∨ argument = .sequenceSpread (.param parameter.name) := by
  have hb : ∀ kind, bareForwardedBinding parameter kind = .param parameter.name
      ∨ bareForwardedBinding parameter kind = .sequenceSpread (.param parameter.name) := by
    intro kind
    unfold bareForwardedBinding
    split <;> simp
  simp only [bareForwardingArgument] at h
  split at h
  · cases h; exact hb _
  · split at h
    · cases h
    · split at h
      · cases h; exact hb _
      · split at h <;> cases h

/-- Example: `F(q) = q * 2` / `A(p) = F` is rejected — A's `p` never becomes F's `q`. -/
theorem bare_forwarding_rejects_a_differently_named_fixed_parameter (p q : Ident) (distinct : p ≠ q) :
    bareForwardingArgument [.capture { name := p }] [p] [] (.capture { name := q }) = .unforwardable := by
  simp [bareForwardingArgument, ParameterPattern.topLevelCaptureKind?, distinct, Ne.symm distinct]

/-- A fixed callee capture that neither the body's own top-level patterns, nor its names,
nor an enclosing binding supply is unforwardable. -/
theorem bare_forwarding_unbound_fixed_capture_is_unforwardable (own : List ParameterPattern)
    (ownNames : List Ident) (captured : List CallableParameter) (name : Ident)
    (hnone : ParameterPattern.topLevelCaptureKind? name own = none)
    (hfree : ownNames.contains name = false)
    (huncaptured : captured.find? (fun binding => binding.name == name) = none) :
    bareForwardingArgument own ownNames captured (.capture { name := name }) = .unforwardable := by
  have hmem : name ∉ ownNames := by simpa using hfree
  simp [bareForwardingArgument, hnone, hmem, huncaptured]

/-- ONE unforwardable callee parameter rejects the whole signature: bare forwarding never
drops, skips or invents a parameter. -/
theorem bare_forwarding_rejects_a_signature_with_an_unforwardable_parameter
    (own : List ParameterPattern) (ownNames : List Ident) (captured : List CallableParameter)
    (signature : List ParameterPattern) (parameter : ParameterPattern) (hin : parameter ∈ signature)
    (hbad : bareForwardingArgument own ownNames captured parameter = .unforwardable) :
    bareForwardingArguments own ownNames captured signature = none := by
  induction signature with
  | nil => cases hin
  | cons first rest ih =>
      cases List.mem_cons.mp hin with
      | inl heq =>
          subst heq
          simp [bareForwardingArguments, hbad]
      | inr hrest =>
          have := ih hrest
          simp only [bareForwardingArguments, this]
          cases bareForwardingArgument own ownNames captured first <;> rfl

/-- A CLOSED LIST NEVER GAINS A PARAMETER: `F(p, q) = p + q` / `A(p) = F` is rejected,
never an inferred `q` — the instance of the two general laws above. -/
theorem bare_forwarding_never_adds_a_parameter (p q : Ident) (distinct : p ≠ q) :
    bareForwardingArguments [.capture { name := p }] [p] []
      [.capture { name := p }, .capture { name := q }] = none :=
  bare_forwarding_rejects_a_signature_with_an_unforwardable_parameter _ _ _ _
    (.capture { name := q }) (by simp)
    (bare_forwarding_unbound_fixed_capture_is_unforwardable _ _ _ q
      (by simp [ParameterPattern.topLevelCaptureKind?, distinct])
      (by simp [Ne.symm distinct]) rfl)

/-- An UNUSED parameter stays unused: `F(p)` / `A(p, unused) = F` forwards `p` alone. -/
theorem bare_forwarding_ignores_an_unused_parameter (p unused : Ident) :
    bareForwardingArguments [.capture { name := p }, .capture { name := unused }] [p, unused] []
      [.capture { name := p }] = some [.param p] := by
  simp [bareForwardingArguments, bareForwardingArgument, ParameterPattern.topLevelCaptureKind?,
    bareForwardedBinding]

/-- NOT POSITIONAL: `F(y, x) = y - x` / `G(x, y) = F` supplies F's `y` from G's `y` and F's
`x` from G's `x` — `F(y, x)`, never G's order. -/
theorem bare_forwarding_is_not_positional (x y : Ident) (distinct : x ≠ y) :
    bareForwardingArguments [.capture { name := x }, .capture { name := y }] [x, y] []
      [.capture { name := y }, .capture { name := x }] = some [.param y, .param x] := by
  simp [bareForwardingArguments, bareForwardingArgument, ParameterPattern.topLevelCaptureKind?,
    bareForwardedBinding, distinct]

/-- STRUCTURAL COMPATIBILITY IS WHOLE-PATTERN, in general: a structural callee parameter (any
non-capture pattern) that no own top-level pattern of the SAME contract supplies is
unforwardable — never assembled from same-named leaves, never from enclosing bindings. The four
named instances below are its examples. -/
theorem bare_forwarding_structural_parameter_needs_a_same_contract_own_pattern
    (own : List ParameterPattern) (ownNames : List Ident) (captured : List CallableParameter)
    (pattern : ParameterPattern) (hnot : ∀ parameter, pattern ≠ .capture parameter)
    (hno : own.any (ParameterPattern.sameContract pattern) = false) :
    bareForwardingArgument own ownNames captured pattern = .unforwardable := by
  cases pattern with
  | capture parameter => exact absurd rfl (hnot parameter)
  | sequenceValue items => simp [bareForwardingArgument, hno]
  | listValue items => simp [bareForwardingArgument, hno]
  | unpacking items => simp [bareForwardingArgument, hno]

/-- Instance: `Single([x])` / `G(x) = Single` is rejected — G's whole `x` never builds
Single's `[x]` because the leaf names coincide. -/
theorem bare_forwarding_never_reshapes_a_leaf (x : Ident) :
    bareForwardingArgument [.capture { name := x }] [x] [] (.listValue [.capture { name := x }])
      = .unforwardable := by
  simp [bareForwardingArgument, ParameterPattern.sameContract]

/-- ... and the same pattern forwards: `G([x]) = Single` is `Single([x])`. -/
theorem bare_forwarding_same_pattern_is_supplied (x : Ident) :
    bareForwardingArgument [.listValue [.capture { name := x }]] [x] []
      (.listValue [.capture { name := x }])
      = .supplied (.listLiteral [.param x]) := by
  simp [bareForwardingArgument, ParameterPattern.sameContract, ParameterPattern.sameContracts,
    ParameterPattern.sourceArgument, ParameterPattern.sourceArguments]

/-- Instance: the same leaf names in another shape are another contract — `F((x, y))` /
`G(x, y) = F` is rejected, the pair never manufactured. -/
theorem bare_forwarding_never_manufactures_a_sequence (x y : Ident) :
    bareForwardingArgument [.capture { name := x }, .capture { name := y }] [x, y] []
      (.sequenceValue [.capture { name := x }, .capture { name := y }]) = .unforwardable := by
  simp [bareForwardingArgument, ParameterPattern.sameContract]

/-- A WHOLE VALUE NEEDS A TOP-LEVEL BINDING, in general: a callee capture whose name the body
binds only INSIDE one of its patterns (no own top-level capture of that name) is unforwardable —
that inner name is an element, not a whole-value parameter, and no enclosing binding of the
name is consulted. -/
theorem bare_forwarding_whole_value_needs_a_top_level_binding (own : List ParameterPattern)
    (ownNames : List Ident) (captured : List CallableParameter) (parameter : CallableParameter)
    (hnone : ParameterPattern.topLevelCaptureKind? parameter.name own = none)
    (hbound : ownNames.contains parameter.name = true) :
    bareForwardingArgument own ownNames captured (.capture parameter) = .unforwardable := by
  have hmem : parameter.name ∈ ownNames := by simpa using hbound
  simp [bareForwardingArgument, hnone, hmem]

/-- Example: `F(x)` / `G([x]) = F` is rejected — the `x` inside G's list pattern is an
element, not G's parameter. -/
example (x : Ident) :
    bareForwardingArgument [.listValue [.capture { name := x }]] [x] [] (.capture { name := x })
      = .unforwardable :=
  bare_forwarding_whole_value_needs_a_top_level_binding _ _ _ _
    (by simp [ParameterPattern.topLevelCaptureKind?]) (by simp)

/-- Instance: positions inside a structural pattern are never renamed either — `F([a, b])` /
`A([x, y]) = F` is rejected. -/
theorem bare_forwarding_never_renames_inside_a_pattern (a b x y : Ident) (distinct : a ≠ x) :
    bareForwardingArgument [.listValue [.capture { name := x }, .capture { name := y }]] [x, y] []
      (.listValue [.capture { name := a }, .capture { name := b }]) = .unforwardable := by
  simp [bareForwardingArgument, ParameterPattern.sameContract, ParameterPattern.sameContracts, distinct]

/-- A collecting source re-spreads into a collecting destination of the same name
(`spread (collect S) = S`, FWD-01). -/
theorem bare_forwarding_collector_respreads (xs : Ident) :
    bareForwardingArgument [.capture { name := xs, kind := .collecting }] [xs] []
      (.capture { name := xs, kind := .collecting }) = .supplied (.sequenceSpread (.param xs)) := by
  simp [bareForwardingArgument, ParameterPattern.topLevelCaptureKind?, bareForwardedBinding]

/-- MIXED KINDS NEVER SPREAD: a re-spread needs BOTH a collecting source and a collecting
destination (`bareForwardedBinding`), so a fixed binding reaches a collector as one item and a
collected list reaches a fixed parameter whole — the source binding's kind alone does not
decide a spread. -/
theorem bare_forwarding_mixed_kind_pairs_pass_the_binding_whole (xs : Ident) :
    bareForwardingArgument [.capture { name := xs }] [xs] []
        (.capture { name := xs, kind := .collecting }) = .supplied (.param xs)
      ∧ bareForwardingArgument [.capture { name := xs, kind := .collecting }] [xs] []
        (.capture { name := xs }) = .supplied (.param xs) := by
  constructor <;> simp [bareForwardingArgument, ParameterPattern.topLevelCaptureKind?, bareForwardedBinding]

/-- A collector nothing of its name supplies receives no argument, and a callee that then
receives nothing elaborates to its bare name `.resolve callee`, never an invented call (how the
evaluator reads that row — Q-03's cached zero-argument demand — is not proved here). -/
theorem bare_forwarding_unsupplied_collector_is_read (callee p xs : Ident) (distinct : p ≠ xs) :
    bareForwardingRow callee [.capture { name := p }] [p] []
      [.capture { name := xs, kind := .collecting }] = some (.resolve callee) := by
  simp [bareForwardingRow, bareForwardingArguments, bareForwardingArgument,
    ParameterPattern.topLevelCaptureKind?, distinct, Ne.symm distinct]

/-- Q-04: a name the closed body does not bind is the ENCLOSING parameter binding a written
name would denote there, reused as it is (`Outer(x) = { Local(y) = F … }` forwards Outer's
`x`) ... -/
theorem bare_forwarding_reuses_an_enclosing_binding (x y : Ident) (distinct : y ≠ x) :
    bareForwardingArgument [.capture { name := y }] [y] [{ name := x }] (.capture { name := x })
      = .supplied (.param x) := by
  simp [bareForwardingArgument, ParameterPattern.topLevelCaptureKind?, bareForwardedBinding,
    distinct, Ne.symm distinct]

/-- ... but the body's OWN binding is nearer, in general: a callee capture the body binds at
its own top level is supplied from that binding, whatever enclosing bindings exist. -/
theorem bare_forwarding_own_binding_beats_an_enclosing_one (own : List ParameterPattern)
    (ownNames : List Ident) (captured : List CallableParameter) (parameter : CallableParameter)
    (kind : ParameterKind) (hown : ParameterPattern.topLevelCaptureKind? parameter.name own = some kind) :
    bareForwardingArgument own ownNames captured (.capture parameter)
      = .supplied (bareForwardedBinding parameter kind) := by
  simp [bareForwardingArgument, hown]

/-- Example: an own fixed `x` beats an enclosing collecting `x`, so nothing is re-spread. -/
example (x : Ident) :
    bareForwardingArgument [.capture { name := x }] [x] [{ name := x, kind := .collecting }]
      (.capture { name := x, kind := .collecting }) = .supplied (.param x) := by
  rw [bare_forwarding_own_binding_beats_an_enclosing_one _ _ _ _ .normal
    (by simp [ParameterPattern.topLevelCaptureKind?])]
  simp [bareForwardedBinding]

/-- Instance: an enclosing binding is a plain named value — it never supplies a structural
parameter. -/
theorem bare_forwarding_enclosing_binding_supplies_no_pattern (x : Ident) :
    bareForwardingArgument [] [] [{ name := x }] (.listValue [.capture { name := x }]) = .unforwardable := by
  simp [bareForwardingArgument]

/-- REPEATED NAMES follow the by-name rule: `P(x, x) = x` / `Q(x) = P` hands Q's ONE binding
`x` to both occurrences, `P(x, x)`. (Design context, not proved here: the two slots are then
ordinary independent arguments that happen to read one binding, which the Model-C binder's
repeated-name check compares, Q-05.) -/
theorem bare_forwarding_repeated_name_reuses_one_binding (x : Ident) :
    bareForwardingArguments [.capture { name := x }] [x] []
      [.capture { name := x }, .capture { name := x }] = some [.param x, .param x] := by
  simp [bareForwardingArguments, bareForwardingArgument, ParameterPattern.topLevelCaptureKind?,
    bareForwardedBinding]

/-- FORMULA LIFTING IS A DIFFERENT MECHANISM: the name bare forwarding refuses to add to a
closed list (`bare_forwarding_rejects_a_differently_named_fixed_parameter`) is exactly the one
`forwardingSource` gives an OPEN inferring level as a new forwarded parameter
(`.forwardedParameter`: `F(q)` / `A = F + 1` gives `A(q)`), while a closed level gets nothing
either (`.unavailable`; Q-15 / PAR-04: the reference stays F's zero-argument demand, a runtime
fact not proved here). -/
theorem formula_lifting_infers_what_bare_forwarding_rejects (p q : Ident) (distinct : p ≠ q) :
    forwardingSource [{ parameters := [], properties := [] }] true q = .forwardedParameter
      ∧ forwardingSource [{ parameters := [p], properties := [] }] false q = .unavailable
      ∧ bareForwardingArgument [.capture { name := p }] [p] [] (.capture { name := q })
        = .unforwardable := by
  refine ⟨?_, ?_, bare_forwarding_rejects_a_differently_named_fixed_parameter p q distinct⟩
  · simp [forwardingSource, selectOwnedDeclaration, selectOwnedDeclarationFrom]
  · simp [forwardingSource, selectOwnedDeclaration, selectOwnedDeclarationFrom, Ne.symm distinct]

/-! ### Callable aliases: binding indirection (decided 2026-10-01) -/

/-- ELIGIBILITY IS DECLARED STRUCTURE: a user callable is an alias target exactly when it
declares a parameter pattern — never decided by zero-argument acceptance. -/
theorem user_alias_target_iff_declares_parameters (p : Option ScopeCtx) (ps : List ParameterPattern)
    (op : List Expr) (pr : List PropDef) (out : List Expr) (id : Option PropertyIdentity) :
    (Algorithm.mk p ps op pr out id).declaresParameterizedStructure = true ↔ ps ≠ [] := by
  cases ps <;> simp [Algorithm.declaresParameterizedStructure]

/-- A ZERO-PARAMETER user algorithm is not an alias target (the `ps = []` corollary of
`user_alias_target_iff_declares_parameters`): `A = Z` stays an ordinary property whose body
reads `Z`. (That it is then cached like any property is evaluator behaviour, guard-checked in
`CoreTests/AliasForwarding.lean`.) -/
theorem zero_parameter_user_algorithm_is_not_an_alias_target (p : Option ScopeCtx) (op : List Expr) (pr : List PropDef)
    (out : List Expr) (id : Option PropertyIdentity) :
    (Algorithm.mk p [] op pr out id).declaresParameterizedStructure = false := rfl

/-- `Only(*xs)` works with no arguments, so the specification never LIFTS a bare reference to
it (Q-03) — but it IS an alias target: the alias rule reads declared structure. -/
theorem collecting_only_callee_is_aliased_not_lifted (xs : Ident) (p : Option ScopeCtx) (op : List Expr)
    (pr : List PropDef) (out : List Expr) (id : Option PropertyIdentity) :
    (Algorithm.mk p [.capture { name := xs, kind := .collecting }] op pr out id).declaresParameterizedStructure = true
      ∧ liftsBareValueReference [.capture { name := xs, kind := .collecting }] = false :=
  ⟨rfl, rfl⟩

/-- Every user signature that lifts is one that aliases: requiring a supplied argument means
declaring a parameter. -/
theorem lifting_signature_is_an_alias_signature (p : Option ScopeCtx) (ps : List ParameterPattern)
    (op : List Expr) (pr : List PropDef) (out : List Expr) (id : Option PropertyIdentity)
    (lifts : liftsBareValueReference ps = true) :
    (Algorithm.mk p ps op pr out id).declaresParameterizedStructure = true := by
  cases ps with
  | nil => exact absurd lifts (by decide)
  | cons pattern rest => rfl

/-- EVERY BUILTIN is an alias target — `if`, the callback builtins and the loops included.
(Design consequence, guard-checked in `CoreTests/AliasForwarding.lean`: the builtin's callable is
used directly, so `I = if` keeps `if`'s laziness and `R = repeat` its minimum arity.) -/
theorem every_builtin_is_an_alias_target (b : Builtin) :
    (Algorithm.builtin b).declaresParameterizedStructure = true := rfl

/-- EVERY CLAUSE FAMILY is an alias target, and so is every alias (a chain normalizes). -/
theorem every_family_and_alias_is_an_alias_target (p : Option ScopeCtx) (op : List Expr)
    (bs : List CondBranch) (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity) :
    (Algorithm.conditional p op bs id).declaresParameterizedStructure = true
      ∧ (Algorithm.alias p op pr target id).declaresParameterizedStructure = true :=
  ⟨rfl, rfl⟩

private def aliasLawBranch (pattern : Pattern) : CondBranch := { pattern := pattern, body := alg [] [] [] [num 0] }

/-- The unnameable family `S(1) = 1` / `S(-1) = -1`: its clauses name no position. -/
private def aliasLawSign : Algorithm :=
  .conditional none [] [aliasLawBranch (.litInt 1), aliasLawBranch (.litInt (-1))]

/-- AN UNNAMEABLE FAMILY CAN BE ALIASED: aliasing needs callable identity, not parameter names,
so `SA = S` is an alias although `S` has no lifting signature (and no forwarding contract). -/
theorem unnameable_family_can_be_aliased :
    aliasLawSign.declaresParameterizedStructure = true ∧ aliasLawSign.liftingSignature? = none :=
  ⟨rfl, rfl⟩

/-- A CALLABLE WITHOUT A FORWARDING CONTRACT CANNOT BARE-FORWARD (narrowed Q-77, decided
2026-10-01), in general: whatever the closed body, a normalized target with no lifting
signature is the front-end error `noForwardingContract` — never a silent zero-argument demand. -/
theorem bare_forwarding_target_without_lifting_signature_has_no_forwarding_contract
    (callee : Ident) (own : List ParameterPattern) (ownNames : List Ident)
    (captured : List CallableParameter) (target : Algorithm) (h : target.liftingSignature? = none) :
    bareForwardingRowOf callee own ownNames captured target = .error .noForwardingContract := by
  simp [bareForwardingRowOf, h]

/-- Instance: a closed lone row `W(x) = SA` whose normalized target is the unnameable family
`S` is that error. (No alias appears in the statement, which takes the already-normalized
target.) -/
theorem unnameable_family_target_cannot_bare_forward (callee x : Ident) :
    bareForwardingRowOf callee [.capture { name := x }] [x] [] aliasLawSign = .error .noForwardingContract :=
  bare_forwarding_target_without_lifting_signature_has_no_forwarding_contract _ _ _ _ _ rfl

/-- ... while a target WITH a contract forwards by its own names. Example with the normalized
target `count` (whatever route reached it): `C = count` / `W(collection) = C` is
`W(collection) = C(collection)`, the call `count` itself would receive. -/
theorem count_target_bare_forwards_by_its_collection_name (callee : Ident) :
    bareForwardingRowOf callee [.capture { name := "collection" }] ["collection"] []
        (Algorithm.builtin .countBuiltin)
      = .ok (.call (.resolve callee) [.param "collection"]) := by
  rfl

/-- An alias has NO lifting signature, NO callee kind and NO parameter patterns of its OWN, so in
these specification functions every callable question — lifting, forwarding, the roles of a
call's arguments — must be asked of its normalized target (that callers do so is the source of
the surface pass and of the `partial` `resolveAliasTarget`). -/
theorem alias_has_no_callable_surface_of_its_own (p : Option ScopeCtx) (op : List Expr)
    (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity) :
    (Algorithm.alias p op pr target id).liftingSignature? = none
      ∧ (Algorithm.alias p op pr target id).liftingCalleeKind? = none
      ∧ (Algorithm.alias p op pr target id).parameterPatterns = [] :=
  ⟨rfl, rfl, rfl⟩

/-- WRITTEN `open A` NEVER TURNS A CALLABLE ALIAS INTO A NAMESPACE: whatever its target, when
the open target resolves to an alias, the production `resolveOpen` refuses it with
`illegalInOpen` (its gate reads `Algorithm.requiresArguments`, `true` for every alias), leaving
the state the resolution reached. (Strengthened from the `requiresArguments` fact alone,
R8/X-13; the resolution `resolveAlgForOpen` itself is `partial`.) -/
theorem alias_is_never_an_open_provider (e : Expr) (ctx : EvalCtx) (p : Option ScopeCtx)
    (op : List Expr) (pr : List PropDef) (target : Expr) (id : Option PropertyIdentity)
    (state state' : EvalState)
    (h : (resolveAlgForOpen e ctx).runState state = (.ok (.alias p op pr target id), state')) :
    (resolveOpen e ctx).runState state
      = (.error (Error.illegalInOpen
          (openTargetRequiresArgumentsMessage (openExprName e) (.alias p op pr target id))), state') := by
  show ((resolveAlgForOpen e ctx).runState >>= fun a => _) state = _
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind]
  rw [h]
  rfl

/-- THE CACHE KEY CARRIES THE BINDING'S NAME: `zeroArgPropertyCacheKey` reads the BINDING —
never the callable it resolves to — so two differently named bindings (an alias `A` and its
target) get different keys. (That a bare read of an alias then evaluates its target's zero-supply
demand under `A`'s entry is evaluator behaviour, guard-checked.) -/
theorem zero_arg_cache_key_carries_the_binding_name (k : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (alias target : PropDef) (ctx : EvalCtx) (env : ValEnv) (distinct : alias.name ≠ target.name) :
    (zeroArgPropertyCacheKey k owner alias ctx env).propertyName = alias.name
      ∧ zeroArgPropertyCacheKey k owner alias ctx env ≠ zeroArgPropertyCacheKey k owner target ctx env :=
  ⟨rfl, fun same => distinct (congrArg ZeroArgPropertyCacheKey.propertyName same)⟩

/-- `F(x) = x`, `A = F`, `B = A`, `C = B` and the family `Fam(0) = 0` / `Fam(n) = n` with its alias
`AF = Fam`: the static chains the next two EXAMPLES normalize. -/
private def aliasLawRoot : Algorithm :=
  algPrivate [] []
    [ ("F", alg ["x"] [] [] [param "x"])
    , ("A", .alias none [] [] (.resolve "F")), ("B", .alias none [] [] (.resolve "A"))
    , ("C", .alias none [] [] (.resolve "B"))
    , ("Fam", .conditional none [] [aliasLawBranch (.litInt 0), aliasLawBranch (.bind "n")])
    , ("AF", .alias none [] [] (.resolve "Fam")) ]
    []

/-- EXAMPLE over the STATIC chase `staticAliasTarget?` (not the evaluator's `partial`
`resolveAliasTarget`): the chain `C -> B -> A -> F` reaches the one callable `F` — its single
parameter `x` — without copying a signature into any link. -/
theorem static_alias_chain_example_reaches_its_target :
    ((staticAliasTarget? 3 [aliasLawRoot] (.alias none [] [] (.resolve "B"))).map
        fun target => target.parameterPatterns.length) = some 1
      ∧ (staticAliasTarget? 3 [aliasLawRoot] (.alias none [] [] (.resolve "B"))).isSome := by
  decide

/-- EXAMPLE over the static chase: the role read off the normalized target of `AF = Fam` is the
family's (position 0 a value slot) and that of `A = F` the user callable's (neutral) — an alias
has no kind of its own (`alias_has_no_callable_surface_of_its_own`). -/
theorem static_alias_target_roles_example :
    ((staticAliasTarget? 3 [aliasLawRoot] (.alias none [] [] (.resolve "Fam"))).bind
        Algorithm.liftingCalleeKind?).map (fun kind => liftingSlotRole kind 0 true) = some .value
      ∧ ((staticAliasTarget? 3 [aliasLawRoot] (.alias none [] [] (.resolve "F"))).bind
        Algorithm.liftingCalleeKind?).map (fun kind => liftingSlotRole kind 0 true) = some .callable := by
  decide

/-
## Deconstruction (unpacking receiver)

Assignment deconstruction (`x, *y, z = RHS`) is parser-elaborated into a helper
whose single parameter is the UNPACKING RECEIVER (`.unpacking [captures]`) applied
to the right-hand side value as one argument. That pattern OPENS its single received value
one level (`Result.spreadItems`: a sequence or a list opens, any other value is one item) and
matches the items element-by-element — so `x, y, z = A` unpacks a stored sequence or list value
`A`. This opening is deconstruction-specific: the written structural patterns open only their
own kind. In production the unpacking level is `bindNeedOne`'s `.unpack` arm, whose nested level
is `bindNeedLevel` itself (`nested_unpack_level_is_bind_need_level`), after the right-hand side's
VALUE demand; a flat call pattern binds whole supply cells
(`call_binder_rejects_unaccepted_supply_before_any_effect`,
`need_level_sources_around_the_collector`). The receiver is not a written structural pattern —
it has no delimiter to select a kind — so it opens both kinds alike; the end-to-end contrast
(deconstruction opens a lone value, a call keeps it whole) concerns the `partial` evaluator and is
guard-checked (CoreTests `ListValues`, `ExplicitValueOpening`). These theorems live with the
production binder laws; this section only states the rule.
-/

/-
## List bridge laws (exact list values)

Exact list values (`Result.listValue`) join the deconstruction opening rule but
remain opaque at ordinary value and call boundaries: `Result.toItems` keeps a
list as one item, while the spread marker (`Result.spreadItems`, which
assignment deconstruction opens its right-hand side with), the LIST pattern
(`Result.listPatternItems?` — never the sequence pattern), the selection
RECEIVER position view (`Result.projectionItems` — the selected element itself is
never opened), and the post-binding builtin collection view open one list
boundary in their documented contexts. The laws below pin
each decision for these total views, mirroring the sequence laws above.
-/

/-- Spread opens exactly one list boundary: `[1, 2, 3]*` supplies the items. -/
theorem spreadItems_listValue (xs : List Result) :
    (Result.listValue xs).spreadItems = xs := rfl

/-- Spreading the empty list supplies zero items (`[]*` is neutral). -/
theorem spreadItems_empty_list : (Result.listValue []).spreadItems = [] := rfl

/-- Spread on sequence values is unchanged by the list extension. -/
theorem spreadItems_sequenceValue (xs : List Result) :
    (Result.sequenceValue xs).spreadItems = xs := rfl

/-- The non-spread item view keeps a list OPAQUE: a list is one item (the boundary helper
`countedTopLevelValues` falls back to this view; Model-C call binding binds whole supply cells
and never consults it). (Postfix selection opens its
RECEIVER's positions through `projectionItems` and the post-binding builtin
collection view opens the bound list through `builtinCollectionItems`, not
through `toItems` — see `projectionItems_listValue` and
`builtinCollectionItems_list` below.) -/
theorem toItems_listValue_opaque (xs : List Result) :
    (Result.listValue xs).toItems = [Result.listValue xs] := rfl

/-- The selection receiver position view offers a list receiver's immediate
elements as positions, exactly like a sequence target. -/
theorem projectionItems_listValue (xs : List Result) :
    (Result.listValue xs).projectionItems = xs := rfl

/-- Positions of sequence targets are unchanged by the list extension. -/
theorem projectionItems_sequenceValue (xs : List Result) :
    (Result.sequenceValue xs).projectionItems = xs := rfl

/-- The empty list has no selectable positions (`[][0]` is out of range). -/
theorem projectionItems_empty_list :
    (Result.listValue []).projectionItems = [] := rfl

/-- Scalar targets are unchanged: an atom offers itself as the single
position, so `7[0]` stays `7`. -/
theorem projectionItems_atom (n : Int) :
    (Result.atom n).projectionItems = [Result.atom n] := rfl

/-- Selection selects one immediate list element and returns it exactly as stored:
`[1, 2, 3][0]` is `1`. -/
theorem select_list_first :
    Result.select? (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) 0
      = some (Result.atom 1) := by
  simp [Result.select?, Result.projectionItems]

/-- `[1, 2, 3][2]` selects the upper-bound element. -/
theorem select_list_last :
    Result.select? (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) 2
      = some (Result.atom 3) := by
  simp [Result.select?, Result.projectionItems]

/-- A selected LIST element stays one exact opaque list:
`[[1, 2], [3, 4]][0]` is `[1, 2]`, never flattened or reopened. -/
theorem select_nested_list_element_stays_list :
    Result.select?
      (Result.listValue
        [Result.listValue [Result.atom 1, Result.atom 2],
         Result.listValue [Result.atom 3, Result.atom 4]]) 0
      = some (Result.listValue [Result.atom 1, Result.atom 2]) := by
  simp [Result.select?, Result.projectionItems]

/-- Chained selection peels one boundary per bracket:
`[[1, 2], [3, 4]][1][0]` is `3`. -/
theorem select_list_chained :
    (Result.select?
      (Result.listValue
        [Result.listValue [Result.atom 1, Result.atom 2],
         Result.listValue [Result.atom 3, Result.atom 4]]) 1).bind
      (fun selected => Result.select? selected 0)
      = some (Result.atom 3) := by
  simp [Result.select?, Result.projectionItems]

/-- A selected SEQUENCE element inside a list is returned exactly as stored —
ONE intact sequence value, never its members — exactly like selecting it from
a sequence target. -/
theorem select_sequence_element_in_list_stays_sequence :
    Result.select?
      (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]]) 0
      = some (Result.sequenceValue [Result.atom 1, Result.atom 2]) := by
  simp [Result.select?, Result.projectionItems]

/-- Out-of-range list selection is a miss (`[][0]` and `[1, 2][2]` are the
existing index out-of-range error). -/
theorem select_empty_list_out_of_range :
    Result.select? (Result.listValue []) 0 = none := by
  simp [Result.select?, Result.projectionItems]

theorem select_list_past_end_out_of_range :
    Result.select? (Result.listValue [Result.atom 1, Result.atom 2]) 2 = none := by
  simp [Result.select?, Result.projectionItems]

/-
## Selection laws (selection is a value boundary)

SELECTION CHOOSES A VALUE; SPREAD OPENS A VALUE (September 2026). `A[i]`,
`first(A)`, and `last(A)` return the selected element exactly as stored and
re-count it through the ONE ordinary value boundary (`Result.valueCount`):
a selected sequence value or exact list is one emitted value, a selected `()`
emits zero values, and the selected value's origin is forgotten. No selection
form opens what it selects — only the spread marker (`Result.spreadItems`)
does, exactly one boundary. Higher-order callback items are selected values
under the same rule (`countedSequenceCallbackItem`).

EVIDENCE. These laws are about the TOTAL helpers `Result.select?`, `Result.projectionItems`,
`Result.valueCount`, `Result.spreadItems`, `reCountValueBoundary`, `evalFirstCounted` /
`evalLastCounted`, `countedSequenceCallbackItem` and `projectInvokingSlot`, and — in § Variadic
postfix selection below — the selection core `selectPosition` / `selectWith` / `selectionResult`.
The `.index` arm of `evalCounted`, the `first`/`last` builtin dispatch (with its empty policy,
`applySequenceBuiltinEmptyPolicy`) and the callback dispatch are `partial`; that they apply these
helpers is a source fact pinned by CoreTests `SelectionValueBoundary` / `VariadicSelection`.
-/

/-- `select?` never rebuilds, normalizes, or opens the selected element: it
IS the stored element at that position of the target's position view. -/
theorem select_is_stored_element (r : Result) (i : Nat) :
    Result.select? r i = r.projectionItems[i]? := rfl

/-- A selected sequence element from a sequence target is the stored
sequence value itself (never its members). -/
theorem select_sequence_element_stays_sequence (xs ys : List Result) :
    Result.select? (Result.sequenceValue (Result.sequenceValue xs :: ys)) 0
      = some (Result.sequenceValue xs) := by
  simp [Result.select?, Result.projectionItems, Result.toItems]

/-- A `()` element selected by `select?` is the empty sequence value itself, whose
`Result.valueCount` is ZERO. -/
theorem select_empty_element_recounts_to_zero (ys : List Result) :
    (Result.select? (Result.sequenceValue (Result.sequenceValue [] :: ys)) 0).map
        Result.valueCount
      = some 0 := by
  simp [Result.select?, Result.projectionItems, Result.toItems, Result.valueCount]

/-- A selected `[]` element is ONE exact list value at the value boundary:
the empty list and the empty sequence value are deliberately distinct. -/
theorem select_empty_list_element_recounts_to_one (ys : List Result) :
    (Result.select? (Result.sequenceValue (Result.listValue [] :: ys)) 0).map
        Result.valueCount
      = some 1 := by
  simp [Result.select?, Result.projectionItems, Result.toItems, Result.valueCount]

/-- The helper `evalFirstCounted` on a non-empty view `x :: xs` yields `(x, valueCount x)`, and
`select?` at position 0 of that view is `x`: two facts about total helpers sharing `x`. (The
relation of `first` to the selection core itself is `first_is_selection_at_zero`; this theorem
is subsumed by `first_is_select_zero_total`.) -/
theorem first_is_select_zero (x : Result) (xs : List Result) (s : EvalState) :
    (evalFirstCounted (x :: xs)).run s
      = (Except.ok ((x, Result.valueCount x), s) : Except Error (CountedResult × EvalState))
    ∧ Result.select? (Result.sequenceValue (x :: xs)) 0 = some x := by
  constructor
  · rfl
  · simp [Result.select?, Result.projectionItems, Result.toItems]

/-- The helper `evalLastCounted` on a non-empty view `xs ++ [x]` yields `(x, valueCount x)`, and
`select?` at the last position of that view is `x` (subsumed by `last_is_select_last_total`; the
relation to the selection core is `last_is_selection_at_count_minus_one`). -/
theorem last_is_select_last (x : Result) (xs : List Result) (s : EvalState) :
    (evalLastCounted (xs ++ [x])).run s
      = (Except.ok ((x, Result.valueCount x), s) : Except Error (CountedResult × EvalState))
    ∧ Result.select? (Result.sequenceValue (xs ++ [x])) xs.length = some x := by
  constructor
  · simp only [evalLastCounted, List.getLast?_concat]
    rfl
  · simp [Result.select?, Result.projectionItems, Result.toItems]

/-- `first` and `last` ARE selections (SEQ-04): the helpers' empty arms report the selection's
own missing position, `badIndex` — the outcome of `()[0]` — never a count of their own (Q-27,
decided 2026-10-05). In production the `first`/`last` builtins reach this through their empty
policy first (`applySequenceBuiltinEmptyPolicy` reports `badIndex` with a "selects from an empty
collection" context before the helper runs; a source fact pinned by CoreTests `ErrorTaxonomy`). -/
theorem first_empty_is_badIndex (s : EvalState) :
    (evalFirstCounted []).run s = (Except.error Error.badIndex : Except Error (CountedResult × EvalState)) := rfl

/-- The `last` twin of `first_empty_is_badIndex`. -/
theorem last_empty_is_badIndex (s : EvalState) :
    (evalLastCounted []).run s = (Except.error Error.badIndex : Except Error (CountedResult × EvalState)) := rfl

/-- SEQ-04 made TOTAL (Q-27, decided 2026-10-05), at the helper level: over EVERY collection
view, the empty one included, `evalFirstCounted` is `select?` at position 0 under the same value
boundary, or the `badIndex` that `selectPosition` reports when `select?` names no position
(`selectPosition_past_the_view_is_badIndex`). The relation to the selection core is
`first_is_selection_at_zero`. -/
theorem first_is_select_zero_total (items : List Result) (s : EvalState) :
    (evalFirstCounted items).run s
      = (match Result.select? (Result.sequenceValue items) 0 with
          | some x => Except.ok ((x, Result.valueCount x), s)
          | none => Except.error Error.badIndex
          : Except Error (CountedResult × EvalState)) := by
  cases items with
  | nil => rfl
  | cons x xs => simp [evalFirstCounted, Result.select?, Result.projectionItems, Result.toItems]; rfl

/-- `evalLastCounted` over EVERY collection view, the empty one included: `badIndex` on the empty
view (where the selection core rejects the index `-1`, `selectPosition_negative_is_badIndex`),
otherwise `select?` at the last position under the same value boundary. The relation to the
selection core is `last_is_selection_at_count_minus_one`. -/
theorem last_is_select_last_total (items : List Result) (s : EvalState) :
    (evalLastCounted items).run s
      = (if items.length = 0 then Except.error Error.badIndex
         else match Result.select? (Result.sequenceValue items) (items.length - 1) with
          | some x => Except.ok ((x, Result.valueCount x), s)
          | none => Except.error Error.badIndex
          : Except Error (CountedResult × EvalState)) := by
  cases items with
  | nil => rfl
  | cons x xs =>
      simp [evalLastCounted, Result.select?, Result.projectionItems, Result.toItems,
        List.getLast?_eq_getElem?]
      rfl

/-- The empty policy follows what a builtin IS (Q-27): the metadata gives `first` and `last`
the selection policy (their empty collection names no position, `badIndex`) and `min`, `max` and
`avg` the aggregate policy (outside the domain, `illegalInEval`). `applySequenceBuiltinEmptyPolicy`
branches on this metadata policy; the builtin only names the message. -/
theorem empty_policy_follows_what_the_builtin_is :
    (sequenceBuiltinMetadata? .firstBuiltin).map (·.emptyPolicy) = some .requireSelectablePosition
    ∧ (sequenceBuiltinMetadata? .lastBuiltin).map (·.emptyPolicy) = some .requireSelectablePosition
    ∧ (sequenceBuiltinMetadata? .minBuiltin).map (·.emptyPolicy) = some .requireAnyItem
    ∧ (sequenceBuiltinMetadata? .maxBuiltin).map (·.emptyPolicy) = some .requireAnyItem
    ∧ (sequenceBuiltinMetadata? .avgBuiltin).map (·.emptyPolicy) = some .requireAnyItem :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Q-06 (decided 2026-10-05): `projectInvokingSlot` — the projection the callback and loop-step
slots call (`expectPreparedSequenceBuiltinAlgorithmSuffixArg`, the `while`/`repeat` steps; a
source fact pinned by CoreTests `ErrorTaxonomy`) — makes an argument with no CALLABLE identity
`notAnAlgorithm` named by its role, and reads no VALUE (its input is the slot's optional
callable). -/
theorem invoking_slot_without_callable_is_notAnAlgorithm (role : String) (s : EvalState) :
    (projectInvokingSlot role none).run s
      = (Except.error (Error.notAnAlgorithm role) : Except Error (Algorithm × EvalState)) := rfl

theorem invoking_slot_with_callable_is_that_callable (role : String) (a : Algorithm) (s : EvalState) :
    (projectInvokingSlot role (some a)).run s = (Except.ok (a, s) : Except Error (Algorithm × EvalState)) := rfl

/-- Q-06's shared diagnostic vocabulary: a reducer role is distinct from the
per-invocation "reduce step" frame. Pin the concrete roles, since the generic
projection laws above intentionally accept any string and cannot detect drift. -/
theorem invoking_slot_roles_follow_the_shared_vocabulary :
    [invokingSlotRole .mapBuiltin, invokingSlotRole .filterBuiltin,
      invokingSlotRole .reduceBuiltin, invokingSlotRole .repeatBuiltin,
      invokingSlotRole .whileBuiltin] =
    ["map transform", "filter predicate", "reduce reducer", "repeat step", "while step"] := rfl

/-- The helper the callback builtins apply to each iterated item (`countedSequenceCallbackItem`)
re-counts it at the ordinary value boundary, whatever count the iteration supplied. (That the
`partial` callback dispatch applies it is a source fact.) -/
theorem callback_item_is_a_value_boundary (item : Result) (n : Nat) :
    countedSequenceCallbackItem (item, n) = (item, Result.valueCount item) := rfl

/-- Explicit spread of a selected sequence element opens exactly ONE boundary:
the immediate members, intact. -/
theorem spread_of_selected_sequence_opens_one_boundary (xs ys : List Result) :
    (Result.select? (Result.sequenceValue (Result.sequenceValue xs :: ys)) 0).map
        Result.spreadItems
      = some xs := by
  simp [Result.select?, Result.projectionItems, Result.toItems, Result.spreadItems]

/-- Explicit spread of a selected list element opens exactly ONE boundary. -/
theorem spread_of_selected_list_opens_one_boundary (xs ys : List Result) :
    (Result.select? (Result.sequenceValue (Result.listValue xs :: ys)) 0).map
        Result.spreadItems
      = some xs := by
  simp [Result.select?, Result.projectionItems, Result.toItems, Result.spreadItems]

/-!
## Variadic postfix selection (October 2026)

`receiver[s1, …, sn]` replaces the retired colon form. PARENTHESES INVOKE A
COMPUTATION; POSTFIX BRACKETS SELECT FROM A VALUE; selection never changes how its
receiver obtains that value. The `.index` arm of `evalCounted` demands the receiver
once, forms the selector supply like a call's (`NeedSupply.addresses evalCounted`), and instantiates
the TOTAL core below (`selectWith`) with `fun cell => Prod.fst <$> demandNeedRecursive cell`;
these laws are about that core
and the ONE positional view it shares with `count`, `first` and `last`. The arm
itself lives in the partial evaluator block: CoreTests `VariadicSelection` pins the
instantiation (receiver once, spreads during formation, left-to-right demand, first
failure) executably, and the C# twin pins the same traces.
-/

/-! ### One immediate positional view -/

/-- COUNTING AND SELECTION SHARE ONE IMMEDIATE POSITIONAL VIEW: the post-binding
collection view `count`, `first` and `last` read IS the positional view selection
reads, for every value. -/
theorem positional_view_is_shared (v : Result) :
    builtinCollectionItems v = Result.projectionItems v := by
  cases v <;> rfl

/-- THE ONE-LEVEL VIEWS ARE ONE FUNCTION (Q-66 "view equality", R8/X-13): the spread view
`Result.spreadItems` — what an explicit spread and the deconstruction unpacking receiver open —
IS the positional view, hence (`positional_view_is_shared`) the post-binding collection view, for
every value. (That each evaluator consumer reads its view is a source fact; the C# twins agree by
inspection and tests.) -/
theorem spread_view_is_the_positional_view (v : Result) :
    Result.spreadItems v = Result.projectionItems v := by
  cases v <;> rfl

/-- KatLang's `count` counts values, not their internal components: a string is ONE
position — the empty string included — and is never decomposed into characters,
code units, code points or graphemes. -/
theorem a_string_is_one_position (s : String) :
    Result.projectionItems (.str s) = [.str s] := rfl

theorem the_empty_string_is_one_position :
    (Result.projectionItems (.str "")).length = 1 := rfl

/-- A Boolean is one position, like a number (`projectionItems_atom`). -/
theorem a_boolean_is_one_position (b : Bool) :
    Result.projectionItems (.bool b) = [.bool b] := rfl

/-- An empty list and an empty sequence have no positions. -/
theorem empty_collections_have_no_positions :
    Result.projectionItems (.sequenceValue []) = [] ∧ Result.projectionItems (.listValue []) = [] :=
  ⟨rfl, rfl⟩

/-- Length corollary of `builtinCollectionItems_list` (whose identity proves that a list's
positions are its IMMEDIATE elements, never their components, never recursively flattened):
a list counts its elements, a list of strings its strings. -/
theorem a_list_counts_its_immediate_elements (xs : List Result) :
    (builtinCollectionItems (.listValue xs)).length = xs.length := rfl

theorem a_list_of_strings_counts_its_strings (xs : List String) :
    (builtinCollectionItems (.listValue (xs.map Result.str))).length = xs.length := by
  simp [builtinCollectionItems]

/-! ### One supplied selector (`selectPosition`) -/

/-- A supplied whole number naming a position selects the stored element, whole. -/
theorem selectPosition_selects_a_named_position (receiver : Result) (i : Int) (v : Result)
    (hi : 0 ≤ i) (h : Result.select? receiver i.toNat = some v) (s : EvalState) :
    (selectPosition receiver (.atom i)).runState s = (.ok v, s) := by
  simp [selectPosition, expectInt, Result.asInt?, Int.not_lt.mpr hi, h]
  rfl

/-- A position past the receiver's positional view is `badIndex`. -/
theorem selectPosition_past_the_view_is_badIndex (receiver : Result) (i : Int) (hi : 0 ≤ i)
    (h : Result.select? receiver i.toNat = none) (s : EvalState) :
    (selectPosition receiver (.atom i)).runState s = (.error Error.badIndex, s) := by
  simp [selectPosition, expectInt, Result.asInt?, Int.not_lt.mpr hi, h]
  rfl

/-- A negative selector names no position (`badIndex`): there is no from-the-end
selection. -/
theorem selectPosition_negative_is_badIndex (receiver : Result) (n : Int) (h : n < 0) (s : EvalState) :
    (selectPosition receiver (.atom n)).runState s = (.error Error.badIndex, s) := by
  simp [selectPosition, expectInt, Result.asInt?, h]
  rfl

/-- A selector of the wrong kind is the kind failure `typeMismatch` — never a Boolean
conversion and never an index error. -/
theorem selectPosition_string_selector_is_typeMismatch (receiver : Result) (t : String) (s : EvalState) :
    (selectPosition receiver (.str t)).runState s
      = (.error (Error.typeMismatch "Expected a number, got a string"), s) := rfl

theorem selectPosition_boolean_selector_is_typeMismatch (receiver : Result) (b : Bool) (s : EvalState) :
    (selectPosition receiver (.bool b)).runState s
      = (.error (Error.typeMismatch "Expected a number, got a Boolean value"), s) := rfl

/-- A list-valued selector is ONE value of the wrong kind: `Data[[0, 1]]` is no index
vector (only `Data[[0, 1]*]` supplies two indices). -/
theorem selectPosition_list_selector_is_typeMismatch (receiver : Result) (xs : List Result)
    (s : EvalState) :
    ∃ msg, (selectPosition receiver (.listValue xs)).runState s = (.error (Error.typeMismatch msg), s) :=
  ⟨_, rfl⟩

/-- A string selects ITSELF at position zero — `'abc'[0]` is `'abc'`, `''[0]` is `''` —
and has no position one: postfix selection never extracts characters. -/
theorem a_string_selects_itself_at_zero (t : String) (s : EvalState) :
    (selectPosition (.str t) (.atom 0)).runState s = (.ok (.str t), s) :=
  selectPosition_selects_a_named_position (.str t) 0 (.str t) (by decide) rfl s

theorem a_string_has_no_position_one (t : String) (s : EvalState) :
    (selectPosition (.str t) (.atom 1)).runState s = (.error Error.badIndex, s) :=
  selectPosition_past_the_view_is_badIndex (.str t) 1 (by decide) rfl s

/-- Every scalar selects itself at zero: `42[0]` is `42`, `true[0]` is `true`. -/
theorem a_number_selects_itself_at_zero (n : Int) (s : EvalState) :
    (selectPosition (.atom n) (.atom 0)).runState s = (.ok (.atom n), s) :=
  selectPosition_selects_a_named_position (.atom n) 0 (.atom n) (by decide) rfl s

theorem a_boolean_selects_itself_at_zero (b : Bool) (s : EvalState) :
    (selectPosition (.bool b) (.atom 0)).runState s = (.ok (.bool b), s) :=
  selectPosition_selects_a_named_position (.bool b) 0 (.bool b) (by decide) rfl s

/-- Both empty collection kinds fail at position zero (`[][0]`, `()[0]`). -/
theorem empty_collections_fail_at_zero (s : EvalState) :
    (selectPosition (.sequenceValue []) (.atom 0)).runState s = (.error Error.badIndex, s)
    ∧ (selectPosition (.listValue []) (.atom 0)).runState s = (.error Error.badIndex, s) :=
  ⟨selectPosition_past_the_view_is_badIndex _ 0 (by decide) rfl s,
   selectPosition_past_the_view_is_badIndex _ 0 (by decide) rfl s⟩

/-! ### The supplied selectors (`selectWith`) -/

theorem selectWith_nil {α : Type} (demand : α → EvalM Result) (receiver : Result) :
    selectWith demand receiver [] = pure [] := rfl

/-- One step: the FIRST supplied selector is demanded and its position selected, and
only then do the remaining selectors run. -/
theorem selectWith_step {α : Type} (demand : α → EvalM Result) (receiver : Result)
    (cell : α) (rest : List α) :
    selectWith demand receiver (cell :: rest)
      = (do
          let selected <- selectPosition receiver (<- demand cell)
          let tail <- selectWith demand receiver rest
          pure (selected :: tail)) := rfl

/-- A selector whose DEMAND fails ends the selection with that error and state. -/
theorem selectWith_failing_demand_ends_it {α : Type} (demand : α → EvalM Result) (receiver : Result)
    (cell : α) (rest : List α) (err : Error) (state state' : EvalState)
    (h : (demand cell).runState state = (.error err, state')) :
    (selectWith demand receiver (cell :: rest)).runState state = (.error err, state') := by
  show ((demand cell).runState >>= fun a => _) state = _
  simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, h]
  rfl

/-- A selector whose POSITION fails ends the selection with that error and state. -/
theorem selectWith_failing_position_ends_it {α : Type} (demand : α → EvalM Result) (receiver : Result)
    (cell : α) (rest : List α) (value : Result) (err : Error) (state state' state'' : EvalState)
    (hd : (demand cell).runState state = (.ok value, state'))
    (hp : (selectPosition receiver value).runState state' = (.error err, state'')) :
    (selectWith demand receiver (cell :: rest)).runState state = (.error err, state'') := by
  show ((demand cell).runState >>= fun a => _) state = _
  simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, hd]
  show ((selectPosition receiver value).runState >>= fun a => _) state' = _
  simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, hp]
  rfl

/-- A selector that succeeds hands its selected value and state to the rest of the run. -/
theorem selectWith_successful_selector_continues {α : Type} (demand : α → EvalM Result)
    (receiver : Result) (cell : α) (rest : List α) (value selected : Result)
    (state state' state'' : EvalState)
    (hd : (demand cell).runState state = (.ok value, state'))
    (hp : (selectPosition receiver value).runState state' = (.ok selected, state'')) :
    (selectWith demand receiver (cell :: rest)).runState state
      = (((selectWith demand receiver rest).runState state'').1.map (selected :: ·),
         ((selectWith demand receiver rest).runState state'').2) := by
  show ((demand cell).runState >>= fun a => _) state = _
  simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, hd]
  show ((selectPosition receiver value).runState >>= fun a => _) state' = _
  simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, hp]
  cases h : (selectWith demand receiver rest).runState state'' with
  | mk result final =>
      cases result <;> rfl

/-- The explicit trace of a selection run in `EvalM`: each supplied selector is
demanded ONCE, in supplied order, from the state its predecessor left, and its
position selected at once; the first failure — of a demand or of a position — ends
the run with that error and state. -/
def selectionTrace {α : Type} (demand : α → EvalM Result) (receiver : Result) :
    List α → EvalState → Except Error (List Result) × EvalState
  | [], state => (.ok [], state)
  | cell :: rest, state =>
      match (demand cell).runState state with
      | (.error err, state') => (.error err, state')
      | (.ok value, state') =>
          match (selectPosition receiver value).runState state' with
          | (.error err, state'') => (.error err, state'')
          | (.ok selected, state'') =>
              ((selectionTrace demand receiver rest state'').1.map (selected :: ·),
               (selectionTrace demand receiver rest state'').2)

/-- LEFT TO RIGHT, EACH SELECTOR ONCE, FIRST FAILURE STOPS: running the selection core
IS its explicit trace (`selectionTrace`), for every demand channel. -/
theorem selectWith_runs_as_its_trace {α : Type} (demand : α → EvalM Result) (receiver : Result)
    (cells : List α) (state : EvalState) :
    (selectWith demand receiver cells).runState state = selectionTrace demand receiver cells state := by
  induction cells generalizing state with
  | nil => rfl
  | cons cell rest ih =>
      cases hd : (demand cell).runState state with
      | mk r state' =>
          cases r with
          | error err =>
              rw [selectWith_failing_demand_ends_it demand receiver cell rest err state state' hd]
              simp [selectionTrace, hd]
          | ok value =>
              cases hp : (selectPosition receiver value).runState state' with
              | mk r' state'' =>
                  cases r' with
                  | error err =>
                      rw [selectWith_failing_position_ends_it demand receiver cell rest value err
                        state state' state'' hd hp]
                      simp [selectionTrace, hd, hp]
                  | ok selected =>
                      rw [selectWith_successful_selector_continues demand receiver cell rest value
                        selected state state' state'' hd hp, ih]
                      simp [selectionTrace, hd, hp]

private theorem selection_trace_stops_at_a_failing_prefix {α : Type} (demand : α → EvalM Result)
    (receiver : Result) (cells rest : List α) (state : EvalState) (err : Error) (final : EvalState)
    (hfail : selectionTrace demand receiver cells state = (.error err, final)) :
    selectionTrace demand receiver (cells ++ rest) state = (.error err, final) := by
  induction cells generalizing state with
  | nil => simp [selectionTrace] at hfail
  | cons cell more ih =>
      simp only [List.cons_append, selectionTrace] at hfail ⊢
      cases hd : (demand cell).runState state with
      | mk r state' =>
          cases r with
          | error e => simp only [hd] at hfail ⊢; exact hfail
          | ok value =>
              simp only [hd] at hfail ⊢
              cases hp : (selectPosition receiver value).runState state' with
              | mk r' state'' =>
                  cases r' with
                  | error e => simp only [hp] at hfail ⊢; exact hfail
                  | ok selected =>
                      simp only [hp] at hfail ⊢
                      cases ht : selectionTrace demand receiver more state'' with
                      | mk tr tf =>
                          rw [ht] at hfail
                          cases tr with
                          | error e =>
                              simp [Except.map] at hfail
                              obtain ⟨rfl, rfl⟩ := hfail
                              rw [ih state'' ht]
                              rfl
                          | ok vs => simp [Except.map] at hfail

/-- LATER SELECTORS ARE NOT DEMANDED AFTER A FAILURE: once a run of supplied selectors fails,
appending further selectors changes nothing — the run's error AND its final state are exactly
those of the failing prefix, whatever selectors follow it, so no later demand contributes an
effect (generalized from a failing HEAD selector to any failing prefix, R8/X-13). -/
theorem selectWith_stops_at_first_failure {α : Type} (demand : α → EvalM Result) (receiver : Result)
    (cells rest : List α) (state : EvalState) (err : Error) (final : EvalState)
    (hfail : (selectWith demand receiver cells).runState state = (.error err, final)) :
    (selectWith demand receiver (cells ++ rest)).runState state = (.error err, final) := by
  rw [selectWith_runs_as_its_trace] at hfail ⊢
  exact selection_trace_stops_at_a_failing_prefix demand receiver cells rest state err final hfail

/-- With the fixed pure demand that reads each `Nat` as its whole-number selector, the selected
values are the stored elements at the supplied positions, in SUPPLIED order, repetitions
included — `Data[2, 0, 2]` selects `30, 10, 30` (whose `selectionResult` is `(30, 10, 30)`) —
and the run touches no state. -/
theorem selectWith_pure_preserves_order_and_repetition (receiver : Result)
    (positions : List Nat) (s : EvalState)
    (h : ∀ i ∈ positions, i < (Result.projectionItems receiver).length) :
    (selectWith (fun (i : Nat) => (pure (Result.atom (Int.ofNat i)) : EvalM Result)) receiver positions).runState s
      = (.ok (positions.map (fun i => (Result.projectionItems receiver).getD i (.sequenceValue []))), s) := by
  induction positions with
  | nil => rfl
  | cons i rest ih =>
      have hi : i < (Result.projectionItems receiver).length := h i (List.mem_cons_self ..)
      have hsel : Result.select? receiver (Int.ofNat i).toNat
          = some ((Result.projectionItems receiver).getD i (.sequenceValue [])) := by
        simp [Result.select?, hi]
      have hp := selectPosition_selects_a_named_position receiver (Int.ofNat i) _ (by simp) hsel s
      rw [selectWith_successful_selector_continues _ receiver i rest (.atom (Int.ofNat i)) _ s s s rfl hp,
        ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
      rfl

/-! ### The selection result (`selectionResult`) -/

/-- Zero selections are the successful empty sequence `()` (emitting zero values) —
not the whole receiver, not `[]`, not a missing output. -/
theorem selection_of_nothing_is_the_empty_sequence :
    selectionResult [] = (.sequenceValue [], 0) := rfl

/-- One selection is the selected value itself. -/
theorem selection_of_one_is_the_value (v : Result) :
    selectionResult [v] = (v, Result.valueCount v) := rfl

/-- Several selections are ONE sequence of the selected values, kept whole. -/
theorem selection_of_several_is_one_sequence (a b : Result) (rest : List Result) :
    selectionResult (a :: b :: rest) = (.sequenceValue (a :: b :: rest), 1) := rfl

/-- Selected empty values stay elements: `Nested[2, 3]` is `((), [])` — never `[]`,
never flattened, never dropped. -/
theorem selected_empty_values_stay_elements :
    selectionResult [.sequenceValue [], .listValue []]
      = (.sequenceValue [.sequenceValue [], .listValue []], 1) := rfl

/-- SELECTION IS A VALUE BOUNDARY, over the production selection core: for EVERY demand
channel, when one supplied selector's demand yields the whole number `i` naming a stored
position of the receiver, the selection core's steps (3) and (4) — `selectWith` over that one
cell, then `selectionResult` — give exactly the value-boundary re-count of the STORED element,
`reCountValueBoundary (selected, n)` for every count `n` the element carried: the stored value
itself with `Result.valueCount`, its origin forgotten. The `.index` arm of `evalCounted`
instantiates `demand` with `fun cell => Prod.fst <$> demandNeedRecursive cell` over the selector
supply formed by `NeedSupply.addresses evalCounted` and demands the receiver first; that arm is
`partial`, so the instantiation (and that every evaluator selection route uses
this core) is a source fact pinned by CoreTests `SelectionValueBoundary` / `VariadicSelection`.
(Strengthened from a restatement of `reCountValueBoundary_recounts` that never mentioned
selection, R8/X-13.) -/
theorem select_is_a_value_boundary {α : Type} (demand : α → EvalM Result)
    (receiver selected : Result) (cell : α) (i : Int) (n : Nat)
    (hi : 0 ≤ i) (h : Result.select? receiver i.toNat = some selected) (s s' : EvalState)
    (hd : (demand cell).runState s = (.ok (.atom i), s')) :
    (do let chosen <- selectWith demand receiver [cell]; pure (selectionResult chosen)
      : EvalM CountedResult).runState s
      = (.ok (reCountValueBoundary (selected, n)), s') := by
  have hp := selectPosition_selects_a_named_position receiver i selected hi h s'
  have hrun := selectWith_successful_selector_continues demand receiver cell [] (.atom i) selected s s' s' hd hp
  show ((selectWith demand receiver [cell]).runState >>= fun a => _) s = _
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind]
  rw [hrun]
  rfl

/-- BRACKETS SOLVE THE INVOCATION AMBIGUITY; THEY DO NOT REMOVE THE ORDINARY
CONSEQUENCES OF SINGLETON NORMALIZATION: selecting one sequence-valued element gives
that sequence itself, so a spread opens IT (`[Data[0]*]` with `Data = [(10, 20), 30]`
is `[10, 20]`) — no selection count survives to recover an outer wrapper. -/
theorem single_selection_keeps_no_wrapper (a b : Result) :
    (selectionResult [.sequenceValue [a, b]]).1.spreadItems = [a, b] := rfl

/-! ### `first` and `last` are selections -/

/-- The selection pipeline over an already evaluated receiver: the `.index` arm's
steps (3) and (4) with the selector values already in hand. -/
def selectionOf (receiver : Result) (selectors : List Result) : EvalM CountedResult := do
  let selected <- selectWith (fun (x : Result) => (pure x : EvalM Result)) receiver selectors
  pure (selectionResult selected)

theorem selectionOf_single (receiver selector : Result) (s : EvalState) :
    (selectionOf receiver [selector]).runState s
      = match (selectPosition receiver selector).runState s with
        | (.ok selected, s') => (.ok (selectionResult [selected]), s')
        | (.error e, s') => (.error e, s') := by
  cases h : (selectPosition receiver selector).runState s with
  | mk r s' =>
      cases r with
      | ok selected =>
          show ((selectWith _ receiver [selector]).runState >>= fun a => _) s = _
          show (((pure selector : EvalM Result).runState >>= fun a => _) >>= fun a => _) s = _
          simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
            StateT.pure, h, selectWith]
      | error e =>
          show ((selectWith _ receiver [selector]).runState >>= fun a => _) s = _
          show (((pure selector : EvalM Result).runState >>= fun a => _) >>= fun a => _) s = _
          simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
            StateT.pure, h]

/-- `first(v) ≡ v[0]` for EVERY evaluated receiver value `v` — a scalar, a string
(`''` included), a sequence, a list, empty or not — at the level of the helpers: the `first`
helper over `v`'s collection view equals the selection core over `v` with the selector `0`
(`selectionOf`, the pure-demand pipeline): the same value under the same value boundary, or the
same `badIndex` when `v` has no positions. A law about one value in hand, not a rewrite of
effectful expressions (`first(BuildData())` invokes once); the builtin's empty policy, which
reports first on an empty collection, and the `partial` dispatch are guard-checked. -/
theorem first_is_selection_at_zero (v : Result) (s : EvalState) :
    (evalFirstCounted (builtinCollectionItems v)).runState s = (selectionOf v [.atom 0]).runState s := by
  rw [positional_view_is_shared, selectionOf_single]
  cases hv : Result.projectionItems v with
  | nil =>
      rw [selectPosition_past_the_view_is_badIndex v 0 (by decide) (by simp [Result.select?, hv]) s]
      rfl
  | cons x xs =>
      rw [selectPosition_selects_a_named_position v 0 x (by decide) (by simp [Result.select?, hv]) s]
      rfl

/-- `last(v) ≡ v[count(v) - 1]` for EVERY evaluated receiver value `v`, at the level of the
helpers: on a value with no positions the index is `-1`, which the selection core rejects as
`badIndex` — exactly what the `last` helper reports; otherwise both select the last element
under the same value boundary. Same caveats: a law about one value in hand
(`last(BuildData())` invokes once, while `BuildData()[count(BuildData()) - 1]` invokes twice),
and the builtin's empty policy and `partial` dispatch are guard-checked. -/
theorem last_is_selection_at_count_minus_one (v : Result) (s : EvalState) :
    (evalLastCounted (builtinCollectionItems v)).runState s
      = (selectionOf v [.atom (Int.ofNat (builtinCollectionItems v).length - 1)]).runState s := by
  rw [positional_view_is_shared, selectionOf_single]
  cases hv : Result.projectionItems v with
  | nil =>
      rw [selectPosition_negative_is_badIndex v _ (by decide) s]
      rfl
  | cons x xs =>
      have hidx : Int.ofNat (x :: xs).length - 1 = Int.ofNat xs.length := by simp
      have hsel : Result.select? v (Int.ofNat xs.length).toNat = some ((x :: xs).getLast (by simp)) := by
        simp [Result.select?, hv, List.getLast_eq_getElem]
      rw [hidx, selectPosition_selects_a_named_position v _ _ (by simp) hsel s]
      simp [evalLastCounted, List.getLast?_eq_some_getLast]
      rfl

/-- `count(v)` is the number of positions selection can name. -/
theorem count_is_the_number_of_positions (v : Result) (s : EvalState) :
    (evalCountCounted (builtinCollectionItems v)).runState s
      = (.ok (.atom (Int.ofNat (Result.projectionItems v).length), 1), s) := by
  rw [positional_view_is_shared]
  rfl

/-- The openable-structure view opens a received list to its items. -/
theorem structureItems_listValue (xs : List Result) :
    Result.structureItems? (Result.listValue xs) = some xs := rfl

/-- The openable-structure view opens a received sequence value. -/
theorem structureItems_sequenceValue (xs : List Result) :
    Result.structureItems? (Result.sequenceValue xs) = some xs := rfl

/-- Atoms are not openable structures. -/
theorem structureItems_atom (n : Int) :
    Result.structureItems? (Result.atom n) = none := rfl

/-- The spread view is the openable-structure view's total extension: it opens
a lone sequence or list and supplies any other value as itself. This is the
opening assignment deconstruction applies to its one right-hand-side value. -/
theorem spreadItems_extends_structureItems (v : Result) :
    (Result.structureItems? v).getD [v] = Result.spreadItems v := by
  cases v <;> rfl

/-
## Structural patterns select the value kind they destructure (September 2026)

`Result.sequencePatternItems?` and `Result.listPatternItems?` are the ONE rules
by which a structural pattern opens the value its slot supplies: the production Model-C
binder `bindNeedOne` reads them (`nested_sequence_level_is_bind_need_level`,
`nested_list_level_is_bind_need_level`; a structural CLAUSE pattern reaches it through
`NeedPattern.ofClause`). A sequence
pattern `(…)` opens a SEQUENCE value only and a list pattern `[…]` a LIST value
only; neither opens the other kind, and no scalar is a one-item structure — the
only pattern that takes a value whole is a bare binder. The view laws below are production
theorems; the binder's outcomes on a wrong kind or a wrong length (the binding's kind mismatch,
the group's arity error, a family's non-match) are guard-checked in
`CoreTests/StructuralPatterns.lean`.
-/

theorem sequence_pattern_items_sequence (xs : List Result) :
    Result.sequencePatternItems? (Result.sequenceValue xs) = some xs := rfl

theorem sequence_pattern_items_never_open_a_list (xs : List Result) :
    Result.sequencePatternItems? (Result.listValue xs) = none := rfl

theorem sequence_pattern_items_never_open_a_scalar (n : Int) (s : String) (b : Bool) :
    Result.sequencePatternItems? (Result.atom n) = none
    ∧ Result.sequencePatternItems? (Result.str s) = none
    ∧ Result.sequencePatternItems? (Result.bool b) = none :=
  ⟨rfl, rfl, rfl⟩

theorem list_pattern_items_list (xs : List Result) :
    Result.listPatternItems? (Result.listValue xs) = some xs := rfl

theorem list_pattern_items_never_open_a_sequence (xs : List Result) :
    Result.listPatternItems? (Result.sequenceValue xs) = none := rfl

theorem list_pattern_items_never_open_a_scalar (n : Int) (s : String) (b : Bool) :
    Result.listPatternItems? (Result.atom n) = none
    ∧ Result.listPatternItems? (Result.str s) = none
    ∧ Result.listPatternItems? (Result.bool b) = none :=
  ⟨rfl, rfl, rfl⟩

/-- No value is opened by BOTH structural patterns: the two kinds are disjoint,
so a sequence pattern and a list pattern never destructure the same value. -/
theorem structural_pattern_kinds_are_disjoint (v : Result) :
    Result.sequencePatternItems? v = none ∨ Result.listPatternItems? v = none := by
  cases v <;> simp [Result.sequencePatternItems?, Result.listPatternItems?]

/-- The singleton rule (`ParameterPattern.isSingletonSequenceItems`): a sequence
pattern of one non-collecting item — a capture, a nested sequence or a nested list — is flagged.
(The collector-only `(*xs)` and the one-element list `[x]` are valid signatures: the next two
theorems.) -/
theorem singleton_sequence_pattern_is_invalid (x : Ident) (inner : List ParameterPattern) :
    ParameterPattern.hasSingletonSequenceGroup (.sequenceValue [.capture { name := x }]) = true
    ∧ ParameterPattern.hasSingletonSequenceGroup (.sequenceValue [.sequenceValue inner]) = true
    ∧ ParameterPattern.hasSingletonSequenceGroup (.sequenceValue [.listValue inner]) = true := by
  simp [ParameterPattern.hasSingletonSequenceGroup, ParameterPattern.isSingletonSequenceItems]

/-- The collector-only sequence pattern `(*xs)` is not flagged by the singleton rule AND is a
valid signature (`signatureViolation? = none`; strengthened from the singleton check alone,
R8/X-13). -/
theorem collector_only_sequence_pattern_is_valid (xs : Ident) :
    ParameterPattern.hasSingletonSequenceGroup
        (.sequenceValue [.capture { name := xs, kind := .collecting }]) = false
    ∧ ParameterPattern.signatureViolation?
        [.sequenceValue [.capture { name := xs, kind := .collecting }]] = none := by
  constructor
  · simp [ParameterPattern.hasSingletonSequenceGroup, ParameterPattern.isSingletonSequenceItems,
      ParameterPattern.anyHasSingletonSequenceGroup]
  · simp [ParameterPattern.signatureViolation?, ParameterPattern.anyHasSingletonSequenceGroup,
      ParameterPattern.hasSingletonSequenceGroup, ParameterPattern.isSingletonSequenceItems,
      ParameterPattern.hasMultipleCollectingCapturesAtAnyLevel,
      ParameterPattern.collectingCaptureCountAtCurrentLevel,
      ParameterPattern.anyHasMultipleCollectingLevel, ParameterPattern.hasMultipleCollectingLevel,
      ParameterPattern.hasRepeatedCaptureNameIncludingCollecting, ParameterPattern.anyCollectingNames,
      ParameterPattern.collectingNames, ParameterPattern.anyNameOccurrences,
      ParameterPattern.nameOccurrences]

/-- The one-element list pattern `[x]` is not flagged by the singleton rule AND is a valid
signature (strengthened, R8/X-13). -/
theorem one_element_list_pattern_is_valid (x : Ident) :
    ParameterPattern.hasSingletonSequenceGroup (.listValue [.capture { name := x }]) = false
    ∧ ParameterPattern.signatureViolation? [.listValue [.capture { name := x }]] = none := by
  constructor
  · simp [ParameterPattern.hasSingletonSequenceGroup, ParameterPattern.anyHasSingletonSequenceGroup]
  · simp [ParameterPattern.signatureViolation?, ParameterPattern.anyHasSingletonSequenceGroup,
      ParameterPattern.hasSingletonSequenceGroup,
      ParameterPattern.hasMultipleCollectingCapturesAtAnyLevel,
      ParameterPattern.collectingCaptureCountAtCurrentLevel,
      ParameterPattern.anyHasMultipleCollectingLevel, ParameterPattern.hasMultipleCollectingLevel,
      ParameterPattern.hasRepeatedCaptureNameIncludingCollecting, ParameterPattern.anyCollectingNames,
      ParameterPattern.collectingNames, ParameterPattern.anyNameOccurrences,
      ParameterPattern.nameOccurrences]

/-
## Inferred signatures are held to the rules of written ones (X-02, September 30 2026)

`ParameterPattern.signatureViolation?` is THE validity of a parameter-pattern list as a callable
signature — the singleton rule, at most one collecting capture per pattern level, and no repeated
name that includes a collecting binding. It is a PRODUCTION definition: the pre-evaluation gate
`validateAlgorithmTree` reads it (a `partial` def, so "enforced before evaluation" is a source fact
pinned by CoreTests `StructuralPatterns`). The C# front end holds every INFERRED signature to the
same rules (`ParameterPattern.FindSignatureViolation`; agreement rests on C# tests): formula
lifting that would compose `K(a, *p, b, *q)` from `C1(a, *p)` and `C2(b, *q)` is the definition's
front-end error. The laws prove two collectors at one level invalid IN GENERAL (top level and
nested), pin the controls as valid (one collector between fixed captures — a collecting name two
callees share is ONE binding in C#'s formula-lifting merge, which Lean does not model; collectors
in their own groups), and the bridge to the binders' precondition: a valid signature has at most
one collecting capture at its top level.
-/

private abbrev lawCapture (name : Ident) : ParameterPattern := .capture { name := name }
private abbrev lawCollecting (name : Ident) : ParameterPattern := .capture { name := name, kind := .collecting }

/-- TWO COLLECTORS AT ONE LEVEL ARE AN INVALID SIGNATURE, at any level: once no singleton
sequence pattern is present (the first rule), a list with more than one collecting capture at
some pattern level is the violation `multipleCollectingAtOneLevel`. -/
theorem two_collectors_at_one_level_are_an_invalid_signature (ps : List ParameterPattern)
    (hs : ParameterPattern.anyHasSingletonSequenceGroup ps = false)
    (hm : ParameterPattern.hasMultipleCollectingCapturesAtAnyLevel ps = true) :
    ParameterPattern.signatureViolation? ps = some .multipleCollectingAtOneLevel := by
  simp [ParameterPattern.signatureViolation?, hs, hm]

/-- The X-02 composition in general: two (or more) TOP-LEVEL collectors, at any positions, are
an invalid signature (strengthened from three decided instances, R8/X-13; the instances follow
as examples). -/
theorem x02_distinct_top_level_collectors_are_an_invalid_signature (ps : List ParameterPattern)
    (hs : ParameterPattern.anyHasSingletonSequenceGroup ps = false)
    (h2 : 2 ≤ ParameterPattern.collectingCaptureCountAtCurrentLevel ps) :
    ParameterPattern.signatureViolation? ps = some .multipleCollectingAtOneLevel :=
  two_collectors_at_one_level_are_an_invalid_signature ps hs (by
    simp only [ParameterPattern.hasMultipleCollectingCapturesAtAnyLevel, Bool.or_eq_true,
      decide_eq_true_eq]
    omega)

example : ParameterPattern.signatureViolation?
    [lawCapture "a", lawCollecting "p", lawCapture "b", lawCollecting "q"]
    = some .multipleCollectingAtOneLevel :=
  x02_distinct_top_level_collectors_are_an_invalid_signature _ (by decide) (by decide)
example : ParameterPattern.signatureViolation?
    [lawCollecting "p", lawCapture "a", lawCapture "b", lawCollecting "q"]
    = some .multipleCollectingAtOneLevel :=
  x02_distinct_top_level_collectors_are_an_invalid_signature _ (by decide) (by decide)
example : ParameterPattern.signatureViolation?
    [lawCapture "a", lawCollecting "p", lawCapture "c", lawCapture "b", lawCollecting "q"]
    = some .multipleCollectingAtOneLevel :=
  x02_distinct_top_level_collectors_are_an_invalid_signature _ (by decide) (by decide)

/-- One collector between two fixed captures, `[a, *rest, b]`, is a valid signature (the shape
C#'s formula-lifting merge gives two callees that share the collecting name `rest`). -/
theorem one_collector_between_fixed_captures_is_a_valid_signature :
    ParameterPattern.signatureViolation? [lawCapture "a", lawCollecting "rest", lawCapture "b"] = none := by
  decide

/-- Witnesses that a collector in its OWN group is that group's level: `[(a, *p), (b, *q)]` and
`[(a, *p), d, *r]` are valid. (Not a general law: `[(a, *p), (b, *p)]` repeats a collecting name
across levels and is `repeatedNameIncludesCollecting`.) -/
theorem x02_one_collector_per_group_witnesses_are_valid :
    ParameterPattern.signatureViolation?
        [.sequenceValue [lawCapture "a", lawCollecting "p"], .sequenceValue [lawCapture "b", lawCollecting "q"]]
      = none
    ∧ ParameterPattern.signatureViolation?
        [.sequenceValue [lawCapture "a", lawCollecting "p"], lawCapture "d", lawCollecting "r"]
      = none := by
  decide

/-- Two collectors at one NESTED level are an invalid signature, in general (strengthened from
the decided instance `[[*r, *s]]`, R8/X-13, which follows as an example). -/
theorem nested_level_with_two_collectors_is_invalid (ps : List ParameterPattern)
    (hs : ParameterPattern.anyHasSingletonSequenceGroup ps = false)
    (hn : ParameterPattern.anyHasMultipleCollectingLevel ps = true) :
    ParameterPattern.signatureViolation? ps = some .multipleCollectingAtOneLevel :=
  two_collectors_at_one_level_are_an_invalid_signature ps hs (by
    simp [ParameterPattern.hasMultipleCollectingCapturesAtAnyLevel, hn])

example : ParameterPattern.signatureViolation? [.listValue [lawCollecting "r", lawCollecting "s"]]
    = some .multipleCollectingAtOneLevel :=
  nested_level_with_two_collectors_is_invalid _ (by decide) (by decide)

/-- A repeated name that includes a collector is invalid, while a repeated FIXED name is a valid
signature (`[x, *x]` versus `[x, x]`; that the valid repeat then binds as Q-05 equality
constraints is the binder's, not part of this statement). -/
theorem repeated_name_with_a_collector_is_invalid_while_fixed_repeats_are_valid :
    ParameterPattern.signatureViolation? [lawCapture "x", lawCollecting "x"]
      = some .repeatedNameIncludesCollecting
    ∧ ParameterPattern.signatureViolation? [lawCapture "x", lawCapture "x"] = none := by
  decide

/-- The bridge to the binders' precondition: a VALID signature has at most one collecting
capture at its top level — the condition `binder_minimum_is_the_signature_minimum` and the
production allocation laws assume (a corollary of `collector_gate_bounds_the_top_level`'s
weaker hypothesis). -/
theorem valid_signature_has_at_most_one_top_level_collector (ps : List ParameterPattern)
    (h : ParameterPattern.signatureViolation? ps = none) :
    ParameterPattern.collectingCaptureCountAtCurrentLevel ps ≤ 1 := by
  simp only [ParameterPattern.signatureViolation?] at h
  by_cases hs : ParameterPattern.anyHasSingletonSequenceGroup ps = true
  · simp [hs] at h
  · by_cases hm : ParameterPattern.hasMultipleCollectingCapturesAtAnyLevel ps = true
    · simp [hs, hm] at h
    · simp only [ParameterPattern.hasMultipleCollectingCapturesAtAnyLevel, Bool.or_eq_true,
        decide_eq_true_eq, not_or] at hm
      omega

/-
## Collection views and list normalization

Repeated-name binding (Q-05, NEED-04, Q-28): the production binder compares each repeated
occurrence with the retained earlier one as it inspects it (`bindNeedName`, `KatLang.lean`), and
since R3 `KatLangArityLaws/BinderTrace.lean` proves that per-occurrence order and verdict
(`repeated_name_binding`, `repeated_events_are_a_prefix_of_the_canonical_order`,
`repeated_callable_only_after_equal_values`, `traced_repeated_failure_points`) with
`sameRepeatedCallableIdentity` symbolic. Q-28's PERMUTATION laws (satisfiability, value up to
`==`, identity and channel availability unchanged when the repeated arguments are permuted) have
NO theorem (the roadmap's R4). Concrete outcomes are executed by guards — CoreTests `HigherOrderCalls`
(`repeatedNameCompatibilityAndFirstFailure`, `twoOccurrenceRepeatsKeepThePairwiseRule`,
`repeatedSuccessfulCallablePermutationsKeepBothChannels`,
`repeatedCountedBindingChecksTheCompletePair`), `ModelC` (`mixedRepeatedConflicts`,
`repeatedBindingKeepsTheCallableContribution`) and `RepeatedNameConstraints`, and on the C#
Decimal128 tier (Q-28, N-F: the first written among equally rich contributions supplies the
retained representation) `NumericRepresentativeSelectionTests`. The laws of this section are the
post-binding builtin collection view, the exact lists collection-producing builtins return, and
the normalization of list values.
-/

/-- The post-binding builtin collection view opens a bound list exactly like a
bound sequence value: ONE outer boundary, so `count([1, 2, 3])` counts three
items just as `count((1, 2, 3))` does. Opening is never recursive — nested
lists stay intact as single items (`count((1, [2], 3))` is 3, and a
collection element `[..]` inside the bound collection is one item; the identity returns `xs`
verbatim, so no element is opened). That the evaluator applies the view only AFTER ordinary
fixed binding — `count(1, 2, 3)` and `count([1, 2, 3]*)` being arity errors — is evaluator
behaviour, pinned by guards. -/
theorem builtinCollectionItems_list (xs : List Result) :
    builtinCollectionItems (Result.listValue xs) = xs := rfl

theorem builtinCollectionItems_keeps_nested_list_opaque (xs : List Result) :
    builtinCollectionItems
      (Result.sequenceValue [Result.atom 1, Result.listValue xs, Result.atom 3])
      = [Result.atom 1, Result.listValue xs, Result.atom 3] := rfl

/-- Collection-producing builtins materialize EXACT lists: for EVERY item list the
materialization is the exact list of those items with emitted count 1 — zero kept items form
`[]`, one kept item forms `[item]` (never erased to the item) — so the builtin result re-enters
arity as one value (generalized from the singleton, R8/X-13). -/
theorem makeCollectionListResult_exact (items : List Result) :
    makeCollectionListResult items = (Result.listValue items, 1) := rfl

theorem makeCollectionListResult_empty :
    makeCollectionListResult [] = (Result.listValue [], 1) := rfl

/-- Normalization preserves list structure exactly: elements normalize but
the list boundary never collapses (`[7]` stays `[7]`). -/
theorem normalize_listValue (xs : List Result) :
    Result.normalize (Result.listValue xs) = Result.listValue (xs.map Result.normalize) := by
  simp [Result.normalize]

/-- `Result.normalize` collapses a singleton SEQUENCE boundary around a list to the list (with
its elements normalized). (Surface `([1, 2])` never reaches `normalize`: the C# parser erases the
redundant group, `Parser.IsRedundantGrouping`.) -/
theorem normalize_singleton_sequence_of_list (xs : List Result) :
    Result.normalize (Result.sequenceValue [Result.listValue xs])
      = Result.listValue (xs.map Result.normalize) := by
  simp [Result.normalize]

/-- Ordinary capture and segment collection stay distinct operations on the same
supply: `capture` normalizes to a sequence value while `collect` preserves
the exact list (the surface illustrations `x = A*` regrouping list items as `(…)` and
`x, *rest = A` collecting them as `[…]` are evaluator behaviour, pinned by guards). -/
theorem capture_and_collect_differ_on_pairs (a b : Result) :
    captureForArityLaw [a, b] =
        Result.sequenceValue [Result.normalize a, Result.normalize b]
      ∧ collectSegment [a, b] = Result.listValue [a, b] :=
  ⟨capture_pair a b, rfl⟩

/-
## Canonical-form laws (general theorems over the value model)

The laws above pin specific shapes of the value views and total helpers; the theorems below
establish the general canonical-form story of `Result.normalize` over the authoritative value
model:

* `normalize_idempotent` — `Result.normalize` is a projection onto canonical
  values;
* `orphanFree_normalize` — canonical values contain no redundant singleton
  sequence boundary anywhere in their tree (no literal-unwritable "orphans");
* `captureForArityLaw_canonical` / `captureForArityLaw_orphanFree` — the capture
  alias `captureForArityLaw` only ever produces canonical, orphan-free values;
* `capture_toItems_of_canonical` — re-capturing the NON-spread item view
  (`Result.toItems`, which keeps lists opaque) reproduces canonical values
  exactly, for every value kind including lists;
* `capture_spreadItems_of_canonical_non_list` / `capture_spreadItems_of_list`
  — the SPREAD/capture round-trip holds exactly on canonical non-list values;
  spreading a list opens its boundary, so re-capture yields the canonical
  capture of its elements instead of the list.
-/

private theorem normalize_sequenceValue_of_map_nil {rs : List Result}
    (h : rs.map Result.normalize = []) :
    Result.normalize (Result.sequenceValue rs) = Result.sequenceValue [] := by
  simp [Result.normalize, h]

private theorem normalize_sequenceValue_of_map_singleton {rs : List Result} {r : Result}
    (h : rs.map Result.normalize = [r]) :
    Result.normalize (Result.sequenceValue rs) = r := by
  simp [Result.normalize, h]

private theorem normalize_sequenceValue_of_map_multi {rs : List Result} {a b : Result}
    {tl : List Result} (h : rs.map Result.normalize = a :: b :: tl) :
    Result.normalize (Result.sequenceValue rs) = Result.sequenceValue (a :: b :: tl) := by
  simp [Result.normalize, h]

mutual
  /-- General idempotence over the real model: `Result.normalize` is a
  projection, so normalizing an already-normalized value changes nothing.
  Canonical values are exactly the fixed points of `Result.normalize`. -/
  theorem normalize_idempotent : ∀ r : Result, r.normalize.normalize = r.normalize
    | .atom _ => by simp [Result.normalize]
    | .str _ => by simp [Result.normalize]
    | .bool _ => by simp [Result.normalize]
    | .sequenceValue rs => by
        have hl := normalize_map_idempotent rs
        cases h : rs.map Result.normalize with
        | nil =>
            rw [normalize_sequenceValue_of_map_nil h]
            exact normalize_empty_sequenceValue
        | cons a tl =>
            cases tl with
            | nil =>
                rw [normalize_sequenceValue_of_map_singleton h]
                rw [h] at hl
                simpa using hl
            | cons b tl2 =>
                rw [normalize_sequenceValue_of_map_multi h]
                rw [h] at hl
                exact normalize_sequenceValue_of_map_multi hl
    | .listValue rs => by
        have hl := normalize_map_idempotent rs
        rw [normalize_listValue, normalize_listValue, hl]
  termination_by r => sizeOf r

  /-- Element-wise idempotence of mapped normalization, the list companion of
  `normalize_idempotent`. -/
  theorem normalize_map_idempotent : ∀ rs : List Result,
      (rs.map Result.normalize).map Result.normalize = rs.map Result.normalize
    | [] => rfl
    | r :: rs => by
        have h1 := normalize_idempotent r
        have h2 := normalize_map_idempotent rs
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨h1, h2⟩
  termination_by rs => sizeOf rs
end

mutual
  /-- Orphan-freedom over the real model: `true` iff no singleton sequence
  boundary `Result.sequenceValue [x]` appears anywhere in the value. A
  singleton boundary is a literal-unwritable "orphan" (a stored `(5)` distinct
  from `5`): normalization erases such boundaries at every ordinary
  construction/capture site, so no canonical value contains one
  (`orphanFree_normalize`). Local tooling definition for these laws, not part
  of the authoritative model. -/
  def orphanFreeResult : Result -> Bool
    | .atom _ => true
    | .str _ => true
    | .bool _ => true
    | .sequenceValue rs => rs.length != 1 && orphanFreeResultList rs
    -- Exact lists carry NO singleton-orphan rule: `[x]` is literal-writable,
    -- so only the elements are checked (a sequence orphan nested inside a
    -- list still counts).
    | .listValue rs => orphanFreeResultList rs

  /-- List traversal for `orphanFreeResult`. -/
  def orphanFreeResultList : List Result -> Bool
    | [] => true
    | r :: rs => orphanFreeResult r && orphanFreeResultList rs
end

example : orphanFreeResult (Result.atom 5) = true := by decide
example : orphanFreeResult (Result.str "s") = true := by decide
example : orphanFreeResult (Result.bool true) = true := by decide
example : orphanFreeResult (Result.sequenceValue []) = true := by decide
example : orphanFreeResult (Result.sequenceValue [Result.atom 1]) = false := by decide
example : orphanFreeResult
    (Result.sequenceValue [Result.atom 1, Result.sequenceValue [Result.atom 2]]) = false := by
  decide
example : orphanFreeResult
    (Result.sequenceValue [Result.atom 1, Result.sequenceValue []]) = true := by decide
example : orphanFreeResult (Result.listValue []) = true := by decide
example : orphanFreeResult (Result.listValue [Result.atom 1]) = true := by decide
example : orphanFreeResult
    (Result.listValue [Result.listValue [Result.atom 1]]) = true := by decide
example : orphanFreeResult
    (Result.listValue [Result.sequenceValue [Result.atom 1]]) = false := by decide

mutual
  /-- Orphan-freedom of canonical values over the real model: normalization
  never leaves a redundant singleton sequence boundary anywhere in the tree. -/
  theorem orphanFree_normalize : ∀ r : Result, orphanFreeResult r.normalize = true
    | .atom _ => by simp [Result.normalize, orphanFreeResult]
    | .str _ => by simp [Result.normalize, orphanFreeResult]
    | .bool _ => by simp [Result.normalize, orphanFreeResult]
    | .sequenceValue rs => by
        have hl := orphanFreeList_map_normalize rs
        cases h : rs.map Result.normalize with
        | nil =>
            rw [normalize_sequenceValue_of_map_nil h]
            simp [orphanFreeResult, orphanFreeResultList]
        | cons a tl =>
            cases tl with
            | nil =>
                rw [normalize_sequenceValue_of_map_singleton h]
                rw [h] at hl
                simpa [orphanFreeResultList] using hl
            | cons b tl2 =>
                rw [normalize_sequenceValue_of_map_multi h]
                rw [h] at hl
                have hlen : ((a :: b :: tl2).length != 1) = true := by
                  simp only [List.length_cons, bne_iff_ne, ne_eq]
                  omega
                show ((a :: b :: tl2).length != 1 && orphanFreeResultList (a :: b :: tl2)) = true
                rw [hlen, hl]
                rfl
    | .listValue rs => by
        have hl := orphanFreeList_map_normalize rs
        rw [normalize_listValue]
        show orphanFreeResultList (rs.map Result.normalize) = true
        exact hl
  termination_by r => sizeOf r

  /-- Every element of a normalized item list is orphan-free, the list
  companion of `orphanFree_normalize`. -/
  theorem orphanFreeList_map_normalize : ∀ rs : List Result,
      orphanFreeResultList (rs.map Result.normalize) = true
    | [] => rfl
    | r :: rs => by
        have h1 := orphanFree_normalize r
        have h2 := orphanFreeList_map_normalize rs
        show (orphanFreeResult r.normalize
            && orphanFreeResultList (rs.map Result.normalize)) = true
        rw [h1, h2]
        rfl
  termination_by rs => sizeOf rs
end

/-- Capture canonicity over `captureForArityLaw` (the normalizing construction of the
spread value and the loop state; the written `.capture` arm combines its slots with the shallow
`combineOutputSlots`, which equals it exactly on canonical slots —
`combineOutputSlots_eq_capture_iff_canonical` in § Repeated spread over the real model — while
that the arm applies it, and that its slots are canonical, stay facts of the `partial` source and
the runtime invariant): a captured item supply
is already canonical, so capture is a fixed point of `Result.normalize`
(corollary of `normalize_idempotent`, since
`captureForArityLaw xs = Result.normalize (Result.sequenceValue xs)`). -/
theorem captureForArityLaw_canonical (xs : List Result) :
    (captureForArityLaw xs).normalize = captureForArityLaw xs :=
  normalize_idempotent (Result.sequenceValue xs)

/-- `captureForArityLaw` never mints an orphan (its agreement with the written `.capture`
arm's `combineOutputSlots` on canonical slots, VAL-03, is `combineOutputSlots_eq_capture_of_canonical`;
canonicality of evaluated slots is the invariant, not a theorem): every captured value is
orphan-free (corollary of `orphanFree_normalize`). -/
theorem captureForArityLaw_orphanFree (xs : List Result) :
    orphanFreeResult (captureForArityLaw xs) = true :=
  orphanFree_normalize (Result.sequenceValue xs)

/-- Item-view/capture round-trip over the real model: on a canonical value,
re-capturing the non-spread item view (`Result.toItems`) reproduces the value
exactly. Lists included: `toItems` keeps a list opaque (one item), and
singleton capture collapses back to that same list. -/
theorem capture_toItems_of_canonical (r : Result) (h : r.normalize = r) :
    captureForArityLaw r.toItems = r := by
  cases r with
  | atom n =>
      show captureForArityLaw [Result.atom n] = Result.atom n
      rw [capture_singleton]
      exact h
  | str s =>
      show captureForArityLaw [Result.str s] = Result.str s
      rw [capture_singleton]
      exact h
  | bool b =>
      show captureForArityLaw [Result.bool b] = Result.bool b
      rw [capture_singleton]
      exact h
  | sequenceValue rs =>
      rw [toItems_sequenceValue]
      exact h
  | listValue rs =>
      show captureForArityLaw [Result.listValue rs] = Result.listValue rs
      rw [capture_singleton]
      exact h

/-- The SPREAD/capture round trip holds exactly on canonical values that are NOT lists
(atoms, strings, Booleans and sequences). A list's spread opens its boundary; its re-capture is
`capture_spreadItems_of_list`. -/
theorem capture_spreadItems_of_canonical_non_list (r : Result)
    (h : r.normalize = r) (hl : ∀ xs, r ≠ Result.listValue xs) :
    captureForArityLaw r.spreadItems = r := by
  cases r with
  | atom n =>
      show captureForArityLaw [Result.atom n] = Result.atom n
      rw [capture_singleton]
      exact h
  | str s =>
      show captureForArityLaw [Result.str s] = Result.str s
      rw [capture_singleton]
      exact h
  | bool b =>
      show captureForArityLaw [Result.bool b] = Result.bool b
      rw [capture_singleton]
      exact h
  | sequenceValue rs =>
      show captureForArityLaw rs = Result.sequenceValue rs
      exact h
  | listValue rs =>
      exact absurd rfl (hl rs)

/-- Spread-then-capture on a list yields the canonical capture of its
ELEMENTS (the value-level law behind the surface `x = A*` regrouping list items as
`(1, 2, 3)`, which is evaluator behaviour). Singleton normalization
applies to the re-capture as usual, so a one-element payload collapses to
that lone element (`[7]` round-trips to `7`, and `[[7]]` to the inner
`[7]`), while multi-element payloads become one sequence value. -/
theorem capture_spreadItems_of_list (xs : List Result) :
    captureForArityLaw (Result.listValue xs).spreadItems
      = Result.normalize (Result.sequenceValue xs) := rfl

/-- Capture/item-view/capture collapse: since captured values are canonical, a second capture
of a captured value's NON-SPREAD item view (`Result.toItems`) is just the first capture. (With the
spread view this fails on lists: `capture_spreadItems_of_list`.) -/
theorem capture_toItems_capture (xs : List Result) :
    captureForArityLaw (captureForArityLaw xs).toItems = captureForArityLaw xs :=
  capture_toItems_of_canonical _ (captureForArityLaw_canonical xs)

/-- Spreading the empty sequence value supplies zero items: spread opens
a value via `Result.spreadItems`, which agrees with `Result.toItems` on
sequence values, so `()*` contributes nothing to the surrounding item
supply. This is the item-view statement of the visible-empty spread law (the
empty instance of `toItems_sequenceValue` / `spreadItems_sequenceValue`;
`spreadItems_empty_list` is the corresponding SPREAD fact for `[]`, whose `toItems` is `[[]]`). -/
theorem toItems_empty : (Result.sequenceValue []).toItems = [] := rfl

/-
## Zero-item-spread neutrality at the capture alias

`()` and `[]` spread to zero items, so inserting either spread view anywhere in an item supply
captured by `captureForArityLaw` changes nothing — while the UNSPREAD values stay visible
one-item slots (`toItems_listValue_opaque`, `valueCount_empty_list`). These are the value-model
faces of the core `capture_zero_item_spread_neutral` family; the surface forms `(n, ()*)` and
`(n, []*)` are written `.capture` slots evaluated by the `partial` arm and pinned by guards.
-/

/-- Generic neutral open at the capture alias: any value whose spread view supplies no items
leaves the captured value unchanged wherever its items are inserted (a congruence once the view
is empty). -/
theorem capture_zero_item_spread_neutral {r : Result}
    (h : r.spreadItems = []) (before after : List Result) :
    captureForArityLaw (before ++ r.spreadItems ++ after)
      = captureForArityLaw (before ++ after) := by
  rw [h]
  simp

/-- `()*`'s items are neutral at the capture alias. -/
theorem capture_empty_sequence_spread_neutral (before after : List Result) :
    captureForArityLaw (before ++ (Result.sequenceValue []).spreadItems ++ after)
      = captureForArityLaw (before ++ after) :=
  capture_zero_item_spread_neutral rfl before after

/-- `[]*`'s items are neutral at the capture alias (the unspread `[]` stays a visible one-item
value: `toItems_listValue_opaque`). -/
theorem capture_empty_list_spread_neutral (before after : List Result) :
    captureForArityLaw (before ++ (Result.listValue []).spreadItems ++ after)
      = captureForArityLaw (before ++ after) :=
  capture_zero_item_spread_neutral rfl before after

/-
## Repeated spread over the real model (Q-66 item 4, October 2026)

The paper algebra proves repeated spread as `items (capture (items v))`
(`CoreArityAlgebraProofs.lean` § Repeated spread is capture-mediated composition). This section
proves the same family over the authoritative `Result` model and the TOTAL production helpers the
evaluator calls:

* `combineOutputSlots` — the SHALLOW slot combination of the shared output-row loop
  (`evalOutputRowsPreparedCore`, which the written `.capture` arm reaches), of written-slot
  reification (`evalExplicitSequenceValueExprSlots`) and of `selectionResult`: zero slots `()`,
  one slot itself, several one sequence of them, with NO renormalization;
* `reopenSpreadItems` — one further written spread layer, `spread(capture(items))`;
  `reopenSpreadLayers` — that step once per extra written star; `spreadSupplyResult` — a spread
  expression's counted result (`evalSequenceSpreadCounted` returns
  `spreadSupplyResult (reopenSpreadLayers (layers - 1) supplied)`);
* `countedTopLevelValues` — how a spread ROW of a capture (and a spread leaf of the internal
  `sequenceConstruct` join) recovers its slots.

Results:

1. shallow combination IS ordinary capture exactly when the slots are canonical
   (`combineOutputSlots_eq_capture_iff_canonical`, whose reverse direction (`.mpr`) is the bridge
   `combineOutputSlots_eq_capture_of_canonical` and whose forward direction (`.mp`) is its
   converse; unconditionally it is capture after normalizing
   the slots, `normalize_sequenceValue_eq_combineOutputSlots_map_normalize`, and
   `combineOutputSlots_keeps_a_raw_slot` is a concrete raw slot it keeps);
2. opening a canonical value yields a canonical supply (`spreadItems_canonical_of_canonical`), so
   a canonical operand meets that premise without any extra assumption, and a reopened supply is
   canonical unconditionally (`reopenSpreadItems_canonical`);
3. the grouped spelling's layer — `(…)*` over a spread row, `combineOutputSlots` of the inner
   spread's recovered slots — IS the stacked step, for every supply and every number of inner
   layers, with NO canonicality premise (`grouped_spread_layer_is_reopen`,
   `stacked_spread_layer_is_grouped_layer`);
4. the repeated-spread laws: only a LONE item opens one more boundary
   (`reopen_spread_opens_only_a_lone_item`), zero items stay zero at every layer
   (`reopen_spread_zero`), a zero- or multi-item canonical supply is a fixed point at every layer
   (`reopen_spread_fixed_point_of_non_singleton`), a lone item reopens as its own spread view
   (`reopen_spread_singleton`), the complete fixed-point characterization
   (`reopen_spread_fixed_iff`), and repeated spread is never recursive flattening
   (`reopen_spread_is_not_recursive_flattening`);
5. the SHALLOW layer loop of C# `EvalSequenceSpreadCounted` (modelled locally by
   `shallowSpreadLayersForLaw` / `shallowSpreadResultForLaw`, read from its source) agrees with
   these helpers on every canonical operand, at every layer count
   (`shallow_spread_agrees_on_canonical_operand`).

EVIDENCE. Every theorem in this section is a PRODUCTION theorem about the total definitions above,
except `reopenSpreadItems_eq_spread_capture`, a LOCAL theorem that reads the production step
through this file's alias `captureForArityLaw`, and the three `shallow_spread_*` theorems of
§ The C#-shaped layer loop, LOCAL theorems over its two LOCAL models of C# source (no theorem here
proves C# code; C# correspondence rests on that inspection plus `StarSyntaxTests` and the
differential corpora).

NOT PROVED HERE. That the `partial` evaluator evaluates a spread operand ONCE and routes `A**`
through `reopenSpreadLayers` and `(A*)*` through the capture arm's `countedTopLevelValues` /
`combineOutputSlots` is a fact of its source, pinned by CoreTests `RepeatedSpread`; that every
evaluated value is canonical is the intended runtime invariant, assumed where a theorem states
`v.normalize = v` and never proved of the evaluator. An evaluator-level theorem
`eval (E**) = eval ((E*)*)` over arbitrary expressions — errors and resources included — needs a
total (fuel-indexed) evaluator and remains open (Q-66 item 4).
-/

/-! ### Shallow slot combination is ordinary capture on canonical slots -/

/-- Zero slots combine to the empty sequence value `()` — never the empty list `[]`. -/
theorem combineOutputSlots_nil : combineOutputSlots [] = Result.sequenceValue [] := rfl

/-- One slot is returned WHOLE: a lone structured slot is not opened, and a lone `()` slot is
returned as `()` — the same VALUE zero slots combine to (`combineOutputSlots_nil`); that a
non-spread `()` row still counts as one visible slot is the row loop's emitted count, a fact of
the `partial` source, not of this function. -/
theorem combineOutputSlots_singleton (v : Result) : combineOutputSlots [v] = v := rfl

/-- Two or more slots form ONE sequence of exactly those slots: no slot is dropped (a `()` slot
stays an element, `combineOutputSlots [(), 1] = ((), 1)`), opened or renormalized. With
`combineOutputSlots_nil` and `combineOutputSlots_singleton` this is the whole definition — the
`0 / 1 / many` rule C# `CombineOutputSlots` has by inspection. -/
theorem combineOutputSlots_multi (a b : Result) (rest : List Result) :
    combineOutputSlots (a :: b :: rest) = Result.sequenceValue (a :: b :: rest) := rfl

example : combineOutputSlots [Result.sequenceValue []] = Result.sequenceValue [] := rfl
example : combineOutputSlots [Result.sequenceValue [], Result.atom 1]
    = Result.sequenceValue [Result.sequenceValue [], Result.atom 1] := rfl

/-- Ordinary capture is shallow combination of the NORMALIZED slots, for every supply: both
sides are the same `0 / 1 / many` match over `xs.map Result.normalize`. -/
theorem normalize_sequenceValue_eq_combineOutputSlots_map_normalize (xs : List Result) :
    Result.normalize (Result.sequenceValue xs) = combineOutputSlots (xs.map Result.normalize) := by
  cases h : xs.map Result.normalize with
  | nil => simp [Result.normalize, h, combineOutputSlots]
  | cons a t =>
      cases t with
      | nil => simp [Result.normalize, h, combineOutputSlots]
      | cons b t2 => simp [Result.normalize, h, combineOutputSlots]

/-- THE CAPTURE BRIDGE: on canonical slots the shallow production combination
`combineOutputSlots` (the written `.capture` arm's, through `evalOutputRowsPreparedCore`) IS
ordinary normalizing capture `Result.normalize (Result.sequenceValue xs)` — the production
expression of `reopenSpreadItems` and `spreadSupplyResult`, and this file's `captureForArityLaw xs`
by `rfl` — for every number of slots and every value kind (atoms, strings, Booleans, sequences,
exact lists, `()`, `[]`, nested structure). Canonical slots are the intended runtime invariant of
evaluated values; the theorem assumes it of `xs` and proves nothing about the evaluator
establishing it. -/
theorem combineOutputSlots_eq_capture_of_canonical (xs : List Result)
    (h : ∀ r ∈ xs, r.normalize = r) :
    combineOutputSlots xs = Result.normalize (Result.sequenceValue xs) := by
  rw [normalize_sequenceValue_eq_combineOutputSlots_map_normalize, map_normalize_id_of_canonical h]

/-- Shallow combination of canonical slots is canonical. -/
theorem combineOutputSlots_canonical_of_canonical (xs : List Result)
    (h : ∀ r ∈ xs, r.normalize = r) :
    (combineOutputSlots xs).normalize = combineOutputSlots xs := by
  rw [combineOutputSlots_eq_capture_of_canonical xs h]
  exact normalize_idempotent (Result.sequenceValue xs)

private theorem canonical_of_map_normalize_eq : ∀ {xs : List Result},
    xs.map Result.normalize = xs -> ∀ r ∈ xs, r.normalize = r
  | [], _ => by simp
  | a :: t, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      intro r hr
      rcases List.mem_cons.mp hr with he | hmem
      · subst he
        exact h.1
      · exact canonical_of_map_normalize_eq h.2 r hmem

/-- THE BRIDGE'S EXACT CONDITION: shallow combination equals ordinary capture EXACTLY when every
slot is canonical — the premise of `combineOutputSlots_eq_capture_of_canonical` is necessary for
every supply, not only sufficient. -/
theorem combineOutputSlots_eq_capture_iff_canonical (xs : List Result) :
    combineOutputSlots xs = Result.normalize (Result.sequenceValue xs) ↔
      ∀ r ∈ xs, r.normalize = r := by
  refine ⟨fun heq => ?_, combineOutputSlots_eq_capture_of_canonical xs⟩
  rw [normalize_sequenceValue_eq_combineOutputSlots_map_normalize] at heq
  match xs, heq with
  | [], _ =>
      intro r hr
      simp at hr
  | [x], heq =>
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      simpa [combineOutputSlots] using heq.symm
  | a :: b :: t, heq =>
      apply canonical_of_map_normalize_eq
      simp only [combineOutputSlots, List.map_cons] at heq
      exact (Result.sequenceValue.inj heq).symm

/-- A concrete raw slot the shallow combination keeps exactly as it is (the orphan `(1)`), where
capture normalizes it — a non-canonical supply on which the two differ, as the forward direction
(`.mp`) of `combineOutputSlots_eq_capture_iff_canonical` requires: `combineOutputSlots` really is
shallow. -/
theorem combineOutputSlots_keeps_a_raw_slot :
    combineOutputSlots [Result.sequenceValue [Result.atom 1], Result.atom 2]
      ≠ Result.normalize (Result.sequenceValue [Result.sequenceValue [Result.atom 1], Result.atom 2]) := by
  simp [combineOutputSlots, Result.normalize]

/-! ### Opening a canonical value yields a canonical supply -/

/-- No value is an element of its own sequence payload (the sequence companion of
`mem_ne_listValue`). -/
theorem mem_ne_sequenceValue {w : Result} {ys : List Result} (h : w ∈ ys) :
    w ≠ Result.sequenceValue ys := by
  intro he
  have hlt : sizeOf w < sizeOf ys := List.sizeOf_lt_of_mem h
  have hsz : sizeOf (Result.sequenceValue ys) = 1 + sizeOf ys := by simp
  rw [he, hsz] at hlt
  omega

/-- Every item the spread view supplies from a canonical value is canonical (the real-model face
of the algebra's `canonicalSupply_items_of_canonical`). A canonical SEQUENCE value's payload is
its own normalization: the one-element case is impossible, since `Result.normalize` never leaves
the orphan `(w)` (`orphanFree_normalize`). This is what lets the repeated-spread laws below assume
canonicality of the OPERAND value only. -/
theorem spreadItems_canonical_of_canonical {v : Result} (h : v.normalize = v) :
    ∀ r ∈ v.spreadItems, r.normalize = r := by
  cases v with
  | atom n =>
      intro r hr
      simp only [Result.spreadItems, Result.toItems, List.mem_singleton] at hr
      subst hr
      exact h
  | str s =>
      intro r hr
      simp only [Result.spreadItems, Result.toItems, List.mem_singleton] at hr
      subst hr
      exact h
  | bool b =>
      intro r hr
      simp only [Result.spreadItems, Result.toItems, List.mem_singleton] at hr
      subst hr
      exact h
  | listValue rs =>
      rw [normalize_listValue] at h
      exact canonical_of_map_normalize_eq (Result.listValue.inj h)
  | sequenceValue rs =>
      show ∀ r ∈ rs, r.normalize = r
      cases hm : rs.map Result.normalize with
      | nil =>
          have hrs : rs = [] := List.map_eq_nil_iff.mp hm
          subst hrs
          simp
      | cons u tl =>
          cases tl with
          | nil =>
              exfalso
              cases rs with
              | nil => simp at hm
              | cons w t =>
                  cases t with
                  | cons b t2 => simp at hm
                  | nil =>
                      have hnu : w.normalize = u := by simpa using hm
                      have hseq : Result.normalize (Result.sequenceValue [w]) = u := by
                        simp [Result.normalize, hnu]
                      rw [hseq] at h
                      have ho := orphanFree_normalize w
                      rw [hnu, h] at ho
                      simp [orphanFreeResult] at ho
          | cons b tl2 =>
              have hn : Result.normalize (Result.sequenceValue rs)
                  = Result.sequenceValue (u :: b :: tl2) := by
                simp [Result.normalize, hm]
              rw [hn] at h
              have heq : u :: b :: tl2 = rs := Result.sequenceValue.inj h
              rw [← heq] at hm
              exact canonical_of_map_normalize_eq (heq ▸ hm)

/-! ### The reopening step (`reopenSpreadItems`) -/

/-- One further spread layer is `spread(capture(items))` — the production definition, read
through the capture alias. -/
theorem reopenSpreadItems_eq_spread_capture (items : List Result) :
    reopenSpreadItems items = (captureForArityLaw items).spreadItems := rfl

/-- A reopened supply is canonical, unconditionally: it is the spread view of a captured, hence
canonical, value. Every layer after the first therefore meets the canonical-supply premise of the
laws below on its own. -/
theorem reopenSpreadItems_canonical (items : List Result) :
    ∀ r ∈ reopenSpreadItems items, r.normalize = r :=
  spreadItems_canonical_of_canonical (normalize_idempotent (Result.sequenceValue items))

/-- On a canonical supply the reopening step is spread after the SHALLOW combination: the
normalizing capture of `reopenSpreadItems` and `combineOutputSlots` agree there. -/
theorem reopenSpreadItems_eq_spread_combineOutputSlots_of_canonical {items : List Result}
    (h : ∀ r ∈ items, r.normalize = r) :
    reopenSpreadItems items = (combineOutputSlots items).spreadItems := by
  rw [combineOutputSlots_eq_capture_of_canonical items h]
  rfl

/-- THE REOPENING THEOREM at the value level: for a canonical value `v`, one further spread layer
over `v*` is `spread(combineOutputSlots(spread(v)))` — and, by `reopenSpreadItems_eq_spread_capture`,
`spread(capture(spread(v)))`, the algebra's `items (capture (items v))`. Only `v`'s canonicality
is assumed; its supply's follows (`spreadItems_canonical_of_canonical`). -/
theorem reopen_spread_is_spread_capture_spread {v : Result} (hv : v.normalize = v) :
    reopenSpreadItems v.spreadItems = (combineOutputSlots v.spreadItems).spreadItems :=
  reopenSpreadItems_eq_spread_combineOutputSlots_of_canonical
    (spreadItems_canonical_of_canonical hv)

/-! ### Stacked and grouped layers are one operation -/

/-- A spread ROW recovers exactly the normalized items of its supply: the capture arm's row loop
reads the inner spread's counted result through `countedTopLevelValues`, which inverts
`spreadSupplyResult` up to normalization — for every supply, `()` items included (a lone `()`
item has count 1, so it is recovered as one slot, never dropped). -/
theorem countedTopLevelValues_spreadSupplyResult (items : List Result) :
    countedTopLevelValues (spreadSupplyResult items) = items.map Result.normalize := by
  match items with
  | [] => rfl
  | [x] =>
      show [Result.normalize (Result.sequenceValue [x])] = [x.normalize]
      rw [normalize_sequenceValue_singleton]
  | a :: b :: t =>
      have hn : Result.normalize (Result.sequenceValue (a :: b :: t))
          = Result.sequenceValue ((a :: b :: t).map Result.normalize) := by
        simp [Result.normalize]
      show countedTopLevelValues
          (Result.normalize (Result.sequenceValue (a :: b :: t)), t.length + 2)
        = (a :: b :: t).map Result.normalize
      rw [hn]
      rfl

/-- THE GROUPED LAYER IS THE STACKED STEP, for every supply (no canonicality premise): the written
capture `(S*)` combines the spread row's recovered slots shallowly, and spreading that value is
exactly `reopenSpreadItems S` — what the stacked `**` applies. So, once the operand has been
evaluated to the supply `S`, `(A*)*` and `A**` perform the same value operation. -/
theorem grouped_spread_layer_is_reopen (items : List Result) :
    (combineOutputSlots (countedTopLevelValues (spreadSupplyResult items))).spreadItems
      = reopenSpreadItems items := by
  rw [countedTopLevelValues_spreadSupplyResult,
    ← normalize_sequenceValue_eq_combineOutputSlots_map_normalize]
  rfl

/-- The last of `n + 1` layers can be taken outermost. -/
theorem reopenSpreadLayers_succ_eq_reopen (n : Nat) (items : List Result) :
    reopenSpreadLayers (n + 1) items = reopenSpreadItems (reopenSpreadLayers n items) := by
  induction n generalizing items with
  | zero => rfl
  | succ k ih =>
      show reopenSpreadLayers (k + 1) (reopenSpreadItems items) = _
      rw [ih]
      rfl

/-- Grouping any stacked chain once more is one more stacked layer, for every supply and every
`n`: `n + 2` written stars (`reopenSpreadLayers (n + 1)` over the first star's supply) equal the
grouped `(A^(n+1 stars))*`. Every mixed spelling (`(A*)**`, `((A*)*)*`, `(A**)*`, …) therefore
reduces to `reopenSpreadLayers` over the operand's supply; the final counted results then agree,
both being `spreadSupplyResult` of the same items. -/
theorem stacked_spread_layer_is_grouped_layer (n : Nat) (items : List Result) :
    reopenSpreadLayers (n + 1) items =
      (combineOutputSlots
        (countedTopLevelValues (spreadSupplyResult (reopenSpreadLayers n items)))).spreadItems := by
  rw [grouped_spread_layer_is_reopen, reopenSpreadLayers_succ_eq_reopen]

/-- Every number of reopening layers over a canonical supply yields a canonical supply. -/
theorem reopenSpreadLayers_canonical {xs : List Result} (h : ∀ r ∈ xs, r.normalize = r) :
    ∀ n : Nat, ∀ r ∈ reopenSpreadLayers n xs, r.normalize = r
  | 0 => h
  | Nat.succ n => by
      rw [reopenSpreadLayers_succ_eq_reopen]
      exact reopenSpreadItems_canonical _

/-! ### Cardinality: only a lone item opens one more boundary -/

/-- `()*` re-captures as `()`, which spreads to nothing. -/
theorem reopenSpreadItems_nil : reopenSpreadItems [] = [] := by
  simp [reopenSpreadItems, Result.normalize, Result.spreadItems, Result.toItems]

/-- The reopening step on ARBITRARY raw supplies: nothing for no items, the normalized lone item's
spread view for one, and the element-wise normalized items for two or more (the real-model face of
the algebra's `items_capture`). -/
theorem reopenSpreadItems_cardinality (xs : List Result) :
    reopenSpreadItems xs =
      match xs with
      | [] => []
      | [x] => (Result.normalize x).spreadItems
      | a :: b :: t => (a :: b :: t).map Result.normalize := by
  match xs with
  | [] => exact reopenSpreadItems_nil
  | [x] =>
      show (Result.normalize (Result.sequenceValue [x])).spreadItems = _
      rw [normalize_sequenceValue_singleton]
  | a :: b :: t =>
      show (Result.normalize (Result.sequenceValue (a :: b :: t))).spreadItems = _
      have hn : Result.normalize (Result.sequenceValue (a :: b :: t))
          = Result.sequenceValue ((a :: b :: t).map Result.normalize) := by
        simp [Result.normalize]
      rw [hn]
      rfl

/-- On a canonical supply the normalization is invisible: a lone item `x` reopens as `x`'s own
spread view, and every other supply — empty or multi-item — is re-supplied exactly. -/
theorem reopenSpreadItems_of_canonical {xs : List Result} :
    (∀ r ∈ xs, r.normalize = r) ->
    reopenSpreadItems xs =
      match xs with
      | [x] => x.spreadItems
      | other => other := by
  intro h
  rw [reopenSpreadItems_cardinality]
  match xs, h with
  | [], _ => rfl
  | [x], h =>
      show (Result.normalize x).spreadItems = x.spreadItems
      rw [h x List.mem_cons_self]
  | a :: b :: t, h =>
      show (a :: b :: t).map Result.normalize = a :: b :: t
      exact map_normalize_id_of_canonical h

/-- THE REPEATED-SPREAD CARDINALITY LAW over `Result` (the algebra's
`repeated_spread_cardinality`): for a canonical value, `v**` re-supplies `v*` unchanged unless
`v*` is ONE item, which then opens its own boundary. Repeated spread opens exactly the boundary
the capture composition exposes — nothing else. -/
theorem reopen_spread_opens_only_a_lone_item {v : Result} (hv : v.normalize = v) :
    reopenSpreadItems v.spreadItems =
      match v.spreadItems with
      | [x] => x.spreadItems
      | other => other :=
  reopenSpreadItems_of_canonical (spreadItems_canonical_of_canonical hv)

/-- No items stay no items, at every layer. -/
theorem reopenSpreadLayers_nil : ∀ n : Nat, reopenSpreadLayers n [] = []
  | 0 => rfl
  | Nat.succ n => by
      show reopenSpreadLayers n (reopenSpreadItems []) = []
      rw [reopenSpreadItems_nil]
      exact reopenSpreadLayers_nil n

/-- Exactly `()` and `[]` spread to no items. -/
theorem spreadItems_eq_nil_iff (v : Result) :
    v.spreadItems = [] ↔ v = Result.sequenceValue [] ∨ v = Result.listValue [] := by
  cases v with
  | atom n => simp [Result.spreadItems, Result.toItems]
  | str s => simp [Result.spreadItems, Result.toItems]
  | bool b => simp [Result.spreadItems, Result.toItems]
  | sequenceValue rs => simp [Result.spreadItems, Result.toItems]
  | listValue rs => simp [Result.spreadItems]

/-- ZERO: a value whose spread supplies no items — `()` or `[]` (`spreadItems_eq_nil_iff`) —
supplies no items under any number of further layers (`[]**` is zero items: `[]* = []`,
`capture [] = ()`, `()* = []`). No canonicality premise. -/
theorem reopen_spread_zero {v : Result} (h : v.spreadItems = []) (n : Nat) :
    reopenSpreadLayers n v.spreadItems = [] := by
  rw [h]
  exact reopenSpreadLayers_nil n

/-- A canonical supply that is not exactly one item is a fixed point of the reopening step. -/
theorem reopenSpreadItems_fixed_of_non_singleton {xs : List Result}
    (h : ∀ r ∈ xs, r.normalize = r) (hlen : xs.length ≠ 1) :
    reopenSpreadItems xs = xs := by
  rw [reopenSpreadItems_of_canonical h]
  match xs, hlen with
  | [], _ => rfl
  | [_], hlen => exact absurd rfl hlen
  | _ :: _ :: _, _ => rfl

/-- … and so of every number of layers. -/
theorem reopenSpreadLayers_fixed_of_non_singleton {xs : List Result}
    (h : ∀ r ∈ xs, r.normalize = r) (hlen : xs.length ≠ 1) :
    ∀ n : Nat, reopenSpreadLayers n xs = xs
  | 0 => rfl
  | Nat.succ n => by
      show reopenSpreadLayers n (reopenSpreadItems xs) = xs
      rw [reopenSpreadItems_fixed_of_non_singleton h hlen]
      exact reopenSpreadLayers_fixed_of_non_singleton h hlen n

/-- MULTI-ITEM FIXED POINT: when `v*` is not exactly one item, `v**`, `v***`, … supply exactly what
`v*` supplies, every structured item kept whole (`[[1, 2], [3, 4]]**` supplies the two inner lists,
never `1, 2, 3, 4`). -/
theorem reopen_spread_fixed_point_of_non_singleton {v : Result} (hv : v.normalize = v)
    (hlen : v.spreadItems.length ≠ 1) (n : Nat) :
    reopenSpreadLayers n v.spreadItems = v.spreadItems :=
  reopenSpreadLayers_fixed_of_non_singleton (spreadItems_canonical_of_canonical hv) hlen n

/-- A lone RAW item reopens as its normalization's spread view. -/
theorem reopenSpreadItems_singleton (x : Result) :
    reopenSpreadItems [x] = (Result.normalize x).spreadItems := by
  show (Result.normalize (Result.sequenceValue [x])).spreadItems = _
  rw [normalize_sequenceValue_singleton]

/-- A lone canonical item reopens as its own spread view. -/
theorem reopenSpreadItems_singleton_of_canonical {x : Result} (hx : x.normalize = x) :
    reopenSpreadItems [x] = x.spreadItems := by
  rw [reopenSpreadItems_singleton, hx]

/-- SINGLETON: when `v*` is the one item `x`, the capture boundary erases the singleton grouping
and `v**` supplies `x*` — the ONLY case in which a further layer opens another boundary (a lone
sequence or list opens one level, a lone `()` or `[]` gives no items, a lone scalar is itself).
`x`'s canonicality follows from `v`'s. -/
theorem reopen_spread_singleton {v x : Result} (hv : v.normalize = v)
    (h : v.spreadItems = [x]) :
    reopenSpreadItems v.spreadItems = x.spreadItems := by
  have hx : x.normalize = x := by
    have hc := spreadItems_canonical_of_canonical hv
    rw [h] at hc
    exact hc x List.mem_cons_self
  rw [h, reopenSpreadItems_singleton_of_canonical hx]

-- Each supply shape on concrete values (the first spread's supply, then further layers).
-- `[7]**`: a lone scalar is itself.
example : reopenSpreadItems (Result.listValue [Result.atom 7]).spreadItems = [Result.atom 7] := by
  simp [reopenSpreadItems, Result.normalize, Result.spreadItems, Result.toItems]
-- `[(1, 2)]**`: a lone sequence value opens one level.
example : reopenSpreadItems (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]]).spreadItems
    = [Result.atom 1, Result.atom 2] := by
  simp [reopenSpreadItems, Result.normalize, Result.spreadItems, Result.toItems]
-- `[[1, 2]]**`: a lone LIST opens too — capture erases only the singleton sequence grouping and
-- returns the list `[1, 2]` itself (normalization never removes a list boundary); the next
-- layer's spread opens that list.
example : reopenSpreadItems (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]).spreadItems
    = [Result.atom 1, Result.atom 2] := by
  simp [reopenSpreadItems, Result.normalize, Result.spreadItems]
-- `[()]**` and `[[]]**`: a lone visible empty item is one item at `*`, zero items at `**`.
example : reopenSpreadItems (Result.listValue [Result.sequenceValue []]).spreadItems = [] := by
  simp [reopenSpreadItems, Result.normalize, Result.spreadItems, Result.toItems]
example : reopenSpreadItems (Result.listValue [Result.listValue []]).spreadItems = [] := by
  simp [reopenSpreadItems, Result.normalize, Result.spreadItems]
-- `[(), []]**`: two visible empty items are a multi-item supply, kept exactly.
example : reopenSpreadItems (Result.listValue [Result.sequenceValue [], Result.listValue []]).spreadItems
    = [Result.sequenceValue [], Result.listValue []] := by
  simp [reopenSpreadItems, Result.normalize, Result.spreadItems, Result.toItems]
-- `[[[7]]]**` supplies `[7]` and `[[[7]]]***` supplies `7`: one boundary per written star.
example : reopenSpreadLayers 1
    (Result.listValue [Result.listValue [Result.listValue [Result.atom 7]]]).spreadItems
    = [Result.listValue [Result.atom 7]] := by
  simp [reopenSpreadLayers, reopenSpreadItems, Result.normalize, Result.spreadItems]
example : reopenSpreadLayers 2
    (Result.listValue [Result.listValue [Result.listValue [Result.atom 7]]]).spreadItems
    = [Result.atom 7] := by
  simp [reopenSpreadLayers, reopenSpreadItems, Result.normalize, Result.spreadItems]

/-! ### The complete fixed-point characterization -/

/-- A value's spread view is exactly itself-as-one-item iff it is not an openable structure. -/
theorem spreadItems_eq_singleton_self_iff (x : Result) :
    x.spreadItems = [x] ↔ x.structureItems? = none := by
  cases x with
  | atom n => simp [Result.spreadItems, Result.toItems, Result.structureItems?]
  | str s => simp [Result.spreadItems, Result.toItems, Result.structureItems?]
  | bool b => simp [Result.spreadItems, Result.toItems, Result.structureItems?]
  | sequenceValue rs =>
      simp only [Result.structureItems?, reduceCtorEq, iff_false]
      intro h
      have hrs : rs = [Result.sequenceValue rs] := h
      have hmem : Result.sequenceValue rs ∈ [Result.sequenceValue rs] := List.mem_cons_self
      rw [← hrs] at hmem
      exact mem_ne_sequenceValue hmem rfl
  | listValue rs =>
      simp only [Result.structureItems?, reduceCtorEq, iff_false]
      intro h
      have hrs : rs = [Result.listValue rs] := h
      have hmem : Result.listValue rs ∈ [Result.listValue rs] := List.mem_cons_self
      rw [← hrs] at hmem
      exact mem_ne_listValue hmem rfl

/-- The reopening step fixes a canonical supply iff it is not one item, or its lone item is not
an openable structure (a number, string or Boolean). -/
theorem reopenSpreadItems_fixed_iff {xs : List Result} (h : ∀ r ∈ xs, r.normalize = r) :
    reopenSpreadItems xs = xs ↔
      xs.length ≠ 1 ∨ ∃ x, xs = [x] ∧ x.structureItems? = none := by
  constructor
  · intro hfix
    match xs, h, hfix with
    | [], _, _ =>
        left
        simp
    | _ :: _ :: _, _, _ =>
        left
        simp
    | [x], h, hfix =>
        right
        refine ⟨x, rfl, ?_⟩
        rw [reopenSpreadItems_singleton_of_canonical (h x List.mem_cons_self)] at hfix
        exact (spreadItems_eq_singleton_self_iff x).mp hfix
  · rintro (hlen | ⟨x, rfl, hx⟩)
    · exact reopenSpreadItems_fixed_of_non_singleton h hlen
    · rw [reopenSpreadItems_singleton_of_canonical (h x List.mem_cons_self)]
      exact (spreadItems_eq_singleton_self_iff x).mpr hx

/-- THE COMPLETE FIXED-POINT CHARACTERIZATION over `Result` (the algebra's
`repeated_spread_fixed_iff`, with the algebra's lone ATOM generalized to the real model's
non-structures — numbers, strings, Booleans): for a canonical value, `v**` supplies exactly what
`v*` supplies iff `v*` is not one item, or its lone item is not a sequence or list value. -/
theorem reopen_spread_fixed_iff {v : Result} (hv : v.normalize = v) :
    reopenSpreadItems v.spreadItems = v.spreadItems ↔
      v.spreadItems.length ≠ 1 ∨ ∃ x, v.spreadItems = [x] ∧ x.structureItems? = none :=
  reopenSpreadItems_fixed_iff (spreadItems_canonical_of_canonical hv)

/-! ### Repeated spread is never recursive flattening -/

private theorem sum_sizeOf_lt : ∀ (ys : List Result), (ys.map sizeOf).sum < sizeOf ys
  | [] => by simp
  | y :: ys => by
      have ih := sum_sizeOf_lt ys
      simp only [List.map_cons, List.sum_cons, List.cons.sizeOf_spec]
      omega

private theorem spread_weight (r : Result) :
    (r.spreadItems.map sizeOf).sum ≤ sizeOf r ∧
      ((r.spreadItems.map sizeOf).sum = sizeOf r → r.structureItems? = none) := by
  cases r with
  | atom n => simp [Result.spreadItems, Result.toItems, Result.structureItems?]
  | str s => simp [Result.spreadItems, Result.toItems, Result.structureItems?]
  | bool b => simp [Result.spreadItems, Result.toItems, Result.structureItems?]
  | sequenceValue rs =>
      have hlt := sum_sizeOf_lt rs
      have hs : sizeOf (Result.sequenceValue rs) = 1 + sizeOf rs := by simp
      show (rs.map sizeOf).sum ≤ _ ∧ ((rs.map sizeOf).sum = _ → _)
      rw [hs]
      exact ⟨by omega, fun h => absurd h (by omega)⟩
  | listValue rs =>
      have hlt := sum_sizeOf_lt rs
      have hs : sizeOf (Result.listValue rs) = 1 + sizeOf rs := by simp
      show (rs.map sizeOf).sum ≤ _ ∧ ((rs.map sizeOf).sum = _ → _)
      rw [hs]
      exact ⟨by omega, fun h => absurd h (by omega)⟩

private theorem flatMap_spread_weight : ∀ (xs : List Result),
    ((xs.flatMap Result.spreadItems).map sizeOf).sum ≤ (xs.map sizeOf).sum ∧
      (((xs.flatMap Result.spreadItems).map sizeOf).sum = (xs.map sizeOf).sum →
        ∀ r ∈ xs, r.structureItems? = none)
  | [] => by simp
  | x :: xs => by
      obtain ⟨h1, h2⟩ := spread_weight x
      obtain ⟨ih1, ih2⟩ := flatMap_spread_weight xs
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons]
      refine ⟨by omega, ?_⟩
      intro heq r hr
      rcases List.mem_cons.mp hr with he | hmem
      · subst he
        exact h2 (by omega)
      · exact ih2 (by omega) r hmem

/-- Opening every member of a supply one more level changes nothing iff no member is an openable
structure (a size argument: opening a structure strictly shrinks the supply's total size). -/
theorem flatMap_spreadItems_eq_self_iff (xs : List Result) :
    xs.flatMap Result.spreadItems = xs ↔ ∀ r ∈ xs, r.structureItems? = none := by
  constructor
  · intro h
    exact (flatMap_spread_weight xs).2 (by rw [h])
  · intro h
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        have hx := h x List.mem_cons_self
        have hxs := ih (fun r hr => h r (List.mem_cons_of_mem x hr))
        rw [List.flatMap_cons, (spreadItems_eq_singleton_self_iff x).mpr hx, hxs]
        rfl

/-- On a canonical supply that is not one item, the reopening step agrees with opening every
member (a `concatMap`-style per-item lift) iff there is no structured member to open — so any
structured member tells the two apart. -/
theorem reopenSpreadItems_is_flattening_iff {xs : List Result}
    (h : ∀ r ∈ xs, r.normalize = r) (hlen : xs.length ≠ 1) :
    reopenSpreadItems xs = xs.flatMap Result.spreadItems ↔
      ∀ r ∈ xs, r.structureItems? = none := by
  rw [reopenSpreadItems_fixed_of_non_singleton h hlen]
  constructor
  · intro heq
    exact (flatMap_spreadItems_eq_self_iff xs).mp heq.symm
  · intro hs
    exact ((flatMap_spreadItems_eq_self_iff xs).mpr hs).symm

/-- NO RECURSIVE FLATTENING (the general form of the algebra's
`repeated_spread_not_recursive_flattening`): when `v*` is not one item and supplies a structured
item, NO number of further written stars opens it — every layer re-supplies `v*` exactly, which
differs from opening its members. -/
theorem reopen_spread_is_not_recursive_flattening {v : Result} (hv : v.normalize = v)
    (hlen : v.spreadItems.length ≠ 1)
    (hs : ∃ r ∈ v.spreadItems, r.structureItems? ≠ none) (n : Nat) :
    reopenSpreadLayers n v.spreadItems ≠ v.spreadItems.flatMap Result.spreadItems := by
  rw [reopen_spread_fixed_point_of_non_singleton hv hlen n]
  intro heq
  obtain ⟨r, hr, hne⟩ := hs
  exact hne ((flatMap_spreadItems_eq_self_iff _).mp heq.symm r hr)

-- `[[1, 2], [3, 4]]**` supplies the two inner lists, not `1, 2, 3, 4`.
example : reopenSpreadItems
      (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2],
        Result.listValue [Result.atom 3, Result.atom 4]]).spreadItems
    = [Result.listValue [Result.atom 1, Result.atom 2],
       Result.listValue [Result.atom 3, Result.atom 4]] := by
  simp [reopenSpreadItems, Result.normalize, Result.spreadItems, Result.toItems]

/-! ### The C#-shaped layer loop

C# `Evaluator.EvalSequenceSpreadCounted` (and its async twin) re-captures between layers and at
the last layer with `MakeCheckedSequenceCapture` — a resource reservation (a C#-only limit tier)
followed by the SHALLOW `CombineOutputSlots` — where Lean's `reopenSpreadItems` /
`spreadSupplyResult` use the normalizing capture. The two definitions below are LOCAL models of
that loop's structural rule, read from the C# source (Lean proves nothing about C# code); the
theorems prove that the shallow rule computes the same supply and counted result as the
production helpers on every canonical operand, at every layer count. -/

/-- LOCAL model of the C# layer loop's supply: each further layer spreads the SHALLOW combination
of the previous supply. -/
def shallowSpreadLayersForLaw : Nat -> List Result -> List Result
  | 0, items => items
  | Nat.succ n, items => shallowSpreadLayersForLaw n (combineOutputSlots items).spreadItems

/-- LOCAL model of the C# spread expression's counted result: the shallow combination of the final
supply with its item count. -/
def shallowSpreadResultForLaw (layers : Nat) (items : List Result) : CountedResult :=
  (combineOutputSlots (shallowSpreadLayersForLaw layers items),
    (shallowSpreadLayersForLaw layers items).length)

/-- The shallow layer rule and the production reopening agree on every canonical supply. -/
theorem shallow_spread_layers_agree_on_canonical_supply {xs : List Result}
    (h : ∀ r ∈ xs, r.normalize = r) (n : Nat) :
    shallowSpreadLayersForLaw n xs = reopenSpreadLayers n xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ k ih =>
      show shallowSpreadLayersForLaw k (combineOutputSlots xs).spreadItems
        = reopenSpreadLayers k (reopenSpreadItems xs)
      rw [← reopenSpreadItems_eq_spread_combineOutputSlots_of_canonical h]
      exact ih (reopenSpreadItems_canonical xs)

/-- … and so do the counted results. -/
theorem shallow_spread_result_agrees_on_canonical_supply {xs : List Result}
    (h : ∀ r ∈ xs, r.normalize = r) (n : Nat) :
    shallowSpreadResultForLaw n xs = spreadSupplyResult (reopenSpreadLayers n xs) := by
  unfold shallowSpreadResultForLaw spreadSupplyResult
  rw [shallow_spread_layers_agree_on_canonical_supply h n,
    combineOutputSlots_eq_capture_of_canonical _ (reopenSpreadLayers_canonical h n)]

/-- THE C#-SHAPED RULE AT THE VALUE LEVEL: for a canonical operand value `v`, a spread with
`n + 1` written stars yields the same counted result under the LOCAL model of C#'s shallow layer
rule (`shallowSpreadResultForLaw`, read from the C# source) as under the production helpers
`evalSequenceSpreadCounted` applies — on the canonical values the runtime invariant promises, the
shallow and the normalizing capture compute the same supply and count. This proves the modelled
rule, not C# code; C#'s per-layer collection reservation is outside the model. -/
theorem shallow_spread_agrees_on_canonical_operand {v : Result} (hv : v.normalize = v)
    (n : Nat) :
    shallowSpreadResultForLaw n v.spreadItems
      = spreadSupplyResult (reopenSpreadLayers n v.spreadItems) :=
  shallow_spread_result_agrees_on_canonical_supply (spreadItems_canonical_of_canonical hv) n

/-
## Result-boundary re-count laws

`reCountValueBoundary` is the shared helper the evaluator applies (a fact of its `partial`
source) at public property/call/builtin RESULT boundaries: the caller observes the same structural
value with emitted count `Result.valueCount` (0 for the empty sequence value,
otherwise 1), whatever internal item-supply count the body produced.
-/

/-- `reCountValueBoundary` in closed form: a result boundary re-counts the
value as `Result.valueCount` and discards the body's internal count. This is
the general law for any counted pair. -/
theorem reCountValueBoundary_recounts (r : Result) (n : Nat) :
    reCountValueBoundary (r, n) = (r, r.valueCount) := rfl

/-- A result boundary never rebuilds the value: only the count changes. -/
theorem reCountValueBoundary_fst (p : CountedResult) :
    (reCountValueBoundary p).fst = p.fst := rfl

/-- Boundary re-counting is idempotent: a value boundary inside a value
boundary re-counts to the same pair. -/
theorem reCountValueBoundary_idempotent (p : CountedResult) :
    reCountValueBoundary (reCountValueBoundary p) = reCountValueBoundary p := rfl

/-- `Result.valueCount` is at most one (by its definition it is 0 only for the empty sequence
value `()`, and 1 for every other value, the empty list `[]` included). -/
theorem valueCount_le_one : ∀ r : Result, r.valueCount ≤ 1
  | .atom _ => Nat.le_refl 1
  | .str _ => Nat.le_refl 1
  | .bool _ => Nat.le_refl 1
  | .sequenceValue [] => Nat.zero_le 1
  | .sequenceValue (_ :: _) => Nat.le_refl 1
  | .listValue _ => Nat.le_refl 1

/-- The empty list is a visible value: `Result.valueCount []` is 1, unlike the empty sequence
value `()` (0 by definition). That the evaluator emits `valueCount` at value boundaries is a
source fact. -/
theorem valueCount_empty_list : (Result.listValue []).valueCount = 1 := rfl

/-- A result boundary emits at most one value: after `reCountValueBoundary`
the count is 0 (empty sequence value) or 1, never a multi-item count. -/
theorem reCountValueBoundary_count_le_one (p : CountedResult) :
    (reCountValueBoundary p).snd ≤ 1 :=
  valueCount_le_one p.fst

/-
## Loop results are value boundaries (Q-26, decided October 2026)

A completed `while`/`repeat` returns `loopResultCounted finalSlots` (a fact of the `partial`
loop evaluator's source, pinned by CoreTests `LoopCardinality`): the
canonical capture of its final state's slots, re-counted at the ordinary
RESULT value boundary exactly like every builtin and call result. The laws
below are instances of the re-count laws above: the loop's slot count is its
own iteration protocol (the step's row supply, LOOP-03) and never leaks into
the count its consumer observes. (Q-24's companion fact — the step's row
supply takes no pattern-derived argument — is definitional: `evalAlgOutputSlots`
has no such parameter; CoreTests `LoopCardinality` pins it per head category.)
-/

/-- The loop result IS the re-counted capture of its final slots. -/
theorem loop_result_is_a_value_boundary (slots : List Result) :
    loopResultCounted slots = reCountValueBoundary (loopStateResult slots, slots.length) := rfl

/-- The re-count never rebuilds the loop result: its value is the canonical
capture of the final slots. -/
theorem loop_result_value (slots : List Result) :
    (loopResultCounted slots).fst = loopStateResult slots := rfl

/-- The loop result's emitted count is its value's `valueCount`, never the
number of final slots. -/
theorem loop_result_count_is_value_count (slots : List Result) :
    (loopResultCounted slots).snd = (loopStateResult slots).valueCount := rfl

/-- `loopResultCounted`'s count is at most one (so a non-spread loop contributes at most one
item to a row supply — a consequence for the `partial` row-supply construction, guard-checked). -/
theorem loop_result_count_le_one (slots : List Result) :
    (loopResultCounted slots).snd ≤ 1 :=
  reCountValueBoundary_count_le_one _

/-- `loopResultCounted` does not depend on the slot count: two final states whose captures are
equal complete to the same counted result (a one-slot state holding `(20, 30)` and the two-slot
state `20, 30` alike). That the loop's consumers see only this result is a source fact. -/
theorem loop_result_depends_only_on_the_final_value (left right : List Result)
    (h : loopStateResult left = loopStateResult right) :
    loopResultCounted left = loopResultCounted right := by
  simp only [loopResultCounted, reCountValueBoundary, h]

/-
## Loop steps are ordinary callables (Q-23, decided October 2026)

A loop step is invoked as the ORDINARY call over the current state supply
(`runNeedStepSlots`: the one binder for a user algorithm, the ordinary family
dispatcher `selectNeedFamilyBranch`, the ordinary builtin argument roles
`applyBuiltinCountedResolved`); only the receiver is the loop's. That dispatch is
exercised by `CoreTests/LoopSteps.lean` (including the one-iteration law:
`repeat(F, 1, s…)` equals `F(s…)` value for value and failure category for
failure category, for families, builtins, aliases and wrappers). The laws below
pin the one piece of new receiver arithmetic — how a builtin's result becomes the
next state — as total facts.
-/

/-- A builtin step supplies exactly ONE row, whatever its result. -/
theorem loop_step_builtin_result_is_one_row (out : CountedResult) :
    (loopStepBuiltinRows out).length = 1 := rfl

/-- The row is the invocation's result value itself. -/
theorem loop_step_builtin_row_is_the_result_value (out : CountedResult) :
    loopStepBuiltinRows out = [out.fst] := rfl

/-- The result's emitted count never decides the slot count: a `()` result
(emitted count 0) and a value (emitted count 1) are both one row. -/
theorem loop_step_builtin_rows_ignore_emitted_count (value : Result) (left right : Nat) :
    loopStepBuiltinRows (value, left) = loopStepBuiltinRows (value, right) := rfl

/-- The `()` result is one visible `()` slot — where re-counting the result as a
top-level supply (`countedTopLevelValues`) would read it as NO slot. -/
theorem loop_step_builtin_empty_result_is_one_slot :
    loopStepBuiltinRows (.sequenceValue [], 0) = [.sequenceValue []] ∧
      countedTopLevelValues (.sequenceValue [], 0) = [] := ⟨rfl, rfl⟩

/-- A collection result is ONE slot holding the collection, never its elements. -/
theorem loop_step_builtin_collection_result_is_one_slot (items : List Result) :
    loopStepBuiltinRows (.listValue items, 1) = [.listValue items] := rfl

/-
## `atoms` builtin laws (issue #136)

`Result.languageAtoms` is the atoms builtin's collector: numeric atoms
gathered depth-first, left to right, through BOTH sequence and exact list
boundaries; strings contribute no atoms. The builtin materializes the
collection as ONE list via `makeCollectionListResult`, so the
result kind never depends on the input kind or on the collected count. Truth
is Boolean-only (`Result.asBool?` reads no atom view at all), so lists still
have no truth value — the traversal laws here can never leak into `if`.
-/

/-- LOCAL mirror of the expression the `partial` `.atomsBuiltin` arm of `applyBuiltinCounted`
returns for an evaluated argument value (agreement by inspection of the source, not proof). -/
def atomsBuiltinResultForLaw (r : Result) : CountedResult :=
  makeCollectionListResult ((Result.languageAtoms r).map Result.atom)

-- `languageAtoms` (like `Result.hostAtoms`) recurses through
-- `List.flatMap`, so it compiles via well-founded recursion and its
-- equations are established by `simp` rather than `rfl`.

theorem atoms_number (n : Int) :
    Result.languageAtoms (Result.atom n) = [n] := by
  simp [Result.languageAtoms]

theorem atoms_string (s : String) :
    Result.languageAtoms (Result.str s) = [] := by
  simp [Result.languageAtoms]

/-- Booleans are not numeric atoms: the collector gives a Boolean no atoms (so the mirror's
materialization is the empty list `[]`). -/
theorem atoms_bool (b : Bool) :
    Result.languageAtoms (Result.bool b) = [] := by
  simp [Result.languageAtoms]

/-- Sequence traversal is concatenation of element traversals, which is
exactly depth-first left-to-right order. -/
theorem atoms_sequence (rs : List Result) :
    Result.languageAtoms (Result.sequenceValue rs)
      = rs.flatMap Result.languageAtoms := by
  simp [Result.languageAtoms]

/-- List traversal follows the same rule as sequence traversal: both
boundary kinds open, and neither is preserved in the result. -/
theorem atoms_list (rs : List Result) :
    Result.languageAtoms (Result.listValue rs)
      = rs.flatMap Result.languageAtoms := by
  simp [Result.languageAtoms]

theorem atoms_empty_sequence :
    Result.languageAtoms (Result.sequenceValue []) = [] := by
  simp [atoms_sequence]

theorem atoms_empty_list :
    Result.languageAtoms (Result.listValue []) = [] := by
  simp [atoms_list]

/-- Order preservation in concatenation form: element order is result order,
with no sorting, deduplication, or per-container grouping. -/
theorem atoms_order_preserved (a b : List Result) :
    Result.languageAtoms (Result.sequenceValue (a ++ b))
      = Result.languageAtoms (Result.sequenceValue a)
        ++ Result.languageAtoms (Result.sequenceValue b) := by
  simp [atoms_sequence]

theorem atoms_nested_sequence :
    Result.languageAtoms (Result.sequenceValue
      [Result.sequenceValue [Result.atom 1, Result.atom 2],
       Result.sequenceValue [Result.atom 3, Result.atom 4]]) = [1, 2, 3, 4] := by
  simp [Result.languageAtoms]

theorem atoms_nested_list :
    Result.languageAtoms (Result.listValue
      [Result.listValue [Result.atom 1, Result.atom 2],
       Result.listValue [Result.atom 3, Result.atom 4]]) = [1, 2, 3, 4] := by
  simp [Result.languageAtoms]

/-- Mixed nesting: `atoms([(1, 2), [3, [4]], 5])` collects `[1, 2, 3, 4, 5]` —
sequence and list boundaries interleave freely and flatten uniformly. -/
theorem atoms_mixed_sequence_list :
    Result.languageAtoms (Result.listValue
      [Result.sequenceValue [Result.atom 1, Result.atom 2],
       Result.listValue [Result.atom 3, Result.listValue [Result.atom 4]],
       Result.atom 5]) = [1, 2, 3, 4, 5] := by
  simp [Result.languageAtoms]

/-- The local mirror `atomsBuiltinResultForLaw` is ONE exact list value with emitted count 1
for EVERY input — including a zero-atom collection, where it is the empty list `[]` (never the
invisible empty sequence). -/
theorem atoms_result_is_list (r : Result) :
    atomsBuiltinResultForLaw r
      = (Result.listValue ((Result.languageAtoms r).map Result.atom), 1) := rfl

/-- Singleton results stay singleton lists: no canonical erasure applies to
the materialized collection. -/
theorem atoms_singleton_preserved (n : Int) :
    atomsBuiltinResultForLaw (Result.atom n)
      = (Result.listValue [Result.atom n], 1) := by
  simp [atomsBuiltinResultForLaw, makeCollectionListResult, atoms_number]

/-- The materialization of the atom 7 is `[7]`, never `7`: the materialized list is
structurally distinct from the bare atom. -/
theorem atoms_singleton_list_ne_atom (n : Int) :
    (atomsBuiltinResultForLaw (Result.atom n)).fst ≠ Result.atom n := by
  simp [atomsBuiltinResultForLaw, makeCollectionListResult, atoms_number]

-- Local equation lemmas for `hostAtoms` (same well-founded shape), used by
-- the agreement proof below.

theorem hostAtoms_atom (n : Int) :
    Result.hostAtoms (Result.atom n) = [n] := by
  simp [Result.hostAtoms]

theorem hostAtoms_str (s : String) :
    Result.hostAtoms (Result.str s) = [] := by
  simp [Result.hostAtoms]

theorem hostAtoms_bool (b : Bool) :
    Result.hostAtoms (Result.bool b) = [] := by
  simp [Result.hostAtoms]

theorem hostAtoms_sequence (rs : List Result) :
    Result.hostAtoms (Result.sequenceValue rs) = rs.flatMap Result.hostAtoms := by
  simp [Result.hostAtoms]

theorem hostAtoms_list (rs : List Result) :
    Result.hostAtoms (Result.listValue rs) = rs.flatMap Result.hostAtoms := by
  simp [Result.hostAtoms]

/-
The language collector and the host projection agree on numeric content.
They stay SEPARATE definitions with separate contracts (exact list value vs
host atom list); this proven agreement documents the coincidence without
letting either drift silently.
-/
mutual
  theorem languageAtoms_eq_hostAtoms : ∀ r : Result,
      Result.languageAtoms r = Result.hostAtoms r
    | .atom n => by rw [atoms_number, hostAtoms_atom]
    | .str s => by rw [atoms_string, hostAtoms_str]
    | .bool b => by rw [atoms_bool, hostAtoms_bool]
    | .sequenceValue rs => by
        rw [atoms_sequence, hostAtoms_sequence]
        exact languageAtomsList_eq_hostAtomsList rs
    | .listValue rs => by
        rw [atoms_list, hostAtoms_list]
        exact languageAtomsList_eq_hostAtomsList rs
  termination_by r => sizeOf r

  theorem languageAtomsList_eq_hostAtomsList : ∀ rs : List Result,
      rs.flatMap Result.languageAtoms = rs.flatMap Result.hostAtoms
    | [] => by simp
    | r :: rs => by
        rw [List.flatMap_cons, List.flatMap_cons,
            languageAtoms_eq_hostAtoms r, languageAtomsList_eq_hostAtomsList rs]
  termination_by rs => sizeOf rs
end

/-- Truth is Boolean-only: a list value never has a truth value, whatever its
contents. `atoms` traversing lists can introduce no list truthiness because
the Boolean view `asBool?` reads no atom view at all. -/
theorem asBool_list_none (rs : List Result) :
    Result.asBool? (Result.listValue rs) = none := rfl

/-- Numbers have no truth value either: the Boolean view of a number is empty (the condition
consumers — `if`, `filter`, `while`, the logical operators — read this view by design; that they
do is a source fact). -/
theorem asBool_atom_none (n : Int) : Result.asBool? (Result.atom n) = none := rfl

/-- Strings have no truth value. -/
theorem asBool_str_none (s : String) : Result.asBool? (Result.str s) = none := rfl

/-- A Boolean value is its own truth value. -/
theorem asBool_bool (b : Bool) : Result.asBool? (Result.bool b) = some b := rfl

/-- A redundant singleton sequence boundary normalizes away before the Boolean
view is taken, exactly as `asInt?` treats a parenthesized number. -/
theorem asBool_singleton_sequence (b : Bool) :
    Result.asBool? (Result.sequenceValue [Result.bool b]) = some b := by
  simp [Result.asBool?, Result.normalize]

/-- A multi-item sequence value is never a Boolean, whatever its items: the Boolean view
performs no flattening (generalized from two-item sequences, R8/X-13). -/
theorem asBool_multi_item_sequence_none (a b : Result) (rest : List Result) :
    Result.asBool? (Result.sequenceValue (a :: b :: rest)) = none := by
  simp [Result.asBool?, Result.normalize]

/-- Booleans are not numbers: the numeric view `asInt?` of a Boolean is empty. The operators'
operand reader `requireNumericScalarOperandOf` (and unary `-`) consult exactly this view, so by
inspection — not proved here — no operator reads a Boolean as `0`/`1`. -/
theorem asInt_bool_none (b : Bool) : Result.asInt? (Result.bool b) = none := rfl

-- AT-MOST-ONCE ARGUMENT VALUE EVALUATION (Q-01) and REPEATED NAMES ARE CONSTRAINTS, NOT MERGES
-- (Q-05) have NO theorem in this section. The first lives on the slot's need cell — the `.param`
-- arm of `evalCounted` demands it first through the partial `demandNeedRecursive` driver.
-- R5 proves completed reuse and qualified publication for the total `NeedDemand.step` shell
-- and its public `demandNeed` specialization in `KatLangArityLaws/NeedControl.lean`; the
-- recursive edge and whole-run at-most-once refinement remain open. This behavior is executed
-- by `CoreTests/ArgumentValueOutcome.lean` and `CoreTests/ModelC.lean`. The second is the
-- production binder's per-occurrence inspection (`bindNeedName`), whose order and verdict are
-- proved since R3 in `KatLangArityLaws/BinderTrace.lean` (`repeated_name_binding` and the
-- repeated-name trace laws; its callable-identity check calls `partial` definitions and stays
-- symbolic), and executed by `CoreTests/RepeatedNameConstraints.lean` (evaluator programs and the
-- binder itself, both argument orders) and `CoreTests/ModelC.lean`. A plain (non-repeated) binder transports its
-- cell and demands nothing: `plain_patterns_bind_without_any_channel`,
-- `binder_name_transports_a_non_repeated_cell`.

/-! ## Builtin call assembly respects argument roles (PV-05 / PV-19 / PV-20, September 2026)

A collection builtin's argument adapter handles each written slot by the ROLE its
position has in the builtin's metadata (`SequenceBuiltinMetadata.slotRole`): a VALUE
slot is demanded once and its outcome — one value or one failure — is final; a
CALLBACK slot carries its algorithm and is invoked by the builtin, never evaluated
merely because it was supplied; and a spread slot is supply assembly whose failure is
the call's failure. The laws below pin the metadata (`slotRole`, read by the lifting
specification), the call-item assembly `collectSequenceCallableCallItems` (which evaluates
nothing), and the per-item preparation helper `prepareSequenceBuiltinSuffixArgItem`. Supply
formation is the total `NeedSupply` core, with public `formNeedSupplySourced` specialization
proved in `KatLangArityLaws/NeedControl.lean`. Its installation of `evalCounted` at the builtin
call site and the per-slot demand (`demandSequenceBuiltinCallItemValue`) remain in the `partial`
evaluator, pinned by `CoreTests/BuiltinArgumentRoles.lean`. -/

/-- The `collection` parameter is a VALUE slot of every collection builtin. -/
theorem collection_position_is_a_value_slot (metadata : SequenceBuiltinMetadata) :
    metadata.slotRole 0 = .value := by
  simp [SequenceBuiltinMetadata.slotRole]

/-- A control position is a CALLBACK exactly when its descriptor is an algorithm control;
every other control is a VALUE slot. -/
theorem control_position_role_follows_its_kind
    (metadata : SequenceBuiltinMetadata) (index : Nat) (descriptor : SequenceBuiltinSuffixArgDescriptor)
    (h : metadata.suffixArgs[index]? = some descriptor) :
    metadata.slotRole (index + 1)
      = if descriptor.kind == .algorithm then .callback else .value := by
  simp [SequenceBuiltinMetadata.slotRole, h]

/-- A position past the fixed signature is SURPLUS (that supplying it is an arity error is the
`partial` arity check's, which never consults `slotRole`). -/
theorem position_past_the_signature_is_surplus
    (metadata : SequenceBuiltinMetadata) (slot : Nat) (h : metadata.suffixArgs.length < slot) :
    metadata.slotRole slot = .surplus := by
  have hne : slot ≠ 0 := by omega
  have hnone : metadata.suffixArgs[slot - 1]? = none := by
    simp
    omega
  simp [SequenceBuiltinMetadata.slotRole, hne, hnone]

/-- `reduce`'s `initial` is an ordinary VALUE slot (HO-04), its reducer a CALLBACK. -/
theorem reduce_initial_is_a_value_slot :
    (sequenceBuiltinMetadata? .reduceBuiltin).map (·.slotRole 2) = some .value := by
  rfl

theorem reduce_reducer_is_a_callback_slot :
    (sequenceBuiltinMetadata? .reduceBuiltin).map (·.slotRole 1) = some .callback := by
  rfl

theorem map_mapper_is_a_callback_slot :
    (sequenceBuiltinMetadata? .mapBuiltin).map (·.slotRole 1) = some .callback := by
  rfl

theorem filter_predicate_is_a_callback_slot :
    (sequenceBuiltinMetadata? .filterBuiltin).map (·.slotRole 1) = some .callback := by
  rfl

/-- Builtin call-item assembly evaluates nothing (CALL-02, CALL-03): one item per received
argument, carrying that argument's cell, and no value, recorded failure or projected callable. -/
theorem call_item_assembly_evaluates_nothing (args : List ResolvedArgumentAlgorithm) :
    (collectSequenceCallableCallItems args).map (·.need?) = args.map (·.need?)
    ∧ ∀ item ∈ collectSequenceCallableCallItems args,
        item.value? = none ∧ item.error? = none ∧ item.callable? = none := by
  constructor
  · simp [collectSequenceCallableCallItems]
  · intro item h
    simp only [collectSequenceCallableCallItems, List.mem_map] at h
    obtain ⟨arg, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- A CALLBACK control item WITHOUT a need cell binds the item's algorithm channel, and nothing
else: the item's value and any value failure are never consulted (CALL-03). (Production items
are need-backed: `callback_control_transports_need_address`.) -/
theorem callback_control_binds_only_the_algorithm_channel
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor) (item : CallableCallItem)
    (alg : Algorithm) (hk : descriptor.kind = .algorithm) (ha : item.algorithm? = some alg)
    (hn : item.need? = none) :
    runEvalM (prepareSequenceBuiltinSuffixArgItem b descriptor item)
      = .ok (.algorithm alg) := by
  simp [prepareSequenceBuiltinSuffixArgItem, hk, ha, hn, runEvalM]
  rfl

/-- A suspended callback control transports its address without changing the heap. -/
theorem callback_control_transports_need_address
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor) (item : CallableCallItem)
    (address : Nat) (state : EvalState) (hk : descriptor.kind = .algorithm)
    (hn : item.need? = some address) :
    (prepareSequenceBuiltinSuffixArgItem b descriptor item).run state =
      .ok (.needAlgorithm address, state) := by
  simp [prepareSequenceBuiltinSuffixArgItem, hk, hn]
  rfl

/-- A VALUE control binds the one value its demand established. -/
theorem value_control_binds_its_established_value
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor) (item : CallableCallItem)
    (v : Result) (hk : descriptor.kind = .value) (hv : item.value? = some v) :
    runEvalM (prepareSequenceBuiltinSuffixArgItem b descriptor item) = .ok (.value v) := by
  simp [prepareSequenceBuiltinSuffixArgItem, hk, hv, runEvalM]
  rfl

/-- A VALUE control item carrying ONLY a recorded failure reports that failure: preparation
never evaluates the slot again, so a failure cannot be retried into a different outcome (PV-05 —
`reduce`'s `initial` included). (Production items, whose placeholder algorithm accepts zero
arguments, behave the same by inspection; not proved here.) -/
theorem value_control_reports_a_bare_recorded_failure
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor) (err : Error)
    (hk : descriptor.kind = .value) :
    runEvalM (prepareSequenceBuiltinSuffixArgItem b descriptor { error? := some err })
      = .error err := by
  cases b <;>
    simp [prepareSequenceBuiltinSuffixArgItem, hk, sequenceBuiltinValueDemandErrorWith?,
      CallableCallItem.named?, runEvalM] <;> rfl

/-
## The unified formula-lifting law (decided 2026-09-30)

A resolved callable reference is lifted when its occurrence is used as a VALUE, and its lifting
signature is its resolved callable's contract (`Algorithm.liftingSignature?`), whatever its
category. These are SPECIFICATION laws (the evaluator calls none of `liftingSlotRole`,
`familyLiftingSignature?`, `liftsBareValueReference`): they pin the role table the C# front end
classifies with (`FormulaLiftingRoles`; agreement rests on `UnifiedFormulaLiftingTests`), EXAMPLES
of the derived signature of a clause family (whole-value slots named by the clauses, never an
invented name), and Q-03's complement for user algorithms
(`lifts_bare_value_reference_iff_not_cacheable`) and builtins
(`builtin_reference_lifts_and_is_never_cacheable`); for clause families only the example
`literal_base_family_reference_lifts` is proved.
-/

/-- A family argument is a VALUE role, whatever the position (a static role, retained by
NEED-05; at run time a family demands only what its patterns inspect or its selected body
consumes, PAT-07/NEED-04). -/
theorem family_arguments_are_value_slots (position : Nat) (known : Bool) :
    liftingSlotRole .family position known = .value := by
  cases known <;> rfl

/-- A Math member or a host operation demands every argument's value. -/
theorem strict_value_arguments_are_value_slots (position : Nat) (known : Bool) :
    liftingSlotRole .strictValue position known = .value := by
  cases known <;> rfl

/-- A user callable's whole argument stays neutral (its binder decides at run time; a plain
capture keeps the callable channel), and so does an argument of a callee known only at run time:
`Twice(A)` passes `A` itself. -/
theorem user_and_dynamic_arguments_stay_neutral (position : Nat) (known : Bool) :
    liftingSlotRole .user position known = .callable
    ∧ liftingSlotRole .dynamic position known = .callable := by
  cases known <;> exact ⟨rfl, rfl⟩

/-- A builtin reads its registry roles: `map`'s collection is a value and its mapper a callback
the builtin invokes; `reduce`'s initial accumulator is a value; `if`'s condition and both
branches are values (laziness does not change a role); a loop's step is invoked while its count
and initial state are values; and a SURPLUS position beyond the signature has the static
VALUE role (at run time a surplus slot is never demanded), so no role depends on how many
arguments a call supplies. Thirteen sampled entries of the table. -/
theorem builtin_slot_roles_follow_the_registry :
    liftingSlotRole (.builtin .mapBuiltin) 0 true = .value
    ∧ liftingSlotRole (.builtin .mapBuiltin) 1 true = .callable
    ∧ liftingSlotRole (.builtin .reduceBuiltin) 1 true = .callable
    ∧ liftingSlotRole (.builtin .reduceBuiltin) 2 true = .value
    ∧ liftingSlotRole (.builtin .ifBuiltin) 0 true = .value
    ∧ liftingSlotRole (.builtin .ifBuiltin) 1 true = .value
    ∧ liftingSlotRole (.builtin .ifBuiltin) 2 true = .value
    ∧ liftingSlotRole (.builtin .repeatBuiltin) 0 true = .callable
    ∧ liftingSlotRole (.builtin .repeatBuiltin) 1 true = .value
    ∧ liftingSlotRole (.builtin .sumBuiltin) 0 true = .value
    ∧ liftingSlotRole (.builtin .mapBuiltin) 2 true = .value
    ∧ liftingSlotRole (.builtin .reduceBuiltin) 3 true = .value
    ∧ liftingSlotRole (.builtin .ifBuiltin) 3 true = .value := by
  decide

/-- After a spread slot a position is known only at run time: for EVERY builtin and position,
it is a value slot exactly when every slot of the builtin is one (generalized from two decided
instances, R8/X-13). -/
theorem unknown_builtin_position_is_a_value_iff_every_slot_is (b : Builtin) (position : Nat) :
    liftingSlotRole (.builtin b) position false = .value ↔ builtinEverySlotIsValue b = true := by
  cases h : builtinEverySlotIsValue b <;> simp [liftingSlotRole, h]

example : liftingSlotRole (.builtin .sumBuiltin) 3 false = .value
    ∧ liftingSlotRole (.builtin .mapBuiltin) 3 false = .callable := by
  decide

private def lawBranch (pattern : Pattern) : CondBranch := { pattern := pattern, body := alg [] [] [] [num 0] }

/-- EXAMPLE (family naming): a literal base case names nothing, so the general clause names the one slot:
`G(0) = …` / `G(n) = …` lifts as `G(n)`. -/
theorem family_literal_base_is_named_by_its_general_clause :
    familyLiftingSignature? [lawBranch (.litInt 0), lawBranch (.bind "n")]
      = some [.capture { name := "n" }] := by
  rfl

/-- EXAMPLE: different clauses may name different positions — `P(a, 0)` / `P(0, b)` lifts as `P(a, b)`. -/
theorem family_positions_are_named_by_the_clauses_that_bind_them :
    familyLiftingSignature?
        [lawBranch (.sequenceValue [.bind "a", .litInt 0]), lawBranch (.sequenceValue [.litInt 0, .bind "b"])]
      = some [.capture { name := "a" }, .capture { name := "b" }] := by
  rfl

/-- EXAMPLE: two positions never share one name — `P(a, 0)` / `P(0, a)` has no lifting signature (by-name
lifting would feed one binding to two independent positions). -/
theorem family_one_name_for_two_positions_is_unnameable :
    familyLiftingSignature?
        [lawBranch (.sequenceValue [.bind "a", .litInt 0]), lawBranch (.sequenceValue [.litInt 0, .bind "a"])]
      = none := by
  rfl

/-- EXAMPLE: clauses that name a position differently leave it unnamed — `H(a, 0)` / `H(b, c)`. -/
theorem family_conflicting_names_are_unnameable :
    familyLiftingSignature?
        [lawBranch (.sequenceValue [.bind "a", .litInt 0]), lawBranch (.sequenceValue [.bind "b", .bind "c"])]
      = none := by
  rfl

/-- EXAMPLE: structural and binderless clause patterns are dispatch detail and name nothing — a family of
list patterns alone has no lifting signature, while a capture clause beside binderless groups
names the slot (`F(()) = …` / `F([]) = …` / `F(x) = …` lifts as `F(x)`). -/
theorem structural_clauses_do_not_name_a_slot :
    familyLiftingSignature? [lawBranch (.listValue []), lawBranch (.listValue [.bind "x"])] = none
    ∧ familyLiftingSignature?
        [lawBranch (.sequenceValue [.sequenceValue []]), lawBranch (.listValue []), lawBranch (.bind "x")]
      = some [.capture { name := "x" }] := by
  exact ⟨rfl, rfl⟩

/-- Q-03's complement for BUILTINS (the user case is `lifts_bare_value_reference_iff_not_cacheable`;
no kind-independent theorem is stated): a builtin never accepts a zero-argument call, and its
lifting signature always requires an argument, so the specification always lifts a builtin
reference in a value role. -/
theorem builtin_reference_lifts_and_is_never_cacheable (b : Builtin) :
    Algorithm.acceptsZeroSuppliedArguments (.builtin b) = false
    ∧ liftsBareValueReference (builtinLiftingSignature b) = true := by
  cases b <;> decide

/-- Q-27 payload hygiene, checked against the independent acceptance predicate for every
    builtin: the reported minimum is accepted, positive, and the LEAST accepted supply — every
    smaller supply is rejected (strengthened from the immediately smaller supply alone, R8/X-13). -/
theorem builtin_minimum_payload_is_the_least_accepted_supply (b : Builtin) :
    builtinAcceptsArity b (builtinMinimumArity b) = true
    ∧ builtinMinimumArity b > 0
    ∧ ∀ k, k < builtinMinimumArity b → builtinAcceptsArity b k = false := by
  cases b <;> decide

/-- EXAMPLE: the family `G(0)` / `G(n)` has the lifting signature `[n]`, which the
specification lifts. (Not every nameable family lifts: a host-built zero-arity family has the
signature `[]`, which does not.) -/
theorem literal_base_family_reference_lifts :
    (familyLiftingSignature? [lawBranch (.litInt 0), lawBranch (.bind "n")]).map liftsBareValueReference
      = some true := by
  rfl

/-!
## The generic binder core: specialization and production equations (R3, October 2026)

Since R3 the Model-C binder and the clause search are written ONCE, generically, in
`KatLang.NeedBinder` (`KatLang.lean`), over any monad `m` with `[Monad m] [MonadExceptOf Error m]`
and the three capabilities of `NeedCapabilities m` — VALUE demand, CALLABLE projection and cell
allocation. The production binder the evaluator calls is that core at `EvalM`:

* `bindNeedPatterns c = NeedBinder.bindPatterns c.capabilities` and likewise for every binder
  name (§ Specialization), where `c.capabilities = ⟨c.value, c.callable, allocateNeed⟩`;
* `selectNeedFamilyBranch c callee cells ctx env name =
  NeedBinder.selectFamily c.capabilities callee cells name (needActivateBranch callee ctx env)`.

These are DEFINITIONAL equalities and prove only that there is one implementation. That the
refactor PRESERVED the pre-R3 binder was established once, at implementation time, by
evidence deliberately kept OUT of the maintained proofs (a maintained copy of the old binder
would be a second binder that can drift): kernel proofs that a verbatim copy of the HEAD
091ddca4 binder block equals the new production binder and dispatcher for every channel pair,
pattern list, cell list, family flag, callee, context and value environment — complete `EvalM`
computations, hence every outcome and the complete final `EvalState` — recorded in the R3
implementation evidence (`artifacts/validation/r3-implementation/`, a local validation
directory, not part of the repository). The maintained regression net is the guards and the
Lean/C# corpora.

§ Production equations restates each production BINDER definition's pre-R3 body as a theorem
(by `rfl`; the dispatcher's equation is its form over `chooseBranch` / `needActivateBranch`,
equal to the pre-R3 `let rec` body by the migration evidence), so proofs written against the
monomorphic binder (§ Model-C production binder laws below) keep their shape. § Generic laws
are stated for every monad and capability record: those without `[LawfulMonad m]` hold of
`EvalM`, of the external trace interpretation (`KatLangArityLaws.BinderTrace`) and of any later
interpretation alike; the one that needs `[LawfulMonad m]` holds of the trace interpretation and
has its own `EvalM` form, `production_plain_step`.

Opaque helpers. The core calls helpers that reach `partial` definitions — literal matching
`matchPattern` (via `matchPatternInto`/`matchStructureInto`), repeated callable identity
`sameRepeatedCallableIdentity` (via `sameDeclaringScope`/`compatibleActivations`), the
kind-mismatch payload `structuralPatternKindMismatch` (via `ParameterPattern.displayName` and
`resultDiagnosticString`) and the duplicate-clause check `Algorithm.hasDuplicateBranchPatterns`
(via `Pattern.matchEquivalentWithRenaming`). No theorem here or in the R3 modules unfolds them:
their outcomes appear symbolically, as the very terms the binder computes.
-/

namespace KatLang.BinderCore

/-! ## Specialization: the production binder IS the generic core at `EvalM` -/

theorem production_source_address_is_the_core (source : NeedSource Nat) :
    needSourceAddress source = NeedBinder.sourceAddress allocateNeed source := rfl

theorem production_gate_is_the_core (ps : List NeedPattern) (count : Nat) (family : Bool)
    (accepted : EvalM (Option NeedEnv)) :
    needCardinalityGate ps count family accepted = NeedBinder.cardinalityGate ps count family accepted := rfl

theorem production_name_is_the_core (c : NeedChannels) (name : Ident) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    bindNeedName c name address repeated bound family
      = NeedBinder.bindName c.capabilities name address repeated bound family := rfl

theorem production_one_is_the_core (c : NeedChannels) (p : NeedPattern) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    bindNeedOne c p address repeated bound family
      = NeedBinder.bindOne c.capabilities p address repeated bound family := rfl

theorem production_sources_is_the_core (c : NeedChannels) (ps : List NeedPattern)
    (sources : List (NeedSource Nat)) (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    bindNeedSources c ps sources repeated bound family
      = NeedBinder.bindSources c.capabilities ps sources repeated bound family := rfl

theorem production_level_is_the_core (c : NeedChannels) (ps : List NeedPattern) (cells : List Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    bindNeedLevel c ps cells repeated bound family
      = NeedBinder.bindLevel c.capabilities ps cells repeated bound family := rfl

/-- THE SPECIALIZATION THEOREM: the production binder the evaluator calls at every binding
    site is the generic core at `EvalM` with the production capabilities. -/
theorem production_binder_is_the_core (c : NeedChannels) (ps : List NeedPattern) (cells : List Nat)
    (family : Bool) :
    bindNeedPatterns c ps cells family = NeedBinder.bindPatterns c.capabilities ps cells family := rfl

/-- The production dispatcher is the generic dispatcher with the production capabilities and
    the one activation `needActivateBranch` over the incoming context and values. -/
theorem production_dispatcher_is_the_core (c : NeedChannels) (callee : Algorithm) (cells : List Nat)
    (ctx : EvalCtx) (env : ValEnv) (name : String) :
    selectNeedFamilyBranch c callee cells ctx env name
      = NeedBinder.selectFamily c.capabilities callee cells name (needActivateBranch callee ctx env) := rfl

/-! ## Production equations: the pre-R3 bodies, as theorems -/

theorem needSourceAddress_cell (address : Nat) :
    needSourceAddress (.cell address) = pure address := rfl

theorem needSourceAddress_collector (slice : List Nat) :
    needSourceAddress (.collector slice) = allocateNeed (.collector slice) := rfl

theorem needSourceAddress_missing :
    needSourceAddress .missing = (throw Error.badArity : EvalM Nat) := rfl

theorem needCardinalityGate_eq (ps : List NeedPattern) (count : Nat) (family : Bool)
    (accepted : EvalM (Option NeedEnv)) :
    needCardinalityGate ps count family accepted =
      if !needAcceptsCardinality ps count then
        if family then pure none
        else throw (Error.arityMismatch (needMinimumSuppliedSlots ps) count)
      else accepted := rfl

theorem bindNeedName_eq (c : NeedChannels) (name : Ident) (address : Nat) (repeated : List Ident)
    (bound : NeedEnv) (family : Bool) :
    bindNeedName c name address repeated bound family = (do
      if repeated.contains name then
        let value <- c.value address
        if let some previous := lookupAssoc name bound then
          let before <- c.value previous
          if !(before == value) then
            if family then return none
            else throw (Error.withContext (repeatedParameterContext name) Error.badArity)
          let first <- c.callable previous
          let second <- c.callable address
          if let some a := first then
            if let some b := second then
              if !sameRepeatedCallableIdentity a b then
                if family then return none
                else throw (Error.typeMismatch "Repeated bind equality requires the same callable identity")
          if first.isSome || second.isNone then return some bound
      pure (some (bound.filter (fun entry => entry.fst != name) ++ [(name, address)])) : EvalM (Option NeedEnv)) := rfl

theorem bindNeedOne_bind (c : NeedChannels) (name : Ident) (collecting : Bool) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    bindNeedOne c (.bind name collecting) address repeated bound family
      = bindNeedName c name address repeated bound family := rfl

theorem bindNeedOne_literal (c : NeedChannels) (literal : Pattern) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    bindNeedOne c (.literal literal) address repeated bound family = (do
      let (value, _) <- c.value address
      pure (if (matchPattern literal value).isSome then some bound else none)) := rfl

/-- The structural arms (sequence, list, unpacking receiver) in their pre-R3 form. -/
theorem bindNeedOne_structural (c : NeedChannels) (pattern : NeedPattern) (ps : List NeedPattern)
    (hp : pattern = .sequence ps ∨ pattern = .list ps ∨ pattern = .unpack ps)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    bindNeedOne c pattern address repeated bound family = (do
      let (value, _) <- c.value address
      let items? := match pattern with
        | .list _ => Result.listPatternItems? value
        | .sequence _ => Result.sequencePatternItems? value
        | _ => some (Result.spreadItems value)
      match items? with
      | none => if family then pure none else throw (structuralPatternKindMismatch pattern.toParameter value)
      | some items => do
          let cells <- items.mapM (fun item => readyNeed (item, Result.valueCount item))
          needCardinalityGate ps cells.length family
            (bindNeedSources c ps (needLevelSources ps cells) repeated bound family)) := by
  rcases hp with rfl | rfl | rfl <;> rfl

theorem bindNeedSources_nil (c : NeedChannels) (sources : List (NeedSource Nat))
    (repeated : List Ident) (current : NeedEnv) (family : Bool) :
    bindNeedSources c [] sources repeated current family = pure (some current) := rfl

theorem bindNeedSources_cons (c : NeedChannels) (p : NeedPattern) (rest : List NeedPattern)
    (sources : List (NeedSource Nat)) (repeated : List Ident) (current : NeedEnv) (family : Bool) :
    bindNeedSources c (p :: rest) sources repeated current family = (do
      let address <- needSourceAddress (sources.headD .missing)
      match <- bindNeedOne c p address repeated current family with
      | none => pure none
      | some next => bindNeedSources c rest sources.tail repeated next family) := rfl

theorem bindNeedLevel_eq (c : NeedChannels) (ps : List NeedPattern) (cells : List Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    bindNeedLevel c ps cells repeated bound family
      = needCardinalityGate ps cells.length family
          (bindNeedSources c ps (needLevelSources ps cells) repeated bound family) := rfl

theorem bindNeedPatterns_eq (c : NeedChannels) (ps : List NeedPattern) (cells : List Nat) (family : Bool) :
    bindNeedPatterns c ps cells family = bindNeedLevel c ps cells (needRepeatedNames ps) [] family := rfl

/-- The production clause search: `NeedBinder.chooseBranch` over the production binder and
    activation. -/
theorem chooseBranch_production_cons (c : NeedChannels) (callee : Algorithm) (cells : List Nat)
    (ctx : EvalCtx) (env : ValEnv) (name : String) (branch : CondBranch) (rest : List CondBranch) :
    NeedBinder.chooseBranch c.capabilities cells name (needActivateBranch callee ctx env) (branch :: rest)
      = (do
          match <- bindNeedPatterns c (needClauseHead branch.pattern) cells true with
          | none => NeedBinder.chooseBranch c.capabilities cells name (needActivateBranch callee ctx env) rest
          | some bindings => needActivateBranch callee ctx env branch bindings) := rfl

theorem selectNeedFamilyBranch_eq (c : NeedChannels) (callee : Algorithm) (cells : List Nat)
    (ctx : EvalCtx) (env : ValEnv) (name : String) :
    selectNeedFamilyBranch c callee cells ctx env name = (do
      if callee.hasDuplicateBranchPatterns then throw Error.duplicateBranchPattern
      let branches := Algorithm.branches callee
      if !branches.any (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) cells.length) then
        throw (Error.arityMismatch ((branches.head?.map (fun branch => needMinimumSuppliedSlots (needClauseHead branch.pattern))).getD 0) cells.length)
      NeedBinder.chooseBranch c.capabilities cells name (needActivateBranch callee ctx env) branches) := rfl

/-! ## Generic laws: every monad, every capability record

A theorem here without `[LawfulMonad m]` holds of the production `EvalM` binder (by
§ Specialization) and of every other interpretation of the one core. A theorem needing the monad
laws states `[LawfulMonad m]` and so applies to lawful interpretations such as the trace monad;
`EvalM` has no such global instance (none is needed by the R3 results), so its counterpart is
proved directly from `EvalM.pure_bind` (`production_plain_step`). -/

section Generic

variable {m : Type → Type} [Monad m] [MonadExceptOf Error m]

/-- A non-repeated name TRANSPORTS its cell: no VALUE demand, no CALLABLE projection, no
    allocation — the pure environment update, in every interpretation and either mode. -/
theorem core_plain_name_is_pure (k : NeedCapabilities m) (name : Ident) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (h : repeated.contains name = false) :
    NeedBinder.bindName k name address repeated bound family
      = pure (some (bound.filter (fun entry => entry.fst != name) ++ [(name, address)])) := by
  simp only [NeedBinder.bindName, h, Bool.false_eq_true, ↓reduceIte]

/-- An unaccepted count at a level is rejected by the gate alone, in every interpretation:
    the family non-match `pure none`, otherwise the arity error with the level's minimum and
    the complete supply count. The level's patterns never run. -/
theorem core_level_rejects_unaccepted_count (k : NeedCapabilities m) (ps : List NeedPattern)
    (cells : List Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool)
    (h : needAcceptsCardinality ps cells.length = false) :
    NeedBinder.bindLevel k ps cells repeated bound family
      = if family then pure none
        else throw (Error.arityMismatch (needMinimumSuppliedSlots ps) cells.length) := by
  simp only [NeedBinder.bindLevel, NeedBinder.cardinalityGate, h, Bool.not_false, ↓reduceIte]

/-- MIXED-HEAD PLAIN STEP, every lawful interpretation: a non-repeated name bound from a
    supplied cell contributes exactly the environment update, and the arbitrary remaining
    traversal — nested, repeated, literal, collecting, allocating — runs unchanged after it.
    The occurrence itself uses no capability; a LATER pattern may still demand the same
    address. -/
theorem core_plain_step [LawfulMonad m] (k : NeedCapabilities m) (name : Ident) (collecting : Bool)
    (address : Nat) (rest : List NeedPattern) (sources : List (NeedSource Nat)) (repeated : List Ident)
    (bound : NeedEnv) (family : Bool) (h : repeated.contains name = false) :
    NeedBinder.bindSources k (.bind name collecting :: rest) (.cell address :: sources) repeated bound family
      = NeedBinder.bindSources k rest sources repeated
          (bound.filter (fun entry => entry.fst != name) ++ [(name, address)]) family := by
  simp only [NeedBinder.bindSources, NeedBinder.sourceAddress, NeedBinder.bindOne, NeedBinder.bindName,
    h, Bool.false_eq_true, ↓reduceIte, pure_bind, List.headD_cons, List.tail_cons]

end Generic

/-- MIXED-HEAD PLAIN STEP at the production binder (`EvalM` has no `LawfulMonad` instance; its
    own `EvalM.pure_bind` suffices): a non-repeated name bound from a supplied cell is exactly its
    environment update, for every channel pair, any remaining patterns and either mode. -/
theorem production_plain_step (c : NeedChannels) (name : Ident) (collecting : Bool) (address : Nat)
    (rest : List NeedPattern) (sources : List (NeedSource Nat)) (repeated : List Ident) (bound : NeedEnv)
    (family : Bool) (h : repeated.contains name = false) :
    bindNeedSources c (.bind name collecting :: rest) (.cell address :: sources) repeated bound family
      = bindNeedSources c rest sources repeated
          (bound.filter (fun entry => entry.fst != name) ++ [(name, address)]) family := by
  rw [bindNeedSources_cons, List.headD_cons, needSourceAddress_cell, EvalM.pure_bind, bindNeedOne_bind,
    production_name_is_the_core, core_plain_name_is_pure _ _ _ _ _ _ h, EvalM.pure_bind]
  rfl

end KatLang.BinderCore

/-
## Model-C production binder laws (FORMAL-07, October 2026)

Since October 2026 the Model-C binder is a TOTAL definition of `KatLang.lean` —
`bindNeedName`, `bindNeedOne`/`bindNeedSources` (structural over the written patterns),
`bindNeedLevel`, `bindNeedPatterns` and the clause-family dispatcher `selectNeedFamilyBranch`
— parametrized by the two capabilities of a supplied cell (`NeedChannels`: VALUE demand and
CALLABLE projection). The evaluator recursion core instantiates every one of them with
`⟨demandNeedRecursive, projectNeedCallable⟩`. Every binder law below that takes a `channels` argument is
stated for ALL channels, so it holds of whatever channels a caller passes — in particular of
that instantiation. The other laws concern the binder's channel-free parts (the allocation
`needLevelSources` and the cardinality gate `needAcceptsCardinality`), the laws-file helpers
`plainNeedBinding`, `NeedSource.map`, `needPatternOfAlgebra` and `NeedSource.algebraValue`, the
paper algebra's correspondence with the allocation, or `makeCollectionListResult`.

What they do NOT establish:
* that the evaluator calls these definitions with `⟨demandNeedRecursive, projectNeedCallable⟩` — the
  call sites are bodies of `partial` defs, so that link is a fact of the source (and of every
  guard that runs a call), not of the kernel;
* the behavior of the opaque recursive driver `demandNeedRecursive` or `evalCounted`.
  Since R5, supply formation BEFORE the top-level gate and collector/completion control
  are total (`NeedSupply`, `NeedDemand`). Their public `formNeedSupplySourced`,
  `formNeedSupply` and `demandNeed` specializations, ordered exact-list materialization,
  failure retention and qualified completion publication are proved in
  `KatLangArityLaws/NeedControl.lean`. Public `demandNeed` is one unfolding of the same
  `NeedDemand.step` used by the partial driver; this does not prove the recursive edge
  or whole-run heap refinement;
* in THIS section, the order of the VALUE demands and CALLABLE projections made by inspecting
  occurrences (repeated names, literals, structural patterns), or the nested levels' gates
  (they run after the container's VALUE demand and after its item cells are allocated;
  `nested_*_level_*` below only identify them with `bindNeedLevel`) — since R3 that order is
  proved in `KatLangArityLaws/BinderTrace.lean` over the external boundary trace, the
  clause search and activation in `KatLangArityLaws/FamilyDispatch.lean`, and channel
  substitution and the family/ordinary mode correspondence in
  `KatLangArityLaws/BinderCorrespondence.lean`;
* outcomes decided by helpers that call `partial` definitions and are therefore opaque:
  literal matching (`matchPattern`), repeated callable identity
  (`sameRepeatedCallableIdentity`), the kind-mismatch payload
  (`structuralPatternKindMismatch`) and the duplicate-clause check
  (`Algorithm.hasDuplicateBranchPatterns`);
* the bound ENVIRONMENT for repeated names (allocation is position-only; the repeated-name
  verdict is `repeated_name_binding` in `KatLangArityLaws/BinderTrace.lean`), or anything
  about C#.

The precondition "at most one collecting binding per pattern level" is the pre-evaluation
gate `validateAlgorithmTree` (X-02); that every binder input passed that gate is an
executable invariant, not a theorem.
-/

/-! ### Minimum supply: the binder's count is the signature's count -/

private theorem collecting_count_is_binder_collector_count (ps : List ParameterPattern) :
    ParameterPattern.collectingCaptureCountAtCurrentLevel ps
      = ((ps.map NeedPattern.ofParameter).filter NeedPattern.isCollecting).length := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      cases p with
      | capture parameter =>
          cases h : parameter.kind <;>
            simp [ParameterPattern.collectingCaptureCountAtCurrentLevel, NeedPattern.ofParameter,
              NeedPattern.isCollecting, List.filter_cons, h, ih] <;> omega
      | sequenceValue items =>
          simpa [ParameterPattern.collectingCaptureCountAtCurrentLevel, NeedPattern.ofParameter,
            NeedPattern.isCollecting, List.filter_cons] using ih
      | listValue items =>
          simpa [ParameterPattern.collectingCaptureCountAtCurrentLevel, NeedPattern.ofParameter,
            NeedPattern.isCollecting, List.filter_cons] using ih
      | unpacking items =>
          simpa [ParameterPattern.collectingCaptureCountAtCurrentLevel, NeedPattern.ofParameter,
            NeedPattern.isCollecting, List.filter_cons] using ih

private theorem has_collecting_iff_count_pos (ps : List ParameterPattern) :
    ParameterPattern.hasCollectingCaptureAtCurrentLevel ps = true
      ↔ 0 < ParameterPattern.collectingCaptureCountAtCurrentLevel ps := by
  induction ps with
  | nil =>
      simp [ParameterPattern.hasCollectingCaptureAtCurrentLevel,
        ParameterPattern.collectingCaptureCountAtCurrentLevel]
  | cons p rest ih =>
      cases p with
      | capture parameter =>
          cases h : parameter.kind <;>
            simp_all [ParameterPattern.hasCollectingCaptureAtCurrentLevel,
              ParameterPattern.collectingCaptureCountAtCurrentLevel] <;> omega
      | sequenceValue items =>
          simpa [ParameterPattern.hasCollectingCaptureAtCurrentLevel,
            ParameterPattern.collectingCaptureCountAtCurrentLevel] using ih
      | listValue items =>
          simpa [ParameterPattern.hasCollectingCaptureAtCurrentLevel,
            ParameterPattern.collectingCaptureCountAtCurrentLevel] using ih
      | unpacking items =>
          simpa [ParameterPattern.hasCollectingCaptureAtCurrentLevel,
            ParameterPattern.collectingCaptureCountAtCurrentLevel] using ih

/-- The pre-evaluation gate's own predicate (`Algorithm.hasMultipleCollectingCaptures`,
    checked by `validateAlgorithmTree`) bounds a signature's TOP level to one collector. -/
theorem collector_gate_bounds_the_top_level (ps : List ParameterPattern)
    (h : ParameterPattern.hasMultipleCollectingCapturesAtAnyLevel ps = false) :
    ParameterPattern.collectingCaptureCountAtCurrentLevel ps ≤ 1 := by
  simp only [ParameterPattern.hasMultipleCollectingCapturesAtAnyLevel, Bool.or_eq_false_iff,
    decide_eq_false_iff_not] at h
  omega

/-- THE ONE MINIMUM (the docstring claim of `ParameterPattern.minimumSuppliedSlots`, now a
    theorem): on a signature with at most one top-level collector, the production binder's
    own count `needMinimumSuppliedSlots` — its arity payload and its acceptance bound — IS
    the signature-level `minimumSuppliedSlots` that the zero-argument demand law, Q-03
    lifting and the property cache read. -/
theorem binder_minimum_is_the_signature_minimum (ps : List ParameterPattern)
    (h : ParameterPattern.collectingCaptureCountAtCurrentLevel ps ≤ 1) :
    needMinimumSuppliedSlots (ps.map NeedPattern.ofParameter)
      = ParameterPattern.minimumSuppliedSlots ps := by
  have hc := collecting_count_is_binder_collector_count ps
  have hp := has_collecting_iff_count_pos ps
  unfold needMinimumSuppliedSlots ParameterPattern.minimumSuppliedSlots
  rw [List.length_map, ← hc]
  by_cases hh : ParameterPattern.hasCollectingCaptureAtCurrentLevel ps = true
  · have := hp.mp hh
    simp [hh]; omega
  · have : ParameterPattern.collectingCaptureCountAtCurrentLevel ps = 0 := by
      have := mt hp.mpr hh; omega
    simp [hh, this]

/-- The precondition is necessary: with two collectors at one level the two counts differ
    (such a signature is refused before evaluation, X-02). -/
theorem binder_minimum_differs_on_two_collectors :
    needMinimumSuppliedSlots
        ([.capture { name := "a", kind := .collecting }, .capture { name := "b", kind := .collecting }]
          |>.map NeedPattern.ofParameter) = 0
    ∧ ParameterPattern.minimumSuppliedSlots
        [.capture { name := "a", kind := .collecting }, .capture { name := "b", kind := .collecting }]
      = 1 := by
  simp [needMinimumSuppliedSlots, NeedPattern.ofParameter, NeedPattern.isCollecting, List.filter_cons,
    ParameterPattern.minimumSuppliedSlots, ParameterPattern.hasCollectingCaptureAtCurrentLevel]

/-- The binder's cardinality GATE accepts the EMPTY supply exactly when the minimum is zero
(gate acceptance is not successful binding: see `two_collectors_misallocate`). -/
theorem cardinality_gate_accepts_empty_supply_iff_minimum_zero (ps : List NeedPattern) :
    needAcceptsCardinality ps 0 = true ↔ needMinimumSuppliedSlots ps = 0 := by
  unfold needAcceptsCardinality needMinimumSuppliedSlots
  constructor
  · intro h; simp at h; omega
  · intro h
    simp
    constructor
    · omega
    · by_cases hany : ps.any NeedPattern.isCollecting = true
      · exact Or.inl (by simpa using hany)
      · right
        have hall : ∀ p ∈ ps, NeedPattern.isCollecting p = false := by
          intro p hp; have := hany; simp at this; simpa using this p hp
        have : (ps.filter NeedPattern.isCollecting) = [] := by
          rw [List.filter_eq_nil_iff]; intro p hp; simp [hall p hp]
        rw [this] at h; simp at h; simp [h]

/-- ZERO-ARGUMENT VALUE DEMAND FOLLOWS ACTUAL CALL ARITY, user algorithms with at most one
    top-level collector (every signature the X-02 gate admits, `collector_gate_bounds_the_top_level`;
    the hypothesis is necessary, `binder_minimum_differs_on_two_collectors`): the acceptance rule
    `Algorithm.acceptsZeroSuppliedArguments` (zero-argument demand, Q-03, the cache) is exactly
    the production binder's cardinality gate on the empty supply — the gate
    `evalZeroArgumentDemandOutputCounted` then runs. -/
theorem zero_argument_acceptance_is_the_binder_gate (parent : Option ScopeCtx)
    (ps : List ParameterPattern) (opens : List Expr) (props : List PropDef) (out : OutputBundle)
    (identity : Option PropertyIdentity)
    (h : ParameterPattern.collectingCaptureCountAtCurrentLevel ps ≤ 1) :
    Algorithm.acceptsZeroSuppliedArguments (.mk parent ps opens props out identity)
      = needAcceptsCardinality (ps.map NeedPattern.ofParameter) 0 := by
  have hacc := cardinality_gate_accepts_empty_supply_iff_minimum_zero (ps.map NeedPattern.ofParameter)
  rw [binder_minimum_is_the_signature_minimum ps h] at hacc
  simp only [Algorithm.acceptsZeroSuppliedArguments, Algorithm.parameterPatterns]
  cases hb : needAcceptsCardinality (ps.map NeedPattern.ofParameter) 0
  · have : ParameterPattern.minimumSuppliedSlots ps ≠ 0 := fun hz => by
      have := hacc.mpr hz; rw [hb] at this; exact Bool.false_ne_true this
    simp [this]
  · have := hacc.mp hb
    simp [this]

private theorem single_head_accepts_one (q : NeedPattern) (n : Nat) (hq : q.isCollecting = false) :
    needAcceptsCardinality [q] n = (1 == n) := by
  simp only [needAcceptsCardinality, needMinimumSuppliedSlots, List.filter_cons, hq,
    List.filter_nil, List.any_cons, List.any_nil, List.length_singleton]
  rw [Bool.eq_iff_iff]
  simp
  omega

/-- A clause head's cardinality gate is its top-level arity: clause binders never collect. -/
theorem clause_head_accepts_exactly_its_top_level_arity (p : Pattern) (n : Nat) :
    needAcceptsCardinality (needClauseHead p) n = (Pattern.topLevelArity p == n) := by
  have hcoll : ∀ q : Pattern, NeedPattern.isCollecting (NeedPattern.ofClause q) = false := by
    intro q; cases q <;> simp [NeedPattern.ofClause, NeedPattern.isCollecting]
  cases p with
  | sequenceValue ps =>
      have hf : (ps.map NeedPattern.ofClause).filter NeedPattern.isCollecting = [] := by
        rw [List.filter_eq_nil_iff]; intro q hq
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
        simp [hcoll r]
      have hany : (ps.map NeedPattern.ofClause).any NeedPattern.isCollecting = false := by
        rw [List.any_eq_false]; intro q hq
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
        simp [hcoll r]
      simp only [needAcceptsCardinality, needMinimumSuppliedSlots, needClauseHead, hf, hany,
        Pattern.topLevelArity, List.length_map, List.length_nil, Nat.sub_zero, Bool.false_or]
      cases hn : (n == ps.length) <;> cases hm : (ps.length == n) <;> simp_all <;> omega
  | bind x =>
      simp only [needClauseHead, Pattern.topLevelArity]; exact single_head_accepts_one _ n (hcoll _)
  | litInt i =>
      simp only [needClauseHead, Pattern.topLevelArity]; exact single_head_accepts_one _ n (hcoll _)
  | litString str =>
      simp only [needClauseHead, Pattern.topLevelArity]; exact single_head_accepts_one _ n (hcoll _)
  | litBool b =>
      simp only [needClauseHead, Pattern.topLevelArity]; exact single_head_accepts_one _ n (hcoll _)
  | listValue ps =>
      simp only [needClauseHead, Pattern.topLevelArity]; exact single_head_accepts_one _ n (hcoll _)

/-- ZERO-ARGUMENT VALUE DEMAND FOLLOWS ACTUAL CALL ARITY, clause families: a family accepts
    the zero-argument demand exactly when the production dispatcher's gate
    (`selectNeedFamilyBranch`: some head accepts the supply count) accepts zero cells. -/
theorem family_zero_argument_acceptance_is_the_dispatch_gate (parent : Option ScopeCtx)
    (opens : List Expr) (branches : List CondBranch) (identity : Option PropertyIdentity) :
    Algorithm.acceptsZeroSuppliedArguments (.conditional parent opens branches identity)
      = branches.any (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) 0) := by
  simp only [Algorithm.acceptsZeroSuppliedArguments, clause_head_accepts_exactly_its_top_level_arity]

/-! ### The cardinality gate precedes every effect -/

/-- CARDINALITY PRECEDES DEMAND (NEED-05, CALL-04, PAT-10(1)), production binder, the TOP
    LEVEL of an ordinary call (`bindNeedPatterns` calls `bindNeedLevel`; supply formation has
    already run): an unaccepted supply count is the arity error whose payload is the level's
    minimum and the COMPLETE supply count, and the binder has done NOTHING — whatever the
    channels are, no cell was demanded or projected, nothing was allocated, the run state is
    unchanged. A nested level's gate is the same `bindNeedLevel`
    (`nested_sequence_level_is_bind_need_level`), reached after the container's VALUE demand
    and the allocation of its item cells. -/
theorem binder_rejects_unaccepted_supply_before_any_effect (channels : NeedChannels)
    (ps : List NeedPattern) (cells : List Nat) (repeated : List Ident) (bound : NeedEnv)
    (h : needAcceptsCardinality ps cells.length = false) (state : EvalState) :
    (bindNeedLevel channels ps cells repeated bound false).runState state
      = (.error (Error.arityMismatch (needMinimumSuppliedSlots ps) cells.length), state) := by
  simp [BinderCore.bindNeedLevel_eq, BinderCore.needCardinalityGate_eq, h]
  rfl

/-- In a clause attempt the same unaccepted count is a NON-MATCH, again before any effect. -/
theorem family_binder_treats_unaccepted_supply_as_a_non_match (channels : NeedChannels)
    (ps : List NeedPattern) (cells : List Nat) (repeated : List Ident) (bound : NeedEnv)
    (h : needAcceptsCardinality ps cells.length = false) :
    bindNeedLevel channels ps cells repeated bound true = pure none := by
  simp [BinderCore.bindNeedLevel_eq, BinderCore.needCardinalityGate_eq, h]

/-- The top-level entry point the evaluator calls. -/
theorem call_binder_rejects_unaccepted_supply_before_any_effect (channels : NeedChannels)
    (ps : List NeedPattern) (cells : List Nat) (h : needAcceptsCardinality ps cells.length = false)
    (state : EvalState) :
    (bindNeedPatterns channels ps cells).runState state
      = (.error (Error.arityMismatch (needMinimumSuppliedSlots ps) cells.length), state) :=
  binder_rejects_unaccepted_supply_before_any_effect channels ps cells _ [] h state

/-- A FAMILY REPORTS `NoMatchingBranch` ONLY FOR AN ACCEPTED COUNT (NEED-05, CALL-04): when
    no clause head accepts the supply count, production dispatch fails before any clause is
    attempted and before any effect — with the duplicate-clause error if the family has
    duplicate heads (checked first; the check calls `partial` definitions, so it is opaque), and
    otherwise with the arity error whose payload is the first clause's minimum and the
    complete supply count. Never `noMatchingBranch`. -/
theorem family_dispatch_rejects_unaccepted_supply_before_any_effect (channels : NeedChannels)
    (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (hnone : (Algorithm.branches callee).any
      (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) cells.length) = false)
    (state : EvalState) :
    (selectNeedFamilyBranch channels callee cells ctx env name).runState state
      = (.error (if callee.hasDuplicateBranchPatterns then Error.duplicateBranchPattern
          else Error.arityMismatch
            (((Algorithm.branches callee).head?.map
              (fun branch => needMinimumSuppliedSlots (needClauseHead branch.pattern))).getD 0)
            cells.length), state) := by
  cases hdup : callee.hasDuplicateBranchPatterns
  · simp [BinderCore.selectNeedFamilyBranch_eq, hdup, hnone]; rfl
  · simp [BinderCore.selectNeedFamilyBranch_eq, hdup]; rfl

/-- The nested level a SEQUENCE pattern opens is bound by the same `bindNeedLevel` — gate,
    allocation and patterns — after its container's VALUE demand and kind check, over fresh
    ready cells holding the opened items. -/
theorem nested_sequence_level_is_bind_need_level (channels : NeedChannels) (ps : List NeedPattern)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    bindNeedOne channels (.sequence ps) address repeated bound family = (do
      let (value, _) <- channels.value address
      match Result.sequencePatternItems? value with
      | none =>
          if family then pure none else throw (structuralPatternKindMismatch (NeedPattern.sequence ps).toParameter value)
      | some items => do
          let cells <- items.mapM (fun item => readyNeed (item, Result.valueCount item))
          bindNeedLevel channels ps cells repeated bound family) := by
  rfl

/-- The LIST pattern's twin of `nested_sequence_level_is_bind_need_level`. -/
theorem nested_list_level_is_bind_need_level (channels : NeedChannels) (ps : List NeedPattern)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    bindNeedOne channels (.list ps) address repeated bound family = (do
      let (value, _) <- channels.value address
      match Result.listPatternItems? value with
      | none =>
          if family then pure none else throw (structuralPatternKindMismatch (NeedPattern.list ps).toParameter value)
      | some items => do
          let cells <- items.mapM (fun item => readyNeed (item, Result.valueCount item))
          bindNeedLevel channels ps cells repeated bound family) := by
  rfl

/-- The deconstruction UNPACKING receiver's level: the demanded value's one-level items
    (`Result.spreadItems`, never a kind mismatch) bound by `bindNeedLevel`. -/
theorem nested_unpack_level_is_bind_need_level (channels : NeedChannels) (ps : List NeedPattern)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    bindNeedOne channels (.unpack ps) address repeated bound family = (do
      let (value, _) <- channels.value address
      let cells <- (Result.spreadItems value).mapM (fun item => readyNeed (item, Result.valueCount item))
      bindNeedLevel channels ps cells repeated bound family) := by
  rfl

/-! ### Allocation: each pattern its cell, the collector its exact slice -/

theorem need_level_sources_length {α : Type} (ps : List NeedPattern) (cells : List α) :
    (needLevelSources ps cells).length = ps.length := by
  simp [needLevelSources]

/-- Without a collector and with exactly as many cells as patterns, pattern `i` is bound from
supplied cell `i`. -/
theorem need_level_sources_without_collector {α : Type} (ps : List NeedPattern) (cells : List α)
    (hnone : ps.findIdx? NeedPattern.isCollecting = none) (hlen : cells.length = ps.length) :
    needLevelSources ps cells = cells.map NeedSource.cell := by
  apply List.ext_getElem
  · simp [needLevelSources, hlen]
  · intro i h1 h2
    simp only [needLevelSources, hnone, List.getElem_map, List.getElem_range, needSourceAt]
    simp at h2
    simp [h2]

/-- AROUND THE COLLECTOR (VAR-02, any lengths and any number of fixed patterns on either side):
    with the level's first collector at `c` and enough
    cells, the patterns before it take the leading `c` cells, the collector takes the exact
    slice of `n + 1 - L` cells after them, and the patterns after it take the remaining
    trailing cells, in order. -/
theorem need_level_sources_around_the_collector {α : Type} (ps : List NeedPattern)
    (cells : List α) (c : Nat) (hc : ps.findIdx? NeedPattern.isCollecting = some c)
    (hlen : ps.length ≤ cells.length + 1) :
    needLevelSources ps cells
      = (cells.take c).map NeedSource.cell
          ++ NeedSource.collector ((cells.drop c).take (cells.length + 1 - ps.length))
          :: (cells.drop (c + (cells.length + 1 - ps.length))).map NeedSource.cell := by
  have hcl : c < ps.length := (List.findIdx?_eq_some_iff_getElem.mp hc).1
  apply List.ext_getElem
  · simp [needLevelSources]; omega
  · intro i h1 h2
    simp only [needLevelSources, hc, List.getElem_map, List.getElem_range, needSourceAt]
    simp only [needLevelSources, List.length_map, List.length_range] at h1
    by_cases hlt : i < c
    · rw [List.getElem_append_left (by simp; omega)]
      have hne : (some c == some i) = false := by simp; omega
      have hnot : ¬ c < i := by omega
      have hi : i < cells.length := by omega
      simp [hne, hnot, List.getElem?_eq_getElem hi]
    · have htake : (List.map NeedSource.cell (List.take c cells)).length = c := by simp; omega
      by_cases heq : i = c
      · subst heq
        rw [List.getElem_append_right (by omega)]
        simp only [htake, Nat.sub_self, List.getElem_cons_zero]
        simp
      · have hgt : c < i := by omega
        have hne : (some c == some i) = false := by simp; omega
        rw [List.getElem_append_right (by omega)]
        have hk : i - (List.map NeedSource.cell (List.take c cells)).length = (i - c - 1) + 1 := by
          rw [htake]; omega
        have hidx : i + (cells.length + 1 - ps.length) - 1 < cells.length := by omega
        simp only [hk, List.getElem_cons_succ, List.getElem_map, List.getElem_drop]
        simp [hne, hgt, List.getElem?_eq_getElem hidx]
        congr 1
        omega

/-- Reading the cells of a source through `f`. -/
def KatLang.NeedSource.map {α β : Type} (f : α -> β) : NeedSource α -> NeedSource β
  | .cell value => .cell (f value)
  | .collector slice => .collector (slice.map f)
  | .missing => .missing

private theorem need_source_at_map {α β : Type} (f : α -> β) (col : Option Nat) (extra : Nat)
    (cells : List α) (i : Nat) :
    needSourceAt col extra (cells.map f) i = (needSourceAt col extra cells i).map f := by
  unfold needSourceAt
  by_cases hc : (col == some i) = true
  · simp [hc, NeedSource.map, List.map_drop, List.map_take]
  · simp only [hc, Bool.false_eq_true, if_false]
    generalize (if (Option.map (fun j => decide (i > j)) col).getD false = true
      then i + extra - 1 else i) = k
    rw [List.getElem?_map]
    cases cells[k]? <;> rfl

/-- ALLOCATION IS PARAMETRIC: it depends only on positions, never on what a cell holds, so
    allocating need addresses and then reading what they hold equals allocating the held
    values directly. -/
theorem need_level_sources_are_parametric {α β : Type} (f : α -> β) (ps : List NeedPattern)
    (cells : List α) :
    needLevelSources ps (cells.map f) = (needLevelSources ps cells).map (NeedSource.map f) := by
  simp only [needLevelSources, List.length_map, List.map_map]
  congr 1
  funext i
  simp [need_source_at_map]

private theorem cell_sources_cover_their_cells {α : Type} (xs : List α) :
    (xs.map NeedSource.cell).flatMap NeedSource.items = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [NeedSource.items] at ih ⊢; exact ih

/-- SUPPLY CONSERVATION (CALL-04, VAR-01/02, NEED-07): on an accepted supply of a level with
    at most one collector, the allocated sources cover EXACTLY the supplied cells, each once,
    in written order — no cell dropped, duplicated or reordered — and no position is missing. -/
theorem need_level_sources_conserve_the_supply {α : Type} (ps : List NeedPattern)
    (cells : List α) (hgate : (ps.filter NeedPattern.isCollecting).length ≤ 1)
    (haccept : needAcceptsCardinality ps cells.length = true) :
    (needLevelSources ps cells).flatMap NeedSource.items = cells
    ∧ NeedSource.missing ∉ needLevelSources ps cells := by
  unfold needAcceptsCardinality needMinimumSuppliedSlots at haccept
  simp at haccept
  cases hc : ps.findIdx? NeedPattern.isCollecting with
  | none =>
      have hall : ∀ p ∈ ps, NeedPattern.isCollecting p = false := List.findIdx?_eq_none_iff.mp hc
      have hany : ¬ ∃ x ∈ ps, NeedPattern.isCollecting x = true := by
        intro ⟨x, hx, hxc⟩; simp [hall x hx] at hxc
      have hlen : cells.length = ps.length := by
        rcases haccept with ⟨_, h | h⟩
        · exact absurd h hany
        · exact h
      rw [need_level_sources_without_collector ps cells hc hlen]
      exact ⟨cell_sources_cover_their_cells cells, by simp⟩
  | some c =>
      have hpos : 0 < (ps.filter NeedPattern.isCollecting).length := by
        obtain ⟨hcl, hcoll, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hc
        apply List.length_pos_of_mem
        exact List.mem_filter.mpr ⟨List.getElem_mem hcl, hcoll⟩
      have hlen : ps.length ≤ cells.length + 1 := by omega
      rw [need_level_sources_around_the_collector ps cells c hc hlen]
      refine ⟨?_, ?_⟩
      · simp only [List.flatMap_append, List.flatMap_cons, NeedSource.items,
          cell_sources_cover_their_cells]
        have hsplit : (cells.drop c).take (cells.length + 1 - ps.length)
            ++ cells.drop (c + (cells.length + 1 - ps.length)) = cells.drop c := by
          rw [← List.drop_drop, List.take_append_drop]
        rw [hsplit, List.take_append_drop]
      · intro hmem
        simp only [List.mem_append, List.mem_cons, List.mem_map] at hmem
        rcases hmem with ⟨a, _, ha⟩ | hcol | ⟨a, _, ha⟩
        · cases ha
        · cases hcol
        · cases ha

/-- The gate is load-bearing: two collectors at one level pass the binder's own cardinality
    check, yet the second collector receives ONE raw cell (never a list), or no cell at all
    (`badArity`). The pre-evaluation gate (X-02, `validateAlgorithmTree`) refuses such a
    signature before evaluation. -/
theorem two_collectors_misallocate :
    needAcceptsCardinality [.bind "a" true, .bind "b" true] 3 = true
    ∧ needLevelSources [.bind "a" true, .bind "b" true] [10, 11, 12]
        = [NeedSource.collector [10, 11], NeedSource.cell 12]
    ∧ needAcceptsCardinality [.bind "a" true, .bind "b" true] 0 = true
    ∧ needLevelSources [.bind "a" true, .bind "b" true] ([] : List Nat)
        = [NeedSource.collector [], NeedSource.missing] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-! ### Plain binding transports cells and demands nothing -/

/-- A non-repeated name TRANSPORTS its cell: no VALUE demand, no CALLABLE projection,
    whatever the channels and in either mode (NEED-01, NEED-03). -/
theorem binder_name_transports_a_non_repeated_cell (channels : NeedChannels) (name : Ident)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool)
    (h : repeated.contains name = false) :
    bindNeedName channels name address repeated bound family
      = pure (some (bound.filter (fun entry => entry.fst != name) ++ [(name, address)])) := by
  rw [BinderCore.production_name_is_the_core]
  exact BinderCore.core_plain_name_is_pure _ _ _ _ _ _ h

/-- The name a plain binder pattern binds (a collecting binding included). -/
def KatLang.NeedPattern.plainName? : NeedPattern -> Option Ident
  | .bind name _ => some name
  | _ => none

/-- The program a level of plain binders runs: each name receives the address of its source
    (`needSourceAddress`: a supplied cell is transported, a collector slice gets one fresh
    suspended collector cell). Neither channel appears. -/
def plainNeedBinding : List Ident -> List (NeedSource Nat) -> NeedEnv -> EvalM (Option NeedEnv)
  | [], _, current => pure (some current)
  | name :: rest, sources, current => do
      let address <- needSourceAddress (sources.headD .missing)
      plainNeedBinding rest sources.tail
        (current.filter (fun entry => entry.fst != name) ++ [(name, address)])

/-- PLAIN BINDING DEMANDS NOTHING (NEED-01, NEED-03, CALL-06, VAR-03), production binder: a
    level of plain, non-repeated binders — fixed or collecting — runs `plainNeedBinding`,
    whatever the channels and whatever the mode. -/
theorem plain_patterns_bind_without_any_channel (channels : NeedChannels) (ps : List NeedPattern)
    (names : List Ident) (hnames : ps.map NeedPattern.plainName? = names.map some)
    (repeated : List Ident) (hrepeated : ∀ name ∈ names, repeated.contains name = false)
    (sources : List (NeedSource Nat)) (current : NeedEnv) (family : Bool) :
    bindNeedSources channels ps sources repeated current family
      = plainNeedBinding names sources current := by
  induction ps generalizing names sources current with
  | nil =>
      cases names with
      | nil => simp [BinderCore.bindNeedSources_nil, plainNeedBinding]
      | cons _ _ => simp at hnames
  | cons p rest ih =>
      cases names with
      | nil => simp at hnames
      | cons n names' =>
          simp only [List.map_cons, List.cons.injEq] at hnames
          obtain ⟨hp, hrest⟩ := hnames
          cases p with
          | bind name c =>
              simp [NeedPattern.plainName?] at hp
              subst hp
              have hn : repeated.contains name = false := hrepeated name (by simp)
              have hr' : ∀ m ∈ names', repeated.contains m = false :=
                fun m hm => hrepeated m (by simp [hm])
              simp only [BinderCore.bindNeedSources_cons, plainNeedBinding, BinderCore.bindNeedOne_bind,
                binder_name_transports_a_non_repeated_cell channels _ _ _ _ _ hn]
              congr 1
              funext address
              simp [ih names' hrest hr']
          | sequence _ => simp [NeedPattern.plainName?] at hp
          | list _ => simp [NeedPattern.plainName?] at hp
          | unpack _ => simp [NeedPattern.plainName?] at hp
          | literal _ => simp [NeedPattern.plainName?] at hp

/-- Corollary at the entry point the evaluator calls: a head of plain binders binding no name
    twice gives the same outcome AND the same run state under any two channel pairs — so the
    production instantiation `⟨demandNeedRecursive, projectNeedCallable⟩` demands and projects
    nothing while binding it. -/
theorem plain_head_binding_is_channel_independent (first second : NeedChannels)
    (ps : List NeedPattern) (names : List Ident)
    (hnames : ps.map NeedPattern.plainName? = names.map some)
    (hdistinct : needRepeatedNames ps = []) (cells : List Nat) (family : Bool) :
    bindNeedPatterns first ps cells family = bindNeedPatterns second ps cells family := by
  have hr : ∀ name ∈ names, ([] : List Ident).contains name = false := by simp
  simp only [BinderCore.bindNeedPatterns_eq, BinderCore.bindNeedLevel_eq, hdistinct,
    plain_patterns_bind_without_any_channel first ps names hnames [] hr,
    plain_patterns_bind_without_any_channel second ps names hnames [] hr]

/-! ### The arity algebra IS the production allocation -/

/-- The algebra's binder patterns as production binder patterns. -/
def needPatternOfAlgebra : CoreArityAlgebra.Pat -> NeedPattern
  | .name s => .bind s false
  | .collecting s => .bind s true

/-- What an algebra-level source denotes: a fixed item, or the exact collected list. -/
def KatLang.NeedSource.algebraValue : NeedSource CoreArityAlgebra.Val -> CoreArityAlgebra.Val
  | .cell value => value
  | .collector slice => CoreArityAlgebra.collect slice
  | .missing => CoreArityAlgebra.Val.seq []

private theorem need_pattern_of_algebra_is_collecting (p : CoreArityAlgebra.Pat) :
    NeedPattern.isCollecting (needPatternOfAlgebra p) = CoreArityAlgebra.Pat.isCollecting p := by
  cases p <;> rfl

private theorem need_pattern_of_algebra_collector_count (ps : List CoreArityAlgebra.Pat) :
    ((ps.map needPatternOfAlgebra).filter NeedPattern.isCollecting).length
      = (ps.filter CoreArityAlgebra.Pat.isCollecting).length := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      cases p <;> simp_all [List.filter_cons, needPatternOfAlgebra, NeedPattern.isCollecting,
        CoreArityAlgebra.Pat.isCollecting]

private theorem need_pattern_of_algebra_first_collector (ps : List CoreArityAlgebra.Pat) :
    (ps.map needPatternOfAlgebra).findIdx? NeedPattern.isCollecting
      = ps.findIdx? CoreArityAlgebra.Pat.isCollecting := by
  rw [List.findIdx?_map]
  congr 1
  funext p
  exact need_pattern_of_algebra_is_collecting p

/-- REFINEMENT FROM THE ALGEBRA (Q-66 "refinement from `bindArgs`"; FORMAL-07): the paper
    algebra's binder `CoreArityAlgebra.bindPats` — hence `bindArgs` and `bindCallback`, which
    are it by definition — is EXACTLY the production ALLOCATION `needLevelSources` read at
    algebra values (`NeedSource.algebraValue`: a fixed pattern its item, the collector
    `collect` of its slice), and it is defined EXACTLY when the level has at most one collector
    (the X-02 condition) and the production cardinality gate accepts. So a `bindPats` theorem
    of `CoreArityAlgebraProofs.lean` is a theorem about this allocation under that guard. It is
    NOT a theorem about the production binder's result: the algebra models no repeated-name
    constraint (on a head that repeats a name `bindPats` binds every occurrence positionally,
    while the production binder compares them, NEED-04), no structural or literal pattern, and
    no `demandNeed`; with two collectors the production allocation misallocates
    (`two_collectors_misallocate`) and only the pre-evaluation gate rejects. -/
theorem algebra_binder_is_the_production_allocation (ps : List CoreArityAlgebra.Pat)
    (xs : CoreArityAlgebra.Supply) :
    CoreArityAlgebra.bindPats ps xs =
      if (ps.filter CoreArityAlgebra.Pat.isCollecting).length ≤ 1
          ∧ needAcceptsCardinality (ps.map needPatternOfAlgebra) xs.length = true then
        some (List.zipWith (fun p source => (p.key, NeedSource.algebraValue source)) ps
          (needLevelSources (ps.map needPatternOfAlgebra) xs))
      else none := by
  have hfl := need_pattern_of_algebra_collector_count ps
  unfold CoreArityAlgebra.bindPats
  unfold needAcceptsCardinality needMinimumSuppliedSlots
  rw [hfl]
  split
  · rename_i hnil
    have hnone : ps.findIdx? CoreArityAlgebra.Pat.isCollecting = none := by
      rw [List.findIdx?_eq_none_iff]
      intro p hp
      have : p ∉ ps.filter CoreArityAlgebra.Pat.isCollecting := by rw [hnil]; simp
      simpa [List.mem_filter, hp] using this
    have hany : (ps.map needPatternOfAlgebra).any NeedPattern.isCollecting = false := by
      have := List.findIdx?_eq_none_iff.mp
        (by rw [need_pattern_of_algebra_first_collector]; exact hnone)
      simpa using this
    simp only [hnil, List.length_nil, hany, List.length_map]
    by_cases hlen : ps.length = xs.length
    · have hsrc := need_level_sources_without_collector (ps.map needPatternOfAlgebra) xs
        (by rw [need_pattern_of_algebra_first_collector]; exact hnone) (by simp [hlen])
      simp [hlen, hsrc, CoreArityAlgebra.bindFixed, List.zipWith_map_right,
        NeedSource.algebraValue]
    · simp [hlen]
      omega
  · rename_i cp hcp
    obtain ⟨i, hi⟩ : ∃ i, ps.findIdx? CoreArityAlgebra.Pat.isCollecting = some i := by
      cases h : ps.findIdx? CoreArityAlgebra.Pat.isCollecting with
      | some i => exact ⟨i, rfl⟩
      | none =>
        exfalso
        have hall := List.findIdx?_eq_none_iff.mp h
        have hmem : cp ∈ ps.filter CoreArityAlgebra.Pat.isCollecting := by rw [hcp]; simp
        rw [List.mem_filter] at hmem
        simp [hall cp hmem.1] at hmem
    obtain ⟨hil, hicoll, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
    have hkey : ps[i] = cp := by
      have hmem : ps[i] ∈ ps.filter CoreArityAlgebra.Pat.isCollecting :=
        List.mem_filter.mpr ⟨List.getElem_mem hil, hicoll⟩
      rw [hcp] at hmem; simpa using hmem
    have hany : (ps.map needPatternOfAlgebra).any NeedPattern.isCollecting = true := by
      rw [List.any_eq_true]
      exact ⟨needPatternOfAlgebra ps[i], List.mem_map.mpr ⟨ps[i], List.getElem_mem hil, rfl⟩,
        by rw [need_pattern_of_algebra_is_collecting]; exact hicoll⟩
    simp only [hi]
    by_cases hshort : xs.length < ps.length - 1
    · rw [if_pos hshort, if_neg (by rw [hcp]; simp [hany]; omega)]
    · have hlen : ps.length ≤ xs.length + 1 := by omega
      rw [if_neg hshort, if_pos (by rw [hcp]; simp [hany]; omega)]
      congr 1
      rw [need_level_sources_around_the_collector (ps.map needPatternOfAlgebra) xs i
        (by rw [need_pattern_of_algebra_first_collector]; exact hi) (by simp; omega)]
      simp only [List.length_map]
      conv => rhs; rw [← List.take_append_drop i ps, List.drop_eq_getElem_cons hil]
      rw [List.zipWith_append (by simp; omega)]
      simp only [List.zipWith_cons_cons, hkey, NeedSource.algebraValue, CoreArityAlgebra.bindFixed,
        List.zipWith_map_right, List.length_drop]
      have e1 : xs.length - (ps.length - (i + 1)) = i + (xs.length + 1 - ps.length) := by omega
      have e3 : (List.take i ps ++ cp :: List.drop (i + 1) ps).length = ps.length := by
        simp; omega
      have e4 : i + (xs.length + 1 - ps.length) - i = xs.length + 1 - ps.length := by omega
      rw [e1, e3, e4]
  · rename_i hne0 hne1
    have hge : 2 ≤ (ps.filter CoreArityAlgebra.Pat.isCollecting).length := by
      cases h : ps.filter CoreArityAlgebra.Pat.isCollecting with
      | nil => exact absurd h hne0
      | cons a t =>
          cases t with
          | nil => exact absurd h (hne1 a)
          | cons b u => simp
    have : ¬ (ps.filter CoreArityAlgebra.Pat.isCollecting).length ≤ 1 := by omega
    simp [this]

/-- `makeCollectionListResult` is `collectSegment` at emitted count 1. R5 connects the total
    public `demandNeed` collector arm to `NeedDemand.materialize` by the kernel theorem
    `KatLang.NeedControl.Production.collector_specialization`; that helper constructs exactly
    this list of demanded slice values (`KatLang.NeedControl.Production.collector_success`).
    The partial `demandNeedRecursive` driver's use of the same shell remains source/guard
    evidence. Several collection builtins return this constructor too. -/
theorem make_collection_list_result_is_collect_segment (items : List Result) :
    makeCollectionListResult items = (collectSegment items, 1) := rfl

/-! ### Production collector and dot-receiver laws (R8/X-13, October 2026)

The production Model-C binder binds supply CELLS, so its collector law is value-blind: what a
cell holds — a sequence, a list, `()`, `[]`, a scalar, a failing computation — cannot change how
it is allocated or bound. These laws state the binder half of the exact collector law and of the
dot-receiver laws (§ Exact collector laws, § Dot-receiver bridge laws) for every channel pair.
They presuppose supply formation: the total `NeedSupply` core forms ONE cell per written
non-spread argument — a dot receiver included — and transports known-slice addresses or
allocates Ready cells for computed-spread items. R5 proves these formation contracts and the
public `formNeedSupply` specialization in `KatLangArityLaws/NeedControl.lean`. The partial
evaluator's use of that core at `evalCounted` remains source/guard evidence, pinned by CoreTests
`ModelC` / `ExplicitValueOpening` / `DotReceiverSegments`.
-/

/-- A LONE COLLECTOR COLLECTS EVERY SUPPLIED CELL, in order, whatever the cells hold: a lone
written argument (a dot receiver included) is ONE collected item, two written arguments two items,
`n` spread items `n` items, and the empty supply the empty slice. -/
theorem lone_collector_collects_every_supplied_cell {α : Type} (name : Ident) (cells : List α) :
    needLevelSources [.bind name true] cells = [.collector cells] := by
  rw [need_level_sources_around_the_collector [.bind name true] cells 0 rfl (by simp)]
  simp

/-- A collector before one fixed pattern: the fixed pattern takes the LAST cell and the collector
every cell before it — a lone receiver cell goes to the fixed pattern, leaving the collector the
empty slice. -/
theorem collector_before_a_fixed_pattern_takes_all_but_the_last_cell {α : Type}
    (collector fixed : Ident) (front : List α) (last : α) :
    needLevelSources [.bind collector true, .bind fixed false] (front ++ [last])
      = [.collector front, .cell last] := by
  rw [need_level_sources_around_the_collector _ _ 0 rfl (by simp)]
  simp

/-- A lone collecting head BINDS by allocating ONE fresh suspended collector cell over exactly the
supplied cells, for every channel pair and in either mode: nothing is demanded or projected, and
no cell is reopened. With `make_collection_list_result_is_collect_segment`, the collector's value
(through the total `NeedDemand.materialize` helper, with public `demandNeed` specialization
and collector success proved in `KatLangArityLaws/NeedControl.lean`) is the exact list of the
cells' values. The partial recursive driver's wiring remains source/guard evidence. This is the
production face of the exact collector law and of collecting-parameter forwarding's target
(`Target(*ys)` re-collects exactly the cells `xs*` transported). -/
theorem lone_collecting_head_allocates_one_collector_over_its_supply (channels : NeedChannels)
    (name : Ident) (cells : List Nat) (family : Bool) :
    bindNeedPatterns channels [.bind name true] cells family
      = (do
          let address <- allocateNeed (.collector cells)
          pure (some [(name, address)])) := by
  have hr : needRepeatedNames [.bind name true] = [] := by
    simp [needRepeatedNames, NeedPattern.names]
  have hacc : needAcceptsCardinality [.bind name true] cells.length = true := by
    simp [needAcceptsCardinality, needMinimumSuppliedSlots, NeedPattern.isCollecting, List.filter_cons]
  have hplain := plain_patterns_bind_without_any_channel channels [.bind name true] [name] rfl []
    (by simp) [.collector cells] [] family
  rw [BinderCore.bindNeedPatterns_eq, BinderCore.bindNeedLevel_eq, BinderCore.needCardinalityGate_eq]
  rw [hr, hacc, lone_collector_collects_every_supplied_cell]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [hplain]
  simp [plainNeedBinding, BinderCore.needSourceAddress_collector]

/-- ONE CELL NEVER SATISFIES TWO FIXED PATTERNS: a one-cell supply against `[a, *r, z]` fails with
`arityMismatch 2 1` and leaves the run state unchanged, for every channel pair — so the cell (a dot
receiver's, say) is never demanded or projected, and however many items its value holds plays no
part (the production form of "the receiver's item count never satisfies arity"). -/
theorem one_cell_supply_fails_two_fixed_patterns_before_any_effect (channels : NeedChannels)
    (a r z : Ident) (cell : Nat) (state : EvalState) :
    (bindNeedPatterns channels [.bind a false, .bind r true, .bind z false] [cell]).runState state
      = (.error (Error.arityMismatch 2 1), state) :=
  call_binder_rejects_unaccepted_supply_before_any_effect channels _ [cell] (by rfl) state

/-! ## String interpolation (STR-02, VAL-12)

`interpolateWith` is the TOTAL combinator that the evaluator's `.interpolatedString` arm
instantiates with the ordinary value read of each hole (`fun hole => eval hole ctx env`). It is
defined above the `partial` evaluator block, so the laws below are kernel-checked theorems about
the combinator itself, each for the channels it quantifies over: every monad and channel
(`interpolate_hole_free_is_its_text`, `interpolate_step`), every `EvalM` channel (the failure,
continuation and trace laws), pure `Id` channels (`interpolate_pure_holes_concatenate`), the
laws-local `recordingHole` (`interpolate_evaluates_each_hole_once_in_order`), and no channel for
`canonical_text_*`. That the evaluator arm passes exactly that read is a source fact, pinned by the
`#guard`s of `CoreTests.Strings` and the `ParityGuards` evaluation-projection probes — the
FORMAL-07 caveat: no theorem here unfolds `evalCounted`. The number text is this model's
integer tier (`toString`); the Decimal128 canonical text, the string limits and the lexical
grammar (quotes, escapes, `{{`/`}}`, hole-level restrictions) are C#-only. -/

/-- A HOLE-FREE interpolation is its text: nothing is evaluated. -/
theorem interpolate_hole_free_is_its_text {m : Type → Type} [Monad m] (value : Expr → m Result)
    (head : String) :
    interpolateWith value head [] = pure head := rfl

/-- One step: the FIRST hole is evaluated through the channel, its structural text and then its
    link's literal text are appended, and only then do the remaining links run. -/
theorem interpolate_step {m : Type → Type} [Monad m] (value : Expr → m Result) (acc : String)
    (link : InterpolationLink) (rest : List InterpolationLink) :
    interpolateWith value acc (link :: rest)
      = (value link.hole >>= fun holeValue =>
          interpolateWith value (acc ++ Result.canonicalText holeValue ++ link.text) rest) := rfl

/-- With a pure (effect-free, total) hole channel the result is the left-to-right
    concatenation of the head, each hole's structural text and each link's text. -/
theorem interpolate_pure_holes_concatenate (f : Expr → Result) (acc : String)
    (links : List InterpolationLink) :
    interpolateWith (m := Id) (fun hole => pure (f hole)) acc links
      = links.foldl (fun text link => text ++ Result.canonicalText (f link.hole) ++ link.text) acc := by
  induction links generalizing acc with
  | nil => rfl
  | cons link rest ih => exact ih _

/-- THE FIRST FAILURE ENDS IT (`EvalM`): a hole whose evaluation fails ends the whole
    interpolation with that hole's error and the state that hole left — no later hole runs. -/
theorem interpolate_failing_hole_ends_it (value : Expr → EvalM Result) (acc : String)
    (link : InterpolationLink) (rest : List InterpolationLink) (err : Error) (state state' : EvalState)
    (h : (value link.hole).runState state = (.error err, state')) :
    (interpolateWith value acc (link :: rest)).runState state = (.error err, state') := by
  show ((value link.hole).runState >>= fun a => (interpolateWith value _ rest).runState) state = _
  simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, h]
  rfl

/-- A hole that succeeds hands its text and the state it left to the rest of the run. -/
theorem interpolate_successful_hole_continues (value : Expr → EvalM Result) (acc : String)
    (link : InterpolationLink) (rest : List InterpolationLink) (holeValue : Result) (state state' : EvalState)
    (h : (value link.hole).runState state = (.ok holeValue, state')) :
    (interpolateWith value acc (link :: rest)).runState state
      = (interpolateWith value (acc ++ Result.canonicalText holeValue ++ link.text) rest).runState state' := by
  show ((value link.hole).runState >>= fun a => (interpolateWith value _ rest).runState) state = _
  simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, h]

/-- The explicit trace of an interpolation run in `EvalM`: each hole's channel runs ONCE, in
    written order, from the state its predecessor left; a successful hole's text is appended at
    once; the first error ends the run with that hole's error and state. -/
def interpolationTrace (value : Expr → EvalM Result) :
    String → List InterpolationLink → EvalState → Except Error String × EvalState
  | acc, [], state => (.ok acc, state)
  | acc, link :: rest, state =>
      match (value link.hole).runState state with
      | (.ok holeValue, state') =>
          interpolationTrace value (acc ++ Result.canonicalText holeValue ++ link.text) rest state'
      | (.error err, state') => (.error err, state')

/-- LEFT TO RIGHT, EACH HOLE EXACTLY ONCE, FIRST FAILURE STOPS (`EvalM`, VAL-12): running the
    combinator IS its explicit trace (`interpolationTrace`), for every hole channel. -/
theorem interpolate_runs_as_its_trace (value : Expr → EvalM Result) (acc : String)
    (links : List InterpolationLink) (state : EvalState) :
    (interpolateWith value acc links).runState state = interpolationTrace value acc links state := by
  induction links generalizing acc state with
  | nil => rfl
  | cons link rest ih =>
      cases h : (value link.hole).runState state with
      | mk result state' =>
          cases result with
          | ok holeValue =>
              rw [interpolate_successful_hole_continues value acc link rest holeValue state state' h, ih]
              simp [interpolationTrace, h]
          | error err =>
              rw [interpolate_failing_hole_ends_it value acc link rest err state state' h]
              simp [interpolationTrace, h]

/-- A hole channel that records every hole it is asked to evaluate. -/
def recordingHole (f : Expr → Result) (hole : Expr) : StateM (List Expr) Result := do
  modify (· ++ [hole])
  pure (f hole)

/-- EACH HOLE EXACTLY ONCE, IN WRITTEN ORDER: with a recording channel the record of evaluated
    holes is exactly the holes as written, each once, and the text is their concatenation. -/
theorem interpolate_evaluates_each_hole_once_in_order (f : Expr → Result) (acc : String)
    (links : List InterpolationLink) (log : List Expr) :
    (interpolateWith (recordingHole f) acc links).run log
      = (links.foldl (fun text link => text ++ Result.canonicalText (f link.hole) ++ link.text) acc,
         log ++ links.map InterpolationLink.hole) := by
  induction links generalizing acc log with
  | nil => simp [interpolateWith]; rfl
  | cons link rest ih =>
      simp [interpolateWith, recordingHole, ih]

/-! ### The structural text of a hole value (`Result.canonicalText`) -/

/-- A string is inserted VERBATIM: never quoted, never re-scanned for holes. -/
theorem canonical_text_of_a_string_is_the_string (s : String) :
    Result.canonicalText (.str s) = s := by
  simp [Result.canonicalText]

/-- A Boolean is its keyword, the spelling of the literal. -/
theorem canonical_text_of_a_boolean_is_its_keyword (b : Bool) :
    Result.canonicalText (.bool b) = Result.boolText b := by
  simp [Result.canonicalText]

/-- A number is the text the `.string` intrinsic writes for it (this model's integer tier). -/
theorem canonical_text_of_a_number_is_the_string_intrinsic_text (n : Int) :
    resultToString (.atom n) = pure (.str (Result.canonicalText (.atom n))) := by
  simp [resultToString, Result.canonicalText]

/-- The empty sequence is `()` and the empty list `[]`: two different texts, never empty
    text — an empty value is a value, not missing output. -/
theorem canonical_text_of_the_empty_sequence : Result.canonicalText (.sequenceValue []) = "()" := by
  simp [Result.canonicalText]

theorem canonical_text_of_the_empty_list : Result.canonicalText (.listValue []) = "[]" := by
  simp [Result.canonicalText]

/-- A sequence keeps its parentheses and a list its brackets, elements separated by `, `, at
    every nesting level (nothing is spread, flattened or quoted). -/
theorem canonical_text_of_a_sequence (rs : List Result) :
    Result.canonicalText (.sequenceValue rs) = "(" ++ ", ".intercalate (rs.map Result.canonicalText) ++ ")" := by
  simp [Result.canonicalText]

theorem canonical_text_of_a_list (rs : List Result) :
    Result.canonicalText (.listValue rs) = "[" ++ ", ".intercalate (rs.map Result.canonicalText) ++ "]" := by
  simp [Result.canonicalText]
