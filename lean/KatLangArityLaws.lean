import KatLang

open KatLang

/-
# KatLangArityLaws

Selected arity laws proved directly over the authoritative `KatLang.lean` model.

`CoreArityAlgebra.lean` defines the small paper-facing algebra, while
`CoreArityAlgebraProofs.lean` proves its small laws and executable checks.
This file is the bridge: it proves the load-bearing laws over real KatLang
`Result` constructors, normalization, lone-sequence item-supply opening, and
real binding helpers.
-/

/--
Paper-facing alias for the real `Result` expression used to canonicalize captured
item supplies: `Result.normalize (Result.sequenceValue xs)`.

This alias lets the bridge file state compact laws over the authoritative
`Result` constructors. The binder-path theorem below should be used when citing
that real rest/variadic binding applies this capture expression.
-/
def captureForArityLaw (xs : List Result) : Result :=
  Result.normalize (Result.sequenceValue xs)

/-- Single rest-shaped signature used to expose the non-opaque variadic splitter. -/
def singleVariadicSignatureForArityLaw : CallableSignature :=
  { name := "F", parameters := [{ name := "x", kind := .variadic }] }

theorem empty_sequence_is_sequenceValue_empty :
    buildEmptySequenceValue 0 = Result.sequenceValue [] := by
  rfl

theorem normalize_empty_sequenceValue :
    Result.normalize (Result.sequenceValue []) = Result.sequenceValue [] := by
  simp [Result.normalize]

theorem empty_sequence_depth_is_canonical :
    buildEmptySequenceValue 1 = Result.sequenceValue [] := by
  rfl

theorem normalize_nested_empty_sequence :
    Result.normalize (Result.sequenceValue [Result.sequenceValue []]) = Result.sequenceValue [] := by
  simp [Result.normalize]

theorem toItems_sequenceValue (xs : List Result) :
    Result.toItems (Result.sequenceValue xs) = xs := by
  rfl

/-
The real model uses capture = Result.normalize after Result.sequenceValue.
This alias theorem is intentionally small; `bindParameterPatternList_single_rest_binds_capture`
is the theorem that connects the real binder path to this expression. Capture is
not raw grouping: singleton capture collapses.
-/
theorem captureForArityLaw_eq_normalize_sequenceValue (xs : List Result) :
    captureForArityLaw xs = Result.normalize (Result.sequenceValue xs) := by
  rfl

theorem capture_eq_normalize_sequenceValue (xs : List Result) :
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
Function-call parameter binding never uses this view. Assignment
deconstruction opens its single right-hand side value through a different
mechanism: the sequence-value parameter pattern (`.sequenceValue`), not the
builtin collection view (see the deconstruction bridge laws at the end of
this file).
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

private theorem collectValues_valueInputs (xs : List Result) :
    bindParameterPatternList.collectValues
      (xs.map (fun value => { value? := some value : ParameterPatternInput }))
      = pure xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [bindParameterPatternList.collectValues, ih]

private theorem drop_length_valueInputs (xs : List Result) :
    List.drop xs.length
      (xs.map (fun value => { value? := some value : ParameterPatternInput })) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem take_length_valueInputs (xs : List Result) :
    List.take xs.length
      (xs.map (fun value => { value? := some value : ParameterPatternInput })) =
      xs.map (fun value => { value? := some value : ParameterPatternInput }) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem bindPairs_nil_nil
    (outerPatterns : List ParameterPattern) (outerInputs : List ParameterPatternInput)
    (allowAlgorithmBindings : Bool)
    (merge : ParameterPatternBindings -> ParameterPatternBindings -> EvalM ParameterPatternBindings) :
    bindParameterPatternList.bindPairs outerPatterns outerInputs allowAlgorithmBindings merge [] [] =
      pure {} := by
  simp [bindParameterPatternList.bindPairs]

/--
The real parameter-pattern binder uses the capture expression directly for a
single top-level variadic/rest capture. This is the binder-path bridge theorem:
the successful binding records `x` as `Result.normalize (Result.sequenceValue xs)`.
-/
theorem bindParameterPatternList_single_rest_binds_capture
    (xs : List Result) (allowAlgorithmBindings : Bool) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .variadic }]
      (xs.map (fun value => { value? := some value : ParameterPatternInput }))
      allowAlgorithmBindings)
      = .ok { argEnv := [("x", Result.normalize (Result.sequenceValue xs))],
              countedParamEnv := [("x", (Result.normalize (Result.sequenceValue xs), xs.length))],
              variadicSupplyEnv := [("x", (Result.normalize (Result.sequenceValue xs), xs.length))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindPairs_nil_nil, collectValues_valueInputs, drop_length_valueInputs, take_length_valueInputs,
    runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup]
  rfl

theorem variadic_single_rest_binds_capture (xs : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .variadic }]
      (xs.map (fun value => { value? := some value : ParameterPatternInput }))
      false)
      = .ok { argEnv := [("x", captureForArityLaw xs)],
              countedParamEnv := [("x", (captureForArityLaw xs, xs.length))],
              variadicSupplyEnv := [("x", (captureForArityLaw xs, xs.length))],
              algEnv := [] } := by
  simpa [captureForArityLaw] using
    bindParameterPatternList_single_rest_binds_capture xs false

theorem bindCallableArguments_single_variadic_items (xs : List Result) :
    bindCallableArguments
      singleVariadicSignatureForArityLaw
      xs
      (fun required actual => Error.arityMismatch required actual)
      (some 0)
      = .ok { normalBindings := [], variadicName? := some "x", variadicItems := xs } := by
  unfold singleVariadicSignatureForArityLaw
  have hvalid :
      CallableSignature.validationError?
        { name := "F", parameters := [{ name := "x", kind := .variadic }] } = none := by
    decide
  simp [bindCallableArguments, CallableSignature.validate, hvalid,
    CallableSignature.variadicIndex?, CallableSignature.variadicIndex?.go.eq_2]

theorem bindCallableArguments_variadic_items_then_capture (xs : List Result) :
    (match bindCallableArguments
        singleVariadicSignatureForArityLaw
        xs
        (fun required actual => Error.arityMismatch required actual)
        (some 0) with
    | .ok bindings => Except.ok (Result.normalize (Result.sequenceValue bindings.variadicItems))
    | .error err => Except.error err)
      = Except.ok (Result.normalize (Result.sequenceValue xs)) := by
  simp [bindCallableArguments_single_variadic_items]

/-
## Deconstruction bridge laws (unpacking receiver)

Assignment deconstruction (`x, y..., z = RHS`) is parser-elaborated into a helper
whose single parameter is a sequence-value pattern (`.sequenceValue [captures]`)
applied to the right-hand side value as one argument. Binding through the real
`bindParameterPatternList`, that pattern OPENS its single received value into items
and matches them element-by-element — so `x, y, z = A` unpacks a stored sequence
value `A`. This opening is deconstruction-specific.

Function-call parameter binding, by contrast, is a flat capture list
(`[.capture x, .capture y]`) bound over the SUPPLIED argument stream, which does NOT
open a single sequence argument. The two groups of laws below pin that contrast over
the real binder: deconstruction (the `.sequenceValue` pattern) opens, while a call
(the flat capture list) preserves the single argument.

The single supplied item is the value `A` (a stored sequence value).
-/

-- Function calls: a flat capture list does NOT open a single sequence argument.

/-- `Add(A)`: one supplied item (the stored sequence value) against two fixed
parameters is an arity mismatch. The call binder does not open `A`. -/
theorem call_fixed_single_sequence_rejected :
    runEvalM (bindParameterPatternList
        [.capture { name := "x", kind := .normal }, .capture { name := "y", kind := .normal }]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .error (Error.arityMismatch 2 1) := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic, runEvalM]
  rfl

/-- `G(A)` mixed fixed/rest call: one supplied item, so `first` receives the whole
stored sequence value and `rest` captures nothing — calls never implicitly open. -/
theorem call_rest_single_sequence_preserved :
    runEvalM (bindParameterPatternList
        [.capture { name := "first", kind := .normal }, .capture { name := "rest", kind := .variadic }]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("first", Result.sequenceValue [Result.atom 1, Result.atom 2]),
                         ("rest", Result.sequenceValue [])],
              countedParamEnv := [("rest", (Result.sequenceValue [], 0))],
              variadicSupplyEnv := [("rest", (Result.sequenceValue [], 0))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup,
    Result.normalize]
  rfl

-- Assignment deconstruction: the `.sequenceValue` pattern OPENS its single value.

/-- `x, y = A`: the deconstruction sequence-value pattern opens the single
right-hand-side value, binding `x = 1`, `y = 2`. -/
theorem deconstruct_fixed_single_sequence_opens :
    runEvalM (bindParameterPatternList
        [.sequenceValue [.capture { name := "x", kind := .normal },
                         .capture { name := "y", kind := .normal }]]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("x", Result.atom 1), ("y", Result.atom 2)],
              countedParamEnv := [], variadicSupplyEnv := [], algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM,
    Result.structureItems?, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, ValEnv.lookup]
  rfl

/-- `first, rest... = A`: the deconstruction sequence-value pattern opens `A`, so
`first = 1` and `rest` captures the remaining items as one grouped value `(2, 3)`. -/
theorem deconstruct_rest_single_sequence_opens :
    runEvalM (bindParameterPatternList
        [.sequenceValue [.capture { name := "first", kind := .normal },
                         .capture { name := "rest", kind := .variadic }]]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]) }]
        true)
      = .ok { argEnv := [("first", Result.atom 1),
                         ("rest", Result.sequenceValue [Result.atom 2, Result.atom 3])],
              countedParamEnv := [("rest", (Result.sequenceValue [Result.atom 2, Result.atom 3], 2))],
              variadicSupplyEnv := [("rest", (Result.sequenceValue [Result.atom 2, Result.atom 3], 2))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM, Result.structureItems?, mergeEqualValEnv,
    mergeEqualCountedParamEnv, mergePatternAlgEnv, lookupAssoc,
    CountedParamEnv.lookup, ValEnv.lookup, Result.normalize]
  rfl

/-
## List bridge laws (exact list values)

Exact list values (`Result.listValue`) join the deconstruction opening rule but
remain opaque at ordinary value and call boundaries: `Result.toItems` keeps a
list as one item, while postfix spread (`Result.spreadItems`), the
deconstruction pattern (`Result.structureItems?`), and the post-binding builtin
collection view open one list boundary in their documented contexts. The laws
below pin each decision over the real model, mirroring the sequence laws above.
-/

/-- Spread opens exactly one list boundary: `[1, 2, 3]...` supplies the items. -/
theorem spreadItems_listValue (xs : List Result) :
    (Result.listValue xs).spreadItems = xs := rfl

/-- Spreading the empty list supplies zero items (`[]...` is neutral). -/
theorem spreadItems_empty_list : (Result.listValue []).spreadItems = [] := rfl

/-- Spread on sequence values is unchanged by the list extension. -/
theorem spreadItems_sequenceValue (xs : List Result) :
    (Result.sequenceValue xs).spreadItems = xs := rfl

/-- The non-spread item view keeps a list OPAQUE: a list is one item, so
value boundaries and indexing projection never open it. (The post-binding
builtin collection view opens the bound list through
`builtinCollectionItems`, not through `toItems` — see
`builtinCollectionItems_list` below.) -/
theorem toItems_listValue_opaque (xs : List Result) :
    (Result.listValue xs).toItems = [Result.listValue xs] := rfl

/-- The deconstruction structure view opens a received list to its items. -/
theorem structureItems_listValue (xs : List Result) :
    Result.structureItems? (Result.listValue xs) = some xs := rfl

/-- The deconstruction structure view opens a received sequence value. -/
theorem structureItems_sequenceValue (xs : List Result) :
    Result.structureItems? (Result.sequenceValue xs) = some xs := rfl

/-- Atoms are not openable structures for deconstruction. -/
theorem structureItems_atom (n : Int) :
    Result.structureItems? (Result.atom n) = none := rfl

/-- The post-binding builtin collection view opens a bound list exactly like a
bound sequence value: ONE outer boundary, so `count([1, 2, 3])` counts three
items just as `count((1, 2, 3))` does. Opening is never recursive — nested
lists stay intact as single items (`count((1, [2], 3))` is 3, and a
collection element `[..]` inside the bound collection is one item). The view
applies only AFTER ordinary fixed binding: `count(1, 2, 3)` and
`count([1, 2, 3]...)` are ordinary arity errors, never collections. -/
theorem builtinCollectionItems_list (xs : List Result) :
    builtinCollectionItems (Result.listValue xs) = xs := rfl

theorem builtinCollectionItems_keeps_nested_list_opaque (xs : List Result) :
    builtinCollectionItems
      (Result.sequenceValue [Result.atom 1, Result.listValue xs, Result.atom 3])
      = [Result.atom 1, Result.listValue xs, Result.atom 3] := rfl

/-- Collection-producing builtins materialize EXACT lists: zero kept items form
`[]`, one kept item forms `[item]` (never erased to the item), and the emitted
count is always 1 — the builtin result re-enters arity as one value. -/
theorem makeCollectionListResult_exact (x : Result) :
    makeCollectionListResult [x] = (Result.listValue [x], 1) := rfl

theorem makeCollectionListResult_empty :
    makeCollectionListResult [] = (Result.listValue [], 1) := rfl

/-- Normalization preserves list structure exactly: elements canonicalize but
the list boundary never collapses (`[7]` stays `[7]`). -/
theorem normalize_listValue (xs : List Result) :
    Result.normalize (Result.listValue xs) = Result.listValue (xs.map Result.normalize) := by
  simp [Result.normalize]

/-- A singleton SEQUENCE boundary around a list still collapses: `([1, 2])` is
`[1, 2]`. Parenthesized grouping stays redundant even when the value is a list. -/
theorem normalize_singleton_sequence_of_list (xs : List Result) :
    Result.normalize (Result.sequenceValue [Result.listValue xs])
      = Result.listValue (xs.map Result.normalize) := by
  simp [Result.normalize]

/-- Rest capture stays sequence-shaped: capturing opened list ITEMS groups them
as one canonical sequence value, never a list (`x, rest... = [1, 2, 3]` gives
`rest = (2, 3)`). -/
theorem capture_of_list_items_is_sequence_shaped (a b : Result) :
    captureForArityLaw [a, b] =
      Result.sequenceValue [Result.normalize a, Result.normalize b] :=
  capture_pair a b

-- Function calls: a lone list argument is ONE argument; calls never open lists.

/-- `Add(A)` with a stored LIST `A`: one supplied item against two fixed
parameters is an arity mismatch — the call binder does not open the list. -/
theorem call_fixed_single_list_rejected :
    runEvalM (bindParameterPatternList
        [.capture { name := "x", kind := .normal }, .capture { name := "y", kind := .normal }]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .error (Error.arityMismatch 2 1) := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic, runEvalM]
  rfl

/-- `G(A)` mixed fixed/rest call with a stored LIST `A`: `first` receives the
whole list value and `rest` captures nothing — calls never implicitly open. -/
theorem call_rest_single_list_preserved :
    runEvalM (bindParameterPatternList
        [.capture { name := "first", kind := .normal }, .capture { name := "rest", kind := .variadic }]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("first", Result.listValue [Result.atom 1, Result.atom 2]),
                         ("rest", Result.sequenceValue [])],
              countedParamEnv := [("rest", (Result.sequenceValue [], 0))],
              variadicSupplyEnv := [("rest", (Result.sequenceValue [], 0))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup,
    Result.normalize]
  rfl

-- Assignment deconstruction: the pattern opens a lone LIST exactly like a
-- lone sequence value.

/-- `x, y = [1, 2]`: the deconstruction pattern opens the lone list, binding
`x = 1`, `y = 2` — identical bindings to `x, y = [1, 2]...`. -/
theorem deconstruct_fixed_single_list_opens :
    runEvalM (bindParameterPatternList
        [.sequenceValue [.capture { name := "x", kind := .normal },
                         .capture { name := "y", kind := .normal }]]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("x", Result.atom 1), ("y", Result.atom 2)],
              countedParamEnv := [], variadicSupplyEnv := [], algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM,
    Result.structureItems?, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, ValEnv.lookup]
  rfl

/-- `first, rest... = [1, 2, 3]`: the deconstruction pattern opens the lone
list; `first = 1` and `rest` captures the remaining ITEMS as one canonical
SEQUENCE value `(2, 3)` — rest capture never reconstructs the source list. -/
theorem deconstruct_rest_single_list_opens :
    runEvalM (bindParameterPatternList
        [.sequenceValue [.capture { name := "first", kind := .normal },
                         .capture { name := "rest", kind := .variadic }]]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) }]
        true)
      = .ok { argEnv := [("first", Result.atom 1),
                         ("rest", Result.sequenceValue [Result.atom 2, Result.atom 3])],
              countedParamEnv := [("rest", (Result.sequenceValue [Result.atom 2, Result.atom 3], 2))],
              variadicSupplyEnv := [("rest", (Result.sequenceValue [Result.atom 2, Result.atom 3], 2))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM, Result.structureItems?, mergeEqualValEnv,
    mergeEqualCountedParamEnv, mergePatternAlgEnv, lookupAssoc,
    CountedParamEnv.lookup, ValEnv.lookup, Result.normalize]
  rfl

/-- Lone-list DISAGREEMENT, lone-rest shape: on a lone list supply the lone-rest
pattern — the ONE shape where call binding and deconstruction agree for a lone
sequence value — produces DIFFERENT bindings: call binding captures the list
itself (`rest = [1, 2]`), deconstruction captures its opened items as a
sequence (`rest = (1, 2)`). Lists never satisfy the lone-sequence agreement. -/
theorem lone_rest_list_call_and_deconstruct_differ :
    runEvalM (bindParameterPatternList
        [.capture { name := "rest", kind := .variadic }]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.atom 1, Result.atom 2])],
              countedParamEnv := [("rest", (Result.listValue [Result.atom 1, Result.atom 2], 1))],
              variadicSupplyEnv := [("rest", (Result.listValue [Result.atom 1, Result.atom 2], 1))],
              algEnv := [] }
    ∧ runEvalM (bindParameterPatternList
        [.sequenceValue [.capture { name := "rest", kind := .variadic }]]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("rest", Result.sequenceValue [Result.atom 1, Result.atom 2])],
              countedParamEnv := [("rest", (Result.sequenceValue [Result.atom 1, Result.atom 2], 2))],
              variadicSupplyEnv := [("rest", (Result.sequenceValue [Result.atom 1, Result.atom 2], 2))],
              algEnv := [] } := by
  constructor
  · simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
      mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup,
      Result.normalize]
    rfl
  · simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      bindParameterPattern, runEvalM, Result.structureItems?, mergeEqualValEnv,
      mergeEqualCountedParamEnv, mergePatternAlgEnv, lookupAssoc,
      CountedParamEnv.lookup, ValEnv.lookup, Result.normalize]
    rfl

/-
## Canonical-form laws (general theorems over the real model)

The laws above pin specific shapes over the real binder paths; the theorems
below establish the general canonical-form story of `Result.normalize` over the
authoritative model:

* `normalize_idempotent` — `Result.normalize` is a projection onto canonical
  values;
* `orphanFree_normalize` — canonical values contain no redundant singleton
  sequence boundary anywhere in their tree (no literal-unwritable "orphans");
* `captureForArityLaw_canonical` / `captureForArityLaw_orphanFree` — the real
  capture expression only ever produces canonical, orphan-free values;
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

/-- Capture canonicity over the real capture expression: a captured item supply
is already canonical, so capture is a fixed point of `Result.normalize`
(corollary of `normalize_idempotent`, since
`captureForArityLaw xs = Result.normalize (Result.sequenceValue xs)`). -/
theorem captureForArityLaw_canonical (xs : List Result) :
    (captureForArityLaw xs).normalize = captureForArityLaw xs :=
  normalize_idempotent (Result.sequenceValue xs)

/-- The real capture expression never mints an orphan: every captured value is
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
  | sequenceValue rs =>
      rw [toItems_sequenceValue]
      exact h
  | listValue rs =>
      show captureForArityLaw [Result.listValue rs] = Result.listValue rs
      rw [capture_singleton]
      exact h

/-- The SPREAD/capture round-trip is sequence-specific: it holds exactly on
canonical values that are not lists. Spreading a list opens its boundary, and
re-capturing the opened items groups them as a sequence value — spread-then-
capture converts a list to a sequence (`x = A...` with `A = [1, 2, 3]` gives
`x = (1, 2, 3)`), losslessly for every other value kind. -/
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
  | sequenceValue rs =>
      show captureForArityLaw rs = Result.sequenceValue rs
      exact h
  | listValue rs =>
      exact absurd rfl (hl rs)

/-- Spread-then-capture on a list yields the canonical capture of its
ELEMENTS — never the same list back: the concrete conversion law behind
`x = A...` re-grouping list items as `(1, 2, 3)`. Singleton normalization
applies to the re-capture as usual, so a one-element payload collapses to
that lone element (`[7]` round-trips to `7`, and `[[7]]` to the inner
`[7]`), while multi-element payloads become one sequence value. -/
theorem capture_spreadItems_of_list (xs : List Result) :
    captureForArityLaw (Result.listValue xs).spreadItems
      = Result.normalize (Result.sequenceValue xs) := rfl

/-- Capture/spread/capture collapse: since captured values are canonical, a
second capture of a captured value's items is just the first capture. -/
theorem capture_toItems_capture (xs : List Result) :
    captureForArityLaw (captureForArityLaw xs).toItems = captureForArityLaw xs :=
  capture_toItems_of_canonical _ (captureForArityLaw_canonical xs)

/-- Spreading the empty sequence value supplies zero items: postfix `...` opens
a value via `Result.spreadItems`, which agrees with `Result.toItems` on
sequence values, so `()...` contributes nothing to the surrounding item
supply. This is the item-view statement of the visible-empty spread law (the
empty instance of `toItems_sequenceValue` / `spreadItems_sequenceValue`;
`spreadItems_empty_list` is the list twin). -/
theorem toItems_empty : (Result.sequenceValue []).toItems = [] := rfl

/-
## Result-boundary re-count laws

`reCountValueBoundary` is the shared helper applied at every public
property/call/builtin RESULT boundary: the caller observes the same structural
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

/-- The structural emitted count of one value is at most one: only the empty
sequence value emits 0; every other value — including the empty list `[]`,
which is a visible exact value — emits exactly 1. -/
theorem valueCount_le_one : ∀ r : Result, r.valueCount ≤ 1
  | .atom _ => Nat.le_refl 1
  | .str _ => Nat.le_refl 1
  | .sequenceValue [] => Nat.zero_le 1
  | .sequenceValue (_ :: _) => Nat.le_refl 1
  | .listValue _ => Nat.le_refl 1

/-- The empty list is a visible value: `[]` emits count 1 at every value
boundary, unlike the empty sequence value `()` which emits 0. -/
theorem valueCount_empty_list : (Result.listValue []).valueCount = 1 := rfl

/-- A result boundary emits at most one value: after `reCountValueBoundary`
the count is 0 (empty sequence value) or 1, never a multi-item count. -/
theorem reCountValueBoundary_count_le_one (p : CountedResult) :
    (reCountValueBoundary p).snd ≤ 1 :=
  valueCount_le_one p.fst
