import KatLang

open KatLang

/-
# KatLangArityLaws

Selected arity laws proved directly over the authoritative `KatLang.lean` model.

`CoreArityAlgebra.lean` defines the small paper-facing algebra, while
`CoreArityAlgebraProofs.lean` proves its small laws and executable checks.
This file is the bridge: it proves the load-bearing laws over real KatLang
`Result` constructors, normalization, lone-structure item-supply opening, and
real binding helpers.
-/

/--
Paper-facing alias for the real `Result` expression used to canonicalize
ORDINARY captured item supplies: `Result.normalize (Result.sequenceValue xs)`.

This is `capture : Supply -> Value` — the canonicalizing value/output capture
boundary (`x = 1, 2, 3`). It is NOT the rest-binding operation: rest binding
uses `collect : Supply -> ListValue` (`collectRest`, exact immutable list),
and postfix spread is `open : Value -> Supply` (`Result.spreadItems`). The
binder-path theorems below pin which operation each receiver applies.
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
This alias theorem is intentionally small; capture is the ORDINARY
value/output construction boundary only. Rest bindings never use it — the
binder-path theorems `bindParameterPatternList_single_rest_binds_collect` and
the leading/middle/trailing bridge family below connect the real binder to
`collectRest` instead. Capture is not raw grouping: singleton capture
collapses, while a singleton rest collects `[item]`.
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

/-
## Rest collection laws (`collect : Supply -> ListValue`)

`collectRest` is the single rest-materialization operation: every rest binding
— deconstruction rest, rest-only variadic parameters, and mixed
prefix/rest/suffix parameter lists — binds its assigned middle supply through
it, after receiver-specific supply preparation. The laws below establish the
required exactness properties.
-/

/-- Stable result kind + exact elements: a rest binding is ALWAYS the exact
immutable list of precisely the assigned items, in order. This is the closed
form of `collect`; length preservation and element exactness are immediate. -/
theorem collectRest_eq_listValue (xs : List Result) :
    collectRest xs = Result.listValue xs := rfl

/-- Exact length: collecting never adds, drops, or merges items. -/
theorem collectRest_length (xs : List Result) :
    (collectRest xs).projectionItems.length = xs.length := rfl

/-- Zero assigned items collect to the exact empty list `[]` — never the
invisible empty sequence value `()`. -/
theorem collectRest_empty : collectRest [] = Result.listValue [] := rfl

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
theorem collectRest_singleton (v : Result) :
    collectRest [v] = Result.listValue [v] := rfl

-- Structured singleton rests over the real model: the boundary of the one
-- remaining item is preserved exactly, for every structure kind.
example (ys : List Result) :
    collectRest [Result.sequenceValue ys]
      = Result.listValue [Result.sequenceValue ys] := rfl
example (ys : List Result) :
    collectRest [Result.listValue ys]
      = Result.listValue [Result.listValue ys] := rfl
example : collectRest [Result.sequenceValue []]
    = Result.listValue [Result.sequenceValue []] := rfl
example : collectRest [Result.listValue []]
    = Result.listValue [Result.listValue []] := rfl

/-- A singleton rest is NEVER erased to its item: `collect [v] ≠ v`. This is
the load-bearing difference from canonical capture (`capture [v] = v` after
normalization), and what keeps one remaining structured row distinct from the
row's own elements. -/
theorem collectRest_singleton_ne_item (v : Result) :
    collectRest [v] ≠ v := by
  intro he
  exact absurd he.symm (mem_ne_listValue List.mem_cons_self)

/-- Open/collect round trip: postfix spread (`open`, `Result.spreadItems`)
re-supplies EXACTLY the collected items, so variadic forwarding
(`Forward(...items) = Target(items...)`) is ordinary list spread with no
hidden raw-supply metadata. -/
theorem spreadItems_collectRest (xs : List Result) :
    (collectRest xs).spreadItems = xs := rfl

/-- A rest value is one visible value: emitted count 1 at every boundary,
including the empty rest `[]`. -/
theorem valueCount_collectRest (xs : List Result) :
    (collectRest xs).valueCount = 1 := rfl

/-- Provenance independence: `collect` depends only on the assembled item
supply, never on which structures were spread to produce it — collecting the
concatenation of two spread supplies is exactly the list of those items,
whatever `a` and `b` were (`first, ...rest = 1, [2, 3]..., (4, 5)...` gives
`rest = [2, 3, 4, 5]`). -/
theorem collectRest_spread_concat_exact (a b : Result) :
    collectRest (a.spreadItems ++ b.spreadItems)
      = Result.listValue (a.spreadItems ++ b.spreadItems) := rfl

/-- Collect/open round trip on the list side: re-collecting a spread list's
items reproduces the list exactly (`collect ∘ open = id` on exact list
values, the real-model face of the core `collect_items_list`). -/
theorem collectRest_spreadItems_listValue (xs : List Result) :
    collectRest ((Result.listValue xs).spreadItems) = Result.listValue xs := rfl

/-- `collectRest` normalizes element-wise only: the collected list boundary is
already canonical, so normalization can only touch the stored elements
(the real-model face of the core `collect_normalize_elementwise`). -/
theorem collectRest_normalize_elementwise (xs : List Result) :
    (collectRest xs).normalize = collectRest (xs.map Result.normalize) := by
  simp [collectRest, Result.normalize]

private theorem map_normalize_id_of_canonical : ∀ {xs : List Result},
    (∀ r ∈ xs, r.normalize = r) -> xs.map Result.normalize = xs
  | [], _ => rfl
  | r :: rs, h => by
      have hr := h r List.mem_cons_self
      have ih := map_normalize_id_of_canonical (xs := rs)
        (fun q hq => h q (List.mem_cons_of_mem r hq))
      simp [hr, ih]

/-- Canonical-supply invariant at the real rest boundary: when every supplied
value is already canonical — which observable runtime supplies are, since
every construction/capture boundary normalizes before storing — the collected
rest is itself a `Result.normalize` fixed point. `collectRest` performs no
normalization of its own (`collectRest xs = Result.listValue xs` stores the
supply unchanged); canonicality of the result comes entirely from the input
invariant. This is the real-model face of the core
`normalize_collect_of_canonicalSupply`. -/
theorem collectRest_canonical_of_canonical_elements {xs : List Result}
    (h : ∀ r ∈ xs, r.normalize = r) :
    (collectRest xs).normalize = collectRest xs := by
  rw [collectRest_normalize_elementwise, map_normalize_id_of_canonical h]

/--
The real parameter-pattern binder uses `collectRest` directly for a single
top-level variadic/rest capture. This is the binder-path bridge theorem: the
successful binding records `x` as the exact immutable list of the supplied
items, with emitted count 1.
-/
theorem bindParameterPatternList_single_rest_binds_collect
    (xs : List Result) (allowAlgorithmBindings : Bool) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .variadic }]
      (xs.map (fun value => { value? := some value : ParameterPatternInput }))
      allowAlgorithmBindings)
      = .ok { argEnv := [("x", Result.listValue xs)],
              countedParamEnv := [("x", (Result.listValue xs, 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindPairs_nil_nil, collectValues_valueInputs, drop_length_valueInputs, take_length_valueInputs,
    runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup, collectRest]
  rfl

theorem variadic_single_rest_binds_collect (xs : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .variadic }]
      (xs.map (fun value => { value? := some value : ParameterPatternInput }))
      false)
      = .ok { argEnv := [("x", collectRest xs)],
              countedParamEnv := [("x", (collectRest xs, 1))],
              algEnv := [] } := by
  simpa [collectRest] using
    bindParameterPatternList_single_rest_binds_collect xs false

theorem bindCallableArguments_single_variadic_items (xs : List Result) :
    bindCallableArguments
      singleVariadicSignatureForArityLaw
      xs
      (fun required actual => Error.arityMismatch required actual)
      = .ok { normalBindings := [], variadicName? := some "x", variadicItems := xs } := by
  unfold singleVariadicSignatureForArityLaw
  have hvalid :
      CallableSignature.validationError?
        { name := "F", parameters := [{ name := "x", kind := .variadic }] } = none := by
    decide
  simp [bindCallableArguments, CallableSignature.validate, hvalid,
    CallableSignature.variadicIndex?, CallableSignature.variadicIndex?.go.eq_2]

theorem bindCallableArguments_variadic_items_then_collect (xs : List Result) :
    (match bindCallableArguments
        singleVariadicSignatureForArityLaw
        xs
        (fun required actual => Error.arityMismatch required actual) with
    | .ok bindings => Except.ok (collectRest bindings.variadicItems)
    | .error err => Except.error err)
      = Except.ok (collectRest xs) := by
  simp [bindCallableArguments_single_variadic_items]

/-- Mixed prefix/rest/suffix signature used to expose the loop-state binder's
empty-rest rule. -/
def mixedVariadicSignatureForArityLaw : CallableSignature :=
  { name := "F",
    parameters :=
      [{ name := "first" }, { name := "rest", kind := .variadic }, { name := "last" }] }

/-- EMPTY LOOP-STATE REST over the real flat-variadic binder: supplying exactly
the fixed parameters binds them from the ends and the rest is assigned ZERO
middle items — the same `collectRest [] = []` rule as every other rest
receiver (`bindParameterPatternList`: required = patterns - 1). This pins the
uniform minimum (fixed parameter count), replacing the old loop-only
"rest collects at least one slot" restriction. -/
theorem bindCallableArguments_mixed_fixed_only_empty_rest (a b : Result) :
    bindCallableArguments
      mixedVariadicSignatureForArityLaw
      [a, b]
      (fun required actual => Error.arityMismatch required actual)
      = .ok {
          normalBindings := [("first", a), ("last", b)],
          variadicName? := some "rest",
          variadicItems := [] } := by
  unfold mixedVariadicSignatureForArityLaw
  have hvalid :
      CallableSignature.validationError?
        { name := "F",
          parameters :=
            [{ name := "first" }, { name := "rest", kind := .variadic }, { name := "last" }] } = none := by
    decide
  simp [bindCallableArguments, CallableSignature.validate, hvalid,
    CallableSignature.variadicIndex?, CallableSignature.variadicIndex?.go.eq_2]

/-- Below the fixed minimum the mixed binder fails with the fixed parameter
count — one state slot cannot bind `first` and `last`. -/
theorem bindCallableArguments_mixed_below_fixed_minimum_fails (a : Result) :
    bindCallableArguments
      mixedVariadicSignatureForArityLaw
      [a]
      (fun required actual => Error.arityMismatch required actual)
      = .error (Error.arityMismatch 2 1) := by
  unfold mixedVariadicSignatureForArityLaw
  have hvalid :
      CallableSignature.validationError?
        { name := "F",
          parameters :=
            [{ name := "first" }, { name := "rest", kind := .variadic }, { name := "last" }] } = none := by
    decide
  simp [bindCallableArguments, CallableSignature.validate, hvalid,
    CallableSignature.variadicIndex?, CallableSignature.variadicIndex?.go.eq_2]

/-
## Generic mixed-pattern bridge theorems

For every supported flat rest shape — leading rest (`Init(...init, last)`),
middle rest (`F(x, ...y, z)`), trailing rest (`Tail(first, ...rest)`); the
rest-only shape is `bindParameterPatternList_single_rest_binds_collect` above —
a successful bind through the REAL shared binder records the rest name as
`collectRest` of exactly the allocated middle supply. The middle supply `mid`
is universally quantified, so each theorem covers the empty, singleton, and
multiple-item rests uniformly, and the fixed captures around the rest keep
their front/back argument boundaries unchanged.

Honest limitation: the front/back capture lists are one fixed capture per
side (the general shape families), not arbitrary-length name-generic capture
lists — a fully name-generic theorem would need induction through the
duplicate-name merge machinery disproportionate to what it would pin. The
wider-arity content is carried by the executable matrices in `CoreTests.lean`
and the generated differential corpora.
-/

/-- Trailing rest (`Tail(first, ...rest)`): for EVERY middle supply — empty,
singleton, or multiple — the rest name binds `collectRest mid` and the leading
fixed capture keeps the front argument boundary. -/
theorem bindParameterPatternList_trailing_rest_binds_collect
    (x : Result) (mid : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "a", kind := .normal },
       .capture { name := "r", kind := .variadic }]
      ((x :: mid).map (fun value => { value? := some value : ParameterPatternInput }))
      false)
      = .ok { argEnv := [("a", x), ("r", collectRest mid)],
              countedParamEnv := [("r", (collectRest mid, 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPattern,
    bindPairs_nil_nil, collectValues_valueInputs,
    take_length_valueInputs, drop_length_valueInputs,
    runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup,
    collectRest]
  rfl

/-- Leading rest (`Init(...init, last)`): for EVERY middle supply the rest
name binds `collectRest mid` and the trailing fixed capture keeps the back
argument boundary. -/
theorem bindParameterPatternList_leading_rest_binds_collect
    (y : Result) (mid : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "r", kind := .variadic },
       .capture { name := "z", kind := .normal }]
      ((mid ++ [y]).map (fun value => { value? := some value : ParameterPatternInput }))
      false)
      = .ok { argEnv := [("r", collectRest mid), ("z", y)],
              countedParamEnv := [("r", (collectRest mid, 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPattern,
    bindPairs_nil_nil, collectValues_valueInputs,
    runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup,
    collectRest]
  rfl

/-- Middle rest (`F(x, ...y, z)`): for EVERY middle supply the rest name binds
`collectRest mid` between the preserved front and back fixed boundaries. -/
theorem bindParameterPatternList_middle_rest_binds_collect
    (x y : Result) (mid : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "a", kind := .normal },
       .capture { name := "r", kind := .variadic },
       .capture { name := "z", kind := .normal }]
      ((x :: (mid ++ [y])).map (fun value => { value? := some value : ParameterPatternInput }))
      false)
      = .ok { argEnv := [("a", x), ("r", collectRest mid), ("z", y)],
              countedParamEnv := [("r", (collectRest mid, 1))],
              algEnv := [] } := by
  have hlen : ¬ (mid.length + 1 + 1 < 2) := by omega
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPattern,
    bindPairs_nil_nil, collectValues_valueInputs,
    runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup,
    collectRest, hlen]
  rfl

/-
## Deconstruction bridge laws (unpacking receiver)

Assignment deconstruction (`x, ...y, z = RHS`) is parser-elaborated into a helper
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
stored sequence value and `rest` collects the empty list `[]` — calls never
implicitly open. -/
theorem call_rest_single_sequence_preserved :
    runEvalM (bindParameterPatternList
        [.capture { name := "first", kind := .normal }, .capture { name := "rest", kind := .variadic }]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("first", Result.sequenceValue [Result.atom 1, Result.atom 2]),
                         ("rest", Result.listValue [])],
              countedParamEnv := [("rest", (Result.listValue [], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup,
    collectRest]
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
              countedParamEnv := [], algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM,
    Result.structureItems?, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, ValEnv.lookup]
  rfl

/-- `first, ...rest = A`: the deconstruction sequence-value pattern opens `A`, so
`first = 1` and `rest` COLLECTS the remaining items as one exact immutable
list `[2, 3]`. -/
theorem deconstruct_rest_single_sequence_opens :
    runEvalM (bindParameterPatternList
        [.sequenceValue [.capture { name := "first", kind := .normal },
                         .capture { name := "rest", kind := .variadic }]]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]) }]
        true)
      = .ok { argEnv := [("first", Result.atom 1),
                         ("rest", Result.listValue [Result.atom 2, Result.atom 3])],
              countedParamEnv := [("rest", (Result.listValue [Result.atom 2, Result.atom 3], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM, Result.structureItems?, mergeEqualValEnv,
    mergeEqualCountedParamEnv, mergePatternAlgEnv, lookupAssoc,
    CountedParamEnv.lookup, ValEnv.lookup, collectRest]
  rfl

/-
## List bridge laws (exact list values)

Exact list values (`Result.listValue`) join the deconstruction opening rule but
remain opaque at ordinary value and call boundaries: `Result.toItems` keeps a
list as one item, while postfix spread (`Result.spreadItems`), the
deconstruction pattern (`Result.structureItems?`), the indexing `:` projection
target view (`Result.projectionItems`), and the post-binding builtin collection
view open one list boundary in their documented contexts. The laws below pin
each decision over the real model, mirroring the sequence laws above.
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
value boundaries and call binding never open it. (Indexing `:` opens its
TARGET through `projectionItems` and the post-binding builtin collection
view opens the bound list through `builtinCollectionItems`, not through
`toItems` — see `projectionItems_listValue` and
`builtinCollectionItems_list` below.) -/
theorem toItems_listValue_opaque (xs : List Result) :
    (Result.listValue xs).toItems = [Result.listValue xs] := rfl

/-- The indexing `:` projection target view opens a list target to its
immediate elements, exactly like a sequence target. -/
theorem projectionItems_listValue (xs : List Result) :
    (Result.listValue xs).projectionItems = xs := rfl

/-- Projection on sequence targets is unchanged by the list extension. -/
theorem projectionItems_sequenceValue (xs : List Result) :
    (Result.sequenceValue xs).projectionItems = xs := rfl

/-- The empty list has no projectable positions (`[]:0` is out of range). -/
theorem projectionItems_empty_list :
    (Result.listValue []).projectionItems = [] := rfl

/-- Scalar projection targets are unchanged: an atom offers itself as the
single position, so `7:0` stays `7`. -/
theorem projectionItems_atom (n : Int) :
    (Result.atom n).projectionItems = [Result.atom n] := rfl

/-- `:` selects one immediate list element and returns it exactly as stored:
`[1, 2, 3]:0` is `1`. -/
theorem select_list_first :
    Result.select? (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) 0
      = some (Result.atom 1, 1) := by
  simp [Result.select?, Result.projectionItems, Result.projectSelectedContent,
    Result.toItems, Result.normalize]

/-- `[1, 2, 3]:2` selects the upper-bound element. -/
theorem select_list_last :
    Result.select? (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) 2
      = some (Result.atom 3, 1) := by
  simp [Result.select?, Result.projectionItems, Result.projectSelectedContent,
    Result.toItems, Result.normalize]

/-- A selected LIST element stays one exact opaque list:
`[[1, 2], [3, 4]]:0` is `[1, 2]`, never flattened or reopened. -/
theorem select_nested_list_element_stays_list :
    Result.select?
      (Result.listValue
        [Result.listValue [Result.atom 1, Result.atom 2],
         Result.listValue [Result.atom 3, Result.atom 4]]) 0
      = some (Result.listValue [Result.atom 1, Result.atom 2], 1) := by
  simp [Result.select?, Result.projectionItems, Result.projectSelectedContent,
    Result.toItems, Result.normalize]

/-- Chained projection peels one boundary per `:`:
`[[1, 2], [3, 4]]:1:0` is `3`. -/
theorem select_list_chained :
    (Result.select?
      (Result.listValue
        [Result.listValue [Result.atom 1, Result.atom 2],
         Result.listValue [Result.atom 3, Result.atom 4]]) 1).bind
      (fun projected => Result.select? projected.fst 0)
      = some (Result.atom 3, 1) := by
  simp [Result.select?, Result.projectionItems, Result.projectSelectedContent,
    Result.toItems, Result.normalize]

/-- A selected SEQUENCE element inside a list projects one level with its
item count, exactly like selecting it from a sequence target. -/
theorem select_sequence_element_in_list_projects :
    Result.select?
      (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]]) 0
      = some (Result.sequenceValue [Result.atom 1, Result.atom 2], 2) := by
  simp [Result.select?, Result.projectionItems, Result.projectSelectedContent,
    Result.toItems, Result.normalize]

/-- Out-of-range list projection is a miss (`[]:0` and `[1, 2]:2` are the
existing projection out-of-range error). -/
theorem select_empty_list_out_of_range :
    Result.select? (Result.listValue []) 0 = none := by
  simp [Result.select?, Result.projectionItems]

theorem select_list_past_end_out_of_range :
    Result.select? (Result.listValue [Result.atom 1, Result.atom 2]) 2 = none := by
  simp [Result.select?, Result.projectionItems]

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

/-- Ordinary capture and rest collection stay distinct operations on the same
supply: `capture` canonicalizes to a sequence value while `collect` preserves
the exact list — `x = A...` re-groups list items as `(…)`, while
`x, ...rest = A` collects them as `[…]`. -/
theorem capture_and_collect_differ_on_pairs (a b : Result) :
    captureForArityLaw [a, b] =
        Result.sequenceValue [Result.normalize a, Result.normalize b]
      ∧ collectRest [a, b] = Result.listValue [a, b] :=
  ⟨capture_pair a b, rfl⟩

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
whole list value and `rest` collects the empty list `[]` — calls never
implicitly open. -/
theorem call_rest_single_list_preserved :
    runEvalM (bindParameterPatternList
        [.capture { name := "first", kind := .normal }, .capture { name := "rest", kind := .variadic }]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("first", Result.listValue [Result.atom 1, Result.atom 2]),
                         ("rest", Result.listValue [])],
              countedParamEnv := [("rest", (Result.listValue [], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup,
    collectRest]
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
              countedParamEnv := [], algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM,
    Result.structureItems?, mergeEqualValEnv, mergeEqualCountedParamEnv,
    mergePatternAlgEnv, lookupAssoc, ValEnv.lookup]
  rfl

/-- `first, ...rest = [1, 2, 3]`: the deconstruction pattern opens the lone
list; `first = 1` and `rest` COLLECTS the remaining items as the exact list
`[2, 3]`. -/
theorem deconstruct_rest_single_list_opens :
    runEvalM (bindParameterPatternList
        [.sequenceValue [.capture { name := "first", kind := .normal },
                         .capture { name := "rest", kind := .variadic }]]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) }]
        true)
      = .ok { argEnv := [("first", Result.atom 1),
                         ("rest", Result.listValue [Result.atom 2, Result.atom 3])],
              countedParamEnv := [("rest", (Result.listValue [Result.atom 2, Result.atom 3], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM, Result.structureItems?, mergeEqualValEnv,
    mergeEqualCountedParamEnv, mergePatternAlgEnv, lookupAssoc,
    CountedParamEnv.lookup, ValEnv.lookup, collectRest]
  rfl

/-- Lone-list receiver DISAGREEMENT, lone-rest shape: call binding collects the
one supplied argument — the list itself — as `rest = [[1, 2]]`, while
deconstruction opens the lone list first and collects its items as
`rest = [1, 2]`. The receiver distinction is observable for every structured
argument. -/
theorem lone_rest_list_call_and_deconstruct_differ :
    runEvalM (bindParameterPatternList
        [.capture { name := "rest", kind := .variadic }]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]])],
              countedParamEnv := [("rest", (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]], 1))],
              algEnv := [] }
    ∧ runEvalM (bindParameterPatternList
        [.sequenceValue [.capture { name := "rest", kind := .variadic }]]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.atom 1, Result.atom 2])],
              countedParamEnv := [("rest", (Result.listValue [Result.atom 1, Result.atom 2], 1))],
              algEnv := [] } := by
  constructor
  · simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
      mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup,
      collectRest]
    rfl
  · simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      bindParameterPattern, runEvalM, Result.structureItems?, mergeEqualValEnv,
      mergeEqualCountedParamEnv, mergePatternAlgEnv, lookupAssoc,
      CountedParamEnv.lookup, ValEnv.lookup, collectRest]
    rfl

/-- The rest-only grouped/spread COINCIDENCE is gone: `F(A)` with a stored
sequence `A` collects the one grouped argument (`items = [(1, 2)]`), while
`F(A...)` collects the opened items (`items = [1, 2]`). The old claim that a
rest-only parameter receives the same canonical value for both calls is
obsolete under exact list collection — supplying one grouped argument and
supplying its items are observably different calls. -/
theorem lone_rest_seq_call_grouped_and_spread_differ :
    runEvalM (bindParameterPatternList
        [.capture { name := "rest", kind := .variadic }]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]])],
              countedParamEnv :=
                [("rest", (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]], 1))],
              algEnv := [] }
    ∧ runEvalM (bindParameterPatternList
        [.capture { name := "rest", kind := .variadic }]
        ((Result.sequenceValue [Result.atom 1, Result.atom 2]).spreadItems.map
          (fun value => { value? := some value : ParameterPatternInput }))
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.atom 1, Result.atom 2])],
              countedParamEnv := [("rest", (Result.listValue [Result.atom 1, Result.atom 2], 1))],
              algEnv := [] } := by
  constructor
  · simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
      mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup,
      collectRest]
    rfl
  · simp [bindParameterPatternList, bindParameterPatternList.findVariadic,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      runEvalM, mergeEqualValEnv, mergeEqualCountedParamEnv,
      mergePatternAlgEnv, lookupAssoc, CountedParamEnv.lookup, ValEnv.lookup,
      collectRest, Result.spreadItems, Result.toItems]
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
## Zero-item-open neutrality at the real capture boundary

`()` and `[]` spread to zero items, so inserting either spread anywhere in a
captured item supply changes nothing — while the UNSPREAD values stay visible
one-item slots. These are the real-model faces of the core
`capture_zero_item_open_neutral` family.
-/

/-- Generic neutral open at the real capture expression: any value whose
spread supplies no items leaves the captured value unchanged wherever the
spread is inserted. -/
theorem capture_zero_item_spread_neutral {r : Result}
    (h : r.spreadItems = []) (before after : List Result) :
    captureForArityLaw (before ++ r.spreadItems ++ after)
      = captureForArityLaw (before ++ after) := by
  rw [h]
  simp

/-- `()...` is neutral at the capture boundary (`(n, ()...) == n`-style). -/
theorem capture_empty_sequence_spread_neutral (before after : List Result) :
    captureForArityLaw (before ++ (Result.sequenceValue []).spreadItems ++ after)
      = captureForArityLaw (before ++ after) :=
  capture_zero_item_spread_neutral rfl before after

/-- `[]...` is neutral at the capture boundary (`(n, []...) == n`-style),
even though the unspread `[]` is a visible one-item value. -/
theorem capture_empty_list_spread_neutral (before after : List Result) :
    captureForArityLaw (before ++ (Result.listValue []).spreadItems ++ after)
      = captureForArityLaw (before ++ after) :=
  capture_zero_item_spread_neutral rfl before after

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

/-
## `atoms` builtin laws (issue #136)

`Result.languageAtoms` is the atoms builtin's collector: numeric atoms
gathered depth-first, left to right, through BOTH sequence and exact list
boundaries; strings contribute no atoms. The builtin materializes the
collection as ONE exact immutable list via `makeCollectionListResult`, so the
result kind never depends on the input kind or on the collected count. Truth
testing (`truthValue?`) reads the separate sequence-only `Result.atoms` view,
so lists still have no truth value — the traversal laws here can never leak
into `if`.
-/

/-- The atoms builtin's observable materialization in closed form: what the
`.atomsBuiltin` dispatch in `applyBuiltinCounted` returns for an evaluated
argument value. -/
def atomsBuiltinResultForLaw (r : Result) : CountedResult :=
  makeCollectionListResult ((Result.languageAtoms r).map Result.atom)

-- `languageAtoms` (like `Result.atoms`/`hostAtoms`) recurses through
-- `List.flatMap`, so it compiles via well-founded recursion and its
-- equations are established by `simp` rather than `rfl`.

theorem atoms_number (n : Int) :
    Result.languageAtoms (Result.atom n) = [n] := by
  simp [Result.languageAtoms]

theorem atoms_string (s : String) :
    Result.languageAtoms (Result.str s) = [] := by
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

/-- The atoms builtin returns ONE exact list value with emitted count 1 for
EVERY input — including a zero-atom collection, where the visible result is
the empty list `[]` (never the invisible empty sequence). -/
theorem atoms_result_is_list (r : Result) :
    atomsBuiltinResultForLaw r
      = (Result.listValue ((Result.languageAtoms r).map Result.atom), 1) := rfl

/-- Singleton results stay singleton lists: no canonical erasure applies to
the materialized collection. -/
theorem atoms_singleton_preserved (n : Int) :
    atomsBuiltinResultForLaw (Result.atom n)
      = (Result.listValue [Result.atom n], 1) := by
  simp [atomsBuiltinResultForLaw, makeCollectionListResult, atoms_number]

/-- `atoms(7)` is `[7]`, never `7`: the materialized list is structurally
distinct from the bare atom. -/
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

/-- Truth testing stays list-opaque: a list value never has a truth value,
whatever its contents. `atoms` traversing lists introduces no list
truthiness because `truthValue?` reads `Result.atoms`, not
`Result.languageAtoms`. -/
theorem truthValue_list_none (rs : List Result) :
    Result.truthValue? (Result.listValue rs) = none := by
  simp [Result.truthValue?, Result.atoms]

/-- Truth flattening skips list elements inside sequence conditions: a
leading list element never changes the truth value of the rest, exactly as
before the atoms change. -/
theorem truthValue_skips_leading_list_element (xs rs : List Result) :
    Result.truthValue? (Result.sequenceValue (Result.listValue xs :: rs))
      = Result.truthValue? (Result.sequenceValue rs) := by
  have h : Result.atoms (Result.sequenceValue (Result.listValue xs :: rs))
      = Result.atoms (Result.sequenceValue rs) := by
    simp [Result.atoms]
  simp [Result.truthValue?, h]
