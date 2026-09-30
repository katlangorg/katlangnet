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
Paper-facing alias for the real `Result` expression used to normalize
ORDINARY captured item supplies: `Result.normalize (Result.sequenceValue xs)`.

This is `capture : Supply -> Value` — the normalizing value/output capture
boundary (`x = 1, 2, 3`). It is NOT the collecting-binding operation: collecting binding
uses `collect : Supply -> ListValue` (`collectSegment`, exact list),
and the spread marker is `spread : Value -> Supply` (`Result.spreadItems`). The
binder-path theorems below pin which operation each receiver applies.
-/
def captureForArityLaw (xs : List Result) : Result :=
  Result.normalize (Result.sequenceValue xs)

/-- Single-variadic signature used to expose the non-opaque variadic splitter. -/
def singleVariadicSignatureForArityLaw : CallableSignature :=
  { name := "F", parameters := [{ name := "x", kind := .collecting }] }

theorem empty_sequence_is_sequenceValue_empty :
    buildEmptySequenceValue 0 = Result.sequenceValue [] := by
  rfl

/-- The flat binder's arity payload describes the complete supply. In
particular, binding a prefix never subtracts it from the reported counts. -/
theorem flat_binding_arity_reports_complete_supply (ps : List Ident) (vs : List Result)
    (h : ps.length ≠ vs.length) :
    runEvalM (bindParams ps vs) = .error (Error.arityMismatch ps.length vs.length) := by
  simp [bindParams, h, runEvalM]
  rfl

/-- A fixed parameter keeps its allocated value, independent of its kind. -/
theorem flat_fixed_parameter_preserves_supplied_value (name : Ident) (v : Result) :
    runEvalM (bindParams [name] [v]) = .ok [(name, v)] := by
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
value/output construction boundary only. Collecting bindings never use it — the
binder-path theorems `bindParameterPatternList_single_collecting_binds_collect` and
the leading/middle/trailing bridge family below connect the real binder to
`collectSegment` instead. Capture is not raw grouping: singleton capture
collapses, while a singleton collected segment stays `[item]`.
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
Call parameter binding never uses this view. Assignment
deconstruction opens its single right-hand side value through a different
mechanism: its unpacking receiver (`.unpacking`, which opens with the
equivalent one-level view `Result.spreadItems`), not the builtin collection
view (see the deconstruction bridge laws later in this file).
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
    (allowAlgorithmBindings : Bool) :
    bindParameterPatternList.bindPairs outerPatterns outerInputs allowAlgorithmBindings [] [] =
      pure [] := by
  simp [bindParameterPatternList.bindPairs]

/-
## Segment collection laws (`collect : Supply -> ListValue`)

`collectSegment` is the single collecting-binding materialization operation: every collecting binding
— deconstruction collecting bindings, single collecting parameters, and mixed
prefix/collecting/suffix parameter lists — binds its assigned middle supply through
it, after receiver-specific supply preparation. The laws below establish the
required exactness properties.
-/

/-- Stable result kind + exact elements: a collecting binding is ALWAYS the exact
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

/-- Open/collect round trip: spread (`open`, `Result.spreadItems`)
re-supplies EXACTLY the collected items, so variadic forwarding
(`Forward(*items) = Target(items*)`) is ordinary list spread with no
hidden raw-supply metadata. -/
theorem spreadItems_collectSegment (xs : List Result) :
    (collectSegment xs).spreadItems = xs := rfl

/-- A collected list is one visible value: emitted count 1 at every boundary,
including the empty collected list `[]`. -/
theorem valueCount_collectSegment (xs : List Result) :
    (collectSegment xs).valueCount = 1 := rfl

/-- Provenance independence: `collect` depends only on the assembled item
supply, never on which structures were spread to produce it — collecting the
concatenation of two spread supplies is exactly the list of those items,
whatever `a` and `b` were (`first, *rest = 1, [2, 3]*, (4, 5)*` gives
`rest = [2, 3, 4, 5]`). -/
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

/-- Canonical-supply invariant at the real collect boundary: when every supplied
value is already canonical — which observable runtime supplies are, since
every construction/capture boundary normalizes before storing — the collected
list is itself a `Result.normalize` fixed point. `collectSegment` performs no
normalization of its own (`collectSegment xs = Result.listValue xs` stores the
supply unchanged); canonicality of the result comes entirely from the input
invariant. This is the real-model face of the core
`normalize_collect_of_canonicalSupply`. -/
theorem collectSegment_canonical_of_canonical_elements {xs : List Result}
    (h : ∀ r ∈ xs, r.normalize = r) :
    (collectSegment xs).normalize = collectSegment xs := by
  rw [collectSegment_normalize_elementwise, map_normalize_id_of_canonical h]

/--
The real parameter-pattern binder uses `collectSegment` directly for a single
top-level variadic capture. This is the binder-path bridge theorem: the
successful binding records `x` as the exact list of the supplied
items, with emitted count 1.
-/
theorem bindParameterPatternList_single_collecting_binds_collect
    (xs : List Result) (allowAlgorithmBindings : Bool) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      (xs.map (fun value => { value? := some value : ParameterPatternInput }))
      allowAlgorithmBindings)
      = .ok { argEnv := [("x", Result.listValue xs)],
              countedParamEnv := [("x", (Result.listValue xs, 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindPairs_nil_nil, collectValues_valueInputs, drop_length_valueInputs, take_length_valueInputs,
    runEvalM,
    collectSegment]
  rfl

theorem variadic_single_collecting_binds_collect (xs : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      (xs.map (fun value => { value? := some value : ParameterPatternInput }))
      false)
      = .ok { argEnv := [("x", collectSegment xs)],
              countedParamEnv := [("x", (collectSegment xs, 1))],
              algEnv := [] } := by
  simpa [collectSegment] using
    bindParameterPatternList_single_collecting_binds_collect xs false

theorem bindCallableArguments_single_variadic_items (xs : List Result) :
    bindCallableArguments
      singleVariadicSignatureForArityLaw
      xs
      (fun required actual => Error.arityMismatch required actual)
      = .ok { normalBindings := [], collectingName? := some "x", collectingItems := xs } := by
  unfold singleVariadicSignatureForArityLaw
  have hvalid :
      CallableSignature.validationError?
        { name := "F", parameters := [{ name := "x", kind := .collecting }] } = none := by
    decide
  simp [bindCallableArguments, CallableSignature.validate, hvalid,
    CallableSignature.collectingIndex?, CallableSignature.collectingIndex?.go.eq_2]

theorem bindCallableArguments_variadic_items_then_collect (xs : List Result) :
    (match bindCallableArguments
        singleVariadicSignatureForArityLaw
        xs
        (fun required actual => Error.arityMismatch required actual) with
    | .ok bindings => Except.ok (collectSegment bindings.collectingItems)
    | .error err => Except.error err)
      = Except.ok (collectSegment xs) := by
  simp [bindCallableArguments_single_variadic_items]

/-- Mixed prefix/collecting/suffix signature used to expose the loop-state binder's
empty-segment rule. -/
def mixedVariadicSignatureForArityLaw : CallableSignature :=
  { name := "F",
    parameters :=
      [{ name := "first" }, { name := "rest", kind := .collecting }, { name := "last" }] }

/-- EMPTY LOOP-STATE SEGMENT over the real flat-variadic binder: supplying exactly
the fixed parameters binds them from the ends and the collecting parameter is assigned ZERO
middle items — the same `collectSegment [] = []` rule as every other collecting-binding
receiver (`bindParameterPatternList`: required = patterns - 1). This pins the
uniform minimum (fixed parameter count), replacing the old loop-only
"the collecting parameter collects at least one slot" restriction. -/
theorem bindCallableArguments_mixed_fixed_only_empty_segment (a b : Result) :
    bindCallableArguments
      mixedVariadicSignatureForArityLaw
      [a, b]
      (fun required actual => Error.arityMismatch required actual)
      = .ok {
          normalBindings := [("first", a), ("last", b)],
          collectingName? := some "rest",
          collectingItems := [] } := by
  unfold mixedVariadicSignatureForArityLaw
  have hvalid :
      CallableSignature.validationError?
        { name := "F",
          parameters :=
            [{ name := "first" }, { name := "rest", kind := .collecting }, { name := "last" }] } = none := by
    decide
  simp [bindCallableArguments, CallableSignature.validate, hvalid,
    CallableSignature.collectingIndex?, CallableSignature.collectingIndex?.go.eq_2]

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
            [{ name := "first" }, { name := "rest", kind := .collecting }, { name := "last" }] } = none := by
    decide
  simp [bindCallableArguments, CallableSignature.validate, hvalid,
    CallableSignature.collectingIndex?, CallableSignature.collectingIndex?.go.eq_2]

/-
## Generic mixed-pattern bridge theorems

For every supported flat variadic shape — leading variadic (`Init(*init, last)`),
middle variadic (`F(x, *y, z)`), trailing variadic (`Tail(first, *rest)`); the
lone-variadic shape is `bindParameterPatternList_single_collecting_binds_collect` above —
a successful bind through the REAL shared binder records the collecting parameter's name as
`collectSegment` of exactly the allocated middle supply. The middle supply `mid`
is universally quantified, so each theorem covers the empty, singleton, and
multiple-item segments uniformly, and the fixed captures around the collecting parameter keep
their front/back argument boundaries unchanged.

Honest limitation: the front/back capture lists are one fixed capture per
side (the general shape families), not arbitrary-length name-generic capture
lists — a fully name-generic theorem would need induction through the
duplicate-name merge machinery disproportionate to what it would pin. The
wider-arity content is carried by the executable matrices in `CoreTests.lean`
and the generated differential corpora.
-/

/-- Trailing variadic (`Tail(first, *rest)`): for EVERY middle supply — empty,
singleton, or multiple — the collecting parameter binds `collectSegment mid` and the leading
fixed capture keeps the front argument boundary. -/
theorem bindParameterPatternList_trailing_collecting_binds_collect
    (x : Result) (mid : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "a", kind := .normal },
       .capture { name := "r", kind := .collecting }]
      ((x :: mid).map (fun value => { value? := some value : ParameterPatternInput }))
      false)
      = .ok { argEnv := [("a", x), ("r", collectSegment mid)],
              countedParamEnv := [("r", (collectSegment mid, 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern,
    bindPairs_nil_nil, collectValues_valueInputs,
    take_length_valueInputs, drop_length_valueInputs,
    runEvalM,
    collectSegment]
  rfl

/-- Leading variadic (`Init(*init, last)`): for EVERY middle supply the variadic
parameter binds `collectSegment mid` and the trailing fixed capture keeps the back
argument boundary. -/
theorem bindParameterPatternList_leading_collecting_binds_collect
    (y : Result) (mid : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "r", kind := .collecting },
       .capture { name := "z", kind := .normal }]
      ((mid ++ [y]).map (fun value => { value? := some value : ParameterPatternInput }))
      false)
      = .ok { argEnv := [("r", collectSegment mid), ("z", y)],
              countedParamEnv := [("r", (collectSegment mid, 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern,
    bindPairs_nil_nil, collectValues_valueInputs,
    runEvalM,
    collectSegment]
  rfl

/-- Middle variadic (`F(x, *y, z)`): for EVERY middle supply the collecting parameter binds
`collectSegment mid` between the preserved front and back fixed boundaries. -/
theorem bindParameterPatternList_middle_collecting_binds_collect
    (x y : Result) (mid : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "a", kind := .normal },
       .capture { name := "r", kind := .collecting },
       .capture { name := "z", kind := .normal }]
      ((x :: (mid ++ [y])).map (fun value => { value? := some value : ParameterPatternInput }))
      false)
      = .ok { argEnv := [("a", x), ("r", collectSegment mid), ("z", y)],
              countedParamEnv := [("r", (collectSegment mid, 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern,
    bindPairs_nil_nil, collectValues_valueInputs,
    runEvalM,
    collectSegment]
  rfl

/-
## Dot-receiver bridge laws (dot-call passes a value)

For extension-call fallback, `receiver.F(args)` is exactly the written call
`F(receiver, args)`: `prepareLexicalDotCallArgs` places the ORIGINAL receiver
expression as the ordinary first argument slot, and `callLexicalWithReceiverCounted`
hands that bundle to the ONE `evalResolvedCallCounted` funnel every written
call uses. There is no receiver-specific assembly, no receiver supply, and no
callee inspection: the receiver is one written argument, so the ordinary
argument laws apply to it unchanged —

- a written non-spread argument reifies to ONE value (`()` included), so a
  collecting parameter collects the receiver as exactly one item whatever its
  value (`dot_call_uses_same_collector_binding_as_plain_call`);
- the receiver is ONE input for arity checking and fixed prefix/suffix
  allocation (its item count never satisfies arity);
- a FIXED parameter binds the receiver's one value;
- only the spread marker opens a receiver: `R*.F(args)` is the ordinary spread
  slot of `F(R*, args)`.
-/

/-- `receiver.F(args)` assembles exactly the argument bundle of the written
call `F(receiver, args)`: the receiver is the ordinary leading argument. -/
theorem dot_receiver_is_ordinary_leading_argument (receiver : Expr) (args : OutputBundle) :
    prepareLexicalDotCallArgs receiver (some args) = receiver :: args := rfl

/-- The argumentless dotted spelling `receiver.F` is the one-argument written
call `F(receiver)`. -/
theorem argumentless_dot_receiver_is_the_one_argument (receiver : Expr) :
    prepareLexicalDotCallArgs receiver none = [receiver] := rfl

/-- `R*.F(args)` is the written spread call `F(R*, args)`: the spread receiver
is an ordinary spread slot, opened by the ONE call-item assembly like every
other spread slot — never by a receiver-specific rule. -/
theorem spread_dot_receiver_is_ordinary_spread_argument (operand : Expr) (args : OutputBundle) :
    prepareLexicalDotCallArgs (.sequenceSpread operand) (some args)
      = .sequenceSpread operand :: args := rfl

private theorem collectValues_single (v : Result) :
    bindParameterPatternList.collectValues [{ value? := some v : ParameterPatternInput }]
      = pure [v] := by
  simp [bindParameterPatternList.collectValues]

/-- The receiver is one written argument, so a collecting parameter collects
it as exactly ONE item whatever its value: `(1, 2).Gather` is
`Gather((1, 2))`, `[(1, 2)]`; `().Gather` is `[()]`; `[1, 2].Gather` is
`[[1, 2]]`. -/
theorem dot_receiver_is_one_collected_item (v : Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      [{ value? := some v : ParameterPatternInput }]
      false)
      = .ok { argEnv := [("x", collectSegment [v])],
              countedParamEnv := [("x", (collectSegment [v], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindPairs_nil_nil, collectValues_single,
    runEvalM,
    collectSegment]
  rfl

/-- With an extra written argument, the fixed suffix binds from the back and
the collector's segment is the receiver alone — collected as that one item
(a sequence, a list, a scalar, and an empty value alike). -/
theorem dot_receiver_with_suffix_is_one_collected_item (v y : Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "r", kind := .collecting },
       .capture { name := "z", kind := .normal }]
      [{ value? := some v : ParameterPatternInput },
       { value? := some y : ParameterPatternInput }]
      false)
      = .ok { argEnv := [("r", collectSegment [v]), ("z", y)],
              countedParamEnv := [("r", (collectSegment [v], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern,
    bindPairs_nil_nil, collectValues_single,
    runEvalM,
    collectSegment]
  rfl

/-- A FIXED parameter binds the receiver's one value: with the receiver as the
only slot, the suffix takes it whole and the collector collects nothing. -/
theorem dot_receiver_fixed_binds_value (v : Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "r", kind := .collecting },
       .capture { name := "z", kind := .normal }]
      [{ value? := some v : ParameterPatternInput }]
      false)
      = .ok { argEnv := [("r", collectSegment []), ("z", v)],
              countedParamEnv := [("r", (collectSegment [], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern,
    bindPairs_nil_nil, bindParameterPatternList.collectValues,
    runEvalM,
    collectSegment]
  rfl

/-- The receiver is ONE input for arity checking whatever it holds: a mixed
prefix/collecting/suffix list requiring two fixed inputs rejects a lone
receiver even when the receiver's value has enough items. -/
theorem dot_receiver_count_never_satisfies_arity (v : Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "a", kind := .normal },
       .capture { name := "r", kind := .collecting },
       .capture { name := "z", kind := .normal }]
      [{ value? := some v : ParameterPatternInput }]
      false)
      = .error (Error.arityMismatch 2 1) := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting, runEvalM]
  rfl

/-
## Exact collector laws (September 2026)

VALUES STAY VALUES. A collecting parameter collects exactly the items the
binder allocated to it (after fixed prefix/suffix allocation) as ONE exact list
(`collectSegment`) and never inspects or opens an item: every non-spread
written argument is ONE item whatever its value, so a lone sequence, list,
`()`, or `[]` is collected as that one value. Only an explicit spread (the
caller's `v*`) or an explicit structural pattern (the callee's `((*xs))` or `([*xs])`)
turns one value into several items. The laws below are stated over the real
binder `bindParameterPatternList`, so they pin the rule at the layer that owns
it — collector binding, never dot-call, selection, or grouping.
-/

/-- A lone written SEQUENCE is one collected item: `Coll((1, 2))` is
`[(1, 2)]` — the collector never opens it (`Coll((1, 2)*)` is the spread
form). -/
theorem collector_lone_sequence_is_one_item (items : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      [{ value? := some (.sequenceValue items) : ParameterPatternInput }]
      false)
      = .ok { argEnv := [("x", collectSegment [.sequenceValue items])],
              countedParamEnv := [("x", (collectSegment [.sequenceValue items], 1))],
              algEnv := [] } :=
  dot_receiver_is_one_collected_item (.sequenceValue items)

/-- A lone written LIST is one collected item, exactly like a sequence:
`Coll([1, 2])` is `[[1, 2]]` (there is no kind-dependent opening). -/
theorem collector_lone_list_is_one_item (items : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      [{ value? := some (.listValue items) : ParameterPatternInput }]
      false)
      = .ok { argEnv := [("x", collectSegment [.listValue items])],
              countedParamEnv := [("x", (collectSegment [.listValue items], 1))],
              algEnv := [] } :=
  dot_receiver_is_one_collected_item (.listValue items)

/-- An empty value is still a value: `Coll(())` is `[()]` and `Coll([])` is
`[[]]` — ONE supplied item each, never the zero-item supply of `Coll()`. -/
theorem collector_lone_empty_values_are_one_item :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      [{ value? := some (.sequenceValue []) : ParameterPatternInput }]
      false)
      = .ok { argEnv := [("x", collectSegment [.sequenceValue []])],
              countedParamEnv := [("x", (collectSegment [.sequenceValue []], 1))],
              algEnv := [] }
    ∧ runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      [{ value? := some (.listValue []) : ParameterPatternInput }]
      false)
      = .ok { argEnv := [("x", collectSegment [.listValue []])],
              countedParamEnv := [("x", (collectSegment [.listValue []], 1))],
              algEnv := [] } :=
  ⟨dot_receiver_is_one_collected_item _, dot_receiver_is_one_collected_item _⟩

/-- Explicit spread is THE value-to-supply operation: it opens a sequence and a
list alike, exactly one level (`Coll((1, 2)*)` and `Coll([1, 2]*)` both supply
`1, 2`), and a scalar supplies itself. -/
theorem explicit_spread_opens_one_level (items : List Result) (n : Int) :
    (Result.sequenceValue items).spreadItems = items
    ∧ (Result.listValue items).spreadItems = items
    ∧ (Result.atom n).spreadItems = [.atom n] := ⟨rfl, rfl, rfl⟩

/-- The collector collects spread-produced items exactly and never reopens
them: `Coll([(1, 2)]*)` is `[(1, 2)]`, `Coll([()]*)` is `[()]`,
`Coll(((1, 2), 3)*)` is `[(1, 2), 3]` — opening is one level. -/
theorem collector_collects_spread_items_exactly (v : Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      (v.spreadItems.map (fun value => { value? := some value : ParameterPatternInput }))
      false)
      = .ok { argEnv := [("x", collectSegment v.spreadItems)],
              countedParamEnv := [("x", (collectSegment v.spreadItems, 1))],
              algEnv := [] } :=
  variadic_single_collecting_binds_collect v.spreadItems

/-- FORWARDING LAW: `Forward(*xs) = Target(xs*)` re-supplies exactly the
collected items — `spread (collect S) = S` (`spreadItems_collectSegment`) — so
a collecting target re-collects the identical list, whatever the supply held
(nothing, `()`, `[]`, nested sequences or lists). -/
theorem forwarding_resupplies_the_collected_items (xs : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      ((collectSegment xs).spreadItems.map (fun value => { value? := some value : ParameterPatternInput }))
      false)
      = runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      (xs.map (fun value => { value? := some value : ParameterPatternInput }))
      false) := by
  rw [spreadItems_collectSegment]

/-- Origin independence: the collector reads only the supplied values — two
written arguments holding equal values (a literal, a property read, a call
result, an `if` branch, `A:0`, `first(A)`) bind identically. -/
theorem selection_origin_does_not_change_collector_binding (v w : Result) (h : v = w) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      [{ value? := some v : ParameterPatternInput }] false)
      = runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      [{ value? := some w : ParameterPatternInput }] false) := by
  subst h; rfl

/-- `R.F(args)` and `F(R, args)` hand the binder the SAME bundle, so the
collector cannot distinguish the two spellings: dot-call is ordinary receiver
injection. -/
theorem dot_call_uses_same_collector_binding_as_plain_call (receiver : Expr) (args : OutputBundle) :
    prepareLexicalDotCallArgs receiver (some args) = receiver :: args := rfl

/-- Through the real binder: two written items are collected exactly
(`Coll((1, 2), 3)` is `[(1, 2), 3]`). -/
theorem collector_binder_two_written_items_are_exact (items : List Result) (y : Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .collecting }]
      [{ value? := some (.sequenceValue items) : ParameterPatternInput },
       { value? := some y : ParameterPatternInput }]
      false)
      = .ok { argEnv := [("x", collectSegment [.sequenceValue items, y])],
              countedParamEnv := [("x", (collectSegment [.sequenceValue items, y], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindPairs_nil_nil, bindParameterPatternList.collectValues,
    runEvalM,
    collectSegment]
  rfl

/-- AFTER allocation the collector's segment is still collected exactly:
`F(*xs, z)` with `F((1, 2), 3)` binds `z = 3` and `xs = [(1, 2)]` — a lone
segment is never opened. -/
theorem collector_binder_lone_segment_after_suffix_is_exact (items : List Result) (y : Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "r", kind := .collecting },
       .capture { name := "z", kind := .normal }]
      [{ value? := some (.sequenceValue items) : ParameterPatternInput },
       { value? := some y : ParameterPatternInput }]
      false)
      = .ok { argEnv := [("r", collectSegment [.sequenceValue items]), ("z", y)],
              countedParamEnv := [("r", (collectSegment [.sequenceValue items], 1))],
              algEnv := [] } :=
  dot_receiver_with_suffix_is_one_collected_item (.sequenceValue items) y

/-- Through the real binder, AFTER allocation: `F(*xs, z)` with
`F((1, 2), 3, 4)` gives the suffix `4` and a two-item collector segment,
collected exactly — `xs = [(1, 2), 3]`. -/
theorem collector_binder_multi_item_segment_after_suffix_is_exact (items : List Result) (y z : Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "r", kind := .collecting },
       .capture { name := "z", kind := .normal }]
      [{ value? := some (.sequenceValue items) : ParameterPatternInput },
       { value? := some y : ParameterPatternInput },
       { value? := some z : ParameterPatternInput }]
      false)
      = .ok { argEnv := [("r", collectSegment [.sequenceValue items, y]), ("z", z)],
              countedParamEnv := [("r", (collectSegment [.sequenceValue items, y], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern,
    bindPairs_nil_nil, bindParameterPatternList.collectValues,
    runEvalM,
    collectSegment]
  rfl

/-
## Zero-supply acceptance laws (September 2026)

A callable may satisfy a ZERO-ARGUMENT VALUE DEMAND exactly when an ordinary
call supplying zero arguments can bind it. Both sides read the ONE rule
`ParameterPattern.minimumSuppliedSlots`, which is the arity check
`bindParameterPatternList` itself enforces: every pattern consumes one supplied
slot, except that a collecting capture at THAT level consumes none.

The laws below pin (1) the rule's values, (2) that the REAL binder accepts
exactly the parameter lists whose minimum is zero, and (3) that the demand law
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

/-- Acceptance is the minimum being zero. -/
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

/-- Through the REAL binder: a collecting-only parameter list binds the EMPTY
supply to the exact empty list. This is what makes `Only()` legal, and therefore
what makes bare `Only` a zero-argument value. -/
theorem collector_binder_empty_supply_is_empty_list (name : Ident) :
    runEvalM (bindParameterPatternList
      [.capture { name := name, kind := .collecting }] [] true)
      = .ok { argEnv := [(name, collectSegment [])],
              countedParamEnv := [(name, (collectSegment [], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindPairs_nil_nil, bindParameterPatternList.collectValues,
    ParameterPattern.minimumSuppliedSlots, ParameterPattern.hasCollectingCaptureAtCurrentLevel,
    runEvalM,
    collectSegment]
  rfl

/-- Through the REAL binder: a required fixed parameter beside a collector still
rejects the empty supply, and reports the MINIMUM (1) rather than the two
declared captures — the very count the zero-argument demand rejection reports. -/
theorem collector_binder_empty_supply_rejects_required_prefix (x r : Ident) :
    runEvalM (bindParameterPatternList
      [.capture { name := x }, .capture { name := r, kind := .collecting }] [] true)
      = .error (Error.arityMismatch 1 0) := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    ParameterPattern.minimumSuppliedSlots, ParameterPattern.hasCollectingCaptureAtCurrentLevel,
    runEvalM, EvalM.error]
  rfl

/-- Through the REAL binder: a fixed-only list rejects the empty supply with its
exact count. -/
theorem fixed_binder_empty_supply_rejects_with_exact_count (x y : Ident) :
    runEvalM (bindParameterPatternList
      [.capture { name := x }, .capture { name := y }] [] true)
      = .error (Error.arityMismatch 2 0) := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    ParameterPattern.minimumSuppliedSlots, ParameterPattern.hasCollectingCaptureAtCurrentLevel,
    runEvalM, EvalM.error]
  rfl

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
## Implicit-lifting eligibility follows zero-argument acceptance (Q-03, September 2026)

The surface pass lifts a bare value-position reference into an implicit
forwarding call exactly when the callee REQUIRES supplied arguments
(`liftsBareValueReference`, over the same `minimumSuppliedSlots` the binder
enforces). A callee that accepts zero supplied arguments — no parameter, or only
a top-level collector — is never lifted: its reference stays the zero-argument
value demand, which the property cache serves. The laws below pin the decision
table and connect it to the evaluator: for a user algorithm, "lifted" and
"cacheable demand" are exact complements, so a reference the front end leaves
bare is always an accepted, cacheable demand.
-/

theorem lifting_skips_parameterless_signature :
    liftsBareValueReference [] = false := rfl

/-- `Roll(*xs)` works with no arguments, so its bare name is never lifted. -/
theorem lifting_skips_collecting_only_signature (name : Ident) :
    liftsBareValueReference [.capture { name := name, kind := .collecting }] = false := rfl

/-- `Inc(x)` requires its argument, so its bare name still lifts. -/
theorem lifting_keeps_required_parameter (x : Ident) :
    liftsBareValueReference [.capture { name := x }] = true := rfl

/-- `Head(x, *rest)` requires ONE supplied value beside the collector: it lifts. -/
theorem lifting_keeps_required_prefix (x r : Ident) :
    liftsBareValueReference
      [.capture { name := x }, .capture { name := r, kind := .collecting }] = true := rfl

/-- A group holding a collector, `H((*xs))`, is one required slot: it lifts. -/
theorem lifting_keeps_grouped_collector (items : List ParameterPattern) :
    liftsBareValueReference [.sequenceValue items] = true := rfl

/-- THE Q-03 LAW. For a user algorithm, the front end lifts a bare value
reference exactly when the property cache could NOT serve it as a zero-argument
demand: lifting and cache eligibility are complements of ONE rule. -/
theorem bare_reference_lifts_iff_not_cacheable
    (p : Option ScopeCtx) (ps : List ParameterPattern) (op : List Expr)
    (pr : List PropDef) (out : List Expr) (id : Option PropertyIdentity) :
    liftsBareValueReference ps
      = !isCacheableZeroArgPropertyAlgorithm (Algorithm.mk p ps op pr out id) := rfl

private theorem bool_true_of_not_eq_false {b : Bool} (h : (!b) = false) : b = true := by
  revert h
  cases b <;> decide

/-- Consequently a reference the front end leaves bare is always a demand the
zero-argument law ACCEPTS and the run cache serves — never a rejection, and
never a fresh evaluation. -/
theorem unlifted_bare_reference_is_an_accepted_cacheable_demand
    (p : Option ScopeCtx) (ps : List ParameterPattern) (op : List Expr)
    (pr : List PropDef) (out : List Expr) (id : Option PropertyIdentity)
    (h : liftsBareValueReference ps = false) :
    acceptsZeroArgumentValueDemand (Algorithm.mk p ps op pr out id) = true
      ∧ isCacheableZeroArgPropertyAlgorithm (Algorithm.mk p ps op pr out id) = true := by
  have hc : isCacheableZeroArgPropertyAlgorithm (Algorithm.mk p ps op pr out id) = true :=
    bool_true_of_not_eq_false
      ((bare_reference_lifts_iff_not_cacheable p ps op pr out id).symm.trans h)
  refine ⟨?_, hc⟩
  rw [zero_argument_value_demand_accepts_exactly_zero_supply_callables _
    (fun b hb => by cases hb)]
  exact hc

/-
## Automatic parameter forwarding preserves existing bindings (Q-04, decided 2026-09-28)

THE LAW: automatic parameter forwarding must not change what an existing name refers
to. `forwardingSource` (KatLang.lean) is the surface pass's one forwarding decision;
these laws pin its two halves over arbitrary owner chains: forwarding reuses exactly
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

/-- THE BINDING-PRESERVATION LAW. Adding the parameter forwarding creates changes the
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

/-- The declaration-validity rule still sees a forwarded parameter: a property of the
same owner, or of a body nested in it, that shares its name is the ordinary
parameter/property collision. -/
theorem forwarded_parameter_still_conflicts_with_a_same_named_property (name : Ident) :
    conflictingOwnedNames { parameters := [], properties := [name], forwarded := [name] } = [name] := by
  simp [conflictingOwnedNames, OwnerLevel.signature]

/-
## The alias and bare-forwarding rules (FWD-02, decided 2026-09-29–30)

A body whose ONE written row is a bare reference to a callable that declares
parameters (`aliasesLoneBareReference`) is not a formula. An OPEN body is an exact
alias: `A = F` inherits `F`'s signature and calls `F` with it rebuilt
(`ParameterPattern.sourceArguments`, `sourceCall`, KatLang.lean). A CLOSED body — a
written parameter list or a clause branch — is bare forwarding: each of `F`'s
parameters is supplied from an EXISTING compatible binding of the same name
(`bareForwardingArgument`, `bareForwardingRow`). The laws below pin the
reconstruction (one argument per top-level pattern, each capture as its own binding,
a collector re-spread, each structural pattern as its own kind), the bare-forwarding
decision (by name, never renamed, never positional, never added to a closed list,
never reshaped from same-named leaves), its distinction from formula lifting, and the
eligibility's relation to Q-03's lifting rule. `CoreTests/AliasForwarding.lean`
evaluates the elaborated trees.
-/

/-- A fixed capture forwards its binding as ONE argument, `x`. -/
theorem source_argument_fixed_capture_is_its_binding (x : Ident) :
    ParameterPattern.sourceArgument (.capture { name := x }) = .param x := rfl

/-- A collecting capture forwards the items it collected, `xs*`: the source's supplied
range reaches the callee as that many arguments. -/
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

/-- The alias's call is its inherited signature rebuilt: `A = F` calls `F` with exactly
the patterns it took from `F`. -/
theorem source_call_rebuilds_the_inherited_signature (callee : Ident) (source : List ParameterPattern) :
    sourceCall callee source = .call (.resolve callee) (ParameterPattern.sourceArguments source) := rfl

/-! ### Bare forwarding (FWD-02, decided 2026-09-30) -/

@[simp] private theorem parameter_kind_normal_beq_normal :
    (ParameterKind.normal == ParameterKind.normal) = true := by decide
@[simp] private theorem parameter_kind_normal_beq_collecting :
    (ParameterKind.normal == ParameterKind.collecting) = false := by decide
@[simp] private theorem parameter_kind_collecting_beq_normal :
    (ParameterKind.collecting == ParameterKind.normal) = false := by decide
@[simp] private theorem parameter_kind_collecting_beq_collecting :
    (ParameterKind.collecting == ParameterKind.collecting) = true := by decide

/-- Same-name forwarding: `F(p) = p * 2` / `A(p) = F` forwards A's `p` to F's `p`. -/
theorem bare_forwarding_same_name_is_supplied (p : Ident) :
    bareForwardingArgument [.capture { name := p }] [p] [] (.capture { name := p })
      = .supplied (.param p) := by
  simp [bareForwardingArgument, ParameterPattern.topLevelCaptureKind?, bareForwardedBinding]

/-- NO RENAMING: `F(q) = q * 2` / `A(p) = F` is rejected — A's `p` never becomes F's `q`,
whatever the arity. -/
theorem bare_forwarding_never_renames (p q : Ident) (distinct : p ≠ q) :
    bareForwardingArgument [.capture { name := p }] [p] [] (.capture { name := q }) = .unforwardable := by
  simp [bareForwardingArgument, ParameterPattern.topLevelCaptureKind?, distinct, Ne.symm distinct]

/-- A CLOSED LIST NEVER GAINS A PARAMETER: `F(p, q) = p + q` / `A(p) = F` is rejected,
never an inferred `q`. -/
theorem bare_forwarding_never_adds_a_parameter (p q : Ident) (distinct : p ≠ q) :
    bareForwardingArguments [.capture { name := p }] [p] []
      [.capture { name := p }, .capture { name := q }] = none := by
  simp [bareForwardingArguments, bareForwardingArgument, ParameterPattern.topLevelCaptureKind?,
    bareForwardedBinding, distinct, Ne.symm distinct]

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

/-- STRUCTURAL COMPATIBILITY IS WHOLE-PATTERN: `Single([x])` / `G(x) = Single` is rejected —
G's whole `x` never builds Single's `[x]` because the leaf names coincide. -/
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

/-- The same leaf names in another shape are another contract: `F((x, y))` / `G(x, y) = F`
never manufactures the pair. -/
theorem bare_forwarding_never_manufactures_a_sequence (x y : Ident) :
    bareForwardingArgument [.capture { name := x }, .capture { name := y }] [x, y] []
      (.sequenceValue [.capture { name := x }, .capture { name := y }]) = .unforwardable := by
  simp [bareForwardingArgument, ParameterPattern.sameContract]

/-- A WHOLE VALUE NEEDS A TOP-LEVEL BINDING: `F(x)` / `G([x]) = F` is rejected — the `x`
inside G's list pattern is an element, not G's parameter. -/
theorem bare_forwarding_whole_value_needs_a_top_level_binding (x : Ident) :
    bareForwardingArgument [.listValue [.capture { name := x }]] [x] [] (.capture { name := x })
      = .unforwardable := by
  simp [bareForwardingArgument, ParameterPattern.topLevelCaptureKind?]

/-- Positions inside a structural pattern are never renamed either: `F([a, b])` /
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

/-- Only the SOURCE binding's kind decides a spread: a fixed binding reaches a collector as
one item, and a collected list reaches a fixed parameter whole. -/
theorem bare_forwarding_source_kind_decides_the_spread (xs : Ident) :
    bareForwardingArgument [.capture { name := xs }] [xs] []
        (.capture { name := xs, kind := .collecting }) = .supplied (.param xs)
      ∧ bareForwardingArgument [.capture { name := xs, kind := .collecting }] [xs] []
        (.capture { name := xs }) = .supplied (.param xs) := by
  constructor <;> simp [bareForwardingArgument, ParameterPattern.topLevelCaptureKind?, bareForwardedBinding]

/-- A collector nothing of its name supplies receives no argument, and a callee that then
receives nothing is its bare name — Q-03's cached value read, never an invented call. -/
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

/-- ... but the body's OWN binding is nearer: an own fixed `x` beats an enclosing
collecting `x`, so nothing is re-spread. -/
theorem bare_forwarding_own_binding_beats_an_enclosing_one (x : Ident) :
    bareForwardingArgument [.capture { name := x }] [x] [{ name := x, kind := .collecting }]
      (.capture { name := x, kind := .collecting }) = .supplied (.param x) := by
  simp [bareForwardingArgument, ParameterPattern.topLevelCaptureKind?, bareForwardedBinding]

/-- An enclosing binding is a plain named value: it never supplies a structural parameter. -/
theorem bare_forwarding_enclosing_binding_supplies_no_pattern (x : Ident) :
    bareForwardingArgument [] [] [{ name := x }] (.listValue [.capture { name := x }]) = .unforwardable := by
  simp [bareForwardingArgument]

/-- REPEATED NAMES follow the by-name rule: `P(x, x) = x` / `Q(x) = P` hands Q's ONE binding
`x` to both occurrences, `P(x, x)` — the two slots are then ordinary independent arguments
that happen to read one binding (Q-05 compares them, merges nothing). -/
theorem bare_forwarding_repeated_name_reuses_one_binding (x : Ident) :
    bareForwardingArguments [.capture { name := x }] [x] []
      [.capture { name := x }, .capture { name := x }] = some [.param x, .param x] := by
  simp [bareForwardingArguments, bareForwardingArgument, ParameterPattern.topLevelCaptureKind?,
    bareForwardedBinding]

/-- FORMULA LIFTING IS A DIFFERENT MECHANISM: the name bare forwarding refuses to add to a
closed list (`bare_forwarding_never_renames`) is exactly the one a formula in an OPEN body
lifts — `F(q)` / `A = F + 1` gives `A(q)` — while a closed formula `A(p) = F + 1` adds
nothing either (§57: the reference stays F's zero-argument demand). -/
theorem formula_lifting_infers_what_bare_forwarding_rejects (p q : Ident) (distinct : p ≠ q) :
    forwardingSource [{ parameters := [], properties := [] }] true q = .forwardedParameter
      ∧ forwardingSource [{ parameters := [p], properties := [] }] false q = .unavailable
      ∧ bareForwardingArgument [.capture { name := p }] [p] [] (.capture { name := q })
        = .unforwardable := by
  refine ⟨?_, ?_, bare_forwarding_never_renames p q distinct⟩
  · simp [forwardingSource, selectOwnedDeclaration, selectOwnedDeclarationFrom]
  · simp [forwardingSource, selectOwnedDeclaration, selectOwnedDeclarationFrom, Ne.symm distinct]

/-- The alias and bare-forwarding rules read the DECLARED signature: a callee with no
parameter pattern is read (its bare name is its value), every other callee is aliased or
forwarded by name. -/
theorem aliases_iff_declares_parameters (signature : List ParameterPattern) :
    aliasesLoneBareReference signature = true ↔ signature ≠ [] := by
  cases signature <;> simp [aliasesLoneBareReference]

/-- `Only(*xs)` works with no arguments, so a bare reference to it is never LIFTED
(Q-03) — but as a lone row it IS aliased: the alias rule reads the declared signature. -/
theorem collecting_only_callee_is_aliased_not_lifted (xs : Ident) :
    aliasesLoneBareReference [.capture { name := xs, kind := .collecting }] = true
      ∧ liftsBareValueReference [.capture { name := xs, kind := .collecting }] = false :=
  ⟨rfl, rfl⟩

/-- Every signature that lifts is one that aliases: requiring a supplied argument means
declaring a parameter. -/
theorem lifting_signature_is_an_alias_signature (signature : List ParameterPattern)
    (lifts : liftsBareValueReference signature = true) :
    aliasesLoneBareReference signature = true := by
  cases signature with
  | nil => exact absurd lifts (by decide)
  | cons pattern rest => rfl

/-- A FIXED parameter binds its one argument unchanged: `Id((1, 2))` binds
the sequence whole. -/
theorem collector_fixed_parameter_binds_value_unchanged (items : List Result) :
    runEvalM (bindParameterPatternList
      [.capture { name := "x", kind := .normal }]
      [{ value? := some (.sequenceValue items) : ParameterPatternInput }]
      false)
      = .ok { argEnv := [("x", .sequenceValue items)], countedParamEnv := [], algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern,
    runEvalM,
    ]
  rfl

/-
## Deconstruction bridge laws (unpacking receiver)

Assignment deconstruction (`x, *y, z = RHS`) is parser-elaborated into a helper
whose single parameter is the UNPACKING RECEIVER (`.unpacking [captures]`) applied
to the right-hand side value as one argument. Binding through the real
`bindParameterPatternList`, that pattern OPENS its single received value one level
(`Result.spreadItems`: a sequence or a list opens, any other value is one item)
and matches the items element-by-element — so `x, y, z = A` unpacks a stored
sequence or list value `A`. This opening is deconstruction-specific: the written
structural patterns open only their own kind.

Call parameter binding, by contrast, is a flat capture list
(`[.capture x, .capture y]`) bound over the SUPPLIED argument supply, which does NOT
open a single sequence argument. The two groups of laws below pin that contrast over
the real binder: deconstruction (the `.unpacking` receiver) opens, while a call
(the flat capture list) preserves the single argument.

The single supplied item is the value `A` (a stored sequence value).
-/

-- Calls: a flat capture list does NOT open a single sequence argument.

/-- `Add(A)`: one supplied item (the stored sequence value) against two fixed
parameters is an arity mismatch. The call binder does not open `A`. -/
theorem call_fixed_single_sequence_rejected :
    runEvalM (bindParameterPatternList
        [.capture { name := "x", kind := .normal }, .capture { name := "y", kind := .normal }]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .error (Error.arityMismatch 2 1) := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting, runEvalM]
  rfl

/-- `G(A)` mixed fixed/variadic call: one supplied item, so fixed allocation
gives `first` the whole stored sequence value and `rest` collects the empty
segment `[]` — the collector collects only the segment left AFTER fixed
allocation, and a fixed parameter binds its slot whole. -/
theorem call_variadic_single_sequence_preserved :
    runEvalM (bindParameterPatternList
        [.capture { name := "first", kind := .normal }, .capture { name := "rest", kind := .collecting }]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("first", Result.sequenceValue [Result.atom 1, Result.atom 2]),
                         ("rest", Result.listValue [])],
              countedParamEnv := [("rest", (Result.listValue [], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM,
    collectSegment]
  rfl

-- Assignment deconstruction binds through its UNPACKING RECEIVER: the elaborated
-- helper's single parameter pattern `.unpacking [targets]`, applied to the one
-- shared right-hand-side value, binds the targets against that value's ONE-LEVEL
-- items (`Result.spreadItems`): a lone sequence or list opens one level and any
-- other value is one item. It is not a written structural pattern — it has no
-- delimiter to select a kind — so it opens both kinds alike.

/-- `x, y = A`: the unpacking receiver opens the single right-hand-side value,
binding `x = 1`, `y = 2`. -/
theorem deconstruct_fixed_single_sequence_opens :
    runEvalM (bindParameterPatternList
        [.unpacking [.capture { name := "x", kind := .normal },
                     .capture { name := "y", kind := .normal }]]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("x", Result.atom 1), ("y", Result.atom 2)],
              countedParamEnv := [], algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM,
    Result.spreadItems, Result.toItems]
  rfl

/-- `first, *rest = A`: the unpacking receiver opens `A`, so `first = 1` and
`rest` COLLECTS the matched items as one exact immutable list `[2, 3]`. -/
theorem deconstruct_collecting_single_sequence_opens :
    runEvalM (bindParameterPatternList
        [.unpacking [.capture { name := "first", kind := .normal },
                     .capture { name := "rest", kind := .collecting }]]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]) }]
        true)
      = .ok { argEnv := [("first", Result.atom 1),
                         ("rest", Result.listValue [Result.atom 2, Result.atom 3])],
              countedParamEnv := [("rest", (Result.listValue [Result.atom 2, Result.atom 3], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM, Result.spreadItems, Result.toItems,
    collectSegment]
  rfl

/-- `x, *rest = 1`: a scalar right-hand side is ONE item for the unpacking
receiver (never a structure it opens): `x = 1` and `rest` collects the empty
list. -/
theorem deconstruct_scalar_is_one_item :
    runEvalM (bindParameterPatternList
        [.unpacking [.capture { name := "x", kind := .normal },
                     .capture { name := "rest", kind := .collecting }]]
        [{ value? := some (Result.atom 1) }]
        true)
      = .ok { argEnv := [("x", Result.atom 1), ("rest", Result.listValue [])],
              countedParamEnv := [("rest", (Result.listValue [], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM, Result.spreadItems, Result.toItems,
    collectSegment]
  rfl

/-- The unpacking receiver DEMANDS its one right-hand-side value like any
pattern that opens a value: a slot with no value fails with its OWN recorded
outcome — a right-hand side without output is that `missingOutput`, never a
spread failure (no spread is involved). -/
theorem deconstruct_valueless_right_hand_side_is_its_own_failure :
    runEvalM (bindParameterPatternList
        [.unpacking [.capture { name := "x", kind := .normal },
                     .capture { name := "y", kind := .normal }]]
        [{ value? := none, error? := some Error.missingOutput }]
        true)
      = .error Error.missingOutput := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM]
  rfl

/-
## List bridge laws (exact list values)

Exact list values (`Result.listValue`) join the deconstruction opening rule but
remain opaque at ordinary value and call boundaries: `Result.toItems` keeps a
list as one item, while the spread marker (`Result.spreadItems`, which
assignment deconstruction opens its right-hand side with), the LIST pattern
(`Result.listPatternItems?` — never the sequence pattern), the indexing `:`
TARGET position view (`Result.projectionItems` — the selected element itself is
never opened), and the post-binding builtin collection view open one list
boundary in their documented contexts. The laws below pin
each decision over the real model, mirroring the sequence laws above.
-/

/-- Spread opens exactly one list boundary: `[1, 2, 3]*` supplies the items. -/
theorem spreadItems_listValue (xs : List Result) :
    (Result.listValue xs).spreadItems = xs := rfl

/-- Spreading the empty list supplies zero items (`[]*` is neutral). -/
theorem spreadItems_empty_list : (Result.listValue []).spreadItems = [] := rfl

/-- Spread on sequence values is unchanged by the list extension. -/
theorem spreadItems_sequenceValue (xs : List Result) :
    (Result.sequenceValue xs).spreadItems = xs := rfl

/-- The non-spread item view keeps a list OPAQUE: a list is one item, so
value boundaries and call binding never open it. (Indexing `:` opens its
TARGET's positions through `projectionItems` and the post-binding builtin
collection view opens the bound list through `builtinCollectionItems`, not
through `toItems` — see `projectionItems_listValue` and
`builtinCollectionItems_list` below.) -/
theorem toItems_listValue_opaque (xs : List Result) :
    (Result.listValue xs).toItems = [Result.listValue xs] := rfl

/-- The indexing `:` target position view offers a list target's immediate
elements as positions, exactly like a sequence target. -/
theorem projectionItems_listValue (xs : List Result) :
    (Result.listValue xs).projectionItems = xs := rfl

/-- Positions of sequence targets are unchanged by the list extension. -/
theorem projectionItems_sequenceValue (xs : List Result) :
    (Result.sequenceValue xs).projectionItems = xs := rfl

/-- The empty list has no selectable positions (`[]:0` is out of range). -/
theorem projectionItems_empty_list :
    (Result.listValue []).projectionItems = [] := rfl

/-- Scalar targets are unchanged: an atom offers itself as the single
position, so `7:0` stays `7`. -/
theorem projectionItems_atom (n : Int) :
    (Result.atom n).projectionItems = [Result.atom n] := rfl

/-- `:` selects one immediate list element and returns it exactly as stored:
`[1, 2, 3]:0` is `1`. -/
theorem select_list_first :
    Result.select? (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) 0
      = some (Result.atom 1) := by
  simp [Result.select?, Result.projectionItems]

/-- `[1, 2, 3]:2` selects the upper-bound element. -/
theorem select_list_last :
    Result.select? (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) 2
      = some (Result.atom 3) := by
  simp [Result.select?, Result.projectionItems]

/-- A selected LIST element stays one exact opaque list:
`[[1, 2], [3, 4]]:0` is `[1, 2]`, never flattened or reopened. -/
theorem select_nested_list_element_stays_list :
    Result.select?
      (Result.listValue
        [Result.listValue [Result.atom 1, Result.atom 2],
         Result.listValue [Result.atom 3, Result.atom 4]]) 0
      = some (Result.listValue [Result.atom 1, Result.atom 2]) := by
  simp [Result.select?, Result.projectionItems]

/-- Chained selection peels one boundary per `:`:
`[[1, 2], [3, 4]]:1:0` is `3`. -/
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

/-- Out-of-range list selection is a miss (`[]:0` and `[1, 2]:2` are the
existing index out-of-range error). -/
theorem select_empty_list_out_of_range :
    Result.select? (Result.listValue []) 0 = none := by
  simp [Result.select?, Result.projectionItems]

theorem select_list_past_end_out_of_range :
    Result.select? (Result.listValue [Result.atom 1, Result.atom 2]) 2 = none := by
  simp [Result.select?, Result.projectionItems]

/-
## Selection laws (selection is a value boundary)

SELECTION CHOOSES A VALUE; SPREAD OPENS A VALUE (September 2026). `A:i`,
`first(A)`, and `last(A)` return the selected element exactly as stored and
re-count it through the ONE ordinary value boundary (`Result.valueCount`):
a selected sequence value or exact list is one emitted value, a selected `()`
emits zero values, and the selected value's origin is forgotten. No selection
form opens what it selects — only the spread marker (`Result.spreadItems`)
does, exactly one boundary. Higher-order callback items are selected values
under the same rule (`countedSequenceCallbackItem`).
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

/-- A selected `()` element is the empty sequence value itself, which the
value boundary counts as ZERO emitted values — whatever route selected it. -/
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

/-- The counted result of a selection is the value-boundary re-count of the
stored element — the exact pair the `.index` arm of `evalCounted` emits
(`(selected, Result.valueCount selected)`), which is what `reCountValueBoundary`
produces for every other value boundary WHATEVER count the value carried
before: the selected value's origin is forgotten. (The `.index` arm itself
lives in the partial evaluator block; CoreTests `SelectionValueBoundary` pins
it executably.) -/
theorem select_is_a_value_boundary (selected : Result) (n : Nat) :
    reCountValueBoundary (selected, n) = (selected, Result.valueCount selected) := rfl

/-- `first(A)` is the selection `A:0` under the same value boundary: for every
non-empty collection view `x :: xs`, `evalFirstCounted` yields exactly
`(x, valueCount x)` — the pair the `.index` arm of `evalCounted` emits for
`select? (sequenceValue (x :: xs)) 0`. -/
theorem first_is_select_zero (x : Result) (xs : List Result) (s : EvalState) :
    (evalFirstCounted (x :: xs)).run s
      = (Except.ok ((x, Result.valueCount x), s) : Except Error (CountedResult × EvalState))
    ∧ Result.select? (Result.sequenceValue (x :: xs)) 0 = some x := by
  constructor
  · rfl
  · simp [Result.select?, Result.projectionItems, Result.toItems]

/-- `last(A)` is the selection `A:(count - 1)` under the same value boundary:
for every non-empty collection view `xs ++ [x]`, `evalLastCounted` yields
`(x, valueCount x)` and `select?` at the last position yields `x`. -/
theorem last_is_select_last (x : Result) (xs : List Result) (s : EvalState) :
    (evalLastCounted (xs ++ [x])).run s
      = (Except.ok ((x, Result.valueCount x), s) : Except Error (CountedResult × EvalState))
    ∧ Result.select? (Result.sequenceValue (xs ++ [x])) xs.length = some x := by
  constructor
  · simp only [evalLastCounted, List.getLast?_concat]
    rfl
  · simp [Result.select?, Result.projectionItems, Result.toItems]

/-- `first` and `last` never carry a count of their own: `first(())` and
`last(())` are the collection-arity rejection. -/
theorem first_empty_is_badArity (s : EvalState) :
    (evalFirstCounted []).run s = (Except.error Error.badArity : Except Error (CountedResult × EvalState)) := rfl

theorem last_empty_is_badArity (s : EvalState) :
    (evalLastCounted []).run s = (Except.error Error.badArity : Except Error (CountedResult × EvalState)) := rfl

/-- A higher-order callback item is a selected value: whatever count the
iteration supplied, the callback observes the value-boundary re-count. -/
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
by which a structural pattern opens the value its slot supplies, shared by the
ordinary binder (`bindParameterPattern`), the counted callback binder
(`bindCountedParameterPattern`, a `partial def`, pinned by the guards in
`CoreTests/StructuralPatterns.lean`) and the family matchers. A sequence
pattern `(…)` opens a SEQUENCE value only and a list pattern `[…]` a LIST value
only; neither opens the other kind, and no scalar is a one-item structure — the
only pattern that takes a value whole is a bare binder.
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

/-- A scalar is never a one-item structure: `P((x, *rest))` rejects the scalar `n`
with the pattern's kind mismatch through the binder itself (formerly the scalar
one-item fallback bound `x = n`, `rest = []`). -/
theorem nested_sequence_pattern_rejects_scalar (n : Int) :
    runEvalM (bindParameterPatternList
        [.sequenceValue [.capture { name := "x", kind := .normal },
                         .capture { name := "rest", kind := .collecting }]]
        [{ value? := some (Result.atom n) }]
        false)
      = .error (structuralPatternKindMismatch
          (.sequenceValue [.capture { name := "x", kind := .normal },
                           .capture { name := "rest", kind := .collecting }])
          (Result.atom n)) := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM,
    Result.sequencePatternItems?, ParameterPattern.minimumSuppliedSlots]
  rfl

/-- A sequence pattern never opens a list: `P((x, y))` rejects `[a, b]` with its
kind mismatch (formerly it opened the list). -/
theorem nested_sequence_pattern_rejects_list (a b : Result) :
    runEvalM (bindParameterPatternList
        [.sequenceValue [.capture { name := "x", kind := .normal },
                         .capture { name := "y", kind := .normal }]]
        [{ value? := some (Result.listValue [a, b]) }]
        false)
      = .error (structuralPatternKindMismatch
          (.sequenceValue [.capture { name := "x", kind := .normal },
                           .capture { name := "y", kind := .normal }])
          (Result.listValue [a, b])) := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM,
    Result.sequencePatternItems?, ParameterPattern.minimumSuppliedSlots]
  rfl

/-- The list pattern `[x]` binds the one element of a one-element list — the
one-element structural pattern (`Only([x])` on `[[7]]` binds `x = [7]`). -/
theorem nested_list_pattern_binds_one_element (v : Result) :
    runEvalM (bindParameterPatternList
        [.listValue [.capture { name := "x", kind := .normal }]]
        [{ value? := some (Result.listValue [v]) }]
        false)
      = .ok { argEnv := [("x", v)], countedParamEnv := [], algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM,
    Result.listPatternItems?, ParameterPattern.minimumSuppliedSlots]
  rfl

/-- A list pattern never opens a sequence: `P([x, y])` rejects `(a, b)` with its
kind mismatch. -/
theorem nested_list_pattern_rejects_sequence (a b : Result) :
    runEvalM (bindParameterPatternList
        [.listValue [.capture { name := "x", kind := .normal },
                     .capture { name := "y", kind := .normal }]]
        [{ value? := some (Result.sequenceValue [a, b]) }]
        false)
      = .error (structuralPatternKindMismatch
          (.listValue [.capture { name := "x", kind := .normal },
                       .capture { name := "y", kind := .normal }])
          (Result.sequenceValue [a, b])) := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM,
    Result.listPatternItems?, ParameterPattern.minimumSuppliedSlots]
  rfl

/-- A list collector `[*xs]` collects every list cardinality exactly: `[]`,
`[v]` and `[v, w]` bind `xs = []`, `[v]`, `[v, w]`. -/
theorem nested_list_collector_collects_every_cardinality (v w : Result) :
    runEvalM (bindParameterPatternList
        [.listValue [.capture { name := "xs", kind := .collecting }]]
        [{ value? := some (Result.listValue []) }] false)
      = .ok { argEnv := [("xs", Result.listValue [])],
              countedParamEnv := [("xs", (Result.listValue [], 1))], algEnv := [] }
    ∧ runEvalM (bindParameterPatternList
        [.listValue [.capture { name := "xs", kind := .collecting }]]
        [{ value? := some (Result.listValue [v]) }] false)
      = .ok { argEnv := [("xs", Result.listValue [v])],
              countedParamEnv := [("xs", (Result.listValue [v], 1))], algEnv := [] }
    ∧ runEvalM (bindParameterPatternList
        [.listValue [.capture { name := "xs", kind := .collecting }]]
        [{ value? := some (Result.listValue [v, w]) }] false)
      = .ok { argEnv := [("xs", Result.listValue [v, w])],
              countedParamEnv := [("xs", (Result.listValue [v, w], 1))], algEnv := [] } := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      bindParameterPattern, runEvalM, Result.listPatternItems?, collectSegment]
    rfl

/-- The singleton rule (`ParameterPattern.isSingletonSequenceItems`): a sequence
pattern of one non-collecting item is invalid, the collector-only `(*xs)` and
every list pattern are valid. -/
theorem singleton_sequence_pattern_is_invalid (x : Ident) (inner : List ParameterPattern) :
    ParameterPattern.hasSingletonSequenceGroup (.sequenceValue [.capture { name := x }]) = true
    ∧ ParameterPattern.hasSingletonSequenceGroup (.sequenceValue [.sequenceValue inner]) = true
    ∧ ParameterPattern.hasSingletonSequenceGroup (.sequenceValue [.listValue inner]) = true := by
  simp [ParameterPattern.hasSingletonSequenceGroup, ParameterPattern.isSingletonSequenceItems]

theorem collector_only_sequence_pattern_is_valid (xs : Ident) :
    ParameterPattern.hasSingletonSequenceGroup
      (.sequenceValue [.capture { name := xs, kind := .collecting }]) = false := by
  simp [ParameterPattern.hasSingletonSequenceGroup, ParameterPattern.isSingletonSequenceItems,
    ParameterPattern.anyHasSingletonSequenceGroup]

theorem one_element_list_pattern_is_valid (x : Ident) :
    ParameterPattern.hasSingletonSequenceGroup (.listValue [.capture { name := x }]) = false := by
  simp [ParameterPattern.hasSingletonSequenceGroup, ParameterPattern.anyHasSingletonSequenceGroup]

/-
## Repeated-name binding is order-independent (September 2026)

A repeated name is decided ONCE per pattern level, when its last contribution joins, by
`repeatedNameFailure`: every PAIR of its contributions must be compatible (equal values;
equal counted values; the same callable identity for two algorithm-channel bindings).
Every contribution carries its own value — the binder fails a valueless one first
(Q-05, see "Repeated names are constraints, not merges" below).
The verdict is a function of the MULTISET of contributions, so no permutation of the
arguments and no grouping of the merges can change it.
-/

private theorem perm_any_eq {α} {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → Bool) :
    l₁.any f = l₂.any f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  exact ⟨fun ⟨x, hx, hf⟩ => ⟨x, h.mem_iff.mp hx, hf⟩,
    fun ⟨x, hx, hf⟩ => ⟨x, h.mem_iff.mpr hx, hf⟩⟩

private theorem pairwise_any_perm {α} {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → α → Bool) :
    l₁.any (fun a => l₁.any (fun b => f a b)) = l₂.any (fun a => l₂.any (fun b => f a b)) := by
  rw [perm_any_eq h]
  congr 1
  funext a
  exact perm_any_eq h _

theorem repeated_name_failure_is_permutation_invariant (names : List Ident)
    {contributions permuted : List ParameterPatternBindings} (h : contributions.Perm permuted) :
    repeatedNameFailure names contributions = repeatedNameFailure names permuted := by
  have hValue : ∀ name, repeatedNameValueConflict name contributions
      = repeatedNameValueConflict name permuted := fun name => by
    simp only [repeatedNameValueConflict]
    exact pairwise_any_perm (h.filterMap _) _
  have hCounted : ∀ name, repeatedNameCountedConflict name contributions
      = repeatedNameCountedConflict name permuted := fun name => by
    simp only [repeatedNameCountedConflict]
    exact pairwise_any_perm (h.filterMap _) _
  have hIdentity : ∀ name, repeatedNameCallableIdentityConflict name contributions
      = repeatedNameCallableIdentityConflict name permuted := fun name => by
    simp only [repeatedNameCallableIdentityConflict]
    exact pairwise_any_perm (h.filterMap _) _
  simp only [repeatedNameFailure, hValue, hCounted, hIdentity]

/-- A successful repeated-name verdict also excludes different callable identities.
    The permutation theorem alone did not constrain the callable kept by the merge. -/
theorem repeated_name_success_has_no_callable_identity_conflict (names : List Ident)
    (contributions : List ParameterPatternBindings)
    (success : repeatedNameFailure names contributions = none) :
    names.any (fun name => repeatedNameCallableIdentityConflict name contributions) = false := by
  unfold repeatedNameFailure at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> simp_all

/-- Any two callable contributions of a successful name have the same identity.
    Thus choosing a first callable cannot choose between distinct declarations or
    captured activations. Declaration identity presumes an identified executable
    program, just as the evaluator's ownership and cache identities do. -/
theorem repeated_name_success_callables_agree (names : List Ident)
    (contributions : List ParameterPatternBindings) (name : Ident)
    (success : repeatedNameFailure names contributions = none) (member : name ∈ names)
    (left right : Algorithm)
    (hl : left ∈ contributions.filterMap (fun c => c.algEnv.lookup name))
    (hr : right ∈ contributions.filterMap (fun c => c.algEnv.lookup name)) :
    sameRepeatedCallableIdentity left right = true := by
  have h := repeated_name_success_has_no_callable_identity_conflict names contributions success
  have hn : repeatedNameCallableIdentityConflict name contributions = false := by
    simpa using (List.any_eq_false.mp h) name member
  unfold repeatedNameCallableIdentityConflict at hn
  have ha : (contributions.filterMap (fun c => c.algEnv.lookup name)).any
      (fun right => !sameRepeatedCallableIdentity left right) = false := by
    simpa using (List.any_eq_false.mp hn) left hl
  have hp := (List.any_eq_false.mp ha) right hr
  simpa using hp

private theorem repeated_lookup_append {A} (name : Ident) (xs ys : Assoc Ident A) :
    lookupAssoc name (xs ++ ys) = (lookupAssoc name xs).orElse (fun _ => lookupAssoc name ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨key, value⟩
    by_cases h : name = key <;> simp [lookupAssoc, h, ih]

private theorem repeated_lookup_appendFirst {A} (name : Ident) (acc incoming : Assoc Ident A) :
    lookupAssoc name (appendFirstOccurrences acc incoming) =
      (lookupAssoc name acc).orElse (fun _ => lookupAssoc name incoming) := by
  induction incoming generalizing acc with
  | nil => simp [appendFirstOccurrences, lookupAssoc]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp only [appendFirstOccurrences, List.foldl_cons]
    split
    next h =>
      rw [show rest.foldl _ acc = appendFirstOccurrences acc rest from rfl, ih]
      by_cases hn : name = key
      · subst name
        cases he : lookupAssoc key acc <;> simp_all [lookupAssoc]
      · simp [lookupAssoc, hn]

    next h =>
      rw [show rest.foldl _ (acc ++ [(key, value)]) = appendFirstOccurrences (acc ++ [(key, value)]) rest from rfl, ih, repeated_lookup_append]
      by_cases hn : name = key
      · subst name
        cases he : lookupAssoc key acc <;> simp_all [lookupAssoc]
      · simp [lookupAssoc, hn]

private def repeatedMergeStep (merged contribution : ParameterPatternBindings) : ParameterPatternBindings := {
  argEnv := appendFirstOccurrences merged.argEnv contribution.argEnv,
  countedParamEnv := appendFirstOccurrences merged.countedParamEnv contribution.countedParamEnv,
  algEnv := appendFirstOccurrences merged.algEnv contribution.algEnv }

private theorem repeated_lookup_fold_merge {A} (name : Ident)
    (project : ParameterPatternBindings → Assoc Ident A)
    (step : ∀ a b, project (repeatedMergeStep a b) = appendFirstOccurrences (project a) (project b))
    (cs : List ParameterPatternBindings) (acc : ParameterPatternBindings) :
    lookupAssoc name (project (cs.foldl repeatedMergeStep acc)) =
      (lookupAssoc name (project acc)).orElse
        (fun _ => (cs.filterMap (fun c => lookupAssoc name (project c))).head?) := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, ih, step, repeated_lookup_appendFirst]
    cases ha : lookupAssoc name (project acc) <;>
      cases hc : lookupAssoc name (project c) <;> simp [hc]

private theorem repeated_merged_lookup {A} (name : Ident)
    (project : ParameterPatternBindings → Assoc Ident A)
    (step : ∀ a b, project (repeatedMergeStep a b) = appendFirstOccurrences (project a) (project b))
    (empty : project {} = []) (cs : List ParameterPatternBindings) :
    lookupAssoc name (project (mergeFirstOccurrences cs)) =
      (cs.filterMap (fun c => lookupAssoc name (project c))).head? := by
  change lookupAssoc name (project (cs.foldl repeatedMergeStep {})) = _
  rw [repeated_lookup_fold_merge name project step cs {}, empty]
  rfl

def RepeatedBindingChannelAgreement {A} (same : A → A → Bool) : Option A → Option A → Prop
  | none, none => True
  | some a, some b => same a b = true
  | _, _ => False

private theorem repeated_first_agrees_of_perm {A} (same : A → A → Bool)
    {xs ys : List A} (permutation : xs.Perm ys)
    (compatible : xs.any (fun a => xs.any (fun b => !same a b)) = false) :
    RepeatedBindingChannelAgreement same xs.head? ys.head? := by
  cases xs with
  | nil => have hy := List.perm_nil.mp permutation.symm; subst ys; trivial
  | cons a xs =>
    cases ys with
    | nil => have hx := List.perm_nil.mp permutation; simp at hx
    | cons b ys =>
      change same a b = true
      have hb : b ∈ a :: xs := permutation.mem_iff.mpr (by simp)
      have ha : (a :: xs).any (fun b => !same a b) = false := by
        simpa using (List.any_eq_false.mp compatible) a (by simp)
      simpa using (List.any_eq_false.mp ha) b hb

/-- Successful repeated-name binding preserves availability and contents on all
    three channels under every contribution permutation. Association-list order
    is not observable; callable contents are compared by callable identity. -/
theorem repeated_name_complete_binding_is_permutation_invariant
    (names : List Ident) (name : Ident) (member : name ∈ names)
    {contributions permuted : List ParameterPatternBindings}
    (permutation : contributions.Perm permuted)
    (success : repeatedNameFailure names contributions = none) :
    RepeatedBindingChannelAgreement (· == ·)
      (lookupAssoc name (mergeFirstOccurrences contributions).argEnv)
      (lookupAssoc name (mergeFirstOccurrences permuted).argEnv) ∧
    RepeatedBindingChannelAgreement (· == ·)
      (lookupAssoc name (mergeFirstOccurrences contributions).countedParamEnv)
      (lookupAssoc name (mergeFirstOccurrences permuted).countedParamEnv) ∧
    RepeatedBindingChannelAgreement sameRepeatedCallableIdentity
      ((mergeFirstOccurrences contributions).algEnv.lookup name)
      ((mergeFirstOccurrences permuted).algEnv.lookup name) := by
  have compatible :
      names.any (fun n => repeatedNameValueConflict n contributions) = false ∧
      names.any (fun n => repeatedNameCountedConflict n contributions) = false ∧
      names.any (fun n => repeatedNameCallableIdentityConflict n contributions) = false := by
    unfold repeatedNameFailure at success
    split at success <;> try contradiction
    split at success <;> try contradiction
    split at success <;> simp_all
  refine ⟨?_, ?_, ?_⟩
  · rw [repeated_merged_lookup name ParameterPatternBindings.argEnv (by intros; rfl) rfl contributions,
        repeated_merged_lookup name ParameterPatternBindings.argEnv (by intros; rfl) rfl permuted]
    apply repeated_first_agrees_of_perm _ (permutation.filterMap _)
    have h := (List.any_eq_false.mp compatible.1) name member
    simpa [repeatedNameValueConflict] using h
  · rw [repeated_merged_lookup name ParameterPatternBindings.countedParamEnv (by intros; rfl) rfl contributions,
        repeated_merged_lookup name ParameterPatternBindings.countedParamEnv (by intros; rfl) rfl permuted]
    apply repeated_first_agrees_of_perm _ (permutation.filterMap _)
    have h := (List.any_eq_false.mp compatible.2.1) name member
    simpa [repeatedNameCountedConflict] using h
  · -- The algorithm channel is compared by the callable it binds (`AlgEnv.lookup`, the
    -- projection an invocation reads). No recorded value failure survives a repeated
    -- name: every contribution of one carries its own value (Q-05, the binder half is
    -- `repeated_capture_success_requires_every_value`), so each algorithm binding it
    -- keeps records none.
    simp only [AlgEnv.lookup]
    rw [repeated_merged_lookup name ParameterPatternBindings.algEnv (by intros; rfl) rfl contributions,
        repeated_merged_lookup name ParameterPatternBindings.algEnv (by intros; rfl) rfl permuted,
        ← List.head?_map, ← List.head?_map, List.map_filterMap, List.map_filterMap]
    apply repeated_first_agrees_of_perm _ (permutation.filterMap _)
    have h := (List.any_eq_false.mp compatible.2.2) name member
    simpa [repeatedNameCallableIdentityConflict, AlgEnv.lookup] using h

-- The canonical instances — `P(f, f, f)` rejects `(Inc, 5, A)` in all six permutations,
-- `(A, A, 5)` binds in all six, and distinct callable identities reject — are
-- executable guards (`CoreTests/HigherOrderCalls.lean`, `repeatedNameVerdictIsOrderIndependent`,
-- `twoOccurrenceRepeatsKeepThePairwiseRule`), since the derived `BEq` on `Result` carries
-- no lawful lemmas to close a value comparison by proof.


/-- A right-kind value with the wrong number of elements is the group's ordinary
arity mismatch, never a kind mismatch: the pair pattern `(x, y)` given the
three-element sequence `(a, b, c)` reports 2 required, 3 supplied. -/
theorem nested_pair_pattern_rejects_three_element_sequence (a b c : Result) :
    runEvalM (bindParameterPatternList
        [.sequenceValue [.capture { name := "x", kind := .normal },
                         .capture { name := "y", kind := .normal }]]
        [{ value? := some (Result.sequenceValue [a, b, c]) }]
        false)
      = .error (Error.arityMismatch 2 3) := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM,
    Result.sequencePatternItems?, ParameterPattern.minimumSuppliedSlots]
  rfl

/-- The post-binding builtin collection view opens a bound list exactly like a
bound sequence value: ONE outer boundary, so `count([1, 2, 3])` counts three
items just as `count((1, 2, 3))` does. Opening is never recursive — nested
lists stay intact as single items (`count((1, [2], 3))` is 3, and a
collection element `[..]` inside the bound collection is one item). The view
applies only AFTER ordinary fixed binding: `count(1, 2, 3)` and
`count([1, 2, 3]*)` are ordinary arity errors, never collections. -/
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

/-- Normalization preserves list structure exactly: elements normalize but
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

/-- Ordinary capture and segment collection stay distinct operations on the same
supply: `capture` normalizes to a sequence value while `collect` preserves
the exact list — `x = A*` re-groups list items as `(…)`, while
`x, *rest = A` collects them as `[…]`. -/
theorem capture_and_collect_differ_on_pairs (a b : Result) :
    captureForArityLaw [a, b] =
        Result.sequenceValue [Result.normalize a, Result.normalize b]
      ∧ collectSegment [a, b] = Result.listValue [a, b] :=
  ⟨capture_pair a b, rfl⟩

-- Calls: a lone list argument is ONE argument; calls never open lists.

/-- `Add(A)` with a stored LIST `A`: one supplied item against two fixed
parameters is an arity mismatch — the call binder does not open the list. -/
theorem call_fixed_single_list_rejected :
    runEvalM (bindParameterPatternList
        [.capture { name := "x", kind := .normal }, .capture { name := "y", kind := .normal }]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .error (Error.arityMismatch 2 1) := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting, runEvalM]
  rfl

/-- `G(A)` mixed fixed/variadic call with a stored LIST `A`: `first` receives the
whole list value and `rest` collects the empty list `[]` — lists never open
implicitly. -/
theorem call_variadic_single_list_preserved :
    runEvalM (bindParameterPatternList
        [.capture { name := "first", kind := .normal }, .capture { name := "rest", kind := .collecting }]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("first", Result.listValue [Result.atom 1, Result.atom 2]),
                         ("rest", Result.listValue [])],
              countedParamEnv := [("rest", (Result.listValue [], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM,
    collectSegment]
  rfl

-- Assignment deconstruction: the unpacking receiver opens a lone LIST exactly
-- like a lone sequence value (it is not a written structural pattern; it has no
-- delimiter to select a kind).

/-- `x, y = [1, 2]`: the unpacking receiver opens the lone list, binding
`x = 1`, `y = 2` — identical bindings to `x, y = [1, 2]*`. -/
theorem deconstruct_fixed_single_list_opens :
    runEvalM (bindParameterPatternList
        [.unpacking [.capture { name := "x", kind := .normal },
                     .capture { name := "y", kind := .normal }]]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("x", Result.atom 1), ("y", Result.atom 2)],
              countedParamEnv := [], algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPattern, runEvalM,
    Result.spreadItems]
  rfl

/-- `first, *rest = [1, 2, 3]`: the unpacking receiver opens the lone list;
`first = 1` and `rest` COLLECTS the matched items as the exact list `[2, 3]`. -/
theorem deconstruct_collecting_single_list_opens :
    runEvalM (bindParameterPatternList
        [.unpacking [.capture { name := "first", kind := .normal },
                     .capture { name := "rest", kind := .collecting }]]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) }]
        true)
      = .ok { argEnv := [("first", Result.atom 1),
                         ("rest", Result.listValue [Result.atom 2, Result.atom 3])],
              countedParamEnv := [("rest", (Result.listValue [Result.atom 2, Result.atom 3], 1))],
              algEnv := [] } := by
  simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
    bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
    bindParameterPattern, runEvalM, Result.spreadItems,
    collectSegment]
  rfl

/-- Lone-list receiver DISAGREEMENT, lone-collecting shape: call binding collects the
one supplied argument — the list itself — as `rest = [[1, 2]]`, while
deconstruction opens the lone list first and collects its items as
`rest = [1, 2]`. The receiver distinction is observable for every structured
argument. -/
theorem lone_collecting_list_call_and_deconstruct_differ :
    runEvalM (bindParameterPatternList
        [.capture { name := "rest", kind := .collecting }]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]])],
              countedParamEnv := [("rest", (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]], 1))],
              algEnv := [] }
    ∧ runEvalM (bindParameterPatternList
        [.unpacking [.capture { name := "rest", kind := .collecting }]]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.atom 1, Result.atom 2])],
              countedParamEnv := [("rest", (Result.listValue [Result.atom 1, Result.atom 2], 1))],
              algEnv := [] } := by
  constructor
  · simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      runEvalM,
      collectSegment]
    rfl
  · simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      bindParameterPattern, runEvalM, Result.spreadItems,
      collectSegment]
    rfl

/-- Lone-SEQUENCE receiver disagreement, lone-collecting shape — the same as
for a list: call binding collects the one supplied argument (`rest = [(1, 2)]`)
while the deconstruction unpacking receiver opens it (`rest = [1, 2]`). Only an
opening receiver opens; the call boundary preserves the value. -/
theorem lone_collecting_seq_call_and_deconstruct_differ :
    runEvalM (bindParameterPatternList
        [.capture { name := "rest", kind := .collecting }]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]])],
              countedParamEnv :=
                [("rest", (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]], 1))],
              algEnv := [] }
    ∧ runEvalM (bindParameterPatternList
        [.unpacking [.capture { name := "rest", kind := .collecting }]]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.atom 1, Result.atom 2])],
              countedParamEnv := [("rest", (Result.listValue [Result.atom 1, Result.atom 2], 1))],
              algEnv := [] } := by
  constructor
  · simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      runEvalM,
      collectSegment]
    rfl
  · simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      bindParameterPattern, runEvalM, Result.spreadItems, Result.toItems,
      collectSegment]
    rfl

/-- A lone SEQUENCE argument keeps the grouped/spread distinction: `F(A)` with
a stored sequence `A = (1, 2)` collects the one sequence value
(`rest = [(1, 2)]`) — the collector never opens an argument — while `F(A*)`
collects the spread items (`rest = [1, 2]`). Sequences and lists behave
identically here (`lone_collecting_list_call_grouped_and_spread_differ`). -/
theorem lone_collecting_seq_call_grouped_and_spread_differ :
    runEvalM (bindParameterPatternList
        [.capture { name := "rest", kind := .collecting }]
        [{ value? := some (Result.sequenceValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]])],
              countedParamEnv :=
                [("rest", (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]], 1))],
              algEnv := [] }
    ∧ runEvalM (bindParameterPatternList
        [.capture { name := "rest", kind := .collecting }]
        ((Result.sequenceValue [Result.atom 1, Result.atom 2]).spreadItems.map
          (fun value => { value? := some value : ParameterPatternInput }))
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.atom 1, Result.atom 2])],
              countedParamEnv := [("rest", (Result.listValue [Result.atom 1, Result.atom 2], 1))],
              algEnv := [] } := by
  constructor
  · simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      runEvalM,
      collectSegment]
    rfl
  · simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      runEvalM,
      collectSegment, Result.spreadItems, Result.toItems]
    rfl

/-- A lone LIST argument keeps the grouped/spread distinction: `F(A)` with a
stored list `A = [1, 2]` collects the one exact list (`rest = [[1, 2]]`) — no
argument opens implicitly — while `F(A*)` collects the spread items
(`rest = [1, 2]`), exactly as for a sequence
(`lone_collecting_seq_call_grouped_and_spread_differ`). -/
theorem lone_collecting_list_call_grouped_and_spread_differ :
    runEvalM (bindParameterPatternList
        [.capture { name := "rest", kind := .collecting }]
        [{ value? := some (Result.listValue [Result.atom 1, Result.atom 2]) }]
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]])],
              countedParamEnv :=
                [("rest", (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]], 1))],
              algEnv := [] }
    ∧ runEvalM (bindParameterPatternList
        [.capture { name := "rest", kind := .collecting }]
        ((Result.listValue [Result.atom 1, Result.atom 2]).spreadItems.map
          (fun value => { value? := some value : ParameterPatternInput }))
        true)
      = .ok { argEnv := [("rest", Result.listValue [Result.atom 1, Result.atom 2])],
              countedParamEnv := [("rest", (Result.listValue [Result.atom 1, Result.atom 2], 1))],
              algEnv := [] } := by
  constructor
  · simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      runEvalM,
      collectSegment]
    rfl
  · simp [bindParameterPatternList, bindParameterPatternList.findCollecting,
      bindParameterPatternList.bindPairs, bindParameterPatternList.collectValues,
      runEvalM,
      collectSegment, Result.spreadItems]
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

/-- The SPREAD/capture round-trip is sequence-specific: it holds exactly on
canonical values that are not lists. Spreading a list opens its boundary, and
re-capturing the spread items groups them as a sequence value — spread-then-
capture converts a list to a sequence (`x = A*` with `A = [1, 2, 3]` gives
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
ELEMENTS — never the same list back: the concrete conversion law behind
`x = A*` re-grouping list items as `(1, 2, 3)`. Singleton normalization
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

/-- Spreading the empty sequence value supplies zero items: spread opens
a value via `Result.spreadItems`, which agrees with `Result.toItems` on
sequence values, so `()*` contributes nothing to the surrounding item
supply. This is the item-view statement of the visible-empty spread law (the
empty instance of `toItems_sequenceValue` / `spreadItems_sequenceValue`;
`spreadItems_empty_list` is the list twin). -/
theorem toItems_empty : (Result.sequenceValue []).toItems = [] := rfl

/-
## Zero-item-spread neutrality at the real capture boundary

`()` and `[]` spread to zero items, so inserting either spread anywhere in a
captured item supply changes nothing — while the UNSPREAD values stay visible
one-item slots. These are the real-model faces of the core
`capture_zero_item_spread_neutral` family.
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

/-- `()*` is neutral at the capture boundary (`(n, ()*) == n`-style). -/
theorem capture_empty_sequence_spread_neutral (before after : List Result) :
    captureForArityLaw (before ++ (Result.sequenceValue []).spreadItems ++ after)
      = captureForArityLaw (before ++ after) :=
  capture_zero_item_spread_neutral rfl before after

/-- `[]*` is neutral at the capture boundary (`(n, []*) == n`-style),
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
  | .bool _ => Nat.le_refl 1
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
collection as ONE list via `makeCollectionListResult`, so the
result kind never depends on the input kind or on the collected count. Truth
is Boolean-only (`Result.asBool?` reads no atom view at all), so lists still
have no truth value — the traversal laws here can never leak into `if`.
-/

/-- The atoms builtin's observable materialization in closed form: what the
`.atomsBuiltin` dispatch in `applyBuiltinCounted` returns for an evaluated
argument value. -/
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

/-- Booleans are not numeric atoms: `atoms(true)` is `[]`. -/
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

/-- Numbers have no truth value either: there is no `0`/nonzero convention
anywhere in the model. -/
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

/-- A multi-item sequence value is never a Boolean, whatever its first item:
the Boolean view performs no flattening. -/
theorem asBool_pair_none (a b : Result) :
    Result.asBool? (Result.sequenceValue [a, b]) = none := by
  simp [Result.asBool?, Result.normalize]

/-- Booleans are not numbers: the numeric view of a Boolean value is empty,
so no arithmetic or ordering operator can ever read one as `0`/`1`. -/
theorem asInt_bool_none (b : Bool) : Result.asInt? (Result.bool b) = none := rfl

/-! ## At-most-once argument value evaluation (Q-01, September 2026)

Within one call, a written argument slot is evaluated at most once for its
value; if that evaluation fails, the failure is the parameter's value outcome
for the whole activation. The two laws below pin the binder half of that rule
over the real `bindParameterPattern`: a slot's algorithm channel is always bound
TOGETHER with the outcome of its one value evaluation (`slotAlgorithmBinding`),
so no failure is ever dropped and no value read can re-derive the parameter's
value from the algorithm. The read half — the `.param` arm of `evalCounted`
reports `AlgBinding.valueFailure?` and never evaluates the algorithm — lives in
the partial evaluator and is pinned by `CoreTests/ArgumentValueOutcome.lean`. -/

/-- A written slot whose one value evaluation FAILED binds its algorithm channel
together with that failure, and binds no value — for a capture whose name does not
repeat at its level (a repeated name needs the slot's OWN value, Q-05:
`repeated_capture_valueless_first_fails_with_its_own_outcome`). -/
theorem failed_slot_binds_its_failure_beside_the_algorithm_channel
    (name : Ident) (a : Algorithm) (err : Error) :
    runEvalM (bindParameterPattern [.capture { name := name }] (.capture { name := name })
      { algorithm? := some a, error? := some err } true)
      = .ok { argEnv := [], countedParamEnv := [],
              algEnv := [(name, { algorithm := a, valueFailure? := some err })] } := by
  simp [bindParameterPattern, slotAlgorithmBinding, runEvalM, ParameterPattern.repeatsAtLevel,
    ParameterPattern.bindsName]
  rfl

/-- A written slot whose one value evaluation SUCCEEDED binds that value and an
algorithm channel that records no failure: the value tier holds the outcome. The
pattern level is irrelevant to a slot that has a value. -/
theorem valued_slot_binds_its_value_and_no_failure
    (level : List ParameterPattern) (name : Ident) (a : Algorithm) (v : Result) :
    runEvalM (bindParameterPattern level (.capture { name := name })
      { value? := some v, algorithm? := some a } true)
      = .ok { argEnv := [(name, v)], countedParamEnv := [],
              algEnv := [(name, { algorithm := a, valueFailure? := none })] } := by
  simp [bindParameterPattern, slotAlgorithmBinding, runEvalM]
  rfl

/-! ## Repeated names are constraints, not merges (Q-05, September 2026)

A repeated parameter name is an equality constraint over INDEPENDENTLY supplied
arguments. Every occurrence must supply its OWN value; the values must be equal;
a failed required value propagates; a callable-only argument cannot satisfy the
constraint; several callable channels must share one identity; and channels from
different occurrences are never spliced together to make up for a missing or
failed value. Repeated-name matching may RESTRICT a binding — it never
manufactures one that no individual argument supplied.

Before Q-05, `repeatedNameAlgorithmConflict` rejected only TWO valueless
contributions: one beside a value was merged into a binding whose value came from
one argument and whose algorithm came from the other (`P(x, x) = x, x(5)` with
`P(Inc, 1)` gave `(1, 6)`), and a failed argument was repaired by the other's value
(`Q(Bad, 7)` gave `7`). The laws below pin the binder half over the real
`bindParameterPatternList`: a valueless occurrence (a callable-only argument, whose
value demand is its own arity rejection, or an argument whose value evaluation
failed) fails the binding with ITS OWN recorded outcome in either argument order,
before any verdict; the first such occurrence wins; and a successful binding of a
repeated capture requires every occurrence to have supplied a value, so its algorithm
channel never records a failure. The executable half — surface programs, collectors,
nested groups, clause families, forwarding — is `CoreTests/RepeatedNameConstraints.lean`. -/

/-- The two-occurrence level `P(x, x)`. -/
def repeatedCapturePair : List ParameterPattern :=
  [.capture { name := "x" }, .capture { name := "x" }]

/-- `P(x, x)`: a valueless FIRST argument — a callable-only one (`Inc`, whose value
demand failed with its own arity rejection) or a failed one — fails with its own
recorded outcome, whatever the second argument supplies: the second is never bound,
so its value cannot stand in, and when BOTH failed the FIRST failure is the one
reported (arguments were evaluated left to right, and binding follows that order). -/
theorem repeated_capture_valueless_first_fails_with_its_own_outcome
    (a? : Option Algorithm) (e? : Option Error) (other : ParameterPatternInput) :
    runEvalM (bindParameterPatternList repeatedCapturePair
      [{ algorithm? := a?, error? := e? }, other] true) = .error (e?.getD Error.badArity) := by
  cases a? <;>
    simp [repeatedCapturePair, bindParameterPatternList, bindParameterPatternList.findCollecting,
      bindParameterPatternList.bindPairs, bindParameterPattern, ParameterPattern.minimumSuppliedSlots,
      ParameterPattern.hasCollectingCaptureAtCurrentLevel, ParameterPattern.repeatsAtLevel,
      ParameterPattern.bindsName, runEvalM] <;> rfl

/-- `P(x, x)`: a valueless SECOND argument beside a value fails with its own recorded
outcome — the first argument's value never stands in for it, and its algorithm is
never paired with that value (`P(7, Bad)` is `Bad`'s failure, `P(1, Inc)` `Inc`'s). -/
theorem repeated_capture_valueless_second_fails_with_its_own_outcome
    (v : Result) (a₁? a₂? : Option Algorithm) (e₁? e? : Option Error) :
    runEvalM (bindParameterPatternList repeatedCapturePair
      [{ value? := some v, algorithm? := a₁?, error? := e₁? }, { algorithm? := a₂?, error? := e? }] true)
      = .error (e?.getD Error.badArity) := by
  cases a₁? <;> cases a₂? <;>
    simp [repeatedCapturePair, bindParameterPatternList, bindParameterPatternList.findCollecting,
      bindParameterPatternList.bindPairs, bindParameterPattern, ParameterPattern.minimumSuppliedSlots,
      ParameterPattern.hasCollectingCaptureAtCurrentLevel, ParameterPattern.repeatsAtLevel,
      ParameterPattern.bindsName, slotAlgorithmBinding, runEvalM] <;> rfl

/-- `P(x, x)` binds only when BOTH arguments supplied their OWN value: no binding of a
repeated capture is ever made from a contribution that had none — neither a
callable-only argument nor a failed one — so no other occurrence's value is ever
paired with its algorithm (and, by `valued_slot_binds_its_value_and_no_failure`,
every algorithm channel the binding keeps records no failure). -/
theorem repeated_capture_success_requires_every_value
    (i₁ i₂ : ParameterPatternInput) (b : ParameterPatternBindings)
    (success : runEvalM (bindParameterPatternList repeatedCapturePair [i₁, i₂] true) = .ok b) :
    i₁.value?.isSome ∧ i₂.value?.isSome := by
  rcases i₁ with ⟨v₁?, a₁?, e₁?⟩
  rcases i₂ with ⟨v₂?, a₂?, e₂?⟩
  cases v₁? with
  | none =>
      rw [repeated_capture_valueless_first_fails_with_its_own_outcome a₁? e₁? ⟨v₂?, a₂?, e₂?⟩] at success
      cases success
  | some v₁ =>
      cases v₂? with
      | none =>
          rw [repeated_capture_valueless_second_fails_with_its_own_outcome v₁ a₁? a₂? e₁? e₂?] at success
          cases success
      | some v₂ => exact ⟨rfl, rfl⟩

/-! ## Builtin call assembly respects argument roles (PV-05 / PV-19 / PV-20, September 2026)

A collection builtin's argument adapter handles each written slot by the ROLE its
position has in the builtin's metadata (`SequenceBuiltinMetadata.slotRole`): a VALUE
slot is demanded once and its outcome — one value or one failure — is final; a
CALLBACK slot carries its algorithm and is invoked by the builtin, never evaluated
merely because it was supplied; and a spread slot is supply assembly whose failure is
the call's failure. The laws below pin the metadata half and the binding half over the
real definitions. The assembly itself lives in the partial evaluator
(`collectSequenceCallableCallItems`) and is pinned by
`CoreTests/BuiltinArgumentRoles.lean`. -/

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

/-- A position past the fixed signature is SURPLUS: supplying it is an arity error. -/
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

/-- A CALLBACK control binds the item's algorithm channel and the callable it names, and
nothing else: the item's value and any value failure are never consulted, because a
callback slot is never value-evaluated (CALL-03). -/
theorem callback_control_binds_only_the_algorithm_channel
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor) (item : CallableCallItem)
    (alg : Algorithm) (hk : descriptor.kind = .algorithm) (ha : item.algorithm? = some alg) :
    runEvalM (prepareSequenceBuiltinSuffixArgItem b descriptor item)
      = .ok (.algorithm alg item.callable?) := by
  simp [prepareSequenceBuiltinSuffixArgItem, hk, ha, runEvalM]
  rfl

/-- A VALUE control binds the one value its demand established. -/
theorem value_control_binds_its_established_value
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor) (item : CallableCallItem)
    (v : Result) (hk : descriptor.kind = .value) (hv : item.value? = some v) :
    runEvalM (prepareSequenceBuiltinSuffixArgItem b descriptor item) = .ok (.value v) := by
  simp [prepareSequenceBuiltinSuffixArgItem, hk, hv, runEvalM]
  rfl

/-- A VALUE control whose one evaluation FAILED reports that failure: binding never
evaluates the slot again, so a failure cannot be retried into a different outcome
(PV-05 — `reduce`'s `initial` included). -/
theorem value_control_reports_its_recorded_failure
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor) (err : Error)
    (hk : descriptor.kind = .value) :
    runEvalM (prepareSequenceBuiltinSuffixArgItem b descriptor { error? := some err })
      = .error err := by
  cases b <;>
    simp [prepareSequenceBuiltinSuffixArgItem, hk, sequenceBuiltinValueDemandErrorWith?,
      CallableCallItem.named?, runEvalM] <;> rfl
