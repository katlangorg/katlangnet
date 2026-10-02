import KatLang

/-
Historical, fully-materialized binding algebra used by older arity proofs.
This module is NOT imported by KatLang and has no production evaluation path.
Its inputs are completed values/failures, not suspended supplies. In particular,
its aggregate merge error precedence is historical and superseded by Model-C's
left-to-right inspecting binder. Current execution laws are in CoreTests.ModelC.
Retaining these explicit historical statements preserves the provenance of the
paper's Ready-value algebra without presenting it as current acquisition semantics.
-/
namespace KatLang.HistoricalReadyBinding
open KatLang

structure CountedParameterPatternBindings where
  countedParamEnv : CountedParamEnv := []
  deriving Repr

/-- Flat fixed binding preserves each supplied value. Check the complete supply
    before zipping, so an arity error reports the original lengths, not the
    unmatched recursive tails. This agrees with the pattern/callback binders
    and C# `BindParams`: two parameters and one pair value is `(2, 1)`. -/
def bindParams (ps : List Ident) (vs : List Result) : EvalM ValEnv :=
  if ps.length != vs.length then
    .error (Error.arityMismatch ps.length vs.length)
  else
    pure (ps.zip vs)


/-- One supplied item prepared for parameter binding: its value view
    (`value?`), its algorithm view where resolvable, and a retained value
    error. VALUES STAY VALUES (September 2026): every item is exactly ONE
    argument whatever supplied it — a non-spread written argument (whatever its
    value: scalar, sequence, list, `()`, `[]`), an explicit spread item, an
    extension dot-call receiver (`R.F(args)` assembles exactly the items of
    `F(R, args)`), a pattern-opened item, or a loop-state slot. No item
    records how it was written, because no binder reinterprets one item as
    several: only explicit spread and explicit structural patterns open a
    value. C#: `ParameterPatternInput`. -/
structure ParameterPatternInput where
  value? : Option Result := none
  algorithm? : Option Algorithm := none
  error? : Option Error := none
  deriving Repr

/-- The algorithm-channel binding one written argument slot contributes: its
    algorithm and, when the slot has no value, the failure its ONE value
    evaluation established (`badArity`, the binders' own default, should a
    valueless slot carry none). Every user-call binder builds its algorithm
    channel through this function (`bindParameterPattern`,
    `bindFlatFixedUserCall`), so no binder can drop a slot's failure and leave
    the parameter's value to be re-derived from the algorithm later
    (AT-MOST-ONCE ARGUMENT VALUE EVALUATION, `AlgBinding`).
    C#: `Evaluator.SlotAlgorithmBinding`. -/
def slotAlgorithmBinding (value? : Option Result) (error? : Option Error)
    (algorithm : Algorithm) : AlgBinding :=
  { algorithm := algorithm,
    valueFailure? := match value? with
      | some _ => none
      | none => some (error?.getD Error.badArity) }

structure ParameterPatternBindings where
  argEnv : ValEnv := []
  countedParamEnv : CountedParamEnv := []
  algEnv : AlgEnv := []
  deriving Repr

/-- Whether one pattern's bindings bind `name` on any channel. -/
def ParameterPatternBindings.binds (bindings : ParameterPatternBindings) (name : Ident) : Bool :=
  (lookupAssoc name bindings.argEnv).isSome || (lookupAssoc name bindings.countedParamEnv).isSome
    || (lookupAssoc name bindings.algEnv).isSome

/-- The names one pattern's bindings bind, each once. -/
def ParameterPatternBindings.names (bindings : ParameterPatternBindings) : List Ident :=
  (bindings.argEnv.map Prod.fst ++ bindings.countedParamEnv.map Prod.fst
    ++ bindings.algEnv.map Prod.fst).eraseDups

/-- Append the entries of `incoming` whose name `acc` does not bind yet: the
    first binding of a name is the one that stays. -/
def appendFirstOccurrences {A} (acc incoming : Assoc Ident A) : Assoc Ident A :=
  incoming.foldl (fun merged entry =>
    if (lookupAssoc entry.1 merged).isSome then merged else merged ++ [entry]) acc

/-- The merged bindings of one pattern level: each name keeps its FIRST binding
    on each channel. Every repeated name has passed `repeatedNameFailure`
    before this runs, so discarded entries agree on the complete value/counted
    channels and callable identity. This storage choice gives no callable
    positional precedence (`repeated_name_complete_binding_is_permutation_invariant`).
    Every contribution of a repeated name carries its OWN value (Q-05,
    `bindParameterPattern`), so the kept algorithm channel accompanies a value its
    own argument supplied — equal to the kept value — never a value some other
    argument supplied in place of a missing or failed one. -/
def mergeFirstOccurrences (contributions : List ParameterPatternBindings) : ParameterPatternBindings :=
  contributions.foldl (fun merged contribution => {
    argEnv := appendFirstOccurrences merged.argEnv contribution.argEnv,
    countedParamEnv := appendFirstOccurrences merged.countedParamEnv contribution.countedParamEnv,
    algEnv := appendFirstOccurrences merged.algEnv contribution.algEnv }) {}

/-- REPEATED-NAME VERDICT, value channel: some PAIR of the values carried by
    `name`'s contributions differs. Every contribution carries a value — the binder
    admits no valueless contribution of a repeated name (Q-05) — so every value must
    be equal. Stated over all pairs, so it depends only on the multiset of
    contributions (`repeated_name_failure_is_permutation_invariant`). -/
def repeatedNameValueConflict (name : Ident) (contributions : List ParameterPatternBindings) : Bool :=
  let values := contributions.filterMap (fun contribution => lookupAssoc name contribution.argEnv)
  values.any (fun first => values.any (fun second => !(first == second)))

/-- REPEATED-NAME VERDICT, counted channel: compare the complete counted binding,
    including emitted count. Ordinary binder inputs use value-boundary counts,
    but successful merge invariance must not rely on discarding this component. -/
def repeatedNameCountedConflict (name : Ident) (contributions : List ParameterPatternBindings) : Bool :=
  let values := contributions.filterMap (fun contribution => lookupAssoc name contribution.countedParamEnv)
  values.any (fun first => values.any (fun second => !(first == second)))


/-- Equal values are insufficient when selecting either callable can change an invocation.
    All callable contributions must have the same identity, even for just two occurrences. -/
def repeatedNameCallableIdentityConflict (name : Ident) (contributions : List ParameterPatternBindings) : Bool :=
  let algorithms := contributions.filterMap (fun contribution => contribution.algEnv.lookup name)
  algorithms.any (fun first => algorithms.any (fun second => !sameRepeatedCallableIdentity first second))

/-- REPEATED-NAME BINDING IS ORDER-INDEPENDENT (September 2026). The failure,
    if any, of the names that become COMPLETE at one merge — every one of their
    contributions at this pattern level is in `contributions`. A repeated name
    binds iff every PAIR of its contributions is compatible (equal values; equal
    complete counted pairs; the same callable identity for two algorithm-channel
    bindings), so the verdict depends on the multiset of contributions and never on
    their order or on how the merges are grouped. Two distinct callable identities
    reject even if their values agree. Within one merge an unequal value or counted
    value (`badArity`) is reported before a callable-identity conflict
    (`typeMismatch`).

    REPEATED NAMES ARE CONSTRAINTS, NOT MERGES (September 2026, Q-05): the verdict
    only RESTRICTS. It sees no valueless contribution — the binder has already
    failed any repeated capture whose slot has no value, with that slot's own
    outcome (`bindParameterPattern`) — so there is no "algorithm-only" verdict, and
    the merged binding never combines one argument's value with another argument's
    algorithm. (The former `repeatedNameAlgorithmConflict` type mismatch rejected
    only TWO algorithm-only contributions; one beside a value was spliced into a
    binding no argument supplied, and a failed contribution was replaced by the
    other's value.) C#: `RepeatedNameAggregate`. -/
def repeatedNameFailure (names : List Ident) (contributions : List ParameterPatternBindings) : Option Error :=
  if names.any (fun name => repeatedNameValueConflict name contributions) then some Error.badArity
  else if names.any (fun name => repeatedNameCountedConflict name contributions) then some Error.badArity
  else if names.any (fun name => repeatedNameCallableIdentityConflict name contributions) then
    some (Error.typeMismatch "Repeated bind equality requires the same callable identity")
  else none

/-- The merges of one bound range (Lean's `bindPairs` order,
    `merge c₁ (merge c₂ (… cₙ))`): the innermost merge runs first, and a
    repeated name is decided at the ONE merge where its last contribution
    joins — the step of its first occurrence in the range — unless the level
    binds it outside this range too (`outside`: the other range or the
    collector), in which case the later cross merge decides it with every
    contribution in hand. `earlier` holds the range's contributions left of the
    current one. C#: `FindRangeRepeatedNameFailure`. -/
def settlePatternRange (outside : Ident -> Bool)
    : List ParameterPatternBindings -> List ParameterPatternBindings -> Option Error
  | [], _ => none
  | current :: rest, earlier =>
      match settlePatternRange outside rest (earlier ++ [current]) with
      | some error => some error
      | none =>
          let completing := current.names.filter (fun name =>
            rest.any (fun contribution => contribution.binds name)
              && !earlier.any (fun contribution => contribution.binds name)
              && !outside name)
          repeatedNameFailure completing (current :: rest)


mutual
partial def bindCountedParameterPattern (pattern : ParameterPattern) (input : CountedResult)
    : EvalM CountedParameterPatternBindings := do
  match pattern with
  | .capture parameter =>
      match parameter.kind with
      | .normal => pure { countedParamEnv := [(parameter.name, input)] }
      | .collecting => .error Error.badArity
  | .sequenceValue items =>
      -- This counted matcher is the callback binding path, and it opens the
      -- callback value through the SAME kind-specific rule as the ordinary
      -- binder `bindParameterPattern` (`Result.sequencePatternItems?`): a
      -- sequence pattern opens a SEQUENCE value only; a list or a scalar is the
      -- pattern's kind mismatch in both, so `map([7], P)` with `P((x, *rest))`
      -- fails exactly like `P(7)` (September 2026; S3 made the two binders one
      -- rule). The pattern's explicit structure opens exactly this one
      -- boundary; a nested collecting binding collects the opened items exactly.
      match Result.sequencePatternItems? input.fst with
      | none => .error (structuralPatternKindMismatch pattern input.fst)
      | some elements =>
          let nestedInputs := elements.map (fun value => (value, Result.valueCount value))
          bindCountedParameterPatternList items nestedInputs
  | .listValue items =>
      -- The list pattern's twin: a LIST value opens, anything else is the
      -- pattern's kind mismatch (`Result.listPatternItems?`).
      match Result.listPatternItems? input.fst with
      | none => .error (structuralPatternKindMismatch pattern input.fst)
      | some elements =>
          let nestedInputs := elements.map (fun value => (value, Result.valueCount value))
          bindCountedParameterPatternList items nestedInputs
  | .unpacking items =>
      -- The deconstruction unpacking receiver opens ONE level of either kind and
      -- treats any other value as one item (`Result.spreadItems`), exactly as
      -- the ordinary binder does.
      let nestedInputs := (Result.spreadItems input.fst).map (fun value => (value, Result.valueCount value))
      bindCountedParameterPatternList items nestedInputs

partial def bindCountedParameterPatternList (patterns : List ParameterPattern)
  (inputs : List CountedResult) : EvalM CountedParameterPatternBindings := do
  let rec findCollecting : List ParameterPattern -> Nat -> Option (Nat × CallableParameter)
    | [], _ => none
    | (.capture parameter) :: rest, index =>
        match parameter.kind with
        | .collecting => some (index, parameter)
        | .normal => findCollecting rest (index + 1)
    | (.sequenceValue _) :: rest, index => findCollecting rest (index + 1)
    | (.listValue _) :: rest, index => findCollecting rest (index + 1)
    | (.unpacking _) :: rest, index => findCollecting rest (index + 1)
  -- The same binding and merge order as `bindParameterPatternList`: every
  -- pattern of a range binds before anything merges, and each repeated name
  -- is decided once, symmetrically, when its last contribution joins
  -- (`settlePatternRange`); counted contributions carry only the counted
  -- channel, so an unequal repeat is `badArity`.
  let asContribution (bindings : CountedParameterPatternBindings) : ParameterPatternBindings :=
    { countedParamEnv := bindings.countedParamEnv }
  let rec bindPairs : List ParameterPattern -> List CountedResult -> EvalM (List ParameterPatternBindings)
    | [], [] => pure []
    | pattern :: patterns', input :: inputs' => do
        let current <- bindCountedParameterPattern pattern input
        let rest <- bindPairs patterns' inputs'
        pure (asContribution current :: rest)
    | _, _ => .error (Error.arityMismatch patterns.length inputs.length)
  let settle (outside : Ident -> Bool) (bound : List ParameterPatternBindings) : EvalM Unit :=
    match settlePatternRange outside bound [] with
    | some error => .error error
    | none => pure ()
  let merged (contributions : List ParameterPatternBindings) : CountedParameterPatternBindings :=
    { countedParamEnv := (mergeFirstOccurrences contributions).countedParamEnv }
  -- The accepted supply is the ONE minimum-supply rule
  -- (`ParameterPattern.minimumSuppliedSlots`): without a collecting capture
  -- every pattern needs its own slot, so the count is EXACT; with one the
  -- minimum is a lower bound and the collector takes whatever is left over.
  match findCollecting patterns 0 with
  | none =>
      let required := ParameterPattern.minimumSuppliedSlots patterns
      if inputs.length != required then
        .error (Error.arityMismatch required inputs.length)
      else do
        let bound <- bindPairs patterns inputs
        settle (fun _ => false) bound
        pure (merged bound)
  | some (collectingIndex, collectingParameter) =>
      let required := ParameterPattern.minimumSuppliedSlots patterns
      if inputs.length < required then
        .error (Error.arityMismatch required inputs.length)
      else
        let prefixPatterns := patterns.take collectingIndex
        let prefixInputs := inputs.take collectingIndex
        let suffixCount := patterns.length - collectingIndex - 1
        let suffixPatterns := patterns.drop (collectingIndex + 1)
        let suffixInputs := inputs.drop (inputs.length - suffixCount)
        let capturedInputs := (inputs.drop collectingIndex).take (inputs.length - suffixCount - collectingIndex)
        let prefixBound <- bindPairs prefixPatterns prefixInputs
        settle (fun name => ParameterPattern.anyBindsName name suffixPatterns
          || collectingParameter.name == name) prefixBound
        let suffixBound <- bindPairs suffixPatterns suffixInputs
        settle (fun name => ParameterPattern.anyBindsName name prefixPatterns
          || collectingParameter.name == name) suffixBound
        -- Collecting binding COLLECTS exactly the items allocated to it as one
        -- exact immutable list value, emitted count 1 (a list is one visible
        -- value): it never opens an item (THE EXACT COLLECTOR LAW).
        let captured := collectSegment (capturedInputs.map Prod.fst)
        let capturedBinding := (collectingParameter.name, (captured, 1))
        let collectingBindings : ParameterPatternBindings :=
          { countedParamEnv := [capturedBinding] }
        let leftSide := prefixBound ++ [collectingBindings]
        let atCollector := [collectingParameter.name].filter (fun name =>
          prefixBound.any (fun contribution => contribution.binds name)
            && !ParameterPattern.anyBindsName name suffixPatterns)
        match repeatedNameFailure atCollector leftSide with
        | some error => .error error
        | none =>
            let atSuffix := (suffixBound.flatMap ParameterPatternBindings.names).eraseDups.filter
              (fun name => leftSide.any (fun contribution => contribution.binds name))
            match repeatedNameFailure atSuffix (leftSide ++ suffixBound) with
            | some error => .error error
            | none => pure (merged (leftSide ++ suffixBound))
      end


/-- `sizeOf` of a list prefix never exceeds the list's `sizeOf`.
    Termination support for the pattern-binding mutual pair below. -/
private theorem list_take_sizeOf_le [SizeOf α] (n : Nat) (xs : List α) :
    sizeOf (List.take n xs) ≤ sizeOf xs := by
  induction xs generalizing n with
  | nil => cases n <;> simp [List.take]
  | cons x xs ih =>
      cases n with
      | zero => simp [List.take]; omega
      | succ n =>
          simp only [List.take, List.cons.sizeOf_spec]
          have := ih n
          omega

/-- `sizeOf` of a list suffix never exceeds the list's `sizeOf`.
    Termination support for the pattern-binding mutual pair below. -/
private theorem list_drop_sizeOf_le [SizeOf α] (n : Nat) (xs : List α) :
    sizeOf (List.drop n xs) ≤ sizeOf xs := by
  induction xs generalizing n with
  | nil => cases n <;> simp [List.drop]
  | cons x xs ih =>
      cases n with
      | zero => simp [List.drop]
      | succ n =>
          simp only [List.drop, List.cons.sizeOf_spec]
          have := ih n
          omega

mutual
  /-- Bind ONE pattern of the pattern `level` (the complete list of patterns at this
      level, the pattern itself included) against its supplied input. -/
  def bindParameterPattern (level : List ParameterPattern) (pattern : ParameterPattern)
      (input : ParameterPatternInput) (allowAlgorithmBindings : Bool)
      : EvalM ParameterPatternBindings := do
    match pattern with
    | .capture parameter =>
        match parameter.kind with
        | .normal =>
            let argEnv := match input.value? with
              | some value => [(parameter.name, value)]
              | none => []
            -- AT-MOST-ONCE ARGUMENT VALUE EVALUATION: a slot whose value evaluation
            -- failed keeps that failure as the parameter's value outcome, beside the
            -- algorithm channel; it is never re-derived from the algorithm.
            let algEnv :=
              if allowAlgorithmBindings then
                match input.algorithm? with
                | some algorithm => [(parameter.name, slotAlgorithmBinding input.value? input.error? algorithm)]
                | none => []
              else []
            -- A valueless slot binds a capture only through its algorithm channel, and
            -- only where the capture does not need a value. REPEATED NAMES ARE
            -- CONSTRAINTS, NOT MERGES (Q-05): a capture whose name the level repeats is
            -- an equality constraint over independently supplied arguments, so it needs
            -- its slot's OWN value, exactly as a sequence-value pattern needs the value
            -- it opens. A callable-only argument (`Inc` passed bare) or a failed one
            -- (`Bad = 1 / 0`) fails here with the slot's own recorded outcome; another
            -- occurrence's value never stands in for it, and no binding pairs one
            -- argument's value with another's algorithm.
            if input.value?.isNone && (input.algorithm?.isNone || !allowAlgorithmBindings
                || ParameterPattern.repeatsAtLevel parameter.name level) then
              .error (input.error?.getD Error.badArity)
            else
              pure { argEnv := argEnv, countedParamEnv := [], algEnv := algEnv }
        | .collecting => .error Error.badArity
    | .sequenceValue items => do
        -- STRUCTURAL PATTERN DELIMITERS SELECT THE VALUE KIND THEY DESTRUCTURE
        -- (September 2026): a sequence pattern `(…)` consumes ONE argument slot
        -- and opens that slot's VALUE only when it is a SEQUENCE value
        -- (`Result.sequencePatternItems?`); a list value or a scalar is the
        -- pattern's kind mismatch (`structuralPatternKindMismatch`), never an
        -- implicit one-item supply and never an opened list. Pattern parentheses
        -- are still call-shape syntax, not a runtime boundary: nothing about how
        -- the slot was WRITTEN survives here — `F((1, 2))`, `F(S)` with
        -- `S = 1, 2`, `F(((1, 2)))`, `F({S})`, and `F((S*))` all bind the value
        -- `(1, 2)`. The opening rule is shared with the counted callback binder
        -- `bindCountedParameterPattern` (S3).
        match input.value? with
        | none => .error (input.error?.getD Error.badArity)
        | some value =>
            match Result.sequencePatternItems? value with
            | none => .error (structuralPatternKindMismatch pattern value)
            | some elements =>
                let nestedInputs := elements.map (fun element => { value? := some element : ParameterPatternInput })
                bindParameterPatternList items nestedInputs false
    | .listValue items => do
        -- The list pattern `[…]`: opens the slot's value only when it is a LIST
        -- value (`Result.listPatternItems?`), keeping every cardinality — `[]`,
        -- `[x]`, `[x, *rest]` — and rejects a sequence or a scalar as its kind
        -- mismatch.
        match input.value? with
        | none => .error (input.error?.getD Error.badArity)
        | some value =>
            match Result.listPatternItems? value with
            | none => .error (structuralPatternKindMismatch pattern value)
            | some elements =>
                let nestedInputs := elements.map (fun element => { value? := some element : ParameterPatternInput })
                bindParameterPatternList items nestedInputs false
    | .unpacking items => do
        -- THE UNPACKING RECEIVER of assignment deconstruction: it demands the ONE
        -- supplied value like any pattern that opens a value (a slot without one
        -- fails with its own recorded outcome, so a right-hand side without output
        -- is that missing output — never a spread failure) and binds the target
        -- list against the value's ONE-LEVEL items: a sequence or a list opens one
        -- level and any other value is one item (`Result.spreadItems`). It is the
        -- only receiver that opens both kinds; no written pattern does.
        match input.value? with
        | none => .error (input.error?.getD Error.badArity)
        | some value =>
            let nestedInputs := (Result.spreadItems value).map (fun element => { value? := some element : ParameterPatternInput })
            bindParameterPatternList items nestedInputs false
  -- Termination: the pattern-side `sizeOf` shrinks around the recursion cycle;
  -- the +1 tag on the list function breaks the tie for same-list entry calls.
  termination_by 2 * sizeOf pattern
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def bindParameterPatternList (patterns : List ParameterPattern)
      (inputs : List ParameterPatternInput) (allowAlgorithmBindings : Bool)
      : EvalM ParameterPatternBindings := do
    let rec findCollecting : List ParameterPattern -> Nat -> Option (Nat × CallableParameter)
      | [], _ => none
      | (.capture parameter) :: rest, index =>
          match parameter.kind with
          | .collecting => some (index, parameter)
          | .normal => findCollecting rest (index + 1)
      | (.sequenceValue _) :: rest, index => findCollecting rest (index + 1)
      | (.listValue _) :: rest, index => findCollecting rest (index + 1)
      | (.unpacking _) :: rest, index => findCollecting rest (index + 1)
    -- `bindPairs` binds EVERY pattern of a range, left to right, before
    -- anything merges: the first binding failure wins over any repeated-name
    -- conflict of the range (September 2026). `settle` then decides the
    -- range's repeated names in the merge order (`settlePatternRange`). A
    -- repeated name's valueless contribution is such a binding failure (Q-05):
    -- each pattern binds against the WHOLE level, which says whether its name
    -- repeats.
    let rec bindPairs : List ParameterPattern -> List ParameterPatternInput
        -> EvalM (List ParameterPatternBindings)
      | [], [] => pure []
      | pattern :: patterns', input :: inputs' => do
          let current <- bindParameterPattern patterns pattern input allowAlgorithmBindings
          let rest <- bindPairs patterns' inputs'
          pure (current :: rest)
      | _, _ => .error (Error.arityMismatch patterns.length inputs.length)
      termination_by ps _ => 2 * sizeOf ps
      decreasing_by
        all_goals simp_wf
        all_goals omega
    let settle (outside : Ident -> Bool) (bound : List ParameterPatternBindings) : EvalM Unit :=
      match settlePatternRange outside bound [] with
      | some error => .error error
      | none => pure ()
    -- The accepted supply is the ONE minimum-supply rule
    -- (`ParameterPattern.minimumSuppliedSlots`): without a collecting capture
    -- every pattern needs its own slot, so the count is EXACT; with one the
    -- minimum is a lower bound and the collector takes whatever is left over.
    match findCollecting patterns 0 with
    | none =>
        let required := ParameterPattern.minimumSuppliedSlots patterns
        if inputs.length != required then
          .error (Error.arityMismatch required inputs.length)
        else do
          let bound <- bindPairs patterns inputs
          settle (fun _ => false) bound
          pure (mergeFirstOccurrences bound)
    | some (collectingIndex, collectingParameter) =>
        let required := ParameterPattern.minimumSuppliedSlots patterns
        if inputs.length < required then
          .error (Error.arityMismatch required inputs.length)
        else
          let prefixPatterns := patterns.take collectingIndex
          let prefixInputs := inputs.take collectingIndex
          let suffixCount := patterns.length - collectingIndex - 1
          let suffixPatterns := patterns.drop (collectingIndex + 1)
          let suffixInputs := inputs.drop (inputs.length - suffixCount)
          let capturedInputs := (inputs.drop collectingIndex).take (inputs.length - suffixCount - collectingIndex)
          -- The prefix binds and settles its own repeated names, then the
          -- suffix; a name the level also binds on the other side of the
          -- collector (or as the collector) waits for the cross merges below.
          let prefixBound <- bindPairs prefixPatterns prefixInputs
          settle (fun name => ParameterPattern.anyBindsName name suffixPatterns
            || collectingParameter.name == name) prefixBound
          let suffixBound <- bindPairs suffixPatterns suffixInputs
          settle (fun name => ParameterPattern.anyBindsName name prefixPatterns
            || collectingParameter.name == name) suffixBound
          let rec collectValues : List ParameterPatternInput -> EvalM (List Result)
            | [] => pure []
            | input :: rest =>
                match input.value? with
                | some value => do
                    let values <- collectValues rest
                    -- Every item allocated to the flat top-level collecting
                    -- position contributes its ONE reified value, unopened.
                    pure (value :: values)
                | none =>
                    -- A collecting binding collects VALUES. A callable-shaped
                    -- argument (one a zero-argument call cannot bind: a builtin,
                    -- a clause family, or an algorithm that requires a supplied
                    -- argument) has no value to collect — only fixed
                    -- parameters keep the dual algorithm channel — so name
                    -- the actual conflict instead of surfacing the argument's
                    -- incidental value-evaluation error. A VALUE — a zero-parameter
                    -- property or any callable accepting zero supplied arguments,
                    -- a collecting-only one included (Q-03) — whose evaluation
                    -- failed is NOT callable-shaped: its genuine error surfaces.
                    -- C#: `BindParameterPatternList` (whose message also
                    -- names the collecting parameter).
                    match input.algorithm? with
                    | some alg =>
                        if alg.isFunctionShaped then
                          .error (Error.typeMismatch
                            "A collecting parameter collects values, but a supplied argument is a callable. Pass a value, or call the callable so its result is collected.")
                        else
                          .error (input.error?.getD Error.badArity)
                    | none => .error (input.error?.getD Error.badArity)
          let segment <- collectValues capturedInputs
          -- Collecting binding COLLECTS exactly the items allocated to it as
          -- one exact immutable list value, emitted count 1 (a list is one
          -- visible value): it never opens an item (THE EXACT COLLECTOR LAW).
          let captured := collectSegment segment
          let collectingBindings : ParameterPatternBindings :=
            { argEnv := [(collectingParameter.name, captured)],
              countedParamEnv := [(collectingParameter.name, (captured, 1))],
              algEnv := [] }
          -- Merge the prefix with the collector, then that with the suffix:
          -- the collector's name completes at the first merge unless the
          -- suffix binds it too, and every name shared with the suffix
          -- completes at the second.
          let leftSide := prefixBound ++ [collectingBindings]
          let atCollector := [collectingParameter.name].filter (fun name =>
            prefixBound.any (fun contribution => contribution.binds name)
              && !ParameterPattern.anyBindsName name suffixPatterns)
          match repeatedNameFailure atCollector leftSide with
          | some error => .error error
          | none =>
              let atSuffix := (suffixBound.flatMap ParameterPatternBindings.names).eraseDups.filter
                (fun name => leftSide.any (fun contribution => contribution.binds name))
              match repeatedNameFailure atSuffix (leftSide ++ suffixBound) with
              | some error => .error error
              | none => pure (mergeFirstOccurrences (leftSide ++ suffixBound))
  termination_by 2 * sizeOf patterns + 1
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have take_le := list_take_sizeOf_le collectingIndex patterns
         omega)
      | (have drop_le := list_drop_sizeOf_le (collectingIndex + 1) patterns
         omega)
end


end KatLang.HistoricalReadyBinding
