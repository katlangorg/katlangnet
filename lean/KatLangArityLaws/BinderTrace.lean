import KatLangArityLaws

open KatLang

/-!
# The external boundary trace of the Model-C binder (R3, October 2026)

The production binder is the generic core `NeedBinder` at `EvalM` (`KatLangArityLaws.lean`
§ The generic binder core, namespace `KatLang.BinderCore`).
This module runs THE SAME core in a second interpretation, `TraceM`, which records every VALUE
and CALLABLE invocation of the binder and every successful allocation (a failed
allocation records nothing) — never anything inside a capability — and proves that the recording
is an exact, protected observation of the production run:

* events are `VALUE(a)` / `CALLABLE(a)`, emitted immediately BEFORE the VALUE demand / CALLABLE
  projection of address `a` — so a failing VALUE or CALLABLE invocation is always the LAST event
  of its run — and `collector(a, slice)` / `ready(a)`, emitted immediately AFTER an allocation
  SUCCEEDED, carrying the address it returned (the next heap position for the production
  allocator, `production_ready_cells`); a FAILED allocation records nothing, so its run ends at
  the last completed invocation (`traced_collector_allocation_failure`; the production
  allocator `allocateNeed` never fails; `traced_ready_allocation_failure` for ready cells);
* `TraceM = ExceptT Error (StateM TraceState)`: the error sits OUTSIDE the state, so a raised
  error keeps both the semantic state and the trace reached so far (the production `EvalM` stack
  has the same order: completed effects survive a failure);
* production capabilities are LIFTED (`traced`): a lifted operation runs the production
  operation on the semantic state and cannot read, clear or forge the trace.

What is observed is the BINDER BOUNDARY: one event per VALUE or CALLABLE invocation the binder
makes and per allocation that succeeded.
A VALUE event is not a count of evaluations — a channel may answer from a completed cell, and
work inside a channel (nested demands, cache publication, host effects) is not observed.

Nothing here touches production: `EvalState` has no trace field, the evaluator never runs
`TraceM`, and C# is unaffected.

THE ORDERING BEHAVIOURS the schedule establishes (the numbers cited by the laws below):
(1) a level's cardinality is checked before any of its patterns is inspected;
(2) a level's sources are visited in written order;
(3) a collector source is allocated before its pattern is bound;
(4) a plain, non-repeated binding invokes neither VALUE nor CALLABLE;
(5) an inspecting literal invokes VALUE before matching;
(6) structural inspection invokes the parent's VALUE first;
(7) structural-kind validation follows the existing kind views;
(8) ready cells are allocated in item order;
(9) the nested cardinality gate follows those allocations;
(10) nested patterns are processed depth first;
(11) the next sibling is processed only after the preceding pattern bound;
(12) a non-match or a raised failure prevents every later inspection.
The schedule functions `oneEvents` / `sourcesEvents` state all twelve at once (each clause
fixes where its events occur); `traced_one` / `traced_sources` prove the traced binder emits
exactly them, and the named laws below restate each behaviour directly.
-/

namespace KatLang.BinderTrace

/-! ## The trace interpretation -/

/-- One binder-boundary event. -/
inductive NeedEvent where
  /-- Emitted immediately before the VALUE demand of `address`. -/
  | value (address : Nat)
  /-- Emitted immediately before the CALLABLE projection of `address`. -/
  | callable (address : Nat)
  /-- Emitted immediately after a collector allocation returned `address`. -/
  | collector (address : Nat) (slice : List Nat)
  /-- Emitted immediately after a ready-cell allocation returned `address`. -/
  | ready (address : Nat)
  /-- Emitted after any other allocation (the binder never allocates one). -/
  | expression (address : Nat)
  /-- Emitted immediately after a META reification of `address` (CallReference S1) returned
      its Ready adapter cell `adapter`; a refused reification records nothing. -/
  | reference (address : Nat) (adapter : Nat)
  deriving Repr, BEq, DecidableEq

/-- The semantic evaluator state and the boundary events recorded so far. -/
structure TraceState where
  semantic : EvalState
  events : List NeedEvent

/-- The trace interpretation: errors outside the state, so a failure keeps both components. -/
abbrev TraceM := ExceptT Error (StateM TraceState)

/-- Run a traced computation. -/
def runTrace {α : Type} (x : TraceM α) (t : TraceState) : Except Error α × TraceState := x t

/-- Run a production computation (the retained-state observation `EvalM.runState`). -/
def runEval {α : Type} (y : EvalM α) (s : EvalState) : Except Error α × EvalState := y.runState s

/-- Continue a run result: the continuation runs on success only; an error keeps its state. -/
def thenRun {α β σ : Type} (r : Except Error α × σ) (k : α → σ → Except Error β × σ) :
    Except Error β × σ :=
  match r with
  | (.ok a, s) => k a s
  | (.error e, s) => (.error e, s)

@[simp] theorem thenRun_ok {α β σ : Type} (a : α) (s : σ) (k : α → σ → Except Error β × σ) :
    thenRun (.ok a, s) k = k a s := rfl

@[simp] theorem thenRun_error {α β σ : Type} (e : Error) (s : σ) (k : α → σ → Except Error β × σ) :
    thenRun (.error e, s) k = (.error e, s) := rfl

/-- Append one event (the observation's only write). -/
def emit (event : NeedEvent) : TraceM Unit :=
  fun t => (.ok (), { t with events := t.events ++ [event] })

/-- Lift a production computation: it runs on the semantic state only and never sees the trace. -/
def liftEval {α : Type} (y : EvalM α) : TraceM α :=
  fun t =>
    let r := runEval y t.semantic
    (r.1, { t with semantic := r.2 })

/-- The event of an allocation that returned `address`. -/
def allocationEvent (suspension : NeedSuspension) (address : Nat) : NeedEvent :=
  match suspension with
  | .collector slice => .collector address slice
  | .ready _ => .ready address
  | .expression _ _ _ => .expression address

/-- THE PROTECTED TRACING of production capabilities: each VALUE / CALLABLE invocation records
    its event and then runs the production operation; each allocation runs the production
    allocation and then records the address it returned. The lifted operations cannot access
    the trace. -/
def traced (k : NeedCapabilities EvalM) : NeedCapabilities TraceM where
  value address := do emit (.value address); liftEval (k.value address)
  callable address := do emit (.callable address); liftEval (k.callable address)
  allocate suspension := do
    let address <- liftEval (k.allocate suspension)
    emit (allocationEvent suspension address)
    pure address
  reference address := do
    let adapter <- liftEval (k.reference address)
    emit (.reference address adapter)
    pure adapter

/-! ### Run equations -/

@[simp] theorem runTrace_pure {α : Type} (a : α) (t : TraceState) :
    runTrace (pure a : TraceM α) t = (.ok a, t) := rfl

@[simp] theorem runTrace_throw {α : Type} (e : Error) (t : TraceState) :
    runTrace (throw e : TraceM α) t = (.error e, t) := rfl

@[simp] theorem runTrace_bind {α β : Type} (x : TraceM α) (f : α → TraceM β) (t : TraceState) :
    runTrace (x >>= f) t = thenRun (runTrace x t) (fun a t' => runTrace (f a) t') := by
  simp only [runTrace, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind]
  rcases x t with ⟨r, t'⟩
  cases r <;> rfl

@[simp] theorem runTrace_map {α β : Type} (f : α → β) (x : TraceM α) (t : TraceState) :
    runTrace (f <$> x) t = thenRun (runTrace x t) (fun a t' => (.ok (f a), t')) := by
  simp only [runTrace, Functor.map, ExceptT.map, ExceptT.mk, bind, StateT.bind]
  rcases x t with ⟨r, t'⟩
  cases r <;> rfl

@[simp] theorem runTrace_emit (event : NeedEvent) (s : EvalState) (tr : List NeedEvent) :
    runTrace (emit event) ⟨s, tr⟩ = (.ok (), ⟨s, tr ++ [event]⟩) := rfl

@[simp] theorem runTrace_liftEval {α : Type} (y : EvalM α) (s : EvalState) (tr : List NeedEvent) :
    runTrace (liftEval y) ⟨s, tr⟩ = ((runEval y s).1, ⟨(runEval y s).2, tr⟩) := rfl

@[simp] theorem runEval_pure {α : Type} (a : α) (s : EvalState) :
    runEval (pure a : EvalM α) s = (.ok a, s) := rfl

@[simp] theorem runEval_throw {α : Type} (e : Error) (s : EvalState) :
    runEval (throw e : EvalM α) s = (.error e, s) := rfl

@[simp] theorem runEval_bind {α β : Type} (y : EvalM α) (g : α → EvalM β) (s : EvalState) :
    runEval (y >>= g) s = thenRun (runEval y s) (fun a s' => runEval (g a) s') := by
  simp only [runEval, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind]
  rcases y.runState s with ⟨r, s'⟩
  cases r <;> rfl

@[simp] theorem runTrace_value (k : NeedCapabilities EvalM) (address : Nat) (s : EvalState) (tr : List NeedEvent) :
    runTrace ((traced k).value address) ⟨s, tr⟩
      = ((runEval (k.value address) s).1, ⟨(runEval (k.value address) s).2, tr ++ [.value address]⟩) := by
  simp [traced]

@[simp] theorem runTrace_callable (k : NeedCapabilities EvalM) (address : Nat) (s : EvalState) (tr : List NeedEvent) :
    runTrace ((traced k).callable address) ⟨s, tr⟩
      = ((runEval (k.callable address) s).1, ⟨(runEval (k.callable address) s).2, tr ++ [.callable address]⟩) := by
  simp [traced]

theorem runTrace_allocate (k : NeedCapabilities EvalM) (suspension : NeedSuspension) (s : EvalState)
    (tr : List NeedEvent) :
    runTrace ((traced k).allocate suspension) ⟨s, tr⟩
      = match runEval (k.allocate suspension) s with
        | (.ok address, s') => (.ok address, ⟨s', tr ++ [allocationEvent suspension address]⟩)
        | (.error e, s') => (.error e, ⟨s', tr⟩) := by
  simp only [traced, runTrace_bind, runTrace_liftEval]
  rcases runEval (k.allocate suspension) s with ⟨r, s'⟩
  cases r <;> simp

theorem runTrace_reference (k : NeedCapabilities EvalM) (address : Nat) (s : EvalState)
    (tr : List NeedEvent) :
    runTrace ((traced k).reference address) ⟨s, tr⟩
      = match runEval (k.reference address) s with
        | (.ok adapter, s') => (.ok adapter, ⟨s', tr ++ [.reference address adapter]⟩)
        | (.error e, s') => (.error e, ⟨s', tr⟩) := by
  simp only [traced, runTrace_bind, runTrace_liftEval]
  rcases runEval (k.reference address) s with ⟨r, s'⟩
  cases r <;> simp

/-! ## The event schedule

`TracesAs x y events` says that the traced computation `x` is an exact, protected observation
of the production computation `y` whose appended events are `events s`: from EVERY semantic
state `s` and EVERY event prefix `tr`, `x` returns exactly `y`'s outcome and final semantic
state, keeps `tr`, and appends exactly `events s` — which therefore depends on the semantic
state alone, never on the prefix. -/

/-- `x` observes `y` exactly, appending `events s` from semantic state `s`. -/
def TracesAs {α : Type} (x : TraceM α) (y : EvalM α) (events : EvalState → List NeedEvent) : Prop :=
  ∀ s tr, runTrace x ⟨s, tr⟩ = ((runEval y s).1, ⟨(runEval y s).2, tr ++ events s⟩)

/-- THE SCHEDULE OF ONE REPEATED-NAME OCCURRENCE (NEED-04, Q-28), in the order the binder
    invokes the capabilities: VALUE of the current cell; then, only if it succeeded and the
    name is already bound, VALUE of the retained representative; then, only if that succeeded
    and the two counted values are equal, CALLABLE of the representative; then, only if that
    succeeded, CALLABLE of the current cell. Every later event is conditional on the earlier
    outcomes — a failure or an unequal value ends the occurrence's events. -/
def repeatedNameEvents (k : NeedCapabilities EvalM) (address : Nat) (previous? : Option Nat)
    (s : EvalState) : List NeedEvent :=
  .value address ::
    match runEval (k.value address) s with
    | (.error _, _) => []
    | (.ok value, s1) =>
      match previous? with
      | none => []
      | some previous =>
        .value previous ::
          match runEval (k.value previous) s1 with
          | (.error _, _) => []
          | (.ok before, s2) =>
            if (!(before == value)) = true then []
            else
              .callable previous ::
                match runEval (k.callable previous) s2 with
                | (.error _, _) => []
                | (.ok _, _) => [.callable address]

/-- One name occurrence: a non-repeated name emits NOTHING; a repeated one follows
    `repeatedNameEvents` against its representative in the binding so far. -/
def nameEvents (k : NeedCapabilities EvalM) (name : Ident) (address : Nat) (repeated : List Ident)
    (bound : NeedEnv) (s : EvalState) : List NeedEvent :=
  if repeated.contains name = true then repeatedNameEvents k address (lookupAssoc name bound) s else []

/-- The ready-cell allocations of a structural pattern's opened items, in item order: one
    `ready(a)` per successful allocation, stopping at a failed one. -/
def readyEvents (k : NeedCapabilities EvalM) : List Result → EvalState → List NeedEvent
  | [], _ => []
  | item :: rest, s =>
    match runEval (k.allocate (.ready (item, Result.valueCount item))) s with
    | (.ok address, s') => .ready address :: readyEvents k rest s'
    | (.error _, _) => []

/-- The address resolution of one source: a supplied cell and a missing position emit nothing;
    a collector slice emits the allocation of its fresh collector cell. -/
def addressEvents (k : NeedCapabilities EvalM) (source : NeedSource Nat) (s : EvalState) : List NeedEvent :=
  match source with
  | .collector slice =>
    match runEval (k.allocate (.collector slice)) s with
    | (.ok address, _) => [.collector address slice]
    | (.error _, _) => []
  | _ => []

/-- The production allocation of a structural pattern's opened items (the binder's own
    `mapM`, at `EvalM`). -/
def readyCells (k : NeedCapabilities EvalM) (items : List Result) : EvalM (List Nat) :=
  items.mapM (fun item => k.allocate (.ready (item, Result.valueCount item)))

mutual
  /-- THE EVENT SCHEDULE OF ONE PATTERN, by its syntax. Every state and outcome it consults is
      the PRODUCTION run (`runEval`) of the generic core at `k`: the schedule decides only
      WHERE events occur, never what the binder computes.

      * a name: `nameEvents` (nothing for a non-repeated name);
      * a literal: exactly `VALUE(a)`;
      * a structural pattern: `VALUE(a)` first; then, only if that demand succeeded and the
        value has the pattern's own kind, the ready allocations of its items in order; then,
        only if all of them succeeded and the nested level's cardinality gate accepts, the
        nested patterns' schedule — depth first. A failed demand, the wrong kind, a failed
        allocation or a rejected nested count ends the pattern's events. -/
  def oneEvents (k : NeedCapabilities EvalM) : NeedPattern → Nat → List Ident → NeedEnv → Bool →
      EvalState → List NeedEvent
    | .bind name _, address, repeated, bound, _, s => nameEvents k name address repeated bound s
    | .literal _, address, _, _, _, _ => [.value address]
    | .metaRef name, address, repeated, bound, _, s =>
      match runEval (k.reference address) s with
      | (.error _, _) => []
      | (.ok adapter, s1) => .reference address adapter :: nameEvents k name adapter repeated bound s1
    | .sequence ps, address, repeated, bound, family, s =>
      .value address ::
        match runEval (k.value address) s with
        | (.error _, _) => []
        | (.ok (value, _), s1) =>
          match Result.sequencePatternItems? value with
          | none => []
          | some items =>
            readyEvents k items s1 ++
              match runEval (readyCells k items) s1 with
              | (.error _, _) => []
              | (.ok cells, s2) =>
                if needAcceptsCardinality ps cells.length = true then
                  sourcesEvents k ps (needLevelSources ps cells) repeated bound family s2
                else []
    | .list ps, address, repeated, bound, family, s =>
      .value address ::
        match runEval (k.value address) s with
        | (.error _, _) => []
        | (.ok (value, _), s1) =>
          match Result.listPatternItems? value with
          | none => []
          | some items =>
            readyEvents k items s1 ++
              match runEval (readyCells k items) s1 with
              | (.error _, _) => []
              | (.ok cells, s2) =>
                if needAcceptsCardinality ps cells.length = true then
                  sourcesEvents k ps (needLevelSources ps cells) repeated bound family s2
                else []
    | .unpack ps, address, repeated, bound, family, s =>
      .value address ::
        match runEval (k.value address) s with
        | (.error _, _) => []
        | (.ok (value, _), s1) =>
          readyEvents k (Result.spreadItems value) s1 ++
            match runEval (readyCells k (Result.spreadItems value)) s1 with
            | (.error _, _) => []
            | (.ok cells, s2) =>
              if needAcceptsCardinality ps cells.length = true then
                sourcesEvents k ps (needLevelSources ps cells) repeated bound family s2
              else []

  /-- THE EVENT SCHEDULE OF ONE LEVEL'S PATTERNS, in written order: for each pattern, its
      source's address events, then — only if the address resolved — the pattern's own
      schedule, then — only if the pattern bound (neither failed nor mismatched) — the
      remaining patterns from the state it left. -/
  def sourcesEvents (k : NeedCapabilities EvalM) : List NeedPattern → List (NeedSource Nat) →
      List Ident → NeedEnv → Bool → EvalState → List NeedEvent
    | [], _, _, _, _, _ => []
    | pattern :: rest, sources, repeated, bound, family, s =>
      addressEvents k (sources.headD .missing) s ++
        match runEval (NeedBinder.sourceAddress k.allocate (sources.headD .missing)) s with
        | (.error _, _) => []
        | (.ok address, s1) =>
          oneEvents k pattern address repeated bound family s1 ++
            match runEval (NeedBinder.bindOne k pattern address repeated bound family) s1 with
            | (.ok (some next), s2) => sourcesEvents k rest sources.tail repeated next family s2
            | _ => []
end

/-- One level: nothing if the cardinality gate rejects, otherwise its patterns' schedule. -/
def levelEvents (k : NeedCapabilities EvalM) (ps : List NeedPattern) (cells : List Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState) : List NeedEvent :=
  if needAcceptsCardinality ps cells.length = true then
    sourcesEvents k ps (needLevelSources ps cells) repeated bound family s
  else []

/-- A whole head. -/
def patternsEvents (k : NeedCapabilities EvalM) (ps : List NeedPattern) (cells : List Nat)
    (family : Bool) (s : EvalState) : List NeedEvent :=
  levelEvents k ps cells (needRepeatedNames ps) [] family s

/-! ### The trace theorem: the traced core is the production core plus exactly the schedule -/

theorem traced_ready_loop (k : NeedCapabilities EvalM) (items : List Result) (acc : List Nat) :
    TracesAs
      (List.mapM.loop (fun item => (traced k).allocate (.ready (item, Result.valueCount item))) items acc)
      (List.mapM.loop (fun item => k.allocate (.ready (item, Result.valueCount item))) items acc)
      (readyEvents k items) := by
  induction items generalizing acc with
  | nil =>
    intro s tr
    simp [List.mapM.loop, readyEvents]
  | cons item rest ih =>
    intro s tr
    simp only [List.mapM.loop, runTrace_bind, runEval_bind, runTrace_allocate, readyEvents]
    rcases h : runEval (k.allocate (.ready (item, Result.valueCount item))) s with ⟨_ | address, s'⟩
    · simp
    · simp [ih (address :: acc) s', allocationEvent]

theorem traced_ready (k : NeedCapabilities EvalM) (items : List Result) :
    TracesAs
      (items.mapM (fun item => (traced k).allocate (.ready (item, Result.valueCount item))))
      (readyCells k items) (readyEvents k items) :=
  traced_ready_loop k items []

theorem traced_name (k : NeedCapabilities EvalM) (name : Ident) (address : Nat) (repeated : List Ident)
    (bound : NeedEnv) (family : Bool) :
    TracesAs (NeedBinder.bindName (traced k) name address repeated bound family)
      (NeedBinder.bindName k name address repeated bound family)
      (nameEvents k name address repeated bound) := by
  intro s tr
  by_cases hr : repeated.contains name = true
  · simp only [NeedBinder.bindName, hr, ↓reduceIte, nameEvents, repeatedNameEvents]
    rcases h1 : runEval (k.value address) s with ⟨_ | value, s1⟩
    · simp [h1]
    · cases hl : lookupAssoc name bound with
      | none => simp [h1]
      | some previous =>
        rcases h2 : runEval (k.value previous) s1 with ⟨_ | before, s2⟩
        · simp [h1, h2]
        · cases hbv : (before == value)
          · cases family <;> simp [h1, h2, hbv]
          · rcases h3 : runEval (k.callable previous) s2 with ⟨_ | first, s3⟩
            · simp [h1, h2, hbv, h3]
            · rcases h4 : runEval (k.callable address) s3 with ⟨_ | second, s4⟩
              · simp [h1, h2, hbv, h3, h4]
              · cases first with
                | none => cases second <;> simp [h1, h2, hbv, h3, h4]
                | some a =>
                  cases second with
                  | none => simp [h1, h2, hbv, h3, h4]
                  | some b =>
                    cases hid : sameRepeatedCallableIdentity a b
                    · cases family <;> simp [h1, h2, hbv, h3, h4, hid]
                    · simp [h1, h2, hbv, h3, h4, hid]
  · have hr' : repeated.contains name = false := by simpa using hr
    simp only [NeedBinder.bindName, hr', Bool.false_eq_true, ↓reduceIte, nameEvents]
    simp

theorem traced_address (k : NeedCapabilities EvalM) (source : NeedSource Nat) :
    TracesAs (NeedBinder.sourceAddress (traced k).allocate source)
      (NeedBinder.sourceAddress k.allocate source) (addressEvents k source) := by
  intro s tr
  cases source with
  | cell address => simp [NeedBinder.sourceAddress, addressEvents]
  | missing => simp [NeedBinder.sourceAddress, addressEvents]
  | collector slice =>
    simp only [NeedBinder.sourceAddress, addressEvents, runTrace_allocate]
    rcases h : runEval (k.allocate (.collector slice)) s with ⟨_ | address, s'⟩ <;> simp [allocationEvent]

mutual
  /-- THE TRACE THEOREM, one pattern: for EVERY production capability record `k`, pattern,
      address, repeated-name index, binding so far, mode, semantic state and event prefix, the
      core run in the trace interpretation over the protected tracing of `k` returns exactly the
      production core's outcome and final semantic state, keeps the prefix, and appends exactly
      `oneEvents k …` — on success, non-match and every error alike. -/
  theorem traced_one (k : NeedCapabilities EvalM) (p : NeedPattern) (address : Nat)
      (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
      TracesAs (NeedBinder.bindOne (traced k) p address repeated bound family)
        (NeedBinder.bindOne k p address repeated bound family)
        (oneEvents k p address repeated bound family) := by
    intro s tr
    cases p with
    | bind name collecting =>
      simp only [NeedBinder.bindOne, oneEvents]
      exact traced_name k name address repeated bound family s tr
    | literal literal =>
      simp only [NeedBinder.bindOne, oneEvents]
      rcases h1 : runEval (k.value address) s with ⟨_ | ⟨value, count⟩, s1⟩ <;> simp [h1]
    | metaRef name =>
      simp only [NeedBinder.bindOne, oneEvents, runTrace_bind, runEval_bind, runTrace_reference]
      rcases h1 : runEval (k.reference address) s with ⟨_ | adapter, s1⟩
      · simp
      · simp only [thenRun_ok]
        rw [traced_name k name adapter repeated bound family s1]
        simp
    | sequence ps =>
      simp only [NeedBinder.bindOne, oneEvents]
      rcases h1 : runEval (k.value address) s with ⟨_ | ⟨value, count⟩, s1⟩
      · simp [h1]
      · cases hi : Result.sequencePatternItems? value with
        | none => cases family <;> simp [h1, hi]
        | some items =>
          simp only [readyCells] at *
          simp only [h1, hi, runTrace_bind, runEval_bind, runTrace_value, thenRun_ok]
          rw [traced_ready k items s1 (tr ++ [NeedEvent.value address])]
          rcases h2 : runEval (readyCells k items) s1 with ⟨_ | cells, s2⟩
          · simp only [readyCells] at h2
            simp [h2]
          · simp only [readyCells] at h2
            simp only [h2, thenRun_ok, NeedBinder.cardinalityGate]
            cases hacc : needAcceptsCardinality ps cells.length
            · cases family <;> simp
            · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              rw [traced_sources k ps (needLevelSources ps cells) repeated bound family s2]
              simp
    | list ps =>
      simp only [NeedBinder.bindOne, oneEvents]
      rcases h1 : runEval (k.value address) s with ⟨_ | ⟨value, count⟩, s1⟩
      · simp [h1]
      · cases hi : Result.listPatternItems? value with
        | none => cases family <;> simp [h1, hi]
        | some items =>
          simp only [readyCells] at *
          simp only [h1, hi, runTrace_bind, runEval_bind, runTrace_value, thenRun_ok]
          rw [traced_ready k items s1 (tr ++ [NeedEvent.value address])]
          rcases h2 : runEval (readyCells k items) s1 with ⟨_ | cells, s2⟩
          · simp only [readyCells] at h2
            simp [h2]
          · simp only [readyCells] at h2
            simp only [h2, thenRun_ok, NeedBinder.cardinalityGate]
            cases hacc : needAcceptsCardinality ps cells.length
            · cases family <;> simp
            · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              rw [traced_sources k ps (needLevelSources ps cells) repeated bound family s2]
              simp
    | unpack ps =>
      simp only [NeedBinder.bindOne, oneEvents]
      rcases h1 : runEval (k.value address) s with ⟨_ | ⟨value, count⟩, s1⟩
      · simp [h1]
      · simp only [readyCells] at *
        simp only [h1, runTrace_bind, runEval_bind, runTrace_value, thenRun_ok]
        rw [traced_ready k (Result.spreadItems value) s1 (tr ++ [NeedEvent.value address])]
        rcases h2 : runEval (readyCells k (Result.spreadItems value)) s1 with ⟨_ | cells, s2⟩
        · simp only [readyCells] at h2
          simp [h2]
        · simp only [readyCells] at h2
          simp only [h2, thenRun_ok, NeedBinder.cardinalityGate]
          cases hacc : needAcceptsCardinality ps cells.length
          · cases family <;> simp
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rw [traced_sources k ps (needLevelSources ps cells) repeated bound family s2]
            simp

  /-- THE TRACE THEOREM, one level's patterns over their sources (see `traced_one`). -/
  theorem traced_sources (k : NeedCapabilities EvalM) (ps : List NeedPattern)
      (sources : List (NeedSource Nat)) (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
      TracesAs (NeedBinder.bindSources (traced k) ps sources repeated bound family)
        (NeedBinder.bindSources k ps sources repeated bound family)
        (sourcesEvents k ps sources repeated bound family) := by
    intro s tr
    cases ps with
    | nil => simp [NeedBinder.bindSources, sourcesEvents]
    | cons p rest =>
      simp only [NeedBinder.bindSources, sourcesEvents, runTrace_bind, runEval_bind]
      rw [traced_address k (sources.headD .missing) s tr]
      rcases h1 : runEval (NeedBinder.sourceAddress k.allocate (sources.headD .missing)) s
        with ⟨_ | address, s1⟩
      · simp
      · simp only [thenRun_ok]
        rw [traced_one k p address repeated bound family s1]
        rcases h2 : runEval (NeedBinder.bindOne k p address repeated bound family) s1
          with ⟨_ | (_ | next), s2⟩
        · simp
        · simp
        · simp only [thenRun_ok]
          rw [traced_sources k rest sources.tail repeated next family s2]
          simp
end

/-- THE TRACE THEOREM, one level: the cardinality gate, then the level's patterns. -/
theorem traced_level (k : NeedCapabilities EvalM) (ps : List NeedPattern) (cells : List Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    TracesAs (NeedBinder.bindLevel (traced k) ps cells repeated bound family)
      (NeedBinder.bindLevel k ps cells repeated bound family)
      (levelEvents k ps cells repeated bound family) := by
  intro s tr
  simp only [NeedBinder.bindLevel, NeedBinder.cardinalityGate, levelEvents]
  cases hacc : needAcceptsCardinality ps cells.length
  · cases family <;> simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact traced_sources k ps (needLevelSources ps cells) repeated bound family s tr

/-- THE TRACE THEOREM, a whole head — the binder every production binding site runs. -/
theorem traced_patterns (k : NeedCapabilities EvalM) (ps : List NeedPattern) (cells : List Nat)
    (family : Bool) :
    TracesAs (NeedBinder.bindPatterns (traced k) ps cells family)
      (NeedBinder.bindPatterns k ps cells family) (patternsEvents k ps cells family) :=
  traced_level k ps cells (needRepeatedNames ps) [] family

/-! ## Trace erasure

The semantic projection of a traced run. `eraseTrace x s tr` runs `x` from semantic state `s`
and event prefix `tr` and forgets the events. -/

/-- Run a traced computation and drop the recorded events. -/
def eraseTrace {α : Type} (x : TraceM α) (s : EvalState) (tr : List NeedEvent) :
    Except Error α × EvalState :=
  ((runTrace x ⟨s, tr⟩).1, (runTrace x ⟨s, tr⟩).2.semantic)

/-- TRACE ERASURE (general): for EVERY production capability record `k` — arbitrary VALUE,
    CALLABLE and allocation operations, lifted through the protected tracing — every head,
    cell list, mode, semantic state and event prefix, erasing the trace of the traced core
    gives EXACTLY the production core's run: the same outcome (success, non-match or the same
    error) and the same final semantic state, effects completed before an error included. -/
theorem trace_erasure (k : NeedCapabilities EvalM) (ps : List NeedPattern) (cells : List Nat)
    (family : Bool) (s : EvalState) (tr : List NeedEvent) :
    eraseTrace (NeedBinder.bindPatterns (traced k) ps cells family) s tr
      = runEval (NeedBinder.bindPatterns k ps cells family) s := by
  simp [eraseTrace, traced_patterns k ps cells family s tr]

/-- TRACE ERASURE AT THE PRODUCTION BINDER: for EVERY pair of production channels — in
    particular the evaluator's `bindingChannels` — the traced core over the
    production capabilities erases to exactly `bindNeedPatterns`, as a complete `EvalM` run. -/
theorem trace_erasure_production (c : NeedChannels) (ps : List NeedPattern) (cells : List Nat)
    (family : Bool) (s : EvalState) (tr : List NeedEvent) :
    eraseTrace (NeedBinder.bindPatterns (traced c.capabilities) ps cells family) s tr
      = (bindNeedPatterns c ps cells family).runState s :=
  trace_erasure c.capabilities ps cells family s tr

/-- THE TRACE ONLY GROWS, and what it gains does not depend on what it held: the final trace is
    the prefix followed by `patternsEvents`, a function of the semantic state alone — on success
    and on failure. -/
theorem trace_extends_its_prefix (k : NeedCapabilities EvalM) (ps : List NeedPattern) (cells : List Nat)
    (family : Bool) (s : EvalState) (tr : List NeedEvent) :
    (runTrace (NeedBinder.bindPatterns (traced k) ps cells family) ⟨s, tr⟩).2.events
      = tr ++ patternsEvents k ps cells family s := by
  simp [traced_patterns k ps cells family s tr]

/-! ## Sequential composition of a level: written order and truncation -/

/-- Whether a binding outcome lets the next pattern run. -/
def continues : Except Error (Option NeedEnv) → Bool
  | .ok (some _) => true
  | _ => false

/-- (2, 11) SEQUENTIAL COMPOSITION, production: binding `ps ++ qs` over one source list is binding
    `ps`, and then — only if `ps` bound — binding `qs` over the remaining sources, from the
    environment and state `ps` left. If `ps` raised an error or did not match, that outcome
    and state are final. -/
theorem sources_append (k : NeedCapabilities EvalM) (ps qs : List NeedPattern)
    (sources : List (NeedSource Nat)) (repeated : List Ident) (bound : NeedEnv) (family : Bool)
    (s : EvalState) :
    runEval (NeedBinder.bindSources k (ps ++ qs) sources repeated bound family) s
      = match runEval (NeedBinder.bindSources k ps sources repeated bound family) s with
        | (.ok (some next), s') =>
          runEval (NeedBinder.bindSources k qs (sources.drop ps.length) repeated next family) s'
        | other => other := by
  induction ps generalizing sources bound s with
  | nil => simp [NeedBinder.bindSources]
  | cons p rest ih =>
    simp only [List.cons_append, NeedBinder.bindSources, runEval_bind]
    rcases h1 : runEval (NeedBinder.sourceAddress k.allocate (sources.headD .missing)) s
      with ⟨_ | address, s1⟩
    · simp
    · simp only [thenRun_ok]
      rcases h2 : runEval (NeedBinder.bindOne k p address repeated bound family) s1
        with ⟨_ | (_ | next), s2⟩
      · simp
      · simp
      · simp only [thenRun_ok]
        rw [ih sources.tail next s2]
        simp

/-- (2, 11) SEQUENTIAL COMPOSITION, events: the events of `ps ++ qs` are the events of `ps`, followed —
    only if `ps` bound — by the events of `qs` from where `ps` left off. Written order at
    every position, with nothing after a failure or a non-match. -/
theorem sources_events_append (k : NeedCapabilities EvalM) (ps qs : List NeedPattern)
    (sources : List (NeedSource Nat)) (repeated : List Ident) (bound : NeedEnv) (family : Bool)
    (s : EvalState) :
    sourcesEvents k (ps ++ qs) sources repeated bound family s
      = sourcesEvents k ps sources repeated bound family s ++
          match runEval (NeedBinder.bindSources k ps sources repeated bound family) s with
          | (.ok (some next), s') => sourcesEvents k qs (sources.drop ps.length) repeated next family s'
          | _ => [] := by
  induction ps generalizing sources bound s with
  | nil => simp [NeedBinder.bindSources, sourcesEvents]
  | cons p rest ih =>
    simp only [List.cons_append, sourcesEvents, NeedBinder.bindSources, runEval_bind]
    rcases h1 : runEval (NeedBinder.sourceAddress k.allocate (sources.headD .missing)) s
      with ⟨_ | address, s1⟩
    · simp
    · simp only [thenRun_ok]
      rcases h2 : runEval (NeedBinder.bindOne k p address repeated bound family) s1
        with ⟨_ | (_ | next), s2⟩
      · simp
      · simp
      · simp only [thenRun_ok]
        rw [ih sources.tail next s2]
        simp

/-- (12) TRUNCATION AT THE FIRST STOP (any position): if the patterns `ps` raise an error or fail to
    match, appending further patterns `qs` changes NOTHING observable — not the outcome, not the
    final semantic state, not one event: no later sibling begins, and nothing is rolled back. -/
theorem traced_sources_truncate (k : NeedCapabilities EvalM) (ps qs : List NeedPattern)
    (sources : List (NeedSource Nat)) (repeated : List Ident) (bound : NeedEnv) (family : Bool)
    (s : EvalState) (tr : List NeedEvent)
    (hstop : continues (runEval (NeedBinder.bindSources k ps sources repeated bound family) s).1 = false) :
    runTrace (NeedBinder.bindSources (traced k) (ps ++ qs) sources repeated bound family) ⟨s, tr⟩
      = runTrace (NeedBinder.bindSources (traced k) ps sources repeated bound family) ⟨s, tr⟩ := by
  rw [traced_sources k (ps ++ qs) sources repeated bound family s tr,
    traced_sources k ps sources repeated bound family s tr,
    sources_append k ps qs sources repeated bound family s,
    sources_events_append k ps qs sources repeated bound family s]
  rcases h : runEval (NeedBinder.bindSources k ps sources repeated bound family) s with ⟨r, s'⟩
  rw [h] at hstop
  rcases r with _ | (_ | next) <;> simp_all [continues]

/-! ## The ordering laws

Each law below is a direct consequence of the trace theorem, stated over the traced binder
itself (or over the production run it erases to), for every capability record `k`. -/

/-- (1) CARDINALITY BEFORE INSPECTION: an unaccepted top-level count ends the binder before any
    event and leaves the semantic state unchanged — the family non-match, otherwise the arity
    error with the head's minimum and the COMPLETE supply count. -/
theorem traced_rejected_count_is_silent (k : NeedCapabilities EvalM) (ps : List NeedPattern)
    (cells : List Nat) (family : Bool) (s : EvalState) (tr : List NeedEvent)
    (h : needAcceptsCardinality ps cells.length = false) :
    runTrace (NeedBinder.bindPatterns (traced k) ps cells family) ⟨s, tr⟩
      = (if family then .ok none
          else .error (Error.arityMismatch (needMinimumSuppliedSlots ps) cells.length), ⟨s, tr⟩) := by
  rw [traced_patterns k ps cells family s tr]
  cases family <;>
    simp [NeedBinder.bindPatterns, NeedBinder.bindLevel, NeedBinder.cardinalityGate, patternsEvents,
      levelEvents, h]

/-- (4) A PLAIN, NON-REPEATED OCCURRENCE IS SILENT: once its address is resolved, binding it
    emits no event, changes no semantic state, and only transports the address into the
    environment. (A collecting occurrence's address is a collector cell the SOURCE resolution
    allocated first — `production_collector_occurrence_in_a_mixed_head`.) -/
theorem traced_plain_occurrence_is_silent (k : NeedCapabilities EvalM) (name : Ident) (collecting : Bool)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState)
    (tr : List NeedEvent) (h : repeated.contains name = false) :
    runTrace (NeedBinder.bindOne (traced k) (.bind name collecting) address repeated bound family) ⟨s, tr⟩
      = (.ok (some (bound.filter (fun entry => entry.fst != name) ++ [(name, address)])), ⟨s, tr⟩) := by
  simp only [NeedBinder.bindOne, BinderCore.core_plain_name_is_pure _ _ _ _ _ _ h, runTrace_pure]

/-- MIXED-HEAD PLAIN STEP (NEED-04, per occurrence): in ANY head — around inspecting, repeated, structural
    or collecting patterns — a plain non-repeated occurrence bound from a supplied cell is
    exactly its environment update: the traced traversal with it equals the traced traversal
    of the rest from the updated environment, so it contributes no event and no state change
    of its own. Later patterns may still demand the same address. -/
theorem traced_plain_occurrence_in_a_mixed_head (k : NeedCapabilities EvalM) (name : Ident)
    (collecting : Bool) (address : Nat) (rest : List NeedPattern) (sources : List (NeedSource Nat))
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (h : repeated.contains name = false) :
    NeedBinder.bindSources (traced k) (.bind name collecting :: rest) (.cell address :: sources) repeated
        bound family
      = NeedBinder.bindSources (traced k) rest sources repeated
          (bound.filter (fun entry => entry.fst != name) ++ [(name, address)]) family :=
  BinderCore.core_plain_step (traced k) name collecting address rest sources repeated bound family h

/-- The same, at any position of a level: a plain non-repeated occurrence's OWN schedule is
    empty, so by `sources_events_append` the events around it are exactly its neighbours'. -/
theorem plain_occurrence_schedule_is_empty (k : NeedCapabilities EvalM) (name : Ident) (collecting : Bool)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState)
    (h : repeated.contains name = false) :
    oneEvents k (.bind name collecting) address repeated bound family s = [] := by
  simp only [oneEvents, nameEvents, h, Bool.false_eq_true, ↓reduceIte]

/-- ALIASING IS NOT INDEPENDENCE: a plain occurrence never demands its cell, but a LATER pattern
    bound from the same address does — `F(x, 7)`-style heads over one aliased cell emit exactly
    the literal's demand of that address. -/
theorem plain_then_literal_on_one_cell (k : NeedCapabilities EvalM) (name : Ident) (literal : Pattern)
    (address : Nat) (family : Bool) (s : EvalState) (tr : List NeedEvent) :
    (runTrace (NeedBinder.bindPatterns (traced k) [.bind name false, .literal literal] [address, address]
        family) ⟨s, tr⟩).2.events = tr ++ [.value address] := by
  rw [trace_extends_its_prefix]
  have hsrc : needLevelSources [NeedPattern.bind name false, .literal literal] [address, address]
      = [.cell address, .cell address] := rfl
  have hrep : needRepeatedNames [NeedPattern.bind name false, .literal literal] = [] := by
    simp [needRepeatedNames, NeedPattern.names]
  have hacc : needAcceptsCardinality [NeedPattern.bind name false, .literal literal] 2 = true := rfl
  simp only [patternsEvents, levelEvents, hrep, List.length_cons, List.length_nil, hacc, ↓reduceIte,
    hsrc, sourcesEvents, addressEvents, List.headD_cons, NeedBinder.sourceAddress, runEval_pure,
    oneEvents, nameEvents, List.contains_nil, Bool.false_eq_true, List.nil_append, List.tail_cons,
    NeedBinder.bindOne, BinderCore.core_plain_name_is_pure (k := k) name address [] [] family rfl]
  split <;> simp

/-- (5) A LITERAL demands its cell's VALUE — exactly one event — and only then decides by the
    matcher; a demand failure is final. -/
theorem traced_literal (k : NeedCapabilities EvalM) (literal : Pattern) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState) (tr : List NeedEvent) :
    runTrace (NeedBinder.bindOne (traced k) (.literal literal) address repeated bound family) ⟨s, tr⟩
      = match runEval (k.value address) s with
        | (.error e, t) => (.error e, ⟨t, tr ++ [.value address]⟩)
        | (.ok (value, _), t) =>
          (.ok (if (matchPattern literal value).isSome then some bound else none),
            ⟨t, tr ++ [.value address]⟩) := by
  rw [traced_one k _ address repeated bound family s tr]
  simp only [NeedBinder.bindOne, oneEvents, runEval_bind]
  rcases runEval (k.value address) s with ⟨_ | ⟨value, count⟩, t⟩ <;> simp

/-- A literal mismatch is a NON-MATCH (`none`) in BOTH binder modes. The ordinary user-call
    driver (`evalNeedUserSupply`, `partial`) turns an unexpected `none` into `badArity`, and
    ordinary signatures contain no literals; so there is NO law "family `none` iff ordinary
    error" at the binder layer. What does hold, for every head, is that a clause attempt and the
    ordinary binding differ only where the ordinary binding raises an incompatibility error, and
    that a literal-free head's ordinary binding is never a non-match
    (`family_attempt_is_the_ordinary_binding`, `ordinary_binding_is_never_a_non_match`,
    `KatLangArityLaws/BinderCorrespondence.lean`). -/
theorem literal_mismatch_is_none_in_both_modes (k : NeedCapabilities EvalM) (literal : Pattern)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s t : EvalState)
    (value : Result) (count : Nat) (hv : runEval (k.value address) s = (.ok (value, count), t))
    (hm : (matchPattern literal value).isSome = false) :
    runEval (NeedBinder.bindOne k (.literal literal) address repeated bound family) s = (.ok none, t) := by
  simp [NeedBinder.bindOne, hv, hm]

/-- Whether an occurrence INSPECTS its cell: every literal and structural pattern, and every
    occurrence of a repeated name. A META capture (CallReference S1) reifies its cell without
    demanding it, so it is not an inspection. -/
def inspectsAt (repeated : List Ident) : NeedPattern → Bool
  | .bind name _ => repeated.contains name
  | .metaRef _ => false
  | _ => true

/-- (5, 6) A FAILED DEMAND OF AN INSPECTING OCCURRENCE'S OWN CELL IS FINAL: the binder raises
    exactly that error, in exactly the state the demand left, and the trace ends with that one
    VALUE event — nothing was projected, allocated or bound. (That the demand comes FIRST in every
    outcome is `inspecting_occurrence_demands_its_cell_first`.) -/
theorem traced_inspection_failure (k : NeedCapabilities EvalM) (p : NeedPattern) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s t : EvalState) (tr : List NeedEvent)
    (e : Error) (hi : inspectsAt repeated p = true) (h : runEval (k.value address) s = (.error e, t)) :
    runTrace (NeedBinder.bindOne (traced k) p address repeated bound family) ⟨s, tr⟩
      = (.error e, ⟨t, tr ++ [.value address]⟩) := by
  rw [traced_one k p address repeated bound family s tr]
  cases p with
  | bind name collecting =>
    simp only [inspectsAt] at hi
    simp only [NeedBinder.bindOne, NeedBinder.bindName, oneEvents, nameEvents, hi, ↓reduceIte]
    simp [repeatedNameEvents, h]
  | literal literal => simp [NeedBinder.bindOne, oneEvents, h]
  | sequence ps => simp [NeedBinder.bindOne, oneEvents, h]
  | list ps => simp [NeedBinder.bindOne, oneEvents, h]
  | unpack ps => simp [NeedBinder.bindOne, oneEvents, h]
  | metaRef name => simp [inspectsAt] at hi

/-- The production face of `traced_inspection_failure`: the occurrence's schedule is exactly its one
    VALUE event and the production run is that error in that state. -/
theorem inspection_failure_schedule (k : NeedCapabilities EvalM) (p : NeedPattern) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s t : EvalState) (e : Error)
    (hi : inspectsAt repeated p = true) (h : runEval (k.value address) s = (.error e, t)) :
    oneEvents k p address repeated bound family s = [.value address]
    ∧ runEval (NeedBinder.bindOne k p address repeated bound family) s = (.error e, t) := by
  have h1 := traced_one k p address repeated bound family s []
  rw [traced_inspection_failure k p address repeated bound family s t [] e hi h] at h1
  simp only [List.nil_append, Prod.mk.injEq, TraceState.mk.injEq] at h1
  obtain ⟨hout, hstate, hevents⟩ := h1
  refine ⟨hevents.symm, ?_⟩
  rcases hrun : runEval (NeedBinder.bindOne k p address repeated bound family) s with ⟨r, t'⟩
  rw [hrun] at hout hstate
  simp only at hout hstate
  rw [← hout, ← hstate]

/-- (12) FIRST FAILURE AT AN ARBITRARY INSPECTED POSITION: when the patterns `before` bound (to `bound'`,
    leaving `s1`) and the next pattern — bound from a supplied cell `address` — inspects it and its
    VALUE demand fails, the whole traversal of the level's patterns (after its gate) raises
    exactly that error, in exactly the state the
    demand left, and its trace is the prefix's events followed by that one VALUE event: no later
    sibling (`after`) and no later event, nothing rolled back. -/
theorem traced_failure_at_any_position (k : NeedCapabilities EvalM) (before after : List NeedPattern)
    (p : NeedPattern) (sources : List (NeedSource Nat)) (repeated : List Ident) (bound bound' : NeedEnv)
    (family : Bool) (s s1 t : EvalState) (tr : List NeedEvent) (address : Nat) (e : Error)
    (hbefore : runEval (NeedBinder.bindSources k before sources repeated bound family) s
      = (.ok (some bound'), s1))
    (hsource : (sources.drop before.length).headD .missing = .cell address)
    (hi : inspectsAt repeated p = true) (hfail : runEval (k.value address) s1 = (.error e, t)) :
    runTrace (NeedBinder.bindSources (traced k) (before ++ p :: after) sources repeated bound family) ⟨s, tr⟩
      = (.error e, ⟨t, tr ++ (sourcesEvents k before sources repeated bound family s ++ [.value address])⟩) := by
  obtain ⟨hevents, hrun⟩ := inspection_failure_schedule k p address repeated bound' family s1 t e hi hfail
  rw [traced_sources k _ sources repeated bound family s tr,
    sources_append k before (p :: after) sources repeated bound family s,
    sources_events_append k before (p :: after) sources repeated bound family s, hbefore]
  simp only [NeedBinder.bindSources, sourcesEvents, hsource, NeedBinder.sourceAddress, addressEvents]
  simp [hevents, hrun]

/-- (6, 7) A STRUCTURAL PATTERN OF THE WRONG KIND: after its one VALUE event, the family
    non-match, otherwise the kind error — no allocation, no nested event. -/
theorem traced_wrong_kind (k : NeedCapabilities EvalM) (ps : List NeedPattern) (asList : Bool)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s t : EvalState)
    (tr : List NeedEvent) (value : Result) (count : Nat)
    (hv : runEval (k.value address) s = (.ok (value, count), t))
    (hk : (if asList then Result.listPatternItems? value else Result.sequencePatternItems? value) = none) :
    runTrace (NeedBinder.bindOne (traced k) (if asList then .list ps else .sequence ps) address
        repeated bound family) ⟨s, tr⟩
      = (if family then .ok none
          else .error (structuralPatternKindMismatch
            (if asList then NeedPattern.list ps else NeedPattern.sequence ps).toParameter value),
        ⟨t, tr ++ [.value address]⟩) := by
  rw [traced_one k _ address repeated bound family s tr]
  cases asList <;> simp only [Bool.false_eq_true, ↓reduceIte] at hk ⊢ <;>
    cases family <;> simp [NeedBinder.bindOne, oneEvents, hv, hk]

/-- The items a structural pattern opens from its demanded value: the binder's own kind view
    (a sequence pattern opens sequence values only, a list pattern list values only, the
    unpacking receiver opens one level of any value). -/
def structuralItems : NeedPattern → Result → Option (List Result)
  | .list _, value => Result.listPatternItems? value
  | .sequence _, value => Result.sequencePatternItems? value
  | _, value => some (Result.spreadItems value)

/-- (6) EVERY INSPECTING OCCURRENCE'S EVENTS BEGIN WITH THE VALUE DEMAND OF ITS OWN CELL. -/
theorem inspecting_occurrence_demands_its_cell_first (k : NeedCapabilities EvalM) (p : NeedPattern)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState)
    (hi : inspectsAt repeated p = true) :
    ∃ rest, oneEvents k p address repeated bound family s = .value address :: rest := by
  cases p with
  | bind name collecting =>
    simp only [inspectsAt] at hi
    simp only [oneEvents, nameEvents, hi, ↓reduceIte, repeatedNameEvents]
    exact ⟨_, rfl⟩
  | literal literal => exact ⟨[], rfl⟩
  | sequence ps => exact ⟨_, rfl⟩
  | list ps => exact ⟨_, rfl⟩
  | unpack ps => exact ⟨_, rfl⟩
  | metaRef name => simp [inspectsAt] at hi

/-- (8, 9) THE NESTED GATE FOLLOWS THE READY ALLOCATIONS, for every structural kind: when the
    opened items are allocated (one ready cell each, in item order) but the nested level rejects
    their count, the parent's VALUE event and every ready allocation have happened — and stay —
    and nothing else: no nested pattern is inspected. -/
theorem traced_nested_count_rejected_after_ready_allocation (k : NeedCapabilities EvalM)
    (p : NeedPattern) (ps : List NeedPattern) (hp : p = .sequence ps ∨ p = .list ps ∨ p = .unpack ps)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool)
    (s t t' : EvalState) (tr : List NeedEvent) (value : Result) (count : Nat) (items : List Result)
    (cells : List Nat) (hv : runEval (k.value address) s = (.ok (value, count), t))
    (hk : structuralItems p value = some items)
    (ha : runEval (readyCells k items) t = (.ok cells, t'))
    (hrej : needAcceptsCardinality ps cells.length = false) :
    runTrace (NeedBinder.bindOne (traced k) p address repeated bound family) ⟨s, tr⟩
      = (if family then .ok none
          else .error (Error.arityMismatch (needMinimumSuppliedSlots ps) cells.length),
        ⟨t', tr ++ .value address :: readyEvents k items t⟩) := by
  rw [traced_one k _ address repeated bound family s tr]
  simp only [readyCells] at ha
  rcases hp with rfl | rfl | rfl <;> simp only [structuralItems, Option.some.injEq] at hk
  all_goals first
    | (cases family <;>
        simp [NeedBinder.bindOne, oneEvents, readyCells, hv, hk, ha, NeedBinder.cardinalityGate, hrej])
    | (subst hk; cases family <;>
        simp [NeedBinder.bindOne, oneEvents, readyCells, hv, ha, NeedBinder.cardinalityGate, hrej])

/-! ### Repeated names: the order, the representative, the verdict -/

/-- The first occurrence of a repeated name demands only its own cell. -/
theorem repeated_first_occurrence_demands_only_its_cell (k : NeedCapabilities EvalM) (address : Nat)
    (s : EvalState) :
    repeatedNameEvents k address none s = [.value address] := by
  simp only [repeatedNameEvents]
  rcases runEval (k.value address) s with ⟨_ | value, s1⟩ <;> rfl

/-- A later occurrence's events are always a PREFIX of the one canonical order
    VALUE(current), VALUE(representative), CALLABLE(representative), CALLABLE(current):
    never reordered, never repeated, cut short only by an earlier outcome. -/
theorem repeated_events_are_a_prefix_of_the_canonical_order (k : NeedCapabilities EvalM)
    (address previous : Nat) (s : EvalState) :
    repeatedNameEvents k address (some previous) s <+:
      [.value address, .value previous, .callable previous, .callable address] := by
  unfold repeatedNameEvents
  rcases runEval (k.value address) s with ⟨_ | value, s1⟩
  · exact ⟨[.value previous, .callable previous, .callable address], rfl⟩
  · dsimp only
    rcases runEval (k.value previous) s1 with ⟨_ | before, s2⟩
    · exact ⟨[.callable previous, .callable address], rfl⟩
    · dsimp only
      by_cases hbv : (!(before == value)) = true
      · rw [if_pos hbv]
        exact ⟨[.callable previous, .callable address], rfl⟩
      · rw [if_neg hbv]
        rcases runEval (k.callable previous) s2 with ⟨_ | first, s3⟩
        · exact ⟨[.callable address], rfl⟩
        · exact ⟨[], rfl⟩

/-- NO CALLABLE PROJECTION BEFORE EQUAL VALUES (NEED-04): a repeated occurrence projects any
    CALLABLE only after BOTH VALUE demands succeeded and the two counted values are equal. -/
theorem repeated_callable_only_after_equal_values (k : NeedCapabilities EvalM) (address previous : Nat)
    (s : EvalState) (x : Nat) (h : NeedEvent.callable x ∈ repeatedNameEvents k address (some previous) s) :
    ∃ value s1 before s2, runEval (k.value address) s = (.ok value, s1)
      ∧ runEval (k.value previous) s1 = (.ok before, s2) ∧ (before == value) = true := by
  unfold repeatedNameEvents at h
  rcases h1 : runEval (k.value address) s with ⟨_ | value, s1⟩ <;> rw [h1] at h <;> dsimp only at h
  · simp at h
  · rcases h2 : runEval (k.value previous) s1 with ⟨_ | before, s2⟩ <;> rw [h2] at h <;> dsimp only at h
    · simp at h
    · by_cases hbv : (!(before == value)) = true
      · rw [if_pos hbv] at h
        simp at h
      · exact ⟨value, s1, before, s2, rfl, h2, by simpa using hbv⟩

/-- THE VERDICT of a repeated occurrence once both projections succeeded: incompatible callable
    identities are the family non-match or the type error; otherwise the binding KEEPS its
    retained representative unless the current contribution is strictly richer (the retained
    one has no callable identity and the current one has), in which case the current address
    replaces it (NEED-04, Q-28). -/
def repeatedVerdict (name : Ident) (address : Nat) (bound : NeedEnv) (family : Bool)
    (first second : Option Algorithm) : Except Error (Option NeedEnv) :=
  let keep : Except Error (Option NeedEnv) :=
    if (first.isSome || second.isNone) = true then .ok (some bound)
    else .ok (some (bound.filter (fun entry => entry.fst != name) ++ [(name, address)]))
  match first, second with
  | some a, some b =>
    if (!sameRepeatedCallableIdentity a b) = true then
      (if family then .ok none
        else .error (Error.typeMismatch "Repeated bind equality requires the same callable identity"))
    else keep
  | _, _ => keep

/-- THE REPEATED-NAME BINDING LAW (NEED-04, Q-28), production: an occurrence of a repeated name
    demands its own VALUE; the first occurrence then binds; a later one demands the retained
    representative's VALUE, compares the COMPLETE counted values (unequal: the family non-match
    or `badArity` under the repeated-parameter context, with no projection), then projects the
    representative's CALLABLE and its own, and decides by `repeatedVerdict`. Every failure is
    final, in the state it left. `sameRepeatedCallableIdentity` stays symbolic (it calls
    `partial` definitions). -/
theorem repeated_name_binding (k : NeedCapabilities EvalM) (name : Ident) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState)
    (hr : repeated.contains name = true) :
    runEval (NeedBinder.bindName k name address repeated bound family) s
      = match runEval (k.value address) s with
        | (.error e, t) => (.error e, t)
        | (.ok value, s1) =>
          match lookupAssoc name bound with
          | none => (.ok (some (bound.filter (fun entry => entry.fst != name) ++ [(name, address)])), s1)
          | some previous =>
            match runEval (k.value previous) s1 with
            | (.error e, t) => (.error e, t)
            | (.ok before, s2) =>
              if (!(before == value)) = true then
                (if family then .ok none
                  else .error (Error.withContext (repeatedParameterContext name) Error.badArity), s2)
              else
                match runEval (k.callable previous) s2 with
                | (.error e, t) => (.error e, t)
                | (.ok first, s3) =>
                  match runEval (k.callable address) s3 with
                  | (.error e, t) => (.error e, t)
                  | (.ok second, s4) => (repeatedVerdict name address bound family first second, s4) := by
  simp only [NeedBinder.bindName, hr, ↓reduceIte]
  rcases h1 : runEval (k.value address) s with ⟨_ | value, s1⟩
  · simp [h1]
  · cases hl : lookupAssoc name bound with
    | none => simp [h1]
    | some previous =>
      rcases h2 : runEval (k.value previous) s1 with ⟨_ | before, s2⟩
      · simp [h1, h2]
      · cases hbv : (before == value)
        · cases family <;> simp [h1, h2, hbv]
        · rcases h3 : runEval (k.callable previous) s2 with ⟨_ | first, s3⟩
          · simp [h1, h2, hbv, h3]
          · rcases h4 : runEval (k.callable address) s3 with ⟨_ | second, s4⟩
            · simp [h1, h2, hbv, h3, h4]
            · cases first with
              | none => cases second <;> simp [h1, h2, hbv, h3, h4, repeatedVerdict]
              | some a =>
                cases second with
                | none => simp [h1, h2, hbv, h3, h4, repeatedVerdict]
                | some b =>
                  cases hid : sameRepeatedCallableIdentity a b
                  · cases family <;> simp [h1, h2, hbv, h3, h4, hid, repeatedVerdict]
                  · simp [h1, h2, hbv, h3, h4, hid, repeatedVerdict]

/-- THE FAILURE POINTS OF A LATER REPEATED OCCURRENCE: each capability failure is final with
    exactly the events up to and including the failing invocation, in exactly the state it
    left; an unequal value ends the occurrence after the two VALUE events — before any
    CALLABLE projection — as the family non-match or the repeated-parameter `badArity`. -/
theorem traced_repeated_failure_points (k : NeedCapabilities EvalM) (name : Ident) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s s1 : EvalState) (tr : List NeedEvent)
    (value : CountedResult) (previous : Nat) (hr : repeated.contains name = true)
    (h1 : runEval (k.value address) s = (.ok value, s1)) (hl : lookupAssoc name bound = some previous) :
    (∀ e t, runEval (k.value previous) s1 = (.error e, t) →
      runTrace (NeedBinder.bindName (traced k) name address repeated bound family) ⟨s, tr⟩
        = (.error e, ⟨t, tr ++ [.value address, .value previous]⟩))
    ∧ (∀ before s2, runEval (k.value previous) s1 = (.ok before, s2) → (before == value) = false →
      runTrace (NeedBinder.bindName (traced k) name address repeated bound family) ⟨s, tr⟩
        = (if family then .ok none
            else .error (Error.withContext (repeatedParameterContext name) Error.badArity),
          ⟨s2, tr ++ [.value address, .value previous]⟩))
    ∧ (∀ before s2 e t, runEval (k.value previous) s1 = (.ok before, s2) → (before == value) = true →
      runEval (k.callable previous) s2 = (.error e, t) →
      runTrace (NeedBinder.bindName (traced k) name address repeated bound family) ⟨s, tr⟩
        = (.error e, ⟨t, tr ++ [.value address, .value previous, .callable previous]⟩))
    ∧ (∀ before s2 first s3 e t, runEval (k.value previous) s1 = (.ok before, s2) →
      (before == value) = true → runEval (k.callable previous) s2 = (.ok first, s3) →
      runEval (k.callable address) s3 = (.error e, t) →
      runTrace (NeedBinder.bindName (traced k) name address repeated bound family) ⟨s, tr⟩
        = (.error e, ⟨t, tr ++ [.value address, .value previous, .callable previous, .callable address]⟩)) := by
  have base := traced_name k name address repeated bound family s tr
  have hn : nameEvents k name address repeated bound s = repeatedNameEvents k address (some previous) s := by
    simp only [nameEvents, hr, ↓reduceIte, hl]
  rw [hn, repeated_name_binding k name address repeated bound family s hr] at base
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e t h2
    rw [base]; simp [repeatedNameEvents, h1, hl, h2]
  · intro before s2 h2 hbv
    rw [base]; cases family <;> simp [repeatedNameEvents, h1, hl, h2, hbv]
  · intro before s2 e t h2 hbv h3
    rw [base]; simp [repeatedNameEvents, h1, hl, h2, hbv, h3]
  · intro before s2 first s3 e t h2 hbv h3 h4
    rw [base]; simp [repeatedNameEvents, h1, hl, h2, hbv, h3, h4]

/-- A MISSING SOURCE is the binder's own `badArity`, before any event and with no state change
    (unreachable on validated signatures: the cardinality gate excludes it). -/
theorem traced_missing_source (k : NeedCapabilities EvalM) (p : NeedPattern) (rest : List NeedPattern)
    (sources : List (NeedSource Nat)) (repeated : List Ident) (bound : NeedEnv) (family : Bool)
    (s : EvalState) (tr : List NeedEvent) (hm : sources.headD .missing = .missing) :
    runTrace (NeedBinder.bindSources (traced k) (p :: rest) sources repeated bound family) ⟨s, tr⟩
      = (.error Error.badArity, ⟨s, tr⟩) := by
  rw [traced_sources k _ sources repeated bound family s tr]
  simp only [NeedBinder.bindSources, sourcesEvents, hm, NeedBinder.sourceAddress, addressEvents,
    runEval_bind, runEval_throw, thenRun_error]
  simp

/-- (10) A NESTED LEVEL IS THE PARENT'S CONTINUATION, depth first, for every structural kind: once a
    structural pattern's VALUE, kind view and ready allocations succeeded and the nested gate
    accepts, the parent's whole run IS the nested patterns' run, started after the parent's
    prefix of events — so a nested failure is the parent's failure, unchanged, and nothing of the
    parent follows it. -/
theorem traced_nested_level_is_the_parents_run (k : NeedCapabilities EvalM) (p : NeedPattern)
    (ps : List NeedPattern) (hp : p = .sequence ps ∨ p = .list ps ∨ p = .unpack ps)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s t t' : EvalState)
    (tr : List NeedEvent) (value : Result) (count : Nat) (items : List Result) (cells : List Nat)
    (hv : runEval (k.value address) s = (.ok (value, count), t))
    (hk : structuralItems p value = some items)
    (ha : runEval (readyCells k items) t = (.ok cells, t'))
    (hacc : needAcceptsCardinality ps cells.length = true) :
    runTrace (NeedBinder.bindOne (traced k) p address repeated bound family) ⟨s, tr⟩
      = runTrace (NeedBinder.bindSources (traced k) ps (needLevelSources ps cells) repeated bound family)
          ⟨t', tr ++ .value address :: readyEvents k items t⟩ := by
  rw [traced_one k _ address repeated bound family s tr,
    traced_sources k ps _ repeated bound family t' _]
  simp only [readyCells] at ha
  rcases hp with rfl | rfl | rfl <;> simp only [structuralItems, Option.some.injEq] at hk
  all_goals first
    | simp [NeedBinder.bindOne, oneEvents, readyCells, hv, hk, ha, NeedBinder.cardinalityGate, hacc]
    | (subst hk; simp [NeedBinder.bindOne, oneEvents, readyCells, hv, ha, NeedBinder.cardinalityGate, hacc])

/-- A READY ALLOCATION FAILING PARTWAY is final (any allocator; `allocateNeed` never fails): after
    the parent's VALUE event, the trace holds the ready events of the items allocated BEFORE the
    failing one and nothing else — no event for the failed allocation, no nested gate, no nested
    pattern — and the state is the one the failing allocation left. -/
theorem traced_ready_allocation_failure (k : NeedCapabilities EvalM) (p : NeedPattern)
    (ps : List NeedPattern) (hp : p = .sequence ps ∨ p = .list ps ∨ p = .unpack ps)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s t t' : EvalState)
    (tr : List NeedEvent) (value : Result) (count : Nat) (items : List Result) (e : Error)
    (hv : runEval (k.value address) s = (.ok (value, count), t))
    (hk : structuralItems p value = some items)
    (ha : runEval (readyCells k items) t = (.error e, t')) :
    runTrace (NeedBinder.bindOne (traced k) p address repeated bound family) ⟨s, tr⟩
      = (.error e, ⟨t', tr ++ .value address :: readyEvents k items t⟩) := by
  rw [traced_one k _ address repeated bound family s tr]
  simp only [readyCells] at ha
  rcases hp with rfl | rfl | rfl <;> simp only [structuralItems, Option.some.injEq] at hk
  all_goals first
    | simp [NeedBinder.bindOne, oneEvents, readyCells, hv, hk, ha]
    | (subst hk; simp [NeedBinder.bindOne, oneEvents, readyCells, hv, ha])

/-- A FAILED COLLECTOR ALLOCATION is final with no event (allocation events follow success
    only), in the state the allocator left; the pattern is never bound. (The production
    allocator `allocateNeed` never fails; this covers every other allocator.) -/
theorem traced_collector_allocation_failure (k : NeedCapabilities EvalM) (p : NeedPattern)
    (rest : List NeedPattern) (slice : List Nat) (sources : List (NeedSource Nat))
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s t : EvalState) (tr : List NeedEvent)
    (e : Error) (h : runEval (k.allocate (.collector slice)) s = (.error e, t)) :
    runTrace (NeedBinder.bindSources (traced k) (p :: rest) (.collector slice :: sources) repeated
        bound family) ⟨s, tr⟩
      = (.error e, ⟨t, tr⟩) := by
  rw [traced_sources k _ _ repeated bound family s tr]
  simp [NeedBinder.bindSources, sourcesEvents, addressEvents, NeedBinder.sourceAddress, h]

/-- A COMPLETE LATER REPEATED OCCURRENCE: when all four invocations succeed and the values are
    equal, the events are exactly VALUE(current), VALUE(representative), CALLABLE(representative),
    CALLABLE(current), and the outcome is `repeatedVerdict` — the identity incompatibility
    (type error, or the family non-match), the retained representative, or its replacement by a
    strictly richer current contribution — in the state the last projection left. -/
theorem traced_repeated_occurrence_complete (k : NeedCapabilities EvalM) (name : Ident) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s s1 s2 s3 s4 : EvalState)
    (tr : List NeedEvent) (value before : CountedResult) (previous : Nat) (first second : Option Algorithm)
    (hr : repeated.contains name = true) (h1 : runEval (k.value address) s = (.ok value, s1))
    (hl : lookupAssoc name bound = some previous) (h2 : runEval (k.value previous) s1 = (.ok before, s2))
    (hbv : (before == value) = true) (h3 : runEval (k.callable previous) s2 = (.ok first, s3))
    (h4 : runEval (k.callable address) s3 = (.ok second, s4)) :
    runTrace (NeedBinder.bindName (traced k) name address repeated bound family) ⟨s, tr⟩
      = (repeatedVerdict name address bound family first second,
          ⟨s4, tr ++ [.value address, .value previous, .callable previous, .callable address]⟩) := by
  rw [traced_name k name address repeated bound family s tr,
    repeated_name_binding k name address repeated bound family s hr]
  simp only [nameEvents, hr, ↓reduceIte]
  simp [hl, repeatedNameEvents, h1, h2, hbv, h3, h4]

/-! ### No CALLABLE event without a repeated name -/

/-- Whether an event is a CALLABLE projection. -/
def NeedEvent.isCallable : NeedEvent → Bool
  | .callable _ => true
  | _ => false

theorem readyEvents_no_callable (k : NeedCapabilities EvalM) (items : List Result) (s : EvalState) :
    ∀ ev ∈ readyEvents k items s, ev.isCallable = false := by
  induction items generalizing s with
  | nil => simp [readyEvents]
  | cons item rest ih =>
    simp only [readyEvents]
    rcases runEval (k.allocate (.ready (item, Result.valueCount item))) s with ⟨_ | address, s'⟩
    · simp
    · intro ev hev
      simp only [List.mem_cons] at hev
      rcases hev with rfl | hev
      · rfl
      · exact ih s' ev hev

theorem addressEvents_no_callable (k : NeedCapabilities EvalM) (source : NeedSource Nat) (s : EvalState) :
    ∀ ev ∈ addressEvents k source s, ev.isCallable = false := by
  cases source with
  | collector slice =>
    simp only [addressEvents]
    rcases runEval (k.allocate (.collector slice)) s with ⟨_ | address, s'⟩ <;> simp [NeedEvent.isCallable]
  | _ => simp [addressEvents]

mutual
  theorem oneEvents_no_callable_without_repeats (k : NeedCapabilities EvalM) (p : NeedPattern)
      (address : Nat) (bound : NeedEnv) (family : Bool) (s : EvalState) :
      ∀ ev ∈ oneEvents k p address [] bound family s, ev.isCallable = false := by
    cases p with
    | bind name collecting => simp [oneEvents, nameEvents]
    | literal literal => simp [oneEvents, NeedEvent.isCallable]
    | metaRef name =>
      intro ev hev
      simp only [oneEvents] at hev
      split at hev <;> simp_all [nameEvents, NeedEvent.isCallable]
    | sequence ps =>
      intro ev hev
      simp only [oneEvents, List.mem_cons] at hev
      rcases hev with rfl | hev
      · rfl
      · split at hev
        · simp at hev
        · split at hev
          · simp at hev
          · rw [List.mem_append] at hev
            rcases hev with hev | hev
            · exact readyEvents_no_callable k _ _ ev hev
            · split at hev
              · simp at hev
              · split at hev
                · exact sourcesEvents_no_callable_without_repeats k ps _ bound family _ ev hev
                · simp at hev
    | list ps =>
      intro ev hev
      simp only [oneEvents, List.mem_cons] at hev
      rcases hev with rfl | hev
      · rfl
      · split at hev
        · simp at hev
        · split at hev
          · simp at hev
          · rw [List.mem_append] at hev
            rcases hev with hev | hev
            · exact readyEvents_no_callable k _ _ ev hev
            · split at hev
              · simp at hev
              · split at hev
                · exact sourcesEvents_no_callable_without_repeats k ps _ bound family _ ev hev
                · simp at hev
    | unpack ps =>
      intro ev hev
      simp only [oneEvents, List.mem_cons] at hev
      rcases hev with rfl | hev
      · rfl
      · split at hev
        · simp at hev
        · rw [List.mem_append] at hev
          rcases hev with hev | hev
          · exact readyEvents_no_callable k _ _ ev hev
          · split at hev
            · simp at hev
            · split at hev
              · exact sourcesEvents_no_callable_without_repeats k ps _ bound family _ ev hev
              · simp at hev

  theorem sourcesEvents_no_callable_without_repeats (k : NeedCapabilities EvalM) (ps : List NeedPattern)
      (sources : List (NeedSource Nat)) (bound : NeedEnv) (family : Bool) (s : EvalState) :
      ∀ ev ∈ sourcesEvents k ps sources [] bound family s, ev.isCallable = false := by
    cases ps with
    | nil => simp [sourcesEvents]
    | cons p rest =>
      intro ev hev
      simp only [sourcesEvents, List.mem_append] at hev
      rcases hev with hev | hev
      · exact addressEvents_no_callable k _ s ev hev
      · split at hev
        · simp at hev
        · rw [List.mem_append] at hev
          rcases hev with hev | hev
          · exact oneEvents_no_callable_without_repeats k p _ bound family _ ev hev
          · split at hev
            · exact sourcesEvents_no_callable_without_repeats k rest _ _ family _ ev hev
            · simp at hev
end

/-- A HEAD THAT REPEATS NO NAME NEVER PROJECTS A CALLABLE (stated over the schedule; with
    `traced_patterns` it is the traced binder's events, `traced_head_without_repeated_names_projects_no_callable`).
    Within a repeated occurrence, a CALLABLE event follows two successful, equal VALUE demands
    (`repeated_callable_only_after_equal_values`). -/
theorem head_without_repeated_names_projects_no_callable (k : NeedCapabilities EvalM)
    (ps : List NeedPattern) (cells : List Nat) (family : Bool) (s : EvalState)
    (h : needRepeatedNames ps = []) :
    ∀ ev ∈ patternsEvents k ps cells family s, ev.isCallable = false := by
  intro ev hev
  simp only [patternsEvents, levelEvents, h] at hev
  split at hev
  · exact sourcesEvents_no_callable_without_repeats k ps _ [] family s ev hev
  · simp at hev

/-! ### The production allocator: fresh addresses, in order, and nothing rolled back -/

/-- `allocateNeed` returns the next free address and appends one cell holding the suspension. -/
theorem allocateNeed_run (suspension : NeedSuspension) (s : EvalState) :
    runEval (allocateNeed suspension) s
      = (.ok s.needs.size, { s with needs := s.needs.push { suspension := suspension } }) := rfl

/-- LOCAL FRESHNESS: the production allocator returns an address outside every supplied list
    whose addresses are valid in the incoming heap, and those supplied addresses remain valid.
    Aliased supplied addresses are allowed. This does not discharge whole-binder freshness:
    that additionally requires the channels not to shrink the heap between allocations. -/
theorem allocateNeed_fresh_for_valid_supply (suspension : NeedSuspension) (s : EvalState)
    (cells : List Nat) (hvalid : ∀ a ∈ cells, a < s.needs.size) :
    (runEval (allocateNeed suspension) s).1 = .ok s.needs.size
    ∧ s.needs.size ∉ cells
    ∧ ∀ a ∈ cells, a < (runEval (allocateNeed suspension) s).2.needs.size := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hmem
    have := hvalid _ hmem
    omega
  · intro a ha
    have := hvalid a ha
    simp only [allocateNeed_run, Array.size_push]
    omega

/-- The need heap after appending one ready cell per item, in item order. -/
def pushReady (needs : Array NeedCell) : List Result → Array NeedCell
  | [] => needs
  | item :: rest => pushReady (needs.push { suspension := .ready (item, Result.valueCount item) }) rest

theorem pushReady_size (needs : Array NeedCell) (items : List Result) :
    (pushReady needs items).size = needs.size + items.length := by
  induction items generalizing needs with
  | nil => simp [pushReady]
  | cons item rest ih => simp [pushReady, ih]; omega

theorem production_ready_loop (k : NeedCapabilities EvalM) (hk : k.allocate = allocateNeed)
    (items : List Result) (acc : List Nat) (s : EvalState) :
    runEval (List.mapM.loop (fun item => k.allocate (.ready (item, Result.valueCount item))) items acc) s
      = (.ok (acc.reverse ++ List.range' s.needs.size items.length),
          { s with needs := pushReady s.needs items }) := by
  induction items generalizing acc s with
  | nil => simp [List.mapM.loop, pushReady]
  | cons item rest ih =>
    simp only [List.mapM.loop, runEval_bind, hk, allocateNeed_run, thenRun_ok]
    rw [← hk, ih]
    simp [pushReady, List.range'_succ]

/-- (8) FRESH READY CELLS (production allocator): a structural pattern's opened items get the
    CONSECUTIVE fresh addresses `size, size + 1, …` of the heap it found, one cell each, holding
    the item and its value count, in item order. -/
theorem production_ready_cells (k : NeedCapabilities EvalM) (hk : k.allocate = allocateNeed)
    (items : List Result) (s : EvalState) :
    runEval (readyCells k items) s
      = (.ok (List.range' s.needs.size items.length), { s with needs := pushReady s.needs items }) := by
  have := production_ready_loop k hk items [] s
  simp only [List.reverse_nil, List.nil_append] at this
  exact this

/-- …and their allocation events are those addresses, in that order. -/
theorem production_ready_events (k : NeedCapabilities EvalM) (hk : k.allocate = allocateNeed)
    (items : List Result) (s : EvalState) :
    readyEvents k items s = (List.range' s.needs.size items.length).map NeedEvent.ready := by
  induction items generalizing s with
  | nil => simp [readyEvents]
  | cons item rest ih =>
    simp only [readyEvents, hk, allocateNeed_run]
    simp [ih, List.range'_succ]

/-- (9) RETAINED STATE AT A NESTED REJECTION (production allocator), every structural kind: when a
    structural pattern's items are opened but the nested level rejects their count, the ready cells allocated for them stay
    in the heap — nothing is rolled back — and the trace is the parent's VALUE followed by their
    consecutive fresh addresses. -/
theorem production_nested_rejection_keeps_its_ready_cells (k : NeedCapabilities EvalM)
    (hk : k.allocate = allocateNeed) (p : NeedPattern) (ps : List NeedPattern)
    (hp : p = .sequence ps ∨ p = .list ps ∨ p = .unpack ps) (address : Nat) (repeated : List Ident)
    (bound : NeedEnv) (family : Bool) (s t : EvalState) (tr : List NeedEvent) (value : Result)
    (count : Nat) (items : List Result) (hv : runEval (k.value address) s = (.ok (value, count), t))
    (hk' : structuralItems p value = some items)
    (hrej : needAcceptsCardinality ps items.length = false) :
    runTrace (NeedBinder.bindOne (traced k) p address repeated bound family) ⟨s, tr⟩
      = (if family then .ok none
          else .error (Error.arityMismatch (needMinimumSuppliedSlots ps) items.length),
        ⟨{ t with needs := pushReady t.needs items },
          tr ++ .value address :: (List.range' t.needs.size items.length).map NeedEvent.ready⟩) := by
  have ha := production_ready_cells k hk items t
  have hrej' : needAcceptsCardinality ps (List.range' t.needs.size items.length).length = false := by
    simpa using hrej
  rw [traced_nested_count_rejected_after_ready_allocation k p ps hp address repeated bound family s t _
    tr value count items _ hv hk' ha hrej', production_ready_events k hk items t]
  simp

/-- (3) A COLLECTOR SOURCE IS ALLOCATED BEFORE ITS PATTERN IS BOUND (production allocator): its one
    fresh collector cell gets the next free address and holds exactly its slice; its allocation
    event comes first, then the pattern's own events at that address, then the rest. -/
theorem production_collector_source_events (k : NeedCapabilities EvalM) (hk : k.allocate = allocateNeed)
    (p : NeedPattern) (rest : List NeedPattern) (slice : List Nat) (sources : List (NeedSource Nat))
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState) :
    sourcesEvents k (p :: rest) (.collector slice :: sources) repeated bound family s
      = .collector s.needs.size slice ::
          (oneEvents k p s.needs.size repeated bound family
              { s with needs := s.needs.push { suspension := .collector slice } } ++
            match runEval (NeedBinder.bindOne k p s.needs.size repeated bound family)
                { s with needs := s.needs.push { suspension := .collector slice } } with
            | (.ok (some next), s2) => sourcesEvents k rest sources repeated next family s2
            | _ => []) := by
  simp [sourcesEvents, addressEvents, NeedBinder.sourceAddress, hk, allocateNeed_run]

/-- The same law over the TRACED binder: from the empty prefix, a head that repeats no name
    records no CALLABLE event. -/
theorem traced_head_without_repeated_names_projects_no_callable (k : NeedCapabilities EvalM)
    (ps : List NeedPattern) (cells : List Nat) (family : Bool) (s : EvalState)
    (h : needRepeatedNames ps = []) :
    ∀ ev ∈ (runTrace (NeedBinder.bindPatterns (traced k) ps cells family) ⟨s, []⟩).2.events,
      ev.isCallable = false := by
  rw [traced_patterns k ps cells family s []]
  simpa using head_without_repeated_names_projects_no_callable k ps cells family s h

/-- (3, 4) MIXED-HEAD PLAIN STEP, collecting occurrence (production allocator): a non-repeated
    collecting occurrence ALLOCATES its one collector cell — the next heap position, holding
    exactly its slice — and demands and projects nothing; the rest of the head then runs from
    the extended heap and environment. -/
theorem production_collector_occurrence_in_a_mixed_head (k : NeedCapabilities EvalM)
    (hk : k.allocate = allocateNeed) (name : Ident) (rest : List NeedPattern) (slice : List Nat)
    (sources : List (NeedSource Nat)) (repeated : List Ident) (bound : NeedEnv) (family : Bool)
    (s : EvalState) (h : repeated.contains name = false) :
    sourcesEvents k (.bind name true :: rest) (.collector slice :: sources) repeated bound family s
      = .collector s.needs.size slice ::
          sourcesEvents k rest sources repeated
            (bound.filter (fun entry => entry.fst != name) ++ [(name, s.needs.size)]) family
            { s with needs := s.needs.push { suspension := .collector slice } }
    ∧ runEval (NeedBinder.bindSources k (.bind name true :: rest) (.collector slice :: sources) repeated
        bound family) s
      = runEval (NeedBinder.bindSources k rest sources repeated
          (bound.filter (fun entry => entry.fst != name) ++ [(name, s.needs.size)]) family)
          { s with needs := s.needs.push { suspension := .collector slice } } := by
  have hplain := BinderCore.core_plain_name_is_pure k name s.needs.size repeated bound family h
  constructor
  · rw [production_collector_source_events k hk]
    simp [plain_occurrence_schedule_is_empty k name true _ repeated bound family _ h, NeedBinder.bindOne,
      hplain]
  · simp [NeedBinder.bindSources, NeedBinder.sourceAddress, hk, allocateNeed_run, NeedBinder.bindOne, hplain]

/-- (3) A LONE COLLECTING HEAD, traced (production allocator): one collector allocation over exactly
    the supplied cells, no VALUE and no CALLABLE event, in either mode. -/
theorem traced_lone_collector (k : NeedCapabilities EvalM) (hk : k.allocate = allocateNeed)
    (name : Ident) (cells : List Nat) (family : Bool) (s : EvalState) (tr : List NeedEvent) :
    runTrace (NeedBinder.bindPatterns (traced k) [.bind name true] cells family) ⟨s, tr⟩
      = (.ok (some [(name, s.needs.size)]),
          ⟨{ s with needs := s.needs.push { suspension := .collector cells } },
            tr ++ [.collector s.needs.size cells]⟩) := by
  have hr : needRepeatedNames [NeedPattern.bind name true] = [] := by
    simp [needRepeatedNames, NeedPattern.names]
  have hacc : needAcceptsCardinality [NeedPattern.bind name true] cells.length = true := by
    simp [needAcceptsCardinality, needMinimumSuppliedSlots, NeedPattern.isCollecting, List.filter_cons]
  rw [traced_patterns k _ cells family s tr]
  simp [NeedBinder.bindPatterns, NeedBinder.bindLevel, NeedBinder.cardinalityGate, patternsEvents,
    levelEvents, hr, hacc, lone_collector_collects_every_supplied_cell, NeedBinder.bindSources,
    sourcesEvents, addressEvents, NeedBinder.sourceAddress, hk, allocateNeed_run, NeedBinder.bindOne,
    NeedBinder.bindName, oneEvents, nameEvents]

/-! ## The protection hypothesis is necessary

The trace theorem quantifies over production operations LIFTED by `traced`, which can neither
write nor read the trace. Each half of that protection is necessary: `forgingValue` WRITES the
trace (it clears it) and breaks the append-only / prefix law, and `traceReadingValue` READS it
(it answers differently once anything was recorded) and breaks erasure itself — so no erasure
or append-only theorem can be stated for arbitrary trace-aware capabilities without a framing
hypothesis such as `TracesAs` for each operation. -/

/-- A hostile, trace-aware VALUE operation: it erases the events recorded so far. -/
def forgingValue (k : NeedCapabilities EvalM) : NeedCapabilities TraceM :=
  { traced k with value := fun address t => ((runEval (k.value address) t.semantic).1,
      { semantic := (runEval (k.value address) t.semantic).2, events := [] }) }

/-- Over the forging operation a literal's binding ERASES the prefix it was given, while over the
    protected tracing the same binding keeps it and appends its one VALUE event. -/
theorem forging_value_loses_the_prefix (k : NeedCapabilities EvalM) (literal : Pattern) (address : Nat)
    (family : Bool) (s : EvalState) (event : NeedEvent) :
    (runTrace (NeedBinder.bindOne (forgingValue k) (.literal literal) address [] [] family) ⟨s, [event]⟩).2.events
      = []
    ∧ (runTrace (NeedBinder.bindOne (traced k) (.literal literal) address [] [] family) ⟨s, [event]⟩).2.events
      = [event, .value address] := by
  constructor
  · simp only [NeedBinder.bindOne, runTrace_bind, forgingValue]
    simp only [runTrace]
    rcases runEval (k.value address) s with ⟨_ | ⟨value, count⟩, t⟩ <;> rfl
  · rw [traced_literal k literal address [] [] family s [event]]
    rcases runEval (k.value address) s with ⟨_ | ⟨value, count⟩, t⟩ <;> rfl

/-- A hostile, trace-READING VALUE operation: while nothing has been recorded it is the protected
    tracing of `k`; once the trace is nonempty it answers `forged` instead. -/
def traceReadingValue (k : NeedCapabilities EvalM) (forged : CountedResult) : NeedCapabilities TraceM :=
  { traced k with value := fun address t =>
      if t.events.isEmpty then runTrace ((traced k).value address) t else (.ok forged, t) }

/-- A production-shaped record whose every cell holds `()`. -/
def emptyValues : NeedCapabilities EvalM :=
  ⟨fun _ => pure (.sequenceValue [], 0), fun _ => pure none, allocateNeed, NeedPlan.reference⟩

/-- Over the trace-reading operation ERASURE FAILS: from a nonempty prefix the unpacking
    receiver sees the forged one-item value, allocates a ready cell and is rejected by its
    nested gate, while the production run binds `()` and succeeds. -/
theorem trace_reading_value_breaks_erasure (s : EvalState) :
    eraseTrace (NeedBinder.bindOne (traceReadingValue emptyValues (.sequenceValue [.atom 1], 1))
        (.unpack []) 0 [] [] false) s [.ready 0]
      ≠ runEval (NeedBinder.bindOne emptyValues (.unpack []) 0 [] [] false) s := by
  have traced : (eraseTrace (NeedBinder.bindOne (traceReadingValue emptyValues (.sequenceValue [.atom 1], 1))
      (.unpack []) 0 [] [] false) s [.ready 0]).1 = .error (Error.arityMismatch 0 1) := rfl
  have production : (runEval (NeedBinder.bindOne emptyValues (.unpack []) 0 [] [] false) s).1
      = .ok (some []) := rfl
  intro h
  have h1 := congrArg Prod.fst h
  rw [traced, production] at h1
  cases h1

end KatLang.BinderTrace
