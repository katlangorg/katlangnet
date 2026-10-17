import KatLangArityLaws

open KatLang KatLang.NeedDemand

/-!
# Total supply and collector-demand control (R5, A2+B2)

PRODUCTION theorems below concern the actual total helpers in KatLang.lean.
Schedules and heap predicates are LOCAL observations, not alternative evaluators.
The public entry points specialize these helpers by definition. The recursive
driver and evalCounted remain partial: their wiring is source/guard evidence,
not universal kernel refinement of the old opaque evaluator. Publication needs
a present post-callback cell; size alone does not preserve suspension identity.
No theorem here concerns C# concurrency, cancellation or whole-run heap refinement.
-/

namespace KatLang.NeedControl.Allocation
theorem bind_run {α β : Type} (m : EvalM α) (f : α → EvalM β) (st : EvalState) :
    (m >>= f).runState st =
      (match m.runState st with
       | (.ok a, next) => (f a).runState next
       | (.error e, next) => (.error e, next)) := by
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind]
  rcases m.runState st with ⟨out, next⟩
  cases out <;> rfl
theorem allocate_run (s : NeedSuspension) (st : EvalState) :
    (allocateNeed s).runState st =
      (.ok st.needs.size, { st with needs := st.needs.push { suspension := s } }) := rfl
theorem allocate_prefix (s : NeedSuspension) (st : EvalState) (a : Nat)
    (ha : a < st.needs.size) :
    ((allocateNeed s).runState st).2.needs[a]? = st.needs[a]? := by
  simp only [allocate_run, Array.getElem?_push]
  split
  · omega
  · rfl
theorem supply_param_transports (name : Ident) (ctx : EvalCtx) (env : ValEnv)
    (st : EvalState) (activation : Option ParameterActivation) (a : Nat)
    (hc : (capturedParameterActivation? name ctx).runState st = (.ok activation, st))
    (ha : lookupAssoc name (activation.map ParameterActivation.needs |>.getD ctx.needEnv) = some a) :
    (supplyNeed (.param name) ctx env).runState st = (.ok a, st) := by
  simp only [supplyNeed, bind_run, hc, ha]
  rfl
theorem supply_literal_one (n : Int) (ctx : EvalCtx) (env : ValEnv) (st : EvalState) :
    (supplyNeed (.num n) ctx env).runState st =
      (.ok st.needs.size,
        {st with needs := st.needs.push {suspension := .expression (.num n) ctx env}}) := rfl





theorem supply_unbound_param (name : Ident) (ctx : EvalCtx) (env : ValEnv)
    (st : EvalState) (activation : Option ParameterActivation)
    (hc : (capturedParameterActivation? name ctx).runState st = (.ok activation, st))
    (ha : lookupAssoc name (activation.map ParameterActivation.needs |>.getD ctx.needEnv) = none) :
    (supplyNeed (.param name) ctx env).runState st =
      (.ok st.needs.size, { st with needs := st.needs.push { suspension := .expression (.param name) ctx env } }) := by
  simp only [supplyNeed, bind_run, hc, ha]
  rfl

theorem known_collector (name : Ident) (ctx : EvalCtx) (st : EvalState)
    (activation : Option ParameterActivation) (a : Nat) (cell : NeedCell) (slice : List Nat)
    (hc : (capturedParameterActivation? name ctx).runState st = (.ok activation, st))
    (ha : lookupAssoc name (activation.map ParameterActivation.needs |>.getD ctx.needEnv) = some a)
    (hcell : st.needs[a]? = some cell)
    (hslice : cell.suspension = .collector slice) :
    (spreadCollectorSlice? (.param name) ctx).runState st = (.ok (some slice), st) := by
  simp only [spreadCollectorSlice?, bind_run, hc, ha]
  rw [show (get : EvalM EvalState).runState st = (.ok st, st) from rfl]
  simp only [hcell, hslice]
  rfl

def ValidCollectorHeap (heap : Array NeedCell) : Prop :=
  ∀ (a : Nat) (cell : NeedCell), heap[a]? = some cell → ∀ slice,
    cell.suspension = .collector slice → ∀ b ∈ slice, b < a

theorem append_valid_collector (st : EvalState) (slice : List Nat)
    (hheap : ValidCollectorHeap st.needs)
    (hslice : ∀ b ∈ slice, b < st.needs.size) :
    ValidCollectorHeap ((allocateNeed (.collector slice)).runState st).2.needs := by
  intro a cell hcell sub hsub b hb
  simp only [allocate_run, Array.getElem?_push] at hcell
  split at hcell
  · rename_i ha
    cases hcell
    cases hsub
    simpa [ha] using hslice b hb
  · exact hheap a cell hcell sub hsub b hb





theorem supply_nonparameter (source : Expr) (ctx : EvalCtx) (env : ValEnv) (st : EvalState)
    (h : ∀ name, source ≠ .param name) :
    (supplyNeed source ctx env).runState st =
      (.ok st.needs.size, { st with needs := st.needs.push { suspension := .expression source ctx env } }) := by
  cases source <;> try rfl
  rename_i name
  exact (h name rfl).elim

def Nonshrinking {α : Type} (m : EvalM α) : Prop :=
  ∀ s, s.needs.size ≤ (m.runState s).2.needs.size

theorem nonshrinking_bind {α β : Type} (m : EvalM α) (f : α → EvalM β)
    (hm : Nonshrinking m) (hf : ∀ a, Nonshrinking (f a)) :
    Nonshrinking (m >>= f) := by
  intro s
  rw [bind_run]
  have h := hm s
  cases hr : m.runState s with
  | mk result next =>
    simp only [hr] at h
    cases result with
    | error e => exact h
    | ok a => exact Nat.le_trans h (hf a next)

theorem two_allocations_fresh {α : Type} (middle : EvalM α) (hm : Nonshrinking middle)
    (left right : NeedSuspension) (s : EvalState) (a b : Nat)
    (hresult : ((do
      let a ← allocateNeed left
      let _ ← middle
      let b ← allocateNeed right
      pure (a, b) : EvalM (Nat × Nat)).runState s).1 = .ok (a, b)) :
    a < b := by
  simp only [bind_run, allocate_run] at hresult
  let first := { s with needs := s.needs.push { suspension := left } }
  have hsize := hm first
  cases hr : middle.runState first with
  | mk result next =>
    rw [show first.needs.size = s.needs.size + 1 by simp [first]] at hsize
    rw [hr] at hsize
    rw [hr] at hresult
    cases result with
    | error e => cases hresult
    | ok value =>
      have hp := Except.ok.inj hresult
      change (s.needs.size, next.needs.size) = (a, b) at hp
      rcases Prod.mk.inj hp with ⟨ha, hb⟩
      change s.needs.size + 1 ≤ next.needs.size at hsize
      omega




end KatLang.NeedControl.Allocation


namespace KatLang.NeedControl.Collector
theorem branch_expression (demand : Nat → EvalM CountedResult) (slice : List Nat) :
    materialize demand slice = (do
      let values ← slice.mapM (fun a => Prod.fst <$> demand a)
      pure (makeCollectionListResult values)) := rfl

theorem bind_run {α β : Type} (m : EvalM α) (f : α → EvalM β) (st : EvalState) :
    (m >>= f).runState st =
      (match m.runState st with
       | (.ok a, next) => (f a).runState next
       | (.error e, next) => (.error e, next)) := by
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind]
  rcases m.runState st with ⟨out, next⟩
  cases out <;> rfl

theorem map_run {α β : Type} (f : α → β) (m : EvalM α) (st : EvalState) :
    (f <$> m).runState st =
      (match m.runState st with
       | (.ok a, next) => (.ok (f a), next)
       | (.error e, next) => (.error e, next)) := by
  simp only [Functor.map, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind]
  rcases m.runState st with ⟨out, next⟩
  cases out <;> rfl

theorem first_failure (demand : Nat → EvalM CountedResult)
    (a : Nat) (rest : List Nat) (s t : EvalState) (e : Error)
    (h : (demand a).runState s = (.error e, t)) :
    (materialize demand (a :: rest)).runState s = (.error e, t) := by
  simp only [materialize, List.mapM, List.mapM.loop, bind_run, map_run, h]

theorem ready_exact (values : Nat → CountedResult) (slice : List Nat) (s : EvalState) :
    (materialize (fun a => (pure (values a) : EvalM CountedResult)) slice).runState s =
      (.ok (.listValue (slice.map (fun a => (values a).1)), 1), s) := by
  suffices h : ∀ (acc : List Result),
      (List.mapM.loop (fun a => Prod.fst <$> (pure (values a) : EvalM CountedResult))
        slice acc).runState s = (.ok (acc.reverse ++ slice.map (fun a => (values a).1)), s) by
    simp only [materialize, List.mapM, bind_run, h [], List.reverse_nil, List.nil_append]
    rfl
  intro acc
  induction slice generalizing acc with
  | nil => simp only [List.mapM.loop, List.map_nil, List.append_nil]; rfl
  | cons a rest ih =>
    simp only [List.mapM.loop, bind_run, map_run]
    change (List.mapM.loop (fun a => Prod.fst <$> (pure (values a) : EvalM CountedResult)) rest ((values a).1 :: acc)).runState s = _
    rw [ih]
    simp only [List.reverse_cons, List.map_cons, List.append_assoc, List.singleton_append]

def stateful (a : Nat) : EvalM CountedResult := do
  let st ← get
  set { st with nextBindingContext := st.nextBindingContext * 10 + a }
  if a == 2 then throw Error.badArity
  pure (.atom a, 1)

theorem retained_failure (s : EvalState) :
    (materialize stateful [1, 2, 3]).runState s =
      (.error Error.badArity, { s with nextBindingContext := (s.nextBindingContext * 10 + 1) * 10 + 2 }) := rfl





end KatLang.NeedControl.Collector


namespace KatLang.NeedControl.Provenance
open KatLang.NeedControl.Collector NeedDemand
@[simp] theorem get_run (s : EvalState) :
    (get : EvalM EvalState).runState s = (.ok s, s) := rfl
@[simp] theorem pure_run {α : Type} (a : α) (s : EvalState) :
    (pure a : EvalM α).runState s = (.ok a, s) := rfl
def sourceAt (heap : Array NeedCell) (a : Nat) : Option Expr :=
  match heap[a]? with
  | some { suspension := .expression e _ _, .. } => some e
  | _ => none

theorem source_run (a : Nat) (s : EvalState) :
    (needWrittenSource? a).runState s = (.ok (sourceAt s.needs a), s) := by
  simp only [needWrittenSource?, bind_run, get_run, sourceAt]
  cases h : s.needs[a]? with
  | none => rfl
  | some cell =>
    cases cell with
    | mk suspension state callable plan => cases suspension <;> rfl

theorem reopen_run (slice : List Nat) (s : EvalState) :
    (slice.mapM (fun a => do pure (a, ← needWrittenSource? a)) : EvalM (List (Nat × Option Expr))).runState s = (.ok (slice.map (fun a => (a, sourceAt s.needs a))), s) := by
  suffices h : ∀ (acc : List (Nat × Option Expr)),
      (List.mapM.loop (fun a => do pure (a, ← needWrittenSource? a)) slice acc).runState s =
        (.ok (acc.reverse ++ slice.map (fun a => (a, sourceAt s.needs a))), s) by
    exact h []
  intro acc
  induction slice generalizing acc with
  | nil => simp only [List.mapM.loop, List.map_nil, List.append_nil]; rfl
  | cons a rest ih =>
    simp only [List.mapM.loop, bind_run, source_run, pure_run]
    rw [ih]
    simp only [List.reverse_cons, List.map_cons, List.append_assoc, List.singleton_append]

theorem reopened_addresses (heap : Array NeedCell) (slice : List Nat) :
    (slice.map (fun a => (a, sourceAt heap a))).map Prod.fst = slice := by
  simp [List.map_map, Function.comp_def]




end KatLang.NeedControl.Provenance


namespace KatLang.NeedControl.Memo
theorem completed_sticky (ev) (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (a : Nat) (s : EvalState) (cell : NeedCell) (outcome : Except Error CountedResult)
    (hc : s.needs[a]? = some cell) (hs : cell.state = .completed outcome) :
    (step ev route demand a).runState s = (outcome, s) := by
  simp only [step, KatLang.NeedControl.Collector.bind_run, KatLang.NeedControl.Provenance.get_run, hc, hs]
  cases outcome <;> rfl

theorem suspended_retains_state (ev) (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (a : Nat) (s t : EvalState) (cell : NeedCell) (outcome : Except Error CountedResult)
    (hc : s.needs[a]? = some cell) (hs : cell.state = .suspended)
    (hr : (suspendedValue ev route demand a cell.suspension).runState
      { s with needs := s.needs.modify a (fun c => { c with state := .evaluating }) } = (outcome, t)) :
    (step ev route demand a).runState s =
      (outcome, { t with needs := t.needs.modify a (fun c => { c with state := .completed outcome }) }) := by
  simp only [step, KatLang.NeedControl.Collector.bind_run, KatLang.NeedControl.Provenance.get_run, hc, hs]
  change (do
    let outcome ← evalAttempt (suspendedValue ev route demand a cell.suspension)
    modify fun s => { s with needs := s.needs.modify a (fun c => { c with state := .completed outcome }) }
    return ← outcome : EvalM CountedResult).runState
      { s with needs := s.needs.modify a (fun c => { c with state := .evaluating }) } = _
  simp only [KatLang.NeedControl.Collector.bind_run, evalAttempt, hr]
  cases outcome <;> rfl



end KatLang.NeedControl.Memo


namespace KatLang.NeedControl.Formation
open KatLang.NeedControl.Collector NeedSupply NeedDemand

theorem ordinary_singleton (ev) (ctx : EvalCtx) (env : ValEnv) (source : Expr)
    (s t : EvalState) (a : Nat)
    (hn : ∀ operand, source ≠ .sequenceSpread operand)
    (hs : (supplyNeed source ctx env).runState s = (.ok a, t)) :
    (form ev ctx env [source]).runState s = (.ok [(a, some source)], t) := by
  cases source <;> simp only [form, slot, bind_run, hs] <;> try rfl
  rename_i operand
  exact (hn operand rfl).elim

theorem computed_spread_ready (ev) (ctx : EvalCtx) (env : ValEnv)
    (operand : Expr) (values : List Result) (s t : EvalState)
    (hk : (spreadCollectorSlice? operand ctx).runState s = (.ok none, s))
    (he : (ev (.sequenceSpread operand) ctx env).runState s = (.ok (.items values), t)) :
    (slot ev ctx env (.sequenceSpread operand)).runState s =
      (values.mapM (fun value => do
        pure (← readyNeed (value, Result.valueCount value), (none : Option Expr)))).runState t := by
  simp only [slot, bind_run, hk, he]

/-- **Cell-preserving spread (CallReference S2).** A computed spread slot whose capability
    contributes transported CELLS (an argument view's plan supply) supplies EXACTLY those cells,
    in order, with their sources: the slot itself allocates nothing, wraps nothing and demands
    nothing beyond the capability's own run. -/
theorem computed_spread_transports (ev) (ctx : EvalCtx) (env : ValEnv)
    (operand : Expr) (cells : List NeedSupply.Sourced) (s t : EvalState)
    (hk : (spreadCollectorSlice? operand ctx).runState s = (.ok none, s))
    (he : (ev (.sequenceSpread operand) ctx env).runState s = (.ok (.cells cells), t)) :
    (slot ev ctx env (.sequenceSpread operand)).runState s = (.ok cells, t) := by
  simp only [slot, bind_run, hk, he]
  rfl

theorem spread_failure (ev) (ctx : EvalCtx) (env : ValEnv)
    (operand : Expr) (rest : OutputBundle) (s t : EvalState) (e : Error)
    (hk : (spreadCollectorSlice? operand ctx).runState s = (.ok none, s))
    (he : (ev (.sequenceSpread operand) ctx env).runState s = (.error e, t)) :
    (form ev ctx env (.sequenceSpread operand :: rest)).runState s = (.error e, t) := by
  simp only [form, slot, bind_run, hk, he]




end KatLang.NeedControl.Formation


namespace KatLang.NeedControl.Schedule
open KatLang.NeedControl.Collector NeedSupply NeedDemand KatLang.NeedControl.Provenance

/-- A complete retained-state schedule, including the state of a failing callback.
    This is an observation of a finite list of callbacks, not a heap interpreter. -/
def schedule {α β : Type} (f : α → EvalM β) : List α → EvalState → Except Error (List β) × EvalState
  | [], s => (.ok [], s)
  | a :: rest, s =>
    match (f a).runState s with
    | (.error e, t) => (.error e, t)
    | (.ok v, t) =>
      match schedule f rest t with
      | (.error e, u) => (.error e, u)
      | (.ok vs, u) => (.ok (v :: vs), u)

theorem mapM_loop_schedule {α β : Type} (f : α → EvalM β) (xs : List α)
    (acc : List β) (s : EvalState) :
    (List.mapM.loop f xs acc).runState s =
      let r := schedule f xs s
      (r.1.map (acc.reverse ++ ·), r.2) := by
  induction xs generalizing acc s with
  | nil => simp [List.mapM.loop, schedule, pure_run, Except.map]
  | cons a rest ih =>
    simp only [List.mapM.loop, bind_run, schedule]
    cases h : (f a).runState s with
    | mk out t =>
      cases out with
      | error e => rfl
      | ok v =>
        dsimp only
        rw [ih]
        cases hr : schedule f rest t with
        | mk tail u =>
          cases tail <;> simp [List.reverse_cons, List.append_assoc, Except.map]

theorem mapM_schedule {α β : Type} (f : α → EvalM β) (xs : List α) (s : EvalState) :
    (xs.mapM f).runState s = schedule f xs s := by
  rw [List.mapM, mapM_loop_schedule]
  cases h : schedule f xs s with
  | mk out t => cases out <;> rfl

theorem collector_schedule (demand : Nat → EvalM CountedResult) (xs : List Nat) (s : EvalState) :
    (materialize demand xs).runState s =
      let r := schedule (fun a => Prod.fst <$> demand a) xs s
      (r.1.map makeCollectionListResult, r.2) := by
  simp only [materialize, bind_run, mapM_schedule]
  cases h : schedule (fun a => Prod.fst <$> demand a) xs s with
  | mk out t => cases out <;> rfl

theorem schedule_failure_prefix {α β : Type} (f : α → EvalM β) (leading tail : List α)
    (s t : EvalState) (e : Error) (h : schedule f leading s = (.error e, t)) :
    schedule f (leading ++ tail) s = (.error e, t) := by
  induction leading generalizing s with
  | nil => cases h
  | cons a rest ih =>
    simp only [List.cons_append, schedule] at h ⊢
    cases hr : (f a).runState s with
    | mk out u =>
      rw [hr] at h
      cases out with
      | error err => exact h
      | ok v =>
        dsimp only at h ⊢
        cases ht : schedule f rest u with
        | mk out2 w =>
          rw [ht] at h
          cases out2 with
          | error err =>
            have eq := Prod.mk.inj h
            cases eq.1
            cases eq.2
            rw [ih u ht]
          | ok vs => cases h

theorem formation_step (ev) (ctx : EvalCtx) (env : ValEnv) (a : Expr) (rest : OutputBundle)
    (s : EvalState) :
    (form ev ctx env (a :: rest)).runState s =
      match (slot ev ctx env a).runState s with
      | (.error e, t) => (.error e, t)
      | (.ok head, t) =>
        match (form ev ctx env rest).runState t with
        | (.error e, u) => (.error e, u)
        | (.ok tail, u) => (.ok (head ++ tail), u) := by
  simp only [form, bind_run]
  cases h : (slot ev ctx env a).runState s with
  | mk out t =>
    cases out with
    | error e => rfl
    | ok head =>
      dsimp only
      cases ht : (form ev ctx env rest).runState t with
      | mk tail u => cases tail <;> rfl

theorem formation_failure_prefix (ev) (ctx : EvalCtx) (env : ValEnv)
    (leading tail : OutputBundle) (s t : EvalState) (e : Error)
    (h : (form ev ctx env leading).runState s = (.error e, t)) :
    (form ev ctx env (leading ++ tail)).runState s = (.error e, t) := by
  induction leading generalizing s with
  | nil => cases h
  | cons a rest ih =>
    simp only [List.cons_append, formation_step] at h ⊢
    cases hr : (slot ev ctx env a).runState s with
    | mk out u =>
      rw [hr] at h
      cases out with
      | error err => exact h
      | ok head =>
        dsimp only at h ⊢
        cases ht : (form ev ctx env rest).runState u with
        | mk out2 w =>
          rw [ht] at h
          cases out2 with
          | error err =>
            have eq := Prod.mk.inj h
            cases eq.1
            cases eq.2
            rw [ih u ht]
          | ok vs => cases h

/-- Explicit Ready allocation schedule: order, per-item value count, metadata, and state. -/
def readyRun : List Result → EvalState → List Sourced × EvalState
  | [], s => ([], s)
  | v :: vs, s =>
    let r := readyRun vs {s with needs := s.needs.push {suspension := .ready (v, Result.valueCount v)}}
    ((s.needs.size, none) :: r.1, r.2)

def readyItem (v : Result) : EvalM Sourced :=
  do pure (← readyNeed (v, Result.valueCount v), none)

theorem ready_item_run (v : Result) (s : EvalState) :
    (readyItem v).runState s =
      (.ok (s.needs.size, none),
        {s with needs := s.needs.push {suspension := .ready (v, Result.valueCount v)}}) := rfl

theorem ready_schedule (items : List Result) (s : EvalState) :
    schedule readyItem items s =
      (.ok (readyRun items s).1, (readyRun items s).2) := by
  induction items generalizing s with
  | nil => rfl
  | cons v vs ih =>
    simp only [schedule, ready_item_run, ih]
    rfl

theorem ready_cells_exact (items : List Result) (s : EvalState) :
    (items.mapM (fun v => do pure (← readyNeed (v, Result.valueCount v), (none : Option Expr)))).runState s =
      (.ok (readyRun items s).1, (readyRun items s).2) := by
  rw [mapM_schedule]
  exact ready_schedule items s

theorem ready_cardinality (items : List Result) (s : EvalState) :
    (readyRun items s).1.length = items.length ∧
      (readyRun items s).2.needs.size = s.needs.size + items.length := by
  induction items generalizing s with
  | nil => exact ⟨rfl, by simp [readyRun]⟩
  | cons v vs ih =>
    simp only [readyRun]
    have h := ih {s with needs := s.needs.push {suspension := .ready (v, Result.valueCount v)}}
    constructor
    · simp only [List.length_cons, h.1]
    · simpa [Array.size_push, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.2

theorem ready_addresses (items : List Result) (s : EvalState) :
    (readyRun items s).1.map Prod.fst = List.range' s.needs.size items.length := by
  induction items generalizing s with
  | nil => rfl
  | cons v vs ih =>
    simp only [readyRun, List.map_cons, ih, List.length_cons, List.range'_succ, Array.size_push]

theorem ready_sources (items : List Result) (s : EvalState) :
    (readyRun items s).1.map Prod.snd = List.replicate items.length none := by
  induction items generalizing s with
  | nil => rfl
  | cons v vs ih => simp only [readyRun, List.map_cons, ih, List.length_cons, List.replicate_succ]

theorem known_slot_exact (ev) (ctx : EvalCtx) (env : ValEnv) (operand : Expr)
    (slice : List Nat) (s : EvalState)
    (h : (spreadCollectorSlice? operand ctx).runState s = (.ok (some slice), s)) :
    (slot ev ctx env (.sequenceSpread operand)).runState s =
      (.ok (slice.map (fun a => (a, sourceAt s.needs a))), s) := by
  simp only [slot, bind_run, h]
  exact reopen_run slice s

theorem noncollector_parameter (name : Ident) (caller : EvalCtx) (s : EvalState)
    (activation : Option ParameterActivation) (a : Nat) (cell : NeedCell)
    (hc : (capturedParameterActivation? name caller).runState s = (.ok activation, s))
    (ha : lookupAssoc name (activation.map ParameterActivation.needs |>.getD caller.needEnv) = some a)
    (present : s.needs[a]? = some cell)
    (kind : ∀ slice, cell.suspension ≠ .collector slice) :
    (spreadCollectorSlice? (.param name) caller).runState s = (.ok none, s) := by
  simp only [spreadCollectorSlice?, bind_run, hc, ha, get_run, present]
  cases hs : cell.suspension with
  | expression e ctx env => rfl
  | ready v => rfl
  | collector slice => exact (kind slice hs).elim

theorem source_expression_any_state (e : Expr) (ctx : EvalCtx) (env : ValEnv)
    (status : NeedState) (callable : Option (Except Error (Option Algorithm))) (plan : NeedPlanSupply) (s : EvalState) (a : Nat)
    (h : s.needs[a]? = some ⟨.expression e ctx env, status, callable, plan⟩) :
    (needWrittenSource? a).runState s = (.ok (some e), s) := by
  rw [source_run]
  simp only [sourceAt, h]

theorem allocation_preserves_valid_address (s : EvalState) (suspension : NeedSuspension)
    (a : Nat) (h : a < s.needs.size) :
    a < ((allocateNeed suspension).runState s).2.needs.size := by
  simp only [KatLang.NeedControl.Allocation.allocate_run, Array.size_push]
  omega

theorem size_preserves_valid_address (s t : EvalState) (a : Nat)
    (valid : a < s.needs.size) (nonshrinking : s.needs.size ≤ t.needs.size) :
    a < t.needs.size := Nat.lt_of_lt_of_le valid nonshrinking

/-- Publication into a valid post-callback address updates CURRENT cell only. -/
theorem completion_publication (s : EvalState) (a : Nat) (current : NeedCell)
    (outcome : Except Error CountedResult) (h : s.needs[a]? = some current) :
    (s.needs.modify a (fun c => {c with state := .completed outcome}))[a]? =
      some {current with state := .completed outcome} := by
  simp [Array.getElem?_modify, h]

theorem completion_preserves_size (s : EvalState) (a : Nat) (outcome : Except Error CountedResult) :
    (s.needs.modify a (fun c => {c with state := .completed outcome})).size = s.needs.size := by
  simp

theorem completion_preserves_other_cell (s : EvalState) (a b : Nat)
    (outcome : Except Error CountedResult) (different : b ≠ a) :
    (s.needs.modify a (fun c => {c with state := .completed outcome}))[b]? = s.needs[b]? := by
  simp [Array.getElem?_modify, Ne.symm different]

/-- Actual memo shell publication with explicit original validity, nonshrinking heap,
    and retained suspension identity. Callable and state fields may evolve. -/
theorem suspended_publishes (ev) (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (a : Nat) (s t : EvalState) (cell current : NeedCell) (outcome : Except Error CountedResult)
    (hc : s.needs[a]? = some cell) (hs : cell.state = .suspended)
    (hr : (NeedDemand.suspendedValue ev route demand a cell.suspension).runState
      {s with needs := s.needs.modify a (fun c => {c with state := .evaluating})} = (outcome, t))
    (valid : a < s.needs.size) (nonshrinking : s.needs.size ≤ t.needs.size)
    (present : t.needs[a]? = some current) (identity : current.suspension = cell.suspension) :
    ((NeedDemand.step ev route demand a).runState s).1 = outcome ∧
    ((NeedDemand.step ev route demand a).runState s).2.needs[a]? =
      some {current with state := .completed outcome} ∧
    current.suspension = cell.suspension ∧ a < t.needs.size := by
  rw [KatLang.NeedControl.Memo.suspended_retains_state ev route demand a s t cell outcome hc hs hr]
  exact ⟨rfl, completion_publication t a current outcome present, identity,
    size_preserves_valid_address s t a valid nonshrinking⟩

/-- Whole-cell prefix equality is intentionally absent: completion changes NeedState. -/
theorem completed_reuse_after_publication (ev) (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (s : EvalState) (a : Nat) (current : NeedCell) (outcome : Except Error CountedResult)
    (h : s.needs[a]? = some current) :
    let t := {s with needs := s.needs.modify a (fun c => {c with state := .completed outcome})}
    (NeedDemand.step ev route demand a).runState t = (outcome, t) := by
  exact KatLang.NeedControl.Memo.completed_sticky ev route demand a _ _ outcome (completion_publication s a current outcome h) rfl


end KatLang.NeedControl.Schedule

namespace KatLang.NeedControl.Production
open Collector Provenance Memo Schedule Allocation

theorem computation_ext {α : Type} {x y : EvalM α} (h : x.runState = y.runState) : x = y := by
  cases x; cases y; cases h; rfl

theorem evalM_associativity {α β γ : Type} (x : EvalM α) (f : α → EvalM β) (g : β → EvalM γ) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
  apply computation_ext
  change ((x.runState >>= fun a => (f a).runState) >>= fun b => (g b).runState) =
    (x.runState >>= fun a => (f a).runState >>= fun b => (g b).runState)
  exact bind_assoc x.runState (fun a => (f a).runState) (fun b => (g b).runState)

/-- The public sourced entry point is the ONE total formation core at `evalSupplySpread`.
    Recursive callers install the same specialization directly (a source fact). -/
theorem sourced_specialization (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    formNeedSupplySourced args ctx env = NeedSupply.form evalSupplySpread ctx env args := rfl

theorem address_projection (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    formNeedSupply args ctx env = (do
      pure ((← formNeedSupplySourced args ctx env).map Prod.fst)) := rfl

theorem address_specialization (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    formNeedSupply args ctx env = NeedSupply.addresses evalSupplySpread ctx env args := rfl

/-- Successful address-only formation preserves the sourced order and final state. -/
theorem address_projection_run (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (s t : EvalState) (sourced : List NeedSupply.Sourced)
    (h : (formNeedSupplySourced args ctx env).runState s = (.ok sourced, t)) :
    (formNeedSupply args ctx env).runState s = (.ok (sourced.map Prod.fst), t) := by
  simp only [address_projection, Collector.bind_run, h]
  rfl

/-- The public demand entry point is total. The recursive edge is still opaque;
    this does NOT assert a kernel equality to demandNeedRecursive. -/
theorem demand_specialization (a : Nat) :
    demandNeed a = NeedDemand.step evalCounted productionPlanRoute demandNeedRecursive a := rfl

/-- This is the actual collector arm the production shell executes. -/
theorem collector_specialization (ev) (route : NeedPlan.Route) (recur : Nat → EvalM CountedResult) (a : Nat) (slice : List Nat) :
    NeedDemand.suspendedValue ev route recur a (.collector slice) =
      NeedDemand.materialize recur slice := rfl

/-- The R3 interface consumes the total formation's projection with no new adapter,
    reallocation, capability, pattern or second binder. -/
theorem binder_composition (channels : NeedChannels) (patterns : List NeedPattern)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (family : Bool) :
    (do
      let cells ← formNeedSupply args ctx env
      bindNeedPatterns channels patterns cells family) = (do
      let sourced ← NeedSupply.form evalSupplySpread ctx env args
      NeedBinder.bindPatterns channels.capabilities patterns (sourced.map Prod.fst) family) := by
  simp only [formNeedSupply, formNeedSupplySourced, bindNeedPatterns]
  simp only [evalM_associativity, EvalM.pure_bind]

theorem completed_reuse (a : Nat) (s : EvalState) (cell : NeedCell)
    (outcome : Except Error CountedResult) (hc : s.needs[a]? = some cell)
    (hs : cell.state = .completed outcome) :
    (demandNeed a).runState s = (outcome, s) :=
  Memo.completed_sticky evalCounted productionPlanRoute demandNeedRecursive a s cell outcome hc hs

theorem evaluating_cycle (ev) (route : NeedPlan.Route) (recur : Nat → EvalM CountedResult) (a : Nat)
    (s : EvalState) (cell : NeedCell) (hc : s.needs[a]? = some cell)
    (hs : cell.state = .evaluating) :
    (NeedDemand.step ev route recur a).runState s = (.error .demandCycle, s) := by
  simp only [NeedDemand.step, Collector.bind_run, Provenance.get_run, hc, hs]
  rfl

theorem invalid_address (ev) (route : NeedPlan.Route) (recur : Nat → EvalM CountedResult) (a : Nat)
    (s : EvalState) (hc : s.needs[a]? = none) :
    (NeedDemand.step ev route recur a).runState s =
      (.error (.illegalInEval "invalid need address"), s) := by
  simp only [NeedDemand.step, Collector.bind_run, Provenance.get_run, hc]
  rfl

/-- Empty and singleton collectors remain exact lists for arbitrary VALUE callbacks. -/
theorem collector_empty (recur : Nat → EvalM CountedResult) (s : EvalState) :
    (NeedDemand.materialize recur []).runState s = (.ok (.listValue [], 1), s) := rfl

theorem collector_success (recur : Nat → EvalM CountedResult) (xs : List Nat)
    (s t : EvalState) (values : List Result)
    (h : schedule (fun a => Prod.fst <$> recur a) xs s = (.ok values, t)) :
    (NeedDemand.materialize recur xs).runState s = (.ok (.listValue values, 1), t) := by
  rw [collector_schedule, h]
  rfl

theorem collector_singleton (recur : Nat → EvalM CountedResult) (a : Nat)
    (s t : EvalState) (v : CountedResult) (h : (recur a).runState s = (.ok v, t)) :
    (NeedDemand.materialize recur [a]).runState s = (.ok (.listValue [v.1], 1), t) := by
  simp only [NeedDemand.materialize, List.mapM, List.mapM.loop, Collector.bind_run,
    Collector.map_run, h]
  rfl

/-- Any failing prefix, including the failing callback's final state, prevents
    all later VALUE demands; addresses may repeat or alias. -/
theorem collector_failure_prefix (recur : Nat → EvalM CountedResult)
    (leading tail : List Nat) (s t : EvalState) (e : Error)
    (h : schedule (fun a => Prod.fst <$> recur a) leading s = (.error e, t)) :
    (NeedDemand.materialize recur (leading ++ tail)).runState s = (.error e, t) := by
  rw [collector_schedule, schedule_failure_prefix _ leading tail s t e h]
  rfl

/-- Conditional whole-list heap-size bridge. It concerns the concrete traversal,
    including failed callbacks, without claiming whole-run heap preservation for the partial
    `demandNeedRecursive` driver or its expression-evaluation callback. -/
theorem schedule_nonshrinking {α β : Type} (f : α → EvalM β) (xs : List α)
    (hf : ∀ a, Nonshrinking (f a)) (s : EvalState) :
    s.needs.size ≤ (schedule f xs s).2.needs.size := by
  induction xs generalizing s with
  | nil => exact Nat.le_refl _
  | cons a rest ih =>
    simp only [schedule]
    have ha := hf a s
    cases hr : (f a).runState s with
    | mk out t =>
      rw [hr] at ha
      cases out with
      | error e => exact ha
      | ok v =>
        dsimp only
        have ht := ih t
        cases hs : schedule f rest t with
        | mk out u =>
          rw [hs] at ht
          cases out <;> exact Nat.le_trans ha ht

theorem collector_nonshrinking (recur : Nat → EvalM CountedResult)
    (hr : ∀ a, Nonshrinking (recur a)) (slice : List Nat) :
    Nonshrinking (NeedDemand.materialize recur slice) := by
  intro s
  rw [collector_schedule]
  have hf : ∀ a, Nonshrinking (Prod.fst <$> recur a) := by
    intro a t
    rw [Collector.map_run]
    have h := hr a t
    cases he : (recur a).runState t with
    | mk out u =>
      rw [he] at h
      cases out <;> exact h
  have h := schedule_nonshrinking _ slice hf s
  cases he : schedule (fun a => Prod.fst <$> recur a) slice s with
  | mk out t =>
    rw [he] at h
    exact h

/-- The formation loop composes local size contracts across all slots and errors.
    Discharging the slot premise for the actual partial spread evaluator remains R7. -/
theorem formation_nonshrinking (ev) (ctx : EvalCtx) (env : ValEnv)
    (hs : ∀ source, Nonshrinking (NeedSupply.slot ev ctx env source))
    (args : OutputBundle) : Nonshrinking (NeedSupply.form ev ctx env args) := by
  intro s
  induction args generalizing s with
  | nil => exact Nat.le_refl _
  | cons a rest ih =>
    rw [formation_step]
    have ha := hs a s
    cases he : (NeedSupply.slot ev ctx env a).runState s with
    | mk out t =>
      rw [he] at ha
      cases out with
      | error e => exact ha
      | ok head =>
        dsimp only
        have ht := ih t
        cases hr : (NeedSupply.form ev ctx env rest).runState t with
        | mk tail u =>
          rw [hr] at ht
          cases tail <;> exact Nat.le_trans ha ht

/-- Publication preserves the post-callback CALLABLE memo, including a memoized error.
    The hypothesis names the current cell, not the snapshot read before evaluation. -/
theorem publication_preserves_callable (s : EvalState) (a : Nat) (current : NeedCell)
    (outcome : Except Error CountedResult) (present : s.needs[a]? = some current) :
    ((s.needs.modify a (fun c => {c with state := .completed outcome}))[a]?).map
      NeedCell.callable = some current.callable := by
  rw [completion_publication s a current outcome present]
  rfl

end KatLang.NeedControl.Production
