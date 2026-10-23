import KatLangArityLaws.EvaluatorMemoLinks
import KatLangArityLaws.AlgorithmProjectionGuards

open KatLang KatLang.CallPlan KatLang.MemoLinks KatLang.CallReferenceGuards KatLang.AlgorithmProjectionGuards

/-!
# FG-M1 guards: completed CALLABLE outcomes and recorded links across intervening evaluation

Executable witnesses over the ACTUAL production operations (`demandNeed`, `projectNeedCallable`,
`NeedPlan.calleeCell productionPlanRoute.classify`, `NeedLink.receiverCell`, `aliasBareCell`,
`takeTerminalAliasInvocation`) beside the kernel theorems of `EvaluatorMemoLinks.lean`, and kernel
witnesses of the relation's boundary: the old `CellKept` alone admits changing each newly
protected field, and the RAW setters (`NeedPlan.setCallee`, `NeedLink.setReceiver`, a raw CALLABLE
write) are rejected by `LinkDisc` — CONTRACT-BOUNDARY witnesses, not production defects: production
reaches those writes only through their guarded writers.

Algorithm payloads are compared by their `repr` text in the executable checks (Algorithm and Error
derive no equality); the payloads are chosen distinguishable (`idA` / `idB`), and the kernel
theorems use Lean equality on the whole outcome.
-/

namespace KatLang.EvaluatorMemoLinksGuards

/-! ## Helpers -/

def outcomeText (o : Except Error (Option Algorithm)) : String := reprStr o

/-- Does cell `c'` keep the three FG-M1 facts of `c`? (A Bool rendering of `LinkKept`.) -/
def linkKeptB (c c' : NeedCell) : Bool :=
  (match c.callable with
   | .projected o => match c'.callable with
     | .projected o' => outcomeText o == outcomeText o'
     | _ => false
   | _ => true) &&
  (match c.callee with | some x => c'.callee == some x | none => true) &&
  (match c.receiver with | some x => c'.receiver == some x | none => true)

/-- A Bool rendering of `LinkHeapKept`: every cell of `h` is present in `h'` and kept. -/
def heapLinkKeptB (h h' : Array NeedCell) : Bool :=
  (List.range h.size).all fun a =>
    match h[a]?, h'[a]? with
    | some c, some c' => linkKeptB c c'
    | some _, none => false
    | none, _ => true

/-- How many cells carry each protected fact (so a check is never vacuous). -/
def protectedCounts (h : Array NeedCell) : Nat × Nat × Nat :=
  h.foldl (fun (p, e, r) c =>
    ((match c.callable with | .projected _ => p + 1 | _ => p),
     (match c.callee with | some _ => e + 1 | none => e),
     (match c.receiver with | some _ => r + 1 | none => r))) (0, 0, 0)

def stateOf (rows : List Expr) : EvalState :=
  match runResultWithState (program (extra ++ refR) rows) with
  | .ok (_, s) => s
  | .error _ => {}

/-- Two distinguishable callable payloads and two distinguishable failures. -/
def idA : Algorithm := alg ["x"] [] [] [.num 1]
def idB : Algorithm := alg ["y"] [] [] [.num 2]

/-- The final state of `Ap(R.Algorithm, 7)`: a supplied link (completed CALLABLE identity, recorded
    receiver), the captured plan (recorded callee), the callee cell (completed CALLABLE) — extended
    with three crafted completed cells: identity `idA`, successful absence, failure `divByZero`,
    and one unprojected and one suspended cell for legitimate transitions. -/
def base : EvalState :=
  let s := stateOf [callN "Ap" [algorithm R, .num 7]]
  { s with needs := s.needs ++ #[
      { suspension := .expression (.num 11) EvalCtx.empty [], callable := .projected (.ok (some idA)) },
      { suspension := .expression (.num 12) EvalCtx.empty [], callable := .projected (.ok none) },
      { suspension := .expression (.num 13) EvalCtx.empty [], callable := .projected (.error .divByZero) },
      { suspension := .expression (.num 14) EvalCtx.empty [] },
      { suspension := .expression (.num 15) EvalCtx.empty [] }] }

def n0 : Nat := base.needs.size - 5   -- `.ok (some idA)`
def n1 : Nat := base.needs.size - 4   -- `.ok none`
def n2 : Nat := base.needs.size - 3   -- `.error .divByZero`
def n3 : Nat := base.needs.size - 2   -- unprojected, suspended
def n4 : Nat := base.needs.size - 1   -- unprojected, suspended

-- The base state carries every kind of protected fact (non-vacuity): the link at 0 has a
-- receiver, the plan at 3 a callee.
#guard (base.needs[0]?.bind NeedCell.receiver).isSome && (base.needs[3]?.bind NeedCell.callee).isSome
#guard match protectedCounts base.needs with | (p, e, r) => p ≥ 5 && e ≥ 1 && r ≥ 1

/-- Intervening production work: VALUE of the link (through its recorded receiver) and of the
    plan, CALLABLE of every cell (publishing the unprojected ones), a fresh allocation and a supply
    of a new plan, then VALUE of a crafted cell. -/
def intervene : EvalM Unit := do
  let _ ← evalAttempt (demandNeed 0)
  let _ ← evalAttempt (demandNeed 3)
  for a in List.range base.needs.size do
    let _ ← evalAttempt (projectNeedCallable a)
  let _ ← allocateNeed (.ready (.atom 99, 1))
  let _ ← evalAttempt (demandNeed n4)

def after : EvalState := (intervene.runState base).2

/-! ## 1, 2, 5 — completed outcomes survive VALUE, projection, allocation; legitimate transitions -/

#guard heapLinkKeptB base.needs after.needs
-- The work was real: the heap grew and the crafted unprojected cell was published (a legitimate
-- unprojected → projected transition), the suspended crafted cell's VALUE completed.
#guard after.needs.size > base.needs.size
#guard after.needs[n3]? matches some (NeedCell.mk _ _ (.projected (.ok none)) _ _ _ _ _ _)
#guard after.needs[n4]? matches some (NeedCell.mk _ (.completed (.ok (.atom 15, 1))) _ _ _ _ _ _ _)
-- The exact stored outcomes are reread by the production projection: identity `idA` (not `idB`),
-- successful absence, the stored failure (not absence) — and the reread changes nothing.
#guard match (projectNeedCallable n0).runState after with
  | (.ok (some g), t) => reprStr g == reprStr idA && reprStr g != reprStr idB && t.needs.size == after.needs.size
  | _ => false
#guard match (projectNeedCallable n1).runState after with
  | (.ok none, t) => t.needs.size == after.needs.size
  | _ => false
#guard match (projectNeedCallable n2).runState after with
  | (.error .divByZero, t) => t.needs.size == after.needs.size
  | _ => false

/-! ## 3 — an ordinary error after useful work keeps the protected records in the retained state -/

def failing : EvalM Unit := do
  let a ← allocateNeed (.expression (.num 21) EvalCtx.empty [])
  let _ ← projectNeedCallable a
  let _ ← demandNeed 0
  let _ ← allocateNeed (.ready (.atom 77, 1))

-- The link's VALUE (bare `Sq`) fails with an ordinary arity error AFTER an allocation and a
-- CALLABLE publication; the retained state keeps every protected record and that work.
#guard match failing.runState base with
  | (.error (.withContext _ (.arityMismatch 1 0)), t) =>
    heapLinkKeptB base.needs t.needs && t.needs.size == base.needs.size + 1 &&
    (t.needs[base.needs.size]? matches some (NeedCell.mk _ _ (.projected (.ok none)) _ _ _ _ _ _))
  | _ => false

/-! ## 4 — established callee and receiver survive and are reused without establishment -/

def recordedCallee : Nat := (base.needs[3]?.bind NeedCell.callee).getD 0
def recordedReceiver : Nat := (base.needs[0]?.bind NeedCell.receiver).getD 0

-- After the intervening work, the canonical-callee accessor over the PRODUCTION route classifier
-- returns the recorded address and allocates nothing; likewise the receiver accessor.
#guard match (NeedPlan.calleeCell productionPlanRoute.classify 3).runState after with
  | (.ok c, t) => c == recordedCallee && t.needs.size == after.needs.size
  | _ => false
#guard match (NeedLink.receiverCell 0).runState after with
  | (.ok r, t) => r == recordedReceiver && t.needs.size == after.needs.size
  | _ => false

/-- A fresh unrecorded plan/link pair (from `R.Algorithm(8)` in a new run) establishes its records
    — the legitimate absent → recorded transition — and they then survive. -/
def fresh : EvalState := stateOf [algorithmCall R [.num 8], callN "Ap" [algorithm R, .num 2]]
#guard match protectedCounts fresh.needs with | (_, e, r) => e ≥ 1 && r ≥ 1
#guard heapLinkKeptB fresh.needs (intervene.runState fresh).2.needs

/-! ## 6 — the D4 alias whole-cell writes keep completed CALLABLE and links -/

/-- An alias binding cell (reached by parameter transport) with a completed CALLABLE identity and
    both links recorded. -/
def aliasCell (use : Nat) : NeedCell :=
  { suspension := .expression (.num 31) EvalCtx.empty [], callable := .projected (.ok (some idA)),
    callee := some 7, receiver := some 8, aliasUse := use }
def aliasState (use : Nat) : EvalState := { needs := #[aliasCell use] }
def aliasCtx : EvalCtx := { callStack := [], needEnv := [("x", 0)] }

-- `aliasUse = 2`, no bare cell yet: the tail path writes back the saved cell with `aliasBare`.
#guard match (aliasBareCell idB (.param "x") aliasCtx).runState (aliasState 2) with
  | (.ok _, t) =>
    heapLinkKeptB (aliasState 2).needs t.needs &&
    (t.needs[0]? matches some (NeedCell.mk _ _ _ _ _ _ _ 2 (some _)))
  | _ => false
-- `aliasUse = 0`: the bare read claims the cell (`aliasUse := 1`).
#guard match (aliasBareCell idB (.param "x") aliasCtx).runState (aliasState 0) with
  | (.ok 0, t) =>
    heapLinkKeptB (aliasState 0).needs t.needs && (t.needs[0]? matches some (NeedCell.mk _ _ _ _ _ _ _ 1 _))
  | _ => false
-- A terminal invocation's claim (`claimTerminalAliasInitial`) keeps the three fields too.
#guard match claimTerminalAliasInitial (aliasCell 0) with
  | some claimed => linkKeptB (aliasCell 0) claimed && claimed.aliasUse == 2
  | none => false

/-- Exercise the terminal invocation's actual whole-cell write, with all three protected
    facts already present in its entry heap. -/
def terminalAlias : Algorithm := alg [] [] [] [.num 0]
def terminalAliasState : EvalState :=
  { aliasState 0 with aliasCells := [(aliasCellKey terminalAlias, 0)] }

#guard match (takeTerminalAliasInvocation terminalAlias).runState terminalAliasState with
  | (.ok (some 0), t) => heapLinkKeptB terminalAliasState.needs t.needs &&
    t.needs.size == terminalAliasState.needs.size &&
    (t.needs[0]? matches some (NeedCell.mk _ _ _ _ _ _ _ 2 _))
  | _ => false
-- A second invocation cannot claim the already-consumed initial work again.
#guard match (do
    let _ ← takeTerminalAliasInvocation terminalAlias
    takeTerminalAliasInvocation terminalAlias).runState terminalAliasState with
  | (.ok none, t) => heapLinkKeptB terminalAliasState.needs t.needs &&
    t.needs.size == terminalAliasState.needs.size
  | _ => false

/-! ## 7 — the old `CellKept` alone permits changing each newly protected field -/

def completedCell : NeedCell :=
  { suspension := .ready (.atom 1, 1), callable := .projected (.error .divByZero),
    callee := some 3, receiver := some 4 }

theorem cellKept_permits_callable_change :
    CellKept completedCell { completedCell with callable := .projected (.ok none) } ∧
    ¬ LinkKept completedCell { completedCell with callable := .projected (.ok none) } :=
  ⟨⟨rfl, fun _ h => h, fun _ h => h, fun _ h => h⟩,
   fun k => by have := k.callable _ rfl; cases this⟩

theorem cellKept_permits_callee_change :
    CellKept completedCell { completedCell with callee := some 9 } ∧
    ¬ LinkKept completedCell { completedCell with callee := some 9 } :=
  ⟨⟨rfl, fun _ h => h, fun _ h => h, fun _ h => h⟩,
   fun k => by have := k.callee 3 rfl; cases this⟩

theorem cellKept_permits_receiver_change :
    CellKept completedCell { completedCell with receiver := none } ∧
    ¬ LinkKept completedCell { completedCell with receiver := none } :=
  ⟨⟨rfl, fun _ h => h, fun _ h => h, fun _ h => h⟩,
   fun k => by have := k.receiver 4 rfl; cases this⟩

-- The same at the operation level: the raw callee setter IS `Disciplined` (old relation)…
example : Disciplined (NeedPlan.setCallee 0 5) := disciplined_setCallee 0 5

/-! ## 8 — contract boundary: raw overwriting setters are rejected by `LinkDisc` -/

def recordedState : EvalState := { needs := #[completedCell] }

/-- …but NOT `LinkDisc`: overwriting a recorded callee is outside the contract (production only
    calls `setCallee` from `calleeCell`'s unrecorded branch). -/
theorem raw_setCallee_rejected : ¬ LinkDisc (NeedPlan.setCallee 0 5) := by
  intro h
  obtain ⟨c', hc', k⟩ := h recordedState 0 completedCell rfl
  have hcal := k.callee 3 rfl
  rw [setCallee_run] at hc'
  simp [withCallee, recordedState] at hc'
  subst hc'
  cases hcal

theorem raw_setReceiver_rejected : ¬ LinkDisc (NeedLink.setReceiver 0 5) := by
  intro h
  obtain ⟨c', hc', k⟩ := h recordedState 0 completedCell rfl
  have hrec := k.receiver 4 rfl
  have hrun : ((NeedLink.setReceiver 0 5).runState recordedState).2.needs[0]? =
      some { completedCell with receiver := some 5 } := rfl
  rw [hrun] at hc'
  cases hc'
  cases hrec

/-- A raw CALLABLE publication over a completed cell. -/
def rawPublish (a : Nat) (o : Except Error (Option Algorithm)) : EvalM Unit :=
  modify fun s => { s with needs := s.needs.modify a (fun cell => { cell with callable := .projected o }) }

theorem raw_callable_write_rejected : ¬ LinkDisc (rawPublish 0 (.ok none)) := by
  intro h
  obtain ⟨c', hc', k⟩ := h recordedState 0 completedCell rfl
  have hcal := k.callable _ rfl
  have hrun : ((rawPublish 0 (.ok none)).runState recordedState).2.needs[0]? =
      some { completedCell with callable := .projected (.ok none) } := rfl
  rw [hrun] at hc'
  cases hc'
  cases hcal

-- …while the GUARDED writers over the same completed cell change nothing: the projection shell
-- returns the stored failure (never absence) without running its callback, the accessors return
-- the recorded addresses.
#guard match (NeedProjection.step (fun _ => pure (some idB)) 0).runState recordedState with
  | (.error .divByZero, t) => (t.needs[0]? matches some (NeedCell.mk _ _ (.projected (.error .divByZero)) _ _ (some 3) (some 4) _ _))
  | _ => false
#guard match (NeedPlan.calleeCell (fun _ => throw .badArity) 0).runState recordedState with
  | (.ok 3, t) => t.needs.size == 1
  | _ => false
#guard match (NeedLink.receiverCell 0).runState recordedState with
  | (.ok 4, t) => t.needs.size == 1
  | _ => false

/-! ## Entry-state preservation is not an in-flight first-writer law

A callee record made INSIDE `calleeCell`'s own route classification (here by a callback that calls
the raw setter) is overwritten by the enclosing establishment's record. `LinkDisc (calleeCell …)`
still holds — the ENTRY cell had no callee — and this is outside FG-M1's claim. -/

def planCell : NeedCell := { suspension := .expression (.call (.resolve "F") []) EvalCtx.empty [] }
#guard (NeedPlan.ofSuspension? planCell.suspension).isSome
#guard match (NeedPlan.calleeCell (fun _ => do NeedPlan.setCallee 0 99; pure .call) 0).runState
    { needs := #[planCell] } with
  | (.ok c, t) => c != 99 && (t.needs[0]?.bind NeedCell.callee) == some c
  | _ => false

/-! ## The universal theorems instantiated (kernel) -/

/-- After ANY production operation from `recordedState`, the completed failure is reread exactly,
    and the recorded callee and receiver are reread with no effect. -/
example (c : EvalCall) :
    (projectNeedCallable 0).runState ((evalUnbounded c).runState recordedState).2 =
      (.error .divByZero, ((evalUnbounded c).runState recordedState).2) ∧
    (NeedPlan.calleeCell productionPlanRoute.classify 0).runState ((evalUnbounded c).runState recordedState).2 =
      (.ok 3, ((evalUnbounded c).runState recordedState).2) ∧
    (NeedLink.receiverCell 0).runState ((evalUnbounded c).runState recordedState).2 =
      (.ok 4, ((evalUnbounded c).runState recordedState).2) :=
  ⟨(production_callable_reread c 0 recordedState completedCell _ rfl rfl).2,
   production_callee_reread c _ 0 3 recordedState completedCell rfl rfl,
   production_receiver_reread c 0 4 recordedState completedCell rfl rfl⟩

/-- …and after any finite sequence of production operations. -/
example (ops : List EvalCall) :
    (projectNeedCallable 0).runState (runOps ops recordedState) = (.error .divByZero, runOps ops recordedState) :=
  runOps_callable_reread ops 0 recordedState completedCell _ rfl rfl

end KatLang.EvaluatorMemoLinksGuards
