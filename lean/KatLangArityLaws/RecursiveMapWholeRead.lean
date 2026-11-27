import KatLangArityLaws.EvaluatorCore
import CoreTests.LazyCollections

open KatLang KatLang.EvaluatorCore

/-!
# The whole read of a recursively mapped list never completes (ledger E-24 (vii), November 2026)

For `F(x) = [x].map(F)`, `F(1).count` gives `1` without demanding the mapped position.
Reading `F(1)` whole demands the one position of `[x].map(F)`, a fresh call of `F` whose result is a fresh list
with a fresh position, and so on. `CoreTests/LazyCollections.lean` § READ GENERATIONS observes that
the run's fuel approximation is incomplete at the fuels 50, 200 and 1,000, and that the count
completes at fuel 1,000. This module proves the first observation for EVERY fuel. It concerns that
exact program and the exact entry point the guards use: the production core
`evalFuel fuel (.evalRunValue e { callStack := [preludeAlg] } [])` from `EvalState.empty`, where `e`
is the identified program.

## Kernel-checked results

* `wholeRead_incomplete`, `fuelValue_F1_incomplete` (the guard's `recursiveMapWholeReadAt`): the outcome is
  `fuelExhausted` at every fuel.
* `wholeRead_production_incomplete`: the production evaluator at the same call (`evalUnbounded`, the
  fuel search over the same core) never completes, by the production bridge
  (`production_completes_iff`).

## The generation invariant

The read is a chain of GENERATIONS. Generation `n` materializes the one position of the list the
previous generation built (the root, for `n = 0`). It demands that position, which calls `F`. It
then allocates the materialization of the position's value and demands it three evaluator calls
deeper than its own (`spine_inc`, `materialize_inc`). `Gen s N stk B A path` describes the state in
which a generation's materialization cell is demanded. It constrains six cells of the block of seven
at `N`, over a heap of `N + 7` cells: the item `x` (a suspended Ready `1`, or the root's suspended
written `1`), the unprojected mapper cell `F`, the suspended mapped position `F(x)` in the context of
the `F` body entered over `stk` with binding context `B` and activation `A`, and the suspended Ready
source, Ready path and cell of the materialization. Every cell of the path lies below `N`. The
receiver `[x]` at `N + 1` and the rest of the state are not constrained.

Each generation allocates exactly seven FRESH cells (`gen_next`). These are the callback's Ready
`1`, the receiver `[x]`, the mapper `F`, the mapped position and the next materialization's source,
path and cell. A generation records one lexical activation and one binding context, and it pushes
one `F` onto the call stack. The demanded position is always a fresh, suspended cell, so the read
never re-reads a memoized prefix. The positions read before stay on the materialization path, below
`N`, so the path check reads the next position instead of reporting a cycle
(`materializePosition_fresh'`). The earlier generations' cells, completed or still evaluating, are
not read again. The proof uses an outcome calculus up to incompleteness: at every fuel, a call
(`EvF`) or a body (`Ev`) is the incomplete outcome or ends with exactly the stated outcome and
state. It has one lemma per evaluator arm the run takes, the call of `F` (`fCall`), the mapped
position (`demandPosition`), the root (`root_output`, `gen_root`) and strong induction on fuel
(`gen_incomplete`).

Not claimed:
* anything about C#, which ends the read with `EvaluationDepthExceeded` (the pairing in
  `LazyCollectionTests` stays finite evidence);
* any other program: there is no general theorem that a result which keeps building lists diverges;
* the lazy extension of the heap-renaming simulation: generations are related by an invariant over
  the actual heap, not by a renaming;
* the all-row `PlainRows` invariant;
* the public `runResult`, which adds identification, validation and the run boundary around this
  call;
* the positive count control `F(1).count`, which stays a guard (`CoreTests/LazyCollections.lean`)
  and is no theorem here.
-/

namespace KatLang.RecursiveMapWholeRead

/-! ## 1. Outcomes up to incompleteness -/

/-- `m` from `s` is incomplete, or ends with outcome `r` in state `t`. -/
def Ev {α : Type} (m : EvalM α) (s : EvalState) (r : Except Error α) (t : EvalState) : Prop :=
  (m.runState s).1 = .error .fuelExhausted ∨ m.runState s = (r, t)

/-- Call `c` from `s` at EVERY fuel: the incomplete outcome, or exactly `(r, t)`. -/
def EvF (c : EvalCall) (s : EvalState) (r : Except Error c.Ret) (t : EvalState) : Prop :=
  ∀ j, (evalFuel j c).runState s = (.error .fuelExhausted, {}) ∨ (evalFuel j c).runState s = (r, t)

@[local simp] theorem get_run (s : EvalState) : (get : EvalM EvalState).runState s = (.ok s, s) := rfl
@[local simp] theorem set_run (s t : EvalState) : (set t : EvalM PUnit).runState s = (.ok PUnit.unit, t) := rfl
@[local simp] theorem modify_run (f : EvalState → EvalState) (s : EvalState) :
    (modify f : EvalM PUnit).runState s = (.ok PUnit.unit, f s) := rfl
@[local simp] theorem pure_run {α : Type} (a : α) (s : EvalState) : (pure a : EvalM α).runState s = (.ok a, s) := rfl
@[local simp] theorem throw_run {α : Type} (e : Error) (s : EvalState) :
    (throw e : EvalM α).runState s = (.error e, s) := rfl
@[local simp] theorem error_run {α : Type} (e : Error) (s : EvalState) :
    (EvalM.error e : EvalM α).runState s = (.error e, s) := rfl

theorem Ev.of_eq {α : Type} {m : EvalM α} {s : EvalState} {r : Except Error α} {t : EvalState}
    (h : m.runState s = (r, t)) : Ev m s r t := .inr h

theorem Ev.pure {α : Type} (a : α) (s : EvalState) : Ev (pure a : EvalM α) s (.ok a) s := .inr rfl

theorem Ev.bind {α β : Type} {m : EvalM α} {f : α → EvalM β} {s u t : EvalState} {a : α}
    {r : Except Error β} (hm : Ev m s (.ok a) u) (hf : Ev (f a) u r t) : Ev (m >>= f) s r t := by
  unfold Ev at *
  rw [EvalM.bind_runState]
  rcases hm with hm | hm
  · left
    revert hm
    rcases m.runState s with ⟨o, v⟩
    intro hm
    simp only at hm
    subst hm
    rfl
  · rw [hm]
    exact hf

/-- A call's outcome at every fuel, from its body's outcome over every fuel iterate. -/
theorem EvF.of_body {c : EvalCall} {s : EvalState} {r : Except Error c.Ret} {t : EvalState}
    (h : ∀ j, Ev (evalStep (evalFuel j) c) s r t) : EvF c s r t := by
  intro j
  cases j with
  | zero => exact .inl rfl
  | succ j =>
    rw [evalFuel_succ]
    by_cases hc : ((evalStep (evalFuel j) c).runState s).1 = .error .fuelExhausted
    · exact .inl (normalize_of_incomplete _ s hc)
    · rw [normalize_of_complete _ s hc]
      rcases h j with h' | h'
      · exact absurd h' hc
      · exact .inr h'

/-- A recursive call inside a body: its outcome up to incompleteness. -/
theorem EvF.ev {c : EvalCall} {s : EvalState} {r : Except Error c.Ret} {t : EvalState}
    (h : EvF c s r t) (j : Nat) : Ev (evalFuel j c) s r t := by
  rcases h j with h | h
  · left; rw [h]
  · right; exact h


/-! ## 2. The terms the run builds -/

/-- The body of `F`: `[x].map(F)` as the front end elaborates it. -/
def fBody : Expr := .dotMember (.listLiteral [.param "x"]) "map" (.resolve "map") (some [.resolve "F"])
def xPattern : ParameterPattern := .capture { name := "x", kind := .normal }
/-- `F` as identified. -/
def fDef : Algorithm := .mk none [xPattern] [] [] [fBody] (some (.syntax 2))
def fProp : PropDef :=
  { name := "F", alg := fDef, isPublic := false, exposure := .exported, identity := some (.syntax 1),
    requiredOwnerDepths := none }
def callF1 : Expr := .call (.resolve "F") [.num 1]
/-- The identified program. -/
def progA : Algorithm := .mk none [] [] [fProp] [callF1] (some (.syntax 0))
def preludeScope : ScopeCtx := preludeAlg.asScopeCtx
/-- The program wired under the prelude. -/
def progW : Algorithm := .mk (some preludeScope) [] [] [fProp] [callF1] (some (.syntax 0))
def progScope : ScopeCtx := .mk (some preludeScope) [] [] [fProp] [callF1] [] none (some (.syntax 0))
/-- `F` wired under the program: what every lookup of `F` yields. -/
def FW : Algorithm := .mk (some progScope) [xPattern] [] [] [fBody] (some (.syntax 2))
/-- The head scope of the `F` invocation recorded as activation `A`. -/
def fScope (A : Nat) : ScopeCtx := .mk (some progScope) ["x"] [] [] [fBody] [] (some A) (some (.syntax 2))
/-- The context of an `F` body entered over the caller stack `stk`, with `x` at cell `X`, binding
    context `B` and activation `A`. -/
def fCtx (stk : List Algorithm) (X B A : Nat) : EvalCtx :=
  { callStack := FW :: stk, needEnv := [("x", X)], bindingContext := B, headScope := some (fScope A) }

@[local simp] theorem FW_params : FW.params = ["x"] := rfl
@[local simp] theorem fCtx_head (stk : List Algorithm) (X B A : Nat) : (fCtx stk X B A).head? = some FW := rfl
@[local simp] theorem fCtx_site (stk : List Algorithm) (X B A : Nat) : siteScope? (fCtx stk X B A) = some (fScope A) := rfl
@[local simp] theorem fCtx_needEnv (stk : List Algorithm) (X B A : Nat) : (fCtx stk X B A).needEnv = [("x", X)] := rfl

theorem listLiteral_body (j : Nat) (stk : List Algorithm) (X B A : Nat) (s : EvalState) :
    Ev (evalStep (evalFuel j) (.evalListLiteralCounted [.param "x"] (fCtx stk X B A) []))
      s (.ok (.listValue [.deferred X], 1)) s := by
  apply Ev.of_eq
  simp [evalStep, EvalBody.evalListLiteralCounted, EvalBody.evalListLiteralCounted.collect, supplyNeed,
    capturedParameterActivation?, capturedParameter, lookupAssoc]


/-! ## 3. Wrappers on success -/

theorem Ev.evalAttempt {α : Type} {m : EvalM α} {s t : EvalState} {a : α} (h : Ev m s (.ok a) t) :
    Ev (KatLang.evalAttempt m) s (.ok (.ok a)) t := by
  unfold Ev at *
  have key : (KatLang.evalAttempt m).runState s = (match m.runState s with
      | (result, nextState) =>
        if result.isIncomplete then ((.error .fuelExhausted : Except Error (Except Error α)), nextState)
        else (.ok result, nextState)) := rfl
  rw [key]
  rcases h with h | h
  · left
    revert h
    rcases m.runState s with ⟨o, u⟩
    intro h
    simp only at h
    subst h
    rfl
  · right
    rw [h]
    rfl

theorem Ev.withNested {α : Type} {m : EvalM α} {s t : EvalState} {a : α} (h : Ev m s (.ok a) t) :
    Ev (withNestedMissingOutput m) s (.ok a) t := by
  unfold withNestedMissingOutput
  exact Ev.bind (Ev.evalAttempt h) (Ev.pure _ _)

theorem Ev.withCtx {α : Type} {msg : String} {m : EvalM α} {s t : EvalState} {a : α} (h : Ev m s (.ok a) t) :
    Ev (KatLang.withCtx msg m) s (.ok a) t := by
  unfold KatLang.withCtx
  exact Ev.bind (Ev.evalAttempt h) (Ev.pure _ _)

theorem Ev.map {α β : Type} {f : α → β} {m : EvalM α} {s t : EvalState} {a : α} (h : Ev m s (.ok a) t) :
    Ev (f <$> m) s (.ok (f a)) t := by
  show Ev (m >>= fun x => (Pure.pure (f x) : EvalM β)) s _ t
  exact Ev.bind h (Ev.pure _ _)

/-! ## 4. The VALUE demand shell over one cell -/

def markEvaluating (s : EvalState) (a : Nat) : EvalState :=
  { s with needs := s.needs.modify a (fun c => { c with state := .evaluating }) }

def markCompleted (s : EvalState) (a : Nat) (o : Except Error CountedResult) : EvalState :=
  { s with needs := s.needs.modify a (fun c => { c with state := .completed o }) }

/-- A suspended Ready cell holding no deferred item completes with its value. -/
theorem demand_ready (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (demand : Nat → EvalM CountedResult) (a : Nat) (s : EvalState) (cell : NeedCell) (v : CountedResult)
    (hcell : s.needs[a]? = some cell) (hsusp : cell.suspension = .ready v) (hstate : cell.state = .suspended)
    (hv : ∀ c, v.fst ≠ .deferred c) :
    Ev (NeedDemand.step ev route demand a) s (.ok v) (markCompleted (markEvaluating s a) a (.ok v)) := by
  apply Ev.of_eq
  rcases v with ⟨v, n⟩
  cases v <;> first
    | (exact absurd rfl (hv _))
    | (simp [NeedDemand.step, hcell, hstate, hsusp, NeedDemand.suspendedValue, KatLang.evalAttempt, markCompleted, markEvaluating, EvalM.bind_runState]; rfl)

/-- A suspended cell holding a written expression that is no call plan: its VALUE is `ev`'s,
    re-counted at the value boundary. -/
theorem demand_expression (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (demand : Nat → EvalM CountedResult) (a : Nat) (s t : EvalState) (cell : NeedCell) (e : Expr)
    (ctx : EvalCtx) (env : ValEnv) (r : CountedResult)
    (hcell : s.needs[a]? = some cell) (hstate : cell.state = .suspended)
    (hsusp : cell.suspension = .expression e ctx env) (hshape : NeedPlan.callShape? e ctx env = none)
    (hev : Ev (ev e ctx env) (markEvaluating s a) (.ok r) t) :
    Ev (NeedDemand.step ev route demand a) s (.ok (reCountValueBoundary r))
      (markCompleted t a (.ok (reCountValueBoundary r))) := by
  have hv : Ev (NeedDemand.suspendedValue ev route demand a cell.suspension) (markEvaluating s a)
      (.ok (reCountValueBoundary r)) t := by
    rw [hsusp]
    simp only [NeedDemand.suspendedValue, hshape]
    exact Ev.map hev
  unfold NeedDemand.step
  refine Ev.bind (Ev.of_eq rfl : Ev (get : EvalM EvalState) s (.ok s) s) ?_
  simp only [hcell, hstate]
  refine Ev.bind (Ev.of_eq rfl : Ev (modify _ : EvalM PUnit) s (.ok PUnit.unit) (markEvaluating s a)) ?_
  refine Ev.bind (Ev.evalAttempt hv) ?_
  refine Ev.bind (Ev.of_eq rfl : Ev (modify _ : EvalM PUnit) t (.ok PUnit.unit)
    (markCompleted t a (.ok (reCountValueBoundary r)))) ?_
  exact Ev.pure _ _


/-- A suspended deferred application: its VALUE is the route's dispatch, re-counted. -/
theorem demand_applied (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (demand : Nat → EvalM CountedResult) (a : Nat) (s t : EvalState) (cell : NeedCell) (callee : Algorithm)
    (cells : List NeedSupply.Sourced) (caller : EvalCtx) (values : ValEnv) (name : String) (r : CountedResult)
    (hcell : s.needs[a]? = some cell) (hstate : cell.state = .suspended)
    (hsusp : cell.suspension = .applied callee cells caller values name)
    (hd : Ev (route.dispatch .none callee cells caller values name) (markEvaluating s a) (.ok r) t) :
    Ev (NeedDemand.step ev route demand a) s (.ok (reCountValueBoundary r))
      (markCompleted t a (.ok (reCountValueBoundary r))) := by
  have hv : Ev (NeedDemand.suspendedValue ev route demand a cell.suspension) (markEvaluating s a)
      (.ok (reCountValueBoundary r)) t := by
    rw [hsusp]
    simp only [NeedDemand.suspendedValue]
    exact Ev.map (Ev.withNested hd)
  unfold NeedDemand.step
  refine Ev.bind (Ev.of_eq rfl : Ev (get : EvalM EvalState) s (.ok s) s) ?_
  simp only [hcell, hstate]
  refine Ev.bind (Ev.of_eq rfl : Ev (modify _ : EvalM PUnit) s (.ok PUnit.unit) (markEvaluating s a)) ?_
  refine Ev.bind (Ev.evalAttempt hv) ?_
  refine Ev.bind (Ev.of_eq rfl : Ev (modify _ : EvalM PUnit) t (.ok PUnit.unit)
    (markCompleted t a (.ok (reCountValueBoundary r)))) ?_
  exact Ev.pure _ _

/-! ## 5. The production VALUE demand at every fuel -/

theorem demandRec_ready (a : Nat) (s : EvalState) (cell : NeedCell) (v : CountedResult)
    (hcell : s.needs[a]? = some cell) (hsusp : cell.suspension = .ready v) (hstate : cell.state = .suspended)
    (hv : ∀ c, v.fst ≠ .deferred c) :
    EvF (.demandNeedRecursive a) s (.ok v) (markCompleted (markEvaluating s a) a (.ok v)) :=
  EvF.of_body fun _ => demand_ready _ _ _ a s cell v hcell hsusp hstate hv

theorem demandRec_expression (a : Nat) (s t : EvalState) (cell : NeedCell) (e : Expr) (ctx : EvalCtx)
    (env : ValEnv) (r : CountedResult) (hcell : s.needs[a]? = some cell) (hstate : cell.state = .suspended)
    (hsusp : cell.suspension = .expression e ctx env) (hshape : NeedPlan.callShape? e ctx env = none)
    (hev : EvF (.evalSuppliedAt a e ctx env) (markEvaluating s a) (.ok r) t) :
    EvF (.demandNeedRecursive a) s (.ok (reCountValueBoundary r))
      (markCompleted t a (.ok (reCountValueBoundary r))) :=
  EvF.of_body fun j => demand_expression _ _ _ a s t cell e ctx env r hcell hstate hsusp hshape (hev.ev j)

theorem demandRec_applied (a : Nat) (s t : EvalState) (cell : NeedCell) (callee : Algorithm)
    (cells : List NeedSupply.Sourced) (caller : EvalCtx) (values : ValEnv) (name : String) (r : CountedResult)
    (hcell : s.needs[a]? = some cell) (hstate : cell.state = .suspended)
    (hsusp : cell.suspension = .applied callee cells caller values name)
    (hd : EvF (.evalSuppliedCallCounted .none callee cells caller values name) (markEvaluating s a) (.ok r) t) :
    EvF (.demandNeedRecursive a) s (.ok (reCountValueBoundary r))
      (markCompleted t a (.ok (reCountValueBoundary r))) :=
  EvF.of_body fun j => demand_applied _ _ _ a s t cell callee cells caller values name r hcell hstate hsusp (hd.ev j)

/-! ## 6. The list literal `[x]` -/

theorem listLiteral_run (stk : List Algorithm) (X B A : Nat) (s : EvalState) :
    EvF (.evalListLiteralCounted [.param "x"] (fCtx stk X B A) []) s (.ok (.listValue [.deferred X], 1)) s :=
  EvF.of_body fun j => listLiteral_body j stk X B A s

theorem evalCounted_listLiteral (els : List Expr) (ctx : EvalCtx) (env : ValEnv) (s t : EvalState)
    (r : CountedResult) (h : EvF (.evalListLiteralCounted els ctx env) s (.ok r) t) :
    EvF (.evalCounted (.listLiteral els) ctx env) s (.ok r) t :=
  EvF.of_body fun j => Ev.withNested (h.ev j)

theorem evalSuppliedAt_plain (a : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) (s t : EvalState)
    (r : CountedResult) (hlink : linkEdge? e = none) (h : EvF (.evalCounted e ctx env) s (.ok r) t) :
    EvF (.evalSuppliedAt a e ctx env) s (.ok r) t :=
  EvF.of_body fun j => by
    show Ev (EvalBody.evalSuppliedAt (evalFuel j) a e ctx env) s (.ok r) t
    unfold EvalBody.evalSuppliedAt
    rw [hlink]
    exact h.ev j


theorem Ev.evalAttempt_error {α : Type} {m : EvalM α} {s t : EvalState} {e : Error}
    (h : Ev m s (.error e) t) (he : e ≠ .fuelExhausted) :
    Ev (KatLang.evalAttempt m) s (.ok (.error e)) t := by
  unfold Ev at *
  have key : (KatLang.evalAttempt m).runState s = (match m.runState s with
      | (result, nextState) =>
        if result.isIncomplete then ((.error .fuelExhausted : Except Error (Except Error α)), nextState)
        else (.ok result, nextState)) := rfl
  rw [key]
  rcases h with h | h
  · left
    revert h
    rcases m.runState s with ⟨o, u⟩
    intro h
    simp only at h
    subst h
    rfl
  · right
    rw [h]
    cases e <;> first | exact absurd rfl he | rfl

/-! ## 7. Resolution inside `F` -/

/-- The prelude as the owner of its bindings. -/
def preludeOwner : Algorithm := .mk none [] [] preludeScope.props [] none
def mapProp : PropDef := publicProp "map" (.builtin .mapBuiltin)
def mapResolved : ResolvedProperty := { owner := preludeOwner, binding := mapProp, alg := .builtin .mapBuiltin }

theorem resolveAlg_listLiteral (els : List Expr) (ctx : EvalCtx) (s : EvalState) :
    EvF (.resolveAlg (.listLiteral els) ctx) s (.error (.notAnAlgorithm "list literal")) s :=
  EvF.of_body fun _ => Ev.of_eq rfl

theorem resolveDotReceiver_listLiteral (els : List Expr) (ctx : EvalCtx) (s : EvalState) :
    EvF (.resolveDotReceiver? (.listLiteral els) ctx) s (.ok none) s :=
  EvF.of_body fun j => by
    show Ev (EvalBody.resolveDotReceiver? (evalFuel j) (.listLiteral els) ctx) s _ s
    unfold EvalBody.resolveDotReceiver?
    exact Ev.bind (Ev.evalAttempt_error ((resolveAlg_listLiteral els ctx s).ev j) nofun) (Ev.pure _ _)

theorem lookupStructural_map :
    lookupInParentsStructuralProperty progScope "map" =
      some { owner := preludeOwner, binding := mapProp, alg := .builtin .mapBuiltin } := rfl

theorem lookupRaw_map (ctx : EvalCtx) : lookupLexicalPropertyRaw FW "map" ctx = pure mapResolved := by
  unfold lookupLexicalPropertyRaw
  rw [show Algorithm.lookupPropDefAny? FW "map" = none from rfl, show Algorithm.parent FW = some progScope from rfl,
    ]
  dsimp only
  rw [lookupStructural_map]
  rfl

theorem lookup_map (stk : List Algorithm) (X B A : Nat) (s : EvalState) :
    EvF (.lookupLexicalProperty FW "map" (fCtx stk X B A)) s (.ok mapResolved) s :=
  EvF.of_body fun j => by
    show Ev (EvalBody.lookupLexicalProperty (evalFuel j) FW "map" (fCtx stk X B A)) s _ s
    unfold EvalBody.lookupLexicalProperty
    rw [lookupLexicalPropertyNoted_unmarked _ _ _ rfl, lookupRaw_map]
    exact Ev.of_eq rfl


theorem resolveAlg_map (stk : List Algorithm) (X B A : Nat) (s : EvalState) :
    EvF (.resolveAlg (.resolve "map") (fCtx stk X B A)) s (.ok (.builtin .mapBuiltin)) s :=
  EvF.of_body fun j => by
    show Ev (EvalBody.resolveAlg (evalFuel j) (.resolve "map") (fCtx stk X B A)) s _ s
    exact Ev.bind ((lookup_map stk X B A s).ev j) (Ev.pure _ _)

/-! ## 8. The `map` builtin over `[x]` -/

def mapMetadata : SequenceBuiltinMetadata := { suffixArgs := [{ name := "mapper" }] }
def emptyAlg : Algorithm := Algorithm.ofExpr (.emptySequence 0)
def litX : Expr := .listLiteral [.param "x"]
def resolveF : Expr := .resolve "F"
/-- A supplied argument cell with its written source. -/
def suppliedArg (a : Nat) (src : Option Expr) : ResolvedArgumentAlgorithm :=
  { algorithm := emptyAlg, need? := some a, source? := src }
def itemOf (a : Nat) (src : Option Expr) : CallableCallItem :=
  { algorithm? := some emptyAlg, source? := src, need? := some a }

theorem demandItem (a : Nat) (src : Option Expr) (ctx : EvalCtx) (env : ValEnv) (s t : EvalState)
    (v : CountedResult) (h : EvF (.demandNeedRecursive a) s (.ok v) t) :
    EvF (.demandSequenceBuiltinCallItemValue (itemOf a src) ctx env) s
      (.ok { itemOf a src with value? := some v.fst }) t :=
  EvF.of_body fun j => by
    show Ev (EvalBody.demandSequenceBuiltinCallItemValue (evalFuel j) (itemOf a src) ctx env) s _ t
    unfold EvalBody.demandSequenceBuiltinCallItemValue
    simp only [itemOf, Option.isSome_none, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    exact Ev.bind (Ev.evalAttempt (h.ev j)) (Ev.pure _ _)

theorem bindMap (L M : Nat) (ctx : EvalCtx) (env : ValEnv) (s t : EvalState) (v : Result)
    (h : EvF (.demandNeedRecursive L) s (.ok (v, 1)) t) (hv : v = .listValue [.deferred X]) :
    EvF (.bindSequenceBuiltinArguments .mapBuiltin mapMetadata [suppliedArg L (some litX), suppliedArg M (some resolveF)] ctx env)
      s (.ok { preparedInput := { items := [.deferred X] }, iterationItems := [(.deferred X, 1)],
               suffixArgs := [.needAlgorithm M] }) t :=
  EvF.of_body fun j => by
    show Ev (EvalBody.bindSequenceBuiltinArguments (evalFuel j) .mapBuiltin mapMetadata _ ctx env) s _ t
    unfold EvalBody.bindSequenceBuiltinArguments
    simp only [collectSequenceCallableCallItems, suppliedArg, mapMetadata, List.map, List.length_cons,
      List.length_nil, Builtin.readsRetainedCollector]
    simp only [show ((0 + 1 + 1 : Nat) != 1 + (0 + 1)) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine Ev.bind ((demandItem L (some litX) ctx env s t (v, 1) h).ev j) ?_
    subst hv
    apply Ev.of_eq
    simp [pendingStageCandidates?, collectionPositions, Builtin.readsPositions, discoveredPositions,
      Result.projectionItems, prepareSequenceBuiltinInput, applySequenceBuiltinEmptyPolicy,
      EvalBody.bindSequenceBuiltinArguments.prepareControls, prepareSequenceBuiltinSuffixArgItem]


/-- The state after one allocation. -/
def pushCell (s : EvalState) (sus : NeedSuspension) : EvalState :=
  { s with needs := s.needs.push { suspension := sus } }

/-- The mapped position `F(x)` of `[x].map(F)`. -/
def mappedSusp (X M : Nat) (ctx : EvalCtx) : NeedSuspension :=
  .applied (.builtin .mappedBuiltin) [(X, none), (M, none)] ctx [] "map transform"

theorem applyMapSequence (L M X : Nat) (ctx : EvalCtx) (s t : EvalState)
    (h : EvF (.bindSequenceBuiltinArguments .mapBuiltin mapMetadata [suppliedArg L (some litX), suppliedArg M (some resolveF)] ctx [])
      s (.ok { preparedInput := { items := [.deferred X] }, iterationItems := [(.deferred X, 1)],
               suffixArgs := [.needAlgorithm M] }) t) :
    EvF (.applyBuiltinCountedSequence .mapBuiltin mapMetadata [suppliedArg L (some litX), suppliedArg M (some resolveF)] ctx [])
      s (.ok (.listValue [.deferred t.needs.size], 1)) (pushCell t (mappedSusp X M ctx)) :=
  EvF.of_body fun j => by
    show Ev (EvalBody.applyBuiltinCountedSequence (evalFuel j) .mapBuiltin mapMetadata _ ctx []) s _ _
    unfold EvalBody.applyBuiltinCountedSequence
    refine Ev.bind (h.ev j) ?_
    apply Ev.of_eq
    simp [LazyList.mapItems, LazyList.itemCell, LazyList.mappedCell, allocateNeed, pushCell, mappedSusp, List.mapM, List.mapM.loop,
      EvalM.bind_runState]

theorem applyMap (L M : Nat) (ctx : EvalCtx) (s t : EvalState) (r : CountedResult)
    (h : EvF (.applyBuiltinCountedSequence .mapBuiltin mapMetadata [suppliedArg L (some litX), suppliedArg M (some resolveF)] ctx [])
      s (.ok r) t) :
    EvF (.applyBuiltinCounted .mapBuiltin [suppliedArg L (some litX), suppliedArg M (some resolveF)] ctx [])
      s (.ok r) t :=
  EvF.of_body fun j => by
    show Ev (EvalBody.applyBuiltinCounted (evalFuel j) .mapBuiltin _ ctx []) s _ _
    unfold EvalBody.applyBuiltinCounted
    exact Ev.withNested (h.ev j)

theorem suppliedMap (L M : Nat) (ctx : EvalCtx) (s t : EvalState) (r : CountedResult)
    (h : EvF (.applyBuiltinCounted .mapBuiltin [suppliedArg L (some litX), suppliedArg M (some resolveF)] ctx [])
      s (.ok r) t) :
    EvF (.evalSuppliedCallCounted .none (.builtin .mapBuiltin) [(L, some litX), (M, some resolveF)] ctx [] "map")
      s (.ok r) t :=
  EvF.of_body fun j => by
    show Ev (EvalBody.evalSuppliedCallCounted (evalFuel j) .none (.builtin .mapBuiltin) _ ctx [] "map") s _ _
    unfold EvalBody.evalSuppliedCallCounted
    exact h.ev j

theorem formMap (spread : NeedSupply.SpreadEval) (ctx : EvalCtx) (s : EvalState) :
    (NeedSupply.form spread ctx [] [litX, resolveF]).runState s =
      (.ok [(s.needs.size, some litX), (s.needs.size + 1, some resolveF)],
        pushCell (pushCell s (.expression litX ctx [])) (.expression resolveF ctx [])) := by
  simp [NeedSupply.form, NeedSupply.slot, supplyNeed, litX, resolveF, allocateNeed, pushCell, EvalM.bind_runState]


/-- The supply of `map([x], F)` in front of a state. -/
def mapSupplied (ctx : EvalCtx) (s : EvalState) : EvalState :=
  pushCell (pushCell s (.expression litX ctx [])) (.expression resolveF ctx [])

theorem resolvedMap (ctx : EvalCtx) (s t : EvalState) (r : CountedResult)
    (h : EvF (.evalSuppliedCallCounted .none (.builtin .mapBuiltin)
      [(s.needs.size, some litX), (s.needs.size + 1, some resolveF)] ctx [] "map") (mapSupplied ctx s) (.ok r) t) :
    EvF (.evalResolvedCallCounted (.builtin .mapBuiltin) [litX, resolveF] ctx [] "map" .none) s (.ok r) t :=
  EvF.of_body fun j => by
    show Ev (EvalBody.evalResolvedCallCounted (evalFuel j) (.builtin .mapBuiltin) _ ctx [] "map" .none) s _ _
    unfold EvalBody.evalResolvedCallCounted
    exact Ev.bind (Ev.of_eq (formMap _ ctx s)) (h.ev j)

theorem lexicalMap (stk : List Algorithm) (X B A : Nat) (s t : EvalState) (r : CountedResult)
    (h : EvF (.evalResolvedCallCounted (.builtin .mapBuiltin) [litX, resolveF] (fCtx stk X B A) [] "map" .none)
      s (.ok r) t) :
    EvF (.callLexicalWithReceiverCounted "map" litX (.resolve "map") (some [resolveF]) (fCtx stk X B A) [])
      s (.ok r) t :=
  EvF.of_body fun j => by
    show Ev (EvalBody.callLexicalWithReceiverCounted (evalFuel j) "map" litX (.resolve "map") _ _ []) s _ _
    unfold EvalBody.callLexicalWithReceiverCounted
    exact Ev.bind ((resolveAlg_map stk X B A s).ev j) (h.ev j)

theorem dotMap (stk : List Algorithm) (X B A : Nat) (s t : EvalState) (r : CountedResult)
    (h : EvF (.callLexicalWithReceiverCounted "map" litX (.resolve "map") (some [resolveF]) (fCtx stk X B A) [])
      s (.ok r) t) :
    EvF (.evalDotCallCounted litX "map" (.resolve "map") (some [resolveF]) (fCtx stk X B A) []) s (.ok r) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalDotCallCounted litX "map" (.resolve "map") (some [resolveF]) (fCtx stk X B A) []) =
      EvalBody.evalDotCallCounted (evalFuel j) litX "map" (.resolve "map") (some [resolveF]) (fCtx stk X B A) [] := rfl
    rw [e]
    unfold EvalBody.evalDotCallCounted
    refine Ev.bind ((resolveDotReceiver_listLiteral [.param "x"] (fCtx stk X B A) s).ev j) ?_
    simp only [selectDotEdge, DotMiss.ofName]
    exact h.ev j

theorem countedBody (stk : List Algorithm) (X B A : Nat) (s t : EvalState) (r : CountedResult)
    (h : EvF (.evalDotCallCounted litX "map" (.resolve "map") (some [resolveF]) (fCtx stk X B A) []) s (.ok r) t) :
    EvF (.evalCounted fBody (fCtx stk X B A) []) s (.ok r) t :=
  EvF.of_body fun j => by
    show Ev (EvalBody.evalCounted (evalFuel j) fBody _ []) s _ _
    unfold EvalBody.evalCounted
    exact Ev.withCtx (h.ev j)

theorem rowsBody (ctx : EvalCtx) (s t : EvalState) (v : Result)
    (h : EvF (.evalCounted fBody ctx []) s (.ok (v, 1)) t) :
    EvF (.evalOutputRowsPreparedCore [fBody] ctx []) s (.ok { counted := (v, 1), outputSlots := [v] }) t :=
  EvF.of_body fun j => by
    show Ev (EvalBody.evalOutputRowsPreparedCore (evalFuel j) [fBody] ctx []) s _ _
    unfold EvalBody.evalOutputRowsPreparedCore
    rw [EvalBody.evalOutputRowsPreparedCore.collect.eq_2]
    refine Ev.bind (Ev.withNested (h.ev j)) ?_
    simp only [fBody]
    rw [EvalBody.evalOutputRowsPreparedCore.collect.eq_1]
    exact Ev.pure _ _


/-! ## 9. Entering `F` -/

/-- The activation an `F` call records for `x` at cell `X` in binding context `b`. -/
def fActivation (X b : Nat) : ParameterActivation :=
  { values := [], needs := [("x", X)], bindingContext := b, ownsInvocation := true }

def recordAct (s : EvalState) (X b : Nat) : EvalState :=
  { s with lexicalActivations := s.lexicalActivations.push (fActivation X b) }

/-- The context a binding boundary hands to `F`'s body. -/
def entryCtx (ctxC : EvalCtx) (X b : Nat) : EvalCtx :=
  { ctxC with bindingContext := b, needEnv := [("x", X)], enteringInvocation := true }

theorem enterF (ctxC : EvalCtx) (X b : Nat) (s : EvalState)
    (hd : ctxC.detachedBefore = 0) (ho : ctxC.outerDetached = []) (hi : ctxC.inputRecord = none) :
    (enterAlgorithmBody FW (entryCtx ctxC X b) []).runState s =
      (.ok (fCtx ctxC.callStack X b s.lexicalActivations.size), recordAct s X b) := by
  rcases ctxC with ⟨cs, ne, bc, hs, db, od, ei, ir⟩
  simp only at hd ho hi
  subst hd ho hi
  simp [enterAlgorithmBody, entryCtx, recordParameterActivation, recordAct, fActivation, EvalM.bind_runState]
  rfl

theorem preparedF (ctxC : EvalCtx) (X b : Nat) (s t : EvalState) (out : PreparedAlgorithmOutput)
    (hd : ctxC.detachedBefore = 0) (ho : ctxC.outerDetached = []) (hi : ctxC.inputRecord = none)
    (h : EvF (.evalOutputRowsPreparedCore [fBody] (fCtx ctxC.callStack X b s.lexicalActivations.size) [])
      (recordAct s X b) (.ok out) t) :
    EvF (.evalAlgOutputPreparedCore FW (entryCtx ctxC X b) []) s (.ok out) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalAlgOutputPreparedCore FW (entryCtx ctxC X b) []) =
      EvalBody.evalAlgOutputPreparedCore (evalFuel j) FW (entryCtx ctxC X b) [] := rfl
    rw [e]
    have hbody : EvalBody.evalAlgOutputPreparedCore (evalFuel j) FW (entryCtx ctxC X b) [] =
        (do let pushedCtx ← enterAlgorithmBody FW (entryCtx ctxC X b) []
            (evalFuel j).evalOutputRowsPreparedCore [fBody] pushedCtx []) := rfl
    rw [hbody]
    exact Ev.bind (Ev.of_eq (enterF ctxC X b s hd ho hi)) (h.ev j)


theorem countedF (ctxE : EvalCtx) (s t : EvalState) (out : PreparedAlgorithmOutput)
    (h : EvF (.evalAlgOutputPreparedCore FW ctxE []) s (.ok out) t) :
    EvF (.evalAlgOutputCountedCore FW ctxE []) s (.ok out.counted) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalAlgOutputCountedCore FW ctxE []) =
      EvalBody.evalAlgOutputCountedCore (evalFuel j) FW ctxE [] := rfl
    rw [e]
    exact Ev.bind (h.ev j) (Ev.pure _ _)

theorem bindX (ch : NeedChannels) (X : Nat) (s : EvalState) :
    (bindNeedPatterns ch [NeedPattern.ofParameter xPattern] [X]).runState s = (.ok (some [("x", X)]), s) := by
  simp [bindNeedPatterns, NeedBinder.bindPatterns, NeedBinder.bindLevel, NeedBinder.cardinalityGate,
    NeedBinder.bindSources, NeedBinder.sourceAddress, NeedBinder.bindOne, NeedBinder.bindName,
    NeedPattern.ofParameter, xPattern, needRepeatedNames, needLevelSources, needAcceptsCardinality,
    NeedBindState.withPlain, NeedEnv.rebind, needMinimumSuppliedSlots, needSourceAt, NeedPattern.isCollecting,
    NeedPattern.names]

def bumpBC (s : EvalState) : EvalState := { s with nextBindingContext := s.nextBindingContext + 1 }

theorem needBC (ctxC : EvalCtx) (X : Nat) (s : EvalState)
    (hne : ctxC.needEnv.filter (fun entry => !(["x"] : List Ident).contains entry.fst) = []) :
    (needBindingContext ctxC [("x", X)]).runState s =
      (.ok { ctxC with bindingContext := s.nextBindingContext, needEnv := [("x", X)] }, bumpBC s) := by
  simp only [needBindingContext, EvalCtx.bindParameters, EvalM.bind_runState, get_run, set_run, pure_run, List.map]
  rw [hne]
  rfl

theorem userSupplyF (ctxC : EvalCtx) (X : Nat) (s t : EvalState) (r : CountedResult)
    (hne : ctxC.needEnv.filter (fun entry => !(["x"] : List Ident).contains entry.fst) = [])
    (h : EvF (.evalAlgOutputCountedCore FW (entryCtx ctxC X s.nextBindingContext) []) (bumpBC s) (.ok r) t) :
    EvF (.evalNeedUserSupply FW [X] ctxC []) s (.ok (reCountValueBoundary r)) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalNeedUserSupply FW [X] ctxC []) =
      EvalBody.evalNeedUserSupply (evalFuel j) FW [X] ctxC [] := rfl
    rw [e]
    have hbody : EvalBody.evalNeedUserSupply (evalFuel j) FW [X] ctxC [] = (do
        let result <- (do
          let some bindings <- withNestedMissingOutput
              (bindNeedPatterns (evalFuel j).bindingChannels [NeedPattern.ofParameter xPattern] [X])
            | throw Error.badArity
          let next <- needBindingContext ctxC bindings
          (evalFuel j).evalAlgOutputCounted FW { next with enteringInvocation := true } [])
        pure (reCountValueBoundary result)) := rfl
    rw [hbody]
    refine Ev.bind ?_ (Ev.pure _ _)
    refine Ev.bind (Ev.withNested (Ev.of_eq (bindX _ X s))) ?_
    dsimp only
    refine Ev.bind (Ev.of_eq (needBC ctxC X s hne)) ?_
    exact h.ev j


/-! ## 10. One call of `F` -/

/-- The body context of the `F` call made from `ctxC` in state `s` with `x` at cell `X`. -/
def callCtx (ctxC : EvalCtx) (X : Nat) (s : EvalState) : EvalCtx :=
  fCtx ctxC.callStack X s.nextBindingContext s.lexicalActivations.size

/-- The state after `map([x], F)` formed its supply inside that call. -/
def callSupplied (ctxC : EvalCtx) (X : Nat) (s : EvalState) : EvalState :=
  mapSupplied (callCtx ctxC X s) (recordAct (bumpBC s) X s.nextBindingContext)

/-- The state after the call: the receiver cell `[x]` completed, the mapped position allocated. -/
def callState (ctxC : EvalCtx) (X : Nat) (s : EvalState) : EvalState :=
  pushCell (markCompleted (markEvaluating (callSupplied ctxC X s) s.needs.size) s.needs.size
      (.ok (.listValue [.deferred X], 1)))
    (mappedSusp X (s.needs.size + 1) (callCtx ctxC X s))

@[local simp] theorem pushCell_size (s : EvalState) (sus : NeedSuspension) :
    (pushCell s sus).needs.size = s.needs.size + 1 := by simp [pushCell]
@[local simp] theorem markEvaluating_size (s : EvalState) (a : Nat) :
    (markEvaluating s a).needs.size = s.needs.size := by simp [markEvaluating]
@[local simp] theorem markCompleted_size (s : EvalState) (a : Nat) (o : Except Error CountedResult) :
    (markCompleted s a o).needs.size = s.needs.size := by simp [markCompleted]
@[local simp] theorem recordAct_needs (s : EvalState) (X b : Nat) : (recordAct s X b).needs = s.needs := rfl
@[local simp] theorem bumpBC_needs (s : EvalState) : (bumpBC s).needs = s.needs := rfl

theorem callSupplied_size (ctxC : EvalCtx) (X : Nat) (s : EvalState) :
    (callSupplied ctxC X s).needs.size = s.needs.size + 2 := by
  simp [callSupplied, mapSupplied]

theorem callSupplied_receiver (ctxC : EvalCtx) (X : Nat) (s : EvalState) :
    (callSupplied ctxC X s).needs[s.needs.size]? = some { suspension := .expression litX (callCtx ctxC X s) [] } := by
  simp [callSupplied, mapSupplied, pushCell, Array.getElem?_push]

/-- The caller's need environment is empty or contains only bindings named `x`. The call of
    `F` binds `x` to the supplied cell `X`.
    With the caller's detachment fields empty and no input record, each completed approximation
    returns `[deferred (N + 2)]`, where `N` is the incoming heap size. The call allocates the
    receiver `[x]` at `N` and the mapper `F` at `N + 1`, completes the receiver with its one
    item `X`, and allocates the mapped position at `N + 2`. It records one activation and one
    binding context. -/
theorem fCall (ctxC : EvalCtx) (X : Nat) (s : EvalState)
    (hne : ctxC.needEnv.filter (fun entry => !(["x"] : List Ident).contains entry.fst) = [])
    (hd : ctxC.detachedBefore = 0) (ho : ctxC.outerDetached = []) (hi : ctxC.inputRecord = none) :
    EvF (.evalNeedUserSupply FW [X] ctxC []) s (.ok (.listValue [.deferred (s.needs.size + 2)], 1))
      (callState ctxC X s) := by
  have hL : EvF (.demandNeedRecursive s.needs.size) (callSupplied ctxC X s)
      (.ok (.listValue [.deferred X], 1))
      (markCompleted (markEvaluating (callSupplied ctxC X s) s.needs.size) s.needs.size
        (.ok (.listValue [.deferred X], 1))) := by
    have := demandRec_expression s.needs.size (callSupplied ctxC X s)
      (markEvaluating (callSupplied ctxC X s) s.needs.size) _ litX (callCtx ctxC X s) []
      (.listValue [.deferred X], 1) (callSupplied_receiver ctxC X s) rfl rfl
      (by simp [NeedPlan.callShape?, litX])
      (evalSuppliedAt_plain _ _ _ _ _ _ _ (by simp [linkEdge?, litX])
        (evalCounted_listLiteral _ _ _ _ _ _ (listLiteral_run _ _ _ _ _)))
    exact this
  have hsize : (markCompleted (markEvaluating (callSupplied ctxC X s) s.needs.size) s.needs.size
      (.ok (.listValue [.deferred X], 1))).needs.size = s.needs.size + 2 := by
    simp [callSupplied_size]
  have hmap := applyMapSequence s.needs.size (s.needs.size + 1) X (callCtx ctxC X s) _ _
    (bindMap (X := X) s.needs.size (s.needs.size + 1) (callCtx ctxC X s) [] _ _ _ hL rfl)
  rw [hsize] at hmap
  have := userSupplyF ctxC X s (callState ctxC X s) _ hne
    (countedF _ _ _ _ (preparedF ctxC X s.nextBindingContext (bumpBC s) _ _ hd ho hi
      (rowsBody _ _ _ _ (countedBody _ _ _ _ _ _ _
        (dotMap _ _ _ _ _ _ _ (lexicalMap _ _ _ _ _ _ _ (resolvedMap _ _ _ _
          (suppliedMap _ _ _ _ _ _ (applyMap _ _ _ _ _ _ hmap)))))))))
  exact this


/-! ## 11. The mapper `F`: its CALLABLE projection -/

theorem lookupStructural_F :
    lookupInParentsStructuralProperty progScope "F" = some { owner := progW, binding := fProp, alg := FW } := rfl

theorem lookupRaw_F (ctx : EvalCtx) :
    lookupLexicalPropertyRaw FW "F" ctx = pure { owner := progW, binding := fProp, alg := FW } := by
  unfold lookupLexicalPropertyRaw
  rw [show Algorithm.lookupPropDefAny? FW "F" = none from rfl, show Algorithm.parent FW = some progScope from rfl]
  dsimp only
  rw [lookupStructural_F]

theorem projectWritten_F (stk : List Algorithm) (X B A : Nat) (s : EvalState) :
    EvF (.projectNeedWritten resolveF (fCtx stk X B A)) s (.ok (some FW)) s :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.projectNeedWritten resolveF (fCtx stk X B A)) =
      EvalBody.projectNeedWritten (evalFuel j) resolveF (fCtx stk X B A) := rfl
    rw [e]
    unfold EvalBody.projectNeedWritten
    simp only [resolveF, fCtx]
    rw [lookupLexicalPropertyNoted_unmarked _ _ _ rfl, lookupRaw_F]
    refine Ev.bind (Ev.evalAttempt (Ev.pure _ s)) ?_
    exact Ev.pure _ _

theorem projectWrittenAt_F (a : Nat) (stk : List Algorithm) (X B A : Nat) (s : EvalState) :
    EvF (.projectNeedWrittenAt a resolveF (fCtx stk X B A)) s (.ok (some FW)) s :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.projectNeedWrittenAt a resolveF (fCtx stk X B A)) =
      EvalBody.projectNeedWrittenAt (evalFuel j) a resolveF (fCtx stk X B A) := rfl
    rw [e]
    unfold EvalBody.projectNeedWrittenAt
    simp only [resolveF, linkEdge?]
    exact (projectWritten_F stk X B A s).ev j

def markProjecting (s : EvalState) (a : Nat) : EvalState :=
  { s with needs := s.needs.modify a (fun c => { c with callable := .projecting }) }

def markProjected (s : EvalState) (a : Nat) (o : Except Error (Option Algorithm)) : EvalState :=
  { s with needs := s.needs.modify a (fun c => { c with callable := .projected o }) }

theorem project_expression (written : Expr → EvalCtx → EvalM (Option Algorithm)) (a : Nat) (s t : EvalState)
    (cell : NeedCell) (src : Expr) (caller : EvalCtx) (values : ValEnv) (r : Option Algorithm)
    (hcell : s.needs[a]? = some cell) (hc : cell.callable = .unprojected)
    (hs : cell.suspension = .expression src caller values) (hwrap : shouldWrapArgExprAsValue src = false)
    (hw : Ev (written src caller) (markProjecting s a) (.ok r) t) :
    Ev (NeedProjection.step (NeedProjection.suspended written) a) s (.ok r) (markProjected t a (.ok r)) := by
  have hv : Ev (NeedProjection.suspended written cell.suspension) (markProjecting s a) (.ok r) t := by
    rw [hs]
    simp only [NeedProjection.suspended, hwrap, Bool.false_eq_true, ↓reduceIte]
    exact hw
  unfold NeedProjection.step
  refine Ev.bind (Ev.of_eq rfl : Ev (get : EvalM EvalState) s (.ok s) s) ?_
  simp only [hcell, hc]
  refine Ev.bind (Ev.of_eq rfl : Ev (modify _ : EvalM PUnit) s (.ok PUnit.unit) (markProjecting s a)) ?_
  refine Ev.bind (Ev.evalAttempt hv) ?_
  refine Ev.bind (Ev.of_eq rfl : Ev (modify _ : EvalM PUnit) t (.ok PUnit.unit) (markProjected t a (.ok r))) ?_
  exact Ev.pure _ _

theorem projectMapper (a : Nat) (stk : List Algorithm) (X B A : Nat) (s : EvalState) (cell : NeedCell)
    (hcell : s.needs[a]? = some cell) (hc : cell.callable = .unprojected)
    (hs : cell.suspension = .expression resolveF (fCtx stk X B A) []) :
    EvF (.projectNeedCallable a) s (.ok (some FW)) (markProjected (markProjecting s a) a (.ok (some FW))) :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.projectNeedCallable a) = EvalBody.projectNeedCallable (evalFuel j) a := rfl
    rw [e]
    exact project_expression _ a s _ cell resolveF (fCtx stk X B A) [] (some FW) hcell hc hs rfl
      ((projectWrittenAt_F a stk X B A _).ev j)

theorem mapperSlot (a : Nat) (s t : EvalState) (h : EvF (.projectNeedCallable a) s (.ok (some FW)) t) :
    EvF (.expectPreparedSequenceBuiltinAlgorithmSuffixArg .mapBuiltin [{ name := "mapper" }]
      [.needAlgorithm a] 0) s (.ok FW) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.expectPreparedSequenceBuiltinAlgorithmSuffixArg .mapBuiltin [{ name := "mapper" }]
        [.needAlgorithm a] 0) = EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg (evalFuel j) .mapBuiltin
        [{ name := "mapper" }] [.needAlgorithm a] 0 := rfl
    rw [e]
    unfold EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg expectPreparedSequenceBuiltinSuffixArgAt
    simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.drop_zero]
    refine Ev.bind (h.ev j) ?_
    exact Ev.pure _ _


/-! ## 12. One `map` position `F(x)`: the deferred step -/

theorem evalCounted_num (n : Int) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    EvF (.evalCounted (.num n) ctx env) s (.ok (.atom n, 1)) s :=
  EvF.of_body fun _ => Ev.of_eq rfl

theorem argValue (a : Nat) (src : Option Expr) (ctx : EvalCtx) (env : ValEnv) (s t : EvalState) (r : CountedResult)
    (h : EvF (.demandNeedRecursive a) s (.ok r) t) :
    EvF (.evalArgumentValueCounted (suppliedArg a src) ctx env) s (.ok r) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalArgumentValueCounted (suppliedArg a src) ctx env) =
      EvalBody.evalArgumentValueCounted (evalFuel j) (suppliedArg a src) ctx env := rfl
    rw [e]
    unfold EvalBody.evalArgumentValueCounted
    simp only [suppliedArg]
    exact h.ev j

theorem callbackUser (ctxF : EvalCtx) (s t : EvalState) (r : CountedResult)
    (h : EvF (.evalNeedUserSupply FW [s.needs.size] ctxF []) (pushCell s (.ready (.atom 1, 1))) (.ok r) t) :
    EvF (.evalUserCallbackCallCounted FW [(.atom 1, 1)] ctxF []) s (.ok r) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalUserCallbackCallCounted FW [(.atom 1, 1)] ctxF []) =
      EvalBody.evalUserCallbackCallCounted (evalFuel j) FW [(.atom 1, 1)] ctxF [] := rfl
    rw [e]
    unfold EvalBody.evalUserCallbackCallCounted
    refine Ev.bind (Ev.of_eq (by simp [List.mapM, List.mapM.loop, readyNeed, allocateNeed, pushCell, EvalM.bind_runState])) (h.ev j)

theorem callbackResolved (ctxF : EvalCtx) (s t : EvalState) (r : CountedResult)
    (h : EvF (.evalUserCallbackCallCounted FW [(.atom 1, 1)] ctxF []) s (.ok r) t) :
    EvF (.evalResolvedCallbackCallCounted FW [(.atom 1, 1)] ctxF [] "map transform") s (.ok r) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalResolvedCallbackCallCounted FW [(.atom 1, 1)] ctxF [] "map transform") =
      (evalFuel j) (.evalUserCallbackCallCounted FW [(.atom 1, 1)] ctxF []) := rfl
    rw [e]
    exact h.ev j

theorem mapCounted (ctxF : EvalCtx) (s t : EvalState) (v : Result)
    (h : EvF (.evalResolvedCallbackCallCounted FW [(.atom 1, 1)] ctxF [] "map transform") s (.ok (v, 1)) t) :
    EvF (.evalMapCounted [(.atom 1, 1)] FW ctxF []) s (.ok (.listValue [v], 1)) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalMapCounted [(.atom 1, 1)] FW ctxF []) =
      EvalBody.evalMapCounted (evalFuel j) [(.atom 1, 1)] FW ctxF [] := rfl
    rw [e]
    unfold EvalBody.evalMapCounted
    simp only [EvalBody.evalMapCounted.mapLoop]
    refine Ev.bind (Ev.bind (Ev.withCtx (h.ev j)) (Ev.bind (Ev.pure [] t) (Ev.pure _ t))) ?_
    exact Ev.pure _ _

theorem applyMapped (X Mp : Nat) (ctxF : EvalCtx) (s u w t : EvalState) (v : Result)
    (hX : EvF (.evalArgumentValueCounted (suppliedArg X none) ctxF []) s (.ok (.atom 1, 1)) u)
    (hMp : EvF (.expectPreparedSequenceBuiltinAlgorithmSuffixArg .mapBuiltin [{ name := "mapper" }]
      [.needAlgorithm Mp] 0) u (.ok FW) w)
    (hmap : EvF (.evalMapCounted [(.atom 1, 1)] FW ctxF []) w (.ok (.listValue [v], 1)) t) :
    EvF (.applyBuiltinCounted .mappedBuiltin [suppliedArg X none, suppliedArg Mp none] ctxF []) s
      (.ok (v, Result.valueCount v)) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.applyBuiltinCounted .mappedBuiltin [suppliedArg X none, suppliedArg Mp none] ctxF []) =
      withNestedMissingOutput (do
        let value <- (evalFuel j).evalArgumentValueCounted (suppliedArg X none) ctxF []
        let transformAlg <- (evalFuel j).expectPreparedSequenceBuiltinAlgorithmSuffixArg .mapBuiltin
          [{ name := "mapper" }] [.needAlgorithm Mp] 0
        match (<- (evalFuel j).evalMapCounted [value] transformAlg ctxF []).fst with
        | .listValue [mapped] => pure (mapped, Result.valueCount mapped)
        | _ => .error (Error.illegalInEval "a map step produces exactly one element")) := rfl
    rw [e]
    exact Ev.withNested (Ev.bind (hX.ev j) (Ev.bind (hMp.ev j) (Ev.bind (hmap.ev j) (Ev.pure _ _))))

theorem suppliedMapped (X Mp : Nat) (ctxF : EvalCtx) (s t : EvalState) (r : CountedResult)
    (h : EvF (.applyBuiltinCounted .mappedBuiltin [suppliedArg X none, suppliedArg Mp none] ctxF []) s (.ok r) t) :
    EvF (.evalSuppliedCallCounted .none (.builtin .mappedBuiltin) [(X, none), (Mp, none)] ctxF [] "map transform")
      s (.ok r) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalSuppliedCallCounted .none (.builtin .mappedBuiltin) [(X, none), (Mp, none)] ctxF []
        "map transform") = (evalFuel j) (.applyBuiltinCounted .mappedBuiltin [suppliedArg X none, suppliedArg Mp none] ctxF []) := rfl
    rw [e]
    exact h.ev j


/-- The item cell of a stage holds the number `1`: a Ready `1` (every callback argument), or the
    written `1` of the root call `F(1)`. -/
def ItemOne (cell : NeedCell) : Prop :=
  cell.state = .suspended ∧
    (cell.suspension = .ready (.atom 1, 1) ∨ ∃ ctx, cell.suspension = .expression (.num 1) ctx [])

theorem demandX (X : Nat) (s : EvalState) (cell : NeedCell) (hX : s.needs[X]? = some cell) (h1 : ItemOne cell) :
    EvF (.demandNeedRecursive X) s (.ok (.atom 1, 1)) (markCompleted (markEvaluating s X) X (.ok (.atom 1, 1))) := by
  obtain ⟨hst, hready | ⟨ctx, hexpr⟩⟩ := h1
  · exact demandRec_ready X s cell _ hX hready hst nofun
  · exact demandRec_expression X s (markEvaluating s X) cell (.num 1) ctx [] (.atom 1, 1) hX hst hexpr
      (by simp [NeedPlan.callShape?])
      (evalSuppliedAt_plain _ _ _ _ _ _ _ (by simp [linkEdge?]) (evalCounted_num 1 ctx [] _))

theorem getElem?_markEvaluating (s : EvalState) (a b : Nat) (h : a ≠ b) :
    (markEvaluating s a).needs[b]? = s.needs[b]? := by
  simp [markEvaluating, Array.getElem?_modify, h]
theorem getElem?_markCompleted (s : EvalState) (a b : Nat) (o : Except Error CountedResult) (h : a ≠ b) :
    (markCompleted s a o).needs[b]? = s.needs[b]? := by
  simp [markCompleted, Array.getElem?_modify, h]
@[local simp] theorem markProjecting_size (s : EvalState) (a : Nat) : (markProjecting s a).needs.size = s.needs.size := by
  simp [markProjecting]
@[local simp] theorem markProjected_size (s : EvalState) (a : Nat) (o : Except Error (Option Algorithm)) :
    (markProjected s a o).needs.size = s.needs.size := by simp [markProjected]

/-- The state after the item and the mapper of a position at `c` were read. -/
def positionRead (s : EvalState) (c X Mp : Nat) : EvalState :=
  markProjected (markProjecting (markCompleted (markEvaluating (markEvaluating s c) X) X (.ok (.atom 1, 1))) Mp) Mp
    (.ok (some FW))

/-- The state after the position at `c` completed: its `F` call made in the stage's context. -/
def positionState (s : EvalState) (c X Mp : Nat) (stk : List Algorithm) (B A : Nat) : EvalState :=
  markCompleted (callState (fCtx stk X B A) s.needs.size (pushCell (positionRead s c X Mp) (.ready (.atom 1, 1)))) c
    (.ok (.listValue [.deferred (s.needs.size + 3)], 1))

/-- **ONE MAPPED POSITION.** The VALUE demand of a suspended position `F(x)` of a stage built in an `F`
    body: it reads the item `1`, projects the mapper `F` and calls it (`fCall`, after the callback's
    Ready `1` at `N`), so its value is the fresh list `[deferred (N + 3)]`. -/
theorem demandPosition (c X Mp : Nat) (stk : List Algorithm) (B A : Nat) (s : EvalState)
    (cellC cellX cellMp : NeedCell)
    (hc : s.needs[c]? = some cellC) (hcS : cellC.state = .suspended)
    (hcSusp : cellC.suspension = mappedSusp X Mp (fCtx stk X B A))
    (hX : s.needs[X]? = some cellX) (h1 : ItemOne cellX)
    (hMp : s.needs[Mp]? = some cellMp) (hMpC : cellMp.callable = .unprojected)
    (hMpSusp : cellMp.suspension = .expression resolveF (fCtx stk X B A) [])
    (hcX : c ≠ X) (hcMp : c ≠ Mp) (hXMp : X ≠ Mp) :
    EvF (.demandNeedRecursive c) s (.ok (.listValue [.deferred (s.needs.size + 3)], 1))
      (positionState s c X Mp stk B A) := by
  have hX1 : (markEvaluating s c).needs[X]? = some cellX := by rw [getElem?_markEvaluating _ _ _ hcX, hX]
  have hdX := demandX X (markEvaluating s c) cellX hX1 h1
  have hMp1 : (markCompleted (markEvaluating (markEvaluating s c) X) X (.ok (.atom 1, 1))).needs[Mp]? = some cellMp := by
    rw [getElem?_markCompleted _ _ _ _ hXMp, getElem?_markEvaluating _ _ _ hXMp, getElem?_markEvaluating _ _ _ hcMp, hMp]
  have hpMp := projectMapper Mp stk X B A _ cellMp hMp1 hMpC hMpSusp
  have hsize : (positionRead s c X Mp).needs.size = s.needs.size := by simp [positionRead]
  have hcall := fCall (fCtx stk X B A) (positionRead s c X Mp).needs.size
    (pushCell (positionRead s c X Mp) (.ready (.atom 1, 1))) rfl rfl rfl rfl
  simp only [pushCell_size, hsize] at hcall
  have := demandRec_applied c s _ cellC (.builtin .mappedBuiltin) [(X, none), (Mp, none)] (fCtx stk X B A) []
    "map transform" _ hc hcS hcSusp
    (suppliedMapped X Mp _ _ _ _ (applyMapped X Mp _ _ _ _ _ _ (argValue X none _ _ _ _ _ hdX)
      (mapperSlot Mp _ _ hpMp)
      (mapCounted _ _ _ _ (callbackResolved _ _ _ _ (callbackUser _ _ _ _ hcall)))))
  exact this


/-! ## 13. Incompleteness and its propagation -/

/-- `m` from `s` is incomplete. -/
def Inc {α : Type} (m : EvalM α) (s : EvalState) : Prop := (m.runState s).1 = .error .fuelExhausted

theorem Inc.bind_left {α β : Type} {m : EvalM α} {f : α → EvalM β} {s : EvalState} (h : Inc m s) :
    Inc (m >>= f) s := by
  unfold Inc at *
  rw [EvalM.bind_runState]
  revert h
  rcases m.runState s with ⟨o, u⟩
  intro h
  simp only at h
  subst h
  rfl

theorem Inc.bind {α β : Type} {m : EvalM α} {f : α → EvalM β} {s u : EvalState} {a : α}
    (hm : Ev m s (.ok a) u) (hf : Inc (f a) u) : Inc (m >>= f) s := by
  rcases hm with hm | hm
  · exact Inc.bind_left hm
  · unfold Inc at *
    rw [EvalM.bind_runState, hm]
    exact hf

theorem Inc.evalAttempt {α : Type} {m : EvalM α} {s : EvalState} (h : Inc m s) : Inc (KatLang.evalAttempt m) s := by
  unfold Inc at *
  have key : (KatLang.evalAttempt m).runState s = (match m.runState s with
      | (result, nextState) =>
        if result.isIncomplete then ((.error .fuelExhausted : Except Error (Except Error α)), nextState)
        else (.ok result, nextState)) := rfl
  rw [key]
  revert h
  rcases m.runState s with ⟨o, u⟩
  intro h
  simp only at h
  subst h
  rfl

theorem Inc.withNested {α : Type} {m : EvalM α} {s : EvalState} (h : Inc m s) :
    Inc (withNestedMissingOutput m) s := by
  unfold withNestedMissingOutput
  exact Inc.bind_left (Inc.evalAttempt h)

theorem Inc.map {α β : Type} {f : α → β} {m : EvalM α} {s : EvalState} (h : Inc m s) : Inc (f <$> m) s := by
  show Inc (m >>= fun x => (Pure.pure (f x) : EvalM β)) s
  exact Inc.bind_left h

/-- A suspended deferred application whose dispatch is incomplete. -/
theorem demand_applied_inc (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (demand : Nat → EvalM CountedResult) (a : Nat) (s : EvalState) (cell : NeedCell) (callee : Algorithm)
    (cells : List NeedSupply.Sourced) (caller : EvalCtx) (values : ValEnv) (name : String)
    (hcell : s.needs[a]? = some cell) (hstate : cell.state = .suspended)
    (hsusp : cell.suspension = .applied callee cells caller values name)
    (hd : Inc (route.dispatch .none callee cells caller values name) (markEvaluating s a)) :
    Inc (NeedDemand.step ev route demand a) s := by
  have hv : Inc (NeedDemand.suspendedValue ev route demand a cell.suspension) (markEvaluating s a) := by
    rw [hsusp]
    simp only [NeedDemand.suspendedValue]
    exact Inc.map (Inc.withNested hd)
  unfold NeedDemand.step
  refine Inc.bind (Ev.of_eq rfl : Ev (get : EvalM EvalState) s (.ok s) s) ?_
  simp only [hcell, hstate]
  refine Inc.bind (Ev.of_eq rfl : Ev (modify _ : EvalM PUnit) s (.ok PUnit.unit) (markEvaluating s a)) ?_
  exact Inc.bind_left (Inc.evalAttempt hv)


/-! ## 14. One materialization generation -/

/-- A materialization path as its Ready cell holds it. -/
def pathValue (path : List Nat) : Result := .listValue (path.map (fun cell => Result.atom (Int.ofNat cell)))

/-- The deferred application that materializes the value in cell `S` on the path in cell `P`. -/
def matSusp (S P : Nat) : NeedSuspension :=
  .applied (.builtin .materializedBuiltin) [(S, none), (P, none)] EvalCtx.empty [] "materialized value"

theorem materializationPath_pathValue (path : List Nat) : materializationPath (pathValue path) = path := by
  unfold pathValue materializationPath
  induction path with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, List.filterMap_cons]
    exact congrArg (p :: ·) ih

/-- The three allocations of `materializeVia` over a lazy value `v` on the path `path`. -/
def matAlloc (t : EvalState) (v : Result) (path : List Nat) : EvalState :=
  pushCell (pushCell (pushCell t (.ready (v, Result.valueCount v))) (.ready (pathValue path, 1)))
    (matSusp t.needs.size (t.needs.size + 1))

theorem materializeVia_lazy_run (demand : Nat → EvalM CountedResult) (v : Result) (path : List Nat)
    (t : EvalState) (hlazy : v.isLazy = true) :
    (materializeVia demand v path).runState t =
      (Prod.fst <$> demand (t.needs.size + 2)).runState (matAlloc t v path) := by
  unfold materializeVia
  simp [hlazy, readyNeed, allocateNeed, EvalM.bind_runState, matAlloc, pushCell, matSusp, pathValue]

theorem materializeVia_inc (demand : Nat → EvalM CountedResult) (v : Result) (path : List Nat) (t : EvalState)
    (hlazy : v.isLazy = true) (h : Inc (demand (t.needs.size + 2)) (matAlloc t v path)) :
    Inc (materializeVia demand v path) t := by
  unfold Inc
  rw [materializeVia_lazy_run demand v path t hlazy]
  exact Inc.map h


theorem materializePosition_fresh' (demand : Nat → EvalM CountedResult) (visiting : List Nat) (cell : Nat)
    (h : cell ∉ visiting) :
    materializePosition demand visiting (.deferred cell) =
      (do materializeVia demand (← forcePosition demand (.deferred cell)) (cell :: visiting)) := by
  simp [materializePosition, h]

/-- The materialized builtin over the source cell `S` (one deferred position `c`) and the path
    cell `P`: it reads the path, then the source, then the position, and materializes the
    position's value; incomplete when that last demand is. -/
theorem materialize_inc (k : Nat) (S P c : Nat) (path : List Nat) (s t : EvalState) (cellS cellP : NeedCell)
    (v : Result)
    (hP : s.needs[P]? = some cellP) (hPst : cellP.state = .suspended)
    (hPs : cellP.suspension = .ready (pathValue path, 1))
    (hS : s.needs[S]? = some cellS) (hSst : cellS.state = .suspended)
    (hSs : cellS.suspension = .ready (.listValue [.deferred c], 1)) (hSP : S ≠ P)
    (hfresh : c ∉ path)
    (hpos : EvF (.demandNeedRecursive c)
      (markCompleted (markEvaluating (markCompleted (markEvaluating s P) P (.ok (pathValue path, 1))) S) S
        (.ok (.listValue [.deferred c], 1))) (.ok (v, 1)) t)
    (hlazy : v.isLazy = true)
    (hnext : Inc (evalFuel k (.demandNeedRecursive (t.needs.size + 2))) (matAlloc t v (c :: path))) :
    Inc (evalStep (evalFuel k) (.applyBuiltinCounted .materializedBuiltin [suppliedArg S none, suppliedArg P none]
      EvalCtx.empty [])) s := by
  have e : evalStep (evalFuel k) (.applyBuiltinCounted .materializedBuiltin [suppliedArg S none, suppliedArg P none]
      EvalCtx.empty []) =
    withNestedMissingOutput (do
      let visiting := materializationPath (← (evalFuel k).evalArgumentValue (suppliedArg P none) EvalCtx.empty [])
      let position := materializePosition (evalFuel k).demandNeedRecursive visiting
      match ← (evalFuel k).evalArgumentValue (suppliedArg S none) EvalCtx.empty [] with
      | .listValue items => do
          pure (Result.listValue (← items.mapM position), 1)
      | .pendingList candidates => do
          let concrete <- LazyList.discover (evalFuel k).demandNeedRecursive
            (fun cell => position (.deferred cell)) none candidates
          pure (Result.listValue concrete, 1)
      | .sequenceValue items => do
          let concrete := Result.sequenceValue (<- items.mapM position)
          pure (concrete, Result.valueCount concrete)
      | value => pure (value, Result.valueCount value)) := rfl
  rw [e]
  refine Inc.withNested ?_
  have hdP := demandRec_ready P s cellP _ hP hPs hPst nofun
  refine Inc.bind (Ev.bind ((argValue P none EvalCtx.empty [] _ _ _ hdP).ev k) (Ev.pure _ _)) ?_
  have hS1 : (markCompleted (markEvaluating s P) P (.ok (pathValue path, 1))).needs[S]? = some cellS := by
    rw [getElem?_markCompleted _ _ _ _ (Ne.symm hSP), getElem?_markEvaluating _ _ _ (Ne.symm hSP), hS]
  have hdS := demandRec_ready S _ cellS _ hS1 hSs hSst nofun
  refine Inc.bind (Ev.bind ((argValue S none EvalCtx.empty [] _ _ _ hdS).ev k) (Ev.pure _ _)) ?_
  simp only [materializationPath_pathValue]
  refine Inc.bind_left ?_
  simp only [List.mapM, List.mapM.loop]
  refine Inc.bind_left ?_
  rw [materializePosition_fresh' _ _ _ hfresh]
  refine Inc.bind (Ev.withNested (Ev.map (hpos.ev k))) ?_
  exact materializeVia_inc _ v (c :: path) t hlazy hnext


theorem inc_succ {c : EvalCall} {s : EvalState} {k : Nat} (h : Inc (evalStep (evalFuel k) c) s) :
    Inc (evalFuel (k + 1) c) s := by
  unfold Inc
  rw [evalFuel_succ, normalize_of_incomplete _ s h]

/-- The VALUE demand of a materialization cell at every fuel, from its builtin's body at the fuel
    three levels below. -/
theorem spine_inc (f M S P : Nat) (s : EvalState) (cell : NeedCell)
    (hM : s.needs[M]? = some cell) (hst : cell.state = .suspended) (hsusp : cell.suspension = matSusp S P)
    (hbody : ∀ k, f = k + 3 → Inc (evalStep (evalFuel k) (.applyBuiltinCounted .materializedBuiltin
      [suppliedArg S none, suppliedArg P none] EvalCtx.empty [])) (markEvaluating s M)) :
    Inc (evalFuel f (.demandNeedRecursive M)) s := by
  have hdisp : ∀ j, Inc (evalFuel j (.evalSuppliedCallCounted .none (.builtin .materializedBuiltin)
      [(S, none), (P, none)] EvalCtx.empty [] "materialized value")) (markEvaluating s M) →
      Inc (evalStep (evalFuel j) (.demandNeedRecursive M)) s := fun j hj =>
    demand_applied_inc _ _ _ M s cell _ _ _ _ _ hM hst hsusp hj
  have happ : ∀ j, Inc (evalFuel j (.applyBuiltinCounted .materializedBuiltin [suppliedArg S none, suppliedArg P none]
      EvalCtx.empty [])) (markEvaluating s M) →
      Inc (evalStep (evalFuel j) (.evalSuppliedCallCounted .none (.builtin .materializedBuiltin)
        [(S, none), (P, none)] EvalCtx.empty [] "materialized value")) (markEvaluating s M) := fun j hj => hj
  rcases f with _ | _ | _ | k
  · rfl
  · exact inc_succ (hdisp 0 rfl)
  · exact inc_succ (hdisp 1 (inc_succ (happ 0 rfl)))
  · exact inc_succ (hdisp (k + 2) (inc_succ (happ (k + 1) (inc_succ (hbody k rfl)))))

/-! ## 15. The generation invariant -/

/-- At the start of a generation the heap has `N + 7` cells. The item, mapped position,
    materialization source, path and materialization cell are suspended. The mapper's callable
    projection is unprojected in the captured context. Every earlier position on the path is
    below `N`, outside this generation's block. -/
structure Gen (s : EvalState) (N : Nat) (stk : List Algorithm) (B A : Nat) (path : List Nat) : Prop where
  size : s.needs.size = N + 7
  item : ∃ cell, s.needs[N]? = some cell ∧ ItemOne cell
  mapper : ∃ cell, s.needs[N + 2]? = some cell ∧ cell.callable = .unprojected ∧
    cell.suspension = .expression resolveF (fCtx stk N B A) []
  position : ∃ cell, s.needs[N + 3]? = some cell ∧ cell.state = .suspended ∧
    cell.suspension = mappedSusp N (N + 2) (fCtx stk N B A)
  source : ∃ cell, s.needs[N + 4]? = some cell ∧ cell.state = .suspended ∧
    cell.suspension = .ready (.listValue [.deferred (N + 3)], 1)
  pathCell : ∃ cell, s.needs[N + 5]? = some cell ∧ cell.state = .suspended ∧
    cell.suspension = .ready (pathValue path, 1)
  mat : ∃ cell, s.needs[N + 6]? = some cell ∧ cell.state = .suspended ∧ cell.suspension = matSusp (N + 4) (N + 5)
  fresh : ∀ p ∈ path, p < N


/-- The state in which the generation at `N` demands the next materialization cell `N + 13`. -/
def nextState (s : EvalState) (N : Nat) (stk : List Algorithm) (B A : Nat) (path : List Nat) : EvalState :=
  let s2 := markCompleted (markEvaluating (markCompleted (markEvaluating (markEvaluating s (N + 6)) (N + 5)) (N + 5)
    (.ok (pathValue path, 1))) (N + 4)) (N + 4) (.ok (.listValue [.deferred (N + 3)], 1))
  matAlloc (positionState s2 (N + 3) N (N + 2) stk B A) (.listValue [.deferred (N + 10)]) ((N + 3) :: path)

@[local simp] theorem pushCell_needs (s : EvalState) (sus : NeedSuspension) :
    (pushCell s sus).needs = s.needs.push { suspension := sus } := rfl
@[local simp] theorem markEvaluating_needs (s : EvalState) (a : Nat) :
    (markEvaluating s a).needs = s.needs.modify a (fun c => { c with state := .evaluating }) := rfl
@[local simp] theorem markCompleted_needs (s : EvalState) (a : Nat) (o : Except Error CountedResult) :
    (markCompleted s a o).needs = s.needs.modify a (fun c => { c with state := .completed o }) := rfl
@[local simp] theorem markProjecting_needs (s : EvalState) (a : Nat) :
    (markProjecting s a).needs = s.needs.modify a (fun c => { c with callable := .projecting }) := rfl
@[local simp] theorem markProjected_needs (s : EvalState) (a : Nat) (o : Except Error (Option Algorithm)) :
    (markProjected s a o).needs = s.needs.modify a (fun c => { c with callable := .projected o }) := rfl


@[local simp] theorem pushCell_nbc (s : EvalState) (sus : NeedSuspension) :
    (pushCell s sus).nextBindingContext = s.nextBindingContext := rfl
@[local simp] theorem pushCell_acts (s : EvalState) (sus : NeedSuspension) :
    (pushCell s sus).lexicalActivations = s.lexicalActivations := rfl
@[local simp] theorem markEvaluating_nbc (s : EvalState) (a : Nat) :
    (markEvaluating s a).nextBindingContext = s.nextBindingContext := rfl
@[local simp] theorem markEvaluating_acts (s : EvalState) (a : Nat) :
    (markEvaluating s a).lexicalActivations = s.lexicalActivations := rfl
@[local simp] theorem markCompleted_nbc (s : EvalState) (a : Nat) (o : Except Error CountedResult) :
    (markCompleted s a o).nextBindingContext = s.nextBindingContext := rfl
@[local simp] theorem markCompleted_acts (s : EvalState) (a : Nat) (o : Except Error CountedResult) :
    (markCompleted s a o).lexicalActivations = s.lexicalActivations := rfl
@[local simp] theorem markProjecting_nbc (s : EvalState) (a : Nat) :
    (markProjecting s a).nextBindingContext = s.nextBindingContext := rfl
@[local simp] theorem markProjecting_acts (s : EvalState) (a : Nat) :
    (markProjecting s a).lexicalActivations = s.lexicalActivations := rfl
@[local simp] theorem markProjected_nbc (s : EvalState) (a : Nat) (o : Except Error (Option Algorithm)) :
    (markProjected s a o).nextBindingContext = s.nextBindingContext := rfl
@[local simp] theorem markProjected_acts (s : EvalState) (a : Nat) (o : Except Error (Option Algorithm)) :
    (markProjected s a o).lexicalActivations = s.lexicalActivations := rfl

/-! Cells of the states a generation builds. -/

theorem matAlloc_size (t : EvalState) (v : Result) (p : List Nat) :
    (matAlloc t v p).needs.size = t.needs.size + 3 := by simp [matAlloc]
/-- Reads cells through the state constructors: the cell lookups first, the arithmetic after. -/
local macro "cells" : tactic => `(tactic| (
  simp only [pushCell_needs, markEvaluating_needs, markCompleted_needs, markProjecting_needs, markProjected_needs,
    recordAct_needs, bumpBC_needs, Array.getElem?_push, Array.getElem?_modify, Array.size_push, Array.size_modify]
  try simp
  all_goals (try (intro h; omega))))

theorem matAlloc_source (t : EvalState) (v : Result) (p : List Nat) :
    (matAlloc t v p).needs[t.needs.size]? = some { suspension := .ready (v, Result.valueCount v) } := by
  simp only [matAlloc]; cells
theorem matAlloc_path (t : EvalState) (v : Result) (p : List Nat) :
    (matAlloc t v p).needs[t.needs.size + 1]? = some { suspension := .ready (pathValue p, 1) } := by
  simp only [matAlloc]; cells
theorem matAlloc_mat (t : EvalState) (v : Result) (p : List Nat) :
    (matAlloc t v p).needs[t.needs.size + 2]? = some { suspension := matSusp t.needs.size (t.needs.size + 1) } := by
  simp only [matAlloc]; cells
theorem matAlloc_old (t : EvalState) (v : Result) (p : List Nat) (i : Nat) (h : i < t.needs.size) :
    (matAlloc t v p).needs[i]? = t.needs[i]? := by
  simp only [matAlloc]; cells
  simp [show i ≠ t.needs.size by omega, show i ≠ t.needs.size + 1 by omega, show i ≠ t.needs.size + 1 + 1 by omega]

theorem callState_size (ctxC : EvalCtx) (X : Nat) (s : EvalState) :
    (callState ctxC X s).needs.size = s.needs.size + 3 := by
  simp [callState, callSupplied, mapSupplied]
theorem callState_mapper (ctxC : EvalCtx) (X : Nat) (s : EvalState) :
    (callState ctxC X s).needs[s.needs.size + 1]? =
      some { suspension := .expression resolveF (callCtx ctxC X s) [] } := by
  simp only [callState, callSupplied, mapSupplied]; cells
theorem callState_position (ctxC : EvalCtx) (X : Nat) (s : EvalState) :
    (callState ctxC X s).needs[s.needs.size + 2]? =
      some { suspension := mappedSusp X (s.needs.size + 1) (callCtx ctxC X s) } := by
  simp only [callState, callSupplied, mapSupplied]; cells
theorem callState_old (ctxC : EvalCtx) (X : Nat) (s : EvalState) (i : Nat) (h : i < s.needs.size) :
    (callState ctxC X s).needs[i]? = s.needs[i]? := by
  simp only [callState, callSupplied, mapSupplied]; cells
  simp [show i ≠ s.needs.size by omega, show i ≠ s.needs.size + 1 by omega, show i ≠ s.needs.size + 1 + 1 by omega,
    show s.needs.size ≠ i by omega]

theorem positionRead_size (s : EvalState) (c X Mp : Nat) : (positionRead s c X Mp).needs.size = s.needs.size := by
  simp [positionRead]
@[local simp] theorem positionRead_nbc (s : EvalState) (c X Mp : Nat) :
    (positionRead s c X Mp).nextBindingContext = s.nextBindingContext := rfl
@[local simp] theorem positionRead_acts (s : EvalState) (c X Mp : Nat) :
    (positionRead s c X Mp).lexicalActivations = s.lexicalActivations := rfl

/-- The context of the `F` call a position at a stage over `stk` makes. -/
theorem position_callCtx (s : EvalState) (c X Mp : Nat) (stk : List Algorithm) (B A : Nat) :
    callCtx (fCtx stk X B A) s.needs.size (pushCell (positionRead s c X Mp) (.ready (.atom 1, 1))) =
      fCtx (FW :: stk) s.needs.size s.nextBindingContext s.lexicalActivations.size := by
  simp only [callCtx, pushCell_nbc, pushCell_acts, positionRead_nbc, positionRead_acts]
  rfl

theorem positionState_size (s : EvalState) (c X Mp : Nat) (stk : List Algorithm) (B A : Nat) :
    (positionState s c X Mp stk B A).needs.size = s.needs.size + 4 := by
  simp [positionState, callState_size, positionRead_size]

theorem positionState_cell (s : EvalState) (c X Mp : Nat) (stk : List Algorithm) (B A : Nat) (i : Nat)
    (hc : c < s.needs.size) (hi : s.needs.size ≤ i) :
    (positionState s c X Mp stk B A).needs[i]? =
      (callState (fCtx stk X B A) s.needs.size (pushCell (positionRead s c X Mp) (.ready (.atom 1, 1)))).needs[i]? := by
  simp only [positionState, markCompleted_needs, Array.getElem?_modify]
  simp [show c ≠ i by omega]

theorem positionState_item (s : EvalState) (c X Mp : Nat) (stk : List Algorithm) (B A : Nat) (hc : c < s.needs.size) :
    (positionState s c X Mp stk B A).needs[s.needs.size]? = some { suspension := .ready (.atom 1, 1) } := by
  rw [positionState_cell _ _ _ _ _ _ _ _ hc (Nat.le_refl _), callState_old _ _ _ _ (by simp [positionRead_size])]
  simp only [pushCell_needs, Array.getElem?_push, positionRead_size, ite_true]

theorem positionState_mapper (s : EvalState) (c X Mp : Nat) (stk : List Algorithm) (B A : Nat) (hc : c < s.needs.size) :
    (positionState s c X Mp stk B A).needs[s.needs.size + 2]? =
      some { suspension := .expression resolveF (fCtx (FW :: stk) s.needs.size s.nextBindingContext
        s.lexicalActivations.size) [] } := by
  rw [positionState_cell _ _ _ _ _ _ _ _ hc (by omega)]
  have := callState_mapper (fCtx stk X B A) s.needs.size (pushCell (positionRead s c X Mp) (.ready (.atom 1, 1)))
  rw [pushCell_size, positionRead_size, position_callCtx] at this
  exact this

theorem positionState_position (s : EvalState) (c X Mp : Nat) (stk : List Algorithm) (B A : Nat)
    (hc : c < s.needs.size) :
    (positionState s c X Mp stk B A).needs[s.needs.size + 3]? =
      some { suspension := mappedSusp s.needs.size (s.needs.size + 2) (fCtx (FW :: stk) s.needs.size
        s.nextBindingContext s.lexicalActivations.size) } := by
  rw [positionState_cell _ _ _ _ _ _ _ _ hc (by omega)]
  have := callState_position (fCtx stk X B A) s.needs.size (pushCell (positionRead s c X Mp) (.ready (.atom 1, 1)))
  rw [pushCell_size, positionRead_size, position_callCtx] at this
  exact this


/-- The heap of a generation after its path, source and position reads, before the position's call. -/
def genReadState (s : EvalState) (N : Nat) (path : List Nat) : EvalState :=
  markCompleted (markEvaluating (markCompleted (markEvaluating (markEvaluating s (N + 6)) (N + 5)) (N + 5)
    (.ok (pathValue path, 1))) (N + 4)) (N + 4) (.ok (.listValue [.deferred (N + 3)], 1))

theorem nextState_eq (s : EvalState) (N : Nat) (stk : List Algorithm) (B A : Nat) (path : List Nat) :
    nextState s N stk B A path =
      matAlloc (positionState (genReadState s N path) (N + 3) N (N + 2) stk B A) (.listValue [.deferred (N + 10)])
        ((N + 3) :: path) := rfl

theorem genReadState_size (s : EvalState) (N : Nat) (path : List Nat) :
    (genReadState s N path).needs.size = s.needs.size := by simp [genReadState]
@[local simp] theorem genReadState_nbc (s : EvalState) (N : Nat) (path : List Nat) :
    (genReadState s N path).nextBindingContext = s.nextBindingContext := rfl
@[local simp] theorem genReadState_acts (s : EvalState) (N : Nat) (path : List Nat) :
    (genReadState s N path).lexicalActivations = s.lexicalActivations := rfl

/-- **THE INVARIANT IS KEPT.** The state in which a generation demands the next materialization cell
    satisfies `Gen` for the next block: seven fresh cells, `F` pushed onto the stack, the next binding
    context and activation, and the position just read added to the path. -/
theorem gen_next (s : EvalState) (N : Nat) (stk : List Algorithm) (B A : Nat) (path : List Nat)
    (hg : Gen s N stk B A path) :
    Gen (nextState s N stk B A path) (N + 7) (FW :: stk) s.nextBindingContext s.lexicalActivations.size
      ((N + 3) :: path) := by
  have hs2 : (genReadState s N path).needs.size = N + 7 := by rw [genReadState_size, hg.size]
  have hc : N + 3 < (genReadState s N path).needs.size := by omega
  have ht : (positionState (genReadState s N path) (N + 3) N (N + 2) stk B A).needs.size = N + 11 := by
    rw [positionState_size, hs2]
  rw [nextState_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [matAlloc_size, ht]
  · refine ⟨{ suspension := .ready (.atom 1, 1) }, ?_, rfl, .inl rfl⟩
    rw [matAlloc_old _ _ _ _ (by omega), ← hs2, positionState_item _ _ _ _ _ _ _ hc]
  · refine ⟨{ suspension := .expression resolveF (fCtx (FW :: stk) (N + 7) s.nextBindingContext s.lexicalActivations.size) [] }, ?_, rfl, rfl⟩
    rw [matAlloc_old _ _ _ _ (by omega), show N + 7 + 2 = (genReadState s N path).needs.size + 2 by omega,
      positionState_mapper _ _ _ _ _ _ _ hc, hs2]
    simp
  · refine ⟨{ suspension := mappedSusp (N + 7) (N + 7 + 2) (fCtx (FW :: stk) (N + 7) s.nextBindingContext s.lexicalActivations.size) }, ?_, rfl, rfl⟩
    rw [matAlloc_old _ _ _ _ (by omega), show N + 7 + 3 = (genReadState s N path).needs.size + 3 by omega,
      positionState_position _ _ _ _ _ _ _ hc, hs2]
    simp
  · refine ⟨{ suspension := .ready (.listValue [.deferred (N + 7 + 3)], 1) }, ?_, rfl, rfl⟩
    rw [show N + 7 + 4 = (positionState (genReadState s N path) (N + 3) N (N + 2) stk B A).needs.size by omega,
      matAlloc_source]
    rfl
  · refine ⟨{ suspension := .ready (pathValue ((N + 3) :: path), 1) }, ?_, rfl, rfl⟩
    rw [show N + 7 + 5 = (positionState (genReadState s N path) (N + 3) N (N + 2) stk B A).needs.size + 1 by omega,
      matAlloc_path]
  · refine ⟨{ suspension := matSusp (N + 7 + 4) (N + 7 + 5) }, ?_, rfl, rfl⟩
    rw [show N + 7 + 6 = (positionState (genReadState s N path) (N + 3) N (N + 2) stk B A).needs.size + 2 by omega,
      matAlloc_mat, ht]
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · omega
    · have := hg.fresh p hp; omega


/-! ## 16. Every generation is incomplete at every fuel -/

theorem genReadState_old (s : EvalState) (N : Nat) (path : List Nat) (i : Nat) (h : i < N + 4) :
    (genReadState s N path).needs[i]? = s.needs[i]? := by
  simp only [genReadState]
  rw [getElem?_markCompleted _ _ _ _ (by omega), getElem?_markEvaluating _ _ _ (by omega),
    getElem?_markCompleted _ _ _ _ (by omega), getElem?_markEvaluating _ _ _ (by omega),
    getElem?_markEvaluating _ _ _ (by omega)]

/-- **THE GENERATION STEP AT EVERY FUEL.** From a state satisfying `Gen`, the VALUE demand of the
    generation's materialization cell is incomplete, at every fuel. -/
theorem gen_incomplete : ∀ (f N : Nat) (stk : List Algorithm) (B A : Nat) (path : List Nat) (s : EvalState),
    Gen s N stk B A path → Inc (evalFuel f (.demandNeedRecursive (N + 6))) s := by
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
    intro N stk B A path s hg
    obtain ⟨cellM, hM, hMst, hMs⟩ := hg.mat
    refine spine_inc f (N + 6) (N + 4) (N + 5) s cellM hM hMst hMs ?_
    intro k hk
    obtain ⟨cellP, hP, hPst, hPs⟩ := hg.pathCell
    obtain ⟨cellS, hS, hSst, hSs⟩ := hg.source
    obtain ⟨cellX, hX, hX1⟩ := hg.item
    obtain ⟨cellMp, hMp, hMpC, hMpS⟩ := hg.mapper
    obtain ⟨cellC, hC, hCst, hCs⟩ := hg.position
    have hP' : (markEvaluating s (N + 6)).needs[N + 5]? = some cellP := by
      rw [getElem?_markEvaluating _ _ _ (by omega), hP]
    have hS' : (markEvaluating s (N + 6)).needs[N + 4]? = some cellS := by
      rw [getElem?_markEvaluating _ _ _ (by omega), hS]
    have hs2 : (genReadState s N path).needs.size = N + 7 := by rw [genReadState_size, hg.size]
    have hpos := demandPosition (N + 3) N (N + 2) stk B A (genReadState s N path) cellC cellX cellMp
      (by rw [genReadState_old _ _ _ _ (by omega), hC]) hCst hCs
      (by rw [genReadState_old _ _ _ _ (by omega), hX]) hX1
      (by rw [genReadState_old _ _ _ _ (by omega), hMp]) hMpC hMpS (by omega) (by omega) (by omega)
    rw [hs2] at hpos
    have ht : (positionState (genReadState s N path) (N + 3) N (N + 2) stk B A).needs.size = N + 11 := by
      rw [positionState_size, hs2]
    refine materialize_inc k (N + 4) (N + 5) (N + 3) path (markEvaluating s (N + 6)) _ cellS cellP
      (.listValue [.deferred (N + 10)]) hP' hPst hPs hS' hSst hSs (by omega)
      (fun hm => by have := hg.fresh (N + 3) hm; omega) hpos rfl ?_
    rw [ht]
    exact ih k (by omega) (N + 7) (FW :: stk) s.nextBindingContext s.lexicalActivations.size ((N + 3) :: path)
      (nextState s N stk B A path) (gen_next s N stk B A path hg)


/-! ## 17. The root: the program as `CoreTests/LazyCollections.lean` writes it -/

/-- `program` as `CoreTests/LazyCollections.lean` spells it: private properties, then output rows. -/
def program (props : List (String × Algorithm)) (rows : List Expr) : Expr := .algorithmExpr (algPrivate [] [] props rows)

/-- `F(x) = [x].map(F)` as `CoreTests/LazyCollections.lean` spells it. -/
def fAlg : Algorithm := alg ["x"] [] [] [.dotCall (.listLiteral [.param "x"]) "map" (some [.resolve "F"])]

/-- THE WITNESS: the program whose one output row is `F(1)`. -/
def witnessProgram : Expr := program [("F", fAlg)] [.call (.resolve "F") [.num 1]]

theorem id_fBody (n : Nat) : (identifyPropertyExpr fBody).run n = (fBody, n) := by
  simp only [fBody, identifyPropertyExpr, List.mapM, List.mapM.loop]
  rfl

theorem id_callF1 (n : Nat) : (identifyPropertyExpr callF1).run n = (callF1, n) := by
  simp only [callF1, identifyPropertyExpr, List.mapM, List.mapM.loop]
  rfl

theorem id_fAlg : (identifyPropertyAlgorithm fAlg).run 2 = (fDef, 3) := by
  rw [identifyPropertyAlgorithm]
  simp only [fAlg, alg, Algorithm.normalParameters, ParameterPattern.normalPatterns, Expr.dotCall]
  show (do
      let identity <- modifyGet (preparedAlgorithmIdentity none)
      return Algorithm.mk none [xPattern] (<- [].mapM identifyPropertyExpr) (<- [].mapM identifyPropertyDefinition)
        (<- [fBody].mapM identifyPropertyExpr) (some identity) : StateM Nat Algorithm).run 2 = _
  simp only [List.mapM, List.mapM.loop]
  simp [id_fBody, preparedAlgorithmIdentity, fDef]
  rfl

theorem id_fProp : (identifyPropertyDefinition (privateProp "F" fAlg)).run 1 = (fProp, 3) := by
  rw [identifyPropertyDefinition]
  simp [preparedPropertyIdentity, privateProp]
  rw [id_fAlg]
  rfl

theorem identified : (identifyPropertyExpr witnessProgram).run' 0 = .algorithmExpr progA := by
  simp only [witnessProgram, program, identifyPropertyExpr]
  rw [identifyPropertyAlgorithm]
  simp only [algPrivate, Algorithm.normalParameters, ParameterPattern.normalPatterns, propsPrivate, List.map,
    Algorithm.declarationId]
  simp only [List.mapM, List.mapM.loop]
  rw [show ((Expr.resolve "F").call [Expr.num 1]) = callF1 from rfl]
  simp [id_fProp, id_callF1, preparedAlgorithmIdentity]
  rfl

theorem preludeScope_def : preludeScope = .mk none [] [] preludeAlg.props [] [] none none := rfl

theorem wired_prog : wireToCaller { callStack := [preludeAlg] } progA = progW := by
  simp only [wireToCaller, List.head?, childOfInContext, scopeInContext, preludeScope, progA, progW]
  simp [activeDeclaration?, sameDeclaringScope, compatibleActivations, siteScope?, EvalCtx.head?, Algorithm.asScopeCtx,
    Algorithm.withParent, preludeAlg, Algorithm.parent, Algorithm.params, Algorithm.opens, Algorithm.props,
    Algorithm.output, Algorithm.branches, Algorithm.declarationId]

/-- The context of the program's rows. -/
def rootCtx : EvalCtx := { callStack := [progW, preludeAlg] }

theorem wired_F : childOfInContext progW fDef rootCtx = FW := by
  simp only [rootCtx, childOfInContext, scopeInContext, progW, FW, fDef, progScope]
  have hsame : sameDeclaringScope preludeScope preludeScope = true := by
    rw [preludeScope_def]; simp [sameDeclaringScope]
  have hcompat : compatibleActivations (some preludeScope) (some preludeScope) = true := by
    rw [preludeScope_def]; simp [compatibleActivations]
  simp [activeDeclaration?, sameDeclaringScope, compatibleActivations, siteScope?, EvalCtx.head?, Algorithm.asScopeCtx,
    Algorithm.withParent, Algorithm.parent, Algorithm.params, Algorithm.opens, Algorithm.props,
    Algorithm.output, Algorithm.branches, Algorithm.declarationId, hsame, hcompat, Algorithm.parameters,
    Algorithm.parameterPatterns, ScopeCtx.activation, show (PropertyIdentity.syntax 0 == PropertyIdentity.syntax 0) = true from rfl]


theorem lookupRaw_root :
    lookupLexicalPropertyRaw progW "F" rootCtx = pure { owner := progW, binding := fProp, alg := FW } := by
  unfold lookupLexicalPropertyRaw
  rw [show Algorithm.lookupPropDefAny? progW "F" = some fProp from rfl]
  dsimp only
  rw [show fProp.alg = fDef from rfl, wired_F]

theorem lookup_root (s : EvalState) :
    EvF (.lookupLexicalProperty progW "F" rootCtx) s (.ok { owner := progW, binding := fProp, alg := FW }) s :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.lookupLexicalProperty progW "F" rootCtx) =
      EvalBody.lookupLexicalProperty (evalFuel j) progW "F" rootCtx := rfl
    rw [e]
    unfold EvalBody.lookupLexicalProperty
    rw [lookupLexicalPropertyNoted_unmarked _ _ _ rfl, lookupRaw_root]
    exact Ev.of_eq rfl

theorem resolveAlg_root (s : EvalState) : EvF (.resolveAlg (.resolve "F") rootCtx) s (.ok FW) s :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.resolveAlg (.resolve "F") rootCtx) =
      ((evalFuel j) (.lookupLexicalProperty progW "F" rootCtx) >>= fun r => pure r.alg) := rfl
    rw [e]
    exact Ev.bind ((lookup_root s).ev j) (Ev.pure _ _)

theorem callee_root (s : EvalState) : EvF (.resolveCalleeAlg (.resolve "F") rootCtx) s (.ok FW) s :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.resolveCalleeAlg (.resolve "F") rootCtx) =
      (evalFuel j) (.resolveAlg (.resolve "F") rootCtx) := rfl
    rw [e]
    exact (resolveAlg_root s).ev j

theorem supplied_root (s t : EvalState) (r : CountedResult)
    (h : EvF (.evalNeedUserSupply FW [0] rootCtx []) s (.ok r) t) :
    EvF (.evalSuppliedCallCounted (.written (.resolve "F") rootCtx) FW [(0, some (.num 1))] rootCtx [] "F") s (.ok r) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalSuppliedCallCounted (.written (.resolve "F") rootCtx) FW [(0, some (.num 1))]
        rootCtx [] "F") = (evalFuel j) (.evalNeedUserSupply FW [0] rootCtx []) := rfl
    rw [e]
    exact h.ev j

theorem formRoot (spread : NeedSupply.SpreadEval) (s : EvalState) :
    (NeedSupply.form spread rootCtx [] [.num 1]).runState s =
      (.ok [(s.needs.size, some (.num 1))], pushCell s (.expression (.num 1) rootCtx [])) := by
  simp [NeedSupply.form, NeedSupply.slot, supplyNeed, allocateNeed, pushCell, EvalM.bind_runState]

theorem resolved_root (t : EvalState) (r : CountedResult)
    (h : EvF (.evalSuppliedCallCounted (.written (.resolve "F") rootCtx) FW [(0, some (.num 1))] rootCtx [] "F")
      (pushCell EvalState.empty (.expression (.num 1) rootCtx [])) (.ok r) t) :
    EvF (.evalResolvedCallCounted FW [.num 1] rootCtx [] "F" (.written (.resolve "F") rootCtx)) EvalState.empty
      (.ok r) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalResolvedCallCounted FW [.num 1] rootCtx [] "F" (.written (.resolve "F") rootCtx)) =
      (do let cells <- NeedSupply.form (evalFuel j).evalSupplySpread rootCtx [] [.num 1]
          (evalFuel j).evalSuppliedCallCounted (.written (.resolve "F") rootCtx) FW cells rootCtx [] "F") := rfl
    rw [e]
    exact Ev.bind (Ev.of_eq (formRoot _ EvalState.empty)) (h.ev j)

theorem callExpr_root (t : EvalState) (r : CountedResult)
    (h : EvF (.evalResolvedCallCounted FW [.num 1] rootCtx [] "F" (.written (.resolve "F") rootCtx)) EvalState.empty
      (.ok r) t) :
    EvF (.evalCallCountedExpr (.resolve "F") [.num 1] rootCtx []) EvalState.empty (.ok r) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalCallCountedExpr (.resolve "F") [.num 1] rootCtx []) =
      (do let callee <- withCtx (CtxMsg.call (.resolve "F")) ((evalFuel j).resolveCalleeAlg (.resolve "F") rootCtx)
          withCtx (CtxMsg.call (.resolve "F")) ((evalFuel j).evalResolvedCallCounted callee [.num 1] rootCtx []
            (openExprName (.resolve "F")) (.written (.resolve "F") rootCtx))) := rfl
    rw [e, show openExprName (.resolve "F") = "F" by simp [openExprName]]
    exact Ev.bind (Ev.withCtx ((callee_root _).ev j)) (Ev.withCtx (h.ev j))

theorem counted_root (t : EvalState) (r : CountedResult)
    (h : EvF (.evalCallCountedExpr (.resolve "F") [.num 1] rootCtx []) EvalState.empty (.ok r) t) :
    EvF (.evalCounted callF1 rootCtx []) EvalState.empty (.ok r) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalCounted callF1 rootCtx []) =
      (evalFuel j) (.evalCallCountedExpr (.resolve "F") [.num 1] rootCtx []) := rfl
    rw [e]
    exact h.ev j


theorem rows_root (t : EvalState) (v : Result)
    (h : EvF (.evalCounted callF1 rootCtx []) EvalState.empty (.ok (v, 1)) t) :
    EvF (.evalOutputRowsPreparedCore [callF1] rootCtx []) EvalState.empty
      (.ok { counted := (v, 1), outputSlots := [v] }) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalOutputRowsPreparedCore [callF1] rootCtx []) =
      EvalBody.evalOutputRowsPreparedCore (evalFuel j) [callF1] rootCtx [] := rfl
    rw [e]
    unfold EvalBody.evalOutputRowsPreparedCore
    rw [EvalBody.evalOutputRowsPreparedCore.collect.eq_2]
    refine Ev.bind (Ev.withNested (h.ev j)) ?_
    simp only [callF1]
    rw [EvalBody.evalOutputRowsPreparedCore.collect.eq_1]
    exact Ev.pure _ _

/-- The root context: the prelude alone. -/
def topCtx : EvalCtx := { callStack := [preludeAlg] }

theorem prepared_root (t : EvalState) (out : PreparedAlgorithmOutput)
    (h : EvF (.evalOutputRowsPreparedCore [callF1] rootCtx []) EvalState.empty (.ok out) t) :
    EvF (.evalAlgOutputPreparedCore progW topCtx []) EvalState.empty (.ok out) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalAlgOutputPreparedCore progW topCtx []) =
      (do let pushedCtx ← enterAlgorithmBody progW topCtx []
          (evalFuel j).evalOutputRowsPreparedCore [callF1] pushedCtx []) := rfl
    rw [e]
    exact Ev.bind (Ev.of_eq rfl) (h.ev j)

theorem countedCore_root (t : EvalState) (out : PreparedAlgorithmOutput)
    (h : EvF (.evalAlgOutputPreparedCore progW topCtx []) EvalState.empty (.ok out) t) :
    EvF (.evalAlgOutputCountedCore progW topCtx []) EvalState.empty (.ok out.counted) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalAlgOutputCountedCore progW topCtx []) =
      EvalBody.evalAlgOutputCountedCore (evalFuel j) progW topCtx [] := rfl
    rw [e]
    exact Ev.bind (h.ev j) (Ev.pure _ _)

theorem zeroArg_root (t : EvalState) (r : CountedResult)
    (h : EvF (.evalAlgOutputCountedCore progW topCtx []) EvalState.empty (.ok r) t) :
    EvF (.evalZeroArgumentDemandOutputCounted progW topCtx []) EvalState.empty (.ok r) t :=
  EvF.of_body fun j => by
    have e : evalStep (evalFuel j) (.evalZeroArgumentDemandOutputCounted progW topCtx []) =
      (evalFuel j) (.evalAlgOutputCountedCore progW topCtx []) := rfl
    rw [e]
    exact h.ev j


/-! ## 18. The whole read of `F(1)` -/

/-- The heap after the root call `F(1)` formed its supply: the written `1`. -/
def rootSupplied : EvalState := pushCell EvalState.empty (.expression (.num 1) rootCtx [])

/-- The heap after the program's output was assembled: `F(1)` called once. -/
def rootOutputState : EvalState := callState rootCtx 0 rootSupplied

theorem root_output :
    EvF (.evalZeroArgumentDemandOutputCounted progW topCtx []) EvalState.empty
      (.ok (.listValue [.deferred 3], 1)) rootOutputState :=
  zeroArg_root _ _ (countedCore_root _ _ (prepared_root _ _ (rows_root _ _ (counted_root _ _ (callExpr_root _ _
    (resolved_root _ _ (supplied_root _ _ _ (fCall rootCtx 0 rootSupplied rfl rfl rfl rfl))))))))

theorem rootOutputState_size : rootOutputState.needs.size = 4 := by
  simp [rootOutputState, callState_size, rootSupplied, EvalState.empty]

/-- THE ROOT GENERATION: the state in which the run value demands its first materialization cell. -/
theorem gen_root :
    Gen (matAlloc rootOutputState (.listValue [.deferred 3]) []) 0 [progW, preludeAlg] 1 0 [] := by
  have h1 : rootSupplied.needs.size = 1 := by simp [rootSupplied, EvalState.empty]
  have hctx : callCtx rootCtx 0 rootSupplied = fCtx [progW, preludeAlg] 0 1 0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [matAlloc_size, rootOutputState_size]
  · refine ⟨{ suspension := .expression (.num 1) rootCtx [] }, ?_, rfl, .inr ⟨rootCtx, rfl⟩⟩
    rw [matAlloc_old _ _ _ _ (by rw [rootOutputState_size]; omega), rootOutputState,
      callState_old _ _ _ _ (by rw [h1]; omega)]
    simp [rootSupplied, pushCell, EvalState.empty]
  · refine ⟨{ suspension := .expression resolveF (fCtx [progW, preludeAlg] 0 1 0) [] }, ?_, rfl, rfl⟩
    rw [matAlloc_old _ _ _ _ (by rw [rootOutputState_size]; omega), rootOutputState,
      show 0 + 2 = rootSupplied.needs.size + 1 by rw [h1], callState_mapper, hctx]
  · refine ⟨{ suspension := mappedSusp 0 (0 + 2) (fCtx [progW, preludeAlg] 0 1 0) }, ?_, rfl, rfl⟩
    rw [matAlloc_old _ _ _ _ (by rw [rootOutputState_size]; omega), rootOutputState,
      show 0 + 3 = rootSupplied.needs.size + 2 by rw [h1], callState_position, hctx, h1]
  · refine ⟨{ suspension := .ready (.listValue [.deferred (0 + 3)], 1) }, ?_, rfl, rfl⟩
    rw [show 0 + 4 = rootOutputState.needs.size by rw [rootOutputState_size], matAlloc_source]
    rfl
  · refine ⟨{ suspension := .ready (pathValue [], 1) }, ?_, rfl, rfl⟩
    rw [show 0 + 5 = rootOutputState.needs.size + 1 by rw [rootOutputState_size], matAlloc_path]
  · refine ⟨{ suspension := matSusp (0 + 4) (0 + 5) }, ?_, rfl, rfl⟩
    rw [show 0 + 6 = rootOutputState.needs.size + 2 by rw [rootOutputState_size], matAlloc_mat,
      rootOutputState_size]
  · intro p hp; cases hp

/-- **THE WHOLE READ OF `F(1)` IS INCOMPLETE AT EVERY FUEL.** For `F(x) = [x].map(F)`, the run
    value of the program whose one output row is `F(1)` — the production Lean evaluator's fuel
    approximation `evalFuel fuel (.evalRunValue …)` from `EvalState.empty`, exactly as
    `CoreTests/LazyCollections.lean` § READ GENERATIONS runs it — is the incomplete outcome for
    EVERY fuel. -/
theorem wholeRead_incomplete (fuel : Nat) :
    ((evalFuel fuel (.evalRunValue ((identifyPropertyExpr witnessProgram).run' 0) topCtx [])).runState
      EvalState.empty).1 = .error .fuelExhausted := by
  rw [identified]
  show Inc (evalFuel fuel (.evalRunValue (.algorithmExpr progA) topCtx [])) EvalState.empty
  cases fuel with
  | zero => rfl
  | succ k =>
    refine inc_succ ?_
    have e : evalStep (evalFuel k) (.evalRunValue (.algorithmExpr progA) topCtx []) =
      (((evalFuel k) (.evalZeroArgumentDemandOutputCounted progW topCtx []) >>= fun out => pure out.fst) >>=
        fun value => materializeVia (evalFuel k).demandNeedRecursive value) := by
      show EvalBody.evalRunValue (evalFuel k) (.algorithmExpr progA) topCtx [] = _
      unfold EvalBody.evalRunValue
      dsimp only
      rw [show wireToCaller topCtx progA = progW from wired_prog]
      rfl
    rw [e]
    refine Inc.bind (Ev.bind (root_output.ev k) (Ev.pure _ _)) ?_
    refine materializeVia_inc _ _ [] rootOutputState rfl ?_
    rw [rootOutputState_size]
    exact gen_incomplete k 0 [progW, preludeAlg] 1 0 [] _ gen_root


/-! ## 19. The observation `CoreTests/LazyCollections.lean` makes, and production -/

/-- The observation used in the finite guard is definitionally the core call of
    `wholeRead_incomplete`, including the identified program and initial state. -/
theorem fuelValue_F1_incomplete (fuel : Nat) :
    KatLangTests.LazyCollections.recursiveMapWholeReadAt fuel = .error .fuelExhausted :=
  wholeRead_incomplete fuel

/-- **PRODUCTION DOES NOT COMPLETE.** The production evaluator at the same call (`evalUnbounded`, the
    fuel search over the same core) never completes from the empty state: by the production bridge a
    completed production outcome is a completed core outcome at some fuel, and there is none. -/
theorem wholeRead_production_incomplete :
    ¬ ProductionCompletes (evalUnbounded (.evalRunValue ((identifyPropertyExpr witnessProgram).run' 0) topCtx []))
      EvalState.empty := by
  intro hc
  obtain ⟨m, _, hm⟩ := (production_completes_iff _ EvalState.empty _).1 ⟨rfl, hc⟩
  exact hm (evalFuel_incomplete_normal m _ _ (wholeRead_incomplete m))

/-- info: 'KatLang.RecursiveMapWholeRead.wholeRead_incomplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.RecursiveMapWholeRead.wholeRead_incomplete

/-- info: 'KatLang.RecursiveMapWholeRead.fuelValue_F1_incomplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.RecursiveMapWholeRead.fuelValue_F1_incomplete

/-- info: 'KatLang.RecursiveMapWholeRead.wholeRead_production_incomplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.RecursiveMapWholeRead.wholeRead_production_incomplete

end KatLang.RecursiveMapWholeRead
