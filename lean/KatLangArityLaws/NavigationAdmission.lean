import KatLangArityLaws.PublishedCallableNormal
import KatLangArityLaws.TotalLeaves

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.NavigationReread KatLang.NavigationSettled
open KatLang.MemoLinks (LinkHeapKept LinkKept)

/-!
# The admission condition of the navigation core: necessary, and what it needs (ledger E-18, step 1, M1)

`NavigationReread.navigation_reread` re-reads a completed, non-minting identity navigation that is a
run of the NAVIGATION CORE (`NavRuns`), i.e. a production run that makes none of three reads
(`navAdmits`). The independent review asked two questions of that restriction; this module answers
both with theorems.

## 1. Is the restriction unnecessarily strong? No: each clause is NECESSARY

For each clause there is a production run — completed, minting nothing — that is NOT re-read from a
navigation extension of its exit state, so `navigation_reread` is FALSE for it and no weaker
admission would do:

* `dangling_read_is_not_reread` — a parameter read through a captured activation index that is NOT
  recorded (`anchored` false): production answers "no cell" now and the cell's identity once a
  record lands on that index.
* `address_fault_is_not_reread` — a projection of an address outside the heap: an address fault
  now, a memo read once the cell exists.
* `cellless_param_row_is_not_reread` — a chase of an alias whose row is a parameter with NO cell
  (`paramRowAdmits` false): production's `supplyNeed` ALLOCATES a binding cell at every run, so the
  second run does not leave the state as it found it.

All three states are SYNTHETIC. They bound the theorem; they are not reachable-program claims and
show no language bug: a source program's run records an activation before any scope carries its
index, allocates a cell before any context names its address, and binds a cell to every parameter
an ordinary call binds. Those three sentences are exactly the whole-run invariants that would turn
`NavRuns` into a consequence of the production probe (§ 2).

## 2. What the admission needs of a reached state

* The ADDRESS clause and the CELL clause are statements about need addresses: the first is
  `a < s.needs.size`, the second that a recorded activation or the context's own tier binds the
  parameter. `AddressInvariant.Inv` with `ValidCtx` (whole-run, proved) bounds every address a
  context, an activation or the alias table holds; it does not say a parameter HAS a cell.
* The ACTIVATION clause is `anchored`: the captured activation index of the parameter is recorded.
  `anchored_of_chainRecorded` reduces it to ONE fact of the reading context — every activation
  index on its site scope's chain is recorded (`ChainRecorded`) — which is monotone in the
  activation array (`ChainRecorded.mono`) and holds of a body entry's head scope as soon as it holds
  of the entered algorithm's chain (`entered_chainRecorded`: the two writers of an activation index
  write the index they have just recorded).

NOT proved, and the reason `NavRuns` is still a premise of `member_bridge_of_probe`: that
`ChainRecorded` holds of EVERY context a reachable navigation reads a parameter in. The contexts a
navigation reads in are the probe's own and `C.push a` for every parameter-row alias `a` its chase
meets; such an alias comes from a lexical lookup or from a PUBLISHED CALLABLE, whose scope chain was
wired in the context its cell was supplied in — an arbitrary evaluation context of the run. The
invariant is therefore a property of every `EvalCtx`, `Algorithm` and `ScopeCtx` value the evaluator
handles, kept by every body: a per-body proof family with a value contract on every call whose
result is an algorithm (the opposite domain of `AddressInvariant`, whose call contracts are trivial
exactly on those results). It is not derivable from a relation between entry and exit STATES (the
indices travel in call arguments, not in the state), which is what made structure-normality
(`PublishedCallableNormal`) provable as a state relation and leaves this one open.
-/

namespace KatLang.NavigationAdmission

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

/-! ## 1. Each clause of the admission is necessary -/

/-- The owner of parameter `x`, activated at index `0`. -/
def ownerScope : ScopeCtx := .mk none ["x"] [] [] [] [] (some 0) none

/-- A site under that owner which does not bind `x` itself. -/
def site : Algorithm := .mk (some ownerScope) [] [] [] [] none

def dctx : EvalCtx := { callStack := [site] }

def identity : Algorithm := .mk none [] [] [] [.num 7] none

/-- No activation is recorded: index `0` dangles. -/
def before : EvalState := {}

/-- A navigation extension of `before`: one cell holding a completed CALLABLE, and the record at
    index `0`. -/
def after : EvalState :=
  { needs := #[{ suspension := .ready (.atom 0, 1), callable := .projected (.ok (some identity)) }]
    lexicalActivations := #[{ values := [], needs := [("x", 0)] }] }

theorem captured : capturedId? "x" dctx = some 0 := by cbv

theorem not_anchored : anchored "x" dctx before = false := by cbv

theorem ext : NavExt before after := by
  refine ⟨⟨?_, ?_, ⟨[{ values := [], needs := [("x", 0)] }], rfl⟩⟩, ⟨fun _ _ h => (by cases h), Nat.le_refl _⟩⟩
  · intro a c hc; simp [before] at hc
  · intro a c hc; simp [before] at hc

/-- Production, at the dangling state: no cell, no identity, no write, no mint. -/
theorem run_before : (projectParameterCallable "x" dctx).runState before = (.ok none, before) := by
  have hb : (projectParameterWith (EvalRec.projectNeedCallable evalUnbounded) "x" dctx).runState before =
      (.ok none, before) := by
    rw [projectParameterWith_run]
    have : parameterAddressIn before.lexicalActivations "x" dctx = none := by cbv
    rw [this]
  have hc : ProductionCompletes ((fun rec : EvalRec => projectParameterWith rec.projectNeedCallable "x" dctx) evalUnbounded) before := by
    unfold ProductionCompletes; rw [hb]; nofun
  exact (KatLang.WhileRoundProduction.production_eq_of_finite (.projectParameterCallable "x" dctx)
    (fun rec => projectParameterWith rec.projectNeedCallable "x" dctx) (fun _ => rfl)
    (finite_projectParameter "x" dctx) before hc).trans hb

/-- Production, at the navigation extension: the record now exists, and the answer CHANGES. -/
theorem run_after : (projectParameterCallable "x" dctx).runState after = (.ok (some identity), after) := by
  have haddr : parameterAddressIn after.lexicalActivations "x" dctx = some 0 := by cbv
  have hmemo := projectNeedCallable_memo 0 after _ (some identity) (by rfl : after.needs[0]? = some _) rfl
  have hb : (projectParameterWith (EvalRec.projectNeedCallable evalUnbounded) "x" dctx).runState after =
      (.ok (some identity), after) := by
    rw [projectParameterWith_run, haddr]
    exact hmemo
  have hc : ProductionCompletes ((fun rec : EvalRec => projectParameterWith rec.projectNeedCallable "x" dctx) evalUnbounded) after := by
    unfold ProductionCompletes; rw [hb]; nofun
  exact (KatLang.WhileRoundProduction.production_eq_of_finite (.projectParameterCallable "x" dctx)
    (fun rec => projectParameterWith rec.projectNeedCallable "x" dctx) (fun _ => rfl)
    (finite_projectParameter "x" dctx) after hc).trans hb

/-- **NEGATIVE CONTROL (i): the ACTIVATION clause is necessary.** A completed production parameter
    projection that minted nothing and wrote nothing is NOT re-read from a navigation extension:
    it is no navigation run, and the conclusion of `navigation_reread` is false for it. Synthetic:
    the context names an activation index nothing recorded. -/
theorem dangling_read_is_not_reread :
    (projectParameterCallable "x" dctx).runState before = (.ok none, before) ∧ NavExt before after ∧
    (projectParameterCallable "x" dctx).runState after ≠ (.ok none, after) ∧
    ¬ NavRuns (.projectParameterCallable "x" dctx) before (.ok none, before) := by
  refine ⟨run_before, ext, ?_, ?_⟩
  · rw [run_after]; intro h; cases h
  · intro hnav
    have h := (navigation_reread _ before before _ hnav rfl).2 after ext
    have h1 : (projectParameterCallable "x" dctx).runState after = (.ok none, after) := h.1
    rw [run_after] at h1
    cases h1

/-- A navigation extension of the empty heap: one cell with a completed CALLABLE. -/
def grown : EvalState := { needs := #[{ suspension := .ready (.atom 0, 1), callable := .projected (.ok none) }] }

theorem ext_grown : NavExt before grown := by
  refine ⟨⟨?_, ?_, ⟨[], rfl⟩⟩, ⟨fun _ _ h => (by cases h), Nat.le_refl _⟩⟩
  · intro a c hc; simp [before] at hc
  · intro a c hc; simp [before] at hc

/-- **NEGATIVE CONTROL (ii): the ADDRESS clause is necessary.** A projection of an address outside
    the heap is an address fault now and a memo read once the cell exists. Synthetic. -/
theorem address_fault_is_not_reread :
    NavExt before grown ∧ (projectNeedCallable 0).runState grown = (.ok none, grown) ∧
    ¬ NavRuns (.projectNeedCallable 0) before (.error (.illegalInEval "invalid need address"), before) := by
  have hg : (projectNeedCallable 0).runState grown = (.ok none, grown) :=
    projectNeedCallable_memo 0 grown _ none (by rfl : grown.needs[0]? = some _) rfl
  refine ⟨ext_grown, hg, ?_⟩
  intro hnav
  have h := ((navigation_reread _ before before _ hnav rfl).2 grown ext_grown).1
  have h1 : (projectNeedCallable 0).runState grown = (.error (.illegalInEval "invalid need address"), grown) := h
  rw [hg] at h1
  cases h1

/-- `A = y` as a runtime-target alias, `y` bound nowhere. -/
def paramAlias : Algorithm := .alias none [] [] (.param "y") none true

def actx : EvalCtx := { callStack := [identity] }

/-- The exit state of the alias's structure chase from the empty state, and of a second chase. -/
def once : EvalState := ((resolveAliasStructure paramAlias actx).runState EvalState.empty).2
def twice : EvalState := ((resolveAliasStructure paramAlias actx).runState once).2

theorem alloc_facts :
    ((resolveAliasStructure paramAlias actx).runState EvalState.empty = (.ok none, once)) ∧
    (once.needs.size = 1) ∧ (once.nextRuntimeDeclaration = 0) ∧
    ((resolveAliasStructure paramAlias actx).runState once = (.ok none, twice)) ∧
    (twice.needs.size = 2) ∧
    (paramRowAdmits paramAlias actx EvalState.empty = false) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- **NEGATIVE CONTROL (iii): the CELL clause is necessary.** A completed, NON-MINTING production
    structure chase that is not re-read: the alias's row is a parameter with no cell, and
    production allocates a binding cell at every run. Synthetic: a source program binds a cell to
    every parameter an ordinary call binds. -/
theorem cellless_param_row_is_not_reread :
    (resolveAliasStructure paramAlias actx).runState EvalState.empty = (.ok none, once) ∧
    once.nextRuntimeDeclaration = EvalState.empty.nextRuntimeDeclaration ∧
    (resolveAliasStructure paramAlias actx).runState once ≠ (.ok none, once) ∧
    ¬ NavRuns (.resolveAliasStructure paramAlias actx) EvalState.empty (.ok none, once) := by
  have hne : once ≠ twice := by
    intro h
    have h1 := alloc_facts.2.1
    have h2 := alloc_facts.2.2.2.2.1
    rw [← h] at h2
    omega
  refine ⟨alloc_facts.1, alloc_facts.2.2.1, ?_, ?_⟩
  · rw [alloc_facts.2.2.2.1]
    intro h
    exact hne (Prod.mk.inj h).2.symm
  · intro hnav
    have h := ((navigation_reread _ EvalState.empty once _ hnav alloc_facts.2.2.1).2 once (NavExt.refl once)).1
    have h1 : (resolveAliasStructure paramAlias actx).runState once = (.ok none, once) := h
    rw [alloc_facts.2.2.2.1] at h1
    exact hne (Prod.mk.inj h1).2.symm

/-- **The unconditional statement is false.** "Every completed, non-minting production navigation
    is re-read from every navigation extension of its exit state" fails on a state no program
    reaches: `NavRuns` (or an invariant of reached states implying it) cannot be dropped. -/
theorem unconditional_reread_is_false :
    ¬ ∀ (c : EvalCall) (s t : EvalState) (o : Except Error c.Ret),
      (evalUnbounded c).runState s = (o, t) → o ≠ .error .fuelExhausted →
      t.nextRuntimeDeclaration = s.nextRuntimeDeclaration →
      ∀ u, NavExt t u → (evalUnbounded c).runState u = (o, u) := by
  intro h
  have := h (.projectParameterCallable "x" dctx) before before (.ok none) run_before (by nofun) rfl after ext
  have h1 : (projectParameterCallable "x" dctx).runState after = (.ok none, after) := this
  rw [run_after] at h1
  cases h1

/-! ## 2. What the activation clause needs: a recorded site chain -/

/-- **A recorded chain**: every activation index on the scope chain is below `k` (instantiated with
    the size of the activation array: every index names an existing record). -/
def ChainRecorded (k : Nat) : Option ScopeCtx → Prop
  | none => True
  | some (.mk parent _ _ _ _ _ activation _) => (∀ id, activation = some id → id < k) ∧ ChainRecorded k parent

theorem ChainRecorded.mono {k k' : Nat} (hk : k ≤ k') :
    ∀ {chain : Option ScopeCtx}, ChainRecorded k chain → ChainRecorded k' chain
  | none, _ => by simp only [ChainRecorded]
  | some (.mk parent _ _ _ _ _ activation _), hv => by
      simp only [ChainRecorded] at hv ⊢
      exact ⟨fun id hid => Nat.lt_of_lt_of_le (hv.1 id hid) hk, ChainRecorded.mono hk (chain := parent) hv.2⟩

/-- Every production operation keeps a recorded chain recorded (the array only grows). -/
theorem ChainRecorded.production {chain : Option ScopeCtx} {s : EvalState}
    (h : ChainRecorded s.lexicalActivations.size chain) (c : EvalCall) :
    ChainRecorded ((evalUnbounded c).runState s).2.lexicalActivations.size chain :=
  h.mono (KatLang.OwnerContextStability.activations_kept c s).size_le

/-- The level's own index, and the rest of the chain. -/
theorem ChainRecorded.parent {k : Nat} {scope : ScopeCtx} (h : ChainRecorded k (some scope)) :
    ChainRecorded k scope.parent := by
  cases scope with
  | mk parent _ _ _ _ _ activation _ =>
    simp only [ChainRecorded] at h
    exact h.2

/-- The owner of a parameter on a recorded chain has a recorded activation. -/
theorem owner_recorded {k : Nat} (name : Ident) :
    ∀ {chain : Option ScopeCtx}, ChainRecorded k chain → ∀ scope, chain = some scope →
      ∀ owner, requiredParameterOwner? scope name = some owner → ∀ id, owner.activation = some id → id < k
  | none, _, _, h, _, _, _, _ => by cases h
  | some (.mk parent params opens props output branches activation decl), hv, scope, h, owner, ho, id, hid => by
      cases h
      simp only [ChainRecorded] at hv
      rw [KatLang.TotalLeaves.requiredParameterOwner?_equation] at ho
      split at ho
      · cases ho
        exact hv.1 id hid
      · cases hp : parent with
        | none =>
          simp only [ScopeCtx.parent, hp] at ho
          cases ho
        | some par =>
          simp only [ScopeCtx.parent, hp] at ho
          exact owner_recorded name (chain := parent) hv.2 par hp owner ho id hid

/-- **THE ACTIVATION CLAUSE FROM A RECORDED SITE CHAIN.** In a context whose site scope's chain is
    recorded at `s`, every parameter read is anchored: the admission condition of
    `projectParameterCallable`, and the first half of a parameter-row alias's. -/
theorem anchored_of_chainRecorded (x : Ident) (ctx : EvalCtx) (s : EvalState)
    (h : ChainRecorded s.lexicalActivations.size (siteScope? ctx)) : anchored x ctx s = true := by
  unfold anchored
  cases hid : capturedId? x ctx with
  | none => rfl
  | some id =>
    refine decide_eq_true ?_
    unfold capturedId? at hid
    cases hh : ctx.head? with
    | none => rw [hh] at hid; cases hid
    | some st =>
      cases hs : siteScope? ctx with
      | none => rw [hh, hs] at hid; cases hid
      | some scope =>
        rw [hh, hs] at hid
        dsimp only at hid
        split at hid
        · cases hid
        · rw [hs] at h
          cases hpar : scope.parent with
          | none => rw [hpar] at hid; cases hid
          | some par =>
            rw [hpar] at hid
            have hid' : (requiredParameterOwner? par x).bind ScopeCtx.activation = some id := hid
            cases ho : requiredParameterOwner? par x with
            | none => rw [ho] at hid'; cases hid'
            | some owner =>
              rw [ho] at hid'
              have hpc : ChainRecorded s.lexicalActivations.size (some par) := by
                have := h.parent
                rw [hpar] at this
                exact this
              exact owner_recorded x hpc par rfl owner ho id hid'

/-- The navigation core admits a parameter projection in a context with a recorded site chain. -/
theorem admits_parameter_read (x : Ident) (ctx : EvalCtx) (s : EvalState)
    (h : ChainRecorded s.lexicalActivations.size (siteScope? ctx)) :
    navAdmits (.projectParameterCallable x ctx) s = true :=
  anchored_of_chainRecorded x ctx s h

/-- The navigation core admits a projection exactly of an address inside the heap. -/
theorem admits_projection_iff (a : Nat) (s : EvalState) :
    navAdmits (.projectNeedCallable a) s = true ↔ a < s.needs.size := by
  show s.needs[a]?.isSome = true ↔ _
  constructor
  · intro h
    rcases Nat.lt_or_ge a s.needs.size with hl | hl
    · exact hl
    · rw [Array.getElem?_eq_none hl] at h; cases h
  · intro h
    rw [Array.getElem?_eq_getElem h]; rfl

/-- The scope a recording body entry installs as its head scope carries the index JUST RECORDED:
    its chain is recorded in the entered state whenever the entered algorithm's own chain was. -/
theorem entered_chainRecorded (a : Algorithm) (s : EvalState)
    (h : ChainRecorded s.lexicalActivations.size a.parent) :
    ChainRecorded (s.lexicalActivations.size + 1) (some (a.asScopeCtx.withActivation s.lexicalActivations.size)) := by
  simp only [Algorithm.asScopeCtx, ScopeCtx.withActivation, ChainRecorded]
  exact ⟨fun id hid => by cases hid; exact Nat.lt_succ_self _, h.mono (Nat.le_succ _)⟩

end KatLang.NavigationAdmission
