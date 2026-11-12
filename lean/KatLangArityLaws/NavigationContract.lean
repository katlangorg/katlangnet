import KatLangArityLaws.NavigationAdmission
import KatLangArityLaws.AddressInvariantProduction

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.MemberSettled KatLang.NavigationReread KatLang.NavigationSettled KatLang.NavigationAdmission
open KatLang.HeapAddressValidity KatLang.AddressInvariant
open KatLang.Publications KatLang.PublishedCallableNormal
open KatLang.OwnerContextStability (ActivationPrefix)
open Lean.Order

/-!
# Reachable navigation is admitted: the reduction to ONE per-body obligation (ledger E-18, step 1, M1)

`NavigationReread.navigation_reread` re-reads a completed, non-minting identity navigation that is a
run of the NAVIGATION CORE (`NavRuns`): production's own core, restricted to runs that make none of
three reads (`navAdmits`: an unrecorded captured activation, an address outside the heap, a
parameter-row alias whose parameter has no cell). `NavigationAdmission` proved each clause necessary
on a synthetic state. This module answers the remaining question — when IS a production navigation
a navigation-core run? — as far as it can be answered without a whole-run proof family:

> **B1 (`navRuns_of_contract`).** For EVERY call contract `K` of the evaluator that
> * every evaluator body keeps, the navigation bodies asking only contract questions
>   (`K.BodySound`, THE PER-BODY OBLIGATION — one proposition, `AddressInvariant.BodySound`'s form), and
> * gives the navigation facts at navigation calls (`K.Admits`: `NavFacts`),
>
> a completed production navigation from a `K.inv` state with a `K.pre` call is a `NavRuns` run.

Nothing else is assumed: no premise mentions the navigation core, `navAdmits` or `NavRuns`.

`navRuns_of_bodySound` specializes this schema to the proposed state invariant and explicit
navigation input facts. Admission is PROVED for that contract (`navigationContract_admits`), so its
only unproved hypothesis is the named `NavigationBodySound` obligation. The additional input and
result predicates are parameters: choosing the full static domain and value contracts, and proving
the obligation for them, remain B2. This specialization does not assert their existence.

## Why the obligation has two halves

A one-run Hoare triple ("from a valid state and a valid call, the exit state is valid") cannot show
that the RESTRICTED core does not refuse: refusal is the incomplete outcome, and a partial-correctness
triple says nothing of a run that is incomplete. What is needed is a fact about the questions a body
ASKS. `K.BodySound` therefore has, beside the triple (`K.Keeps (evalStep rec)`), a second half for the
eight navigation bodies: over an answer that keeps the contract, the body runs ALIKE over that answer
GUARDED by the contract (`K.guard`: a question outside the contract is refused). It is the semantic
form of "every call site's precondition is established", which is what a syntax-directed Hoare proof
establishes at each recursive call anyway; it is stated for `evalStep` over an arbitrary answer and
never mentions the navigation core.

The reduction is then two-run agreement by the approximation order, with no second evaluator: the
guarded production answer of fuel `n`, restricted to navigation shapes, approximates `navFuel n`
(induction hypothesis and admission), so by `evalStep_monotone` the body over it approximates the body
over `navFuel n`; the body over it IS the body over production's answer (guard transparency, and the
navigation bodies ask only navigation-shaped questions, `evalStep_shapeGuard`), which completes.

## The navigation facts, and where the three clauses come from

`NavFacts` is the navigation fragment of the proposed contract; `navFacts_admits` proves it implies
admission, clause by clause:

* ACTIVATION — `Backed acts chain`: every ACTIVATED level of the scope chain names a recorded
  activation (`Backed.chainRecorded`, then `NavigationAdmission.anchored_of_chainRecorded`);
* CELL — the same record binds every parameter of its level (`Backed`'s second half), and a
  parameter-row alias lives under its owner's ACTIVATION (`ParamRowOwned`): together the parameter's
  cell is found through the recorded activation whatever context reads it
  (`paramRowAdmits_of_owned`);
* ADDRESS — a projected address is inside the heap. At the two navigation call sites that project,
  this is DERIVED from the proved whole-run invariant `AddressInvariant.Inv` and `ValidCtx`:
  `parameter_address_valid` (a parameter's cell) and `bindingCell_address_valid` (a chase step's
  binding cell); `guard_projectParameterCallable` is the obligation's second half for that body,
  proved outright from them.

`Backed` is monotone in the activation array (`Backed.mono`, `Backed.ext`), so it survives every
production operation (`Backed.production`).

## What is reused

The obligation ranges over NORMAL answers only (`NormalRec`: an incomplete outcome is THE incomplete
outcome — every fuel iterate is one), which is all B1 uses. That makes the proved address family
an instance of its first half with no body re-proved: a normal answer keeping the address contract
on its completed runs is approximated by its completed part, which is sound on every outcome
(`addressContract_keeps_step`, from `AddressInvariant.evalStep_sound`).

## NOT proved here (B2)

That such a contract EXISTS for the production evaluator: `K.BodySound` for a concrete `K` is a
proof family over all 102 bodies, with a value contract on every algorithm-returning call. The
proposed state half is `StoredOK` (every stored caller and every published CALLABLE is `CtxOK` /
`AlgOK`); it is stated, holds of the empty state, and is NOT proved to be kept. In particular
`ParamRowOwned` is not a consequence of binder facts: it needs the local-only law — a member that
captures an ancestor parameter is wired only under that ancestor's activation — whose static half
(the exposure metadata is complete) is computed by the C# front end and is NOT validated by this
file's pre-evaluation checks. `NavigationContractGuards` shows a host-built tree with an exported
parameter-row member reaches a navigation that is not re-read. Nothing here is about C#.
-/

namespace KatLang.NavigationContract

/-! ## A call contract, and the per-body obligation -/

/-- **A CALL CONTRACT of the evaluator**: a state invariant, how a run may change the state (what a
    later precondition must survive), and a precondition and a result contract per call. -/
structure Contract where
  inv : EvalState → Prop
  ext : EvalState → EvalState → Prop
  pre : EvalCall → EvalState → Prop
  post : (c : EvalCall) → c.Ret → EvalState → Prop

namespace Contract
variable (K : Contract)

/-- `m` keeps the contract of call `c`: a COMPLETED run from an invariant state satisfying the
    precondition ends in an invariant state, an extension of the entry state, with a result
    satisfying the result contract. -/
def Holds (c : EvalCall) (m : EvalM c.Ret) : Prop :=
  ∀ s, K.inv s → K.pre c s → (m.runState s).1 ≠ .error .fuelExhausted →
    K.inv (m.runState s).2 ∧ K.ext s (m.runState s).2 ∧
      ∀ x, (m.runState s).1 = .ok x → K.post c x (m.runState s).2

/-- An answer every call of which keeps the contract. -/
def Keeps (rec : EvalRec) : Prop := ∀ c, K.Holds c (rec c)

/-- **The answer GUARDED by the contract**: a question asked outside the contract — from a state
    that is not invariant, or with a call that does not satisfy its precondition — is refused (the
    incomplete outcome). No second evaluator: where it answers, it is `rec`. -/
noncomputable def guard (rec : EvalRec) : EvalRec := fun c =>
  ⟨fun s => @ite _ (K.inv s ∧ K.pre c s) (Classical.propDecidable _)
    ((rec c).runState s) (.error .fuelExhausted, {})⟩

theorem guard_run_of (rec : EvalRec) (c : EvalCall) (s : EvalState) (hi : K.inv s) (hp : K.pre c s) :
    (K.guard rec c).runState s = (rec c).runState s := by
  show @ite _ (K.inv s ∧ K.pre c s) (Classical.propDecidable _) _ _ = _
  rw [ite_eq_left ⟨hi, hp⟩]

theorem guard_run_of_not (rec : EvalRec) (c : EvalCall) (s : EvalState) (h : ¬ (K.inv s ∧ K.pre c s)) :
    (K.guard rec c).runState s = (.error .fuelExhausted, {}) := by
  show @ite _ (K.inv s ∧ K.pre c s) (Classical.propDecidable _) _ _ = _
  rw [ite_eq_right h]

end Contract

/-- The call shapes of identity navigation: what `navAdmits` answers somewhere. -/
def navStatic : EvalCall → Bool
  | .aliasStepIsRuntime _ _ _ _ => true
  | .resolveAliasChase _ _ _ _ _ _ => true
  | .resolveAliasStructure _ _ => true
  | .resolveDotReceiver? _ _ => true
  | .projectNeedStructuralMember _ _ => true
  | .algorithmIntrinsicRoute _ _ => true
  | .projectParameterCallable _ _ => true
  | .projectNeedCallable _ => true
  | .resolveAlg e _ => resolveAlgAdmits e
  | _ => false

theorem navStatic_of_admits {c : EvalCall} {s : EvalState} (h : navAdmits c s = true) : navStatic c = true := by
  cases c <;> first | rfl | exact h | (simp [navAdmits] at h)

/-- The eight navigation BODIES the navigation core runs over itself (a projection is handed to
    production's core whole). -/
def navBody (c : EvalCall) : Bool := navStatic c && !isProjection c

/-- An answer whose every incomplete outcome is THE incomplete outcome (no retained state) — what
    every fuel iterate of the core is (`evalFuel_incomplete_normal`), and all the obligation has to
    range over. -/
def NormalRec (rec : EvalRec) : Prop :=
  ∀ (c : EvalCall) (s : EvalState), ((rec c).runState s).1 = .error .fuelExhausted → (rec c).IsIncompleteAt s

theorem normalRec_fuel (n : Nat) : NormalRec (evalFuel n) := fun c s h => evalFuel_incomplete_normal n c s h

/-- **THE PER-BODY OBLIGATION** of a contract `K`. Over every (normal) answer that keeps the contract:
    1. every evaluator body keeps the contract (`AddressInvariant.BodySound`'s form), and
    2. each of the eight navigation bodies, run from an invariant state on a call satisfying its
       precondition, asks only contract questions: it runs alike over the GUARDED answer. -/
def Contract.BodySound (K : Contract) : Prop :=
  ∀ rec : EvalRec, NormalRec rec → K.Keeps rec →
    K.Keeps (evalStep rec) ∧
    ∀ (c : EvalCall) (s : EvalState), navBody c = true → K.inv s → K.pre c s →
      ((evalStep rec c).runState s).1 ≠ .error .fuelExhausted →
      (evalStep (K.guard rec) c).runState s = (evalStep rec c).runState s

/-! ## The navigation bodies ask only navigation-shaped questions -/

/-- An answer restricted to the navigation shapes. -/
def shapeGuard (rec : EvalRec) : EvalRec := fun c => if navStatic c then rec c else EvalM.incomplete

theorem shapeGuard_of (rec : EvalRec) (c : EvalCall) (h : navStatic c = true) : shapeGuard rec c = rec c := by
  unfold shapeGuard; rw [ite_eq_left h]

theorem shapeGuard_of_not (rec : EvalRec) (c : EvalCall) (h : navStatic c = false) :
    shapeGuard rec c = EvalM.incomplete := by
  unfold shapeGuard; rw [ite_eq_right (by rw [h]; nofun)]

/-- **SHAPE CLOSURE.** Each of the eight navigation bodies is the same computation over an answer and
    over that answer restricted to the navigation shapes: its recursive calls are identity-navigation
    calls, and `resolveAlg` only of a head that is no name, block or parameter. -/
theorem evalStep_shapeGuard (rec : EvalRec) (c : EvalCall) (h : navBody c = true) :
    evalStep (shapeGuard rec) c = evalStep rec c := by
  cases c
  case aliasStepIsRuntime step target ctx visited => rfl
  case resolveAliasChase fc pr a ctx visited last => rfl
  case resolveAliasStructure a ctx => rfl
  case projectNeedStructuralMember e ctx => rfl
  case algorithmIntrinsicRoute receiver ctx => rfl
  case projectParameterCallable x ctx => rfl
  case resolveDotReceiver? e ctx =>
    cases e with
    | dotMember o n fb args => cases args <;> rfl
    | _ => rfl
  case resolveAlg e ctx =>
    cases e <;> first
      | rfl
      | (simp [navBody, navStatic, resolveAlgAdmits] at h)
  all_goals (simp [navBody, navStatic, isProjection] at h)

/-! ## Transfer of the contract through the fuel core and to production -/

/-- Under the per-body obligation, the total core keeps the contract at every fuel. -/
theorem Contract.keeps_fuel (K : Contract) (hbody : K.BodySound) : ∀ n, K.Keeps (evalFuel n) := by
  intro n
  induction n with
  | zero => exact fun c s _ _ hne => absurd rfl hne
  | succ n ih =>
    intro c s hi hp hne
    rw [evalFuel_succ] at hne ⊢
    by_cases hraw : ((evalStep (evalFuel n) c).runState s).1 = .error .fuelExhausted
    · rw [normalize_of_incomplete _ s hraw] at hne
      exact absurd rfl hne
    · rw [normalize_of_complete _ s hraw]
      exact (hbody _ (normalRec_fuel n) ih).1 c s hi hp hraw

/-- **PRODUCTION keeps the contract** (the Hoare form of reachability): a completed production
    operation from an invariant state, on a call satisfying its precondition, ends in an invariant
    state — an extension of the entry state — with a result satisfying the result contract. So the
    invariant at the empty state reaches every state a sequence of contract calls reaches. -/
theorem Contract.production_keeps (K : Contract) (hbody : K.BodySound) : K.Keeps evalUnbounded := by
  intro c s hi hp hne
  obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hne⟩
  rw [← hr]
  exact K.keeps_fuel hbody m c s hi hp ((evalFuel_completes_iff m c s).1 hm)

/-! ## B1: the two-run agreement -/

/-- **TWO-RUN AGREEMENT.** Under the per-body obligation of a contract whose invariant and
    preconditions give admission at the navigation shapes: wherever the total core completes a
    navigation call from an invariant state satisfying its precondition, the NAVIGATION core — the
    same bodies over the restricted answer — returns the same outcome and the same state.

    By induction on fuel, through the approximation order: the guarded core of fuel `n`, restricted
    to the navigation shapes, approximates `navFuel n` (induction hypothesis), so the body over it
    approximates the body over `navFuel n` (`evalStep_monotone`); and the body over it is the body
    over the core (guard transparency and shape closure), which completes. -/
theorem navFuel_agrees (K : Contract) (hbody : K.BodySound)
    (hadm : ∀ c s, navStatic c = true → K.inv s → K.pre c s → navAdmits c s = true) :
    ∀ (n : Nat) (c : EvalCall) (s : EvalState), navStatic c = true → K.inv s → K.pre c s →
      Completes (evalFuel n c) s → (navFuel n c).runState s = (evalFuel n c).runState s := by
  intro n
  induction n with
  | zero => intro c s _ _ _ hc; exact absurd rfl hc
  | succ n ih =>
    intro c s hc hi hp hcomp
    have hne := (evalFuel_completes_iff (n + 1) c s).1 hcomp
    rw [navFuel_succ_run, ite_eq_left (hadm c s hc hi hp)]
    by_cases hproj : isProjection c = true
    · rw [ite_eq_left hproj]
    · rw [ite_eq_right hproj, evalFuel_succ]
      rw [evalFuel_succ] at hne
      -- the core's body completes
      have hraw : ((evalStep (evalFuel n) c).runState s).1 ≠ .error .fuelExhausted := by
        intro hraw
        rw [normalize_of_incomplete _ s hraw] at hne
        exact hne rfl
      have hnav : navBody c = true := by
        unfold navBody
        rw [hc]
        cases hp' : isProjection c with
        | true => exact absurd hp' hproj
        | false => rfl
      -- the guarded core, restricted to the navigation shapes, approximates the navigation core
      have hle : shapeGuard (K.guard (evalFuel n)) ⊑ navFuel n := by
        intro c' s'
        cases hc' : navStatic c' with
        | false =>
          left
          rw [shapeGuard_of_not _ _ hc']
          rfl
        | true =>
          rw [shapeGuard_of _ _ hc']
          by_cases hv : K.inv s' ∧ K.pre c' s'
          · by_cases hcomp' : Completes (evalFuel n c') s'
            · right
              rw [K.guard_run_of _ _ _ hv.1 hv.2]
              exact (ih c' s' hc' hv.1 hv.2 hcomp').symm
            · left
              have hi' : (evalFuel n c').IsIncompleteAt s' := Classical.not_not.mp hcomp'
              unfold EvalM.IsIncompleteAt at hi' ⊢
              rw [K.guard_run_of _ _ _ hv.1 hv.2]
              exact hi'
          · left
            unfold EvalM.IsIncompleteAt
            exact K.guard_run_of_not _ _ _ hv
      -- the body over it IS the body over the core
      have hbodyeq : (evalStep (shapeGuard (K.guard (evalFuel n))) c).runState s =
          (evalStep (evalFuel n) c).runState s := by
        rw [evalStep_shapeGuard _ c hnav]
        exact (hbody _ (normalRec_fuel n) (K.keeps_fuel hbody n)).2 c s hnav hi hp hraw
      have hstep : (evalStep (navFuel n) c).runState s = (evalStep (evalFuel n) c).runState s := by
        rcases evalStep_monotone _ _ hle c s with hinc | heq
        · exfalso
          apply hraw
          unfold EvalM.IsIncompleteAt at hinc
          rw [← hbodyeq, hinc]
        · rw [← heq, hbodyeq]
      have hraw' : ((evalStep (navFuel n) c).runState s).1 ≠ .error .fuelExhausted := by rw [hstep]; exact hraw
      rw [normalize_of_complete _ s hraw', normalize_of_complete _ s hraw, hstep]

/-- **B1 — REACHABLE NAVIGATION IS ADMITTED, relative to the per-body obligation.** For every contract
    `K` that the bodies keep (`K.BodySound`) and that gives admission at the navigation shapes: a
    COMPLETED production navigation from an invariant state, on a call satisfying its precondition,
    is a run of the navigation core. No premise mentions the navigation core's own runs. -/
theorem navRuns_of_admitting (K : Contract) (hbody : K.BodySound)
    (hadm : ∀ c s, navStatic c = true → K.inv s → K.pre c s → navAdmits c s = true)
    (c : EvalCall) (s : EvalState) (hc : navStatic c = true) (hi : K.inv s) (hp : K.pre c s)
    (hdone : ProductionCompletes (evalUnbounded c) s) :
    NavRuns c s ((evalUnbounded c).runState s) := by
  obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hdone⟩
  exact ⟨m, (navFuel_agrees K hbody hadm m c s hc hi hp hm).trans hr, hdone⟩

/-! ## The navigation facts: what the three admission clauses need of a reached state -/

/-- **A BACKED chain.** Every ACTIVATED level of the scope chain names a recorded activation, and
    that record binds a cell to every parameter of the level. (An unactivated level — a
    parameterized container navigated from outside its activation, `F.Q` — is unconstrained.) -/
def Backed (acts : Array ParameterActivation) : Option ScopeCtx → Prop
  | none => True
  | some (.mk parent params _ _ _ _ activation _) =>
      (∀ id, activation = some id → ∃ act, acts[id]? = some act ∧
        ∀ y, params.contains y = true → (lookupAssoc y act.needs).isSome = true) ∧
      Backed acts parent

/-- A backed chain stays backed in every array that keeps the records it names. -/
theorem Backed.mono {acts acts' : Array ParameterActivation}
    (h : ∀ (i : Nat) (act : ParameterActivation), acts[i]? = some act → acts'[i]? = some act) :
    ∀ {chain : Option ScopeCtx}, Backed acts chain → Backed acts' chain
  | none, _ => by simp only [Backed]
  | some (.mk parent _ _ _ _ _ activation _), hv => by
      simp only [Backed] at hv ⊢
      refine ⟨fun id hid => ?_, Backed.mono h (chain := parent) hv.2⟩
      obtain ⟨act, ha, hb⟩ := hv.1 id hid
      exact ⟨act, h id act ha, hb⟩

theorem lt_of_getElem?_some {α : Type} {xs : Array α} {i : Nat} {x : α} (h : xs[i]? = some x) : i < xs.size := by
  rcases Nat.lt_or_ge i xs.size with hl | hl
  · exact hl
  · rw [Array.getElem?_eq_none hl] at h; cases h

/-- The activation array only grows, record for record: a backed chain survives every extension. -/
theorem Backed.ext {s t : EvalState} (h : ActivationPrefix s t) {chain : Option ScopeCtx}
    (hb : Backed s.lexicalActivations chain) : Backed t.lexicalActivations chain :=
  hb.mono (fun i act hi => by rw [h.lookup (lt_of_getElem?_some hi)]; exact hi)

/-- Every production operation keeps a backed chain backed, whatever its outcome. -/
theorem Backed.production {s : EvalState} {chain : Option ScopeCtx}
    (hb : Backed s.lexicalActivations chain) (c : EvalCall) :
    Backed ((evalUnbounded c).runState s).2.lexicalActivations chain :=
  hb.ext (KatLang.OwnerContextStability.activations_kept c s)

/-- A backed chain is a recorded chain (`NavigationAdmission.ChainRecorded`). -/
theorem Backed.chainRecorded {acts : Array ParameterActivation} :
    ∀ {chain : Option ScopeCtx}, Backed acts chain → ChainRecorded acts.size chain
  | none, _ => by simp only [ChainRecorded]
  | some (.mk parent _ _ _ _ _ activation _), hv => by
      simp only [Backed] at hv
      simp only [ChainRecorded]
      refine ⟨fun id hid => ?_, Backed.chainRecorded (chain := parent) hv.2⟩
      obtain ⟨act, ha, -⟩ := hv.1 id hid
      exact lt_of_getElem?_some ha

/-- The ACTIVATED owner of a parameter on a backed chain: its record exists and binds the parameter. -/
theorem owner_backed {acts : Array ParameterActivation} (name : Ident) :
    ∀ {chain : Option ScopeCtx}, Backed acts chain → ∀ scope, chain = some scope →
      ∀ owner, requiredParameterOwner? scope name = some owner → ∀ id, owner.activation = some id →
        ∃ act, acts[id]? = some act ∧ (lookupAssoc name act.needs).isSome = true
  | none, _, _, h, _, _, _, _ => by cases h
  | some (.mk parent params opens props output branches activation decl), hv, scope, h, owner, ho, id, hid => by
      cases h
      simp only [Backed] at hv
      rw [KatLang.TotalLeaves.requiredParameterOwner?_equation] at ho
      split at ho
      · rename_i hc
        cases ho
        obtain ⟨act, ha, hb⟩ := hv.1 id hid
        exact ⟨act, ha, hb name hc⟩
      · cases hp : parent with
        | none =>
          simp only [ScopeCtx.parent, hp] at ho
          cases ho
        | some par =>
          simp only [ScopeCtx.parent, hp] at ho
          exact owner_backed name (chain := parent) hv.2 par hp owner ho id hid

/-- **A parameter-row alias lives under its owner's ACTIVATION**: the nearest level of its own chain
    that binds the row's parameter is activated. State-independent. Every other algorithm satisfies
    it. (An alias wired under an UNACTIVATED owner would read the row's parameter in whatever
    context chases it.) -/
def ParamRowOwned : Algorithm → Prop
  | .alias parent _ _ (.param y) _ _ =>
      ∃ p owner id, parent = some p ∧ requiredParameterOwner? p y = some owner ∧ owner.activation = some id
  | _ => True

/-- The captured activation of a parameter row, read in the alias's own pushed context: its owner's,
    on the alias's OWN chain — the reading context takes no part. -/
theorem capturedId?_paramRow (p : ScopeCtx) (opens : List Expr) (props : List PropDef) (y : Ident)
    (id : Option PropertyIdentity) (reference : Bool) (ctx : EvalCtx) :
    capturedId? y (ctx.push (.alias (some p) opens props (.param y) id reference)) =
      (requiredParameterOwner? p y).bind ScopeCtx.activation := rfl

/-- **THE ACTIVATION AND CELL CLAUSES of a chase step.** An alias whose chain is backed and whose
    parameter row, if it has one, is owned: the navigation core admits its chase in EVERY context. -/
theorem paramRowAdmits_of_owned (a : Algorithm) (ctx : EvalCtx) (s : EvalState)
    (hb : Backed s.lexicalActivations a.parent) (ho : ParamRowOwned a) : paramRowAdmits a ctx s = true := by
  unfold paramRowAdmits
  split
  · rename_i parent opens props y id reference
    obtain ⟨p, owner, i, hp, hown, hid⟩ := ho
    subst hp
    obtain ⟨act, hact, hy⟩ := owner_backed y (chain := some p) hb p rfl owner hown i hid
    have hcap : capturedId? y (ctx.push (.alias (some p) opens props (.param y) id reference)) = some i := by
      rw [capturedId?_paramRow, hown]
      exact hid
    have hanch : anchored y (ctx.push (.alias (some p) opens props (.param y) id reference)) s = true := by
      unfold anchored
      rw [hcap]
      exact decide_eq_true (lt_of_getElem?_some hact)
    have haddr : parameterAddressIn s.lexicalActivations y
        (ctx.push (.alias (some p) opens props (.param y) id reference)) = lookupAssoc y act.needs := by
      unfold parameterAddressIn
      rw [hcap]
      show lookupAssoc y ((s.lexicalActivations[i]?.map ParameterActivation.needs).getD _) = _
      rw [hact]
      rfl
    rw [hanch, haddr, hy]
    rfl
  · rfl

/-- **THE NAVIGATION FACTS**: the navigation fragment of the proposed call precondition — what a
    contract has to give at a navigation call for the navigation core to admit it. Every other
    navigation call is admitted outright. -/
def NavFacts : EvalCall → EvalState → Prop
  | .resolveAliasChase _ _ a _ _ _, s => Backed s.lexicalActivations a.parent ∧ ParamRowOwned a
  | .projectParameterCallable _ ctx, s => Backed s.lexicalActivations (siteScope? ctx)
  | .projectNeedCallable a, s => a < s.needs.size
  | _, _ => True

/-- **ADMISSION FROM THE NAVIGATION FACTS**, clause by clause. -/
theorem navFacts_admits (c : EvalCall) (s : EvalState) (hc : navStatic c = true) (h : NavFacts c s) :
    navAdmits c s = true := by
  cases c
  case resolveAliasChase fc pr a ctx vis last => exact paramRowAdmits_of_owned a ctx s h.1 h.2
  case projectParameterCallable x ctx => exact anchored_of_chainRecorded x ctx s (Backed.chainRecorded h)
  case projectNeedCallable a => exact (admits_projection_iff a s).2 h
  case resolveAlg e ctx => exact hc
  all_goals first | rfl | (simp [navStatic] at hc)

/-- A contract ADMITS navigation: at every navigation call, its invariant and precondition give the
    navigation facts. -/
def Contract.Admits (K : Contract) : Prop :=
  ∀ c s, navStatic c = true → K.inv s → K.pre c s → NavFacts c s

/-- **B1.** Under the per-body obligation of a contract that admits navigation, a completed
    production navigation from an invariant state, on a call satisfying its precondition, is a
    navigation-core run. -/
theorem navRuns_of_contract (K : Contract) (hbody : K.BodySound) (hadm : K.Admits)
    (c : EvalCall) (s : EvalState) (hc : navStatic c = true) (hi : K.inv s) (hp : K.pre c s)
    (hdone : ProductionCompletes (evalUnbounded c) s) :
    NavRuns c s ((evalUnbounded c).runState s) :=
  navRuns_of_admitting K hbody (fun c s hc hi hp => navFacts_admits c s hc (hadm c s hc hi hp)) c s hc hi hp hdone

/-- **B1 with re-read.** Such a navigation that minted no runtime identity is a navigation extension
    and is RE-READ — the same outcome, no write — from every navigation extension of its exit state. -/
theorem reread_of_contract (K : Contract) (hbody : K.BodySound) (hadm : K.Admits)
    (c : EvalCall) (s t : EvalState) (o : Except Error c.Ret) (hc : navStatic c = true) (hi : K.inv s)
    (hp : K.pre c s) (hrun : (evalUnbounded c).runState s = (o, t)) (hne : o ≠ .error .fuelExhausted)
    (hmint : t.nextRuntimeDeclaration = s.nextRuntimeDeclaration) :
    NavExt s t ∧ ∀ u, NavExt t u → (evalUnbounded c).runState u = (o, u) ∧ NavRuns c u (o, u) := by
  have hnav := navRuns_of_contract K hbody hadm c s hc hi hp (by unfold ProductionCompletes; rw [hrun]; exact hne)
  rw [hrun] at hnav
  exact navigation_reread c s t o hnav hmint

/-! ## The ADDRESS clause from `AddressInvariant.Inv` and `ValidCtx`

Two navigation call sites project a cell: a parameter's projection and a chase's runtime step. At
both, the projected address is inside the heap by the PROVED whole-run address invariant. -/

/-- **A parameter's cell is inside the heap**: found through a recorded activation (`Inv.activations`)
    or in the context's own tier (`ValidCtx`). -/
theorem parameter_address_valid (x : Ident) (ctx : EvalCtx) (s : EvalState) (vs : Inv s)
    (vc : ValidCtx s.needs ctx) (a : Nat) (h : parameterAddressIn s.lexicalActivations x ctx = some a) :
    a < s.needs.size := by
  unfold parameterAddressIn at h
  cases hid : capturedId? x ctx with
  | none =>
    rw [hid] at h
    exact ValidNeedEnv.lookup vc h
  | some id =>
    rw [hid] at h
    cases hact : s.lexicalActivations[id]? with
    | none =>
      have h' : lookupAssoc x ctx.needEnv = some a := by
        have : (Option.bind (some id) fun id => s.lexicalActivations[id]?) = none := hact
        rw [this] at h
        exact h
      exact ValidNeedEnv.lookup vc h'
    | some act =>
      have h' : lookupAssoc x act.needs = some a := by
        have : (Option.bind (some id) fun id => s.lexicalActivations[id]?) = some act := hact
        rw [this] at h
        exact h
      exact ValidNeedEnv.lookup (vs.activations id act hact).1 h'

/-- **A chase step's binding cell is inside the heap it leaves**, and the address invariant is kept:
    the recorded cell (`Inv.aliasCells`), a transported parameter cell, or a fresh one. -/
theorem bindingCell_address_valid (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (s : EvalState)
    (vs : Inv s) (vc : ValidCtx s.needs ctx) :
    Inv ((aliasBindingCell wired target ctx).runState s).2 ∧
    s.needs.size ≤ ((aliasBindingCell wired target ctx).runState s).2.needs.size ∧
    ∀ a, ((aliasBindingCell wired target ctx).runState s).1 = .ok a →
      a < ((aliasBindingCell wired target ctx).runState s).2.needs.size :=
  aliasBindingCell_spec (P := fun h => ValidCtx h ctx) (fun _ ph => ph)
    (fun _ _ g v => ValidCtx.mono g v) s vs vc

/-- **THE SECOND HALF OF THE OBLIGATION for a parameter's projection, PROVED.** For every contract
    whose invariant gives the address invariant, whose precondition of a parameter projection gives
    a valid context, and whose precondition of a CALLABLE projection is implied by the address
    bound: the body asks only contract questions — its one question is the projection of the
    parameter's cell, at the entry state. -/
theorem guard_projectParameterCallable (K : Contract) (rec : EvalRec) (x : Ident) (ctx : EvalCtx) (s : EvalState)
    (hi : K.inv s) (hinv : Inv s) (hctx : ValidCtx s.needs ctx)
    (hproj : ∀ a, a < s.needs.size → K.pre (.projectNeedCallable a) s) :
    (evalStep (K.guard rec) (.projectParameterCallable x ctx)).runState s =
      (evalStep rec (.projectParameterCallable x ctx)).runState s := by
  show (projectParameterWith (EvalRec.projectNeedCallable (K.guard rec)) x ctx).runState s =
    (projectParameterWith (EvalRec.projectNeedCallable rec) x ctx).runState s
  rw [projectParameterWith_run, projectParameterWith_run]
  cases haddr : parameterAddressIn s.lexicalActivations x ctx with
  | none => rfl
  | some a => exact K.guard_run_of rec _ s hi (hproj a (parameter_address_valid x ctx s hinv hctx a haddr))

/-- The second half for `resolveAlg` at a head the navigation core answers: the body asks nothing. -/
theorem guard_resolveAlg (K : Contract) (rec : EvalRec) (e : Expr) (ctx : EvalCtx)
    (he : resolveAlgAdmits e = true) :
    evalStep (K.guard rec) (.resolveAlg e ctx) = evalStep rec (.resolveAlg e ctx) := by
  cases e <;> first
    | rfl
    | (simp [resolveAlgAdmits] at he)

/-! ## What is reused: the address contract instantiates the first half

`AddressInvariant.evalStep_sound` (proved, every body) is a per-body step for answers sound on EVERY
outcome. A normal answer that keeps the address contract on its COMPLETED runs is approximated by
its completed part, which is sound on every outcome; so the first half of the obligation holds of
the address contract by the existing proof family, with no body re-proved. -/

/-- The address contract of `AddressInvariant`, as a `Contract`. -/
def addressContract : Contract where
  inv := Inv
  ext := fun s t => s.needs.size ≤ t.needs.size
  pre := fun c s => CallPre c s.needs
  post := fun c x s => CallPost c x s.needs

/-- **THE FIRST HALF OF THE OBLIGATION for the address contract, from the proved family.** -/
theorem addressContract_keeps_step (rec : EvalRec) (hn : NormalRec rec) (hk : addressContract.Keeps rec) :
    addressContract.Keeps (evalStep rec) := by
  classical
  -- the completed part of `rec`, stopping at the entry state where `rec` does not complete
  let part : EvalRec := fun c =>
    ⟨fun s => if ((rec c).runState s).1 = .error .fuelExhausted then (.error .fuelExhausted, s) else (rec c).runState s⟩
  have hpart : ∀ c s, (part c).runState s =
      if ((rec c).runState s).1 = .error .fuelExhausted then (.error .fuelExhausted, s) else (rec c).runState s :=
    fun _ _ => rfl
  have hsound : RecSound part := by
    intro c _ s vs ps
    rw [hpart]
    by_cases hc : ((rec c).runState s).1 = .error .fuelExhausted
    · rw [ite_eq_left hc]
      exact ⟨vs, Nat.le_refl _, fun _ h => by cases h⟩
    · rw [ite_eq_right hc]
      exact hk c s vs ps hc
  have hle : rec ⊑ part := by
    intro c s
    by_cases hc : ((rec c).runState s).1 = .error .fuelExhausted
    · exact .inl (hn c s hc)
    · right
      rw [hpart, ite_eq_right hc]
  intro c s vs ps hne
  rcases evalStep_monotone _ _ hle c s with hi | he
  · exfalso
    apply hne
    unfold EvalM.IsIncompleteAt at hi
    rw [hi]
  · rw [he]
    exact evalStep_sound part hsound c (callPre_mono c) s vs ps

/-! ## The proposed state invariant (stated; its preservation is the obligation) -/

/-- A usable algorithm value: its chain is backed, and a parameter row is owned. -/
def AlgOK (acts : Array ParameterActivation) (a : Algorithm) : Prop :=
  Backed acts a.parent ∧ ParamRowOwned a

/-- A usable context: a non-empty call stack (so every written block is re-wired before use), a
    backed site chain, and usable algorithms on the stack. -/
def CtxOK (acts : Array ParameterActivation) (ctx : EvalCtx) : Prop :=
  ctx.callStack ≠ [] ∧ Backed acts (siteScope? ctx) ∧ ∀ a ∈ ctx.callStack, AlgOK acts a

/-- **THE PROPOSED STATE INVARIANT (activation half).** The two places a state stores a context or an
    algorithm: every stored suspension's caller is usable, and every published CALLABLE identity is.
    With `AddressInvariant.Inv` it is the proposed `K.inv`. It holds of the empty state
    (`storedOK_empty`); that every body keeps it is NOT proved here. -/
def StoredOK (s : EvalState) : Prop :=
  ∀ (a : Nat) (c : NeedCell), s.needs[a]? = some c →
    (∀ source caller values, c.suspension = .expression source caller values →
      CtxOK s.lexicalActivations caller) ∧
    (∀ g, c.callable = .projected (.ok (some g)) → AlgOK s.lexicalActivations g)

theorem storedOK_empty : StoredOK EvalState.empty := by
  intro a c h
  simp [EvalState.empty] at h

/-- An algorithm's own level is unactivated: it is backed exactly when the algorithm's chain is. -/
theorem backed_asScopeCtx (acts : Array ParameterActivation) (a : Algorithm) :
    Backed acts (some a.asScopeCtx) ↔ Backed acts a.parent := by
  unfold Algorithm.asScopeCtx
  simp only [Backed]
  exact ⟨fun h => h.2, fun h => ⟨fun _ hid => (by cases hid), h⟩⟩

/-- The entry context of a run (`runResultM`'s) is usable in every state. -/
theorem entry_ctxOK (acts : Array ParameterActivation) : CtxOK acts { callStack := [preludeAlg] } := by
  have hpre : AlgOK acts preludeAlg := ⟨by show Backed acts none; simp only [Backed], trivial⟩
  refine ⟨by simp, ?_, ?_⟩
  · show Backed acts (some preludeAlg.asScopeCtx)
    exact (backed_asScopeCtx acts preludeAlg).2 hpre.1
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact hpre

theorem AlgOK.ext {s t : EvalState} (h : ActivationPrefix s t) {a : Algorithm}
    (ha : AlgOK s.lexicalActivations a) : AlgOK t.lexicalActivations a := ⟨ha.1.ext h, ha.2⟩

theorem CtxOK.ext {s t : EvalState} (h : ActivationPrefix s t) {ctx : EvalCtx}
    (hc : CtxOK s.lexicalActivations ctx) : CtxOK t.lexicalActivations ctx :=
  ⟨hc.1, hc.2.1.ext h, fun a ha => (hc.2.2 a ha).ext h⟩

/-- The navigation facts of a chase from a usable algorithm, of a parameter read in a usable context,
    and of a projection of a valid address. -/
theorem navFacts_chase {s : EvalState} {a : Algorithm} (ha : AlgOK s.lexicalActivations a) (fc pr : Bool)
    (ctx : EvalCtx) (vis : List String) (last : Option (Algorithm × PropDef)) :
    NavFacts (.resolveAliasChase fc pr a ctx vis last) s := ha

theorem navFacts_parameter {s : EvalState} {ctx : EvalCtx} (hc : CtxOK s.lexicalActivations ctx) (x : Ident) :
    NavFacts (.projectParameterCallable x ctx) s := hc.2.1

/-! ## B1 at the proposed invariant: only the per-body obligation remains -/

/-- Structural inputs sufficient for navigation admission. Other call-site requirements (including
    static well-formedness, exposure completeness and contracts for algorithm-valued results) belong
    to the additional input/result predicates of `navigationContract`; they are NOT discharged here.
    These facts concern the entry arguments, not a run of either evaluator core. -/
def NavigationInputs : EvalCall → EvalState → Prop
  | .resolveAliasChase _ _ a _ _ _, s => AlgOK s.lexicalActivations a
  | .projectParameterCallable _ ctx, s => CtxOK s.lexicalActivations ctx
  | .projectNeedCallable a, s => a < s.needs.size
  | _, _ => True

/-- The proposed state invariant, the proved address contracts, and navigation's structural input
    facts, with room for the remaining static input and value-result contracts. This is a concrete
    contract FAMILY, not a completed table of those remaining contracts or a whole-run theorem. -/
def navigationContract (extraPre : EvalCall → EvalState → Prop)
    (extraPost : (c : EvalCall) → c.Ret → EvalState → Prop) : Contract where
  inv := fun s => Inv s ∧ StoredOK s
  ext := fun s t => s.needs.size ≤ t.needs.size ∧ ActivationPrefix s t
  pre := fun c s => CallPre c s.needs ∧ NavigationInputs c s ∧ extraPre c s
  post := fun c x s => CallPost c x s.needs ∧ extraPost c x s

/-- The proposed state invariant is established at the run's empty state. -/
theorem navigationContract_empty (extraPre : EvalCall → EvalState → Prop)
    (extraPost : (c : EvalCall) → c.Ret → EvalState → Prop) :
    (navigationContract extraPre extraPost).inv EvalState.empty := ⟨empty_inv, storedOK_empty⟩

/-- Admission is derived, not an additional unproved premise of the specialized B1 theorem. -/
theorem navigationContract_admits (extraPre : EvalCall → EvalState → Prop)
    (extraPost : (c : EvalCall) → c.Ret → EvalState → Prop) :
    (navigationContract extraPre extraPost).Admits := by
  intro c s _ _ hp
  have inputs : NavigationInputs c s := hp.2.1
  cases c with
  | resolveAliasChase fc pr a ctx vis last => exact inputs
  | projectParameterCallable x ctx => exact inputs.2.1
  | projectNeedCallable a => exact inputs
  | _ => trivial

/-- **THE ONE UNPROVED PER-BODY OBLIGATION for B1 at the proposed invariant.** Its two halves are
    exactly `Contract.BodySound`, instantiated with `navigationContract`. No admission or navigation
    run is assumed here. No choice of the additional predicates is claimed to satisfy it. -/
def NavigationBodySound (extraPre : EvalCall → EvalState → Prop)
    (extraPost : (c : EvalCall) → c.Ret → EvalState → Prop) : Prop :=
  (navigationContract extraPre extraPost).BodySound

/-- **B1, with only the per-body obligation unproved.** Every completed production navigation of
    any of the nine shapes, from the proposed invariant on its explicit input contract, is a
    navigation-core run. No no-mint premise: minting is relevant only at re-read. -/
theorem navRuns_of_bodySound (extraPre : EvalCall → EvalState → Prop)
    (extraPost : (c : EvalCall) → c.Ret → EvalState → Prop)
    (hbody : NavigationBodySound extraPre extraPost)
    (c : EvalCall) (s : EvalState) (hc : navStatic c = true)
    (hi : (navigationContract extraPre extraPost).inv s)
    (hp : (navigationContract extraPre extraPost).pre c s)
    (hdone : ProductionCompletes (evalUnbounded c) s) :
    NavRuns c s ((evalUnbounded c).runState s) :=
  navRuns_of_contract _ hbody (navigationContract_admits extraPre extraPost) c s hc hi hp hdone

/-! ## The member bridge, relative to the obligation -/

/-- **THE MEMBER BRIDGE with `NavRuns` and CALLABLE normality BOTH discharged from reachability
    facts — relative to the per-body obligation.** `PublishedCallableNormal.member_bridge_of_probe_reached`
    whose premise `NavRuns` of the receiver probe is replaced by: the entry state is invariant and the
    probe satisfies its precondition, for a contract the bodies keep and that admits navigation. Its
    conclusion is the reached bridge's, unchanged. Remaining premises: the receiver path; the probe's
    COMPLETED production run and that it minted nothing (necessary:
    `MemberStabilityGuards.memberOriginRemintsRuntimeIdentity`); production's own dot decision; the
    normal heap; production completes. -/
theorem member_bridge_of_contract (K : Contract) (hbody : K.BodySound) (hadm : K.Admits)
    (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s s' : EvalState) (owner : Algorithm) (p : PropDef)
    (hshape : receiverPath target = true)
    (hi : K.inv s) (hp : K.pre (.resolveDotReceiver? target ctx) s)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok (some owner), s'))
    (hmint : s'.nextRuntimeDeclaration = s.nextRuntimeDeclaration)
    (hsel : selectDotEdge ctx target N (some owner) = .ok (.member owner p))
    (hheap : NormalHeap s.needs)
    (hprod : ProductionCompletes (evalCounted (.dotMember target N fallback (some args)) ctx env) s) :
    (ordinaryCall productionPlanRoute a ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩
        .call).runState s =
      (reCountValueBoundary <$> evalCounted (.dotMember target N fallback (some args)) ctx env).runState s := by
  have hrun : (evalUnbounded (.resolveDotReceiver? target ctx)).runState s = (.ok (some owner), s') := hprobe
  have hnav := navRuns_of_contract K hbody hadm (.resolveDotReceiver? target ctx) s rfl hi hp
    (by unfold ProductionCompletes; rw [hrun]; nofun)
  rw [hrun] at hnav
  exact member_bridge_of_probe_reached a target N fallback args ctx env s s' owner p hshape hnav hmint hsel
    hheap hprod

end KatLang.NavigationContract
