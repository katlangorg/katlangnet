import KatLangArityLaws.NavigationContract
import KatLangArityLaws.PublishedCallableInstances

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.NavigationReread KatLang.NavigationSettled KatLang.NavigationAdmission
open KatLang.NavigationContract

/-!
# The navigation contract: its static premise is necessary, and its facts hold where instances reach (E-18 step 1, M1)

`NavigationContract` reduces "a reachable production navigation is a navigation-core run" to one
per-body obligation of a call contract that gives the navigation facts (`NavFacts`). This module
bounds that reduction from both sides.

## 1. The cell clause needs a STATIC premise the evaluator does not check (`MisExposed`)

`ParamRowOwned` — a parameter-row alias lives under its owner's activation — holds of a source
program because a member that captures an ancestor parameter is LOCAL-ONLY, so the accessibility law
(`memberAccessible?`) refuses it outside that ancestor's activation. The exposure of a member is
metadata of the tree (`PropDef.exposure`); the C# front end computes it, and no pre-evaluation
check of `KatLang.lean` reads it. `MisExposed` is a HOST-BUILT tree whose parameter-row member is
marked exported:

    F(y) = { public A = y ⏎ y }      -- `A` marked `exported`, although its row is the parameter `y`

From the EMPTY state, in the root's own context, production's own operations — the structural
projection of the written path `F.A`, then the structure chase of the member it returns, i.e. the
two steps of the CALLABLE projection of an argument `F.A` (`projectNeedWritten`) — complete, mint
nothing, and are NOT re-read: every chase allocates a binding cell (`mis_exposed_is_not_reread`).
The tree is a legal evaluator input, so the admitted domain of the reachability theorem must carry
the static premise; the SAME tree with the member marked local-only is refused by accessibility
before any chase (`well_exposed_is_refused`). Classification: host-built, not a front-end output,
and no production semantic defect — the evaluator does what the metadata says.

## 2. The hypotheses of B1 are jointly satisfiable (`ProjectionOnly`)

`projectionContract` constrains the CALLABLE projection alone. Its per-body obligation holds
trivially (no navigation BODY has a precondition), it admits navigation, and B1 then returns the
navigation run of a production projection. DEGENERATE on purpose: it exercises the reduction end to
end and shows its premises do not contradict each other; it is not evidence that a contract
covering the eight navigation bodies exists (that is B2).

## 3. The navigation facts hold on the reached instance states (`Reached`)

On the reached states of `PublishedCallableInstances.LinkAncestor` (a CAPTURED-ANCESTOR parameter
read) and `LinkForwardedPath` (a FORWARDED parameter), the reading context's site chain is `Backed`
— decided by a checker (`backedB`, sound: `backedB_sound`) evaluated on the reached state — so
admission of the parameter projection FOLLOWS from the navigation facts (`navFacts_admits`). The
facts are established here by evaluating the reached state, not from the per-body obligation:
evidence that the proposed facts are the right ones, not a proof that every reached state has them.
-/

namespace KatLang.NavigationContractGuards

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

/-! ## 1. A mis-exposed parameter-row member -/

namespace MisExposed

/-- `A = y`, a transparent reference whose row is the enclosing parameter. -/
def rowAlias : Algorithm := .alias none [] [] (.param "y")

/-- The member `A` of `F`, with the given exposure. -/
def member (exposure : PropExposure) : PropDef :=
  { name := "A", alg := rowAlias, isPublic := true, exposure := exposure }

/-- `F(y) = { A = y ⏎ y }`. -/
def owner (exposure : PropExposure) : Algorithm :=
  Algorithm.mk none (Algorithm.normalParameters ["y"]) [] [member exposure] [.param "y"]

/-- The program: a root that declares `F`. -/
def program (exposure : PropExposure) : Expr :=
  .algorithmExpr (Algorithm.mk none [] [] [publicProp "F" (owner exposure)] [.num 0])

/-- The root with the declaration identities `runResultM` assigns. -/
def root (exposure : PropExposure) : Algorithm :=
  match (identifyPropertyExpr (program exposure)).run' 0 with
  | .algorithmExpr a => a
  | _ => preludeAlg

/-- The context of the root's rows: the root as the one level of the call stack. The prelude level
    `runResultM` wires a root under is left out on purpose: it carries no declaration identity, so
    wiring `F`'s member in a chain that ends in it compares two PRINTED scopes of different terms
    (`sameDeclaringScope`'s `reprStr` arm), which no Lean proof decides. Every scope here carries the
    identity `runResultM` assigns, so every comparison is of identities. -/
def ctx (exposure : PropExposure) : EvalCtx := { callStack := [root exposure] }

/-- The written path `F.A`. -/
def path : Expr := .dotMember (.resolve "F") "A" (.resolve "A") none

/-- What the structural projection of `F.A` returns in the mis-exposed program. -/
def wired : Algorithm :=
  match ((projectNeedStructuralMember path (ctx .exported)).runState EvalState.empty).1 with
  | .ok (some a) => a
  | _ => preludeAlg

/-- The exit states of the member's structure chase from the empty state, and of a second chase. -/
def once : EvalState := ((resolveAliasStructure wired (ctx .exported)).runState EvalState.empty).2
def twice : EvalState := ((resolveAliasStructure wired (ctx .exported)).runState once).2

theorem facts :
    ((projectNeedStructuralMember path (ctx .exported)).runState EvalState.empty =
      (.ok (some wired), EvalState.empty)) ∧
    ((resolveAliasStructure wired (ctx .exported)).runState EvalState.empty = (.ok none, once)) ∧
    (once.needs.size = 1) ∧ (once.nextRuntimeDeclaration = 0) ∧
    ((resolveAliasStructure wired (ctx .exported)).runState once = (.ok none, twice)) ∧
    (twice.needs.size = 2) ∧
    (paramRowAdmits wired (ctx .exported) EvalState.empty = false) ∧
    ((projectNeedWritten path (ctx .exported)).runState EvalState.empty = (.ok none, once)) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))

/-- The member production returns is the alias, wired where the path found it. -/
theorem projected : (projectNeedStructuralMember path (ctx .exported)).runState EvalState.empty =
    (.ok (some wired), EvalState.empty) := facts.1

/-- The CALLABLE projection of the written argument `F.A` is those two steps, and allocates. -/
theorem written_projection : (projectNeedWritten path (ctx .exported)).runState EvalState.empty =
    (.ok none, once) := facts.2.2.2.2.2.2.2

/-- The navigation facts FAIL of that chase: the alias is not under its owner's activation. -/
theorem navFacts_fail :
    ¬ NavFacts (.resolveAliasChase false true wired (ctx .exported) [] none) EvalState.empty := by
  intro h
  have hadm : paramRowAdmits wired (ctx .exported) EvalState.empty = true :=
    navFacts_admits (.resolveAliasChase false true wired (ctx .exported) [] none) EvalState.empty rfl h
  rw [facts.2.2.2.2.2.2.1] at hadm
  cases hadm

/-- The specialized B1 contract excludes this HOST-BUILT counterexample at its entry, whatever
    additional static input and result contracts B2 eventually selects. -/
theorem outside_navigationContract (extraPre : EvalCall → EvalState → Prop)
    (extraPost : (c : EvalCall) → c.Ret → EvalState → Prop) :
    ¬ (navigationContract extraPre extraPost).pre
      (.resolveAliasChase false true wired (ctx .exported) [] none) EvalState.empty := by
  intro hp
  exact navFacts_fail (navigationContract_admits extraPre extraPost _ _ rfl
    (navigationContract_empty extraPre extraPost) hp)

/-- **NEGATIVE CONTROL: the static premise of the cell clause is necessary.** In a host-built tree
    whose parameter-row member is marked EXPORTED, production reaches — from the empty state, by its
    own operations on the program's own written path — a completed, non-minting structure chase that
    is NOT re-read (every run allocates a binding cell) and is no navigation run. Host-built: the
    evaluator's pre-evaluation checks do not read `PropDef.exposure`. -/
theorem mis_exposed_is_not_reread :
    (projectNeedStructuralMember path (ctx .exported)).runState EvalState.empty =
      (.ok (some wired), EvalState.empty) ∧
    (resolveAliasStructure wired (ctx .exported)).runState EvalState.empty = (.ok none, once) ∧
    once.nextRuntimeDeclaration = EvalState.empty.nextRuntimeDeclaration ∧
    (resolveAliasStructure wired (ctx .exported)).runState once ≠ (.ok none, once) ∧
    ¬ NavRuns (.resolveAliasStructure wired (ctx .exported)) EvalState.empty (.ok none, once) := by
  have hne : once ≠ twice := by
    intro h
    have h1 := facts.2.2.1
    have h2 := facts.2.2.2.2.2.1
    rw [← h] at h2
    omega
  refine ⟨facts.1, facts.2.1, facts.2.2.2.1, ?_, ?_⟩
  · rw [facts.2.2.2.2.1]
    intro h
    exact hne (Prod.mk.inj h).2.symm
  · intro hnav
    have h := ((navigation_reread _ EvalState.empty once _ hnav facts.2.2.2.1).2 once (NavExt.refl once)).1
    have h1 : (resolveAliasStructure wired (ctx .exported)).runState once = (.ok none, once) := h
    rw [facts.2.2.2.2.1] at h1
    exact hne (Prod.mk.inj h1).2.symm

/-- The exposure a front end gives the member: it captures the ancestor parameter `y`. -/
def localOnly : PropExposure := .localCapturedAncestorParams ["y"]

/-- **POSITIVE CONTROL: with the member marked local-only, accessibility refuses the path** — from
    the same state, in the same context, before any chase: nothing is allocated. -/
theorem well_exposed_is_refused :
    (projectNeedStructuralMember path (ctx localOnly)).runState EvalState.empty =
      (.error (.localOnlyProperty "F" "A" localOnly), EvalState.empty) := by
  cbv

end MisExposed

/-! ## 2. The hypotheses of B1 are jointly satisfiable -/

namespace ProjectionOnly

/-- A contract of the CALLABLE projection alone: its address is inside the heap. -/
def projectionContract : Contract where
  inv := fun _ => True
  ext := fun _ _ => True
  pre := fun c s => ∃ a, c = .projectNeedCallable a ∧ a < s.needs.size
  post := fun _ _ _ => True

theorem bodySound : projectionContract.BodySound := by
  intro rec _ _
  refine ⟨fun c s _ _ _ => ⟨trivial, trivial, fun _ _ => trivial⟩, ?_⟩
  intro c s hnav _ hp _
  obtain ⟨a, rfl, -⟩ := hp
  cases hnav

theorem admits : projectionContract.Admits := by
  intro c s _ _ hp
  obtain ⟨a, rfl, ha⟩ := hp
  exact ha

/-- B1 at the degenerate contract: a completed production projection of an address inside the heap
    is a navigation run. -/
theorem projection_navRuns (a : Nat) (s : EvalState) (ha : a < s.needs.size)
    (hdone : ProductionCompletes (projectNeedCallable a) s) :
    NavRuns (.projectNeedCallable a) s ((projectNeedCallable a).runState s) :=
  navRuns_of_contract projectionContract bodySound admits (.projectNeedCallable a) s rfl trivial ⟨a, rfl, ha⟩ hdone

/-- … and it is not vacuous: the memo read of `NavigationAdmission.grown`. -/
theorem grown_navRuns : NavRuns (.projectNeedCallable 0) grown (.ok none, grown) := by
  have hrun : (projectNeedCallable 0).runState grown = (.ok none, grown) := address_fault_is_not_reread.2.1
  have h := projection_navRuns 0 grown (by decide) (by unfold ProductionCompletes; rw [hrun]; nofun)
  rw [hrun] at h
  exact h

end ProjectionOnly

/-! ## 3. The navigation facts on reached instance states -/

/-- One level: an activated level names a record that binds its parameters. -/
def levelB (acts : Array ParameterActivation) (params : List Ident) : Option Nat → Bool
  | none => true
  | some id =>
      match acts[id]? with
      | none => false
      | some act => params.all (fun y => (lookupAssoc y act.needs).isSome)

/-- A decision procedure for `Backed`. -/
def backedB (acts : Array ParameterActivation) : Option ScopeCtx → Bool
  | none => true
  | some (.mk parent params _ _ _ _ activation _) => levelB acts params activation && backedB acts parent

theorem levelB_sound {acts : Array ParameterActivation} {params : List Ident} {id : Nat}
    (h : levelB acts params (some id) = true) :
    ∃ act, acts[id]? = some act ∧ ∀ y, params.contains y = true → (lookupAssoc y act.needs).isSome = true := by
  have h' : (match acts[id]? with
      | none => false
      | some act => params.all (fun y => (lookupAssoc y act.needs).isSome)) = true := h
  cases hact : acts[id]? with
  | none => rw [hact] at h'; cases h'
  | some act =>
    rw [hact] at h'
    exact ⟨act, rfl, fun y hy => (List.all_eq_true.mp h') y (List.contains_iff_mem.mp hy)⟩

theorem backedB_sound {acts : Array ParameterActivation} :
    ∀ {chain : Option ScopeCtx}, backedB acts chain = true → Backed acts chain
  | none, _ => by simp only [Backed]
  | some (.mk parent params _ _ _ _ activation _), h => by
      simp only [backedB, Bool.and_eq_true] at h
      simp only [Backed]
      refine ⟨fun id hid => ?_, backedB_sound (chain := parent) h.2⟩
      subst hid
      exact levelB_sound h.1

namespace Reached

open KatLang.PublishedCallableInstances

/-- **CAPTURED ANCESTOR, reached.** On the reached state of `LinkAncestor` the reading context's
    site chain is backed, so the navigation core's admission of the head parameter's projection
    follows from the navigation facts. -/
theorem ancestor_backed :
    Backed LinkAncestor.entry.lexicalActivations (siteScope? LinkAncestor.ctxIn) :=
  backedB_sound (by cbv)

theorem ancestor_admitted :
    navAdmits (.projectParameterCallable "c" LinkAncestor.ctxIn) LinkAncestor.entry = true :=
  navFacts_admits _ _ rfl ancestor_backed

/-- … and the fact is not trivially true there: the chain names a record (the head parameter is read
    through a captured activation), so over an activation array without it the chain is NOT backed. -/
theorem ancestor_backed_needs_the_record :
    ¬ Backed (#[] : Array ParameterActivation) (siteScope? LinkAncestor.ctxIn) := by
  intro h
  have hanch := anchored_of_chainRecorded "c" LinkAncestor.ctxIn ({} : EvalState) (Backed.chainRecorded h)
  unfold anchored at hanch
  cases hid : capturedId? "c" LinkAncestor.ctxIn with
  | none =>
    have := LinkAncestor.captured_ancestor.1
    rw [hid] at this
    cases this
  | some id =>
    rw [hid] at hanch
    exact absurd (of_decide_eq_true hanch) (Nat.not_lt_zero id)

/-- **FORWARDED PARAMETER, reached.** The same on the reached state of `LinkForwardedPath`. -/
theorem forwarded_backed :
    Backed LinkForwardedPath.entry.lexicalActivations (siteScope? LinkForwardedPath.ctxIn) :=
  backedB_sound (by cbv)

theorem forwarded_admitted :
    navAdmits (.projectParameterCallable "b" LinkForwardedPath.ctxIn) LinkForwardedPath.entry = true :=
  navFacts_admits _ _ rfl forwarded_backed

end Reached

end KatLang.NavigationContractGuards
