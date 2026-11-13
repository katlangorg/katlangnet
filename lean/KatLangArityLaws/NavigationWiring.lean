import KatLangArityLaws.NavigationContract
import KatLangArityLaws.TotalLeaves

open KatLang KatLang.MemberStability KatLang.NavigationReread KatLang.NavigationAdmission
open KatLang.NavigationContract
open KatLang.OwnerContextStability (ActivationPrefix)

/-!
# Where a backed chain comes from: the context wiring of navigation (ledger E-18, step 1, B2 preparation)

`NavigationContract` proposes, for the ACTIVATION clause of navigation admission, that every scope
chain an algorithm or a context carries is `Backed`: each ACTIVATED level names a recorded
activation that binds every parameter of the level. This module proves, helper by helper, where
that fact comes from and that every wiring helper of the evaluator keeps it. Nothing here is about
the CELL clause's `ParamRowOwned`: the B2 preparation found a source program that broke it; since
the anchoring of a container's chain (2026-11-13) that program keeps it
(`NavigationSourceDomainGuards`), and it is not proved in general.

## 1. The written tree carries no activation index (`identify_noAct`)

`runResultM` evaluates `(identifyPropertyExpr e).run' 0`. The identity pass rebuilds every scope
level with `activation := none` (`identifyPropertyScope`), at every depth, so every algorithm of
the prepared program — whatever a host put in a parent slot — has an activation-free chain
(`noActExpr`), and an activation-free chain is backed in EVERY state (`backed_of_noAct`). This is
the static fact the three uses that take a parent from the written tree need (below: 1, 2, 7).

## 2. The seven uses of a nested algorithm without in-context re-wiring

| use | what establishes its chain |
| --- | --- |
| 1. `wireToCaller` on an empty call stack — the block as written | host-only: no evaluator context is empty (`CtxOK` carries a non-empty stack); the written chain is activation-free (`backed_wireToCaller`'s third premise, from § 1) |
| 2. `wireOpenBlockToGlobalScope` on a pre-parented block — its own parent | the written tree: activation-free (§ 1); an unparented block is wired under the stack's root level (`backed_wireOpenBlockToGlobalScope`) |
| 3. `Algorithm.childOf` — static wiring under an unactivated level | the parent algorithm's own chain (`backed_childOf`) |
| 4. `Algorithm.withParent` at a module root — the chain's root level | a level of the chain it is given (`Backed.chainRoot`, `backed_withParent`) |
| 5. `lookupInParentsDirect` / `lookupInParentsStructuralProperty` — the level as found | a level of the chain walked (`backed_lookupInParentsDirect`, `backed_lookupInParentsStructuralProperty`) |
| 6. `Algorithm.forOpens` — an algorithm over a chain level | that level (`backed_forOpens`) |
| 7. a builtin argument without a cell — used as given | host-only (the hand-built fixture seam: a source call supplies every argument through a cell); the written chain is activation-free (§ 1) |

In-context wiring (`scopeInContext`, `childOfInContext`, `wireToCaller` on a non-empty stack) picks a
level of the site chain or the parent's own over its anchored chain, whose levels are kept levels,
activated site levels or re-parented static ones (`backed_anchorChain`, `backed_scopeInContext`,
`backed_childOfInContext`).

## 3. Where an ACTIVATED level comes from

Two operations mint an activation, and each records it: body entry (`enterAlgorithmBody`) and
family dispatch (`wireSelectedBranchBody`). The record binds the level's parameters exactly when
the entering context's need tier does (`recorded_binds`): the binder's coverage of the callee's
names is the one fact these lemmas take as a premise (`enterAlgorithmBody_backed`,
`wireSelectedBranchBody_backed`). It is NOT proved here that every entry happens with that
coverage — that is a result contract of the binder, part of the per-body obligation.

## NOT proved here

The per-body obligation (`NavigationBodySound`); that stored suspensions and published CALLABLE
identities keep these facts (`StoredOK`); anything about the cell clause; anything about C#.
-/

namespace KatLang.NavigationWiring

/-! ## Backed chains under the wiring helpers -/

theorem Backed.parent {acts : Array ParameterActivation} {sc : ScopeCtx} (h : Backed acts (some sc)) :
    Backed acts sc.parent := by
  cases sc
  simp only [Backed] at h
  exact h.2

/-- The chain's root level is backed (use 4: a module is wired there). -/
theorem Backed.chainRoot {acts : Array ParameterActivation} :
    ∀ {chain : Option ScopeCtx}, Backed acts chain → ∀ sc, chain = some sc → Backed acts (some sc.chainRoot)
  | none, _, _, h => by cases h
  | some (.mk none params opens props output branches activation id), hb, sc, h => by
      cases h
      rw [ScopeCtx.chainRoot]
      exact hb
  | some (.mk (some parent) params opens props output branches activation id), hb, sc, h => by
      cases h
      simp only [Backed] at hb
      rw [ScopeCtx.chainRoot]
      exact Backed.chainRoot (chain := some parent) hb.2 parent rfl

theorem backed_map_chainRoot {acts : Array ParameterActivation} {p : Option ScopeCtx} (h : Backed acts p) :
    Backed acts (p.map ScopeCtx.chainRoot) := by
  cases p with
  | none => exact h
  | some sc => exact Backed.chainRoot h sc rfl

/-- **`Algorithm.withParent` keeps a backed chain** (uses 3–6 all wire through it): the wired
    algorithm's chain is the given one, its root level (a module), or none (a builtin). -/
theorem backed_withParent {acts : Array ParameterActivation} (a : Algorithm) {p : Option ScopeCtx}
    (h : Backed acts p) : Backed acts (a.withParent p).parent := by
  unfold Algorithm.withParent
  split <;> first
    | exact h
    | exact backed_map_chainRoot h
    | (show Backed acts none; simp only [Backed])

/-- Use 3: static wiring under the parent algorithm's own (unactivated) level. -/
theorem backed_childOf {acts : Array ParameterActivation} (a child : Algorithm) (h : Backed acts a.parent) :
    Backed acts (Algorithm.childOf a child).parent :=
  backed_withParent child ((backed_asScopeCtx acts a).2 h)

/-- Use 6: the lookup wrapper over a chain level. -/
theorem backed_forOpens {acts : Array ParameterActivation} (sc : ScopeCtx) (h : Backed acts (some sc)) :
    Backed acts (Algorithm.forOpens sc).parent := h

/-- The active declaration found on a backed chain is a level of it. -/
theorem backed_activeDeclaration {acts : Array ParameterActivation} (required : ScopeCtx) :
    ∀ {chain : Option ScopeCtx}, Backed acts chain → ∀ sc, activeDeclaration? required chain = some sc →
      Backed acts (some sc)
  | none, _, _, h => by simp only [activeDeclaration?] at h; cases h
  | some (.mk parent params opens props output branches activation id), hb, sc, h => by
      simp only [activeDeclaration?] at h
      split at h
      · cases h
        exact hb
      · simp only [Backed] at hb
        exact backed_activeDeclaration required (chain := parent) hb.2 sc h

/-- The activated declaration found on a backed chain is a level of it. -/
theorem backed_activatedDeclaration {acts : Array ParameterActivation} (required : ScopeCtx) :
    ∀ {chain : Option ScopeCtx}, Backed acts chain → ∀ sc, activatedDeclaration? required chain = some sc →
      Backed acts (some sc)
  | none, _, _, h => by simp only [activatedDeclaration?] at h; cases h
  | some (.mk parent params opens props output branches activation id), hb, sc, h => by
      simp only [activatedDeclaration?] at h
      split at h
      · cases h
        exact hb
      · simp only [Backed] at hb
        exact backed_activatedDeclaration required (chain := parent) hb.2 sc h

/-- **The anchored chain of a backed chain is backed** on a backed site: each of its levels is a kept
    level of the chain, an activated level of the site chain, or a static level of the chain over its
    anchored parent. -/
theorem backed_anchorChain {acts : Array ParameterActivation} {site : Option ScopeCtx}
    (hs : Backed acts site) : ∀ {chain : Option ScopeCtx}, Backed acts chain →
      Backed acts (anchorChain site chain)
  | none, _ => by simp only [anchorChain, Backed]
  | some (.mk parent params opens props output branches activation id), hb => by
      have hre : Backed acts (some (.mk (anchorChain site parent) params opens props output branches
          activation id)) := by
        simp only [Backed] at hb ⊢
        exact ⟨hb.1, backed_anchorChain hs hb.2⟩
      simp only [anchorChain]
      split
      · exact hb
      · split
        · rename_i active hact
          exact backed_activatedDeclaration _ hs active hact
        · exact hre

/-- **In-context wiring picks a backed level**: the algorithm's active declaration on the site chain,
    or its own unactivated level over its anchored chain. -/
theorem backed_scopeInContext {acts : Array ParameterActivation} (a : Algorithm) (ctx : EvalCtx)
    (ha : Backed acts a.parent) (hs : Backed acts (siteScope? ctx)) :
    Backed acts (some (scopeInContext a ctx)) := by
  have hown : Backed acts (some a.asScopeCtx) := (backed_asScopeCtx acts a).2 ha
  simp only [scopeInContext]
  split
  · exact hown
  · split
    · rename_i sc hact
      exact backed_activeDeclaration a.asScopeCtx hs sc hact
    · simp only [Backed]
      exact ⟨fun _ hid => (by cases hid), backed_anchorChain hs ha⟩

theorem backed_childOfInContext {acts : Array ParameterActivation} (parent child : Algorithm) (ctx : EvalCtx)
    (hp : Backed acts parent.parent) (hs : Backed acts (siteScope? ctx)) :
    Backed acts (childOfInContext parent child ctx).parent :=
  backed_withParent child (backed_scopeInContext parent ctx hp hs)

/-- **Uses 1 and the ordinary case of `wireToCaller`.** Under a non-empty stack the block is wired in
    context; on an empty stack (no evaluator context is one) it is the block as written, whose own
    chain must be backed — an activation-free written chain is (`backed_of_noAct`). -/
theorem backed_wireToCaller {acts : Array ParameterActivation} (ctx : EvalCtx) (a : Algorithm)
    (hstack : ∀ caller, ctx.callStack.head? = some caller → Backed acts caller.parent)
    (hs : Backed acts (siteScope? ctx))
    (hwritten : ctx.callStack.head? = none → Backed acts a.parent) :
    Backed acts (wireToCaller ctx a).parent := by
  unfold wireToCaller
  cases hhead : ctx.callStack.head? with
  | none => exact hwritten hhead
  | some caller => exact backed_childOfInContext caller a ctx (hstack caller hhead) hs

/-- **Use 2.** An open block that already has a parent keeps it (the written tree's); an unparented
    one is wired under the stack's root level. -/
theorem backed_wireOpenBlockToGlobalScope {acts : Array ParameterActivation} (ctx : EvalCtx) (a : Algorithm)
    (hwritten : Backed acts a.parent) (hstack : ∀ g ∈ ctx.callStack, Backed acts g.parent) :
    Backed acts (wireOpenBlockToGlobalScope ctx a).parent := by
  unfold wireOpenBlockToGlobalScope
  split
  · rename_i g _ hg
    have hmem : g ∈ ctx.callStack := by
      have := List.mem_of_mem_head? hg
      exact List.mem_reverse.mp this
    exact backed_childOf g a (hstack g hmem)
  · exact hwritten

/-- **Use 5 (direct).** The member `lookupInParentsDirect` finds is wired under the level it was
    found in, a level of the chain walked. -/
theorem backed_lookupInParentsDirect {acts : Array ParameterActivation} (name : Ident) :
    ∀ {chain : Option ScopeCtx}, Backed acts chain → ∀ sc, chain = some sc →
      ∀ r, lookupInParentsDirect sc name = some r → Backed acts r.parent
  | none, _, _, h, _, _ => by cases h
  | some (.mk parent params opens props output branches activation id), hb, sc, h, r, hr => by
      cases h
      rw [KatLang.TotalLeaves.lookupInParentsDirect_equation] at hr
      split at hr
      · cases hr
        exact backed_withParent _ hb
      · cases hp : parent with
        | none =>
          simp only [ScopeCtx.parent, hp] at hr
          cases hr
        | some par =>
          simp only [ScopeCtx.parent, hp] at hr
          simp only [Backed] at hb
          exact backed_lookupInParentsDirect name (chain := parent) hb.2 par hp r hr

/-- **Use 5 (structural).** The binding `lookupInParentsStructuralProperty` finds: its algorithm is
    wired under the level found, and the owner rebuilt from that level carries the level's own chain. -/
theorem backed_lookupInParentsStructuralProperty {acts : Array ParameterActivation} (name : Ident) :
    ∀ {chain : Option ScopeCtx}, Backed acts chain → ∀ sc, chain = some sc →
      ∀ r, lookupInParentsStructuralProperty sc name = some r →
        Backed acts r.alg.parent ∧ Backed acts r.owner.parent
  | none, _, _, h, _, _ => by cases h
  | some (.mk none params opens props output branches activation id), hb, sc, h, r, hr => by
      cases h
      unfold lookupInParentsStructuralProperty at hr
      split at hr
      · cases hr
        exact ⟨backed_withParent _ hb, by show Backed acts none; simp only [Backed]⟩
      · cases hr
  | some (.mk (some par) params opens props output branches activation id), hb, sc, h, r, hr => by
      cases h
      unfold lookupInParentsStructuralProperty at hr
      split at hr
      · cases hr
        refine ⟨backed_withParent _ hb, ?_⟩
        simp only [Backed] at hb
        exact hb.2
      · simp only [Backed] at hb
        exact backed_lookupInParentsStructuralProperty name (chain := some par) hb.2 par rfl r hr

/-! ## An activation-free chain is backed in every state -/

mutual
  /-- No scope level of the expression's tree carries an activation index. -/
  def noActExpr : Expr → Bool
    | .param _ => true
    | .num _ => true
    | .stringLiteral _ => true
    | .boolLiteral _ => true
    | .resolve _ => true
    | .emptySequence _ => true
    | .unary _ e => noActExpr e
    | .binary _ a b => noActExpr a && noActExpr b
    | .comparison first links => noActExpr first && noActLinks links
    | .index a selectors => noActExpr a && noActExprs selectors
    | .sequenceConstruct a b => noActExpr a && noActExpr b
    | .sequenceSpread e => noActExpr e
    | .listLiteral items => noActExprs items
    | .capture rows => noActExprs rows
    | .algorithmExpr a => noActAlg a
    | .call f args => noActExpr f && noActExprs args
    | .dotMember target _ fallback none => noActExpr target && noActExpr fallback
    | .dotMember target _ fallback (some args) => noActExpr target && noActExpr fallback && noActExprs args

  def noActExprs : List Expr → Bool
    | [] => true
    | e :: rest => noActExpr e && noActExprs rest

  def noActLinks : List ComparisonLink → Bool
    | [] => true
    | ⟨_, operand⟩ :: rest => noActExpr operand && noActLinks rest

  def noActAlg : Algorithm → Bool
    | .builtin _ => true
    | .mk parent _ opens props output _ =>
        noActParent parent && noActExprs opens && noActProps props && noActExprs output
    | .conditional parent opens branches _ => noActParent parent && noActExprs opens && noActBranches branches
    | .alias parent opens props target _ _ =>
        noActParent parent && noActExprs opens && noActProps props && noActExpr target

  def noActProps : List PropDef → Bool
    | [] => true
    | ⟨_, a, _, _, _, _⟩ :: rest => noActAlg a && noActProps rest

  def noActBranches : List CondBranch → Bool
    | [] => true
    | ⟨_, body⟩ :: rest => noActAlg body && noActBranches rest

  def noActParent : Option ScopeCtx → Bool
    | none => true
    | some scope => noActScope scope

  def noActScope : ScopeCtx → Bool
    | .mk parent _ opens props output branches activation _ =>
        activation.isNone && noActParent parent && noActExprs opens && noActProps props &&
          noActExprs output && noActBranches branches
end

/-- **An activation-free chain is backed over every activation array**: `Backed` constrains
    activated levels only. -/
theorem backed_of_noAct (acts : Array ParameterActivation) :
    ∀ {chain : Option ScopeCtx}, noActParent chain = true → Backed acts chain
  | none, _ => by simp only [Backed]
  | some (.mk parent params opens props output branches activation id), h => by
      simp only [noActParent, noActScope, Bool.and_eq_true] at h
      simp only [Backed]
      refine ⟨fun i hi => ?_, backed_of_noAct acts (chain := parent) h.1.1.1.1.2⟩
      have hnone := h.1.1.1.1.1
      rw [hi] at hnone
      cases hnone

theorem noActAlg_parent {a : Algorithm} (h : noActAlg a = true) : noActParent a.parent = true := by
  cases a with
  | builtin b => rfl
  | mk parent pats opens props output id =>
    simp only [noActAlg, Bool.and_eq_true] at h
    exact h.1.1.1
  | conditional parent opens branches id =>
    simp only [noActAlg, Bool.and_eq_true] at h
    exact h.1.1
  | «alias» parent opens props target id reference =>
    simp only [noActAlg, Bool.and_eq_true] at h
    exact h.1.1.1

/-- A written algorithm of an activation-free tree is usable where it stands (uses 1, 2, 7): its own
    chain is backed in every state. -/
theorem backed_of_noActAlg (acts : Array ParameterActivation) {a : Algorithm} (h : noActAlg a = true) :
    Backed acts a.parent := backed_of_noAct acts (noActAlg_parent h)

/-! ## The identity pass leaves no activation index

`runResultM` evaluates `(identifyPropertyExpr e).run' 0`. The pass is a counter-threading walk; every
result it returns, whatever the counter, is activation-free: `identifyPropertyScope` writes
`activation := none` at every level it rebuilds, and every parent slot is rebuilt by it. -/

/-- Every result of the counter-threading computation satisfies `P`, whatever the counter. -/
def Post {α : Type} (m : StateM Nat α) (P : α → Prop) : Prop := ∀ n, P (m.run n).1

theorem Post.pure {α : Type} {P : α → Prop} (a : α) (h : P a) : Post (Pure.pure a : StateM Nat α) P := fun _ => h

theorem Post.bind {α β : Type} {P : α → Prop} {Q : β → Prop} {m : StateM Nat α} {f : α → StateM Nat β}
    (hm : Post m P) (hf : ∀ a, P a → Post (f a) Q) : Post (m >>= f) Q := by
  intro n
  have h : ((m >>= f).run n) = (f (m.run n).1).run (m.run n).2 := rfl
  rw [h]
  exact hf _ (hm n) _

theorem Post.map {α β : Type} {P : α → Prop} {Q : β → Prop} {m : StateM Nat α} (f : α → β)
    (hm : Post m P) (h : ∀ a, P a → Q (f a)) : Post (f <$> m) Q := by
  intro n
  have e : ((f <$> m).run n) = (f (m.run n).1, (m.run n).2) := rfl
  rw [e]
  exact h _ (hm n)

theorem Post.modifyGet {α : Type} (f : Nat → α × Nat) : Post (modifyGet f : StateM Nat α) (fun _ => True) :=
  fun _ => trivial

theorem Post.mapM {α β : Type} {P : β → Prop} {f : α → StateM Nat β} :
    ∀ (xs : List α), (∀ x ∈ xs, Post (f x) P) → Post (xs.mapM f) (fun ys => ∀ y ∈ ys, P y)
  | [], _ => by
      rw [List.mapM_nil]
      exact Post.pure _ (fun _ h => by cases h)
  | x :: rest, h => by
      rw [List.mapM_cons]
      exact Post.bind (h x List.mem_cons_self) (fun y hy =>
        Post.bind (Post.mapM rest (fun z hz => h z (List.mem_cons_of_mem _ hz))) (fun ys hys =>
          Post.pure _ (by
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hy
            · exact hys z hz)))

theorem noActExprs_of : ∀ (xs : List Expr), (∀ x ∈ xs, noActExpr x = true) → noActExprs xs = true
  | [], _ => rfl
  | x :: rest, h => by
      simp only [noActExprs, Bool.and_eq_true]
      exact ⟨h x List.mem_cons_self, noActExprs_of rest (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

theorem noActLinks_of : ∀ (xs : List ComparisonLink), (∀ x ∈ xs, noActExpr x.operand = true) → noActLinks xs = true
  | [], _ => rfl
  | ⟨op, operand⟩ :: rest, h => by
      simp only [noActLinks, Bool.and_eq_true]
      exact ⟨h ⟨op, operand⟩ List.mem_cons_self, noActLinks_of rest (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

theorem noActProps_of : ∀ (xs : List PropDef), (∀ x ∈ xs, noActAlg x.alg = true) → noActProps xs = true
  | [], _ => rfl
  | ⟨name, a, isPublic, exposure, identity, positions⟩ :: rest, h => by
      simp only [noActProps, Bool.and_eq_true]
      exact ⟨h ⟨name, a, isPublic, exposure, identity, positions⟩ List.mem_cons_self,
        noActProps_of rest (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

theorem noActBranches_of : ∀ (xs : List CondBranch), (∀ x ∈ xs, noActAlg x.body = true) → noActBranches xs = true
  | [], _ => rfl
  | ⟨pattern, body⟩ :: rest, h => by
      simp only [noActBranches, Bool.and_eq_true]
      exact ⟨h ⟨pattern, body⟩ List.mem_cons_self,
        noActBranches_of rest (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

/-- The four statements of the identity pass, for every tree smaller than `k`. -/
def IdentifyNoAct (k : Nat) : Prop :=
  (∀ e : Expr, sizeOf e < k → Post (identifyPropertyExpr e) (fun r => noActExpr r = true)) ∧
  (∀ a : Algorithm, sizeOf a < k → Post (identifyPropertyAlgorithm a) (fun r => noActAlg r = true)) ∧
  (∀ sc : ScopeCtx, sizeOf sc < k → Post (identifyPropertyScope sc) (fun r => noActScope r = true)) ∧
  (∀ p : PropDef, sizeOf p < k → Post (identifyPropertyDefinition p) (fun r => noActAlg r.alg = true))

theorem Post.conseq {α : Type} {P Q : α → Prop} {m : StateM Nat α} (hm : Post m P) (h : ∀ a, P a → Q a) :
    Post m Q := fun n => h _ (hm n)

/-- What the walk of an optional argument list returns. -/
def noActOptExprs : Option (List Expr) → Bool
  | none => true
  | some items => noActExprs items

theorem identifyNoAct : ∀ k, IdentifyNoAct k := by
  intro k
  induction k with
  | zero => exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨ihE, ihA, ihS, ihP⟩ := ih
    -- the element-wise walks of the four list shapes, for a list inside a tree of size at most `k`
    have exprs : ∀ (xs : List Expr), sizeOf xs ≤ k →
        Post (xs.mapM identifyPropertyExpr) (fun ys => noActExprs ys = true) := fun xs hxs =>
      (Post.mapM xs (fun x hx => ihE x (by have := List.sizeOf_lt_of_mem hx; omega))).conseq noActExprs_of
    have props : ∀ (xs : List PropDef), sizeOf xs ≤ k →
        Post (xs.mapM identifyPropertyDefinition) (fun ys => noActProps ys = true) := fun xs hxs =>
      (Post.mapM xs (fun x hx => ihP x (by have := List.sizeOf_lt_of_mem hx; omega))).conseq noActProps_of
    have branches : ∀ (xs : List CondBranch), sizeOf xs ≤ k →
        Post (xs.mapM fun b => do return { b with body := (← identifyPropertyAlgorithm b.body) })
          (fun ys => noActBranches ys = true) := fun xs hxs =>
      (Post.mapM (P := fun b => noActAlg b.body = true) xs (fun x hx =>
        Post.bind (ihA x.body (by
          have := List.sizeOf_lt_of_mem hx
          have := CondBranch.sizeOf_body_lt x
          omega)) (fun r hr => Post.pure _ hr))).conseq noActBranches_of
    have links : ∀ (xs : List ComparisonLink), sizeOf xs ≤ k →
        Post (xs.mapM fun link => do return { link with operand := (← identifyPropertyExpr link.operand) })
          (fun ys => noActLinks ys = true) := fun xs hxs =>
      (Post.mapM (P := fun l => noActExpr l.operand = true) xs (fun x hx =>
        Post.bind (ihE x.operand (by
          have := List.sizeOf_lt_of_mem hx
          have := ComparisonLink.sizeOf_operand_lt x
          omega)) (fun r hr => Post.pure _ hr))).conseq noActLinks_of
    have noParent : Post (Pure.pure none : StateM Nat (Option ScopeCtx)) (fun r => noActParent r = true) :=
      Post.pure none rfl
    have someParent : ∀ (sc : ScopeCtx), sizeOf sc < k →
        Post (some <$> identifyPropertyScope sc) (fun r => noActParent r = true) := fun sc hsc =>
      Post.map some (ihS sc hsc) (fun r hr => hr)
    refine ⟨?_, ?_, ?_, ?_⟩
    -- expressions
    · intro e hsz
      cases e with
      | param x => rw [identifyPropertyExpr]; exact Post.pure _ rfl
      | num n => rw [identifyPropertyExpr]; exact Post.pure _ rfl
      | stringLiteral t => rw [identifyPropertyExpr]; exact Post.pure _ rfl
      | boolLiteral b => rw [identifyPropertyExpr]; exact Post.pure _ rfl
      | resolve n => rw [identifyPropertyExpr]; exact Post.pure _ rfl
      | emptySequence n => rw [identifyPropertyExpr]; exact Post.pure _ rfl
      | unary op e =>
        simp only [Expr.unary.sizeOf_spec] at hsz
        rw [identifyPropertyExpr]
        exact Post.bind (ihE e (by omega)) (fun r hr => Post.pure _ (by simp only [noActExpr]; exact hr))
      | binary op a b =>
        simp only [Expr.binary.sizeOf_spec] at hsz
        rw [identifyPropertyExpr]
        exact Post.bind (ihE a (by omega)) (fun ra ha => Post.bind (ihE b (by omega)) (fun rb hb =>
          Post.pure _ (by simp only [noActExpr, Bool.and_eq_true]; exact ⟨ha, hb⟩)))
      | comparison first ls =>
        simp only [Expr.comparison.sizeOf_spec] at hsz
        rw [identifyPropertyExpr]
        exact Post.bind (ihE first (by omega)) (fun rf hf => Post.bind (links ls (by omega)) (fun rl hl =>
          Post.pure _ (by simp only [noActExpr, Bool.and_eq_true]; exact ⟨hf, hl⟩)))
      | index a bs =>
        simp only [Expr.index.sizeOf_spec] at hsz
        rw [identifyPropertyExpr]
        exact Post.bind (ihE a (by omega)) (fun ra ha => Post.bind (exprs bs (by omega)) (fun rb hb =>
          Post.pure _ (by simp only [noActExpr, Bool.and_eq_true]; exact ⟨ha, hb⟩)))
      | sequenceConstruct a b =>
        simp only [Expr.sequenceConstruct.sizeOf_spec] at hsz
        rw [identifyPropertyExpr]
        exact Post.bind (ihE a (by omega)) (fun ra ha => Post.bind (ihE b (by omega)) (fun rb hb =>
          Post.pure _ (by simp only [noActExpr, Bool.and_eq_true]; exact ⟨ha, hb⟩)))
      | sequenceSpread e =>
        simp only [Expr.sequenceSpread.sizeOf_spec] at hsz
        rw [identifyPropertyExpr]
        exact Post.bind (ihE e (by omega)) (fun r hr => Post.pure _ (by simp only [noActExpr]; exact hr))
      | listLiteral items =>
        simp only [Expr.listLiteral.sizeOf_spec] at hsz
        rw [identifyPropertyExpr]
        exact Post.bind (exprs items (by omega)) (fun r hr => Post.pure _ (by simp only [noActExpr]; exact hr))
      | capture rows =>
        simp only [Expr.capture.sizeOf_spec] at hsz
        rw [identifyPropertyExpr]
        exact Post.bind (exprs rows (by omega)) (fun r hr => Post.pure _ (by simp only [noActExpr]; exact hr))
      | algorithmExpr a =>
        simp only [Expr.algorithmExpr.sizeOf_spec] at hsz
        rw [identifyPropertyExpr]
        exact Post.bind (ihA a (by omega)) (fun r hr => Post.pure _ (by simp only [noActExpr]; exact hr))
      | call f args =>
        simp only [Expr.call.sizeOf_spec] at hsz
        rw [identifyPropertyExpr]
        exact Post.bind (ihE f (by omega)) (fun rf hf => Post.bind (exprs args (by omega)) (fun ra ha =>
          Post.pure _ (by simp only [noActExpr, Bool.and_eq_true]; exact ⟨hf, ha⟩)))
      | dotMember target name fallback args =>
        simp only [Expr.dotMember.sizeOf_spec] at hsz
        rw [identifyPropertyExpr]
        refine Post.bind (ihE target (by omega)) (fun rt ht => Post.bind (ihE fallback (by omega)) (fun rf hf => ?_))
        have hlast : ∀ ra, noActOptExprs ra = true → noActExpr (.dotMember rt name rf ra) = true := by
          intro ra ha
          cases ra with
          | none => simp only [noActExpr, Bool.and_eq_true]; exact ⟨ht, hf⟩
          | some items => simp only [noActExpr, Bool.and_eq_true]; exact ⟨⟨ht, hf⟩, ha⟩
        cases args with
        | none =>
          exact Post.bind (Post.pure (P := fun r => noActOptExprs r = true) none rfl)
            (fun ra ha => Post.pure _ (hlast ra ha))
        | some items =>
          simp only [Option.some.sizeOf_spec] at hsz
          exact Post.bind (Post.map (Q := fun r => noActOptExprs r = true) some (exprs items (by omega))
            (fun r hr => hr)) (fun ra ha => Post.pure _ (hlast ra ha))
    -- algorithms
    · intro a hsz
      cases a with
      | builtin b =>
        rw [identifyPropertyAlgorithm]
        exact Post.bind (Post.modifyGet _) (fun _ _ => Post.pure _ rfl)
      | mk parent pats opens ps output id =>
        simp only [Algorithm.mk.sizeOf_spec] at hsz
        rw [identifyPropertyAlgorithm]
        refine Post.bind (Post.modifyGet _) (fun identity _ => ?_)
        have hparent : Post (match parent with
            | none => (Pure.pure none : StateM Nat (Option ScopeCtx))
            | some scope => some <$> identifyPropertyScope scope) (fun r => noActParent r = true) := by
          cases parent with
          | none => exact noParent
          | some sc => simp only [Option.some.sizeOf_spec] at hsz; exact someParent sc (by omega)
        have hrest : ∀ rp, noActParent rp = true → Post (do
            let ro ← opens.mapM identifyPropertyExpr
            let rps ← ps.mapM identifyPropertyDefinition
            let rout ← output.mapM identifyPropertyExpr
            Pure.pure (Algorithm.mk rp pats ro rps rout (some identity))) (fun r => noActAlg r = true) :=
          fun rp hp => Post.bind (exprs opens (by omega)) (fun ro ho => Post.bind (props ps (by omega)) (fun rps hps =>
            Post.bind (exprs output (by omega)) (fun rout hout =>
              Post.pure _ (by simp only [noActAlg, Bool.and_eq_true]; exact ⟨⟨⟨hp, ho⟩, hps⟩, hout⟩))))
        cases parent with
        | none => exact Post.bind hparent hrest
        | some sc => exact Post.bind hparent hrest
      | conditional parent opens brs id =>
        simp only [Algorithm.conditional.sizeOf_spec] at hsz
        rw [identifyPropertyAlgorithm]
        refine Post.bind (Post.modifyGet _) (fun identity _ => ?_)
        have hparent : Post (match parent with
            | none => (Pure.pure none : StateM Nat (Option ScopeCtx))
            | some scope => some <$> identifyPropertyScope scope) (fun r => noActParent r = true) := by
          cases parent with
          | none => exact noParent
          | some sc => simp only [Option.some.sizeOf_spec] at hsz; exact someParent sc (by omega)
        have hrest : ∀ rp, noActParent rp = true → Post (do
            let ro ← opens.mapM identifyPropertyExpr
            let rb ← brs.mapM fun b => do return { b with body := (← identifyPropertyAlgorithm b.body) }
            Pure.pure (Algorithm.conditional rp ro rb (some identity))) (fun r => noActAlg r = true) :=
          fun rp hp => Post.bind (exprs opens (by omega)) (fun ro ho => Post.bind (branches brs (by omega)) (fun rb hb =>
            Post.pure _ (by simp only [noActAlg, Bool.and_eq_true]; exact ⟨⟨hp, ho⟩, hb⟩)))
        cases parent with
        | none => exact Post.bind hparent hrest
        | some sc => exact Post.bind hparent hrest
      | «alias» parent opens ps target id reference =>
        simp only [Algorithm.alias.sizeOf_spec] at hsz
        rw [identifyPropertyAlgorithm]
        refine Post.bind (Post.modifyGet _) (fun identity _ => ?_)
        have hparent : Post (match parent with
            | none => (Pure.pure none : StateM Nat (Option ScopeCtx))
            | some scope => some <$> identifyPropertyScope scope) (fun r => noActParent r = true) := by
          cases parent with
          | none => exact noParent
          | some sc => simp only [Option.some.sizeOf_spec] at hsz; exact someParent sc (by omega)
        have hrest : ∀ rp, noActParent rp = true → Post (do
            let ro ← opens.mapM identifyPropertyExpr
            let rps ← ps.mapM identifyPropertyDefinition
            let rt ← identifyPropertyExpr target
            Pure.pure (Algorithm.alias rp ro rps rt (some identity) reference)) (fun r => noActAlg r = true) :=
          fun rp hp => Post.bind (exprs opens (by omega)) (fun ro ho => Post.bind (props ps (by omega)) (fun rps hps =>
            Post.bind (ihE target (by omega)) (fun rt ht =>
              Post.pure _ (by simp only [noActAlg, Bool.and_eq_true]; exact ⟨⟨⟨hp, ho⟩, hps⟩, ht⟩))))
        cases parent with
        | none => exact Post.bind hparent hrest
        | some sc => exact Post.bind hparent hrest
    -- scope levels
    · intro sc hsz
      cases sc with
      | mk parent params opens ps output brs activation id =>
        simp only [ScopeCtx.mk.sizeOf_spec] at hsz
        have hrest : ∀ rp, noActParent rp = true → Post (do
            let ro ← opens.mapM identifyPropertyExpr
            let rps ← ps.mapM identifyPropertyDefinition
            let rout ← output.mapM identifyPropertyExpr
            let rb ← brs.mapM fun b => do return { b with body := (← identifyPropertyAlgorithm b.body) }
            Pure.pure (ScopeCtx.mk rp params ro rps rout rb none id)) (fun r => noActScope r = true) :=
          fun rp hp => Post.bind (exprs opens (by omega)) (fun ro ho => Post.bind (props ps (by omega)) (fun rps hps =>
            Post.bind (exprs output (by omega)) (fun rout hout => Post.bind (branches brs (by omega)) (fun rb hb =>
              Post.pure _ (by
                simp only [noActScope, Bool.and_eq_true]
                exact ⟨⟨⟨⟨⟨rfl, hp⟩, ho⟩, hps⟩, hout⟩, hb⟩)))))
        cases parent with
        | none =>
          rw [identifyPropertyScope]
          exact Post.bind noParent hrest
        | some par =>
          simp only [Option.some.sizeOf_spec] at hsz
          rw [identifyPropertyScope]
          exact Post.bind (someParent par (by omega)) hrest
    -- properties
    · intro p hsz
      rw [identifyPropertyDefinition]
      exact Post.bind (Post.modifyGet _) (fun identity _ =>
        Post.bind (ihA p.alg (by have := PropDef.sizeOf_alg_lt p; omega)) (fun r hr => Post.pure _ hr))

/-- **THE IDENTITY PASS LEAVES NO ACTIVATION INDEX.** Whatever tree a host supplies — activation
    indices in parent slots included — the program `runResultM` evaluates carries none, at any depth. -/
theorem identify_noAct (e : Expr) (n : Nat) : noActExpr ((identifyPropertyExpr e).run' n) = true :=
  (identifyNoAct (sizeOf e + 1)).1 e (Nat.lt_succ_self _) n

/-- The root algorithm `runResultM` wires, and every algorithm written inside it, has a chain that is
    backed in every state: the static fact of the uses that take a parent from the written tree. -/
theorem prepared_root_backed (e : Expr) (root : Algorithm) (acts : Array ParameterActivation)
    (h : (identifyPropertyExpr e).run' 0 = .algorithmExpr root) : noActAlg root = true ∧ Backed acts root.parent := by
  have hno := identify_noAct e 0
  rw [h] at hno
  have hroot : noActAlg root = true := by simpa only [noActExpr] using hno
  exact ⟨hroot, backed_of_noActAlg acts hroot⟩

/-! ## Where an activated level comes from: the two writers of the activation array -/

theorem lookupAssoc_filter_of {A : Type} (names : List Ident) (y : Ident) (hy : names.contains y = true) :
    ∀ (env : Assoc Ident A), (lookupAssoc y env).isSome = true →
      (lookupAssoc y (env.filter (fun b => names.contains b.fst))).isSome = true
  | [], h => by simp [lookupAssoc] at h
  | (k, v) :: rest, h => by
      have hf : ((k, v) :: rest).filter (fun b => names.contains b.fst) =
          if names.contains k = true then (k, v) :: rest.filter (fun b => names.contains b.fst)
          else rest.filter (fun b => names.contains b.fst) := List.filter_cons
      rw [hf]
      by_cases hk : y = k
      · subst hk
        rw [ite_eq_left hy]
        show (if y = y then some v else _).isSome = true
        rw [ite_eq_left rfl]
        rfl
      · have hrest : (lookupAssoc y rest).isSome = true := by
          have h' : (if y = k then some v else lookupAssoc y rest).isSome = true := h
          rw [ite_eq_right hk] at h'
          exact h'
        have ih := lookupAssoc_filter_of names y hy rest hrest
        by_cases hin : names.contains k = true
        · rw [ite_eq_left hin]
          show (if y = k then some v else _).isSome = true
          rw [ite_eq_right hk]
          exact ih
        · rw [ite_eq_right hin]
          exact ih

/-- **THE RECORD OF AN ACTIVATION BINDS WHAT THE ENTERING TIER BINDS.** `recordParameterActivation`
    appends one record; it binds every name of `names` the context's need tier binds. -/
theorem recorded_binds (names : List Ident) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    ∃ act, ((recordParameterActivation names ctx env).runState s) =
        (.ok s.lexicalActivations.size, { s with lexicalActivations := s.lexicalActivations.push act }) ∧
      ∀ y, names.contains y = true → (lookupAssoc y ctx.needEnv).isSome = true →
        (lookupAssoc y act.needs).isSome = true :=
  ⟨{ values := env.filter (fun b => names.contains b.fst),
     needs := ctx.needEnv.filter (fun b => names.contains b.fst),
     bindingContext := ctx.bindingContext }, rfl,
    fun y hy hb => lookupAssoc_filter_of names y hy ctx.needEnv hb⟩

theorem backed_push {acts : Array ParameterActivation} (act : ParameterActivation) {chain : Option ScopeCtx}
    (h : Backed acts chain) : Backed (acts.push act) chain :=
  Backed.mono (fun i a hi => by
    have hlt := lt_of_getElem?_some hi
    have hkeep : (acts.push act)[i]? = acts[i]? := by
      rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]
    rw [hkeep]
    exact hi) h

/-- **BODY ENTRY ESTABLISHES A BACKED SITE CHAIN** — given the binder's coverage: when the entering
    tier binds every parameter of the entered algorithm, the entered context's site chain is backed
    in the exit state, and the exit state extends the entry state's activations. -/
theorem enterAlgorithmBody_backed (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (ha : Backed s.lexicalActivations a.parent)
    (hcover : ∀ y, a.params.contains y = true → (lookupAssoc y ctx.needEnv).isSome = true) :
    ∃ entered t, (enterAlgorithmBody a ctx env).runState s = (.ok entered, t) ∧ ActivationPrefix s t ∧
      entered.callStack = a :: ctx.callStack ∧ Backed t.lexicalActivations (siteScope? entered) := by
  unfold enterAlgorithmBody
  split
  · refine ⟨ctx.push a, s, rfl, ActivationPrefix.refl s, rfl, ?_⟩
    show Backed s.lexicalActivations (some a.asScopeCtx)
    exact (backed_asScopeCtx _ a).2 ha
  · obtain ⟨act, hrun, hbinds⟩ := recorded_binds a.params ctx env s
    refine ⟨{ ctx.push a with headScope := some (a.asScopeCtx.withActivation s.lexicalActivations.size) },
      { s with lexicalActivations := s.lexicalActivations.push act }, ?_, ActivationPrefix.push s act, rfl, ?_⟩
    · rw [KatLang.CallPlan.bind_run, hrun]
      rfl
    · show Backed (s.lexicalActivations.push act) (some (a.asScopeCtx.withActivation s.lexicalActivations.size))
      unfold Algorithm.asScopeCtx ScopeCtx.withActivation
      simp only [Backed]
      refine ⟨fun i hi => ?_, backed_push act ha⟩
      cases hi
      exact ⟨act, by simp, fun y hy => hbinds y hy (hcover y hy)⟩

/-- **FAMILY DISPATCH ESTABLISHES A BACKED BRANCH BODY** — given the binder's coverage of the matched
    pattern's names: the selected body is wired under the family level whose activation is recorded
    and binds those names. -/
theorem wireSelectedBranchBody_backed (callee body : Algorithm) (binderNames : List Ident) (ctx : EvalCtx)
    (env : ValEnv) (s : EvalState) (hc : Backed s.lexicalActivations callee.parent)
    (hcover : ∀ y, binderNames.contains y = true → (lookupAssoc y ctx.needEnv).isSome = true) :
    ∃ wired t, (wireSelectedBranchBody callee body binderNames ctx env).runState s = (.ok wired, t) ∧
      ActivationPrefix s t ∧ Backed t.lexicalActivations wired.parent := by
  obtain ⟨act, hrun, hbinds⟩ := recorded_binds binderNames ctx env s
  refine ⟨body.withParent (some (.mk callee.parent binderNames callee.opens callee.props callee.output
      callee.branches (some s.lexicalActivations.size) callee.declarationId)),
    { s with lexicalActivations := s.lexicalActivations.push act }, ?_, ActivationPrefix.push s act, ?_⟩
  · unfold wireSelectedBranchBody
    rw [KatLang.CallPlan.bind_run, hrun]
    rfl
  · apply backed_withParent
    simp only [Backed]
    refine ⟨fun i hi => ?_, backed_push act hc⟩
    cases hi
    exact ⟨act, by simp, fun y hy => hbinds y hy (hcover y hy)⟩

end KatLang.NavigationWiring
