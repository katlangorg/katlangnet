import KatLangArityLaws.NestedRepeatedNames

open KatLang KatLang.BinderTrace KatLang.RepeatedNameLaws KatLang.NestedRepeatedNames
open KatLang.CallableIdentityDomain

/-!
# FG-I1: callable identities from construction provenance (November 2026)

`CallableIdentityDomain` proves transitivity of `sameRepeatedCallableIdentity` on domains stated
about the comparison (`NoCrossFallback`, printer-free `WalkAligned`, `SuccessAligned`). This module
states an INDEPENDENT construction domain and connects it to the production definitions that make
callable identities.

THE PROVENANCE DOMAIN (`PresenceTable`, `ChainFollows`, `Follows`). A table `T` records, per
declaration, whether that declaration is wired under an anonymous level. `Follows T a` says that
`a` and every identified level of its parent chain were wired as the table records. It reads no
comparison, no printed text and no second algorithm: the same declaration under different lexical
activations, different identified parents, or different depths all stay inside one table. Only ONE
thing is excluded: one declaration wired under an identified level in one place and under an
anonymous level in another (`mixed_same_declaration_outside_domain`).

RESULTS.
1. `identity_walk_aligned_of_follows`, `same_identity_trans_of_follows`,
   `callable_trans_on_of_follows`: on the domain, identity is transitive, with no printer premise.
2. Use site: `head_callable_trans_on_of_success_aligned`, `production_head_walk_success_aligned`
   (the pairwise form, also reached from `ModelNoCross`), `production_head_walk_follows` (the
   production binder channels, `CallableTransOn` DERIVED from `ModelFollows`),
   `model_follows_of_heap` (from the state's published CALLABLE outcomes),
   `publication_heap_follows` (the one publishing operation, `NeedProjection.step`, keeps it).
3. Production preservation, each over the actual definition: `chainFollows_asScopeCtx`,
   `chainFollows_withActivation`, `chainFollows_chainRoot`, `follows_withParent` (module rooting
   included), `follows_childOf`, `follows_childOfInContext`, `follows_wireToCaller`,
   `follows_wireSelectedBranchBody`, `follows_lookupInParentsStructuralProperty`,
   `follows_of_identifyRuntime` (a retained wrapper keeps its entry, a minted one gets a fresh one).
4. Entry and preparation: `wireToCaller_entry`, `entry_follows`,
   `identifyPropertyAlgorithm_declarationId`, `identifyPropertyScope_slots`,
   `identification_keeps_anonymous_parent`.

WHAT REMAINS CONDITIONAL.
* `ModelFollows` / `HeapFollows` are PREMISES at the production corollaries: no whole-run theorem
  says that every CALLABLE outcome of a real run follows one table. Results 3 and 4 establish the
  invariant at each producer, not across the 102 evaluator bodies.
* `follows_childOfInContext` keeps one printer-dependent premise, `SitePresence`: the production
  `activeDeclaration?` compares a wired algorithm with every site level through
  `sameDeclaringScope`, and at a mixed pair that is the printed fallback. `ReprSeparatesPresence`
  implies it (`sitePresence_of_separating`). `reprStr` reaches `Format.pretty`, whose layout loop
  is `partial`; these proofs supply no separation fact about its output.
  `CallableIdentityClosure.use_site_is_a_printer_fact` shows a printer fact cannot be avoided on
  admitted input: on an equal-depth fork the use-site obligation itself implies one.
* The domain is proper, on purpose. Host-built `shared` declarations can place one declaration
  under an identified and an anonymous level, and a real run then reaches the mixed fallback at a
  repeated-name comparison; `CallableIdentityProvenanceGuards` runs those programs. Through unequal
  depths activations refuse the pair anyway; at equal depth the printed fallback alone decides, and
  this module claims nothing.
* Host tokens and owned views are encoder inputs: a table over them is a statement about those
  tokens, never about C# object identity.

Identity semantics are unchanged. Binder premises (`ProdRel`, `Fits`, `RepeatedPlainList`) stay
explicit and independent of everything here.
-/

namespace KatLang.CallableIdentityProvenance

/-! ## The provenance domain -/

/-- Per declaration, whether it is wired under an anonymous level. -/
abbrev PresenceTable := Option PropertyIdentity → Bool

/-- The table key of an identity slot: the declaration, without an owned component view. -/
abbrev declKey : Option PropertyIdentity → Option PropertyIdentity :=
  PropertyIdentity.callableDeclaration

/-- Whether the parent exists and is anonymous. -/
def parentAnonymous : Option ScopeCtx → Bool
  | some scope => scope.declarationId.isNone
  | none => false

/-- Every identified level of the chain is wired as the table records. -/
def ChainFollows (T : PresenceTable) : ScopeCtx → Prop
  | .mk none _ _ _ _ _ _ id => id.isSome = true → T (declKey id) = false
  | .mk (some p) _ _ _ _ _ _ id =>
      (id.isSome = true → T (declKey id) = p.declarationId.isNone) ∧ ChainFollows T p

/-- An algorithm is a builtin, or it and its parent chain are wired as the table records. -/
def Follows (T : PresenceTable) (a : Algorithm) : Prop :=
  a.isBuiltin = true ∨
    (T (declKey a.declarationId) = parentAnonymous a.parent ∧
      ∀ p, a.parent = some p → ChainFollows T p)

theorem presence_of_table {b : Bool} {p q : ScopeCtx}
    (hp : b = p.declarationId.isNone) (hq : b = q.declarationId.isNone) :
    p.declarationId.isSome = q.declarationId.isSome := by
  cases hP : p.declarationId <;> cases hQ : q.declarationId <;> simp_all

/-- RESULT 1 (levels): chains of one table stay on an aligned decision path from any pair of levels
    with equal presence. -/
theorem walk_aligned_of_follows (T : PresenceTable) : ∀ x y : ScopeCtx,
    x.declarationId.isSome = y.declarationId.isSome →
    ChainFollows T x → ChainFollows T y → WalkAligned x y
  | .mk xp _ _ _ _ _ _ (some a), .mk yp _ _ _ _ _ _ (some b), _, hx, hy => by
      rcases xp with _ | p <;> rcases yp with _ | q <;> simp only [WalkAligned]
      · intros; trivial
      · intros; trivial
      · intros; trivial
      · intro hab _
        subst hab
        simp only [ChainFollows] at hx hy
        have hp := hx.1 rfl
        have hq := hy.1 rfl
        exact walk_aligned_of_follows T p q (presence_of_table hp hq) hx.2 hy.2
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none, _, _, _ => by simp only [WalkAligned]
  | .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ none, h, _, _ => by
      simp [ScopeCtx.declarationId] at h
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ (some _), h, _, _ => by
      simp [ScopeCtx.declarationId] at h

theorem not_isBuiltin_iff_parent {a : Algorithm} (h : a.isBuiltin = true) : a.parent = none := by
  cases a <;> simp_all [Algorithm.isBuiltin, Algorithm.parent]

/-- RESULT 1 (algorithms): two followers of one table are in the printer-free pairwise domain. -/
theorem identity_walk_aligned_of_follows (T : PresenceTable) (a b : Algorithm)
    (ha : Follows T a) (hb : Follows T b) : IdentityWalkAligned a b := by
  intro hd
  rcases ha with ha | ⟨ta, ca⟩
  · simp [not_isBuiltin_iff_parent ha, ParentWalkAligned]
  rcases hb with hb | ⟨tb, cb⟩
  · simp only [not_isBuiltin_iff_parent hb]
    cases a.parent <;> simp [ParentWalkAligned]
  cases hl : a.parent with
  | none => simp [ParentWalkAligned]
  | some p =>
    cases hr : b.parent with
    | none => simp [ParentWalkAligned]
    | some q =>
      simp only [ParentWalkAligned]
      have hd' : declKey a.declarationId = declKey b.declarationId := hd
      rw [hl] at ta
      rw [hr, ← hd'] at tb
      simp only [parentAnonymous] at ta tb
      exact walk_aligned_of_follows T p q (presence_of_table ta tb) (ca p hl) (cb q hr)

/-- RESULT 1: TRANSITIVITY of repeated callable identity on the provenance domain. No printer
    premise, no profile premise. -/
theorem same_identity_trans_of_follows (T : PresenceTable) (a b c : Algorithm)
    (ha : Follows T a) (hb : Follows T b) (hc : Follows T c)
    (hab : sameRepeatedCallableIdentity a b = true) (hbc : sameRepeatedCallableIdentity b c = true) :
    sameRepeatedCallableIdentity a c = true :=
  same_identity_trans_of_walk_aligned a b c (identity_walk_aligned_of_follows T a b ha hb)
    (identity_walk_aligned_of_follows T b c hb hc) hab hbc

/-- `CallableTransOn` for every contribution list whose present identities follow one table. -/
theorem callable_trans_on_of_follows (T : PresenceTable) (l : List Contribution)
    (h : ∀ a, Present l a → Follows T a) : CallableTransOn l :=
  fun a b c ha hb hc hab hbc =>
    same_identity_trans_of_follows T a b c (h a ha) (h b hb) (h c hc) hab hbc

/-- THE ONE EXCLUSION: one declaration under an identified and under an anonymous parent follows
    no table. (A real run reaching this shape is in `CallableIdentityProvenanceGuards`.) -/
theorem mixed_same_declaration_outside_domain (d : PropertyIdentity) (x y : ScopeCtx)
    (a b : Algorithm) (hna : a.isBuiltin = false) (hnb : b.isBuiltin = false)
    (hda : a.declarationId = some d) (hdb : b.declarationId = some d)
    (hpa : a.parent = some x) (hpb : b.parent = some y)
    (hx : x.declarationId.isSome = true) (hy : y.declarationId = none) :
    ¬ ∃ T, Follows T a ∧ Follows T b := by
  rintro ⟨T, ha, hb⟩
  rcases ha with ha | ⟨ta, -⟩
  · simp [hna] at ha
  rcases hb with hb | ⟨tb, -⟩
  · simp [hnb] at hb
  rw [hda, hpa] at ta
  rw [hdb, hpb] at tb
  simp only [parentAnonymous, hy, Option.isNone_none] at ta tb
  rw [ta] at tb
  cases hX : x.declarationId <;> simp_all

/-! ## The repeated-name use site -/

/-- Observed identities are pairwise success-aligned. -/
def ModelSuccessAligned (M : Model) : Prop :=
  ∀ a b, ModelPresent M a → ModelPresent M b → SuccessAligned a b

theorem model_success_aligned_of_no_cross (M : Model) (h : ModelNoCross M) :
    ModelSuccessAligned M :=
  fun a b ha hb => success_aligned_of_no_cross a b (h a b ha hb)

theorem model_success_aligned_after_growth {M N : Model} (he : Model.Extends M N)
    (hf : FreshIdless M N) (h : ModelSuccessAligned M) : ModelSuccessAligned N :=
  fun a b ha hb => h a b (model_present_before_growth he hf a ha)
    (model_present_before_growth he hf b hb)

/-- Every defined head walk keeps the pairwise domain, so `CallableTransOn` holds of every final
    contribution list. -/
theorem head_callable_trans_on_of_success_aligned (M : Model) (ps : List NeedPattern)
    (cells : List Nat) (family : Bool) (w : Walk) (hw : M.WF) (h : walkHead M ps cells family = some w)
    (hd : ModelSuccessAligned M) (addresses : List Nat) :
    CallableTransOn (addresses.map (contrib w.2.1.obs)) := by
  have hn : ModelSuccessAligned w.2.1 := by
    unfold walkHead gateWalk at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact hd
    · have shape := sources_shape ps _ _ {} family M w hw h
      exact model_success_aligned_after_growth shape.1 shape.2.2.1 hd
  apply callable_trans_on_of_success_aligned
  intro a b ha hb
  obtain ⟨ca, hca, hia⟩ := ha
  obtain ⟨cb, hcb, hib⟩ := hb
  obtain ⟨aa, -, rfl⟩ := List.mem_map.mp hca
  obtain ⟨ab, -, rfl⟩ := List.mem_map.mp hcb
  exact hn a b (model_present_of_obs _ aa a hia) (model_present_of_obs _ ab b hib)

/-- The production binder channels with the pairwise domain. -/
theorem production_head_walk_success_aligned
    (ev : Nat → Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (written : Nat → Expr → EvalCtx → EvalM (Option Algorithm)) (M : Model) (s : EvalState)
    (ps : List NeedPattern) (cells : List Nat) (family : Bool) (hs : ProdRel M s)
    (hp : RepeatedPlainList (needRepeatedNames ps) ps)
    (hf : Fits M (needRepeatedNames ps) ps (needLevelSources ps cells))
    (hd : ModelSuccessAligned M) :
    ∃ w t, walkHead M ps cells family = some w ∧
      runEval (bindNeedPatterns (NeedChannels.shell ev route demand written) ps cells family) s
        = (w.1.map (Option.map NeedBindState.bound), t) ∧
      ProdRel w.2.1 t ∧ ∀ addresses : List Nat, CallableTransOn (addresses.map (contrib w.2.1.obs)) := by
  obtain ⟨w, t, hw, ht, hr⟩ := production_head_walk ev route demand written M s ps cells family hs hp hf
  exact ⟨w, t, hw, ht, hr, fun addresses =>
    head_callable_trans_on_of_success_aligned M ps cells family w (prodRel_wf hs) hw hd addresses⟩

/-- Every observed identity follows the table. -/
def ModelFollows (T : PresenceTable) (M : Model) : Prop :=
  ∀ a, ModelPresent M a → Follows T a

theorem model_success_aligned_of_follows (T : PresenceTable) (M : Model) (h : ModelFollows T M) :
    ModelSuccessAligned M :=
  fun a b ha hb => success_aligned_of_walk_aligned a b
    (identity_walk_aligned_of_follows T a b (h a ha) (h b hb))

/-- RESULT 2: the production binder channels, with `CallableTransOn` DERIVED from the provenance
    domain. `ProdRel`, the fitting supply and the valid repeated head stay separate premises. -/
theorem production_head_walk_follows (T : PresenceTable)
    (ev : Nat → Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (written : Nat → Expr → EvalCtx → EvalM (Option Algorithm)) (M : Model) (s : EvalState)
    (ps : List NeedPattern) (cells : List Nat) (family : Bool) (hs : ProdRel M s)
    (hp : RepeatedPlainList (needRepeatedNames ps) ps)
    (hf : Fits M (needRepeatedNames ps) ps (needLevelSources ps cells))
    (hd : ModelFollows T M) :
    ∃ w t, walkHead M ps cells family = some w ∧
      runEval (bindNeedPatterns (NeedChannels.shell ev route demand written) ps cells family) s
        = (w.1.map (Option.map NeedBindState.bound), t) ∧
      ProdRel w.2.1 t ∧ ∀ addresses : List Nat, CallableTransOn (addresses.map (contrib w.2.1.obs)) :=
  production_head_walk_success_aligned ev route demand written M s ps cells family hs hp hf
    (model_success_aligned_of_follows T M hd)

/-- Every published successful CALLABLE outcome of the heap follows the table. -/
def HeapFollows (T : PresenceTable) (s : EvalState) : Prop :=
  ∀ (a : Nat) (cell : NeedCell), s.needs[a]? = some cell → ∀ alg : Algorithm,
    cell.callable = NeedCallableState.projected (.ok (some alg)) → Follows T alg

/-- The observation model reads its identities from the state: a heap of followers gives a model of
    followers. -/
theorem model_follows_of_heap (T : PresenceTable) (M : Model) (s : EvalState)
    (hs : ProdRel M s) (hh : HeapFollows T s) : ModelFollows T M := by
  rintro a ⟨address, v, hv⟩
  obtain ⟨c, hc, -, hcal⟩ := hs.stable address _ hv
  rcases hcal with hp | ⟨-, hnone, -⟩
  · exact hh address c hc a hp
  · cases hnone

theorem empty_heap_follows (T : PresenceTable) : HeapFollows T EvalState.empty := by
  intro a cell hc
  simp [EvalState.empty] at hc

/-- Writing a CALLABLE state keeps the heap's followers, when the written state is one. -/
theorem heapFollows_setCallable (T : PresenceTable) (s : EvalState) (a : Nat) (v : NeedCallableState)
    (hs : HeapFollows T s) (hv : ∀ alg, v = .projected (.ok (some alg)) → Follows T alg) :
    HeapFollows T (NeedControl.Projection.setCallable a v s) := by
  intro b cell hc alg hcal
  by_cases hba : b = a
  · subst hba
    cases hcur : s.needs[b]? with
    | none =>
      simp [NeedControl.Projection.setCallable, Array.getElem?_modify, hcur] at hc
    | some current =>
      rw [NeedControl.Projection.setCallable_at s b v current hcur] at hc
      cases hc
      exact hv alg hcal
  · rw [NeedControl.Projection.setCallable_other s a b v hba] at hc
    exact hs b cell hc alg hcal

/-- THE PUBLICATION STEP: `NeedProjection.step` over an unprojected cell keeps the heap's
    followers when the projection's own run does and its outcome is a follower. Sticky reuse
    (`projected_sticky`) changes no state. -/
theorem publication_heap_follows (T : PresenceTable)
    (project : NeedSuspension → EvalM (Option Algorithm)) (a : Nat)
    (s t : EvalState) (cell : NeedCell) (outcome : Except Error (Option Algorithm))
    (hc : s.needs[a]? = some cell) (hu : cell.callable = .unprojected)
    (hr : (project cell.suspension).runState
      (NeedControl.Projection.setCallable a .projecting s) = (outcome, t))
    (hcomplete : outcome.isIncomplete = false)
    (ht : HeapFollows T t) (ho : ∀ alg, outcome = .ok (some alg) → Follows T alg) :
    HeapFollows T ((NeedProjection.step project a).runState s).2 := by
  rw [NeedControl.Projection.unprojected_publishes project a s t cell outcome hc hu hr hcomplete]
  apply heapFollows_setCallable T t a _ ht
  intro alg h
  cases h
  exact ho alg rfl

/-! ## Production preservation -/

theorem withParent_declarationId (c : Algorithm) (p : Option ScopeCtx) :
    (c.withParent p).declarationId = c.declarationId := by
  unfold Algorithm.withParent
  split <;> rfl

/-- `withParent` wires under the given scope, or under its chain root for a loaded module. -/
theorem withParent_parent_cases (c : Algorithm) (s : ScopeCtx) (hb : c.isBuiltin = false) :
    (c.withParent (some s)).parent = some s ∨ (c.withParent (some s)).parent = some s.chainRoot := by
  unfold Algorithm.withParent
  split <;> simp_all [Algorithm.parent, Algorithm.isBuiltin]

/-- The plain arm: a non-module algorithm is wired exactly under the given scope. -/
theorem withParent_parent_of_not_module (c : Algorithm) (s : ScopeCtx) (hb : c.isBuiltin = false)
    (hm : c.isModuleRoot = false) : (c.withParent (some s)).parent = some s := by
  unfold Algorithm.withParent
  split <;>
    simp_all [Algorithm.parent, Algorithm.isBuiltin, Algorithm.isModuleRoot,
      Algorithm.declarationId, PropertyIdentity.callableDeclaration]

theorem chainFollows_chainRoot (T : PresenceTable) : ∀ s : ScopeCtx,
    ChainFollows T s → ChainFollows T s.chainRoot
  | .mk none _ _ _ _ _ _ _, h => h
  | .mk (some p) _ _ _ _ _ _ _, h => by
      simp only [ChainFollows] at h
      exact chainFollows_chainRoot T p h.2

/-- WIRING: a wired algorithm follows when its scope does and the table records the scope it was
    actually wired under. -/
theorem follows_withParent (T : PresenceTable) (c : Algorithm) (s : ScopeCtx)
    (hs : ChainFollows T s)
    (ht : c.isBuiltin = false →
      T (declKey c.declarationId) = parentAnonymous (c.withParent (some s)).parent) :
    Follows T (c.withParent (some s)) := by
  cases hb : c.isBuiltin with
  | true =>
    refine Or.inl ?_
    cases c <;> simp_all [Algorithm.isBuiltin, Algorithm.withParent]
  | false =>
    refine Or.inr ⟨?_, ?_⟩
    · rw [withParent_declarationId]; exact ht hb
    · intro p hp
      rcases withParent_parent_cases c s hb with h | h <;> rw [h] at hp <;> cases hp
      · exact hs
      · exact chainFollows_chainRoot T s hs

/-- The scope view of a follower follows (the production owner/scope reconstruction). -/
theorem chainFollows_asScopeCtx (T : PresenceTable) (a : Algorithm) (ha : Follows T a) :
    ChainFollows T a.asScopeCtx := by
  rcases ha with hb | ⟨ht, hc⟩
  · cases a <;> simp_all [Algorithm.isBuiltin, Algorithm.asScopeCtx, ChainFollows,
      Algorithm.parent, Algorithm.declarationId]
  · unfold Algorithm.asScopeCtx
    cases hp : a.parent with
    | none =>
      simp only [ChainFollows]
      intro _
      rw [ht, hp]
      rfl
    | some p =>
      simp only [ChainFollows]
      refine ⟨fun _ => ?_, hc p hp⟩
      rw [ht, hp]
      rfl

theorem asScopeCtx_declarationId (a : Algorithm) :
    a.asScopeCtx.declarationId = a.declarationId := rfl

/-- An activation changes neither identity nor parent chain. -/
theorem chainFollows_withActivation (T : PresenceTable) (v : Nat) (s : ScopeCtx)
    (h : ChainFollows T s) : ChainFollows T (s.withActivation v) := by
  cases s with
  | mk p ps op props out branches activation id =>
    cases p <;> simpa only [ScopeCtx.withActivation, ChainFollows] using h

theorem withActivation_declarationId (v : Nat) (s : ScopeCtx) :
    (s.withActivation v).declarationId = s.declarationId := by
  cases s; rfl

/-- `childOf`: a lexical child wired under a follower, recorded at that presence. -/
theorem follows_childOf (T : PresenceTable) (a child : Algorithm) (ha : Follows T a)
    (hm : child.isModuleRoot = false)
    (ht : child.isBuiltin = false → T (declKey child.declarationId) = a.declarationId.isNone) :
    Follows T (Algorithm.childOf a child) := by
  apply follows_withParent T child a.asScopeCtx (chainFollows_asScopeCtx T a ha)
  intro hb
  rw [withParent_parent_of_not_module child _ hb hm]
  exact ht hb

/-! ### The levels of a chain and contextual wiring -/

/-- The levels of a chain, innermost first. -/
def chainLevels : Option ScopeCtx → List ScopeCtx
  | none => []
  | some (.mk p ps op props out branches activation id) =>
      .mk p ps op props out branches activation id :: chainLevels p

theorem chainFollows_of_mem (T : PresenceTable) : ∀ (s x : ScopeCtx),
    ChainFollows T s → x ∈ chainLevels (some s) → ChainFollows T x
  | .mk none _ _ _ _ _ _ _, x, h, m => by
      simp only [chainLevels, List.mem_cons, List.not_mem_nil, or_false] at m
      subst m
      exact h
  | .mk (some p) _ _ _ _ _ _ _, x, h, m => by
      simp only [chainLevels, List.mem_cons] at m
      rcases m with rfl | m
      · exact h
      · simp only [ChainFollows] at h
        exact chainFollows_of_mem T p x h.2 m

/-- The production `activeDeclaration?` returns a level of the chain it was given, and that level
    passed `sameDeclaringScope`. -/
theorem activeDeclaration_some (required : ScopeCtx) : ∀ (level : Option ScopeCtx) (x : ScopeCtx),
    activeDeclaration? required level = some x →
      x ∈ chainLevels level ∧ sameDeclaringScope required x = true
  | none, _, h => by simp [activeDeclaration?] at h
  | some (.mk p ps op props out branches activation id), x, h => by
      simp only [activeDeclaration?] at h
      split at h
      · rename_i hif
        cases h
        simp only [Bool.and_eq_true] at hif
        exact ⟨by simp [chainLevels], hif.1⟩
      · obtain ⟨m, hs⟩ := activeDeclaration_some required p x h
        exact ⟨by simp only [chainLevels]; exact List.mem_cons_of_mem _ m, hs⟩

theorem activeDeclaration_self (s : ScopeCtx) : activeDeclaration? s (some s) = some s := by
  cases s with
  | mk p ps op props out branches activation id =>
    simp only [activeDeclaration?, same_declaring_scope_refl, compatible_activations_refl,
      Bool.and_self, if_true]

/-- THE PRINTER-DEPENDENT PREMISE of contextual wiring: every site level that `sameDeclaringScope`
    accepts for `required` has `required`'s presence. Production asks this of a mixed pair whenever
    the site chain has an anonymous level (`forOpens` scopes, the prelude), and the answer there is
    the printed fallback. -/
def SitePresence (required : ScopeCtx) (site : Option ScopeCtx) : Prop :=
  ∀ x ∈ chainLevels site, sameDeclaringScope required x = true →
    x.declarationId.isSome = required.declarationId.isSome

/-- The existing printer residual implies the premise; it is the only known discharge in general. -/
theorem sitePresence_of_separating (hsep : ReprSeparatesPresence) (required : ScopeCtx)
    (site : Option ScopeCtx) : SitePresence required site := by
  intro x _ hs
  cases hr : required with
  | mk rp rps rop rprops rout rb ra rid =>
    cases hx : x with
    | mk xp xps xop xprops xout xb xa xid =>
      subst hr hx
      cases rid with
      | none =>
        cases xid with
        | none => rfl
        | some b =>
          simp only [sameDeclaringScope, beq_iff_eq] at hs
          exact absurd hs.symm (hsep _ _ rfl rfl)
      | some a =>
        cases xid with
        | some b => rfl
        | none =>
          simp only [sameDeclaringScope, beq_iff_eq] at hs
          exact absurd hs (hsep _ _ rfl rfl)

/-- `scopeInContext` of a follower follows and keeps its presence, under the site premise. -/
theorem scopeInContext_follows (T : PresenceTable) (a : Algorithm) (ctx : EvalCtx)
    (ha : Follows T a) (hsite : ∀ s, siteScope? ctx = some s → ChainFollows T s)
    (hp : SitePresence a.asScopeCtx (siteScope? ctx)) :
    ChainFollows T (scopeInContext a ctx) ∧
      (scopeInContext a ctx).declarationId.isSome = a.declarationId.isSome := by
  have hself := chainFollows_asScopeCtx T a ha
  unfold scopeInContext
  have hnone : a.asScopeCtx.activation = none := rfl
  simp only [hnone, Option.isSome_none, Bool.false_eq_true, if_false]
  cases hact : activeDeclaration? a.asScopeCtx (siteScope? ctx) with
  | none => exact ⟨hself, rfl⟩
  | some x =>
    obtain ⟨m, hs⟩ := activeDeclaration_some _ _ _ hact
    simp only [Option.getD_some]
    refine ⟨?_, hp x m hs⟩
    cases hsc : siteScope? ctx with
    | none => rw [hsc] at m; simp [chainLevels] at m
    | some s =>
      rw [hsc] at m
      exact chainFollows_of_mem T s x (hsite s hsc) m

/-- `childOfInContext`: the production contextual child wiring. -/
theorem follows_childOfInContext (T : PresenceTable) (parent child : Algorithm) (ctx : EvalCtx)
    (hparent : Follows T parent) (hsite : ∀ s, siteScope? ctx = some s → ChainFollows T s)
    (hp : SitePresence parent.asScopeCtx (siteScope? ctx))
    (hm : child.isModuleRoot = false)
    (ht : child.isBuiltin = false → T (declKey child.declarationId) = parent.declarationId.isNone) :
    Follows T (childOfInContext parent child ctx) := by
  obtain ⟨hs, hpres⟩ := scopeInContext_follows T parent ctx hparent hsite hp
  unfold childOfInContext
  apply follows_withParent T child _ hs
  intro hb
  rw [withParent_parent_of_not_module child _ hb hm, ht hb]
  simp only [parentAnonymous]
  cases h1 : (scopeInContext parent ctx).declarationId <;>
    cases h2 : parent.declarationId <;> simp_all

/-- `wireToCaller`: the production wiring of a written inline algorithm. -/
theorem follows_wireToCaller (T : PresenceTable) (caller : Algorithm) (rest : List Algorithm)
    (ctx : EvalCtx) (a : Algorithm) (hstack : ctx.callStack = caller :: rest)
    (hcaller : Follows T caller) (hsite : ∀ s, siteScope? ctx = some s → ChainFollows T s)
    (hp : SitePresence caller.asScopeCtx (siteScope? ctx))
    (hm : a.isModuleRoot = false)
    (ht : a.isBuiltin = false → T (declKey a.declarationId) = caller.declarationId.isNone) :
    Follows T (wireToCaller ctx a) := by
  unfold wireToCaller
  rw [hstack]
  exact follows_childOfInContext T caller a ctx hcaller hsite hp hm ht

/-- The result of `wireSelectedBranchBody` and its state: one activation record, then the body under
    the family's scope with the binders and that activation. -/
theorem wireSelectedBranchBody_run (callee body : Algorithm) (binders : List Ident) (ctx : EvalCtx)
    (env : ValEnv) (s : EvalState) :
    ∃ t, (wireSelectedBranchBody callee body binders ctx env).runState s =
      (.ok (body.withParent (some (.mk callee.parent binders callee.opens callee.props
        callee.output callee.branches (some s.lexicalActivations.size) callee.declarationId))), t) :=
  ⟨_, rfl⟩

/-- `wireSelectedBranchBody`: the branch body under its family's activated level. -/
theorem follows_wireSelectedBranchBody (T : PresenceTable) (callee body : Algorithm)
    (binders : List Ident) (id : Nat) (hcallee : Follows T callee)
    (hm : body.isModuleRoot = false)
    (ht : body.isBuiltin = false → T (declKey body.declarationId) = callee.declarationId.isNone) :
    Follows T (body.withParent (some (.mk callee.parent binders callee.opens callee.props
      callee.output callee.branches (some id) callee.declarationId))) := by
  apply follows_withParent T body _ _
  · intro hb
    rw [withParent_parent_of_not_module body _ hb hm]
    exact ht hb
  · have h := chainFollows_asScopeCtx T callee hcallee
    unfold Algorithm.asScopeCtx at h
    cases hp : callee.parent <;> simpa only [hp, ChainFollows] using h

/-- Where a structural parent-chain lookup wires its result: the production definition. -/
theorem lookupInParentsStructuralProperty_wired (name : Ident) : ∀ (sc : ScopeCtx) (r : ResolvedProperty),
    lookupInParentsStructuralProperty sc name = some r →
      ∃ level ∈ chainLevels (some sc), r.binding ∈ level.props ∧
        r.alg = r.binding.alg.withParent (some level)
  | .mk parent ps op props out branches activation id, r, h => by
      unfold lookupInParentsStructuralProperty at h
      cases hl : lookupPropDefAny? props name with
      | some prop =>
        simp only [ScopeCtx.props, hl, Option.some.injEq] at h
        subst h
        refine ⟨_, by simp [chainLevels], ?_, rfl⟩
        exact List.mem_of_find?_eq_some hl
      | none =>
        simp only [ScopeCtx.props, hl] at h
        cases parent with
        | none => simp at h
        | some p =>
          obtain ⟨level, m, hb, ha⟩ := lookupInParentsStructuralProperty_wired name p r h
          exact ⟨level, by simp only [chainLevels]; exact List.mem_cons_of_mem _ m, hb, ha⟩

/-- `lookupInParentsStructuralProperty`: a found member follows when its declaring level's
    properties are recorded at that level. -/
theorem follows_lookupInParentsStructuralProperty (T : PresenceTable) (sc : ScopeCtx) (name : Ident)
    (r : ResolvedProperty) (hs : ChainFollows T sc)
    (hl : lookupInParentsStructuralProperty sc name = some r)
    (hprops : ∀ level ∈ chainLevels (some sc), ∀ prop ∈ level.props,
      prop.alg.isBuiltin = false →
        T (declKey prop.alg.declarationId) =
          parentAnonymous (prop.alg.withParent (some level)).parent) :
    Follows T r.alg := by
  obtain ⟨level, m, hb, ha⟩ := lookupInParentsStructuralProperty_wired name sc r hl
  rw [ha]
  exact follows_withParent T _ level (chainFollows_of_mem T sc level hs m) (hprops level m _ hb)

/-! ### Runtime wrappers -/

/-- The production minting step: the next number, the wrapper's parent untouched. -/
theorem identifyRuntimeAlgorithm_run (a : Algorithm) (s : EvalState) :
    (identifyRuntimeAlgorithm a).runState s =
      (.ok (a.withDeclarationId (some (.runtime s.nextRuntimeDeclaration))),
        { s with nextRuntimeDeclaration := s.nextRuntimeDeclaration + 1 }) := rfl

/-- Record one runtime declaration. -/
def PresenceTable.mint (T : PresenceTable) (n : Nat) (b : Bool) : PresenceTable :=
  fun k => if k == some (.runtime n) then b else T k

/-- The runtime number `n` occurs nowhere in the chain. -/
def ChainFreshRuntime (n : Nat) (s : ScopeCtx) : Prop :=
  ∀ x ∈ chainLevels (some s), declKey x.declarationId ≠ some (.runtime n)

theorem mint_other (T : PresenceTable) (n : Nat) (b : Bool) (k : Option PropertyIdentity)
    (h : k ≠ some (.runtime n)) : T.mint n b k = T k := by
  simp [PresenceTable.mint, h]

theorem mint_self (T : PresenceTable) (n : Nat) (b : Bool) :
    T.mint n b (some (.runtime n)) = b := by
  simp [PresenceTable.mint]

/-- Recording a fresh number changes no existing chain's standing. -/
theorem chainFollows_mint (T : PresenceTable) (n : Nat) (b : Bool) : ∀ s : ScopeCtx,
    ChainFollows T s → ChainFreshRuntime n s → ChainFollows (T.mint n b) s
  | .mk none ps op props out branches activation id, h, hf => by
      simp only [ChainFollows] at h ⊢
      intro hid
      rw [mint_other T n b (declKey id) (hf (.mk none ps op props out branches activation id)
        (by simp [chainLevels]))]
      exact h hid
  | .mk (some p) ps op props out branches activation id, h, hf => by
      simp only [ChainFollows] at h ⊢
      refine ⟨fun hid => ?_, chainFollows_mint T n b p h.2 ?_⟩
      · rw [mint_other T n b (declKey id) (hf (.mk (some p) ps op props out branches activation id)
          (by simp [chainLevels]))]
        exact h.1 hid
      · intro x m
        exact hf x (by simp only [chainLevels]; exact List.mem_cons_of_mem _ m)

theorem withDeclarationId_parent (a : Algorithm) (id : Option PropertyIdentity) :
    (a.withDeclarationId id).parent = a.parent := by
  cases a <;> rfl

theorem withDeclarationId_declarationId (a : Algorithm) (id : Option PropertyIdentity)
    (hb : a.isBuiltin = false) : (a.withDeclarationId id).declarationId = id := by
  cases a <;> simp_all [Algorithm.isBuiltin, Algorithm.withDeclarationId, Algorithm.declarationId]

/-- A MINTED wrapper: recording its fresh number at its actual parent, the wrapper follows. -/
theorem follows_of_identifyRuntime (T : PresenceTable) (a : Algorithm) (n : Nat)
    (ha : Follows T a) (hf : ∀ p, a.parent = some p → ChainFreshRuntime n p) :
    Follows (T.mint n (parentAnonymous a.parent)) (a.withDeclarationId (some (.runtime n))) := by
  cases hb : a.isBuiltin with
  | true =>
    refine Or.inl ?_
    cases a <;> simp_all [Algorithm.isBuiltin, Algorithm.withDeclarationId]
  | false =>
    refine Or.inr ⟨?_, ?_⟩
    · rw [withDeclarationId_declarationId a _ hb, withDeclarationId_parent]
      exact mint_self T n _
    · intro p hp
      rw [withDeclarationId_parent] at hp
      rcases ha with hbb | ⟨-, hc⟩
      · simp [hb] at hbb
      · exact chainFollows_mint T n _ p (hc p hp) (hf p hp)

/-- Two independently minted wrappers are distinct identities, whatever their parents. -/
theorem minted_wrappers_distinct (a b : Algorithm) (n m : Nat) (hne : n ≠ m)
    (ha : a.isBuiltin = false) (hb : b.isBuiltin = false) :
    sameRepeatedCallableIdentity (a.withDeclarationId (some (.runtime n)))
      (b.withDeclarationId (some (.runtime m))) = false := by
  have h : ¬ sameRepeatedCallableIdentity (a.withDeclarationId (some (.runtime n)))
      (b.withDeclarationId (some (.runtime m))) = true := by
    intro hs
    rcases same_identity_parts _ _ hs with ⟨-, -⟩ | ⟨hd, -⟩
    · cases a <;> cases b <;> simp_all [Algorithm.isBuiltin, same_identity_eq, asBuiltin?,
        Algorithm.withDeclarationId, identityCore, Algorithm.declarationId,
        PropertyIdentity.callableDeclaration]
    · rw [withDeclarationId_declarationId a _ ha, withDeclarationId_declarationId b _ hb] at hd
      simp [PropertyIdentity.callableDeclaration] at hd
      exact hne hd
  simpa using h

/-! ## Entry and preparation -/

/-- The run's root context. -/
def entryCtx : EvalCtx := { callStack := [preludeAlg] }

/-- ROOT WIRING is the production wiring under the prelude's level, a kernel fact. -/
theorem wireToCaller_entry (a : Algorithm) :
    wireToCaller entryCtx a = a.withParent (some preludeAlg.asScopeCtx) := by
  have hsite : siteScope? entryCtx = some preludeAlg.asScopeCtx := rfl
  simp only [wireToCaller, entryCtx, List.head?_cons, childOfInContext, scopeInContext]
  have hself := activeDeclaration_self preludeAlg.asScopeCtx
  have h : activeDeclaration? preludeAlg.asScopeCtx (siteScope? { callStack := [preludeAlg] }) =
      some preludeAlg.asScopeCtx := by
    rw [show siteScope? { callStack := [preludeAlg] } = some preludeAlg.asScopeCtx from rfl]
    exact hself
  have hact : preludeAlg.asScopeCtx.activation = none := rfl
  simp only [hact, Option.isSome_none, Bool.false_eq_true, if_false, h, Option.getD_some]

/-- The table recording only the root declaration, wired under the anonymous prelude. -/
def entryTable (a : Algorithm) : PresenceTable := fun k => k == declKey a.declarationId

theorem prelude_chainRoot : preludeAlg.asScopeCtx.chainRoot = preludeAlg.asScopeCtx := rfl

/-- THE ENTRY BOUNDARY: whatever root identification produced follows its one-entry table once
    wired, module-marked roots included. -/
theorem entry_follows (a : Algorithm) : Follows (entryTable a) (wireToCaller entryCtx a) := by
  rw [wireToCaller_entry]
  have hprelude : ChainFollows (entryTable a) preludeAlg.asScopeCtx :=
    show (none : Option PropertyIdentity).isSome = true → _ from fun h => by simp at h
  apply follows_withParent (entryTable a) a _ hprelude
  intro hb
  have htable : entryTable a (declKey a.declarationId) = true := by simp [entryTable]
  rw [htable]
  rcases withParent_parent_cases a _ hb with h | h <;> rw [h]
  · rfl
  · rw [prelude_chainRoot]; rfl

/-- Identification gives every non-builtin its prepared identity, whatever came in. -/
theorem identifyPropertyAlgorithm_declarationId (a : Algorithm) (n : Nat) (hb : a.isBuiltin = false) :
    ((identifyPropertyAlgorithm a).run n).1.declarationId =
      some (preparedAlgorithmIdentity a.declarationId n).1 := by
  rw [identifyPropertyAlgorithm]
  cases a with
  | builtin b => simp [Algorithm.isBuiltin] at hb
  | mk p ps op pr out id => cases p <;> rfl
  | conditional p op bs id => cases p <;> rfl
  | alias p op pr t id r => cases p <;> rfl

/-- Identification keeps a level's identity slot, `none` included, and clears its activation. -/
theorem identifyPropertyScope_slots (s : ScopeCtx) (n : Nat) :
    ((identifyPropertyScope s).run n).1.declarationId = s.declarationId ∧
      ((identifyPropertyScope s).run n).1.activation = none := by
  cases s with
  | mk p ps op pr out bs act id =>
    rw [identifyPropertyScope.eq_def]
    cases p <;> exact ⟨rfl, rfl⟩

/-- So identification does NOT make every parent identified: an anonymous parent stays anonymous. -/
theorem identification_keeps_anonymous_parent (s : ScopeCtx) (ps : List ParameterPattern)
    (op : List Expr) (pr : List PropDef) (out : List Expr) (id : Option PropertyIdentity) (n : Nat)
    (hs : s.declarationId = none) :
    ∃ s', ((identifyPropertyAlgorithm (.mk (some s) ps op pr out id)).run n).1.parent = some s' ∧
      s'.declarationId = none := by
  refine ⟨((identifyPropertyScope s).run (preparedAlgorithmIdentity id n).2).1, ?_, ?_⟩
  · exact (by rw [identifyPropertyAlgorithm]; rfl :
      ((identifyPropertyAlgorithm (.mk (some s) ps op pr out id)).run n).1.parent =
        some ((identifyPropertyScope s).run (preparedAlgorithmIdentity id n).2).1)
  · exact ((identifyPropertyScope_slots s _).1).trans hs

/-- The former `partial` body of `ScopeCtx.declaration` is the total definition's equation. -/
theorem declaration_equation (s : ScopeCtx) :
    s.declaration = match s with
      | .mk p ps op props out branches _ id =>
          .mk (p.map ScopeCtx.declaration) ps op props out branches none id := by
  cases s with
  | mk p ps op pr out bs act id => cases p <;> rfl

/-- The former `partial` body of `activeDeclaration?` is the total definition's equation. -/
theorem activeDeclaration_equation (required : ScopeCtx) (level : Option ScopeCtx) :
    activeDeclaration? required level = match level with
      | none => none
      | some scope =>
          if sameDeclaringScope required scope && compatibleActivations (some required) (some scope)
          then some scope else activeDeclaration? required scope.parent := by
  cases level with
  | none => simp only [activeDeclaration?]
  | some scope => cases scope; simp only [activeDeclaration?, ScopeCtx.parent]

/-- `ScopeCtx.declaration` keeps a level's identity slot. -/
theorem declaration_declarationId (s : ScopeCtx) : s.declaration.declarationId = s.declarationId := by
  cases s with
  | mk p ps op pr out bs act id => cases p <;> rfl

/-- `ScopeCtx.declaration` erases the activation at every depth; `withActivation` is invisible to it. -/
theorem declaration_withActivation (v : Nat) (s : ScopeCtx) :
    (s.withActivation v).declaration = s.declaration := by
  cases s with
  | mk p ps op pr out bs act id => cases p <;> rfl

/-- The anonymous fallback's one kernel fact: equal declarations print equally, so two anonymous
    levels of one declaration are the same declaring scope, whatever their activations. -/
theorem same_anonymous_scope_of_declaration_eq (x y : ScopeCtx)
    (hx : x.declarationId = none) (hd : x.declaration = y.declaration) :
    sameDeclaringScope x y = true := by
  cases x with
  | mk xp xps xo xpr xout xb xa xid =>
    cases hx' : xid with
    | some _ => subst hx'; simp [ScopeCtx.declarationId] at hx
    | none =>
      subst hx'
      cases y with
      | mk yp yps yo ypr yout yb ya yid =>
        have : sameDeclaringScope (.mk xp xps xo xpr xout xb xa none)
            (.mk yp yps yo ypr yout yb ya yid) =
            (reprStr (ScopeCtx.mk xp xps xo xpr xout xb xa none).declaration ==
              reprStr (ScopeCtx.mk yp yps yo ypr yout yb ya yid).declaration) := by
          simp only [sameDeclaringScope]
        rw [this, hd]
        simp

end KatLang.CallableIdentityProvenance
