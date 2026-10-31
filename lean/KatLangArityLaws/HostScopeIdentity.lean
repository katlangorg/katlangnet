import KatLangArityLaws.RepeatedNameLaws

open KatLang KatLang.RepeatedNameLaws

/-!
# HOST-LEAN-O6: host-scope identity (October 2026)

C# keys every ORIGINAL ownerless host `ScopeCtx` object by reference, at the declaring level and at
every ancestor of a resolving chain (OD-1(a), HOST-ALIAS-R14, HOST-NESTED-1). Lean represents that
object identity as an explicit INPUT: the host-scope token `PropertyIdentity.host n` in a host
level's identity slot. These laws are about the production definitions of `lean/KatLang.lean` that
carry, compare or serialize it: `PropertyIdentity.hostToken?`, `ScopeCtx.hostChain`, `hostMarks`,
`hostKeyPrefix`, the property-cache key `zeroArgPropertyCacheKey` (`hostOwners`), the runtime-alias
keys `aliasCellKey` / `aliasChaseKey`, the declaring-scope relation `sameDeclaringScope` (NEED-04
callables, Q-19 providers, accessibility), the identification decisions
`preparedAlgorithmIdentity` / `preparedPropertyIdentity`, and the derived owner of
`lookupInParentsStructuralProperty`. All of them are TOTAL, so each statement is a kernel fact
about the definition the evaluator calls.

WHAT IS NOT CLAIMED. Lean cannot recover C# object provenance from equal values: that one host
object received one token and distinct objects distinct tokens is the encoder's obligation
(`tests/KatLang.Tests/LeanAstEncoder.cs`, a reference map), exercised by the executable differential
corpus `CoreTests/HostParentDifferential.lean`, not proved here. The partial identification pass
(`identifyPropertyScope` keeps every identity slot verbatim) and the pre-evaluation consistency check
(`hostProvenanceViolation?`) are executable (`CoreTests/HostScopeIdentity.lean`); their per-node
identity decisions are proved below. Separation statements for TEXTUAL keys rest on the prefix code
`hostMarksKeyChars`, proved injective here — no property of `reprStr` is assumed.

RESULTS.
1. Kind disjointness: `hostToken_eq_some_iff`, `host_ne_*`.
2. Preparation: `preparedAlgorithmIdentity_*`, `preparedPropertyIdentity_*` (supplied host tokens
   survive, none is ever minted, the decision is the former one off host/owned-view provenance);
   `derived_owner_host_identity` (the owner rebuilt from a host level carries its token and chain).
3/4. Reuse and separation: `cacheKey_hostOwners`, `cacheKey_eq_of_owner_components`,
   `cacheKey_separates_hostMarks`, `cacheKey_separates_ancestor` (a changed host token at ANY depth
   separates); `hostKeyPrefix_append_inj`, `aliasCellKey_separates`, `aliasChaseKey_separates`,
   `aliasCellKey_separates_ancestor`, `aliasCellKey_eq_of_components`.
5. Owned reconstruction: `hostChain_owned`, `hostChain_withActivation`,
   `hostChain_reconstruction`, `hostChain_branch_scope`.
6. The declaring-scope relation: `sameDeclaringScope_host_distinct`,
   `sameDeclaringScope_parent_distinct`, `sameRepeatedCallableIdentity_parent_distinct`.
7. Isolation: `cacheKey_hostOwners_context_free` (the new component reads neither access kind,
   binding, context, environment nor binding context).
8. Token-free compatibility and renaming: `hostMarks_tokenFree`, `cacheKey_tokenFree`,
   `aliasCellKey_tokenFree`, `aliasCellKey_eq_iff_of_tokenFree`; `hostMarks_rename`,
   `hostMarks_rename_eq_iff`.
9. Owned list views: `sharedView_declaration`, `moduleView_declaration`,
   `preparedAlgorithmIdentity_sharedView` / `_moduleView`, `sameDeclaringScope_sharedView_distinct`,
   `sameRepeatedCallableIdentity_sharedViews`, `aliasCellKey_sharedViews`. Scope comparison retains
   the component view; callable and alias declaration comparisons erase it. The encoder's existing
   context-qualified property ids are still required by cache/alias structural shapes.
10. Actual component keys: `cacheKey_componentOwners`, `cacheKey_separates_components`,
    `aliasCellKey_separates_components`, `aliasChaseKey_separates_components`,
    `cacheKey_componentFree`, `empty_component_token`. Zero is the equivalent empty-list pair;
    nonempty component tokens are global across declarations.
-/

namespace KatLang.HostScopeIdentity

/-! ## 1. Kind disjointness -/

theorem hostToken_eq_some_iff (id : Option PropertyIdentity) (n : Nat) :
    PropertyIdentity.hostToken? id = some n ↔ id = some (.host n) := by
  rcases id with _ | i
  · simp [PropertyIdentity.hostToken?]
  · cases i <;> simp [PropertyIdentity.hostToken?]

theorem host_ne_syntax (n m : Nat) : PropertyIdentity.host n ≠ .syntax m := nofun
theorem host_ne_shared (n m : Nat) : PropertyIdentity.host n ≠ .shared m := nofun
theorem host_ne_runtime (n m : Nat) : PropertyIdentity.host n ≠ .runtime m := nofun
theorem host_ne_module (n m : Nat) : PropertyIdentity.host n ≠ .module m := nofun
theorem host_ne_sharedView (n d v : Nat) : PropertyIdentity.host n ≠ .sharedView d v := nofun
theorem host_ne_moduleView (n d v : Nat) : PropertyIdentity.host n ≠ .moduleView d v := nofun

/-- Owned-view provenance preserves the declaration seen by callable/alias identity. -/
theorem sharedView_declaration (d v : Nat) :
    PropertyIdentity.callableDeclaration (some (.sharedView d v)) = some (.shared d) := rfl
theorem moduleView_declaration (d v : Nat) :
    PropertyIdentity.callableDeclaration (some (.moduleView d v)) = some (.module d) := rfl

/-- Empty component pairs are equivalent even across annotated input and runtime-created levels. -/
theorem empty_component_token (d : Nat) :
    PropertyIdentity.componentToken? (some (.sharedView d 0)) = none := rfl

/-- A declaration, module or runtime identity is never read as a host token. -/
theorem hostToken_of_not_host (i : PropertyIdentity) (h : ∀ n, i ≠ .host n) :
    PropertyIdentity.hostToken? (some i) = none := by
  cases i <;> simp_all [PropertyIdentity.hostToken?]

/-! ## 2. Preparation -/

/-- Identification keeps a supplied host identity (never renames it, so validation can refuse a
    misplaced one) and consumes no fresh number for it. -/
theorem preparedAlgorithmIdentity_host (n next : Nat) :
    preparedAlgorithmIdentity (some (.host n)) next = (.host n, next) := rfl

theorem preparedPropertyIdentity_host (n next : Nat) :
    preparedPropertyIdentity (some (.host n)) next = (.host n, next) := rfl

theorem preparedAlgorithmIdentity_sharedView (d v next : Nat) :
    preparedAlgorithmIdentity (some (.sharedView d v)) next = (.sharedView d v, next) := rfl
theorem preparedAlgorithmIdentity_moduleView (d v next : Nat) :
    preparedAlgorithmIdentity (some (.moduleView d v)) next = (.moduleView d v, next) := rfl

/-- Identification never MINTS a host identity: a host result was supplied. -/
theorem preparedAlgorithmIdentity_host_supplied (id : Option PropertyIdentity) (next n : Nat)
    (h : (preparedAlgorithmIdentity id next).1 = .host n) : id = some (.host n) := by
  unfold preparedAlgorithmIdentity at h
  split at h <;> simp_all

theorem preparedPropertyIdentity_host_supplied (id : Option PropertyIdentity) (next n : Nat)
    (h : (preparedPropertyIdentity id next).1 = .host n) : id = some (.host n) := by
  unfold preparedPropertyIdentity at h
  split at h <;> simp_all

/-- The identification decision before HOST-LEAN-O6, for algorithms. -/
def legacyAlgorithmIdentity (id : Option PropertyIdentity) (next : Nat) : PropertyIdentity × Nat :=
  match id with
  | some (.shared n) => (.shared n, next)
  | some (.module n) => (.module n, next)
  | _ => (.syntax next, next + 1)

/-- The identification decision before HOST-LEAN-O6, for properties. -/
def legacyPropertyIdentity (id : Option PropertyIdentity) (next : Nat) : PropertyIdentity × Nat :=
  match id with
  | some (.shared n) => (.shared n, next)
  | _ => (.syntax next, next + 1)

/-- Off host and owned-view provenance the algorithm decision is exactly the former one
    (ordinary unannotated source unchanged). Owned views have their own preservation law below. -/
theorem preparedAlgorithmIdentity_legacy (id : Option PropertyIdentity) (next : Nat)
    (h : PropertyIdentity.hostToken? id = none)
    (hv : PropertyIdentity.callableDeclaration id = id) :
    preparedAlgorithmIdentity id next = legacyAlgorithmIdentity id next := by
  rcases id with _ | i
  · rfl
  · cases i <;> simp_all [PropertyIdentity.hostToken?, PropertyIdentity.callableDeclaration,
      preparedAlgorithmIdentity, legacyAlgorithmIdentity]

theorem preparedPropertyIdentity_legacy (id : Option PropertyIdentity) (next : Nat)
    (h : PropertyIdentity.hostToken? id = none) :
    preparedPropertyIdentity id next = legacyPropertyIdentity id next := by
  rcases id with _ | i
  · rfl
  · cases i <;> simp_all [PropertyIdentity.hostToken?, preparedPropertyIdentity, legacyPropertyIdentity]

/-- THE DERIVED OWNER. When a level declares the looked-up name, the owner
    `lookupInParentsStructuralProperty` rebuilds from it carries the level's own identity slot — a host
    level's token — and the level's whole host chain. This is the one legitimate internal algorithm
    with a host identity; it is never an input, so the input placement rule does not apply to it. -/
theorem derived_owner_host_identity (parent : Option ScopeCtx) (params : List Ident) (opens : List Expr)
    (props : List PropDef) (output : List Expr) (branches : List CondBranch) (act : Option Nat)
    (id : Option PropertyIdentity) (name : Ident) (p : PropDef)
    (h : lookupPropDefAny? props name = some p) :
    ∃ r, lookupInParentsStructuralProperty (.mk parent params opens props output branches act id) name = some r
      ∧ r.owner.declarationId = id
      ∧ r.owner.asScopeCtx.hostChain = (ScopeCtx.mk parent params opens props output branches act id).hostChain := by
  have hl : lookupInParentsStructuralProperty (.mk parent params opens props output branches act id) name =
      some (ResolvedProperty.mk (Algorithm.mk parent (Algorithm.normalParameters params) opens props output id) p
        (Algorithm.withParent (some (ScopeCtx.mk parent params opens props output branches act id)) p.alg)) := by
    simp only [lookupInParentsStructuralProperty, ScopeCtx.props, h]
  exact ⟨_, hl, rfl, by cases parent <;> rfl⟩

/-! ## Host chains and marks -/

/-- Position `i` of a host chain is the host token of the ancestor at depth `i`. -/
theorem hostChain_get_ancestor : ∀ (sc : ScopeCtx) (i : Nat),
    sc.hostChain[i]? = (sc.ancestor? i).map (fun l => PropertyIdentity.hostToken? l.declarationId)
  | .mk parent _ _ _ _ _ _ id, 0 => by
      cases parent <;> rfl
  | .mk none _ _ _ _ _ _ _, Nat.succ i => by
      simp [ScopeCtx.hostChain, ScopeCtx.ancestor?, ScopeCtx.parent]
  | .mk (some p) _ _ _ _ _ _ _, Nat.succ i => by
      simp only [ScopeCtx.hostChain, ScopeCtx.ancestor?, ScopeCtx.parent, List.getElem?_cons_succ]
      exact hostChain_get_ancestor p i

/-- A host mark is exactly a host level at its position. -/
theorem mem_hostMarks : ∀ (c : List (Option Nat)) (d i t : Nat),
    (d + i, t) ∈ hostMarks d c ↔ c[i]? = some (some t)
  | [], d, i, t => by simp [hostMarks]
  | none :: rest, d, 0, t => by
      simp only [hostMarks, List.getElem?_cons_zero, Option.some.injEq, reduceCtorEq, iff_false, Nat.add_zero]
      intro hm
      have := marks_depth_ge rest (d + 1) d t hm
      omega
  | none :: rest, d, Nat.succ i, t => by
      simp only [hostMarks, List.getElem?_cons_succ]
      have := mem_hostMarks rest (d + 1) i t
      rwa [show d + 1 + i = d + (i + 1) by omega] at this
  | some u :: rest, d, 0, t => by
      simp only [hostMarks, List.mem_cons, Prod.mk.injEq, List.getElem?_cons_zero, Option.some.injEq,
        Nat.add_zero, true_and]
      constructor
      · rintro (h | hm)
        · exact h.symm
        · have := marks_depth_ge rest (d + 1) d t hm; omega
      · intro h; exact Or.inl h.symm
  | some u :: rest, d, Nat.succ i, t => by
      simp only [hostMarks, List.mem_cons, Prod.mk.injEq, List.getElem?_cons_succ]
      have := mem_hostMarks rest (d + 1) i t
      rw [show d + 1 + i = d + (i + 1) by omega] at this
      constructor
      · rintro (⟨h, _⟩ | hm)
        · omega
        · exact this.mp hm
      · intro h; exact Or.inr (this.mpr h)
where
  marks_depth_ge : ∀ (c : List (Option Nat)) (d e t : Nat), (e, t) ∈ hostMarks d c → d ≤ e
    | [], _, _, _, h => by simp [hostMarks] at h
    | none :: rest, d, e, t, h => by
        simp only [hostMarks] at h
        have := marks_depth_ge rest (d + 1) e t h; omega
    | some u :: rest, d, e, t, h => by
        simp only [hostMarks, List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨h, _⟩ | h
        · omega
        · have := marks_depth_ge rest (d + 1) e t h; omega

/-- Equal marks carry equal host tokens at every position. -/
theorem hostMarks_eq_get (c c' : List (Option Nat)) (h : hostMarks 0 c = hostMarks 0 c') (i t : Nat)
    (hc : c[i]? = some (some t)) : c'[i]? = some (some t) := by
  have m := (mem_hostMarks c 0 i t).mpr hc
  rw [h] at m
  exact (mem_hostMarks c' 0 i t).mp m

/-- SEPARATION AT ANY DEPTH: a host level at position `i` of one chain that the other chain does not
    have there — a different token, an evaluator-owned level, or no level — separates the marks. -/
theorem hostMarks_separate (c c' : List (Option Nat)) (i t : Nat) (hc : c[i]? = some (some t))
    (hc' : c'[i]? ≠ some (some t)) : hostMarks 0 c ≠ hostMarks 0 c' :=
  fun h => hc' (hostMarks_eq_get c c' h i t hc)

/-! ## 3/4. The property-cache owner -/

/-- The typed host component of a property-cache key is the owner chain's host marks. -/
theorem cacheKey_hostOwners (k : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (ctx : EvalCtx) (env : ValEnv) (obc : Option Nat) :
    (zeroArgPropertyCacheKey k owner binding ctx env obc).hostOwners = hostMarks 0 owner.asScopeCtx.hostChain :=
  rfl

/-- 7. ISOLATION: the host component reads only the owner — never the access kind, the binding,
    the access context, the value environment or the owner's binding context — so every existing
    environment, activation and run distinction of the key is untouched by it. -/
theorem cacheKey_hostOwners_context_free (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (b b' : PropDef) (ctx ctx' : EvalCtx) (env env' : ValEnv) (obc obc' : Option Nat) :
    (zeroArgPropertyCacheKey k owner b ctx env obc).hostOwners =
      (zeroArgPropertyCacheKey k' owner b' ctx' env' obc').hostOwners := rfl

/-- SAME-OBJECT REUSE: the key depends on its owner only through the owner's declaration, the
    structural shape of its scope and its host chain; two owners agreeing on those — one host object
    reached through several edges, an equivalent owned reconstruction under the same host ancestry —
    have one key when the remaining components agree. -/
theorem cacheKey_eq_of_owner_components (k : ZeroArgPropertyAccessKind) (o o' : Algorithm) (b : PropDef)
    (ctx : EvalCtx) (env : ValEnv) (obc : Option Nat)
    (hd : o.declarationId = o'.declarationId)
    (hs : cacheScopeShape o.asScopeCtx = cacheScopeShape o'.asScopeCtx)
    (hh : o.asScopeCtx.hostChain = o'.asScopeCtx.hostChain)
    (hc : o.asScopeCtx.componentChain = o'.asScopeCtx.componentChain) :
    zeroArgPropertyCacheKey k o b ctx env obc = zeroArgPropertyCacheKey k o' b ctx env obc := by
  simp only [zeroArgPropertyCacheKey, hd, hs, hh, hc]

/-- DISTINCT-OBJECT SEPARATION: different host marks are different keys, whatever else the two
    accesses share (declaration, property list, shape, environments). -/
theorem cacheKey_separates_hostMarks (k k' : ZeroArgPropertyAccessKind) (o o' : Algorithm) (b b' : PropDef)
    (ctx ctx' : EvalCtx) (env env' : ValEnv) (obc obc' : Option Nat)
    (h : hostMarks 0 o.asScopeCtx.hostChain ≠ hostMarks 0 o'.asScopeCtx.hostChain) :
    zeroArgPropertyCacheKey k o b ctx env obc ≠ zeroArgPropertyCacheKey k' o' b' ctx' env' obc' :=
  fun heq => h (by
    have := congrArg ZeroArgPropertyCacheKey.hostOwners heq
    simpa only [cacheKey_hostOwners] using this)

/-- A host ANCESTOR at any depth `i` of the owner's scope separates: if the ancestor there is the host
    object `t` for one owner and not for the other, the keys differ (HOST-NESTED-1). -/
theorem cacheKey_separates_ancestor (k k' : ZeroArgPropertyAccessKind) (o o' : Algorithm) (b b' : PropDef)
    (ctx ctx' : EvalCtx) (env env' : ValEnv) (obc obc' : Option Nat) (i t : Nat) (l : ScopeCtx)
    (hl : o.asScopeCtx.ancestor? i = some l) (ht : l.declarationId = some (.host t))
    (hl' : ∀ l', o'.asScopeCtx.ancestor? i = some l' → l'.declarationId ≠ some (.host t)) :
    zeroArgPropertyCacheKey k o b ctx env obc ≠ zeroArgPropertyCacheKey k' o' b' ctx' env' obc' := by
  apply cacheKey_separates_hostMarks
  apply hostMarks_separate _ _ i t
  · rw [hostChain_get_ancestor, hl]; simp [ht, PropertyIdentity.hostToken?]
  · rw [hostChain_get_ancestor]
    intro hc
    cases ha : o'.asScopeCtx.ancestor? i with
    | none => simp [ha] at hc
    | some l' =>
      simp only [ha, Option.map_some, Option.some.injEq] at hc
      exact hl' l' ha ((hostToken_eq_some_iff _ t).mp hc)

/-! ## 3/4. The runtime-alias keys: a prefix code, no `reprStr` assumption -/

theorem unaryKeyChars_append_inj : ∀ (a b : Nat) (x y : List Char),
    unaryKeyChars a ++ x = unaryKeyChars b ++ y → a = b ∧ x = y
  | 0, 0, x, y, h => by simpa [unaryKeyChars] using h
  | 0, Nat.succ _, _, _, h => by simp [unaryKeyChars] at h
  | Nat.succ _, 0, _, _, h => by simp [unaryKeyChars] at h
  | Nat.succ a, Nat.succ b, x, y, h => by
      simp only [unaryKeyChars, List.cons_append, List.cons.injEq, true_and] at h
      have := unaryKeyChars_append_inj a b x y h
      exact ⟨by omega, this.2⟩

theorem hostMarksKeyChars_append_inj : ∀ (m m' : List (Nat × Nat)) (x y : List Char),
    hostMarksKeyChars m ++ '@' :: x = hostMarksKeyChars m' ++ '@' :: y → m = m' ∧ x = y
  | [], [], x, y, h => by simpa [hostMarksKeyChars] using h
  | [], (_, _) :: _, _, _, h => by simp [hostMarksKeyChars] at h
  | (_, _) :: _, [], _, _, h => by simp [hostMarksKeyChars] at h
  | (d, t) :: rest, (d', t') :: rest', x, y, h => by
      simp only [hostMarksKeyChars, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨hd, h⟩ := unaryKeyChars_append_inj d d' _ _ h
      obtain ⟨ht, h⟩ := unaryKeyChars_append_inj t t' _ _ h
      obtain ⟨hr, hxy⟩ := hostMarksKeyChars_append_inj rest rest' x y h
      exact ⟨by rw [hd, ht, hr], hxy⟩

/-- THE PREFIX CODE: two keys opening with host prefixes are equal only if their host marks and
    their remainders are. -/
theorem hostKeyPrefix_append_inj (c c' : List (Option Nat)) (s s' : String)
    (h : hostKeyPrefix c ++ s = hostKeyPrefix c' ++ s') : hostMarks 0 c = hostMarks 0 c' ∧ s = s' := by
  have hl := congrArg String.toList h
  simp only [hostKeyPrefix, String.toList_append, String.toList_ofList, List.append_assoc] at hl
  have hat : "@".toList = ['@'] := rfl
  rw [hat] at hl
  simp only [List.singleton_append] at hl
  obtain ⟨hm, hs⟩ := hostMarksKeyChars_append_inj _ _ _ _ hl
  exact ⟨hm, String.toList_inj.mp hs⟩

/-- DISTINCT-OBJECT SEPARATION of binding cells: different host marks of the declaring chains are
    different cells (and so different resolved targets). -/
theorem aliasCellKey_separates (a b : Algorithm)
    (h : hostMarks 0 (ScopeCtx.hostChainOf a.parent) ≠ hostMarks 0 (ScopeCtx.hostChainOf b.parent)) :
    aliasCellKey a ≠ aliasCellKey b := by
  intro heq
  unfold aliasCellKey at heq
  exact h (hostKeyPrefix_append_inj (ScopeCtx.hostChainOf a.parent) (ScopeCtx.hostChainOf b.parent)
    (hostKeyPrefix (ScopeCtx.componentChainOf a.parent) ++ aliasCellShapeKey a)
    (hostKeyPrefix (ScopeCtx.componentChainOf b.parent) ++ aliasCellShapeKey b) heq).1

/-- … and different chase-visit keys, so two hosts' aliases are never a false cycle. -/
theorem aliasChaseKey_separates (a b : Algorithm)
    (h : hostMarks 0 (ScopeCtx.hostChainOf a.parent) ≠ hostMarks 0 (ScopeCtx.hostChainOf b.parent)) :
    aliasChaseKey a ≠ aliasChaseKey b := by
  intro heq
  unfold aliasChaseKey aliasCellKey at heq
  simp only [String.append_assoc] at heq
  exact h (hostKeyPrefix_append_inj _ _ _ _ heq).1

theorem hostChainOf_get_ancestor (p : Option ScopeCtx) (i : Nat) :
    (ScopeCtx.hostChainOf p)[i]? =
      (p.bind (fun sc => sc.ancestor? i)).map (fun l => PropertyIdentity.hostToken? l.declarationId) := by
  cases p with
  | none => simp [ScopeCtx.hostChainOf]
  | some sc => simpa [ScopeCtx.hostChainOf] using hostChain_get_ancestor sc i

/-- A host ancestor at any depth of the declaring chain separates binding cells. -/
theorem aliasCellKey_separates_ancestor (a b : Algorithm) (i t : Nat) (l : ScopeCtx)
    (hl : a.parent.bind (fun sc => sc.ancestor? i) = some l) (ht : l.declarationId = some (.host t))
    (hl' : ∀ l', b.parent.bind (fun sc => sc.ancestor? i) = some l' → l'.declarationId ≠ some (.host t)) :
    aliasCellKey a ≠ aliasCellKey b := by
  apply aliasCellKey_separates
  apply hostMarks_separate _ _ i t
  · rw [hostChainOf_get_ancestor, hl]; simp [ht, PropertyIdentity.hostToken?]
  · rw [hostChainOf_get_ancestor]
    intro hc
    cases ha : b.parent.bind (fun sc => sc.ancestor? i) with
    | none => simp [ha] at hc
    | some l' =>
      simp only [ha, Option.map_some, Option.some.injEq] at hc
      exact hl' l' ha ((hostToken_eq_some_iff _ t).mp hc)

/-- SAME-OBJECT REUSE of binding cells: equal host marks and equal structural parts are one cell. -/
theorem aliasCellKey_eq_of_components (a b : Algorithm)
    (hm : hostMarks 0 (ScopeCtx.hostChainOf a.parent) = hostMarks 0 (ScopeCtx.hostChainOf b.parent))
    (hc : hostMarks 0 (ScopeCtx.componentChainOf a.parent) = hostMarks 0 (ScopeCtx.componentChainOf b.parent))
    (hs : aliasCellShapeKey a = aliasCellShapeKey b) : aliasCellKey a = aliasCellKey b := by
  unfold aliasCellKey hostKeyPrefix; rw [hm, hc, hs]

/-! ## 5. Owned reconstruction -/

/-- An evaluator-owned (or anonymous) level contributes no host token: its chain is its parent's
    under one `none`, whatever its declaration, parameters, body or activation. -/
theorem hostChain_owned (parent : Option ScopeCtx) (ps : List Ident) (op : List Expr) (pr : List PropDef)
    (out : List Expr) (br : List CondBranch) (act : Option Nat) (id : Option PropertyIdentity)
    (h : PropertyIdentity.hostToken? id = none) :
    (ScopeCtx.mk parent ps op pr out br act id).hostChain = none :: ScopeCtx.hostChainOf parent := by
  cases parent <;> simp [ScopeCtx.hostChain, ScopeCtx.hostChainOf, h]

/-- Activation never changes host provenance. -/
theorem hostChain_withActivation (v : Nat) (sc : ScopeCtx) :
    (ScopeCtx.withActivation v sc).hostChain = sc.hostChain := by
  cases sc with | mk p _ _ _ _ _ _ _ => cases p <;> rfl

/-- OWNED RECONSTRUCTION: two evaluator-owned levels under the same host ancestry have one host
    chain — however their declarations, bodies and activations were rebuilt — and two under different
    host ancestries have different ones (intentionally). -/
theorem hostChain_reconstruction (p p' : Option ScopeCtx) (ps ps' : List Ident) (op op' : List Expr)
    (pr pr' : List PropDef) (out out' : List Expr) (br br' : List CondBranch) (act act' : Option Nat)
    (id id' : Option PropertyIdentity)
    (h : PropertyIdentity.hostToken? id = none) (h' : PropertyIdentity.hostToken? id' = none) :
    (ScopeCtx.mk p ps op pr out br act id).hostChain = (ScopeCtx.mk p' ps' op' pr' out' br' act' id').hostChain
      ↔ ScopeCtx.hostChainOf p = ScopeCtx.hostChainOf p' := by
  rw [hostChain_owned p ps op pr out br act id h, hostChain_owned p' ps' op' pr' out' br' act' id' h']
  simp

/-- The family scope a conditional call wires a selected branch under (`wireSelectedBranchBody`) has
    exactly its clause family's host chain. -/
theorem hostChain_branch_scope (callee : Algorithm) (names : List Ident) (id : Nat) :
    (ScopeCtx.mk callee.parent names callee.opens callee.props callee.output callee.branches (some id)
      callee.declarationId).hostChain = callee.asScopeCtx.hostChain := by
  unfold Algorithm.asScopeCtx; cases callee.parent <;> rfl

/-! ## 6. The declaring-scope relation (NEED-04, Q-19, accessibility) -/

/-- Two host levels with different tokens are never one declaring scope. -/
theorem sameDeclaringScope_host_distinct (p q : Option ScopeCtx) (ps qs : List Ident) (o o' : List Expr)
    (pr pr' : List PropDef) (out out' : List Expr) (br br' : List CondBranch) (act act' : Option Nat)
    (a b : Nat) (h : a ≠ b) :
    sameDeclaringScope (.mk p ps o pr out br act (some (.host a))) (.mk q qs o' pr' out' br' act' (some (.host b)))
      = false := by
  have hne : (PropertyIdentity.host a == PropertyIdentity.host b) = false := by
    cases hb : (PropertyIdentity.host a == PropertyIdentity.host b)
    · rfl
    · exact absurd (by simpa using property_identity_eq_of_beq _ _ hb) h
  cases p <;> cases q <;> simp [sameDeclaringScope, hne]

/-- An identified level is never the same declaring scope as one whose parent chain is a different
    declaring scope: a host ancestor separates at any depth through this recursion. -/
theorem sameDeclaringScope_parent_distinct (p q : ScopeCtx) (ps qs : List Ident) (o o' : List Expr)
    (pr pr' : List PropDef) (out out' : List Expr) (br br' : List CondBranch) (act act' : Option Nat)
    (x y : PropertyIdentity) (h : sameDeclaringScope p q = false) :
    sameDeclaringScope (.mk (some p) ps o pr out br act (some x)) (.mk (some q) qs o' pr' out' br' act' (some y))
      = false := by
  show ((x == y && ps == qs) && sameDeclaringScope p q) = false
  rw [h]; simp

/-- NEED-04 and Q-19 compare algorithms by `sameRepeatedCallableIdentity`: two user algorithms whose
    declaring scopes differ — a different host object anywhere on the compared chains — are two
    callables (two providers), whatever their declaration. -/
theorem sameRepeatedCallableIdentity_parent_distinct (p q : ScopeCtx) (ps qs : List ParameterPattern)
    (o o' : List Expr) (pr pr' : List PropDef) (out out' : List Expr) (d d' : Option PropertyIdentity)
    (h : sameDeclaringScope p q = false) :
    sameRepeatedCallableIdentity (.mk (some p) ps o pr out d) (.mk (some q) qs o' pr' out' d') = false := by
  show (((PropertyIdentity.callableDeclaration d == PropertyIdentity.callableDeclaration d' && sameDeclaringScope p q) && compatibleActivations (some p) (some q)) &&
    compatibleActivations (some q) (some p)) = false
  rw [h]; simp

/-! ## 8. Token-free compatibility and renaming -/

/-- Distinct component views of one declaration are distinct declaring scopes, even if every
    printed field and host ancestor is equal. -/
theorem sameDeclaringScope_sharedView_distinct (p : Option ScopeCtx) (ps : List Ident)
    (op : List Expr) (pr : List PropDef) (out : List Expr) (br : List CondBranch) (act : Option Nat)
    (d v w : Nat) (h : v ≠ w) :
    sameDeclaringScope (.mk p ps op pr out br act (some (.sharedView d v)))
      (.mk p ps op pr out br act (some (.sharedView d w))) = false := by
  have hn : (PropertyIdentity.sharedView d v == PropertyIdentity.sharedView d w) = false := by
    simp [BEq.beq, instBEqPropertyIdentity.beq, h]
  cases p <;> simp [sameDeclaringScope, hn]

/-- Replacing a callable's own component lists never changes its declaration identity. Its
    declaring parent and captured activations remain determinants. -/
theorem sameRepeatedCallableIdentity_sharedViews (p : Option ScopeCtx) (ps qs : List ParameterPattern)
    (op oq : List Expr) (pr qr : List PropDef) (out output : List Expr) (d v w : Nat) :
    sameRepeatedCallableIdentity (.mk p ps op pr out (some (.sharedView d v)))
      (.mk p qs oq qr output (some (.sharedView d w))) = true := by
  cases p <;> simp [sameRepeatedCallableIdentity, Algorithm.declarationId, Algorithm.parent,
    PropertyIdentity.callableDeclaration,
    same_declaring_scope_refl, compatible_activations_refl]

/-- Alias cells compare their own declaration, not their own component-list view. -/
theorem aliasCellKey_sharedViews (a : Algorithm) (d v w : Nat) :
    aliasCellKey (a.withDeclarationId (some (.sharedView d v))) =
      aliasCellKey (a.withDeclarationId (some (.sharedView d w))) := by
  cases a <;> rfl

/-- A chain with no host level has no marks. -/
theorem hostMarks_tokenFree : ∀ (d : Nat) (c : List (Option Nat)), (∀ x ∈ c, x = none) → hostMarks d c = []
  | _, [], _ => rfl
  | d, none :: rest, h => hostMarks_tokenFree (d + 1) rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
  | _, some _ :: _, h => by simp at h

/-- On a host-token-free owner the host field is constant `[]`. Ordinary unannotated source also
    satisfies `cacheKey_componentFree`, so both added typed fields are constant there. -/
theorem cacheKey_tokenFree (k : ZeroArgPropertyAccessKind) (owner : Algorithm) (b : PropDef) (ctx : EvalCtx)
    (env : ValEnv) (obc : Option Nat) (h : ∀ x ∈ owner.asScopeCtx.hostChain, x = none) :
    (zeroArgPropertyCacheKey k owner b ctx env obc).hostOwners = [] :=
  hostMarks_tokenFree 0 _ h

/-- The host prefix is constant on a host-token-free chain; component provenance is independent.
    With neither annotation, `aliasCellKey_eq_iff_of_tokenFree` gives legacy equality decisions. -/
theorem aliasCellKey_tokenFree (a : Algorithm) (h : ∀ x ∈ ScopeCtx.hostChainOf a.parent, x = none) :
    aliasCellKey a = "@" ++ hostKeyPrefix (ScopeCtx.componentChainOf a.parent) ++ aliasCellShapeKey a := by
  unfold aliasCellKey hostKeyPrefix
  rw [hostMarks_tokenFree 0 _ h]
  rfl

/-- … so two token-free aliases share a cell exactly when they did before HOST-LEAN-O6. -/
theorem aliasCellKey_eq_iff_of_tokenFree (a b : Algorithm) (ha : ∀ x ∈ ScopeCtx.hostChainOf a.parent, x = none)
    (hb : ∀ x ∈ ScopeCtx.hostChainOf b.parent, x = none)
    (hca : ∀ x ∈ ScopeCtx.componentChainOf a.parent, x = none)
    (hcb : ∀ x ∈ ScopeCtx.componentChainOf b.parent, x = none) :
    aliasCellKey a = aliasCellKey b ↔ aliasCellShapeKey a = aliasCellShapeKey b := by
  rw [aliasCellKey_tokenFree a ha, aliasCellKey_tokenFree b hb]
  simp only [hostKeyPrefix, hostMarks_tokenFree 0 _ hca, hostMarks_tokenFree 0 _ hcb]
  constructor
  · intro h; exact (String.append_right_inj "@@").mp h
  · intro h; rw [h]

/-- Component marks are a typed field of the actual production cache key, not a printer fact. -/
theorem cacheKey_componentOwners (k : ZeroArgPropertyAccessKind) (owner : Algorithm) (b : PropDef)
    (ctx : EvalCtx) (env : ValEnv) (obc : Option Nat) :
    (zeroArgPropertyCacheKey k owner b ctx env obc).componentOwners =
      hostMarks 0 owner.asScopeCtx.componentChain := rfl

theorem cacheKey_separates_components (k : ZeroArgPropertyAccessKind) (a b : Algorithm) (p : PropDef)
    (ctx : EvalCtx) (env : ValEnv) (obc : Option Nat)
    (h : hostMarks 0 a.asScopeCtx.componentChain ≠ hostMarks 0 b.asScopeCtx.componentChain) :
    zeroArgPropertyCacheKey k a p ctx env obc ≠ zeroArgPropertyCacheKey k b p ctx env obc := by
  intro eq
  exact h (congrArg ZeroArgPropertyCacheKey.componentOwners eq)

/-- Alias parent component identity survives even when that parent declares no property. -/
theorem aliasCellKey_separates_components (a b : Algorithm)
    (h : hostMarks 0 (ScopeCtx.componentChainOf a.parent) ≠ hostMarks 0 (ScopeCtx.componentChainOf b.parent)) :
    aliasCellKey a ≠ aliasCellKey b := by
  intro eq
  unfold aliasCellKey at eq
  have rest := (hostKeyPrefix_append_inj (ScopeCtx.hostChainOf a.parent) (ScopeCtx.hostChainOf b.parent)
    (hostKeyPrefix (ScopeCtx.componentChainOf a.parent) ++ aliasCellShapeKey a)
    (hostKeyPrefix (ScopeCtx.componentChainOf b.parent) ++ aliasCellShapeKey b) eq).2
  exact h (hostKeyPrefix_append_inj (ScopeCtx.componentChainOf a.parent) (ScopeCtx.componentChainOf b.parent)
    (aliasCellShapeKey a) (aliasCellShapeKey b) rest).1

theorem aliasChaseKey_separates_components (a b : Algorithm)
    (h : hostMarks 0 (ScopeCtx.componentChainOf a.parent) ≠ hostMarks 0 (ScopeCtx.componentChainOf b.parent)) :
    aliasChaseKey a ≠ aliasChaseKey b := by
  intro eq
  unfold aliasChaseKey aliasCellKey at eq
  simp only [String.append_assoc] at eq
  have rest := (hostKeyPrefix_append_inj (ScopeCtx.hostChainOf a.parent) (ScopeCtx.hostChainOf b.parent)
    _ _ eq).2
  exact h (hostKeyPrefix_append_inj (ScopeCtx.componentChainOf a.parent) (ScopeCtx.componentChainOf b.parent)
    _ _ rest).1

theorem cacheKey_componentFree (k : ZeroArgPropertyAccessKind) (owner : Algorithm) (b : PropDef)
    (ctx : EvalCtx) (env : ValEnv) (obc : Option Nat)
    (h : ∀ x ∈ owner.asScopeCtx.componentChain, x = none) :
    (zeroArgPropertyCacheKey k owner b ctx env obc).componentOwners = [] := hostMarks_tokenFree 0 _ h

/-- Renaming every host token of a chain by `f`. -/
def renameHostChain (f : Nat → Nat) (c : List (Option Nat)) : List (Option Nat) := c.map (Option.map f)

theorem hostMarks_rename (f : Nat → Nat) : ∀ (d : Nat) (c : List (Option Nat)),
    hostMarks d (renameHostChain f c) = (hostMarks d c).map (fun m => (m.1, f m.2))
  | _, [] => rfl
  | d, none :: rest => by simpa [renameHostChain, hostMarks] using hostMarks_rename f (d + 1) rest
  | d, some _ :: rest => by simpa [renameHostChain, hostMarks] using hostMarks_rename f (d + 1) rest

/-- RENAMING: a coherent INJECTIVE renaming of host tokens changes the stored token values but
    preserves every equality decision between host components. -/
theorem hostMarks_rename_eq_iff (f : Nat → Nat) (hf : ∀ a b, f a = f b → a = b) (c c' : List (Option Nat)) :
    hostMarks 0 (renameHostChain f c) = hostMarks 0 (renameHostChain f c') ↔ hostMarks 0 c = hostMarks 0 c' := by
  rw [hostMarks_rename, hostMarks_rename]
  constructor
  · intro h
    refine (List.map_inj_right (fun m m' hm => ?_)).mp h
    simp only [Prod.mk.injEq] at hm
    exact Prod.ext hm.1 (hf _ _ hm.2)
  · intro h; rw [h]

end KatLang.HostScopeIdentity
