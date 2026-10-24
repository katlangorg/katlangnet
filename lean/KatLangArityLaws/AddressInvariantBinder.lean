import KatLangArityLaws.AddressInvariantSpecs

open KatLang KatLang.NeedControl.Allocation KatLang.HeapAddressValidity KatLang.AddressInvariant

/-!
# FG-H1-FU-01 (M2): the binder and the clause-family dispatcher under `Inv`

The ONE Model-C binder (`NeedBinder.bindOne` / `bindSources` / `bindPatterns`), the clause search
(`chooseBranch`, `selectFamily`) and their production instances (`bindNeedPatterns`,
`selectNeedFamilyBranch`) return a valid callee need environment and keep `Inv` on success,
non-match and every error, for EVERY capability record satisfying `CapsSpec`. Unlike FG-H1's
`CapsSound`, `CapsSpec` asks the VALUE capability for a VALID RESULT (`CRV`): a structural pattern
allocates one Ready cell per opened item of that value, and `Inv` covers Ready payloads.
-/

namespace KatLang.AddressInvariant

/-! ## Opened items of a valid value are valid -/

section Items
variable {h : Array NeedCell}

theorem RV.toItems {r : Result} (v : RV h r) : RLV h r.toItems := by
  cases r with
  | sequenceValue xs => exact RV.seq_iff.1 v
  | _ => exact RLV.singleton v

theorem RV.spreadItems {r : Result} (v : RV h r) : RLV h r.spreadItems := by
  cases r with
  | listValue xs => exact RV.list_iff.1 v
  | _ => exact RV.toItems v

theorem RV.projectionItems {r : Result} (v : RV h r) : RLV h r.projectionItems := by
  cases r with
  | listValue xs => exact RV.list_iff.1 v
  | _ => exact RV.toItems v

theorem RV.sequencePatternItems {r : Result} {xs : List Result} (v : RV h r)
    (e : r.sequencePatternItems? = some xs) : RLV h xs := by
  cases r <;> simp [Result.sequencePatternItems?] at e
  subst e; exact RV.seq_iff.1 v

theorem RV.listPatternItems {r : Result} {xs : List Result} (v : RV h r)
    (e : r.listPatternItems? = some xs) : RLV h xs := by
  cases r <;> simp [Result.listPatternItems?] at e
  subst e; exact RV.list_iff.1 v

theorem RV.structureItems {r : Result} {xs : List Result} (v : RV h r)
    (e : r.structureItems? = some xs) : RLV h xs := by
  cases r <;> simp [Result.structureItems?] at e
  · subst e; exact RV.seq_iff.1 v
  · subst e; exact RV.list_iff.1 v

theorem RV.select {r x : Result} {i : Nat} (v : RV h r) (e : r.select? i = some x) : RV h x :=
  (RV.projectionItems v).getElem? e

end Items

attribute [ht_lemmas] RV.toItems RV.spreadItems RV.projectionItems RV.sequencePatternItems
  RV.listPatternItems RV.structureItems RV.select
attribute [ht_fwd] RV.sequencePatternItems RV.listPatternItems RV.structureItems RV.select

/-! ## Capabilities -/

/-- The binder's capability contract under `Inv`: VALUE returns a valid result, CALLABLE keeps the
    invariant, allocation stores a valid suspension, META returns a valid adapter. -/
structure CapsSpec (caps : NeedCapabilities EvalM) : Prop where
  value : DemandSpec caps.value
  callable : ProjectSpec caps.callable
  allocate : ∀ susp, SoundI (fun h => SuspV h susp) (caps.allocate susp) (fun a h => a < h.size)
  reference : ∀ a, SoundI (fun h => a < h.size) (caps.reference a) (fun r h => r < h.size)

theorem CapsSpec.value_app {P : Array NeedCell → Prop} {caps : NeedCapabilities EvalM} (hc : CapsSpec caps)
    {a : Nat} (hreq : ∀ h, P h → a < h.size) : SoundI P (caps.value a) (fun r h => CRV h r) :=
  hc.value.app hreq
theorem CapsSpec.callable_app {P : Array NeedCell → Prop} {caps : NeedCapabilities EvalM} (hc : CapsSpec caps)
    {a : Nat} (hreq : ∀ h, P h → a < h.size) : SoundI P (caps.callable a) (fun _ _ => True) :=
  hc.callable.app hreq
theorem CapsSpec.allocate_app {P : Array NeedCell → Prop} {caps : NeedCapabilities EvalM} (hc : CapsSpec caps)
    {susp : NeedSuspension} (hreq : ∀ h, P h → SuspV h susp) :
    SoundI P (caps.allocate susp) (fun a h => a < h.size) :=
  SoundI.weaken (hc.allocate susp) hreq (fun _ _ g v => SuspV.mono g v) (fun _ _ h => h)
theorem CapsSpec.reference_app {P : Array NeedCell → Prop} {caps : NeedCapabilities EvalM} (hc : CapsSpec caps)
    {a : Nat} (hreq : ∀ h, P h → a < h.size) : SoundI P (caps.reference a) (fun r h => r < h.size) :=
  SoundI.weaken (hc.reference a) hreq (hmono_lt a) (fun _ _ h => h)

attribute [ht_spec] CapsSpec.value_app CapsSpec.callable_app CapsSpec.allocate_app CapsSpec.reference_app

theorem OptEnvValid.mono {h h' : Array NeedCell} (g : h.size ≤ h'.size) {r : Option NeedEnv}
    (v : OptEnvValid r h) : OptEnvValid r h' := fun env e => ValidNeedEnv.mono g (v env e)
theorem OptEnvValid.get_some {h : Array NeedCell} {env : NeedEnv} (v : OptEnvValid (Option.some env) h) :
    ValidNeedEnv h env := v env rfl
theorem OptEnvValid.nothing {h : Array NeedCell} : OptEnvValid Option.none h := fun _ e => by cases e
theorem OptEnvValid.of_valid {h : Array NeedCell} {env : NeedEnv} (v : ValidNeedEnv h env) :
    OptEnvValid (Option.some env) h := fun _ e => by cases e; exact v
attribute [ht_lemmas] OptEnvValid.get_some OptEnvValid.nothing OptEnvValid.of_valid
attribute [ht_fwd] OptEnvValid.get_some

set_option hygiene false in
macro_rules | `(tactic| ht_pmono) => `(tactic| (intro _ _ _ g v; exact OptEnvValid.mono g v))

theorem ValidNeedEnv.singleton {h : Array NeedCell} {name : Ident} {a : Nat} (v : a < h.size) :
    ValidNeedEnv h [(name, a)] := by
  intro p m
  simp only [List.mem_singleton] at m
  subst m; exact v
theorem ValidNeedEnv.nil {h : Array NeedCell} : ValidNeedEnv h [] := fun _ m => by cases m
attribute [ht_lemmas] ValidNeedEnv.singleton ValidNeedEnv.nil

theorem bindName_spec {P : Array NeedCell → Prop} {caps : NeedCapabilities EvalM} (hc : CapsSpec caps)
    {name : Ident} {address : Nat} {repeated : List Ident} {bound : NeedEnv} {family : Bool}
    (hreq : ∀ h, P h → address < h.size ∧ ValidNeedEnv h bound) :
    SoundI P (NeedBinder.bindName caps name address repeated bound family) (fun r h => OptEnvValid r h) := by
  unfold NeedBinder.bindName; ht_tac

attribute [ht_spec] bindName_spec

theorem sourceAddress_spec {P : Array NeedCell → Prop} {caps : NeedCapabilities EvalM} (hc : CapsSpec caps)
    {source : NeedSource Nat} (hreq : ∀ h, P h → ValidSource h source) :
    SoundI P (NeedBinder.sourceAddress caps.allocate source) (fun a h => a < h.size) := by
  cases source <;> (unfold NeedBinder.sourceAddress; ht_tac)

attribute [ht_spec] sourceAddress_spec

theorem cardinalityGate_spec {P : Array NeedCell → Prop} {patterns : List NeedPattern} {count : Nat}
    {family : Bool} {accepted : EvalM (Option NeedEnv)}
    (ha : SoundI P accepted (fun r h => OptEnvValid r h)) :
    SoundI P (NeedBinder.cardinalityGate patterns count family accepted) (fun r h => OptEnvValid r h) := by
  unfold NeedBinder.cardinalityGate
  split
  · split
    · exact SoundI.pure _ (fun _ _ => OptEnvValid.nothing)
    · exact SoundI.throw _
  · exact ha

attribute [ht_spec] cardinalityGate_spec

theorem ValidSource.mono {h h' : Array NeedCell} (g : h.size ≤ h'.size) {s : NeedSource Nat}
    (v : ValidSource h s) : ValidSource h' s := by
  cases s with
  | cell a => exact Nat.lt_of_lt_of_le v g
  | collector sl => exact ValidAddresses.mono g v
  | missing => trivial

/-- Every source of a level is valid. -/
def SourcesV (h : Array NeedCell) (sources : List (NeedSource Nat)) : Prop :=
  ∀ source ∈ sources, ValidSource h source

theorem SourcesV.mono {h h' : Array NeedCell} (g : h.size ≤ h'.size) {s : List (NeedSource Nat)}
    (v : SourcesV h s) : SourcesV h' s := fun x m => ValidSource.mono g (v x m)
theorem SourcesV.headD {h : Array NeedCell} {s : List (NeedSource Nat)} (v : SourcesV h s) :
    ValidSource h (s.headD .missing) := headD_valid v
theorem SourcesV.tail {h : Array NeedCell} {s : List (NeedSource Nat)} (v : SourcesV h s) :
    SourcesV h s.tail := fun x m => v x (List.mem_of_mem_tail m)
theorem SourcesV.level {h : Array NeedCell} {cells : List Nat} (v : ValidAddresses h cells)
    (patterns : List NeedPattern) : SourcesV h (needLevelSources patterns cells) :=
  needLevelSources_valid v patterns
attribute [ht_lemmas] SourcesV.headD SourcesV.tail SourcesV.level

set_option hygiene false in
macro_rules | `(tactic| ht_hmono) => `(tactic| (intro _ _ g v; split_ands; exact ⟨SourcesV.mono g ‹_›, ValidNeedEnv.mono g ‹_›⟩))
set_option hygiene false in
macro_rules | `(tactic| mono_atom $g) => `(tactic| exact SourcesV.mono $g ‹_›)

/-- **The binder.** -/
theorem binder_spec (caps : NeedCapabilities EvalM) (hc : CapsSpec caps) (repeated : List Ident)
    (family : Bool) :
    (∀ pattern address bound, SoundI (fun h => address < h.size ∧ ValidNeedEnv h bound)
        (NeedBinder.bindOne caps pattern address repeated bound family) (fun r h => OptEnvValid r h)) ∧
    (∀ patterns sources current,
      SoundI (fun h => SourcesV h sources ∧ ValidNeedEnv h current)
        (NeedBinder.bindSources caps patterns sources repeated current family) (fun r h => OptEnvValid r h)) := by
  refine NeedBinder.bindOne.mutual_induct
    (motive_1 := fun pattern address bound =>
      SoundI (fun h => address < h.size ∧ ValidNeedEnv h bound)
        (NeedBinder.bindOne caps pattern address repeated bound family) (fun r h => OptEnvValid r h))
    (motive_2 := fun patterns sources current =>
      SoundI (fun h => SourcesV h sources ∧ ValidNeedEnv h current)
        (NeedBinder.bindSources caps patterns sources repeated current family) (fun r h => OptEnvValid r h))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro address bound name collecting
    simp only [NeedBinder.bindOne]
    exact bindName_spec hc (fun h ph => ph)
  · intro address bound name
    simp only [NeedBinder.bindOne]
    refine SoundI.bind (SoundI.tryCatch (hc.reference_app (fun h ph => ph.1)) (fun _ => SoundI.throw _))
      (fun _ _ _ g v => Nat.lt_of_lt_of_le v g) ?_
    intro adapter
    exact bindName_spec hc (fun h ph => ⟨ph.2, ph.1.2⟩)
  · intro address bound literal
    simp only [NeedBinder.bindOne]
    refine SoundI.bind (hc.value_app (fun h ph => ph.1)) (fun _ _ _ g v => CRV.mono g v) ?_
    intro pair
    exact SoundI.pure _ (fun h ph env he => by
      split at he
      · cases he; exact ph.1.2
      · cases he)
  · intro address bound ps ih
    simp only [NeedBinder.bindOne]
    ht_tac
  · intro address bound ps ih
    simp only [NeedBinder.bindOne]
    ht_tac
  · intro address bound ps ih
    simp only [NeedBinder.bindOne]
    ht_tac
  · intro sources current
    simp only [NeedBinder.bindSources]
    ht_tac
  · intro sources current pattern rest ih1 ih2
    simp only [NeedBinder.bindSources]
    ht_tac

theorem bindSources_spec {P : Array NeedCell → Prop} {caps : NeedCapabilities EvalM} (hc : CapsSpec caps)
    {patterns : List NeedPattern} {sources : List (NeedSource Nat)} {repeated : List Ident}
    {current : NeedEnv} {family : Bool} (hreq : ∀ h, P h → SourcesV h sources ∧ ValidNeedEnv h current) :
    SoundI P (NeedBinder.bindSources caps patterns sources repeated current family)
      (fun r h => OptEnvValid r h) :=
  SoundI.weaken ((binder_spec caps hc repeated family).2 patterns sources current) hreq
    (fun _ _ g v => ⟨SourcesV.mono g v.1, ValidNeedEnv.mono g v.2⟩) (fun _ _ h => h)

attribute [ht_spec] bindSources_spec

/-- **The pattern-level binder.** From valid supplied cells, a valid callee need environment. -/
theorem bindPatterns_spec {P : Array NeedCell → Prop} {caps : NeedCapabilities EvalM} (hc : CapsSpec caps)
    {patterns : List NeedPattern} {cells : List Nat} {family : Bool}
    (hreq : ∀ h, P h → ValidAddresses h cells) :
    SoundI P (NeedBinder.bindPatterns caps patterns cells family) (fun r h => OptEnvValid r h) := by
  unfold NeedBinder.bindPatterns NeedBinder.bindLevel; ht_tac

attribute [ht_spec] bindPatterns_spec

/-- The activation contract of a family dispatch: from the valid bindings of the selected
    clause, under the fixed caller requirement `R`. -/
def ActivateSpec {β : Type} (R : Array NeedCell → Prop) (activate : CondBranch → NeedEnv → EvalM β)
    (Q : β → Array NeedCell → Prop) : Prop :=
  ∀ branch bindings, SoundI (fun h => R h ∧ ValidNeedEnv h bindings) (activate branch bindings) Q

theorem ActivateSpec.app {P R : Array NeedCell → Prop} {β : Type} {activate : CondBranch → NeedEnv → EvalM β}
    {Q : β → Array NeedCell → Prop} (ha : ActivateSpec R activate Q) (hR : HMono R) {branch : CondBranch}
    {bindings : NeedEnv} (hreq : ∀ h, P h → R h ∧ ValidNeedEnv h bindings) :
    SoundI P (activate branch bindings) Q :=
  SoundI.weaken (ha branch bindings) hreq (fun _ _ g v => ⟨hR _ _ g v.1, ValidNeedEnv.mono g v.2⟩)
    (fun _ _ h => h)

attribute [ht_spec] ActivateSpec.app

theorem chooseBranch_spec {P R : Array NeedCell → Prop} {β : Type} {caps : NeedCapabilities EvalM}
    (hc : CapsSpec caps) {cells : List Nat} {calleeName : String}
    {activate : CondBranch → NeedEnv → EvalM β} {Q : β → Array NeedCell → Prop}
    (ha : ActivateSpec R activate Q) (hR : HMono R) {branches : List CondBranch}
    (hreq : ∀ h, P h → R h ∧ ValidAddresses h cells) :
    SoundI P (NeedBinder.chooseBranch caps cells calleeName activate branches) Q := by
  induction branches generalizing P with
  | nil => unfold NeedBinder.chooseBranch; ht_tac
  | cons b rest ih =>
    unfold NeedBinder.chooseBranch
    refine SoundI.bind (bindPatterns_spec hc (fun h ph => (hreq h ph).2))
      (fun _ _ _ g v => OptEnvValid.mono g v) ?_
    intro r
    cases r with
    | none => exact ih (fun h ph => hreq h ph.1)
    | some bindings =>
      exact ha.app hR (fun h ph => ⟨(hreq h ph.1).1, ph.2 bindings rfl⟩)

attribute [ht_spec] chooseBranch_spec

theorem selectFamily_spec {P R : Array NeedCell → Prop} {β : Type} {caps : NeedCapabilities EvalM}
    (hc : CapsSpec caps) {callee : Algorithm} {cells : List Nat} {calleeName : String}
    {activate : CondBranch → NeedEnv → EvalM β} {Q : β → Array NeedCell → Prop}
    (ha : ActivateSpec R activate Q) (hR : HMono R)
    (hreq : ∀ h, P h → R h ∧ ValidAddresses h cells) :
    SoundI P (NeedBinder.selectFamily caps callee cells calleeName activate) Q := by
  unfold NeedBinder.selectFamily; ht_tac

/-! ## The production binder -/

/-- The binder channels under `Inv`: VALUE returns a valid result, CALLABLE keeps the invariant. -/
structure ChannelsSpec (channels : NeedChannels) : Prop where
  value : DemandSpec channels.value
  callable : ProjectSpec channels.callable

theorem capabilities_spec {channels : NeedChannels} (hc : ChannelsSpec channels) :
    CapsSpec (NeedChannels.capabilities channels) :=
  ⟨hc.value, hc.callable, fun _ => allocate_spec (fun _ h => h), fun _ => reference_spec⟩

attribute [ht_lemmas] capabilities_spec

/-- **Production binder** (`bindNeedPatterns`) at any channels satisfying `ChannelsSpec`. -/
theorem bindNeedPatterns_spec {P : Array NeedCell → Prop} {channels : NeedChannels}
    (hc : ChannelsSpec channels) {patterns : List NeedPattern} {cells : List Nat} {family : Bool}
    (hreq : ∀ h, P h → ValidAddresses h cells) :
    SoundI P (bindNeedPatterns channels patterns cells family) (fun r h => OptEnvValid r h) :=
  bindPatterns_spec (capabilities_spec hc) hreq

attribute [ht_spec] bindNeedPatterns_spec

/-- **Production clause-family dispatch** (`selectNeedFamilyBranch` with `needActivateBranch`):
    the activated body's context and values are valid. -/
theorem selectNeedFamilyBranch_spec {P : Array NeedCell → Prop} {channels : NeedChannels}
    (hc : ChannelsSpec channels) {callee : Algorithm} {cells : List Nat} {ctx : EvalCtx} {env : ValEnv}
    {calleeName : String} (hreq : ∀ h, P h → ValidAddresses h cells ∧ ValidCtx h ctx ∧ VEV h env) :
    SoundI P (selectNeedFamilyBranch channels callee cells ctx env calleeName)
      (fun r h => ValidCtx h r.2.1 ∧ VEV h r.2.2) := by
  unfold selectNeedFamilyBranch
  refine selectFamily_spec (R := fun h => ValidCtx h ctx ∧ VEV h env) (capabilities_spec hc) ?_
    (hmono_ctx_env ctx env) (fun h ph => ⟨⟨(hreq h ph).2.1, (hreq h ph).2.2⟩, (hreq h ph).1⟩)
  intro branch bindings
  exact needActivateBranch_spec (fun h ph => ⟨ph.1.1, ph.1.2, ph.2⟩)

attribute [ht_spec] selectNeedFamilyBranch_spec

/-- The two total shells (`NeedChannels.shell`) over contract-satisfying callbacks. -/
theorem shell_spec {ev : Nat → Expr → EvalCtx → ValEnv → EvalM CountedResult} {route : NeedPlan.Route}
    {demand : Nat → EvalM CountedResult} {written : Nat → Expr → EvalCtx → EvalM (Option Algorithm)}
    (hev : ∀ a, EvSpec (ev a)) (hr : RouteSpec route) (hd : DemandSpec demand)
    (hw : ∀ a, WrittenSpec (written a)) : ChannelsSpec (NeedChannels.shell ev route demand written) :=
  ⟨fun a => demandStep_spec (hev a) hr hd, fun a => projStep_spec (projSuspended_spec (hw a))⟩

end KatLang.AddressInvariant
