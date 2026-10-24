import KatLangArityLaws.AddressInvariantBinder

open KatLang KatLang.NeedControl.Allocation KatLang.HeapAddressValidity KatLang.AddressInvariant
open KatLang.CallPlan (bind_run get_run pure_run modify_run throw_run lift_run evalAttempt_run)

/-!
# FG-H1-FU-01 (M2): pure result shaping, loops, selection, rows and the alias write points

* Every pure operation the evaluator applies to results only rearranges, wraps or drops the
  results it is given, or builds address-free values, so it maps valid results to valid results
  (`RV.normalize`, `countedTopLevelValues_valid`, `openSpreadItems_valid`, …).
* The recursive helpers with callbacks (`selectWith`, `selectViewWith`, `interpolateWith`,
  `OutputRows.formLeftToRight`, `WhileRound.discover`) keep `Inv` whenever their callbacks keep
  it under the caller's own precondition (a callback contract `∀ x, SoundI (P ∧ …) (cb x) Q`,
  which `ht_tac` proves inline at the call site).
* The alias write points: `aliasBindingCellRecorded` records a valid address in `aliasCells`;
  `aliasBareCell` writes back the cell it read BEFORE three intermediate operations — valid in
  the earlier heap, hence in the current one — with a fresh valid `aliasBare`;
  `takeTerminalAliasInvocation` claims a cell (`aliasUse` only) and returns a recorded address.
-/

namespace KatLang.AddressInvariant

/-! ## Pure operations on results -/

section Pure
variable {h : Array NeedCell}

theorem RV.normalize : ∀ {r : Result}, RV h r → RV h r.normalize
  | .atom _, v => by simpa [Result.normalize] using v
  | .str _, v => by simpa [Result.normalize] using v
  | .bool _, v => by simpa [Result.normalize] using v
  | .callRef _, v => by simpa [Result.normalize] using v
  | .argView _, v => by simpa [Result.normalize] using v
  | .sequenceValue rs, v => by
    have hs : RLV h (rs.map Result.normalize) := by
      intro x m
      obtain ⟨y, my, rfl⟩ := List.mem_map.mp m
      exact RV.normalize (RV.seq_iff.1 v y my)
    simp only [Result.normalize]
    split
    · rename_i r hr; exact hs r (by rw [hr]; exact List.mem_cons_self)
    · exact RV.seq hs
  | .listValue rs, v => by
    simp only [Result.normalize]
    refine RV.list (fun x m => ?_)
    obtain ⟨y, my, rfl⟩ := List.mem_map.mp m
    exact RV.normalize (RV.list_iff.1 v y my)

theorem countedTopLevelValues_valid {p : CountedResult} (v : CRV h p) : RLV h (countedTopLevelValues p) := by
  obtain ⟨r, n⟩ := p
  have v' : RV h r := v
  match n with
  | 0 => exact RLV.nil
  | 1 => exact RLV.singleton v'
  | Nat.succ (Nat.succ k) => exact RV.toItems v'

theorem combineOutputSlots_valid {xs : List Result} (v : RLV h xs) : RV h (combineOutputSlots xs) := by
  unfold combineOutputSlots
  split
  · exact v.head
  · exact RV.seq v

theorem spreadSupplyResult_valid {xs : List Result} (v : RLV h xs) : CRV h (spreadSupplyResult xs) :=
  RV.normalize (RV.seq v)

theorem openSpreadItems_valid : ∀ {n : Nat} {r : Result} {xs : List Result},
    openSpreadItems n r = .ok xs → RV h r → RLV h xs
  | n, .argView _, _, e, _ => by cases n <;> simp [openSpreadItems] at e
  | 0, .atom _, _, e, v => by simp [openSpreadItems] at e; subst e; exact RV.spreadItems v
  | 0, .str _, _, e, v => by simp [openSpreadItems] at e; subst e; exact RV.spreadItems v
  | 0, .bool _, _, e, v => by simp [openSpreadItems] at e; subst e; exact RV.spreadItems v
  | 0, .sequenceValue _, _, e, v => by simp [openSpreadItems] at e; subst e; exact RV.spreadItems v
  | 0, .listValue _, _, e, v => by simp [openSpreadItems] at e; subst e; exact RV.spreadItems v
  | 0, .callRef _, _, e, v => by simp [openSpreadItems] at e; subst e; exact RV.spreadItems v
  | Nat.succ n, .atom a, xs, e, v => by
    simp only [openSpreadItems] at e
    exact openSpreadItems_valid e (RV.normalize (RV.seq (RV.spreadItems v)))
  | Nat.succ n, .str a, xs, e, v => by
    simp only [openSpreadItems] at e
    exact openSpreadItems_valid e (RV.normalize (RV.seq (RV.spreadItems v)))
  | Nat.succ n, .bool a, xs, e, v => by
    simp only [openSpreadItems] at e
    exact openSpreadItems_valid e (RV.normalize (RV.seq (RV.spreadItems v)))
  | Nat.succ n, .sequenceValue a, xs, e, v => by
    simp only [openSpreadItems] at e
    exact openSpreadItems_valid e (RV.normalize (RV.seq (RV.spreadItems v)))
  | Nat.succ n, .listValue a, xs, e, v => by
    simp only [openSpreadItems] at e
    exact openSpreadItems_valid e (RV.normalize (RV.seq (RV.spreadItems v)))
  | Nat.succ n, .callRef a, xs, e, v => by
    simp only [openSpreadItems] at e
    exact openSpreadItems_valid e (RV.normalize (RV.seq (RV.spreadItems v)))

theorem openSupplySpread_items : ∀ {n : Nat} {r : Result} {xs : List Result},
    openSupplySpread n r = .ok (.items xs) → RV h r → RLV h xs
  | 0, .argView _, _, e, _ => by simp [openSupplySpread] at e
  | Nat.succ n, .argView _, _, e, _ => by simp [openSupplySpread] at e
  | 0, .atom a, xs, e, v | 0, .str a, xs, e, v | 0, .bool a, xs, e, v
  | 0, .sequenceValue a, xs, e, v | 0, .listValue a, xs, e, v | 0, .callRef a, xs, e, v => by
    simp only [openSupplySpread] at e
    cases ho : openSpreadItems 0 _ with
    | error _ => rw [ho] at e; cases e
    | ok ys => rw [ho] at e; cases e; exact openSpreadItems_valid ho v
  | Nat.succ n, .atom a, xs, e, v | Nat.succ n, .str a, xs, e, v | Nat.succ n, .bool a, xs, e, v
  | Nat.succ n, .sequenceValue a, xs, e, v | Nat.succ n, .listValue a, xs, e, v | Nat.succ n, .callRef a, xs, e, v => by
    simp only [openSupplySpread] at e
    exact openSupplySpread_items e (RV.normalize (RV.seq (RV.spreadItems v)))

theorem openSupplySpread_view : ∀ {n : Nat} {r : Result} {a : Nat},
    openSupplySpread n r = .ok (.view a) → RV h r → a < h.size
  | 0, .argView b, _, e, v => by simp [openSupplySpread] at e; subst e; exact RV.argView_lt v
  | Nat.succ n, .argView _, _, e, _ => by simp [openSupplySpread] at e
  | 0, .atom a, _, e, _ | 0, .str a, _, e, _ | 0, .bool a, _, e, _
  | 0, .sequenceValue a, _, e, _ | 0, .listValue a, _, e, _ | 0, .callRef a, _, e, _ => by
    simp only [openSupplySpread] at e
    cases ho : openSpreadItems 0 _ with
    | error _ => rw [ho] at e; cases e
    | ok ys => rw [ho] at e; cases e
  | Nat.succ n, .atom a, _, e, v | Nat.succ n, .str a, _, e, v | Nat.succ n, .bool a, _, e, v
  | Nat.succ n, .sequenceValue a, _, e, v | Nat.succ n, .listValue a, _, e, v | Nat.succ n, .callRef a, _, e, v => by
    simp only [openSupplySpread] at e
    exact openSupplySpread_view e (RV.normalize (RV.seq (RV.spreadItems v)))

theorem selectionResult_valid {xs : List Result} (v : RLV h xs) : CRV h (selectionResult xs) :=
  combineOutputSlots_valid v

theorem makeCollectionListResult_valid {xs : List Result} (v : RLV h xs) :
    CRV h (makeCollectionListResult xs) := RV.list v

theorem reCountValueBoundary_valid {p : CountedResult} (v : CRV h p) : CRV h (reCountValueBoundary p) := v

theorem loopResultCounted_valid {xs : List Result} (v : RLV h xs) : CRV h (loopResultCounted xs) :=
  RV.normalize (RV.seq v)

theorem loopStepBuiltinRows_valid {p : CountedResult} (v : CRV h p) : RLV h (loopStepBuiltinRows p) :=
  RLV.singleton v

theorem outputRowsItems_valid {e : Expr} {out : CountedResult} (v : CRV h out) :
    RLV h (OutputRows.items e out) := by
  unfold OutputRows.items
  split
  · exact countedTopLevelValues_valid v
  · split
    · exact RLV.singleton v
    · exact countedTopLevelValues_valid v

theorem countedSequenceCallbackItem_valid {p : CountedResult} (v : CRV h p) :
    CRV h (countedSequenceCallbackItem p) := v

theorem buildEmptySequenceValue_valid {d : Nat} : RV h (buildEmptySequenceValue d) := RV.seq RLV.nil

theorem builtinCollectionItems_valid {r : Result} (v : RV h r) : RLV h (builtinCollectionItems r) := by
  unfold builtinCollectionItems
  split
  · exact RV.seq_iff.1 v
  · exact RV.list_iff.1 v
  · exact RLV.singleton v

theorem RLV.dropLast {xs : List Result} (v : RLV h xs) : RLV h xs.dropLast :=
  v.sub (fun _ m => List.dropLast_subset _ m)

theorem nextSlots_valid {xs : List Result} (v : RLV h xs) : RLV h (WhileRound.nextSlots xs) := by
  unfold WhileRound.nextSlots
  split
  · exact v
  · exact RLV.dropLast v

theorem RLV.map_fst_ones {xs : List Result} (v : RLV h xs) : CRLV h (xs.map (fun value => (value, 1))) :=
  CRLV.ones v

theorem RV.str_of {r : Result} {s : String} (e : r = .str s) : RV h r := by subst e; exact RV.str s

end Pure

attribute [ht_lemmas] RV.normalize countedTopLevelValues_valid combineOutputSlots_valid
  spreadSupplyResult_valid openSpreadItems_valid openSupplySpread_items openSupplySpread_view
  selectionResult_valid makeCollectionListResult_valid reCountValueBoundary_valid
  loopResultCounted_valid loopStepBuiltinRows_valid outputRowsItems_valid
  countedSequenceCallbackItem_valid buildEmptySequenceValue_valid builtinCollectionItems_valid
  RLV.dropLast nextSlots_valid RLV.map_fst_ones
attribute [ht_fwd] openSpreadItems_valid openSupplySpread_items openSupplySpread_view

/-! ## Generic loops with address-free results -/

theorem SoundI.forIn_true {α β : Type} {P : Array NeedCell → Prop} (xs : List α) (init : β)
    {f : α → β → EvalM (ForInStep β)} (hf : ∀ a b, SoundI P (f a b) (fun _ _ => True)) :
    SoundI P (forIn xs init f) (fun _ _ => True) := by
  intro hp
  suffices ∀ (as' : List α) (b : β) (hh : ∃ bs, bs ++ as' = xs),
      SoundOver Inv P (List.forIn'.loop xs (fun a _ b => f a b) as' b hh) (fun _ _ => True) from
    this xs init ⟨[], rfl⟩
  intro as'
  induction as' with
  | nil => intro b hh; unfold List.forIn'.loop; exact SoundI.pure _ (fun _ _ => trivial) hp
  | cons a rest ih =>
    intro b hh
    unfold List.forIn'.loop
    refine SoundI.bind (hf a b) PMono.true (fun r => ?_) hp
    intro hp'
    cases r with
    | done b' => exact SoundI.pure _ (fun _ _ => trivial) hp'
    | yield b' =>
      intro s vs ps
      exact ih b' _ s vs ps.1

theorem SoundI.forM_true {α : Type} {P : Array NeedCell → Prop} (xs : List α) {f : α → EvalM PUnit}
    (hf : ∀ a, SoundI P (f a) (fun _ _ => True)) : SoundI P (xs.forM f) (fun _ _ => True) := by
  induction xs with
  | nil => unfold List.forM; exact SoundI.pure _ (fun _ _ => trivial)
  | cons x rest ih =>
    unfold List.forM
    intro hp
    refine SoundI.bind (hf x) PMono.true (fun _ => ?_) hp
    intro hp' s vs ps
    exact ih hp s vs ps.1

theorem SoundI.foldlM_true {α β : Type} {P : Array NeedCell → Prop} {f : β → α → EvalM β}
    (hf : ∀ b a, SoundI P (f b a) (fun _ _ => True)) (xs : List α) (init : β) :
    SoundI P (xs.foldlM f init) (fun _ _ => True) := by
  induction xs generalizing init with
  | nil => unfold List.foldlM; exact SoundI.pure _ (fun _ _ => trivial)
  | cons x rest ih =>
    unfold List.foldlM
    intro hp
    refine SoundI.bind (hf init x) PMono.true (fun b => ?_) hp
    intro hp' s vs ps
    exact ih b hp s vs ps.1

theorem SoundI.mapM_true {α β : Type} {P : Array NeedCell → Prop} {f : α → EvalM β} {xs : List α}
    (hf : ∀ x ∈ xs, SoundI P (f x) (fun _ _ => True)) : SoundI P (xs.mapM f) (fun _ _ => True) :=
  SoundI.true_post (SoundI.mapM PMono.true xs hf)

attribute [ht_spec] SoundI.forIn_true SoundI.forM_true SoundI.foldlM_true SoundI.mapM_true

/-! ## Recursive helpers with address-free results -/

theorem resolveAlgForOpen_aux {P : Array NeedCell → Prop} (hP : HMono P) (e : Expr) (ctx : EvalCtx) :
    SoundI P (resolveAlgForOpen e ctx) (fun _ _ => True) := by
  induction e using resolveAlgForOpen.induct ctx with
  | case7 o n a ih => unfold resolveAlgForOpen; ht_tac
  | _ => unfold resolveAlgForOpen; ht_tac

theorem resolveAlgForOpen_spec {P : Array NeedCell → Prop} {e : Expr} {ctx : EvalCtx} :
    SoundI P (resolveAlgForOpen e ctx) (fun _ _ => True) := fun hP => resolveAlgForOpen_aux hP e ctx hP

attribute [ht_spec] resolveAlgForOpen_spec

theorem lookupOpenProperties_spec {P : Array NeedCell → Prop} {a : Algorithm} {name : Ident} {ctx : EvalCtx} :
    SoundI P (lookupOpenProperties a name ctx) (fun _ _ => True) := by
  unfold lookupOpenProperties resolveAllOpens resolveOpen; ht_tac

attribute [ht_spec] lookupOpenProperties_spec

theorem lookupOpenPropertiesInParentChain_aux {P : Array NeedCell → Prop} (hP : HMono P) (sc : ScopeCtx)
    (name : Ident) (ctx : EvalCtx) : SoundI P (lookupOpenPropertiesInParentChain sc name ctx) (fun _ _ => True) := by
  induction sc using lookupOpenPropertiesInParentChain.induct with
  | _ t ih =>
    unfold lookupOpenPropertiesInParentChain
    cases t with
    | mk parent _ _ _ _ _ _ _ => cases parent <;> ht_tac

theorem lookupOpenPropertiesInParentChain_spec {P : Array NeedCell → Prop} {sc : ScopeCtx} {name : Ident}
    {ctx : EvalCtx} : SoundI P (lookupOpenPropertiesInParentChain sc name ctx) (fun _ _ => True) :=
  fun hP => lookupOpenPropertiesInParentChain_aux hP sc name ctx hP

attribute [ht_spec] lookupOpenPropertiesInParentChain_spec

theorem lookupLexicalPropertyRaw_spec {P : Array NeedCell → Prop} {a : Algorithm} {name : Ident} {ctx : EvalCtx} :
    SoundI P (lookupLexicalPropertyRaw a name ctx) (fun _ _ => True) := by
  unfold lookupLexicalPropertyRaw lookupOpenPropertiesInChain; ht_tac

theorem resolveAliasStep_spec {P : Array NeedCell → Prop} {step : Algorithm} {target : Expr} {ctx : EvalCtx} :
    SoundI P (resolveAliasStep step target ctx) (fun _ _ => True) := by
  unfold resolveAliasStep; ht_tac

attribute [ht_spec] lookupLexicalPropertyRaw_spec resolveAliasStep_spec

theorem collectSingleAtomicNumbers_aux {P : Array NeedCell → Prop} (hP : HMono P) (b : Builtin) (index : Nat)
    (items : List Result) : SoundI P (collectSingleAtomicNumbers b index items) (fun _ _ => True) := by
  induction items generalizing index with
  | nil => unfold collectSingleAtomicNumbers; ht_tac
  | cons i rest ih => unfold collectSingleAtomicNumbers; ht_tac

theorem collectSingleAtomicNumbers_spec {P : Array NeedCell → Prop} {b : Builtin} {index : Nat}
    {items : List Result} : SoundI P (collectSingleAtomicNumbers b index items) (fun _ _ => True) :=
  fun hP => collectSingleAtomicNumbers_aux hP b index items hP

theorem minLoop_aux {P : Array NeedCell → Prop} (hP : HMono P) (numbers : List Int) (current : Int) :
    SoundI P (evalMinCounted.minLoop numbers current) (fun _ _ => True) := by
  induction numbers generalizing current with
  | nil => unfold evalMinCounted.minLoop; ht_tac
  | cons n rest ih => unfold evalMinCounted.minLoop; ht_tac

theorem maxLoop_aux {P : Array NeedCell → Prop} (hP : HMono P) (numbers : List Int) (current : Int) :
    SoundI P (evalMaxCounted.maxLoop numbers current) (fun _ _ => True) := by
  induction numbers generalizing current with
  | nil => unfold evalMaxCounted.maxLoop; ht_tac
  | cons n rest ih => unfold evalMaxCounted.maxLoop; ht_tac

theorem minLoop_spec {P : Array NeedCell → Prop} {numbers : List Int} {current : Int} :
    SoundI P (evalMinCounted.minLoop numbers current) (fun _ _ => True) := fun hP => minLoop_aux hP numbers current hP
theorem maxLoop_spec {P : Array NeedCell → Prop} {numbers : List Int} {current : Int} :
    SoundI P (evalMaxCounted.maxLoop numbers current) (fun _ _ => True) := fun hP => maxLoop_aux hP numbers current hP

attribute [ht_spec] collectSingleAtomicNumbers_spec minLoop_spec maxLoop_spec

theorem dedupList_go_sub {α : Type} [BEq α] : ∀ (seen xs : List α) (x : α),
    x ∈ dedupList.go seen xs → x ∈ xs
  | _, [], _, m => by simp [dedupList.go] at m
  | seen, y :: rest, x, m => by
    unfold dedupList.go at m
    split at m
    · exact List.mem_cons_of_mem _ (dedupList_go_sub seen rest x m)
    · rcases List.mem_cons.mp m with rfl | m
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (dedupList_go_sub _ rest x m)

theorem RLV.dedup {h : Array NeedCell} {xs : List Result} (v : RLV h xs) : RLV h (dedupList xs) :=
  v.sub (fun x m => dedupList_go_sub [] xs x m)

attribute [ht_lemmas] RLV.dedup

/-! ## Recursive helpers with callbacks (contracts relative to the caller's precondition) -/

theorem selectWith_aux {P : Array NeedCell → Prop} (hP : HMono P) {demand : Nat → EvalM Result}
    {receiver : Result} (hd : ∀ a, SoundI (fun h => P h ∧ a < h.size) (demand a) (fun r h => RV h r))
    {cells : List Nat} (hreq : ∀ h, P h → RV h receiver ∧ ValidAddresses h cells) :
    SoundI P (selectWith demand receiver cells) (fun xs h => RLV h xs) := by
  induction cells with
  | nil => unfold selectWith; ht_tac
  | cons c rest ih =>
    have ih' := ih (fun h ph => ⟨(hreq h ph).1, fun b m => (hreq h ph).2 b (List.mem_cons_of_mem _ m)⟩)
    clear ih
    unfold selectWith selectPosition; ht_tac

theorem selectWith_spec {P : Array NeedCell → Prop} {demand : Nat → EvalM Result} {receiver : Result}
    {cells : List Nat} (hd : ∀ a, SoundI (fun h => P h ∧ a < h.size) (demand a) (fun r h => RV h r))
    (hreq : ∀ h, P h → RV h receiver ∧ ValidAddresses h cells) :
    SoundI P (selectWith demand receiver cells) (fun xs h => RLV h xs) :=
  fun hP => selectWith_aux hP hd hreq hP

theorem selectViewWith_aux {P : Array NeedCell → Prop} (hP : HMono P) {demand : Nat → EvalM Result}
    {cellsOf : EvalM (List NeedSupply.Sourced)} {demandCell : Nat → EvalM Result}
    (hd : ∀ a, SoundI (fun h => P h ∧ a < h.size) (demand a) (fun r h => RV h r))
    (hc : SoundI P cellsOf (fun xs h => ValidSourced h xs))
    (hdc : ∀ a, SoundI (fun h => P h ∧ a < h.size) (demandCell a) (fun r h => RV h r))
    {selectors : List Nat} (hreq : ∀ h, P h → ValidAddresses h selectors) :
    SoundI P (selectViewWith demand cellsOf demandCell selectors) (fun xs h => RLV h xs) := by
  induction selectors with
  | nil => unfold selectViewWith; ht_tac
  | cons c rest ih =>
    have ih' := ih (fun h ph b m => hreq h ph b (List.mem_cons_of_mem _ m))
    clear ih
    unfold selectViewWith selectorIndex; ht_tac

theorem selectViewWith_spec {P : Array NeedCell → Prop} {demand : Nat → EvalM Result}
    {cellsOf : EvalM (List NeedSupply.Sourced)} {demandCell : Nat → EvalM Result} {selectors : List Nat}
    (hd : ∀ a, SoundI (fun h => P h ∧ a < h.size) (demand a) (fun r h => RV h r))
    (hc : SoundI P cellsOf (fun xs h => ValidSourced h xs))
    (hdc : ∀ a, SoundI (fun h => P h ∧ a < h.size) (demandCell a) (fun r h => RV h r))
    (hreq : ∀ h, P h → ValidAddresses h selectors) :
    SoundI P (selectViewWith demand cellsOf demandCell selectors) (fun xs h => RLV h xs) :=
  fun hP => selectViewWith_aux hP hd hc hdc hreq hP

theorem interpolateWith_aux {P : Array NeedCell → Prop} (hP : HMono P) {value : Expr → EvalM Result}
    (hv : ∀ e, SoundI P (value e) (fun _ _ => True)) (acc : String) (links : List InterpolationLink) :
    SoundI P (interpolateWith value acc links) (fun _ _ => True) := by
  induction links generalizing acc with
  | nil => unfold interpolateWith; ht_tac
  | cons l rest ih => unfold interpolateWith; ht_tac

theorem interpolateWith_spec {P : Array NeedCell → Prop} {value : Expr → EvalM Result} {acc : String}
    {links : List InterpolationLink} (hv : ∀ e, SoundI P (value e) (fun _ _ => True)) :
    SoundI P (interpolateWith value acc links) (fun _ _ => True) :=
  fun hP => interpolateWith_aux hP hv acc links hP

theorem formLeftToRight_aux {P : Array NeedCell → Prop} (hP : HMono P) {form : Expr → EvalM (List Result)}
    (hf : ∀ e, SoundI P (form e) (fun xs h => RLV h xs)) (rows : List Expr) :
    SoundI P (OutputRows.formLeftToRight form rows) (fun xs h => RLV h xs) := by
  induction rows with
  | nil => unfold OutputRows.formLeftToRight; ht_tac
  | cons e rest ih => unfold OutputRows.formLeftToRight; ht_tac

theorem formLeftToRight_spec {P : Array NeedCell → Prop} {form : Expr → EvalM (List Result)}
    {rows : List Expr} (hf : ∀ e, SoundI P (form e) (fun xs h => RLV h xs)) :
    SoundI P (OutputRows.formLeftToRight form rows) (fun xs h => RLV h xs) :=
  fun hP => formLeftToRight_aux hP hf rows hP

/-- A discovered flag row's supply. -/
def OptRowsV (h : Array NeedCell) (r : Option (List Expr × List Result)) : Prop :=
  ∀ p, r = some p → RLV h p.2

theorem OptRowsV.mono {h h' : Array NeedCell} (g : h.size ≤ h'.size) {r : Option (List Expr × List Result)}
    (v : OptRowsV h r) : OptRowsV h' r := fun p e => RLV.mono g (v p e)
theorem OptRowsV.some {h : Array NeedCell} {p : List Expr × List Result} (v : OptRowsV h (Option.some p)) :
    RLV h p.2 := v p rfl
theorem OptRowsV.nothing {h : Array NeedCell} : OptRowsV h Option.none := fun _ e => by cases e
theorem OptRowsV.of_rows {h : Array NeedCell} {p : List Expr × List Result} (v : RLV h p.2) :
    OptRowsV h (Option.some p) := fun _ e => by cases e; exact v
attribute [ht_fwd] OptRowsV.some
attribute [ht_lemmas] OptRowsV.some OptRowsV.nothing OptRowsV.of_rows

set_option hygiene false in
macro_rules | `(tactic| mono_atom $g) => `(tactic| exact OptRowsV.mono $g ‹_›)

theorem discover_aux {P : Array NeedCell → Prop} (hP : HMono P) {form : Expr → EvalM (List Result)}
    (hf : ∀ e, SoundI P (form e) (fun xs h => RLV h xs)) (rows : List Expr) :
    SoundI P (WhileRound.discover form rows) (fun r h => OptRowsV h r) := by
  induction rows with
  | nil => unfold WhileRound.discover; ht_tac
  | cons e rest ih => unfold WhileRound.discover; ht_tac

theorem discover_spec {P : Array NeedCell → Prop} {form : Expr → EvalM (List Result)}
    {rows : List Expr} (hf : ∀ e, SoundI P (form e) (fun xs h => RLV h xs)) :
    SoundI P (WhileRound.discover form rows) (fun r h => OptRowsV h r) :=
  fun hP => discover_aux hP hf rows hP

attribute [ht_spec] selectWith_spec selectViewWith_spec interpolateWith_spec formLeftToRight_spec discover_spec

/-! ## The alias write points -/

theorem GotV.aliasCell {st : EvalState} {h : Array NeedCell} (v : GotV st h) {k : String} {a : Nat}
    (e : lookupAssoc k st.aliasCells = some a) : a < h.size := by
  obtain ⟨k', m⟩ := lookup_mem k st.aliasCells a e
  exact Nat.lt_of_lt_of_le (v.1.aliasCells _ m) v.2

attribute [ht_lemmas] GotV.aliasCell
attribute [ht_fwd] GotV.aliasCell

theorem SoundI.modify_aliasCells {P : Array NeedCell → Prop} {key : String} {a : Nat}
    (hreq : ∀ h, P h → a < h.size) :
    SoundI P (modify fun s => { s with aliasCells := (key, a) :: s.aliasCells } : EvalM Unit)
      (fun _ _ => True) := by
  intro _ s vs ps
  rw [modify_run]
  exact ⟨inv_aliasCell vs key a (hreq _ ps), Nat.le_refl _, fun _ _ => trivial⟩

attribute [ht_spec] SoundI.modify_aliasCells

/-- **The `aliasCells` write point.** -/
theorem aliasBindingCellRecorded_spec {P : Array NeedCell → Prop} {wired : Algorithm} {target : Expr}
    {ctx : EvalCtx} (hreq : ∀ h, P h → ValidCtx h ctx) :
    SoundI P (aliasBindingCellRecorded wired target ctx) (fun a h => a < h.size) := by
  unfold aliasBindingCellRecorded; ht_tac

theorem aliasBindingCell_spec {P : Array NeedCell → Prop} {wired : Algorithm} {target : Expr}
    {ctx : EvalCtx} (hreq : ∀ h, P h → ValidCtx h ctx) :
    SoundI P (aliasBindingCell wired target ctx) (fun a h => a < h.size) := by
  unfold aliasBindingCell
  split
  · exact supply_spec (fun h ph => ⟨hreq h ph, VEV.nil⟩)
  · exact aliasBindingCellRecorded_spec hreq

attribute [ht_spec] aliasBindingCellRecorded_spec aliasBindingCell_spec

/-- The collector order a cell present in an `Inv` heap respects, for any later write of a cell
    with the same suspension at its address. -/
theorem Inv.collector_below {s : EvalState} (vs : Inv s) {a : Nat} {c : NeedCell}
    (hc : s.needs[a]? = some c) : ∀ slice, c.suspension = .collector slice → ∀ b ∈ slice, b < a :=
  fun slice hs b hb => vs.collectors a c hc slice hs b hb

/-- **The stale-snapshot write point** (`aliasBareCell`): the cell read before
    `bindParameters` / `enterAlgorithmBody` / `supplyNeed` is written back with its new
    `aliasBare`; the snapshot was valid in the earlier heap, hence in the current one. -/
theorem aliasBareCell_spec {P : Array NeedCell → Prop} {wired : Algorithm} {target : Expr}
    {ctx : EvalCtx} (hreq : ∀ h, P h → ValidCtx h ctx) :
    SoundI P (aliasBareCell wired target ctx) (fun a h => a < h.size) := by
  intro hp s vs ps
  unfold aliasBareCell
  rw [EvalM.bind_runState]
  obtain ⟨v1, g1, r1⟩ := aliasBindingCell_spec hreq hp s vs ps
  rcases h1 : (aliasBindingCell wired target ctx).runState s with ⟨o1, t⟩
  rw [h1] at v1 g1 r1
  cases o1 with
  | error e => exact ⟨v1, g1, fun _ hx => by cases hx⟩
  | ok address =>
    have ha : address < t.needs.size := r1 address rfl
    have pt : P t.needs := hp _ _ g1 ps
    dsimp only
    rw [EvalM.bind_runState, get_run]
    dsimp only
    cases hc : t.needs[address]? with
    | none =>
      simp only [hc]
      exact ⟨v1, g1, fun x hx => by cases hx; exact ha⟩
    | some cell =>
      simp only [hc]
      have vc : CellV t.needs cell := v1.cells address cell hc
      have hcol := Inv.collector_below v1 hc
      split
      · -- claim: `aliasUse := 1`
        rw [EvalM.bind_runState]
        simp only [set, StateT.set, ExceptT.lift]
        refine ⟨inv_set v1 address _ hcol (vc.with_aliasUse 1), ?_, ?_⟩
        · show s.needs.size ≤ (t.needs.set! address _).size
          simp [Array.set!]; exact g1
        · intro x hx; cases hx; show address < (t.needs.set! address _).size
          simp [Array.set!]; exact ha
      · split
        · rename_i bare hbare
          exact ⟨v1, g1, fun x hx => by cases hx; exact vc.aliasBare_lt hbare⟩
        · -- a fresh bare cell over the stale snapshot
          have hQ : HMono (fun h => P h ∧ t.needs.size ≤ h.size) :=
            fun _ _ g v => ⟨hp _ _ g v.1, Nat.le_trans v.2 g⟩
          have body : SoundI (fun h => P h ∧ t.needs.size ≤ h.size)
              (do
                let bindingCtx ← EvalCtx.bindParameters [] ctx
                let declaringCtx ← enterAlgorithmBody wired bindingCtx []
                let bare ← supplyNeed target declaringCtx []
                modify fun s => { s with needs := s.needs.set! address { cell with aliasBare := some bare } }
                pure bare : EvalM Nat) (fun a h => a < h.size) := by
            refine SoundI.bind (bindParameters_spec (fun h ph => hreq h ph.1))
              (fun _ _ _ g v => ValidCtx.mono g v) ?_
            intro bindingCtx
            refine SoundI.bind (enterAlgorithmBody_spec (fun h ph => ⟨ph.2, VEV.nil⟩))
              (fun _ _ _ g v => ValidCtx.mono g v) ?_
            intro declaringCtx
            refine SoundI.bind (supply_spec (fun h ph => ⟨ph.2, VEV.nil⟩))
              (fun _ _ _ g v => Nat.lt_of_lt_of_le v g) ?_
            intro bare
            intro _ u vu pu
            rw [EvalM.bind_runState, modify_run]
            have g0 : t.needs.size ≤ u.needs.size := pu.1.1.1.2
            refine ⟨inv_set vu address _ hcol ((CellV.mono g0 vc).with_aliasBare (OptAddr.mk pu.2)), ?_, ?_⟩
            · show u.needs.size ≤ (u.needs.set! address _).size
              simp [Array.set!]
            · intro x hx; cases hx; show bare < (u.needs.set! address _).size
              simp [Array.set!]; exact pu.2
          obtain ⟨v2, g2, r2⟩ := body hQ t v1 ⟨pt, Nat.le_refl _⟩
          exact ⟨v2, Nat.le_trans g1 g2, r2⟩

/-- **The terminal-claim write point** (`takeTerminalAliasInvocation`): `aliasUse` only, and the
    returned address is a recorded alias cell. -/
theorem takeTerminal_spec {P : Array NeedCell → Prop} {a : Algorithm} :
    SoundI P (takeTerminalAliasInvocation a) (fun o h => OptAddr h o) := by
  intro hp s vs ps
  unfold takeTerminalAliasInvocation
  split
  · rw [EvalM.bind_runState, get_run]
    dsimp only
    cases hl : lookupAssoc (aliasCellKey _) s.aliasCells with
    | none => simp only [hl]; exact ⟨vs, Nat.le_refl _, fun x hx => by cases hx; exact OptAddr.nil⟩
    | some address =>
      simp only [hl]
      have ha : address < s.needs.size := GotV.aliasCell ⟨vs, Nat.le_refl _⟩ hl
      cases hc : s.needs[address]? with
      | none => simp only [hc]; exact ⟨vs, Nat.le_refl _, fun x hx => by cases hx; exact OptAddr.nil⟩
      | some cell =>
        simp only [hc]
        have vc : CellV s.needs cell := vs.cells address cell hc
        cases hcl : claimTerminalAliasInitial cell with
        | none => simp only [hcl]; exact ⟨vs, Nat.le_refl _, fun x hx => by cases hx; exact OptAddr.nil⟩
        | some claimed =>
          simp only [hcl]
          have hcl' : claimed = { cell with aliasUse := 2 } := by
            unfold claimTerminalAliasInitial at hcl
            split at hcl
            · cases hcl; rfl
            · cases hcl
          subst hcl'
          rw [EvalM.bind_runState]
          refine ⟨inv_set vs address _ (fun sl hs => Inv.collector_below vs hc sl hs) (vc.with_aliasUse 2), ?_, ?_⟩
          · show s.needs.size ≤ (s.needs.set! address _).size
            simp [Array.set!]
          · intro x hx; cases hx
            exact OptAddr.mk (by show address < (s.needs.set! address _).size; simp [Array.set!]; exact ha)
  · exact ⟨vs, Nat.le_refl _, fun x hx => by cases hx; exact OptAddr.nil⟩

attribute [ht_spec] aliasBareCell_spec takeTerminal_spec

end KatLang.AddressInvariant
