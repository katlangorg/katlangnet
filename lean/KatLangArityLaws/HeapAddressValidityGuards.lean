import KatLangArityLaws.HeapAddressValidity

open KatLang NeedSupply KatLang.HeapAddressValidity KatLang.NeedControl.Allocation

/-!
# FG-H1 guards: witnesses and counterexamples for heap-address validity

Positive witnesses run the ACTUAL production helpers on concrete states (kernel `rfl` where the
helper reduces, `#guard` where it passes through the opaque `requiredParameterOwner?`) and apply
the universal theorems of `HeapAddressValidity.lean` to them. Negative witnesses show each key
premise is necessary: dropping it makes the corresponding universal statement FALSE
(`¬ Sound …` theorems), and a reversed collector order is rejected although every member is
in bounds. These complement, never replace, the universal proofs.
-/

namespace KatLang.HeapAddressValidityGuards

def ctxWith (env : NeedEnv) : EvalCtx := { callStack := [], needEnv := env }
def refuse : SpreadEval := fun _ _ _ => throw Error.divByZero

/-! ## Fresh Ready and expression allocation -/

def readyCell : NeedCell := { suspension := .ready (.atom 7, 1) }
def oneReady : EvalState := { needs := #[readyCell] }

theorem ready_fresh : (readyNeed (.atom 7, 1)).runState EvalState.empty = (.ok 0, oneReady) := rfl

theorem oneReady_valid : StateValid oneReady := by
  have h := ready_sound (.atom 7, 1) EvalState.empty empty_valid trivial
  rw [ready_fresh] at h
  exact h.1

def exprCell : NeedCell := { suspension := .expression (.num 3) (ctxWith [("x", 0)]) [] }
def readyAndExpr : EvalState := { needs := #[readyCell, exprCell] }

/-- A literal allocates one expression cell storing the (valid) caller tier `[("x", 0)]`. -/
theorem expression_fresh :
    (supplyNeed (.num 3) (ctxWith [("x", 0)]) []).runState oneReady = (.ok 1, readyAndExpr) := rfl

theorem expression_fresh_valid : StateValid readyAndExpr := by
  have h := supply_sound (.num 3) (ctxWith [("x", 0)]) [] oneReady oneReady_valid
    (fun p m => by simp [ctxWith] at m; subst m; decide)
  rw [expression_fresh] at h
  exact h.1

/-! ## Parameter forwarding: direct and captured -/

/-- Direct forwarding transports cell 0: no allocation, the state is unchanged. -/
theorem direct_forwarding :
    (supplyNeed (.param "x") (ctxWith [("x", 0)]) []).runState oneReady = (.ok 0, oneReady) := rfl

/-- The owner scope binding `x` in activation 0, and a site nested in it. -/
def ownerScope : ScopeCtx := .mk none ["x"] [] [] [] [] (some 0) none
def siteCtx : EvalCtx :=
  { callStack := [Algorithm.mk none [] [] [] []],
    headScope := some (.mk (some ownerScope) [] [] [] [] [] none none) }

def capturedState (needs : NeedEnv) : EvalState :=
  { oneReady with lexicalActivations := #[{ values := [], needs := needs }] }

-- Captured forwarding: the site's own tier is EMPTY; activation 0 supplies cell 0, untouched.
#guard match (supplyNeed (.param "x") siteCtx []).runState (capturedState [("x", 0)]) with
  | (.ok 0, s) => s.needs.size == 1
  | _ => false

-- The parameter context of the captured read is the activation's tier.
#guard match (parameterContext "x" siteCtx []).runState (capturedState [("x", 0)]) with
  | (.ok (c, _), _) => c.needEnv == [("x", 0)]
  | _ => false

-- NEGATIVE: an activation saved with a dangling need address forwards it unchecked.
#guard match (supplyNeed (.param "x") siteCtx []).runState (capturedState [("x", 9)]) with
  | (.ok 9, s) => s.needs.size == 1
  | _ => false

theorem capturedState_valid : StateValid (capturedState [("x", 0)]) := by
  refine ⟨oneReady_valid.collectors, oneReady_valid.suspensionEnvs, ?_⟩
  intro i act h
  match i, h with
  | 0, h =>
    simp [capturedState] at h
    subst h
    intro p m
    simp at m
    subst m
    decide

/-- ... and that state is exactly what `StateValid.activations` rules out. -/
theorem dangling_activation_invalid : ¬ StateValid (capturedState [("x", 9)]) := by
  intro h
  have := h.activations 0 { values := [], needs := [("x", 9)] } (by simp [capturedState])
    ("x", 9) (by simp)
  simp [capturedState, oneReady] at this

/-- Recording an activation from a valid tier: the saved activation IS the valid one above. -/
theorem record_then_valid :
    (recordParameterActivation ["x"] (ctxWith [("x", 0), ("y", 0)]) []).runState oneReady =
      (.ok 0, { oneReady with lexicalActivations := #[savedActivation ["x"] (ctxWith [("x", 0), ("y", 0)]) []] }) ∧
    (savedActivation ["x"] (ctxWith [("x", 0), ("y", 0)]) []).needs = [("x", 0)] := ⟨rfl, rfl⟩

/-! ## Collector slices: empty, repeated, nested; known-slice reopening -/

def collectors : EvalState :=
  { needs := #[readyCell, { suspension := .collector [] }, { suspension := .collector [0, 0] },
      { suspension := .collector [2, 0] }] }

/-- Built by the production allocator from `oneReady`: empty, repeated and nested collectors. -/
theorem collectors_built :
    (do
      let _ ← allocateNeed (.collector [])
      let _ ← allocateNeed (.collector [0, 0])
      allocateNeed (.collector [2, 0]) : EvalM Nat).runState oneReady = (.ok 3, collectors) := rfl

theorem collectors_valid : StateValid collectors := by
  have step := fun (sl : List Nat) (s : EvalState) (vs : StateValid s) (hs : ValidAddresses s.needs sl) =>
    (allocate_sound (.collector sl) s vs hs).1
  have h1 := step [] oneReady oneReady_valid (fun _ m => by cases m)
  have h2 := step [0, 0] _ h1 (fun a m => by simp at m; subst m; decide)
  have h3 := step [2, 0] _ h2 (fun a m => by simp at m; rcases m with rfl | rfl <;> decide)
  exact h3

/-- Reopening the nested collector (address 3) transports `[2, 0]`, both below 3. -/
theorem nested_reopen :
    (spreadCollectorSlice? (.param "xs") (ctxWith [("xs", 3)])).runState collectors =
      (.ok (some [2, 0]), collectors) := rfl

/-- Known-slice formation: original addresses in order, repeated ones kept, no cell allocated
    and nothing demanded (the state is returned unchanged, the callback never runs). -/
theorem known_slice_no_allocation :
    (form refuse (ctxWith [("xs", 2)]) [] [.sequenceSpread (.param "xs")]).runState collectors =
      (.ok [(0, none), (0, none)], collectors) := rfl

theorem empty_slice_no_allocation :
    (form refuse (ctxWith [("xs", 1)]) [] [.sequenceSpread (.param "xs")]).runState collectors =
      (.ok [], collectors) := rfl

/-! ## Mixed supply, a heap-growing callback, failure after a valid prefix -/

/-- A computed spread that allocates a fresh Ready cell and transports it. -/
def growSpread : SpreadEval := fun _ _ _ => do
  let a ← readyNeed (.atom 5, 1)
  pure (.cells [(a, none)])

theorem growSpread_sound (ctx : EvalCtx) (env : ValEnv) : SpreadSound growSpread ctx env := by
  intro operand
  refine Sound.bind (mid := fun a h => a < h.size) (fun _ _ _ g v => ValidCtx.mono g v)
    ((ready_sound _).weaken (fun _ _ => trivial) (fun _ _ h => h)) ?_
  intro a
  exact Sound.pure _ (fun _ h p m => by simp at m; subst m; exact h.2)

/-- Opens items `1, 2` (fresh Ready cells) for `(1)*`; any other spread allocates one Ready cell
    and then transports the (OLD) cell 0, valid in its post-state. -/
def mixedSpread : SpreadEval := fun e _ _ =>
  match e with
  | .sequenceSpread (.num 1) => pure (.items [.atom 1, .atom 2])
  | _ => do
    let _ ← readyNeed (.atom 0, 1)
    pure (.cells [(0, none)])

theorem mixedSpread_sound (ctx : EvalCtx) (env : ValEnv) : SpreadSound mixedSpread ctx env := by
  intro operand
  unfold mixedSpread
  split
  · exact Sound.pure _ (fun _ _ => trivial)
  · refine Sound.bind (mid := fun a h => a < h.size) (fun _ _ _ g v => ValidCtx.mono g v)
      ((ready_sound _).weaken (fun _ _ => trivial) (fun _ _ h => h)) ?_
    intro a
    exact Sound.pure _ (fun _ h p m => by
      simp at m; subst m; exact Nat.lt_of_le_of_lt (Nat.zero_le _) h.2)

def mixedArgs : OutputBundle :=
  [.num 9, .sequenceSpread (.num 1), .sequenceSpread (.num 2), .param "x"]

/-- Ordinary slot (fresh expression cell 1), Ready items (cells 2, 3), cell transport (cell 0,
    after the callback allocated cell 4), bound parameter (cell 0): all below the final size 5. -/
theorem mixed_supply :
    ((form mixedSpread (ctxWith [("x", 0)]) [] mixedArgs).runState oneReady).1 =
      .ok [(1, some (.num 9)), (2, none), (3, none), (0, none), (0, some (.param "x"))] ∧
    ((form mixedSpread (ctxWith [("x", 0)]) [] mixedArgs).runState oneReady).2.needs.size = 5 :=
  ⟨rfl, rfl⟩

theorem mixed_supply_valid :
    ValidSourced ((form mixedSpread (ctxWith [("x", 0)]) [] mixedArgs).runState oneReady).2.needs
      [(1, some (.num 9)), (2, none), (3, none), (0, none), (0, some (.param "x"))] :=
  (form_sound mixedSpread _ [] (mixedSpread_sound _ []) mixedArgs oneReady oneReady_valid
    (fun p m => by simp [ctxWith] at m; subst m; decide)).2.2 _ mixed_supply.1

/-- The heap-growing callback's NEW cell is valid in the callback's post-state. -/
theorem grow_supply :
    (form growSpread (ctxWith []) [] [.sequenceSpread (.num 0)]).runState EvalState.empty =
      (.ok [(0, none)], { needs := #[{ suspension := .ready (.atom 5, 1) }] }) := rfl

/-- A valid prefix (one ordinary cell) then a failing spread: the error is returned, the cell
    allocated by the prefix is RETAINED (no rollback) and still valid. -/
theorem failure_after_prefix :
    (form refuse (ctxWith []) [] [.num 1, .sequenceSpread (.num 0)]).runState EvalState.empty =
      (.error .divByZero,
        { needs := #[{ suspension := .expression (.num 1) (ctxWith []) [] }] }) := rfl

theorem failure_after_prefix_valid :
    StateValid { needs := #[{ suspension := .expression (.num 1) (ctxWith []) [] }] } ∧
    ValidSourced (#[{ suspension := .expression (.num 1) (ctxWith []) [] }] : Array NeedCell)
      [(0, some (.num 1))] := by
  have refuse_sound : SpreadSound refuse (ctxWith []) [] := fun _ => Sound.throw_ _
  have hl : (form refuse (ctxWith []) [] [.num 1]).runState EvalState.empty =
      (.ok [(0, some (.num 1))], { needs := #[{ suspension := .expression (.num 1) (ctxWith []) [] }] }) := rfl
  have ht : (form refuse (ctxWith []) [] [.sequenceSpread (.num 0)]).runState
      { needs := #[{ suspension := .expression (.num 1) (ctxWith []) [] }] } =
      (.error .divByZero, { needs := #[{ suspension := .expression (.num 1) (ctxWith []) [] }] }) := rfl
  have r := form_failure_retains_prefix refuse (ctxWith []) [] refuse_sound [.num 1]
    [.sequenceSpread (.num 0)] _ _ _ _ _ empty_valid (fun _ m => by cases m) hl ht
  exact ⟨r.2.1, r.2.2.2⟩

-- Production wrapper: ordinary slot, known repeated slice, then a bound parameter.
#guard match (formNeedSupplySourced [.num 4, .sequenceSpread (.param "xs"), .param "x"]
    (ctxWith [("xs", 2), ("x", 3)]) []).runState collectors with
  | (.ok [(4, some (.num 4)), (0, none), (0, none), (3, some (.param "x"))], s) => s.needs.size == 5
  | _ => false

/-! ## Negative witnesses: each premise matters -/

/-- Without a valid caller tier, ordinary transport returns a dangling address. -/
theorem supply_needs_valid_env :
    ¬ Sound (fun _ => True) (supplyNeed (.param "x") (ctxWith [("x", 9)]) []) (fun a h => a < h.size) := by
  intro h
  have r := (h EvalState.empty empty_valid trivial).2.2 9 rfl
  exact absurd r (by decide)

/-- Without a valid caller tier, a fresh expression cell stores a dangling environment. -/
theorem expression_needs_valid_env :
    ¬ Sound (fun _ => True) (supplyNeed (.num 1) (ctxWith [("x", 9)]) []) (fun a h => a < h.size) := by
  intro h
  have v := (h EvalState.empty empty_valid trivial).1
  have := v.suspensionEnvs 0 _ rfl _ _ _ rfl ("x", 9) (by simp [ctxWith])
  exact absurd this (by decide)

/-- Without a valid slice, a collector would reference a cell at/after itself. -/
theorem collector_needs_valid_slice :
    ¬ Sound (fun _ => True) (allocateNeed (.collector [0])) (fun a h => a < h.size) := by
  intro h
  have v := (h EvalState.empty empty_valid trivial).1
  have := v.collectors 0 _ rfl [0] rfl 0 (by simp)
  omega

/-- Self and forward collector edges violate the order although every member is in bounds:
    the order is strictly stronger than bounds (reversing it would admit the forward edge). -/
def selfEdge : Array NeedCell := #[{ suspension := .collector [0] }]
def forwardEdge : Array NeedCell := #[{ suspension := .collector [1] }, readyCell]

theorem selfEdge_in_bounds : ∀ b ∈ [0], b < selfEdge.size := by decide
theorem selfEdge_rejected : ¬ ValidCollectorHeap selfEdge := by
  intro h
  exact collector_no_self_edge h (a := 0) rfl rfl (by simp)
theorem forwardEdge_in_bounds : ∀ b ∈ [1], b < forwardEdge.size := by decide
theorem forwardEdge_rejected : ¬ ValidCollectorHeap forwardEdge := by
  intro h
  exact collector_no_forward_edge h (a := 0) (b := 1) rfl rfl (by simp) (by decide)

/-- A callback returning a dangling `.cells` address violates `SpreadSound`, and without that
    premise formation returns an invalid supply. -/
def danglingSpread : SpreadEval := fun _ _ _ => pure (.cells [(9, none)])

theorem dangling_not_sound : ¬ SpreadSound danglingSpread (ctxWith []) [] := by
  intro h
  have r := (h (.num 0) EvalState.empty empty_valid (fun _ m => by cases m)).2.2 _ rfl
  have := r (9, none) (by simp)
  exact absurd this (by decide)

theorem form_needs_spread_contract :
    ¬ Sound (fun h => ValidCtx h (ctxWith [])) (form danglingSpread (ctxWith []) [] [.sequenceSpread (.num 0)])
      (fun xs h => ValidSourced h xs) := by
  intro h
  have r := (h EvalState.empty empty_valid (fun _ m => by cases m)).2.2 [(9, none)] rfl
  have := r (9, none) (by simp)
  exact absurd this (by decide)

end KatLang.HeapAddressValidityGuards
