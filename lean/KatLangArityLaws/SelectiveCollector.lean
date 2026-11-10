import KatLangArityLaws.ArgumentView

open KatLang KatLang.CallPlan

/-!
# Selective observation of a retained collector (NEED-07, November 2026)

A collecting parameter retains an exact slice of its original need cells. `count`, `first`, `last`,
`take` and postfix selection read that slice as positions instead of requesting the collector's whole
VALUE. Every statement is about the production definitions in `KatLang.lean`:

* **The retained-slice rule** (`EvalBody.retainedCellSlice?`, `EvalBody.writtenCollectorSlice?`). A
  collector cell retains its own slice, a Ready cell retains none, and a written expression that is
  neither a parameter nor a static reference retains none, for EVERY recursive answer `rec`
  (`collector_cell_retains_its_slice`, `ready_cell_retains_nothing`,
  `calculated_receiver_retains_nothing`). A classification reading a collector or Ready cell writes
  nothing.
* **The builtin demand sets** (`retainedCollectorBuiltin`). `count` is the slice's length and its run
  is independent of cell demand (`retained_count`, `retained_count_demands_nothing`); `first`/`last`
  depend on cell demand only at their one position (`retained_first_demands_only_first`,
  `retained_last_demands_only_last`) and report the ordinary `badIndex` on an empty slice
  (`retained_first_empty`); `take` is exactly the construction of its validated prefix
  (`retained_take_is_the_prefix`), a non-positive count demands nothing
  (`retained_take_nonpositive_demands_nothing`) and its run depends on cell demand only inside the
  prefix (`retained_take_demands_only_the_prefix`).
* **Selection** (`selectViewWith` over `retainedSourced`). An empty supply reads nothing
  (`retained_selection_empty`), an invalid selector fails before any element
  (`retained_invalid_selector_demands_nothing`) and one valid selector depends on cell demand only at
  its position (`retained_selection_demands_only_selected`).
* **The ONE take policy** (`takePrefix`). Cells and values share it: `takePrefix_map`, and the eager
  `evalTakeCounted` is that prefix's list (`eager_take_is_the_prefix`), so a retained `take` over
  demanded values has the eager result (`retained_take_values`).

DOMAIN. These laws start from a slice already identified as retained and state what the consumer does
with it. They claim nothing about C#: that an ordinary program reaches these definitions, and that the
C# twin agrees, are the finite evidence of `CoreTests/SelectiveCollectorReads.lean`,
`SelectiveCollectorReadTests` and the `selective-collector-*` executable specification cases. Eager
laws for ordinary values (`selectWith`, `evalCountCounted`) and for argument views are untouched.
-/

namespace KatLang.SelectiveCollector

/-! ## The retained-slice rule -/

theorem collector_cell_retains_its_slice (rec : EvalRec) (fuel address : Nat) (s : EvalState)
    (cell : NeedCell) (slice : List Nat)
    (hcell : s.needs[address]? = some cell) (hslice : cell.suspension = .collector slice) :
    (EvalBody.retainedCellSlice? rec (fuel + 1) address).runState s = (.ok (some slice), s) := by
  simp only [EvalBody.retainedCellSlice?, bind_run]
  rw [show (get : EvalM EvalState).runState s = (.ok s, s) from rfl]
  simp only [hcell, hslice]
  rfl

theorem ready_cell_retains_nothing (rec : EvalRec) (fuel address : Nat) (s : EvalState)
    (cell : NeedCell) (value : CountedResult)
    (hcell : s.needs[address]? = some cell) (hready : cell.suspension = .ready value) :
    (EvalBody.retainedCellSlice? rec (fuel + 1) address).runState s = (.ok none, s) := by
  simp only [EvalBody.retainedCellSlice?, bind_run]
  rw [show (get : EvalM EvalState).runState s = (.ok s, s) from rfl]
  simp only [hcell, hready]
  rfl

/-- **Only a reference can be retained.** A receiver that is no parameter and no static reference, a
    list, capture, call, selection or calculation among them, has no slice, for every recursive
    answer: the ordinary eager path decides it. -/
theorem calculated_receiver_retains_nothing (rec : EvalRec) (receiver : Expr) (ctx : EvalCtx)
    (hparam : ∀ name, receiver ≠ .param name) (hpath : Expr.staticAliasPath? receiver = none) :
    EvalBody.writtenCollectorSlice? rec receiver ctx = pure none := by
  unfold EvalBody.writtenCollectorSlice?
  have hcell : EvalBody.transparentRetainedCell? rec receiver ctx = pure none := by
    unfold EvalBody.transparentRetainedCell?
    simp only [hpath]
  cases receiver
  case param name => exact (hparam name rfl).elim
  all_goals (simp only [hcell]; rfl)

/-! ## The builtin demand sets -/

theorem mapM_agree {α β : Type} (f g : α → EvalM β) (items : List α) (hagree : ∀ a ∈ items, f a = g a) :
    items.mapM f = items.mapM g := by
  have key : ∀ (rest : List α) (acc : List β), (∀ a ∈ rest, f a = g a) →
      List.mapM.loop f rest acc = List.mapM.loop g rest acc := by
    intro rest
    induction rest with
    | nil => intro _ _; rfl
    | cons a rest ih =>
      intro acc h
      simp only [List.mapM.loop]
      rw [h a List.mem_cons_self]
      congr 1
      funext b
      exact ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))
  exact key items [] hagree

theorem retained_count (demand : Nat → EvalM CountedResult) (metadata : SequenceBuiltinMetadata)
    (suffixArgs : List PreparedSequenceBuiltinSuffixArg) (slice : List Nat) (s : EvalState) :
    (retainedCollectorBuiltin demand .countBuiltin metadata suffixArgs slice).runState s =
      (.ok (.atom (Int.ofNat slice.length), 1), s) := by
  simp only [retainedCollectorBuiltin]
  rw [KatLang.ArgumentViewLaws.count_run]
  simp [retainedSourced]

/-- **`count` demands no element**: two runs that differ only in cell demand agree. -/
theorem retained_count_demands_nothing (d₁ d₂ : Nat → EvalM CountedResult) (metadata : SequenceBuiltinMetadata)
    (suffixArgs : List PreparedSequenceBuiltinSuffixArg) (slice : List Nat) (s : EvalState) :
    (retainedCollectorBuiltin d₁ .countBuiltin metadata suffixArgs slice).runState s =
      (retainedCollectorBuiltin d₂ .countBuiltin metadata suffixArgs slice).runState s := by
  rw [retained_count, retained_count]

/-- `first` depends on cell demand only at the slice's first position. -/
theorem retained_first_demands_only_first (d₁ d₂ : Nat → EvalM CountedResult)
    (metadata : SequenceBuiltinMetadata) (suffixArgs : List PreparedSequenceBuiltinSuffixArg)
    (cell : Nat) (rest : List Nat) (s : EvalState) (hagree : d₁ cell = d₂ cell) :
    (retainedCollectorBuiltin d₁ .firstBuiltin metadata suffixArgs (cell :: rest)).runState s =
      (retainedCollectorBuiltin d₂ .firstBuiltin metadata suffixArgs (cell :: rest)).runState s := by
  simp only [retainedCollectorBuiltin]
  refine KatLang.ArgumentViewLaws.first_demands_only_first _ _ _ s s (retainedSourced (cell :: rest)) rfl ?_
  intro p hp
  simp only [retainedSourced, List.map_cons, List.head?_cons, Option.some.injEq] at hp
  subst hp
  simp only [hagree]

/-- `last` depends on cell demand only at the slice's last position. -/
theorem retained_last_demands_only_last (d₁ d₂ : Nat → EvalM CountedResult)
    (metadata : SequenceBuiltinMetadata) (suffixArgs : List PreparedSequenceBuiltinSuffixArg)
    (slice : List Nat) (s : EvalState) (hagree : ∀ cell, slice.getLast? = some cell → d₁ cell = d₂ cell) :
    (retainedCollectorBuiltin d₁ .lastBuiltin metadata suffixArgs slice).runState s =
      (retainedCollectorBuiltin d₂ .lastBuiltin metadata suffixArgs slice).runState s := by
  simp only [retainedCollectorBuiltin]
  refine KatLang.ArgumentViewLaws.last_demands_only_last _ _ _ s s (retainedSourced slice) rfl ?_
  intro p hp
  simp only [retainedSourced, List.getLast?_map, Option.map_eq_some_iff] at hp
  obtain ⟨cell, hcell, rfl⟩ := hp
  simp only [hagree cell hcell]

/-- An empty slice has no first position: the failure `first([])` reports. -/
theorem retained_first_empty (demand : Nat → EvalM CountedResult) (metadata : SequenceBuiltinMetadata)
    (suffixArgs : List PreparedSequenceBuiltinSuffixArg) (s : EvalState) :
    (retainedCollectorBuiltin demand .firstBuiltin metadata suffixArgs []).runState s =
      (.error (argumentViewEmptySelection .firstBuiltin), s) := by
  simp only [retainedCollectorBuiltin]
  exact KatLang.ArgumentViewLaws.first_empty _ _ s s rfl

/-- **`take` is the construction of its validated prefix**: after its count, it is the collector's own
    materialization over exactly `takePrefix`. -/
theorem retained_take_is_the_prefix (demand : Nat → EvalM CountedResult) (metadata : SequenceBuiltinMetadata)
    (suffixArgs : List PreparedSequenceBuiltinSuffixArg) (slice : List Nat) (s : EvalState) (count : Int)
    (hcount : (expectPreparedSequenceBuiltinWholeNumberSuffixArg .takeBuiltin metadata.suffixArgs suffixArgs 0).runState s =
      (.ok count, s)) :
    (retainedCollectorBuiltin demand .takeBuiltin metadata suffixArgs slice).runState s =
      (NeedDemand.materialize demand (takePrefix slice count)).runState s := by
  simp only [retainedCollectorBuiltin, bind_run, hcount]

/-- A non-positive count demands nothing and builds `[]`. -/
theorem retained_take_nonpositive_demands_nothing (demand : Nat → EvalM CountedResult)
    (slice : List Nat) (count : Int) (s : EvalState) (hcount : count ≤ 0) :
    (NeedDemand.materialize demand (takePrefix slice count)).runState s =
      (.ok (makeCollectionListResult []), s) := by
  simp only [takePrefix, ite_eq_left hcount]
  rfl

/-- `take` depends on cell demand only inside its prefix. -/
theorem retained_take_demands_only_the_prefix (d₁ d₂ : Nat → EvalM CountedResult) (slice : List Nat) (count : Int)
    (hagree : ∀ cell ∈ takePrefix slice count, d₁ cell = d₂ cell) :
    NeedDemand.materialize d₁ (takePrefix slice count) = NeedDemand.materialize d₂ (takePrefix slice count) := by
  unfold NeedDemand.materialize
  rw [mapM_agree (fun a => Prod.fst <$> d₁ a) (fun a => Prod.fst <$> d₂ a) (takePrefix slice count)
    (fun cell hmem => by simp only [hagree cell hmem])]

/-! ## Selection -/

/-- An empty selector supply reads no position and demands no element. -/
theorem retained_selection_empty {α : Type} (demand : α → EvalM Result) (demandCell : Nat → EvalM Result)
    (slice : List Nat) (s : EvalState) :
    (selectViewWith demand (pure (retainedSourced slice)) demandCell []).runState s = (.ok [], s) := rfl

/-- An invalid selector fails before any element is demanded. -/
theorem retained_invalid_selector_demands_nothing {α : Type} (demand : α → EvalM Result)
    (demandCell : Nat → EvalM Result) (slice : List Nat) (selector : α) (rest : List α) (s t : EvalState)
    (v : Result) (e : Error) (hd : (demand selector).runState s = (.ok v, t))
    (hi : ((selectorIndex v).runState t).1 = .error e) :
    (selectViewWith demand (pure (retainedSourced slice)) demandCell (selector :: rest)).runState s = (.error e, t) :=
  KatLang.ArgumentViewLaws.select_invalid_before_supply demand _ demandCell selector rest s t v e hd hi

/-- One valid selector depends on cell demand only at its own position. A position past the slice
    demands nothing: it has no cell. -/
theorem retained_selection_demands_only_selected {α : Type} (demand : α → EvalM Result)
    (d₁ d₂ : Nat → EvalM Result) (slice : List Nat) (selector : α) (s t : EvalState) (v : Result) (n : Nat)
    (hd : (demand selector).runState s = (.ok v, t)) (hi : (selectorIndex v).runState t = (.ok n, t))
    (hagree : ∀ cell, slice[n]? = some cell → d₁ cell = d₂ cell) :
    (selectViewWith demand (pure (retainedSourced slice)) d₁ [selector]).runState s =
      (selectViewWith demand (pure (retainedSourced slice)) d₂ [selector]).runState s := by
  refine KatLang.ArgumentViewLaws.select_demands_only_selected demand _ d₁ d₂ selector s t t v n
    (retainedSourced slice) hd hi rfl ?_
  intro p hp
  simp only [retainedSourced, List.getElem?_map, Option.map_eq_some_iff] at hp
  obtain ⟨cell, hcell, rfl⟩ := hp
  exact hagree cell hcell

/-! ## The ONE take policy -/

theorem takePrefix_map {α β : Type} (f : α → β) (items : List α) (count : Int) :
    (takePrefix items count).map f = takePrefix (items.map f) count := by
  unfold takePrefix
  split
  · rfl
  · exact List.map_take ..

theorem eager_take_is_the_prefix (items : List Result) (count : Int) (s : EvalState) :
    (evalTakeCounted items count).runState s = (.ok (makeCollectionListResult (takePrefix items count)), s) := rfl

/-- A retained `take` over cells whose VALUES are `values` keeps the same values as the eager `take`
    of the whole list. -/
theorem retained_take_values {α : Type} (value : α → Result) (cells : List α) (count : Int) :
    (takePrefix cells count).map value = takePrefix (cells.map value) count :=
  takePrefix_map value cells count

end KatLang.SelectiveCollector
