import KatLangArityLaws.NeedControl
import KatLangArityLaws.RecursiveMapWholeRead

open KatLang KatLang.NeedControl.Schedule

/-!
# The C#-only boundaries of lazy collections, on the Lean side (issue #204, November 2026)

`SEMANTIC-ALIGNMENT.md` records three C#-only behaviors of lazy collections that have no Lean
counterpart: the STAGE-SITE frame of a deferred step's failure, the RESERVATIONS of a list's
positions against the collection budgets, and the READ-GENERATION bound on a result that keeps
building lists while it is read whole. Each is a C# observation added to a Lean observation. This
module states the Lean observation each one is added to, as a kernel theorem about the production
definitions of `KatLang.lean`. `CoreTests/LazyCollections.lean` § "The C#-only boundaries" and
`LazyCollectionTests` run the paired programs.

* STAGE-SITE FRAMES. Discovery re-raises a candidate's failed verdict EXACTLY as the verdict cell's
  demand returns it (`discover_verdict_failure`): the model adds no frame for the written call that
  built the stage. In the paired `count(filter(...))` example C# adds the building call's frame
  (`while evaluating call to filter`) between the consumer and the same predicate failure.
* RESERVATIONS. A `map` stage over known positions has exactly its source's cardinality, every
  position a deferred item (`mapItems_positions`), and a `filter` stage one CANDIDATE per source
  position, its cardinality left to discovery (`filterItems_candidates`). C# reserves the known map
  length at construction, the accepted filter count on scan completion, and a discovered map's
  length on its first concrete read. The paired runs measure these reservations. Lean models the
  positions and their values.
* READ GENERATIONS. The path check in `materializePosition` rejects positions already on its path
  (`materializePosition_on_path`: a self-containing value is `demandCycle`, as in C#) and reads
  every other position, extending the path (`materializePosition_fresh`): it has no depth bound. The
  whole read of `F(1)` for `F(x) = [x].map(F)` is incomplete at EVERY fuel
  (`recursiveMap_wholeRead_incomplete`, proved in `RecursiveMapWholeRead.lean`), and its production
  run never completes (`recursiveMap_wholeRead_production`). C# ends that read with
  `EvaluationDepthExceeded` after `MaxDepth` read generations. It also refuses a finite structure
  built during the read deeper than that (`atoms(Nest(200))`), which Lean completes.

Not claimed: anything about C# (each pairing is finite evidence), any law of the C# policies
themselves, and the divergence of any program but the `F(1)` witness. For that witness the claim is
the incompleteness of the fuel approximation of the guards' core call (from `EvalState.empty`, under
the prelude call stack) and the non-completion of production at that call. The positive control
`F(1).count` stays a guard.
-/

namespace KatLang.LazyCollectionBoundaries

/-! ## Schedules: the shape of every completed element-wise step -/

/-- Every completed schedule of a callback whose completed outcomes satisfy `Q` returns one
    result per input, each satisfying `Q`. -/
theorem schedule_ok {α β : Type} {f : α → EvalM β} {Q : β → Prop}
    (hf : ∀ a s b t, (f a).runState s = (.ok b, t) → Q b) :
    ∀ (xs : List α) (s : EvalState) (bs : List β) (t : EvalState),
      schedule f xs s = (.ok bs, t) → bs.length = xs.length ∧ ∀ b ∈ bs, Q b := by
  intro xs
  induction xs with
  | nil => intro s bs t h; cases h; exact ⟨rfl, nofun⟩
  | cons a rest ih =>
    intro s bs t h
    simp only [schedule] at h
    rcases ha : (f a).runState s with ⟨_ | b, u⟩
    · rw [ha] at h; cases h
    · rw [ha] at h
      dsimp only at h
      rcases hr : schedule f rest u with ⟨_ | bs', v⟩
      · rw [hr] at h; cases h
      · rw [hr] at h
        cases h
        obtain ⟨hl, hq⟩ := ih u bs' _ hr
        refine ⟨by simp [hl], fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hf a s x u ha
        · exact hq x hx

/-! ## Reservations: the cardinality of a stage, fixed when it is built -/

/-- **A `map` stage over known positions has its source's cardinality**, every position a
    deferred item (the mapped application of that position), on every completed construction. C#
    reserves exactly this count when it builds the stage (`Evaluator.StageResult`). -/
theorem mapItems_positions (mapper : Nat × Option Expr) (caller : EvalCtx) (values : ValEnv)
    (items : List Result) (s : EvalState) (r : Result) (t : EvalState)
    (h : (LazyList.mapItems mapper caller values items).runState s = (.ok r, t)) :
    ∃ positions, r = .listValue positions ∧ positions.length = items.length ∧
      ∀ x ∈ positions, ∃ cell, x = .deferred cell := by
  unfold LazyList.mapItems at h
  rw [KatLang.NeedControl.Collector.bind_run, mapM_schedule] at h
  rcases hs : schedule (fun item => do
      pure (Result.deferred (← LazyList.mappedCell mapper caller values (← LazyList.itemCell item))))
      items s with ⟨_ | positions, u⟩
  · rw [hs] at h; cases h
  · rw [hs] at h
    cases h
    have hd : ∀ (item : Result) (s' : EvalState) (x : Result) (t' : EvalState),
        (do pure (Result.deferred (← LazyList.mappedCell mapper caller values (← LazyList.itemCell item))) :
          EvalM Result).runState s' = (.ok x, t') → ∃ cell, x = .deferred cell := by
      intro item s' x t' hx
      rw [KatLang.NeedControl.Collector.bind_run] at hx
      rcases hi : (LazyList.itemCell item).runState s' with ⟨_ | c, u'⟩
      · rw [hi] at hx; cases hx
      · rw [hi] at hx
        dsimp only at hx
        rw [KatLang.NeedControl.Collector.bind_run] at hx
        rcases hm : (LazyList.mappedCell mapper caller values c).runState u' with ⟨_ | m, w⟩
        · rw [hm] at hx; cases hx
        · rw [hm] at hx
          cases hx
          exact ⟨m, rfl⟩
    obtain ⟨hl, hq⟩ := schedule_ok hd items s positions _ hs
    exact ⟨positions, rfl, hl, hq⟩

/-- **A `filter` stage over known positions has one CANDIDATE per source position** and no known
    cardinality: it is a pending list, whose positions are the candidates its discovery accepts. C#
    reserves that accepted count when the scan completes (`FilteredList.Complete`). -/
theorem filterItems_candidates (predicate : Nat × Option Expr) (caller : EvalCtx) (values : ValEnv)
    (items : List Result) (s : EvalState) (r : Result) (t : EvalState)
    (h : (LazyList.filterItems predicate caller values items).runState s = (.ok r, t)) :
    ∃ candidates, r = .pendingList candidates ∧ candidates.length = items.length := by
  unfold LazyList.filterItems at h
  rw [KatLang.NeedControl.Collector.bind_run] at h
  rcases hsrc : (readyNeed (.pendingList [], 1)).runState s with ⟨_ | src, u⟩
  · rw [hsrc] at h; cases h
  · rw [hsrc] at h
    dsimp only at h
    rw [KatLang.NeedControl.Collector.bind_run, mapM_schedule] at h
    rcases hs : schedule _ items.zipIdx u with ⟨_ | candidates, v⟩
    · rw [hs] at h; cases h
    · rw [hs] at h
      cases h
      obtain ⟨hl, -⟩ := schedule_ok (Q := fun _ => True) (fun _ _ _ _ _ => trivial) _ u candidates _ hs
      exact ⟨candidates, rfl, by simp [hl]⟩

/-! ## Stage-site frames: discovery re-raises the step's own failure -/

/-- **THE MODEL ADDS NO STAGE FRAME.** When a candidate's verdict cell fails, discovery fails with
    THAT error, in that state — whatever the limit, the visit and the later candidates. A consumer
    then reports it under its own frames only; C# also frames it with the written call that built
    the stage (`LazyList.AtSite`). -/
theorem discover_verdict_failure (demand : Nat → EvalM CountedResult) (visit : Nat → EvalM Result)
    (limit : Option Nat) (cell verdictCell : Nat) (rest : List (Nat × Nat)) (s t : EvalState) (e : Error)
    (hl : limit ≠ some 0) (hd : (demand verdictCell).runState s = (.error e, t)) :
    (LazyList.discover demand visit limit ((cell, verdictCell) :: rest)).runState s = (.error e, t) := by
  have hb : (limit == some 0) = false := by
    cases limit with
    | none => rfl
    | some n => cases n with
      | zero => exact absurd rfl hl
      | succ n => rfl
  simp only [LazyList.discover, hb, Bool.false_eq_true, ↓reduceIte]
  rw [KatLang.NeedControl.Collector.bind_run, hd]

/-! ## Read generations: the whole-value read refuses only its own path -/

/-- **A position already on the read's path is the value's own cycle**: `demandCycle`, before any
    demand. A fresh position can still fail during its own demand. -/
theorem materializePosition_on_path (demand : Nat → EvalM CountedResult) (visiting : List Nat) (cell : Nat)
    (h : visiting.contains cell = true) :
    materializePosition demand visiting (.deferred cell) = .error Error.demandCycle := by
  have h' : cell ∈ visiting := by simpa using h
  simp [materializePosition, h']

/-- **Every other position is read and materialized, the path one longer**: no depth bound. -/
theorem materializePosition_fresh (demand : Nat → EvalM CountedResult) (visiting : List Nat) (cell : Nat)
    (h : visiting.contains cell = false) :
    materializePosition demand visiting (.deferred cell) =
      (do materializeVia demand (← forcePosition demand (.deferred cell)) (cell :: visiting)) := by
  have h' : cell ∉ visiting := by simpa using h
  simp [materializePosition, h']

/-- For `F(x) = [x].map(F)`, the whole read of `F(1)` in the READ GENERATIONS guard exhausts
    every fuel. Each generation demands a fresh position and materializes its value three
    evaluator calls deeper. Every address already on the path is older than that position. -/
theorem recursiveMap_wholeRead_incomplete (fuel : Nat) :
    KatLangTests.LazyCollections.recursiveMapWholeReadAt fuel = .error .fuelExhausted :=
  RecursiveMapWholeRead.fuelValue_F1_incomplete fuel

/-- The production evaluator at that call never completes. -/
theorem recursiveMap_wholeRead_production :
    ¬ EvaluatorCore.ProductionCompletes
      (evalUnbounded (.evalRunValue ((identifyPropertyExpr RecursiveMapWholeRead.witnessProgram).run' 0)
        { callStack := [preludeAlg] } [])) EvalState.empty :=
  RecursiveMapWholeRead.wholeRead_production_incomplete

end KatLang.LazyCollectionBoundaries
