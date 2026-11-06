import KatLangArityLaws.FiniteLoopCorrespondence

open KatLang KatLang.EvaluatorCore KatLang.WhileRoundProduction KatLang.FiniteLoop

/-!
# FG-L1 evidence: theorem instantiations and executable boundaries

The first half instantiates the kernel theorems of `FiniteLoopCorrespondence.lean`: a concrete step
that is really in the `count_one_user` domain (so that domain is not vacuous), several rounds
over a state whose slot structure matters, and finite `while` traces. The second half
executes the production operations on the distinctions those theorems state. Observations
keep full raw structure, the emitted count and the whole final state (`reprStr`); nothing is
compared through atom flattening. Lean only: C# is compared at the neutral observation of
`LoopStepCallableDispatchTests`, `LoopCardinalityLawTests` and `LoopConditionFirstTests`.
-/

namespace KatLang.FiniteLoopGuards

/-! ## The ordinary-call domain is inhabited -/

/-- `Lit(x) = 7`, a user step with a parameter, written output and no property. -/
def litStep : Algorithm := alg ["x"] [] [] [.num 7]

theorem literal_row (n : Int) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    (evalCounted (.num n) ctx env).runState s = (.ok (.atom n, 1), s) :=
  production_of_answer_free (.evalCounted (.num n) ctx env) s _ (fun _ => rfl) nofun

/-- Numeric literal rows have value-boundary counts from every state. -/
theorem boundedRows_literals (ctx : EvalCtx) (env : ValEnv) :
    ∀ (rows : List Expr) (s : EvalState), (∀ e ∈ rows, ∃ n, e = Expr.num n) → BoundedRows ctx env rows s := by
  intro rows
  induction rows with
  | nil => intro _ _; trivial
  | cons e rest ih =>
    intro s h
    obtain ⟨n, rfl⟩ := h e (by simp)
    simp only [BoundedRows, literal_row]
    exact ⟨.inr (by simp), ih s (fun x hx => h x (by simp [hx]))⟩

theorem litStep_domain : UserStep litStep where
  user := ⟨_, _, _, _, _, _, _, rfl⟩
  checks := check_user_passes _ _ _ _ _ _ _ rfl rfl
  noView _ := rfl

theorem litStep_rows (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (s : EvalState) :
    UserRowsBounded litStep ctx env cells s :=
  fun _ _ next u _ _ => boundedRows_literals _ _ _ _ (by simp [litStep, alg, Algorithm.output])

/-- `count_one_user` holds for a concrete step, with every domain premise DISCHARGED: the only
    premise left is the projection of the retained step. -/
theorem litStep_count_one (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s s₁ : EvalState) (hi : (invokeNeed step).runState s = (.ok (some litStep), s₁)) :
    StepAgreement id ((runNeedStepSlots litStep ctx env cells name).runState s₁)
      ((evalNeedUserSupply litStep cells ctx env).runState s₁) ∧
    (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s =
      oneRoundOutcome ((runNeedStepSlots litStep ctx env cells name).runState s₁) :=
  count_one_user step ctx env name cells s s₁ litStep hi litStep_domain (litStep_rows ctx env cells s₁)

/-- The slot `7` is canonical, so the value equality of the corollary applies to its row supply. -/
theorem litStep_value : loopResultCounted [.atom 7] = ordinaryValue [.atom 7] :=
  loop_value_of_canonical _ (by simp [Result.normalize])

/-! ## Several rounds over a state whose structure matters -/

section Rounds
variable (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
  (alg₀ : Algorithm) (cells : List Nat) (s s₁ s₂ s₃ s₄ : EvalState) (x y z : Result)

/-- Two rounds: the first emits TWO rows, so the second reads TWO fresh Ready cells; it emits one
    row. The run composes over those real cells, and its result is the last round's supply
    materialized: this is not nesting of a one-argument value call. -/
theorem two_rows_then_one
    (hi₀ : (invokeNeed step).runState s = (.ok (some alg₀), s₁))
    (h₁ : (runNeedStepSlots alg₀ ctx env cells name).runState s₁ = (.ok [x, y], s₂))
    (hi₁ : (invokeNeed step).runState (pushReady s₂ [x, y]) = (.ok (some alg₀), s₃))
    (h₂ : (runNeedStepSlots alg₀ ctx env [s₂.needs.size, s₂.needs.size + 1] name).runState s₃ = (.ok [z], s₄)) :
    (repeatAfterSetup evalUnbounded step ctx env name 2 cells).runState s =
      (.ok (loopResultCounted [z]), pushCompleted s₄ [z]) := by
  have ht : RepeatTrace step ctx env name 2 cells s (.ok (readyAddrs s₄.needs.size [z])) (pushReady s₄ [z]) :=
    .next hi₀ h₁ (.next hi₁ h₂ (.done _ _))
  have hm : (materialize (readyAddrs s₄.needs.size [z])).runState (pushReady s₄ [z]) =
      (.ok [z], pushCompleted s₄ [z]) := materialize_ready [z] s₄.needs (pushReady s₄ [z]) rfl
  exact ((repeat_after_setup_iff step ctx env name 2 cells s _ _).2 ⟨_, _, ht, .materialized hm⟩).1

/-- One grouped row and two rows are ONE public value but different next states. -/
theorem grouped_versus_rows (n : Nat) :
    loopResultCounted [Result.sequenceValue [.atom 1, .atom 2]] = loopResultCounted [.atom 1, .atom 2] ∧
    (readyAddrs n [Result.sequenceValue [.atom 1, .atom 2]]).length = 1 ∧
    (readyAddrs n [.atom 1, .atom 2]).length = 2 := by
  simp [loopResultCounted, loopStateResult, reCountValueBoundary, Result.normalize, readyAddrs]

/-- The first failure stops the composition, whatever rounds remain, in its retained state. -/
theorem failure_after_prefix (n : Nat) (e : Error) (he : e ≠ .fuelExhausted)
    (hi₀ : (invokeNeed step).runState s = (.ok (some alg₀), s₁))
    (h₁ : (runNeedStepSlots alg₀ ctx env cells name).runState s₁ = (.ok [x], s₂))
    (hi₁ : (invokeNeed step).runState (pushReady s₂ [x]) = (.ok (some alg₀), s₃))
    (h₂ : (runNeedStepSlots alg₀ ctx env [s₂.needs.size] name).runState s₃ = (.error e, s₄)) :
    (repeatDriver step ctx env name evalUnbounded (n + 2) cells).runState s = (.error e, s₄) :=
  ((repeat_trace_iff step ctx env name (n + 2) cells s s₄ _).1
    (.next hi₀ h₁ (.stepError he hi₁ h₂))).1

/-- One accepted transition, then a false round: the result cell is the transition's Ready cell,
    the entering cell of the stopping round, in the state that round left. -/
theorem one_transition_then_false
    (hi₀ : (invokeNeed step).runState s = (.ok (some alg₀), s₁))
    (h₁ : (runNeedWhileRound alg₀ ctx env cells name).runState s₁ = (.ok (some [x]), s₂))
    (hi₁ : (invokeNeed step).runState (pushReady s₂ [x]) = (.ok (some alg₀), s₃))
    (h₂ : (runNeedWhileRound alg₀ ctx env [s₂.needs.size] name).runState s₃ = (.ok none, s₄)) :
    (whileDriver step ctx env name cells).runState s = (.ok [s₂.needs.size], s₄) :=
  (while_of_trace step ctx env name (.next hi₀ h₁ (.stop hi₁ h₂))).1

/-- An ordinary error after accepted transitions is the driver's outcome, nothing later runs. -/
theorem while_error_after_prefix (e : Error) (he : e ≠ .fuelExhausted)
    (hi₀ : (invokeNeed step).runState s = (.ok (some alg₀), s₁))
    (h₁ : (runNeedWhileRound alg₀ ctx env cells name).runState s₁ = (.ok (some [x]), s₂))
    (hi₁ : (invokeNeed step).runState (pushReady s₂ [x]) = (.ok (some alg₀), s₃))
    (h₂ : (runNeedWhileRound alg₀ ctx env [s₂.needs.size] name).runState s₃ = (.error e, s₄)) :
    (whileDriver step ctx env name cells).runState s = (.error e, s₄) :=
  (while_of_trace step ctx env name (.next hi₀ h₁ (.roundError he hi₁ h₂))).1

/-- Count zero does not depend on the step at all. -/
theorem zero_rounds_ignore_the_step (other : ResolvedArgumentAlgorithm) :
    (repeatAfterSetup evalUnbounded step ctx env name 0 cells).runState s =
      (repeatAfterSetup evalUnbounded other ctx env name 0 cells).runState s := by
  rw [repeat_zero, repeat_zero]

/-- A projection refusal is an iteration-time failure: `n + 1` rounds fail, zero rounds do not. -/
theorem refused_step_fails_at_the_first_iteration (n : Nat) (t : EvalState)
    (h : (invokeNeed step).runState s = (.ok none, t)) :
    (repeatDriver step ctx env name evalUnbounded (n + 1) cells).runState s =
      (.error (Error.notAnAlgorithm (invokingSlotRole .repeatBuiltin)), t) :=
  ((repeat_trace_iff step ctx env name (n + 1) cells s t _).1 (.refused h)).1

end Rounds

/-! ## Executable boundaries on whole programs -/

def add (a b : Expr) : Expr := .binary .add a b
def sub (a b : Expr) : Expr := .binary .sub a b
def mul (a b : Expr) : Expr := .binary .mul a b
def dv (a b : Expr) : Expr := .binary .div a b
def lt (a : Expr) (n : Int) : Expr := .comparison a [⟨.lt, .num n⟩]
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def tickCall : Expr := callN "tick" []
def loopRepeat (step : Expr) (n : Expr) : Expr := callN "repeat" [step, n]
def loopWhile (step : Expr) : Expr := callN "while" [step]
/-- `[1][5]*`: an explicit spread whose own evaluation fails (`badIndex`). -/
def badSpread : Expr := .sequenceSpread (.index (.listLiteral [.num 1]) [.num 5])
/-- `[1][7]`: a value that fails (`badIndex`) with a different selector. -/
def badValue : Expr := .index (.listLiteral [.num 1]) [.num 7]

def decls : List (Ident × Algorithm) :=
  [("Inc", alg ["x"] [] [] [add (.param "x") (.num 1)]),
   ("Swap", alg ["a", "b"] [] [] [.param "b", .param "a"]),
   ("Group", alg ["a", "b"] [] [] [.capture [.param "b", .param "a"]]),
   ("Open", alg ["a", "b"] [] [] [.sequenceSpread (.capture [.param "b", .param "a"])]),
   ("Drop", alg ["x"] [] [] [.num 1]),
   ("Pair", alg ["x"] [] [] [.param "x", .param "x"]),
   ("Nothing", alg ["x"] [] [] [.emptySequence 0]),
   ("Gone", alg ["x"] [] [] [.sequenceSpread (.emptySequence 0)]),
   ("Zero", alg [] [] [] [.num 9]),
   ("Fam", .conditional none [] [
      ⟨.litInt 0, alg [] [] [] [.num 100]⟩,
      ⟨.bind "n", alg [] [] [] [sub (.param "n") (.num 1)]⟩]),
   ("A", .alias none [] [] (.resolve "Inc")),
   ("V", alg [] [] [] [.num 5]),
   -- `n` ticks, then `1 / n`: a division by zero after a successful prefix.
   ("Dec", alg ["n"] [] [] [add (mul tickCall (.num 0)) (add (mul (dv (.num 1) (.param "n")) (.num 0)) (sub (.param "n") (.num 1)))]),
   -- `x + 1 + tick() * 0, x < 2`: the transition row runs only after a true flag.
   ("Up", alg ["x"] [] [] [add (add (.param "x") (.num 1)) (mul tickCall (.num 0)), lt (.param "x") 2]),
   -- `v` is a VALUE parameter in callee position.
   ("Ap", alg ["v", "n"] [] [] [loopRepeat (.call (.param "v") [.num 1]) (.param "n")])]

def program (rows : List Expr) : Expr := .algorithmExpr (algPrivate [] [] decls rows)
def run (rows : List Expr) : Except Error Result := runResult (program rows)

def ticks (rows : List Expr) : Option Nat :=
  match runResultWithState (program rows) with
  | .ok (_, s) => some s.tickCounter
  | .error _ => none

def valueIs (r : Except Error Result) (v : Result) : Bool :=
  match r with
  | .ok x => reprStr x == reprStr v
  | .error _ => false

def innermost : Error → Error
  | .withContext _ e => innermost e
  | e => e

def failsWith (r : Except Error Result) (p : Error → Bool) : Bool :=
  match r with
  | .error e => p (innermost e)
  | .ok _ => false

def pair (a b : Int) : Result := .sequenceValue [.atom a, .atom b]

-- Counts zero, one and several: no zero-count iteration, one call, a genuine composition.
#guard valueIs (run [loopRepeat (callN "Inc" [.num 3]) (.num 0)]) (.atom 3)
#guard valueIs (run [loopRepeat (callN "Inc" [.num 3]) (.num 1)]) (.atom 4)
#guard valueIs (run [loopRepeat (callN "Inc" [.num 3]) (.num 4)]) (.atom 7)
-- The empty initial state; a lazy unused input; zero iterations still materialize.
#guard valueIs (run [loopRepeat (callN "Zero" []) (.num 0)]) (.sequenceValue [])
#guard valueIs (run [loopRepeat (callN "Drop" [badValue]) (.num 1)]) (.atom 1)
#guard failsWith (run [loopRepeat (callN "Drop" [badValue]) (.num 0)]) (· matches .badIndex)
-- A captured spread fails before the count is demanded; a non-spread argument is not demanded.
#guard failsWith (run [loopRepeat (callN "Inc" [badSpread]) (dv (.num 1) (.num 0))]) (· matches .badIndex)
#guard failsWith (run [loopRepeat (callN "Inc" [badValue]) (dv (.num 1) (.num 0))]) (· matches .divByZero)
#guard failsWith (run [loopRepeat (callN "Inc" [.num 1]) (.num (-1))]) (· matches .illegalInEval _)
-- A noncallable captured callee: zero iterations finish; an iteration refuses it.
#guard valueIs (run [callN "Ap" [.num 5, .num 0]]) (.atom 1)
#guard failsWith (run [callN "Ap" [.num 5, .num 1]]) (· matches .notAnAlgorithm _)
-- Slots are not the public value. Two rows, a grouped row and a spread of it: the same value after
-- one iteration, different next states, so the second iteration tells them apart.
#guard valueIs (run [loopRepeat (callN "Swap" [.num 1, .num 2]) (.num 1)]) (pair 2 1)
#guard valueIs (run [loopRepeat (callN "Group" [.num 1, .num 2]) (.num 1)]) (pair 2 1)
#guard valueIs (run [loopRepeat (callN "Open" [.num 1, .num 2]) (.num 1)]) (pair 2 1)
#guard valueIs (run [loopRepeat (callN "Swap" [.num 1, .num 2]) (.num 2)]) (pair 1 2)
#guard valueIs (run [loopRepeat (callN "Open" [.num 1, .num 2]) (.num 2)]) (pair 1 2)
#guard failsWith (run [loopRepeat (callN "Group" [.num 1, .num 2]) (.num 2)]) (· matches .arityMismatch ..)
-- The naive nesting of a one-argument value call is the WRONG composition.
#guard failsWith (run [callN "Swap" [callN "Swap" [.num 1, .num 2]]]) (· matches .arityMismatch ..)
-- An exact list is one slot; `()` is one visible slot; an empty spread is none.
#guard valueIs (run [loopRepeat (callN "Pair" [.listLiteral [.num 1]]) (.num 1)])
  (.sequenceValue [.listValue [.atom 1], .listValue [.atom 1]])
#guard valueIs (run [loopRepeat (callN "Nothing" [.num 1]) (.num 1)]) (.sequenceValue [])
#guard valueIs (run [loopRepeat (callN "Nothing" [.num 1]) (.num 2)]) (.sequenceValue [])
#guard valueIs (run [loopRepeat (callN "Gone" [.num 1]) (.num 1)]) (.sequenceValue [])
#guard failsWith (run [loopRepeat (callN "Gone" [.num 1]) (.num 2)]) (· matches .arityMismatch ..)
-- The callable categories.
#guard valueIs (run [loopRepeat (callN "Fam" [.num 2]) (.num 3)]) (.atom 100)
#guard valueIs (run [loopRepeat (callN "count" [.listLiteral [.num 1, .num 2]]) (.num 1)]) (.atom 2)
#guard valueIs (run [loopRepeat (callN "A" [.num 1]) (.num 2)]) (.atom 3)
-- A failure after a successful prefix: the second round ticks and fails; no third round.
#guard valueIs (run [loopRepeat (callN "Dec" [.num 1]) (.num 1)]) (.atom 0)
#guard failsWith (run [loopRepeat (callN "Dec" [.num 1]) (.num 3)]) (· matches .divByZero)
#guard (runResultM (program [loopRepeat (callN "Dec" [.num 1]) (.num 3)])).runState EvalState.empty |>.2.tickCounter == 2
-- False-first and later-false: the entering cell survives, skipped transition rows never run.
#guard valueIs (run [loopWhile (callN "Up" [.num 5])]) (.atom 5)
#guard ticks [loopWhile (callN "Up" [.num 5])] == some 0
#guard valueIs (run [loopWhile (callN "Up" [.num 0])]) (.atom 2)
#guard ticks [loopWhile (callN "Up" [.num 0])] == some 2

/-! ## The theorems' own equations, on one concrete supply, with the whole final state -/

def stepCtx : EvalCtx := { callStack := [preludeAlg] }

def stepArg (a : Algorithm) : ResolvedArgumentAlgorithm := { algorithm := a }

def incStep : Algorithm := alg ["x"] [] [] [add (.param "x") (.num 1)]
def swapStep : Algorithm := alg ["x"] [] [] [.param "x", add (.param "x") (.num 1)]
/-- One spread row supplying two slots. -/
def spreadStep : Algorithm := alg ["x"] [] [] [.sequenceSpread (.capture [.param "x", .num 2])]

def entry (n : Int) : Nat × EvalState :=
  match (readyNeed (.atom n, 1)).runState EvalState.empty with
  | (.ok c, s) => (c, s)
  | (.error _, s) => (0, s)

def viaRepeat (a : Algorithm) (n : Int) : Except Error CountedResult × EvalState :=
  let (c, s) := entry n
  (repeatAfterSetup evalUnbounded (stepArg a) stepCtx [] "S" 1 [c]).runState s

def viaOneRound (a : Algorithm) (n : Int) : Except Error CountedResult × EvalState :=
  let (c, s) := entry n
  oneRoundOutcome ((runNeedStepSlots a stepCtx [] [c] "S").runState s)

def viaCall (a : Algorithm) (n : Int) : Except Error CountedResult × EvalState :=
  let (c, s) := entry n
  (evalNeedUserSupply a [c] stepCtx []).runState s

def viaStep (a : Algorithm) (n : Int) : Except Error (List Result) × EvalState :=
  let (c, s) := entry n
  (runNeedStepSlots a stepCtx [] [c] "S").runState s

-- `repeat_one_round`: the whole outcome and final state, for one and for several rows.
#guard reprStr (viaRepeat incStep 3) == reprStr (viaOneRound incStep 3)
#guard reprStr (viaRepeat swapStep 3) == reprStr (viaOneRound swapStep 3)
#guard reprStr (viaRepeat spreadStep 3) == reprStr (viaOneRound spreadStep 3)
-- `user_step_agreement`: the SAME final state as the ordinary call.
#guard reprStr (viaStep incStep 3).2 == reprStr (viaCall incStep 3).2
#guard reprStr (viaStep swapStep 3).2 == reprStr (viaCall swapStep 3).2
#guard reprStr (viaStep spreadStep 3).2 == reprStr (viaCall spreadStep 3).2
-- ... the ordinary value is `ordinaryValue` of the row supply.
#guard match (viaStep swapStep 3).1, (viaCall swapStep 3).1 with
  | .ok ys, .ok c => reprStr c == reprStr (ordinaryValue ys) && reprStr c == reprStr (loopResultCounted ys)
  | _, _ => false
-- The loop's final heap is the call's plus the completed slot cells, nothing else.
#guard (viaRepeat swapStep 3).2.needs.size == (viaCall swapStep 3).2.needs.size + 2
#guard reprStr (viaRepeat swapStep 3).2.zeroArgPropertyCache == reprStr (viaCall swapStep 3).2.zeroArgPropertyCache
#guard reprStr (viaRepeat swapStep 3).2.lexicalActivations == reprStr (viaCall swapStep 3).2.lexicalActivations

/-! ## Why the direct equality is narrowed -/

-- A row whose count is not a value boundary: a host-built Ready cell of count two. The loop's row
-- rule splits it; the ordinary reader keeps one slot. Hence `RowBoundary`.
def hostTwoCell : Except Error (List Result) × Except Error CountedResult :=
  let hostValue : CountedResult := (pair 1 2, 2)
  match (readyNeed hostValue).runState EvalState.empty with
  | (.ok c, s) =>
    let echo := alg ["x"] [] [] [.param "x"]
    (((runNeedStepSlots echo stepCtx [] [c] "S").runState s).1,
     ((evalNeedUserSupply echo [c] stepCtx []).runState s).1)
  | _ => (.error .badArity, .error .badArity)

#guard match hostTwoCell with
  | (.ok ys, .ok c) => ys.length == 2 && reprStr c.fst == reprStr (pair 1 2)
  | _ => false

-- A zero-supply call publishes a property result; the loop reads no such entry. Hence the
-- non-empty supply of `ordinary_user_of_nonempty`.
def publishedAfter (rows : List Expr) : Option Nat :=
  match runResultWithState (.algorithmExpr (algPrivate [] [] [("Zero", alg [] [] [] [.num 9])] rows)) with
  | .ok (_, s) => some s.zeroArgPropertyCache.length
  | .error _ => none

#guard publishedAfter [callN "Zero" []] == some 1
#guard publishedAfter [loopRepeat (callN "Zero" []) (.num 1)] == some 0

end KatLang.FiniteLoopGuards
