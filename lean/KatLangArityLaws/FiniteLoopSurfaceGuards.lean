import KatLangArityLaws.FiniteLoopSurface

open KatLang KatLang.EvaluatorCore KatLang.WhileRoundProduction KatLang.FiniteLoop KatLang.FiniteLoopSurface

/-!
# E-15 widening evidence: the surface domain, instantiated and executed

The first half instantiates the theorems of `FiniteLoopSurface.lean` on concrete steps whose rows
are NOT numeric literals (`x + 1`, `x < 3`, a capture, a clause family over arithmetic, an alias of
such a step): every domain premise is discharged by the row classes, so the only premise left
is the step projection (and, for an alias, its resolution). The second half runs whole programs:
`repeat(Step(args), 1)` against `Step(args)` for each new row shape and for the builtin and
alias step categories of the C# loop corpus (`LoopStepCallableDispatchTests`), observed by
`reprStr` of the full value, and an exact final-state observation on one concrete supply.
-/

namespace KatLang.FiniteLoopSurfaceGuards

def add (a b : Expr) : Expr := .binary .add a b
def mul (a b : Expr) : Expr := .binary .mul a b
def sub (a b : Expr) : Expr := .binary .sub a b
def lt (a : Expr) (n : Int) : Expr := .comparison a [⟨.lt, .num n⟩]
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def loopRepeat (step : Expr) (n : Expr) : Expr := callN "repeat" [step, n]
def loopWhile (step : Expr) : Expr := callN "while" [step]

/-! ## The row classes, on the shapes they name -/

#guard scalarRow (add (.param "x") (.num 1))
#guard scalarRow (lt (.param "x") 3)
#guard scalarRow (.unary .minus (.param "x"))
#guard scalarRow (mul (callN "F" [.param "x"]) (.num 2))
#guard scalarRow (.emptySequence 0)
#guard valueRow (.capture [.param "b", .param "a"])
#guard valueRow (.index (.param "xs") [.num 0])
#guard valueRow (.listLiteral [.param "x"])
#guard valueRow (.resolve "K")
#guard valueRow (.sequenceSpread (.param "xs"))
-- Excluded: a bare parameter, a bare call and a dot member carry the cell's or the callee's count.
#guard !valueRow (.param "x")
#guard !valueRow (callN "F" [.param "x"])
#guard !valueRow (.dotMember (.param "x") "F" (.resolve "F") none)
-- Value rows that are not scalar rows: their value need not be canonical.
#guard !scalarRow (.capture [.param "b", .param "a"])
#guard !scalarRow (.listLiteral [.param "x"])

/-! ## The domain theorems on concrete steps: every row premise discharged -/

/-- `Inc(x) = x + 1`: arithmetic on a parameter. -/
def incStep : Algorithm := alg ["x"] [] [] [add (.param "x") (.num 1)]
/-- `Next(x) = x + 1, x < 3`: two scalar rows, the shape of a `while` step. -/
def nextStep : Algorithm := alg ["x"] [] [] [add (.param "x") (.num 1), lt (.param "x") 3]
/-- `Flip(a, b) = (b, a)`: one capture row, a value row that is not scalar. -/
def flipStep : Algorithm := alg ["a", "b"] [] [] [.capture [.param "b", .param "a"]]
/-- `Fam(0) = 100; Fam(n) = n * 2`: a clause family whose clause rows are arithmetic. -/
def famStep : Algorithm :=
  .conditional none [] [⟨.litInt 0, alg [] [] [] [.num 100]⟩, ⟨.bind "n", alg [] [] [] [mul (.param "n") (.num 2)]⟩]

theorem incStep_user : UserStep incStep where
  user := ⟨_, _, _, _, _, _, _, rfl⟩
  checks := check_user_passes _ _ _ _ _ _ _ rfl rfl
  noView _ := rfl

theorem incStep_rows : RowsBy scalarRow incStep := by
  intro e he; simp [incStep, alg, Algorithm.output] at he; subst he; rfl

theorem nextStep_user : UserStep nextStep where
  user := ⟨_, _, _, _, _, _, _, rfl⟩
  checks := check_user_passes _ _ _ _ _ _ _ rfl rfl
  noView _ := rfl

theorem nextStep_rows : RowsBy scalarRow nextStep := by
  intro e he; simp [nextStep, alg, Algorithm.output] at he; rcases he with rfl | rfl <;> rfl

theorem flipStep_rows : RowsBy valueRow flipStep := by
  intro e he; simp [flipStep, alg, Algorithm.output] at he; subst he; rfl

theorem famStep_clauses : ∀ b ∈ famStep.branches, ClauseBy scalarRow b.body := by
  intro b hb
  simp [famStep, Algorithm.branches] at hb
  rcases hb with rfl | rfl
  · exact ⟨⟨_, _, _, _, _, _, _, rfl⟩, rfl, by intro e he; simp [alg, Algorithm.output] at he; subst he; rfl⟩
  · exact ⟨⟨_, _, _, _, _, _, _, rfl⟩, rfl, by intro e he; simp [alg, Algorithm.output] at he; subst he; rfl⟩

/-- Before E-15's widening, `UserRowsBounded` was discharged for numeric literal rows only; a
    capture row is now discharged for every context, supply and state. -/
theorem flipStep_rows_bounded (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (s : EvalState) :
    UserRowsBounded flipStep ctx env cells s :=
  userRowsBounded_of_valueRows flipStep flipStep_rows ctx env cells s

theorem famStep_rows_bounded (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (name : String) (s : EvalState) :
    FamilyRowsBounded famStep ctx env cells name s :=
  familyRowsBounded_of_clauses famStep
    (fun b hb => ⟨(famStep_clauses b hb).user, (famStep_clauses b hb).props,
      (famStep_clauses b hb).rows.value_of_scalar⟩) ctx env cells name s

/-- `Inc(x).repeat(1) = Inc(x)` BY VALUE, from the projected step alone. -/
theorem incStep_count_one (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s s₁ : EvalState) (hi : (invokeNeed step).runState s = (.ok (some incStep), s₁))
    (v : CountedResult) :
    (∃ u, (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s = (.ok v, u)) ↔
      (∃ t, (evalNeedUserSupply incStep cells ctx env).runState s₁ = (.ok v, t)) :=
  count_one_user_value step ctx env name cells s s₁ incStep hi incStep_user incStep_rows v

/-- The two-row `while`-shaped step, by value. -/
theorem nextStep_count_one (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s s₁ : EvalState) (hi : (invokeNeed step).runState s = (.ok (some nextStep), s₁))
    (v : CountedResult) :
    (∃ u, (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s = (.ok v, u)) ↔
      (∃ t, (evalNeedUserSupply nextStep cells ctx env).runState s₁ = (.ok v, t)) :=
  count_one_user_value step ctx env name cells s s₁ nextStep hi nextStep_user nextStep_rows v

/-- The clause family, by value. -/
theorem famStep_count_one (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s s₁ : EvalState) (hi : (invokeNeed step).runState s = (.ok (some famStep), s₁))
    (v : CountedResult) :
    (∃ u, (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s = (.ok v, u)) ↔
      (∃ t, (evalNeedFamilySupply famStep cells ctx env name).runState s₁ = (.ok v, t)) :=
  count_one_family_value step ctx env name cells s s₁ none [] _ none hi famStep_clauses v

/-- An alias of `Inc`, by value against the ordinary call of the ALIAS; the alias resolution is the
    one premise beyond the projection. -/
theorem aliasInc_count_one (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (c : NeedSupply.Sourced) (s s₁ s' : EvalState) (origin : CalleeOrigin)
    (hi : (invokeNeed step).runState s = (.ok (some (.alias none [] [] (.resolve "Inc") none false)), s₁))
    (hres : (resolveAliasTarget (.alias none [] [] (.resolve "Inc") none false) ctx).runState s₁ = (.ok incStep, s'))
    (v : CountedResult) :
    (∃ u, (repeatAfterSetup evalUnbounded step ctx env name 1 [c.1]).runState s = (.ok v, u)) ↔
      (∃ t, (evalSuppliedCallCounted origin (.alias none [] [] (.resolve "Inc") none false) [c] ctx env name).runState s₁ = (.ok v, t)) :=
  count_one_alias_value step ctx env name c [] s s₁ none [] [] _ none false origin incStep s' hi hres
    incStep_user incStep_rows v

/-- A `count` step: its numeric result is canonical, so `repeat(1)` IS the call's value. -/
theorem count_step_value (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s s₁ t : EvalState) (origin : CalleeOrigin) (n : Int)
    (hi : (invokeNeed step).runState s = (.ok (some (.builtin .countBuiltin)), s₁))
    (hcall : (evalSuppliedCallCounted origin (.builtin .countBuiltin) (cells.map fun c => (c, none)) ctx env name).runState s₁ =
      (.ok (.atom n, 1), t)) :
    (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s =
      (.ok (reCountValueBoundary (.atom n, 1)), pushCompleted t [.atom n]) :=
  count_one_builtin_ok step ctx env name cells s s₁ .countBuiltin origin hi (.atom n, 1) t
    (scalar_canonical _ (.inl ⟨n, rfl⟩)) hcall

/-! ## Whole programs: `repeat(Step(args), 1)` against `Step(args)` -/

def decls : List (Ident × Algorithm) :=
  [("Inc", incStep),
   ("Next", nextStep),
   ("Flip", flipStep),
   ("Fam", famStep),
   ("Neg", alg ["x"] [] [] [.unary .minus (.param "x")]),
   ("Not", alg ["x"] [] [] [.unary .not (.param "x")]),
   ("Lit", alg ["x"] [] [] [.stringLiteral "a", .boolLiteral true]),
   ("Unit", alg ["x"] [] [] [.emptySequence 0]),
   ("Twice", alg ["x"] [] [] [add (.param "x") (.num 1), mul (.param "x") (.num 2)]),
   ("Sel", alg ["xs"] [] [] [.index (.param "xs") [.num 0]]),
   ("Lst", alg ["x"] [] [] [.listLiteral [.param "x", .param "x"]]),
   ("Blk", alg ["x"] [] [] [.algorithmExpr (alg [] [] [] [add (.param "x") (.num 1)])]),
   ("Spr", alg ["x"] [] [] [.sequenceSpread (.capture [.param "x", .num 1])]),
   -- Internal joins are covered by the invariant, but the parser never produces one.
   ("Join", alg ["x"] [] [] [.sequenceConstruct (.param "x") (.num 1)]),
   ("K", alg [] [] [] [.num 5]),
   ("Name", alg ["x"] [] [] [.resolve "K"]),
   ("Use", alg ["x"] [] [] [mul (callN "Inc" [.param "x"]) (.num 2)]),
   ("AInc", .alias none [] [] (.resolve "Inc")),
   ("ACount", .alias none [] [] (.resolve "count")),
   ("Down", .conditional none [] [⟨.litInt 0, alg [] [] [] [.num 0, .boolLiteral false]⟩,
      ⟨.bind "n", alg [] [] [] [sub (.param "n") (.num 1), lt (.param "n") 100]⟩])]

def program (rows : List Expr) : Expr := .algorithmExpr (algPrivate [] [] decls rows)
def run (rows : List Expr) : Except Error Result := runResult (program rows)

def obs (r : Except Error Result) : String :=
  match r with
  | .ok v => reprStr v
  | .error _ => "error"

/-- `repeat(step, 1)` and `step` complete with the same full value. -/
def sameAsCall (step : Expr) : Bool :=
  match run [loopRepeat step (.num 1)], run [step] with
  | .ok a, .ok b => reprStr a == reprStr b
  | _, _ => false

def valueIs (r : Except Error Result) (v : Result) : Bool := obs r == reprStr v

-- Scalar rows: arithmetic, comparison, unary, strings, Booleans, `()`, several rows, a call inside
-- an operator.
#guard sameAsCall (callN "Inc" [.num 3])
#guard sameAsCall (callN "Next" [.num 1])
#guard sameAsCall (callN "Neg" [.num 3])
#guard sameAsCall (callN "Not" [.boolLiteral true])
#guard sameAsCall (callN "Lit" [.num 0])
#guard sameAsCall (callN "Unit" [.num 0])
#guard sameAsCall (callN "Twice" [.num 4])
#guard sameAsCall (callN "Use" [.num 4])
-- Value rows that are not scalar: a capture, a selection, a list, a name.
#guard sameAsCall (callN "Flip" [.num 1, .num 2])
#guard sameAsCall (callN "Sel" [.listLiteral [.num 8, .num 9]])
#guard sameAsCall (callN "Lst" [.num 1])
#guard sameAsCall (callN "Name" [.num 1])
#guard sameAsCall (callN "Blk" [.num 3])
#guard sameAsCall (callN "Spr" [.num 3])
#guard sameAsCall (callN "Join" [.num 3])
-- Clause families over arithmetic, both clauses.
#guard sameAsCall (callN "Fam" [.num 0])
#guard sameAsCall (callN "Fam" [.num 3])
-- Aliases: of a user step and of a builtin.
#guard sameAsCall (callN "AInc" [.num 3])
#guard sameAsCall (callN "ACount" [.listLiteral [.num 1, .num 2]])
-- Builtin steps of the C# loop corpus: the one result is the call's value.
#guard sameAsCall (callN "count" [.listLiteral [.num 1, .num 2]])
#guard sameAsCall (callN "sum" [.listLiteral [.num 1, .num 2]])
#guard sameAsCall (callN "first" [.listLiteral [.num 3, .num 4]])
#guard sameAsCall (callN "take" [.listLiteral [.num 1, .num 2, .num 3], .num 2])
#guard sameAsCall (callN "order" [.listLiteral [.num 3, .num 1, .num 2]])
#guard sameAsCall (callN "range" [.num 1, .num 3])
#guard sameAsCall (callN "if" [.boolLiteral true, .num 1, .num 2])
#guard sameAsCall (callN "first" [.listLiteral [.emptySequence 0]])
#guard sameAsCall (callN "if" [.boolLiteral false, .binary .div (.num 1) (.num 0), .num 2])
#guard sameAsCall (callN "if" [.boolLiteral true, .num 1, .binary .div (.num 1) (.num 0)])
#guard sameAsCall (callN "last" [.listLiteral [.num 3, .num 4]])
#guard sameAsCall (callN "skip" [.listLiteral [.num 1, .num 2, .num 3], .num 1])
#guard sameAsCall (callN "orderDesc" [.listLiteral [.num 3, .num 1, .num 2]])
#guard sameAsCall (callN "distinct" [.listLiteral [.num 1, .num 1, .num 2]])
#guard sameAsCall (callN "atoms" [.capture [.num 1, .capture [.num 2, .num 3]]])
#guard sameAsCall (callN "contains" [.listLiteral [.num 1, .num 2], .num 2])
#guard sameAsCall (callN "map" [.listLiteral [.num 1, .num 2], .resolve "Inc"])
#guard sameAsCall (callN "filter" [.listLiteral [.num 1, .num 3],
    .algorithmExpr (alg ["x"] [] [] [lt (.param "x") 3])])
#guard sameAsCall (callN "reduce" [.listLiteral [.num 1, .num 2],
    .algorithmExpr (alg ["e", "a"] [] [] [add (.param "e") (.param "a")]), .num 0])
#guard sameAsCall (loopRepeat (callN "Inc" [.num 0]) (.num 2))
#guard sameAsCall (loopWhile (callN "Next" [.num 0]))
#guard sameAsCall (callN "tick" [])
#guard sameAsCall (callN "min" [.listLiteral [.num 1, .num 2]])
#guard sameAsCall (callN "max" [.listLiteral [.num 1, .num 2]])
#guard sameAsCall (callN "avg" [.listLiteral [.num 1, .num 3]])
-- The absolute values, so that agreement is not agreement on an error.
#guard valueIs (run [loopRepeat (callN "Inc" [.num 3]) (.num 1)]) (.atom 4)
#guard valueIs (run [loopRepeat (callN "Twice" [.num 4]) (.num 1)]) (.sequenceValue [.atom 5, .atom 8])
#guard valueIs (run [loopRepeat (callN "Fam" [.num 3]) (.num 1)]) (.atom 6)
#guard valueIs (run [loopRepeat (callN "AInc" [.num 3]) (.num 1)]) (.atom 4)
#guard valueIs (run [loopRepeat (callN "count" [.listLiteral [.num 1, .num 2]]) (.num 1)]) (.atom 2)
#guard valueIs (run [loopRepeat (callN "ACount" [.listLiteral [.num 1, .num 2]]) (.num 1)]) (.atom 2)
#guard valueIs (run [loopRepeat (callN "range" [.num 1, .num 3]) (.num 1)]) (.listValue [.atom 1, .atom 2, .atom 3])
#guard valueIs (run [loopRepeat (callN "count" [.listLiteral [.capture [.num 1, .num 2], .emptySequence 0]]) (.num 1)]) (.atom 2)
#guard valueIs (run [loopRepeat (callN "if" [.boolLiteral false, .binary .div (.num 1) (.num 0), .num 2]) (.num 1)]) (.atom 2)
-- Several rounds over the new shapes compose over the real cells.
#guard valueIs (run [loopRepeat (callN "Fam" [.num 3]) (.num 2)]) (.atom 12)
-- A capture row is ONE grouped slot: the second round meets a one-cell state (as `Group`, FG-L1).
#guard match run [loopRepeat (callN "Flip" [.num 1, .num 2]) (.num 2)] with
  | .error e => (match e with | .withContext _ (.arityMismatch ..) => true | .arityMismatch .. => true | _ => false)
  | .ok _ => false
#guard valueIs (run [loopWhile (callN "Next" [.num 0])]) (.atom 3)
#guard valueIs (run [loopWhile (callN "Down" [.num 3])]) (.atom 0)

/-! ## The theorems' own equations on one concrete supply, with the whole final state -/

def stepCtx : EvalCtx := { callStack := [preludeAlg] }
def stepArg (a : Algorithm) : ResolvedArgumentAlgorithm := { algorithm := a }

def entry (n : Int) : Nat × EvalState :=
  match (readyNeed (.atom n, 1)).runState EvalState.empty with
  | (.ok c, s) => (c, s)
  | (.error _, s) => (0, s)

def viaRepeat (a : Algorithm) (n : Int) : Except Error CountedResult × EvalState :=
  let (c, s) := entry n
  (repeatAfterSetup evalUnbounded (stepArg a) stepCtx [] "S" 1 [c]).runState s

def viaCall (a : Algorithm) (n : Int) : Except Error CountedResult × EvalState :=
  let (c, s) := entry n
  (evalNeedUserSupply a [c] stepCtx []).runState s

def viaFamily (a : Algorithm) (n : Int) : Except Error CountedResult × EvalState :=
  let (c, s) := entry n
  (evalNeedFamilySupply a [c] stepCtx [] "S").runState s

def viaStep (a : Algorithm) (n : Int) : Except Error (List Result) × EvalState :=
  let (c, s) := entry n
  (runNeedStepSlots a stepCtx [] [c] "S").runState s

-- `count_one_user_value` / `count_one_family_value`: the SAME counted value, and the loop heap is
-- the call heap plus one completed cell per slot.
#guard reprStr (viaRepeat incStep 3).1 == reprStr (viaCall incStep 3).1
#guard reprStr (viaRepeat nextStep 1).1 == reprStr (viaCall nextStep 1).1
#guard reprStr (viaRepeat famStep 3).1 == reprStr (viaFamily famStep 3).1
#guard reprStr (viaRepeat famStep 0).1 == reprStr (viaFamily famStep 0).1
#guard (viaRepeat nextStep 1).2.needs.size == (viaCall nextStep 1).2.needs.size + 2
#guard reprStr (viaRepeat nextStep 1).2.lexicalActivations == reprStr (viaCall nextStep 1).2.lexicalActivations
-- All fields of the final state, not just heap length or the activation list.
#guard reprStr (viaRepeat nextStep 1).2 ==
  reprStr (pushCompleted (viaCall nextStep 1).2 [.atom 2, .bool true])
-- `user_slots_canonical`: every slot of a scalar-row step is canonical.
#guard match (viaStep nextStep 1).1 with
  | .ok ys => ys.length == 2 && ys.all (fun y => reprStr y.normalize == reprStr y)
  | .error _ => false

end KatLang.FiniteLoopSurfaceGuards
