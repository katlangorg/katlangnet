import KatLangArityLaws.WhileRoundProduction

open KatLang KatLang.WhileRoundProduction

/-!
# CF-4 executable evidence at the production evaluator (S6c)

Executable witnesses beside the kernel theorems of `WhileRoundProduction.lean`, over the PRODUCTION
operations (`formOutputRow`, `whileVerdictSlots`, `runNeedWhileRound`, whole runs through `runResultM`). The
observations are the run's own state — the number of lexical activations, heap cells and
published property-cache entries — so no tracing field is added to `EvalState`. Each section has
a LOCAL negative control (a re-entering or re-dispatching round, an explicit fresh call, an
unshared node) that the same observation distinguishes from production.
-/

namespace KatLang.WhileRoundProductionGuards

private def sub1 (e : Expr) : Expr := .binary .sub e (.num 1)
private def gt (a : Expr) (n : Int) : Expr := .comparison a [⟨.gt, .num n⟩]
private def lt (a : Expr) (n : Int) : Expr := .comparison a [⟨.lt, .num n⟩]

/-! ## Ordinary counted row formation, including host-built supplies

These witnesses deliberately use Ready counted pairs, not parser-derived value-boundary results.
The same sequence with count one stays one value; with count two it supplies two items. Replacing
the row conversion with an unconditional singleton or unconditional flattening fails one of them.
A zero-count non-spread row stays visible, while an empty spread contributes nothing. -/

def readyRowSupplies (row : Expr) (out : CountedResult) (expected : List Result) : Bool :=
  match (do
    let cell ← readyNeed out
    formOutputRow { callStack := [], needEnv := [("x", cell)] } [] row : EvalM _).runState EvalState.empty |>.1 with
  | .ok items => items == expected
  | .error _ => false

#guard readyRowSupplies (.param "x") (.sequenceValue [.atom 7, .bool true], 2)
  [.atom 7, .bool true]
#guard readyRowSupplies (.param "x") (.sequenceValue [.atom 7, .bool true], 1)
  [.sequenceValue [.atom 7, .bool true]]
#guard readyRowSupplies (.param "x") (.sequenceValue [], 0) [.sequenceValue []]
#guard readyRowSupplies (.sequenceSpread (.param "x")) (.sequenceValue [], 0) []
#guard readyRowSupplies (.param "x") (.listValue [.atom 7, .atom 8], 1)
  [.listValue [.atom 7, .atom 8]]

/-- `Count(x) = x - 1, x > 1`. -/
def countStep : Algorithm := alg ["x"] [] [] [sub1 (.param "x"), gt (.param "x") 1]

/-- ONE production round of `step` over one Ready state cell holding `n`, bound by the ordinary
    binder context (`needBindingContext`), from the empty state. -/
def roundOf (read : Algorithm → EvalCtx → ValEnv → EvalM (Option (List Result))) (step : Algorithm)
    (n : Int) : Except Error (Option (List Result)) × EvalState :=
  (do
    let cell ← readyNeed (.atom n, 1)
    let next ← needBindingContext { callStack := [preludeAlg] } [("x", cell)]
    read step next [] : EvalM _).runState EvalState.empty

def isNext (expected : List Result) : Except Error (Option (List Result)) → Bool
  | .ok (some xs) => xs == expected
  | _ => false

def isStop : Except Error (Option (List Result)) → Bool
  | .ok none => true
  | _ => false

/-- NEGATIVE CONTROL (never a production path): a round that ENTERS THE BODY AGAIN before forming
    the transitions — discovery in one entered context, the earlier rows in a second one. -/
def reenteringRound (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM (Option (List Result)) := do
  let first ← enterAlgorithmBody a ctx env
  match ← WhileRound.discover (formOutputRow first env) a.output.reverse with
  | none => WhileRound.noFlag
  | some (earlier, flagItems) =>
    match flagItems.getLast? with
    | none => WhileRound.noFlag
    | some f =>
      if ← WhileRound.flag f then
        let second ← enterAlgorithmBody a ctx env
        let formed ← OutputRows.formLeftToRight (formOutputRow second env) earlier
        pure (some (WhileRound.nextSlots (formed ++ flagItems)))
      else pure none

/-! ## Setup once versus body re-entry (a user step) -/

-- Production: the true round's next state, with exactly ONE lexical activation (the one body
-- entry of a parameterized step) and the one Ready cell (no row allocates a copy of `x`).
#guard isNext [.atom 3] (roundOf whileVerdictSlots countStep 4).1
#guard (roundOf whileVerdictSlots countStep 4).2.lexicalActivations.size == 1
#guard (roundOf whileVerdictSlots countStep 4).2.needs.size == 1
-- A stopping round enters once too and forms nothing more.
#guard isStop (roundOf whileVerdictSlots countStep 1).1
#guard (roundOf whileVerdictSlots countStep 1).2.lexicalActivations.size == 1
-- The control computes the same VALUE but enters twice: the activation count rejects it.
#guard isNext [.atom 3] (roundOf reenteringRound countStep 4).1
#guard (roundOf reenteringRound countStep 4).2.lexicalActivations.size == 2

-- `whileVerdictSlots_entered`, executed: production equals `conditionFirst` over the production
-- row formation in the ONE entered context, from the entered state.
def enteredSide (n : Int) : Except Error (Option (List Result)) × EvalState :=
  (do
    let cell ← readyNeed (.atom n, 1)
    let next ← needBindingContext { callStack := [preludeAlg] } [("x", cell)]
    let s ← get
    set (enteredState countStep next [] s)
    WhileRound.conditionFirst (formOutputRow (enteredCtx countStep next s) []) countStep.output :
      EvalM _).runState EvalState.empty

#guard reprStr (roundOf whileVerdictSlots countStep 4) == reprStr (enteredSide 4)
#guard reprStr (roundOf whileVerdictSlots countStep 1) == reprStr (enteredSide 1)
-- ... and the re-entering control does not satisfy it (its final state differs).
#guard reprStr (roundOf reenteringRound countStep 4) != reprStr (enteredSide 4)

/-! ## A failed body check reaches nothing (`production_check_failure_reaches_no_row`) -/

def noOutputStep : Algorithm := alg ["x"] [] [] []
def duplicateStep : Algorithm :=
  alg ["x"] [] [privateProp "P" (alg [] [] [] [.num 1]), privateProp "P" (alg [] [] [] [.num 2])]
    [sub1 (.param "x"), gt (.param "x") 1]

def failsWith (check : Error → Bool) : Except Error (Option (List Result)) → Bool
  | .error e => check e
  | _ => false

-- The check's error, no body entry (no activation) and no row (only the bound Ready cell).
#guard failsWith (· matches .missingOutput _) (roundOf whileVerdictSlots noOutputStep 4).1
#guard (roundOf whileVerdictSlots noOutputStep 4).2.lexicalActivations.size == 0
#guard failsWith (· matches .duplicateProperty "P") (roundOf whileVerdictSlots duplicateStep 4).1
#guard (roundOf whileVerdictSlots duplicateStep 4).2.lexicalActivations.size == 0
#guard (roundOf whileVerdictSlots duplicateStep 4).2.needs.size == 1
-- The supply reader (`repeat`) shares the same checks.
#guard (roundOf (fun a c v => (some <$> evalAlgOutputSlots a c v : EvalM _)) noOutputStep 4).1 matches .error (.missingOutput _)

/-! ## Setup once versus re-dispatch (a selected family body) -/

/-- `Fam(0) = 0, false ; Fam(n) = n - 1, n > 0`. -/
def famStep : Algorithm :=
  .conditional none [] [
    ⟨.litInt 0, alg [] [] [] [.num 0, .boolLiteral false]⟩,
    ⟨.bind "n", alg [] [] [] [sub1 (.param "n"), gt (.param "n") 0]⟩]

def famRound (n : Int) : Except Error (Option (List Result)) × EvalState :=
  (do
    let cell ← readyNeed (.atom n, 1)
    runNeedWhileRound famStep { callStack := [preludeAlg] } [] [cell] "Fam" : EvalM _).runState EvalState.empty

/-- NEGATIVE CONTROL: dispatch the family AGAIN for the transitions (a second selected body). -/
def famRedispatch (n : Int) : Except Error (Option (List Result)) × EvalState :=
  (do
    let cell ← readyNeed (.atom n, 1)
    let ctx : EvalCtx := { callStack := [preludeAlg] }
    let (body, next, values) ← selectNeedFamilyBranch bindingChannels famStep [cell] ctx [] "Fam"
    let _ ← whileVerdictSlots body next values
    let (body', next', values') ← selectNeedFamilyBranch bindingChannels famStep [cell] ctx [] "Fam"
    whileVerdictSlots body' next' values' : EvalM _).runState EvalState.empty

-- Production: ONE dispatch, so ONE binder activation (`wireSelectedBranchBody`); the selected
-- body (no parameters, no local member) is entered once without recording another.
#guard isNext [.atom 1] (famRound 2).1
#guard (famRound 2).2.lexicalActivations.size == 1
-- The selected clause's own rows are read condition first: `Fam(0)` stops.
#guard isStop (famRound 0).1
#guard (famRound 0).2.lexicalActivations.size == 1
-- The re-dispatching control reaches the same value with TWO binder activations.
#guard isNext [.atom 1] (famRedispatch 2).1
#guard (famRedispatch 2).2.lexicalActivations.size == 2

-- A selected body with a local property records its OWN body activation in addition to the
-- retained family-binder activation. This makes re-entry BETWEEN the two phases observable,
-- even when the family is dispatched only once in both runs.
def famLocalStep : Algorithm :=
  .conditional none [] [
    ⟨.litInt 0, alg [] [] [] [.num 0, .boolLiteral false]⟩,
    ⟨.bind "x", alg [] [] [
      privateLocalProp "Q" (.localCapturedAncestorParams ["x"])
        (alg [] [] [] [sub1 (.param "x")])]
      [.binary .add (.resolve "Q") (.num 0), gt (.resolve "Q") 0]⟩]

def famLocalRound (n : Int) : Except Error (Option (List Result)) × EvalState :=
  (do
    let cell ← readyNeed (.atom n, 1)
    runNeedWhileRound famLocalStep { callStack := [preludeAlg] } [] [cell] "FamLocal" :
      EvalM _).runState EvalState.empty

/-- NEGATIVE CONTROL: select ONCE, then re-enter that very selected body between discovery
    and transitions (`reenteringRound`); there is no second family dispatch here. -/
def famBodyReentry (n : Int) : Except Error (Option (List Result)) × EvalState :=
  (do
    let cell ← readyNeed (.atom n, 1)
    let (body, next, values) ← selectNeedFamilyBranch bindingChannels famLocalStep [cell]
      { callStack := [preludeAlg] } [] "FamLocal"
    reenteringRound body next values : EvalM _).runState EvalState.empty

#guard isNext [.atom 1] (famLocalRound 2).1
#guard (famLocalRound 2).2.lexicalActivations.size == 2
#guard isNext [.atom 1] (famBodyReentry 2).1
#guard (famBodyReentry 2).2.lexicalActivations.size == 3

/-! ## Whole runs: shared cells, shared local, explicit calls, effectful empty rows -/

private def call (f : String) (args : List Expr) : Expr := .call (.resolve f) args
private def whileOf (step : String) (state : List Expr) : Expr := call "while" [call step state]
private def localQ (body : Expr) : PropDef :=
  privateLocalProp "Q" (.localCapturedAncestorParams ["x"]) (alg [] [] [] [body])

/-- The library. The observable effect is heap allocation: a call whose argument is a computed
    expression (`F(x + 0)`, `Tail(n + 0)`) allocates exactly ONE argument cell per evaluation (a
    bare parameter argument would be transported, allocating nothing).
    `F(y) = y - 1`; `Tail(n) = ()`;
    `Sq(x) = { Q = F(x + 0) ⏎ Q + 0, Q > 1 }` (a local first demanded by the flag);
    `Sx(x) = { Q = F(x + 0) ⏎ Q() + 0, Q() > 1 }` (explicit fresh calls);
    `Tl(n) = n + 1, n < 2, Tail(n + 0)*` and `Tn(n) = n + 1, n < 2` (with/without an effectful
    empty trailing spread); `Tw(x, z) = F(x + 0), F(x + 0), x > 1` (two written occurrences of ONE
    `Expr` node) beside `Tb(x, z) = x - 1, x - 1, x > 1`;
    `Dv(x) = 10 / (x - 1), F(x + 0) > -1` (a true flag, then a failing transition). -/
def program (rows : List Expr) : Expr :=
  let fx := call "F" [.binary .add (.param "x") (.num 0)]
  .algorithmExpr (Algorithm.mk none [] [] [
    privateProp "F" (alg ["y"] [] [] [sub1 (.param "y")]),
    privateProp "Tail" (alg ["n"] [] [] [.emptySequence 0]),
    privateProp "Cnt" countStep,
    privateProp "Sq" (alg ["x"] [] [localQ fx]
      [.binary .add (.resolve "Q") (.num 0), gt (.resolve "Q") 1]),
    privateProp "Sx" (alg ["x"] [] [localQ fx]
      [.binary .add (call "Q" []) (.num 0), gt (call "Q" []) 1]),
    privateProp "Tl" (alg ["n"] [] [] [.binary .add (.param "n") (.num 1), lt (.param "n") 2,
      .sequenceSpread (call "Tail" [.binary .add (.param "n") (.num 0)])]),
    privateProp "Tn" (alg ["n"] [] [] [.binary .add (.param "n") (.num 1), lt (.param "n") 2]),
    privateProp "Tw" (alg ["x", "z"] [] [] [fx, fx, gt (.param "x") 1]),
    privateProp "Tb" (alg ["x", "z"] [] [] [sub1 (.param "x"), sub1 (.param "x"), gt (.param "x") 1]),
    privateProp "Dv" (alg ["x"] [] [] [.binary .div (.num 10) (sub1 (.param "x")), gt fx (-1)])
  ] rows)

def run (rows : List Expr) : Except Error Result × EvalState :=
  (runResultM (program rows)).runState EvalState.empty

def cells (rows : List Expr) : Nat := (run rows).2.needs.size
def entries (rows : List Expr) : Nat := (run rows).2.zeroArgPropertyCache.length

def innermostDivByZero : Error → Bool
  | .withContext _ inner => innermostDivByZero inner
  | .divByZero => true
  | _ => false

def okValue (rows : List Expr) (expected : Result) : Bool :=
  match (run rows).1 with
  | .ok v => v == expected
  | _ => false

-- A captured local first demanded by the flag and reused by the transition, with the correct
-- input-dependent value each round: `Sq` from 4 runs rounds 4 (Q = 3, true), 3 (Q = 2, true),
-- 2 (Q = 1, false) and returns 2 — a stale cross-round value could not stop there.
#guard okValue [whileOf "Sq" [.num 4]] (.atom 2)
-- One published entry per round (three distinct owner contexts) ...
#guard entries [whileOf "Sq" [.num 4]] == 3
-- ... and the explicit fresh calls `Q()` never READ an entry: the first of each round is Q's
-- owning zero-supply invocation in that round's owner context and establishes one entry per round
-- (CACHE-PUB-1; formerly none) ...
#guard okValue [whileOf "Sx" [.num 4]] (.atom 2)
#guard entries [whileOf "Sx" [.num 4]] == 3
-- ... but each still evaluates `F(x + 0)` again in every accepted transition: exactly one more
-- argument cell per accepted round (two), which is what the shared bare read saves.
#guard cells [whileOf "Sx" [.num 4]] == cells [whileOf "Sq" [.num 4]] + 2

-- A lazy supplied initial cell demanded during discovery is reused by the transition: `F(5)` is
-- evaluated ONCE (one more cell than a literal initial state, not two).
#guard okValue [whileOf "Cnt" [call "F" [.num 5]]] (.atom 1)
#guard cells [whileOf "Cnt" [call "F" [.num 5]]] == cells [whileOf "Cnt" [.num 4]] + 1

-- Effectful empty trailing spreads are formed once per round — the stopping round included —
-- and never replayed by the transitions: exactly three `Tail` argument cells over three rounds.
#guard okValue [whileOf "Tl" [.num 0]] (.atom 2)
#guard okValue [whileOf "Tn" [.num 0]] (.atom 2)
#guard cells [whileOf "Tl" [.num 0]] == cells [whileOf "Tn" [.num 0]] + 3

-- Two written occurrences of ONE shared `Expr` node are two rows, each formed once per accepted
-- round (never deduplicated): from (3, 0), rounds 3 and 2 are accepted (two cells each), 1 stops.
#guard okValue [whileOf "Tw" [.num 3, .num 0]] (.sequenceValue [.atom 1, .atom 1])
#guard okValue [whileOf "Tb" [.num 3, .num 0]] (.sequenceValue [.atom 1, .atom 1])
#guard cells [whileOf "Tw" [.num 3, .num 0]] == cells [whileOf "Tb" [.num 3, .num 0]] + 4

-- First transition failure after a successful discovery: the transition's own error, and the
-- flag's evaluation of `F(x + 0)` (one argument cell) is kept — no rollback of discovery.
#guard match (run [whileOf "Dv" [.num 1]]).1 with
  | .error e => innermostDivByZero e
  | _ => false
#guard cells [whileOf "Dv" [.num 1]] == cells [whileOf "Cnt" [.num 1]] + 1

end KatLang.WhileRoundProductionGuards
