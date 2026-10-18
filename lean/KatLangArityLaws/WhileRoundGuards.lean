import KatLangArityLaws.WhileRound

open KatLang

/-!
# Witnesses for the condition-first `while` round (LOOP-CF1)

Executable witnesses over the PRODUCTION `WhileRound.conditionFirst`, with a row-forming capability
whose effects are observable: every formed row appends one Ready cell labelled with the row to the
need heap, so the heap's labels are the formation order. A "pulse" row reads the heap size as a
counter. They witness what the laws state, and what they deliberately do NOT state: without the
CF-7 premise, condition-first effects are not a subset of step-first effects, and a step-first
success can become a condition-first failure.
-/

namespace KatLang.WhileRoundGuards

open KatLang.WhileRoundLaws

/-- Row `.num label` of a test round: logs `label`, then supplies `items label (pulse)`, where the
    pulse is the number of rows formed before it; `none` items fail with `divByZero`. -/
def logRow (items : Int → Nat → Option (List Result)) : Expr → EvalM (List Result)
  | .num label => do
    let pulse := (← get).needs.size
    let _ ← readyNeed (.atom label, 1)
    match items label pulse with
    | some xs => pure xs
    | none => throw Error.divByZero
  | _ => throw (Error.illegalInEval "not a test row")

/-- The labels of the formed rows, in formation order. -/
def formed (st : EvalState) : List Int :=
  st.needs.toList.filterMap fun cell =>
    match cell.suspension with
    | .ready (.atom label, _) => some label
    | _ => none

def rows (n : Nat) : List Expr := (List.range n).map fun i => .num (Int.ofNat i)

def runRound (round : EvalM (Option (List Result))) : Except Error (Option (List Result)) × List Int :=
  let (out, st) := round.runState EvalState.empty
  (out, formed st)

def isStop : Except Error (Option (List Result)) → Bool
  | .ok none => true
  | _ => false

def isNext (expected : List Result) : Except Error (Option (List Result)) → Bool
  | .ok (some next) => next == expected
  | _ => false

def isDivByZero : Except Error (Option (List Result)) → Bool
  | .error .divByZero => true
  | _ => false

def isTypeMismatch : Except Error (Option (List Result)) → Bool
  | .error (.typeMismatch _) => true
  | _ => false

def isNoFlag : Except Error (Option (List Result)) → Bool
  | .error (.withContext _ .badArity) => true
  | _ => false

-- `10 / (x - 1), x > 1` at x = 1: row 0 fails, row 1 is `false`.
def divThenFalse (label : Int) (_ : Nat) : Option (List Result) :=
  if label = 0 then none else some [.bool false]

#guard isStop (runRound (WhileRound.conditionFirst (logRow divThenFalse) (rows 2))).1
#guard (runRound (WhileRound.conditionFirst (logRow divThenFalse) (rows 2))).2 == [1]
-- The retired reading failed on row 0 first.
#guard isDivByZero (runRound (stepFirst (logRow divThenFalse) (rows 2))).1

-- A true round: the flag row first, then the earlier rows left to right; the next state is the
-- supply in written order without the flag.
def threeRows (label : Int) (_ : Nat) : Option (List Result) :=
  if label = 2 then some [.bool true] else some [.atom (10 + label)]

#guard (runRound (WhileRound.conditionFirst (logRow threeRows) (rows 3))).2 == [2, 0, 1]
#guard isNext [.atom 10, .atom 11] (runRound (WhileRound.conditionFirst (logRow threeRows) (rows 3))).1

-- Effectful EMPTY trailing rows (review r3/r12): discovery forms rows 3 and 2 (right to left),
-- then the flag row 1; a false flag never forms row 0. Step-first formed 0, 1, 2, 3.
def emptyTail (label : Int) (_ : Nat) : Option (List Result) :=
  if label ≥ 2 then some [] else if label = 1 then some [.bool false] else some [.atom 2]

#guard (runRound (WhileRound.conditionFirst (logRow emptyTail) (rows 4))).2 == [3, 2, 1]
#guard isStop (runRound (WhileRound.conditionFirst (logRow emptyTail) (rows 4))).1
#guard (runRound (stepFirst (logRow emptyTail) (rows 4))).2 == [0, 1, 2, 3]

-- With a true flag, the empty trailing rows are not re-formed: 3, 2, 1, then 0.
def emptyTailTrue (label : Int) (_ : Nat) : Option (List Result) :=
  if label ≥ 2 then some [] else if label = 1 then some [.bool true] else some [.atom 2]

#guard (runRound (WhileRound.conditionFirst (logRow emptyTailTrue) (rows 4))).2 == [3, 2, 1, 0]
#guard isNext [.atom 2] (runRound (WhileRound.conditionFirst (logRow emptyTailTrue) (rows 4))).1

-- One item is both the flag and the next state; no item at all is the missing flag.
def oneItem (_ : Int) (_ : Nat) : Option (List Result) := some [.bool true]
def noItem (_ : Int) (_ : Nat) : Option (List Result) := some []

#guard isNext [.bool true] (runRound (WhileRound.conditionFirst (logRow oneItem) (rows 1))).1
#guard isNoFlag (runRound (WhileRound.conditionFirst (logRow noItem) (rows 3))).1
#guard (runRound (WhileRound.conditionFirst (logRow noItem) (rows 3))).2 == [2, 1, 0]

-- A non-Boolean flag is reported before the failing earlier row.
def failThenFive (label : Int) (_ : Nat) : Option (List Result) :=
  if label = 0 then none else some [.atom 5]

#guard isTypeMismatch (runRound (WhileRound.conditionFirst (logRow failThenFive) (rows 2))).1
#guard isDivByZero (runRound (stepFirst (logRow failThenFive) (rows 2))).1

-- NOT an effect subset (review r1): `1 / 0, mark(false)`. Condition-first forms the flag row,
-- which the step-first execution never reached (it failed on row 0), and succeeds.
#guard (runRound (stepFirst (logRow divThenFalse) (rows 2))).2 == [0]
#guard (runRound (WhileRound.conditionFirst (logRow divThenFalse) (rows 2))).2 == [1]

-- Old success becomes a new failure (review r19): `1 / (1 - pulse()), pulse() == 0`.
def pulseRows (label : Int) (pulse : Nat) : Option (List Result) :=
  if label = 0 then (if pulse = 1 then none else some [.atom 1])
  else some [.bool (pulse = 0)]

#guard isStop (runRound (stepFirst (logRow pulseRows) (rows 2))).1
#guard isDivByZero (runRound (WhileRound.conditionFirst (logRow pulseRows) (rows 2))).1

-- CF-7's premise holds for these state-independent rows, and the readers agree.
def constRows (label : Int) (_ : Nat) : Option (List Result) :=
  if label = 2 then some [.bool true] else some [.atom label]

def pureRow : Expr → EvalM (List Result)
  | .num label => match constRows label 0 with
    | some xs => pure xs
    | none => throw Error.divByZero
  | _ => throw (Error.illegalInEval "not a test row")

#guard (WhileRound.conditionFirst pureRow (rows 3)).runState EvalState.empty
  |>.1 |> isNext [.atom 0, .atom 1]
#guard (stepFirst pureRow (rows 3)).runState EvalState.empty |>.1 |> isNext [.atom 0, .atom 1]

end KatLang.WhileRoundGuards
