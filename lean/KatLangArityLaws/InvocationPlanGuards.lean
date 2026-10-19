import KatLangArityLaws.InvocationPlan

open KatLang KatLang.CallPlan

/-!
# M1.5 guards: invocation plans on the AUTHORITATIVE production route

Every guard below runs the authoritative evaluator of `KatLang.lean` itself: VALUE is the public
`demandNeed` (whose suspended-call arm is `NeedPlan.execute` at `productionPlanRoute`, and whose
nested demands go through the recursive `demandNeedRecursive` edge installing the same route),
META is `reifyNeedCall` and explicit invocation is `invokeNeedCall`. There is no harness
evaluator, no separate plan table and no prototype state: plan state is the `plan` field of the
production `NeedCell`s of the production `EvalState`.

`agrees` compares plan-routed VALUE with the pre-M1.5 completion of the same cell (the shell
around `reCountValueBoundary <$> evalCounted source`, i.e. the ordinary
`evalCallCountedExpr`): same outcome, and the same heap once the demanded cell's own plan
record is erased. Nested demands inside both runs use the authoritative recursive edge.
-/

namespace KatLang.CallPlanGuards

def bad : Expr := .binary .div (.num 1) (.num 0)

/-- `Sign(0) = 0`, `Sign(n) = 1`: a clause family whose first branch inspects its argument. -/
def signFamily : Algorithm :=
  .conditional none [] [
    ⟨.litInt 0, alg [] [] [] [.num 0]⟩,
    ⟨.bind "n", alg [] [] [] [.num 1]⟩]

def root : Algorithm := algPrivate [] []
  [("F", alg ["v"] [] [] [.binary .add (.param "v") (.num 1)]),
   ("Keep", alg ["x", "y"] [] [] [.param "x"]),
   ("Add2", alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")]),
   ("Pair", alg [] [] [] [.num 1, .num 2]),
   ("BadPair", alg [] [] [] [bad, .num 2]),
   ("Bad", alg ["v"] [] [] [.binary .div (.param "v") (.num 0)]),
   ("Id", alg ["x"] [] [] [.param "x"]),
   -- A user body whose own row supplies a nested call `F(v)` to `Id`.
   ("G", alg ["v"] [] [] [.call (.resolve "Id") [.call (.resolve "F") [.param "v"]]]),
   ("Sign", signFamily)] []

/-- A different lexical owner whose `F` means something else (shadowing check). -/
def otherRoot : Algorithm :=
  algPrivate [] [] [("F", alg ["v"] [] [] [.binary .mul (.param "v") (.num 100)])] []

def ctx : EvalCtx := EvalCtx.empty.push root
def otherCtx : EvalCtx := EvalCtx.empty.push otherRoot

def callF (arg : Expr) : Expr := .call (.resolve "F") [arg]

/-! ## Observation helpers (read-only views of the production heap) -/

def start {α : Type} (setup : EvalM α) : Option (α × EvalState) :=
  match setup.run EvalState.empty with
  | .ok r => some r
  | .error _ => none

def run {α : Type} (m : EvalM α) (s : EvalState) : Except Error α × EvalState :=
  m.runState s

def refOk (r : Except Error NeedPlan.CallReference) (a : Nat) : Bool :=
  match r with
  | .ok ref => ref.plan == a
  | .error _ => false

def valueIs (r : Except Error CountedResult) (v : Int) : Bool :=
  match r with
  | .ok (value, _) => value == .atom v
  | .error _ => false

/-- The innermost error under its context frames. -/
def innermostError : Error -> Error
  | .withContext _ inner => innermostError inner
  | err => err

/-- `r` failed, and its innermost error is exactly `expected` (constructor and payload). -/
def failsAs {α : Type} (r : Except Error α) (expected : Error) : Bool :=
  match r with
  | .ok _ => false
  | .error err => reprStr (innermostError err) == reprStr expected

-- The observer rejects success, another constructor and another payload, through frames.
#guard failsAs (.error (.withContext "c" (.withContext "d" .divByZero)) : Except Error Nat) .divByZero
#guard !failsAs (.ok 1 : Except Error Nat) .divByZero
#guard !failsAs (.error (.withContext "c" .badArity) : Except Error Nat) .divByZero
#guard !failsAs (.error (.arityMismatch 1 3) : Except Error Nat) (.arityMismatch 1 2)

/-- The META refusal of a cell that is not a supplied call computation. -/
def metaRefusal : Error := .notAnAlgorithm "meta: not a supplied call computation"

def suspendedAt (s : EvalState) (a : Nat) : Bool :=
  match s.needs[a]? with
  | some { state := .suspended, .. } => true
  | _ => false

def completedAt (s : EvalState) (a : Nat) : Bool :=
  match s.needs[a]? with
  | some { state := .completed _, .. } => true
  | _ => false

def unpreparedAt (s : EvalState) (a : Nat) : Bool :=
  match s.needs[a]? with
  | some { plan := .unprepared, .. } => true
  | _ => false

/-- The plan's prepared supply addresses, if its preparation succeeded. -/
def suppliedCells (s : EvalState) (a : Nat) : Option (List Nat) :=
  match s.needs[a]? with
  | some { plan := .prepared (.ok cells), .. } => some (cells.map Prod.fst)
  | _ => none

def preparationFailed (s : EvalState) (a : Nat) : Bool :=
  match s.needs[a]? with
  | some { plan := .prepared (.error _), .. } => true
  | _ => false

/-- Every cell's plan record, in address order (an order-sensitive fingerprint). -/
def planRecords (s : EvalState) : String := reprStr (s.needs.toList.map NeedCell.plan)

/-- The addresses of cells that hold a written call to `name`. -/
def callCellsTo (s : EvalState) (name : Ident) : List Nat :=
  (List.range s.needs.size).filter fun a =>
    match s.needs[a]? with
    | some { suspension := .expression (.call (.resolve n) _) _ _, .. } => n == name
    | _ => false

/-- Erase one cell's plan record (`agrees` compares everything else). -/
def erasePlan (a : Nat) (s : EvalState) : EvalState :=
  { s with needs := s.needs.modify a (fun c => { c with plan := .unprepared }) }

/-! ## Plan-routed VALUE = the pre-M1.5 ordinary completion (result and heap) -/

/-- The completion shell of the cell around the ordinary call, exactly as `NeedDemand.step`
    ran it before M1.5 (`reCountValueBoundary <$> ev e ctx env`). -/
def ordinaryCompletion (a : Nat) : EvalM CountedResult := do
  let some cell := (← get).needs[a]? | throw (Error.illegalInEval "invalid need address")
  match cell.suspension with
  | .expression e caller values =>
    modify fun s => { s with needs := s.needs.modify a (fun c => { c with state := .evaluating }) }
    let outcome ← evalAttempt (reCountValueBoundary <$> evalCounted e caller values)
    modify fun s => { s with needs := s.needs.modify a (fun c => { c with state := .completed outcome }) }
    return ← outcome
  | _ => throw (Error.illegalInEval "not an expression cell")

def agrees (source : Expr) : Bool :=
  match start (supplyNeed source ctx []) with
  | some (a, st) =>
    let ordinary := run (ordinaryCompletion a) st
    let planned := run (demandNeed a) st
    reprStr ordinary.1 == reprStr planned.1 &&
      reprStr ordinary.2 == reprStr (erasePlan a planned.2)
  | none => false

#guard agrees (callF (.num 41))                                              -- demanded argument
#guard agrees (.call (.resolve "Keep") [.num 7, bad])                        -- unused failing argument
#guard agrees (.call (.resolve "Add2") [.sequenceSpread (.call (.resolve "Pair") [])]) -- arbitrary spread
#guard agrees (.call (.resolve "Add2") [.sequenceSpread (.call (.resolve "BadPair") [])]) -- failing spread
#guard agrees (.call (.resolve "F") [bad, .num 2])                           -- wrong cardinality
#guard agrees (.call (.resolve "Bad") [.num 1])                              -- failing VALUE
#guard agrees (callF (callF (.num 1)))                                       -- nested supplied call
#guard agrees (.call (.resolve "G") [.num 41])                               -- nested call in a body
#guard agrees (.call (.resolve "count") [.listLiteral [.num 1, .num 2]])      -- builtin callee
#guard agrees (.call (.resolve "Sign") [.num 0])                             -- clause family
#guard agrees (.call (.resolve "Sign") [bad])                                -- family inspects a failure
#guard agrees (.call (.resolve "Missing") [bad])                             -- unresolvable callee

/-- Wrong cardinality keeps its exact error (shape and call context) and demands nothing. -/
def wrongArityError : Bool :=
  match start (supplyNeed (.call (.resolve "F") [bad, .num 2]) ctx []) with
  | some (a, s0) =>
    let (v, s1) := run (demandNeed a) s0
    let (o, _) := run (ordinaryCompletion a) s0
    reprStr v == reprStr o &&
    (match v with
     | .error (.withContext m (.arityMismatch 1 2)) => m == CtxMsg.call (.resolve "F")
     | _ => false) &&
    (match suppliedCells s1 a with
     | some [x, y] => suspendedAt s1 x && suspendedAt s1 y
     | _ => false)
  | none => false
#guard wrongArityError

/-! ## META twice, VALUE, META, then two explicit invocations -/

def valueThenInvokeTwice : Bool :=
  match start (supplyNeed (callF (.num 41)) ctx []) with
  | some (a, s0) =>
    let (r1, s1) := run (reifyNeedCall a) s0
    let (r2, s2) := run (reifyNeedCall a) s1
    let (v, s3) := run (demandNeed a) s2
    let (r3, s4) := run (reifyNeedCall a) s3
    let (i1, s5) := run (invokeNeedCall ⟨a⟩) s4
    let (i2, s6) := run (invokeNeedCall ⟨a⟩) s5
    let (v2, s7) := run (demandNeed a) s6
    -- META twice: same plan, and the WHOLE production state is unchanged (no target, no
    -- argument demand, no preparation, no binding context).
    refOk r1 a && refOk r2 a && reprStr s2 == reprStr s0 && unpreparedAt s2 a &&
    -- VALUE prepared the plan once; META afterwards still reifies the original plan.
    valueIs v 42 && refOk r3 a && reprStr s4 == reprStr s3 &&
    -- Both invocations run the target afresh over the one prepared argument cell.
    valueIs i1 42 && valueIs i2 42 &&
    s5.needs.size == s4.needs.size && s6.needs.size == s4.needs.size &&
    suppliedCells s6 a == suppliedCells s3 a &&
    (match suppliedCells s6 a with
     | some [b] => completedAt s6 b && b != a
     | _ => false) &&
    -- Fresh executions: each opens a new binding context.
    s5.nextBindingContext > s4.nextBindingContext && s6.nextBindingContext > s5.nextBindingContext &&
    -- The original VALUE stays memoized: the read changes nothing.
    valueIs v2 42 && reprStr s7 == reprStr s6
  | none => false
#guard valueThenInvokeTwice

/-! ## META, invocation, then VALUE: one supply, the original VALUE still computed once -/

def metaInvokeThenValue : Bool :=
  match start (supplyNeed (callF (.num 41)) ctx []) with
  | some (a, s0) =>
    let (r, s1) := run (reifyNeedCall a) s0
    let (i, s2) := run (invokeNeedCall r.toOption.get!) s1
    let stillSuspended := suspendedAt s2 a
    let cells := suppliedCells s2 a
    let (v, s3) := run (demandNeed a) s2
    refOk r a && valueIs i 42 && stillSuspended && valueIs v 42 && completedAt s3 a &&
    s3.needs.size == s2.needs.size && suppliedCells s3 a == cells && cells.isSome &&
    -- The supplied argument was demanded once (by the invocation) and is reused by VALUE.
    (match cells with
     | some [b] => completedAt s2 b
     | _ => false)
  | none => false
#guard metaInvokeThenValue

/-! ## Arbitrary spread: inert META, one preparation, sticky success and failure -/

def spreadOnce : Bool :=
  match start (supplyNeed (.call (.resolve "Add2") [.sequenceSpread (.call (.resolve "Pair") [])]) ctx []) with
  | some (a, s0) =>
    let (r, s1) := run (reifyNeedCall a) s0
    let (i1, s2) := run (invokeNeedCall ⟨a⟩) s1
    let (i2, s3) := run (invokeNeedCall ⟨a⟩) s2
    let (v, s4) := run (demandNeed a) s3
    refOk r a && reprStr s1 == reprStr s0 &&                          -- capture opened nothing
    s2.needs.size == s0.needs.size + 2 &&                              -- one spread: two Ready cells
    s3.needs.size == s2.needs.size && s4.needs.size == s2.needs.size &&
    valueIs i1 3 && valueIs i2 3 && valueIs v 3 &&
    (match suppliedCells s4 a with | some cells => cells.length == 2 | none => false)
  | none => false
#guard spreadOnce

def failingSpreadIsSticky : Bool :=
  match start (supplyNeed (.call (.resolve "Add2") [.sequenceSpread (.call (.resolve "BadPair") [])]) ctx []) with
  | some (a, s0) =>
    let (r, s1) := run (reifyNeedCall a) s0
    let (v, s2) := run (demandNeed a) s1
    let (i, s3) := run (invokeNeedCall ⟨a⟩) s2
    let (v2, s4) := run (demandNeed a) s3
    let (r2, s5) := run (reifyNeedCall a) s4
    refOk r a && reprStr s1 == reprStr s0 &&
    failsAs v .divByZero && preparationFailed s2 a &&
    -- The invocation reuses the failed preparation: no second spread, no new cell.
    failsAs i .divByZero && s3.needs.size == s2.needs.size && planRecords s3 == planRecords s2 &&
    s3.nextBindingContext == s2.nextBindingContext &&    -- `BadPair()` was not called again
    reprStr v2 == reprStr v && reprStr s4 == reprStr s3 &&
    refOk r2 a && reprStr s5 == reprStr s4
  | none => false
#guard failingSpreadIsSticky

/-! ## Zero-demand callee with a failing argument; wrong cardinality before any demand -/

def unusedFailingArgument : Bool :=
  match start (supplyNeed (.call (.resolve "Keep") [.num 7, bad]) ctx []) with
  | some (a, s0) =>
    let (r, s1) := run (reifyNeedCall a) s0
    let (i, s2) := run (invokeNeedCall ⟨a⟩) s1
    let (v, s3) := run (demandNeed a) s2
    refOk r a && valueIs i 7 && valueIs v 7 &&
    (match suppliedCells s3 a with
     | some [_, unused] => suspendedAt s3 unused
     | _ => false)
  | none => false
#guard unusedFailingArgument

def arityBeforeDemand : Bool :=
  match start (supplyNeed (.call (.resolve "F") [bad, .num 2]) ctx []) with
  | some (a, s0) =>
    let (r, s1) := run (reifyNeedCall a) s0
    let (i, s2) := run (invokeNeedCall ⟨a⟩) s1
    let (v, s3) := run (demandNeed a) s2
    refOk r a && failsAs i (.arityMismatch 1 2) && failsAs v (.arityMismatch 1 2) && reprStr i == reprStr v &&
    (match suppliedCells s3 a with
     | some [x, y] => suspendedAt s3 x && suspendedAt s3 y
     | _ => false)
  | none => false
#guard arityBeforeDemand

/-! ## Failing VALUE, then META: sticky failure, stable plan, continued observation -/

def failingValueThenMeta : Bool :=
  match start (supplyNeed (.call (.resolve "Bad") [.num 1]) ctx []) with
  | some (a, s0) =>
    let (v1, s1) := run (demandNeed a) s0
    let (r, s2) := run (reifyNeedCall a) s1
    let (v2, s3) := run (demandNeed a) s2
    let (i, s4) := run (invokeNeedCall ⟨a⟩) s3
    let (v3, s5) := run (demandNeed a) s4
    failsAs v1 .divByZero && refOk r a && reprStr s2 == reprStr s1 &&
    reprStr v2 == reprStr v1 && reprStr s3 == reprStr s1 &&
    -- The invocation fails afresh (a fresh target execution), without touching the VALUE.
    failsAs i .divByZero && reprStr v3 == reprStr v1 && completedAt s5 a &&
    suppliedCells s5 a == suppliedCells s1 a
  | none => false
#guard failingValueThenMeta

/-- A recoverable ordinary VALUE failure does not end the observing computation: inside ONE
    production `EvalM` run, the failure is caught (`evalAttempt`) and META continues. -/
def recoveredFailureThenMeta : Bool :=
  match start (supplyNeed (.call (.resolve "Bad") [.num 1]) ctx []) with
  | some (a, s0) =>
    let observe : EvalM (Except Error CountedResult × NeedPlan.CallReference) := do
      let v ← evalAttempt (demandNeed a)
      let r ← reifyNeedCall a
      pure (v, r)
    match run observe s0 with
    | (.ok (v, r), s1) => failsAs v .divByZero && r.plan == a && completedAt s1 a
    | _ => false
  | none => false
#guard recoveredFailureThenMeta

/-! ## Forwarding through two hops of the production binder, after VALUE, into a scope that
    shadows the callee -/

def forwardedSetup : EvalM (Nat × Nat × Nat) := do
  let a ← supplyNeed (callF (.num 41)) ctx []
  let channels : NeedChannels := ⟨demandNeed, projectNeedCallable⟩
  let some b1 ← bindNeedPatterns channels [.bind "x"] [a] | throw Error.badArity
  let ctx1 ← needBindingContext otherCtx b1
  let hop1 ← supplyNeed (.param "x") ctx1 []
  let some b2 ← bindNeedPatterns channels [.bind "y"] [hop1] | throw Error.badArity
  let ctx2 ← needBindingContext otherCtx b2
  let hop2 ← supplyNeed (.param "y") ctx2 []
  pure (a, hop1, hop2)

def forwardingKeepsThePlan : Bool :=
  match start forwardedSetup with
  | some ((a, hop1, hop2), s0) =>
    let (v, s1) := run (demandNeed a) s0          -- VALUE before the META at the far end
    let (r, s2) := run (reifyNeedCall hop2) s1
    let (i, s3) := run (invokeNeedCall r.toOption.get!) s2
    let (v2, _) := run (demandNeed hop2) s3
    -- Both hops transported the original cell: no new cell was allocated for them.
    hop1 == a && hop2 == a && s0.needs.size == a + 1 &&
    valueIs v 42 && refOk r a &&
    -- The callee is the ORIGINAL owner's F (41 + 1), not the forwarding scope's (41 * 100).
    valueIs i 42 && valueIs v2 42 && suppliedCells s3 a == suppliedCells s1 a
  | none => false
#guard forwardingKeepsThePlan

/-- Forwarding before VALUE: the far end's VALUE demand completes the ORIGINAL cell. -/
def forwardedValueCompletesOriginal : Bool :=
  match start forwardedSetup with
  | some ((a, _, hop2), s0) =>
    let (v, s1) := run (demandNeed hop2) s0
    valueIs v 42 && completedAt s1 a && (suppliedCells s1 a).isSome
  | none => false
#guard forwardedValueCompletesOriginal

/-- Both forwarding hops happen AFTER the original VALUE completed. Binding into a receiver
    with another `F` still transports the completed cell and its original plan unchanged. -/
def forwardingAfterCompletion : Bool :=
  match start (do
    let a ← supplyNeed (callF (.num 41)) ctx []
    let value ← demandNeed a
    let channels : NeedChannels := ⟨demandNeed, projectNeedCallable⟩
    let some b1 ← bindNeedPatterns channels [.bind "x"] [a] | throw Error.badArity
    let c1 ← needBindingContext otherCtx b1
    let h1 ← supplyNeed (.param "x") c1 []
    let some b2 ← bindNeedPatterns channels [.bind "y"] [h1] | throw Error.badArity
    let c2 ← needBindingContext otherCtx b2
    let h2 ← supplyNeed (.param "y") c2 []
    pure (a, h1, h2, value)) with
  | some ((a, h1, h2, value), s0) =>
    let (r, s1) := run (reifyNeedCall h2) s0
    let (i, s2) := run (invokeNeedCall ⟨h2⟩) s1
    let (v, s3) := run (demandNeed h2) s2
    h1 == a && h2 == a && valueIs (.ok value) 42 &&
    refOk r a && reprStr s1 == reprStr s0 && valueIs i 42 && valueIs v 42 &&
    s0.needs.size == 2 && s2.needs.size == s0.needs.size &&
    suppliedCells s2 a == suppliedCells s0 a && reprStr s3 == reprStr s2
  | none => false
#guard forwardingAfterCompletion

/-! ## Parameter callees use the original caller's independent CALLABLE projection -/

def parameterCalleeUsesThePlan : Bool :=
  match start (do
    let f ← supplyNeed (.resolve "F") ctx []
    let caller : EvalCtx := { ctx with needEnv := [("f", f)] }
    let a ← supplyNeed (.call (.param "f") [.num 41]) caller []
    pure (f, a)) with
  | some ((f, a), s0) =>
    let (r, s1) := run (reifyNeedCall a) s0
    let ordinary := run (ordinaryCompletion a) s0
    let (v, s2) := run (demandNeed a) s1
    let (i, s3) := run (invokeNeedCall ⟨a⟩) s2
    refOk r a && reprStr s1 == reprStr s0 &&
    valueIs v 42 && valueIs i 42 && suspendedAt s3 f &&
    (suppliedCells s2 a).isSome && suppliedCells s3 a == suppliedCells s2 a &&
    reprStr v == reprStr ordinary.1 && reprStr (erasePlan a s2) == reprStr ordinary.2
  | none => false
#guard parameterCalleeUsesThePlan

/-- A call-shaped cell demanding itself still goes through the one cycle/completion shell.
    Its ordinary failure remains sticky and META can observe the plan after it. -/
def callShapedCycleIsSticky : Bool :=
  match start (supplyNeed (.call (.resolve "Id") [.param "x"])
      { ctx with needEnv := [("x", 0)] } []) with
  | some (a, s0) =>
    let (v, s1) := run (demandNeed a) s0
    let (r, s2) := run (reifyNeedCall a) s1
    let (v2, s3) := run (demandNeed a) s2
    a == 0 &&
    (match v with
     | .error (.withContext m .demandCycle) => m == CtxMsg.call (.resolve "Id")
     | _ => false) &&
    suppliedCells s1 a == some [a] && completedAt s1 a && refOk r a &&
    reprStr v2 == reprStr v && reprStr s2 == reprStr s1 && reprStr s3 == reprStr s2 &&
    reprStr v == reprStr (run (ordinaryCompletion a) s0).1
  | none => false
#guard callShapedCycleIsSticky

/-! ## A negative witness for the conditional simulation's proof boundary -/

/-- `Oblivious a m` quantifies over ALL heaps, including a suspended `a`. Production dispatch
    can demand `a`, so changing its plan record to `preparing` changes success to a cycle.
    The fresh-plan theorem's abstract non-vacuity witness therefore does not discharge its
    production obligations. Ordinary VALUE's narrower evaluating-cell invariant is still open. -/
def dispatchIsNotGloballyOblivious : Bool :=
  match start (supplyNeed (callF (.num 41)) ctx []) with
  | some (a, s0) =>
    let id := alg ["x"] [] [] [.param "x"]
    let m := evalSuppliedCallCounted id [(a, none)] ctx [] "Id"
    let ordinary := run m s0
    let changed := run m (withPlan a .preparing s0)
    valueIs ordinary.1 42 &&
    (match changed.1 with
     | .error (.withContext msg .demandCycle) => msg == CtxMsg.call (.resolve "F")
     | _ => false)
  | none => false
#guard dispatchIsNotGloballyOblivious

/-! ## Observation order on the same source cell: both orders reach the same state -/

def ordersAgree (source : Expr) : Bool :=
  match start (supplyNeed source ctx []) with
  | some (a, s0) =>
    let (rm, sm) := run (reifyNeedCall a) s0
    let (vm, tm) := run (demandNeed a) sm
    let (vv, tv) := run (demandNeed a) s0
    let (rv, sv) := run (reifyNeedCall a) tv
    refOk rm a && refOk rv a && reprStr vm == reprStr vv && reprStr tm == reprStr sv
  | none => false

#guard ordersAgree (.call (.resolve "Add2") [.sequenceSpread (.call (.resolve "Pair") [])])
#guard ordersAgree (.call (.resolve "Bad") [.num 1])   -- the failing order, observed after failure

/-! ## Distinct dynamic occurrences; deliberate transport of one existing cell or slice -/

def distinctOccurrences : Bool :=
  match start (do
    let a ← supplyNeed (callF (callF (.num 1))) ctx []
    let b ← supplyNeed (callF (callF (.num 1))) ctx []
    pure (a, b)) with
  | some ((a, b), s0) =>
    let (_, s1) := run (invokeNeedCall ⟨a⟩) s0
    let (_, s2) := run (invokeNeedCall ⟨b⟩) s1
    a != b &&
    (match suppliedCells s2 a, suppliedCells s2 b with
     | some [x], some [y] => x != y
     | _, _ => false)
  | none => false
#guard distinctOccurrences

def transportedCellIsShared : Bool :=
  match start (do
    let c ← supplyNeed (.num 5) ctx []
    let shared : EvalCtx := { ctx with needEnv := [("x", c)] }
    let a ← supplyNeed (callF (.param "x")) shared []
    let b ← supplyNeed (callF (.param "x")) shared []
    pure (c, a, b)) with
  | some ((c, a, b), s0) =>
    let (i, s1) := run (invokeNeedCall ⟨a⟩) s0
    let (j, s2) := run (demandNeed b) s1
    a != b && valueIs i 6 && valueIs j 6 &&
    suppliedCells s2 a == some [c] && suppliedCells s2 b == some [c] && completedAt s2 c
  | none => false
#guard transportedCellIsShared

/-- A collector slice spread onward is transported (the same cells), while two independent
    written supplies allocate new cells. -/
def collectorSliceTransport : Bool :=
  match start (do
    let c1 ← supplyNeed (.num 1) ctx []
    let c2 ← supplyNeed (.num 2) ctx []
    let k ← allocateNeed (.collector [c1, c2])
    let shared : EvalCtx := { ctx with needEnv := [("xs", k)] }
    let a ← supplyNeed (.call (.resolve "Add2") [.sequenceSpread (.param "xs")]) shared []
    let b ← supplyNeed (.call (.resolve "Add2") [.sequenceSpread (.param "xs")]) shared []
    let x ← supplyNeed (.call (.resolve "Add2") [.num 1, .num 2]) ctx []
    let y ← supplyNeed (.call (.resolve "Add2") [.num 1, .num 2]) ctx []
    pure (c1, c2, a, b, x, y)) with
  | some ((c1, c2, a, b, x, y), s0) =>
    let (va, s1) := run (demandNeed a) s0
    let (vb, s2) := run (demandNeed b) s1
    let (vx, s3) := run (demandNeed x) s2
    let (vy, s4) := run (demandNeed y) s3
    valueIs va 3 && valueIs vb 3 && valueIs vx 3 && valueIs vy 3 &&
    suppliedCells s4 a == some [c1, c2] && suppliedCells s4 b == some [c1, c2] &&
    (match suppliedCells s4 x, suppliedCells s4 y with
     | some xs, some ys => xs.length == 2 && ys.length == 2 && xs.all (fun p => !ys.contains p) &&
         xs.all (fun p => p != c1 && p != c2)
     | _, _ => false)
  | none => false
#guard collectorSliceTransport

/-! ## Conditional family: ordinary dispatch and demand over the plan's supply -/

def familyDispatch : Bool :=
  match start (do
    let z ← supplyNeed (.call (.resolve "Sign") [.num 0]) ctx []
    let n ← supplyNeed (.call (.resolve "Sign") [.num 5]) ctx []
    pure (z, n)) with
  | some ((z, n), s0) =>
    let (vz, s1) := run (demandNeed z) s0
    let (vn, s2) := run (demandNeed n) s1
    let (iz, s3) := run (invokeNeedCall ⟨z⟩) s2
    valueIs vz 0 && valueIs vn 1 && valueIs iz 0 &&
    -- The inspecting first branch demanded each supplied argument once, through its cell.
    (match suppliedCells s3 z, suppliedCells s3 n with
     | some [p], some [q] => completedAt s3 p && completedAt s3 q
     | _, _ => false) &&
    s3.needs.size == s2.needs.size
  | none => false
#guard familyDispatch

/-! ## Nested call inside a user body: the recursive edge consults authoritative plan state

`G(v) = Id(F(v))`. Demanding `G(41)` evaluates G's body, which supplies the nested call `F(v)` to
`Id` as a NEW cell; `Id`'s parameter read demands that cell through `demandNeedRecursive`. That
nested demand executed the nested cell's own plan: its preparation is recorded in the production
heap (M1 limitation closed), and META/invocation of the nested cell reuse it. -/

def nestedCallUsesThePlan : Bool :=
  match start (supplyNeed (.call (.resolve "G") [.num 41]) ctx []) with
  | some (g, s0) =>
    let (v, s1) := run (demandNeed g) s0
    match callCellsTo s1 "F" with
    | [inner] =>
      let preparedByNestedDemand := suppliedCells s1 inner
      let (r, s2) := run (reifyNeedCall inner) s1
      let (i, s3) := run (invokeNeedCall ⟨inner⟩) s2
      valueIs v 42 && completedAt s1 inner &&
      -- The nested demand prepared the nested plan (one cell: `v`, transported from G's own
      -- parameter cell, so no new argument cell for it).
      (match preparedByNestedDemand, suppliedCells s1 g with
       | some [p], some [q] => p == q
       | _, _ => false) &&
      refOk r inner && valueIs i 42 && suppliedCells s3 inner == preparedByNestedDemand &&
      s3.needs.size == s2.needs.size
    | _ => false
  | none => false
#guard nestedCallUsesThePlan

/-! ## META refuses what is not a supplied call, with no effect -/

def refusals : Bool :=
  match start (do
    let n ← supplyNeed (.num 7) ctx []
    let r ← readyNeed (.atom 7, 1)
    let k ← allocateNeed (.collector [n])
    let d ← supplyNeed (.call (.dotMember (.resolve "Box") "F" (.resolve "F") none) []) ctx []
    let c ← supplyNeed (.call (.num 7) []) ctx []
    let b ← supplyNeed (.call (.algorithmExpr (alg ["x"] [] [] [.param "x"])) [.num 1]) ctx []
    pure (n, r, k, d, c, b)) with
  | some ((n, r, k, d, c, b), s0) =>
    [n, r, k, d, c, b, 99].all fun address =>
      (match run (reifyNeedCall address) s0 with
       | (.error _, s) => reprStr s == reprStr s0
       | (.ok _, _) => false) &&
      (match run (invokeNeedCall ⟨address⟩) s0 with
       | (.error _, s) => reprStr s == reprStr s0
       | (.ok _, _) => false)
  | none => false
#guard refusals

/-- A completed scalar argument cell does not become an invocation, and an unsupported call
    cell stays on the ordinary route (no plan record) after VALUE. -/
def readyAndUnsupportedStayOrdinary : Bool :=
  match start (do
    let n ← supplyNeed (.num 7) ctx []
    let u ← supplyNeed (.call (.algorithmExpr (alg ["x"] [] [] [.param "x"])) [.num 1]) ctx []
    pure (n, u)) with
  | some ((n, u), s0) =>
    let (vn, s1) := run (demandNeed n) s0
    let (vu, s2) := run (demandNeed u) s1
    valueIs vn 7 && valueIs vu 1 &&
    failsAs (run (reifyNeedCall n) s2).1 metaRefusal && failsAs (run (reifyNeedCall u) s2).1 metaRefusal &&
    s2.needs.toList.all (fun c => match c.plan with | .unprepared => true | _ => false)
  | none => false
#guard readyAndUnsupportedStayOrdinary

end KatLang.CallPlanGuards
