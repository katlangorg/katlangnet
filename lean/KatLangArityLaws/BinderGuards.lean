import KatLangArityLaws.FamilyDispatch

open KatLang KatLang.BinderTrace KatLang.FamilyDispatch

/-!
# Executable guards for the R3 binder trace (finite evidence, never theorems)

These `#guard`s run THE production binder — the generic core using the public channels
`⟨demandNeed, projectNeedCallable⟩` with `allocateNeed` — in the trace interpretation, over real
need heaps (ready cells, suspended expressions that fail, completed cells), and over a few
stateful synthetic channel records where a production heap cannot produce the situation (a
representative whose re-demand fails, a failing CALLABLE projection, two distinct callable
identities with equal values, an effect counter). They pin the concrete event schedules the
theorems of `KatLangArityLaws.BinderTrace` and `KatLangArityLaws.FamilyDispatch` characterize,
including allocation events and their addresses. A guard is a finite witness: the universal
statements are the theorems. Since R5, public `demandNeed` is a total one-step specialization
of `NeedDemand.step`; evaluator binding sites pass the partial `demandNeedRecursive` driver,
which invokes the same shell. Their recursive connection remains source/guard evidence.
-/

namespace KatLang.BinderGuards

/-- Public demand/projection channels used by these guards; evaluator binding sites use
    `demandNeedRecursive` as their VALUE channel. -/
def productionChannels : NeedChannels := ⟨demandNeed, projectNeedCallable⟩

/-- The production capabilities of the binder core. -/
def production : NeedCapabilities EvalM := productionChannels.capabilities

def readyCell (value : Result) : NeedCell := { suspension := .ready (value, Result.valueCount value) }
def failingCell : NeedCell := { suspension := .expression (.binary .div (.num 1) (.num 0)) EvalCtx.empty [] }
def expressionCell (expr : Expr) : NeedCell := { suspension := .expression expr EvalCtx.empty [] }
def heap (cells : List NeedCell) : EvalState := { needs := cells.toArray }
def readyHeap (values : List Result) : EvalState := heap (values.map readyCell)

def run (k : NeedCapabilities EvalM) (patterns : List NeedPattern) (cells : List Nat) (s : EvalState)
    (family : Bool := false) : Except Error (Option NeedEnv) × TraceState :=
  runTrace (NeedBinder.bindPatterns (traced k) patterns cells family) ⟨s, []⟩

def isOkSome : Except Error (Option NeedEnv) → Bool
  | .ok (some _) => true
  | _ => false
def isOkNone : Except Error (Option NeedEnv) → Bool
  | .ok none => true
  | _ => false
def bindingIs (expected : NeedEnv) : Except Error (Option NeedEnv) → Bool
  | .ok (some env) => env == expected
  | _ => false
def isDivByZero {α : Type} : Except Error α → Bool
  | .error .divByZero => true
  | _ => false
def isArity {α : Type} (expected actual : Nat) : Except Error α → Bool
  | .error (.arityMismatch e a) => e == expected && a == actual
  | _ => false
def isRepeatedBadArity {α : Type} : Except Error α → Bool
  | .error (.withContext _ .badArity) => true
  | _ => false
def isTypeMismatch {α : Type} : Except Error α → Bool
  | .error (.typeMismatch _) => true
  | _ => false
def isIllegal {α : Type} : Except Error α → Bool
  | .error (.illegalInEval _) => true
  | _ => false
def isDemandCycle {α : Type} : Except Error α → Bool
  | .error .demandCycle => true
  | _ => false
def isNoMatch {α : Type} : Except Error α → Bool
  | .error (.noMatchingBranch _) => true
  | _ => false
def isDuplicate {α : Type} : Except Error α → Bool
  | .error .duplicateBranchPattern => true
  | _ => false
def suspendedAt (s : EvalState) (address : Nat) : Bool :=
  match s.needs[address]?.map (·.state) with
  | some NeedState.suspended => true
  | _ => false
def completedAt (s : EvalState) (address : Nat) : Bool :=
  match s.needs[address]?.map (·.state) with
  | some (NeedState.completed _) => true
  | _ => false

/-! ## The adapted Option B′ guards (now with allocation events) -/

-- 1. All plain: no event, the failing cell is never demanded.
#guard let out := run production [.bind "a", .bind "b"] [0, 1] (heap [failingCell, readyCell (.atom 2)])
  isOkSome out.1 && out.2.events == [] && suspendedAt out.2.semantic 0
-- 2. An inspection after a plain occurrence demands only its own cell.
#guard (run production [.bind "a", .literal (.litInt 2)] [0, 1] (readyHeap [.atom 9, .atom 2])).2.events
  == [.value 1]
-- 3. A literal non-match ends a family attempt after its one VALUE event.
#guard let out := run production [.literal (.litInt 0), .literal (.litInt 2)] [0, 1] (readyHeap [.atom 1, .atom 2]) true
  isOkNone out.1 && out.2.events == [.value 0]
-- 4. A real demand failure is final: no later sibling.
#guard let out := run production [.literal (.litInt 0), .literal (.litInt 2)] [0, 1] (heap [failingCell, readyCell (.atom 2)]) true
  isDivByZero out.1 && out.2.events == [.value 0]
-- 5. Repeated equality: VALUE current, VALUE representative, CALLABLE representative, CALLABLE current.
#guard (run production [.bind "x", .bind "x"] [0, 1] (readyHeap [.atom 1, .atom 1])).2.events
  == [.value 0, .value 1, .value 0, .callable 0, .callable 1]
-- 6. Repeated inequality: no projection, no later sibling.
#guard let out := (run production [.bind "x", .bind "x", .literal (.litInt 2)] [0, 1, 2]
    (readyHeap [.atom 1, .atom 9, .atom 2]) true)
  isOkNone out.1 && out.2.events == [.value 0, .value 1, .value 0]
-- 7. Two nested list levels before the sibling, depth first, with their ready allocations.
#guard (run production [.list [.list [.literal (.litInt 1)], .literal (.litInt 2)], .literal (.litInt 3)] [0, 1]
    (readyHeap [.listValue [.listValue [.atom 1], .atom 2], .atom 3])).2.events
  == [.value 0, .ready 2, .ready 3, .value 2, .ready 4, .value 4, .value 3, .value 1]
-- 8. Pre-inspection count rejection: nothing at all.
#guard let out := run production [.literal (.litInt 0), .literal (.litInt 2)] [0] (heap [failingCell]) true
  isOkNone out.1 && out.2.events == [] && out.2.semantic.needs.size == 1
-- 9. Ready allocation BEFORE the nested count rejection, and the cells stay.
#guard let out := run production [.list [.bind "x"]] [0] (readyHeap [.listValue [.atom 1, .atom 2]])
  isArity 1 2 out.1 && out.2.events == [.value 0, .ready 1, .ready 2] && out.2.semantic.needs.size == 3
-- 10. A collector allocates one fresh cell over its slice and demands nothing.
#guard let out := run production [.bind "xs" true] [0, 1] (heap [failingCell, readyCell (.atom 2)])
  bindingIs [("xs", 2)] out.1 && out.2.events == [.collector 2 [0, 1]] && out.2.semantic.needs.size == 3
    && suspendedAt out.2.semantic 0

/-! ## Aliasing, depth, collectors around fixed patterns -/

-- An aliased cell: the plain occurrence is silent, the later literal demands the SAME address.
#guard let out := run production [.bind "a", .literal (.litInt 7)] [0, 0] (readyHeap [.atom 7])
  bindingIs [("a", 0)] out.1 && out.2.events == [.value 0]
-- Two VALUE events on one address are two binder invocations (an event counts invocations,
-- not evaluations); the cell ends completed. No guard here counts evaluations: single flight
-- is `demandNeed`'s own law, outside the binder boundary.
#guard let out := (run production [.literal (.litInt 7), .literal (.litInt 7)] [0, 0]
    (heap [expressionCell (.binary .add (.num 3) (.num 4))]))
  isOkSome out.1 && out.2.events == [.value 0, .value 0] && completedAt out.2.semantic 0
-- A repeated name over one aliased failing cell: the first demand fails, nothing follows.
#guard let out := run production [.bind "x", .bind "x"] [0, 0] (heap [failingCell])
  isDivByZero out.1 && out.2.events == [.value 0]
-- Three nested list levels, each opened after its parent's demand and allocation.
#guard let out := (run production [.list [.list [.list [.literal (.litInt 5)]]]] [0]
    (readyHeap [.listValue [.listValue [.listValue [.atom 5]]]]))
  isOkSome out.1 && out.2.events == [.value 0, .ready 1, .value 1, .ready 2, .value 2, .ready 3, .value 3]
-- A collector between two fixed patterns: one collector allocation over the middle slice, no demand.
#guard let out := run production [.bind "a", .bind "xs" true, .bind "z"] [0, 1, 2, 3] (readyHeap [.atom 0, .atom 1, .atom 2, .atom 3])
  bindingIs [("a", 0), ("xs", 4), ("z", 3)] out.1 && out.2.events == [.collector 4 [1, 2]]
-- A collector before an inspecting literal: the allocation comes first, then the literal's demand.
#guard let out := run production [.bind "xs" true, .literal (.litInt 9)] [0, 1, 2] (readyHeap [.atom 1, .atom 2, .atom 9])
  bindingIs [("xs", 3)] out.1 && out.2.events == [.collector 3 [0, 1], .value 2]

-- A sequence pattern never opens a list: one VALUE event, then the kind error (ordinary mode) or
-- the non-match (family), with no allocation.
#guard let out := run production [.sequence [.bind "a", .bind "b"]] [0] (readyHeap [.listValue [.atom 1, .atom 2]])
  isTypeMismatch out.1 && out.2.events == [.value 0] && out.2.semantic.needs.size == 1
#guard isOkNone (run production [.sequence [.bind "a", .bind "b"]] [0] (readyHeap [.listValue [.atom 1, .atom 2]]) true).1
-- The unpacking receiver opens one level of any value and binds the fresh ready cells.
#guard let out := run production [.unpack [.bind "x", .bind "y"]] [0] (readyHeap [.sequenceValue [.atom 1, .atom 2]])
  bindingIs [("x", 1), ("y", 2)] out.1 && out.2.events == [.value 0, .ready 1, .ready 2]

/-- Production VALUE/CALLABLE with an allocator that fails once the heap holds three cells. -/
def boundedAllocator : NeedCapabilities EvalM :=
  { production with allocate := fun suspension => do
      if (← get).needs.size ≥ 3 then throw (Error.illegalInEval "heap full")
      allocateNeed suspension }

-- A ready allocation failing partway: the parent's VALUE, the one completed allocation, then the
-- error — no event for the failed allocation, no nested pattern.
#guard let out := run boundedAllocator [.list [.bind "x", .bind "y"]] [1] (readyHeap [.atom 0, .listValue [.atom 1, .atom 2]]) |>.1
  isIllegal out
#guard (run boundedAllocator [.list [.bind "x", .bind "y"]] [1] (readyHeap [.atom 0, .listValue [.atom 1, .atom 2]])).2.events
  == [.value 1, .ready 2]

/-! ## Repeated names: modes, failure points, identities (stateful synthetic channels) -/

-- Ordinary mode, unequal values: the repeated-parameter badArity, after exactly the two VALUE events.
#guard let out := run production [.bind "x", .bind "x"] [0, 1] (readyHeap [.atom 1, .atom 9])
  isRepeatedBadArity out.1 && out.2.events == [.value 0, .value 1, .value 0]
-- The CURRENT occurrence's VALUE fails before any representative or CALLABLE event.
#guard let out := run production [.bind "x", .bind "x"] [0, 1] (heap [readyCell (.atom 1), failingCell])
  isDivByZero out.1 && out.2.events == [.value 0, .value 1]

/-- A channel record whose VALUE demand of cell 0 fails once ANY VALUE demand has succeeded
    (the success counter is `nextRuntimeDeclaration`); every other demand answers `1` and
    counts. CALLABLE: none. -/
def flakyRepresentative : NeedCapabilities EvalM where
  value address := do
    let s <- get
    if address == 0 && s.nextRuntimeDeclaration > 0 then throw Error.demandCycle
    set { s with nextRuntimeDeclaration := s.nextRuntimeDeclaration + 1 }
    pure (.atom 1, 1)
  callable _ := pure none
  allocate := allocateNeed
  reference := NeedPlan.reference

-- The representative's re-demand fails: events end at it, no CALLABLE projection.
#guard let out := run flakyRepresentative [.bind "x", .bind "x"] [0, 1] (heap [])
  isDemandCycle out.1 && out.2.events == [.value 0, .value 1, .value 0]

/-- Equal values; CALLABLE of cell `failAt` raises; cells 2 and 3 carry DIFFERENT builtin
    identities; every other cell has none. -/
def projectionChannels (failAt : Nat) : NeedCapabilities EvalM where
  value _ := pure (.atom 1, 1)
  callable address :=
    if address == failAt then throw (Error.illegalInEval "projection failed")
    else if address == 2 then pure (some (.builtin .countBuiltin))
    else if address == 3 then pure (some (.builtin .sumBuiltin))
    else pure none
  allocate := allocateNeed
  reference := NeedPlan.reference

-- The representative's CALLABLE projection fails: the current one is never projected.
#guard let out := run (projectionChannels 0) [.bind "x", .bind "x"] [0, 1] (heap [])
  isIllegal out.1 && out.2.events == [.value 0, .value 1, .value 0, .callable 0]
-- The current occurrence's CALLABLE projection fails last.
#guard let out := run (projectionChannels 1) [.bind "x", .bind "x"] [0, 1] (heap [])
  isIllegal out.1 && out.2.events == [.value 0, .value 1, .value 0, .callable 0, .callable 1]
-- Incompatible identities: the type error in ordinary mode, the non-match in a family.
#guard let out := run (projectionChannels 99) [.bind "x", .bind "x"] [2, 3] (heap [])
  isTypeMismatch out.1 && out.2.events == [.value 2, .value 3, .value 2, .callable 2, .callable 3]
#guard isOkNone (run (projectionChannels 99) [.bind "x", .bind "x"] [2, 3] (heap []) true).1
-- A richer later contribution replaces the representative; an equally rich one keeps it.
#guard bindingIs [("x", 2)] (run (projectionChannels 99) [.bind "x", .bind "x"] [0, 2] (heap [])).1
#guard bindingIs [("x", 2)] (run (projectionChannels 99) [.bind "x", .bind "x"] [2, 0] (heap [])).1
#guard bindingIs [("x", 0)] (run (projectionChannels 99) [.bind "x", .bind "x"] [0, 1] (heap [])).1

/-! ## Families: precedence, retained effects, activation under a nonempty context -/

def literalFamily : Algorithm := .conditional none []
  [{ pattern := .litInt 0, body := Algorithm.ofExpr (.num 10) },
   { pattern := .litInt 1, body := Algorithm.ofExpr (.num 20) }] none

def runFamily (k : NeedCapabilities EvalM) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx)
    (env : ValEnv) (s : EvalState) :=
  runTrace (NeedBinder.selectFamily (traced k) callee cells "F"
    (tracedActivation (needActivateBranch callee ctx env))) ⟨s, []⟩

-- Retry over the same cell, activation of the second clause only.
#guard let out := runFamily production literalFamily [0] EvalCtx.empty [] (readyHeap [.atom 1])
  out.1.toOption.isSome && out.2.events == [.value 0, .value 0]
    && out.2.semantic.nextBindingContext == 2 && out.2.semantic.lexicalActivations.size == 1
-- A raised failure in the first attempt aborts the search.
#guard let out := runFamily production literalFamily [0] EvalCtx.empty [] (heap [failingCell])
  isDivByZero out.1 && out.2.events == [.value 0] && out.2.semantic.lexicalActivations.size == 0
-- The family count check precedes every attempt.
#guard let out := runFamily production literalFamily [] EvalCtx.empty [] (heap [failingCell])
  isArity 1 0 out.1 && out.2.events == []
-- Exhaustion after every attempt.
#guard let out := runFamily production literalFamily [0] EvalCtx.empty [] (readyHeap [.atom 2])
  isNoMatch out.1 && out.2.events == [.value 0, .value 0]
-- The duplicate-clause check precedes even the count check.
def duplicateFamily : Algorithm := .conditional none []
  [{ pattern := .litInt 0, body := Algorithm.ofExpr (.num 10) },
   { pattern := .litInt 0, body := Algorithm.ofExpr (.num 20) }] none
#guard let out := runFamily production duplicateFamily [] EvalCtx.empty [] (heap [])
  isDuplicate out.1 && out.2.events == []

-- Every attempt binds the SAME original cells, in their original order: over the two-cell supply
-- `(1, 2)`, `F(0, n)` mismatches on its first cell and `F(a, 2)` then matches with `a` = cell 0 and
-- its literal on cell 1 (a re-formed or reordered supply would bind `a` to cell 1 and mismatch).
def pairFamily : Algorithm := .conditional none []
  [{ pattern := .sequenceValue [.litInt 0, .bind "n"], body := Algorithm.ofExpr (.num 10) },
   { pattern := .sequenceValue [.bind "a", .litInt 2], body := Algorithm.ofExpr (.param "a") }] none
#guard let out := runFamily production pairFamily [0, 1] EvalCtx.empty [] (readyHeap [.atom 1, .atom 2])
  match out.1 with
  | .ok (_, next, _) => next.needEnv == [("a", 0)] && out.2.events == [.value 0, .value 1]
  | .error _ => false

/-- A VALUE channel that counts its invocations in `nextRuntimeDeclaration` and answers `1`. -/
def countingValue : NeedCapabilities EvalM where
  value _ := do
    modify fun s => { s with nextRuntimeDeclaration := s.nextRuntimeDeclaration + 1 }
    pure (.atom 1, 1)
  callable _ := pure none
  allocate := allocateNeed
  reference := NeedPlan.reference

-- A rejected attempt's completed effect is retained: two VALUE invocations, counter 2.
#guard let out := runFamily countingValue literalFamily [0] EvalCtx.empty [] (heap [])
  out.1.toOption.isSome && out.2.semantic.nextRuntimeDeclaration == 2 && out.2.events == [.value 0, .value 0]
-- On a real heap the first attempt completes the cell; the second reads it completed.
#guard let out := runFamily production literalFamily [0] EvalCtx.empty [] (heap [expressionCell (.binary .add (.num 0) (.num 1))])
  out.1.toOption.isSome && completedAt out.2.semantic 0 && out.2.events == [.value 0, .value 0]

def binderFamily : Algorithm := .conditional none []
  [{ pattern := .litInt 0, body := Algorithm.ofExpr (.num 10) },
   { pattern := .bind "n", body := Algorithm.ofExpr (.param "n") }] none
def outerContext : EvalCtx :=
  { callStack := [Algorithm.ofExpr (.num 0)], needEnv := [("n", 7), ("other", 8)], bindingContext := 3 }
def outerValues : ValEnv := [("n", .atom 100), ("w", .atom 5)]

-- Activation under a NONEMPTY context: the bound name shadows the inherited cell and value, other
-- names are kept, the binding context is the fresh counter value, and one activation is recorded.
def activationHeap : EvalState := { (readyHeap [.atom 4]) with nextBindingContext := 41 }
#guard let out := runFamily production binderFamily [0] outerContext outerValues activationHeap
  match out.1 with
  | .ok (_, next, values) =>
    next.needEnv == [("n", 0), ("other", 8)] && next.bindingContext == 41
      && next.callStack.length == 2 && values.length == 1
      && out.2.semantic.nextBindingContext == 42 && out.2.semantic.lexicalActivations.size == 1
      && (out.2.semantic.lexicalActivations[0]?.map (·.needs)) == some [("n", 0)]
      && (out.2.semantic.lexicalActivations[0]?.map (·.bindingContext)) == some 41
      && out.2.events == [.value 0]
  | .error _ => false

/-! ## Through the production entry points themselves -/

-- `bindNeedPatterns` surfaces a raised demand failure in both modes (never a non-match).
#guard match (bindNeedPatterns productionChannels [.literal (.litInt 0)] [0] false).run (heap [failingCell]) with
  | .error .divByZero => true
  | _ => false
#guard match (bindNeedPatterns productionChannels [.literal (.litInt 0)] [0] true).run (heap [failingCell]) with
  | .error .divByZero => true
  | _ => false

/-- The counting VALUE channel as production channels. -/
def countingChannels : NeedChannels := ⟨countingValue.value, countingValue.callable⟩

-- `selectNeedFamilyBranch` keeps a rejected attempt's completed effect (no rollback): two VALUE
-- invocations leave the counter at 2, and the second clause is selected.
#guard match (selectNeedFamilyBranch countingChannels literalFamily [0] EvalCtx.empty [] "F").runState (heap []) with
  | (.ok _, s) => s.nextRuntimeDeclaration == 2
  | _ => false
-- … and attempts the second clause on the SAME cells (the two-cell family).
#guard match (selectNeedFamilyBranch productionChannels pairFamily [0, 1] EvalCtx.empty [] "F").run
    (readyHeap [.atom 1, .atom 2]) with
  | .ok ((_, next, _), _) => next.needEnv == [("a", 0)]
  | _ => false

/-! ## Erasure, on concrete runs (the theorem is `trace_erasure`) -/

def erasesExactly (k : NeedCapabilities EvalM) (patterns : List NeedPattern) (cells : List Nat)
    (s : EvalState) (family : Bool) : Bool :=
  reprStr (eraseTrace (NeedBinder.bindPatterns (traced k) patterns cells family) s [.ready 99])
    == reprStr (runEval (NeedBinder.bindPatterns k patterns cells family) s)

#guard erasesExactly production [.list [.list [.literal (.litInt 1)], .literal (.litInt 2)], .literal (.litInt 3)] [0, 1]
  (readyHeap [.listValue [.listValue [.atom 1], .atom 2], .atom 3]) false
#guard erasesExactly production [.bind "x", .bind "x", .literal (.litInt 2)] [0, 1, 2]
  (heap [readyCell (.atom 1), failingCell, readyCell (.atom 2)]) true
#guard erasesExactly production [.list [.bind "x"]] [0] (readyHeap [.listValue [.atom 1, .atom 2]]) false
#guard erasesExactly flakyRepresentative [.bind "x", .bind "x"] [0, 1] (heap []) false

/-! ## Independent review: counted values, nested repetition and hostile capabilities -/

-- Equal semantic values with DIFFERENT emitted counts are incompatible before any CALLABLE.
def differentCounts : NeedCapabilities EvalM :=
  { production with value := fun address => pure (.atom 7, address + 1) }
#guard let out := run differentCounts [.bind "x", .bind "x"] [0, 1] (heap [])
  isRepeatedBadArity out.1 && out.2.events == [.value 0, .value 1, .value 0]

-- Repetition crosses a structural boundary; depth-first inspection retains the nested cell.
#guard let out := (run production [.list [.bind "x"], .bind "x"] [0, 1]
    (readyHeap [.listValue [.atom 7], .atom 7]))
  bindingIs [("x", 2)] out.1
    && out.2.events == [.value 0, .ready 2, .value 2, .value 1, .value 2, .callable 2, .callable 1]

-- Two available, equal callable identities keep the earlier complete contribution.
def equalIdentities : NeedCapabilities EvalM :=
  { production with
    value := fun _ => pure (.atom 7, 1)
    callable := fun _ => pure (some (.builtin .countBuiltin)) }
#guard bindingIs [("x", 0)] (run equalIdentities [.bind "x", .bind "x"] [0, 1] (heap [])).1

-- A channel can mutate semantic state BEFORE raising an incompatibility-shaped error.
-- Both modes must propagate it; family search must stop without retry or activation.
def statefulIncompatibility : NeedCapabilities EvalM :=
  { production with value := fun _ => do
      let _ <- allocateNeed (.ready (.atom 9, 1))
      modify fun s => { s with nextRuntimeDeclaration := s.nextRuntimeDeclaration + 11 }
      throw (Error.arityMismatch 3 4) }
#guard [false, true].all fun family =>
  let out := run statefulIncompatibility [.bind "x", .bind "x"] [0, 1] (heap []) family
  isArity 3 4 out.1 && out.2.events == [.value 0]
    && out.2.semantic.needs.size == 1 && out.2.semantic.nextRuntimeDeclaration == 11
#guard let out := runFamily statefulIncompatibility literalFamily [0] EvalCtx.empty [] (heap [])
  isArity 3 4 out.1 && out.2.events == [.value 0]
    && out.2.semantic.needs.size == 1 && out.2.semantic.nextRuntimeDeclaration == 11
    && out.2.semantic.lexicalActivations.size == 0

-- Failed allocation retains its semantic work but emits no successful-allocation event.
def statefulAllocationFailure : NeedCapabilities EvalM :=
  { production with allocate := fun suspension => do
      let _ <- allocateNeed suspension
      throw (Error.illegalInEval "allocation failed after its effect") }
#guard let out := run statefulAllocationFailure [.bind "xs" true] [0] (heap [failingCell])
  isIllegal out.1 && out.2.events == [] && out.2.semantic.needs.size == 2
    && suspendedAt out.2.semantic 0

-- Arbitrary allocators can reuse even a plain-only supplied address. This is why static
-- noninterference explicitly requires freshness; the production allocator never does this.
#guard let k : NeedCapabilities EvalM := { production with allocate := fun _ => pure 0 }
  let out := (run k [.bind "plain", .list [.literal (.litInt 7)]] [0, 1]
    (readyHeap [.atom 5, .listValue [.atom 7]]))
  isOkNone out.1 && out.2.events == [.value 1, .ready 0, .value 0]

end KatLang.BinderGuards
