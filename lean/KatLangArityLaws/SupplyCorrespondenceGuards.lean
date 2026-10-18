import KatLangArityLaws.SupplyCorrespondence
import KatLangArityLaws.CallReferenceGuards

open KatLang KatLang.SupplyCorrespondence

/-!
# Executable guards for the callback / direct-call binder correspondence (R6, S5)

Witnesses for `KatLangArityLaws/SupplyCorrespondence.lean` on real heaps with the production
channels `⟨demandNeed, projectNeedCallable⟩` (the `partial` projection runs here; it is a premise
of the theorems):

1. the callback prefix (`args.mapM readyNeed`, then `bindNeedPatterns`) from an EMPTY heap and
   from a heap that already holds three cells binds every head of the matrix to corresponding
   outcomes — the same error, both non-matches, or the same names at addresses shifted by
   exactly three (the address table of `ready_supplies_bind_correspondingly`);
2. negative controls for each premise: a wrong emitted COUNT, a wrong structural KIND, a lost
   CALLABLE channel (equal VALUES, different callable projections) and an invalid META
   equivalence (a written call reifies, its Ready result refuses).
Executable checks, not theorems.
-/

namespace KatLang.SupplyCorrespondenceGuards

def channels : NeedChannels := ⟨demandNeed, projectNeedCallable⟩

/-- A heap that already holds three unrelated cells. -/
def prefilled : EvalState :=
  { needs := #[{ suspension := .ready (.atom 9, 1) }, { suspension := .ready (.atom 8, 1) },
      { suspension := .collector [0, 1] }] }

/-- The callback route's binding prefix. -/
def callbackBind (args : List CountedResult) (ps : List NeedPattern) (family : Bool) :
    EvalM (Option NeedEnv) := do
  let cells ← args.mapM readyNeed
  bindNeedPatterns channels ps cells family

def outcome (s : EvalState) (args : List CountedResult) (ps : List NeedPattern) (family : Bool := false) :
    Except Error (Option NeedEnv) :=
  ((callbackBind args ps family).runState s).1

/-- The correspondence of `OptEnvCorr` / `ResCorr` under the table `a ↦ a + offset`. -/
def correspond (r1 r2 : Except Error (Option NeedEnv)) (offset : Nat) : Bool :=
  match r1, r2 with
  | .ok none, .ok none => true
  | .ok (some e1), .ok (some e2) =>
      e1.length == e2.length && (e1.zip e2).all (fun (x, y) => x.1 == y.1 && x.2 + offset == y.2)
  | .error e1, .error e2 => reprStr e1 == reprStr e2
  | _, _ => false

def x : NeedPattern := .bind "x"
def y : NeedPattern := .bind "y"
def rest : NeedPattern := .bind "rest" true

def heads : List (List NeedPattern) :=
  [[], [x], [x, y], [rest], [x, rest], [rest, y], [x, rest, y], [.sequence [x, y]],
   [.list [x, y]], [.sequence [x, rest]], [.list [rest]], [.unpack [x, y]], [x, x],
   [.sequence [x, x]], [x, .sequence [x, y]], [.literal (.litInt 1), y], [.metaRef "op"],
   [.sequence []], [.list []]]

def argSets : List (List CountedResult) :=
  [[], [(.atom 1, 1)], [(.atom 1, 1), (.atom 2, 1)], [(.atom 1, 1), (.atom 1, 1)],
   [(.sequenceValue [.atom 1, .atom 2], 1)], [(.listValue [.atom 1, .atom 2], 1)],
   [(.sequenceValue [.atom 1, .atom 2], 1), (.atom 1, 1)], [(.sequenceValue [], 1)],
   [(.listValue [], 1)], [(.atom 1, 1), (.atom 1, 2)]]

-- 1. The matrix, in both modes: corresponding outcomes from two different heaps.
#guard heads.all fun ps => argSets.all fun args =>
  correspond (outcome EvalState.empty args ps) (outcome prefilled args ps) 3 &&
  correspond (outcome EvalState.empty args ps true) (outcome prefilled args ps true) 3

-- The matrix is not vacuous: it contains successes, non-matches and errors.
#guard heads.any fun ps => argSets.any fun args =>
  match outcome EvalState.empty args ps with | .ok (some (_ :: _)) => true | _ => false
#guard heads.any fun ps => argSets.any fun args =>
  match outcome EvalState.empty args ps true with | .ok none => true | _ => false
#guard heads.any fun ps => argSets.any fun args =>
  match outcome EvalState.empty args ps with | .error _ => true | _ => false

-- 2a. WRONG COUNT: equal displayed values, different emitted counts, are different supplies.
#guard match outcome EvalState.empty [(.atom 1, 1), (.atom 1, 1)] [x, x] with
  | .ok (some _) => true | _ => false
#guard match outcome EvalState.empty [(.atom 1, 1), (.atom 1, 2)] [x, x] with
  | .error (.withContext _ .badArity) => true | _ => false

-- 2b. WRONG STRUCTURAL KIND: a sequence pattern opens a sequence value, not a list value.
#guard match outcome EvalState.empty [(.sequenceValue [.atom 1, .atom 2], 1)] [.sequence [x, y]] with
  | .ok (some _) => true | _ => false
#guard match outcome EvalState.empty [(.listValue [.atom 1, .atom 2], 1)] [.sequence [x, y]] with
  | .error (.typeMismatch _) => true | _ => false

-- 2c. LOST CALLABLE CHANNEL: the same cells and VALUES, two CALLABLE projections that differ on
-- cell 1. `CapCorr.callable` fails between them, and the repeated name retains a different cell.
def withCallable (callableAt : Nat → Option Algorithm) : NeedCapabilities EvalM :=
  ⟨demandNeed, fun a => pure (callableAt a), allocateNeed, NeedPlan.reference⟩

def readyHeap : EvalState :=
  { needs := #[{ suspension := .ready (.atom 5, 1) }, { suspension := .ready (.atom 5, 1) }] }

#guard match ((NeedBinder.bindPatterns (withCallable fun a => if a == 1 then some (.builtin .mapBuiltin) else none)
    [x, x] [0, 1]).runState readyHeap).1,
  ((NeedBinder.bindPatterns (withCallable fun _ => none) [x, x] [0, 1]).runState readyHeap).1 with
  | .ok (some e1), .ok (some e2) => lookupAssoc "x" e1 == some 1 && lookupAssoc "x" e2 == some 0
  | _, _ => false

-- 2d. INVALID META EQUIVALENCE: a supplied written call reifies (`Capture(Sq(5)).Invoke()` is
-- 25), while a callback element is Ready data and the same `meta` capture refuses it.
#guard CallReferenceGuards.valueIs (runResult (CallReferenceGuards.program []
  [CallReferenceGuards.invoke (CallReferenceGuards.call "Capture" [CallReferenceGuards.call "Sq" [.num 5]])]))
  (.atom 25)
#guard CallReferenceGuards.isMetaRefusal (runResult (CallReferenceGuards.program []
  [.call (resolve "map") [.listLiteral [CallReferenceGuards.call "Sq" [.num 5]], resolve "Capture"]]))
-- At the binder: a Ready cell's META capture is the structured refusal, in either mode.
#guard match outcome EvalState.empty [(.atom 25, 1)] [.metaRef "op"],
             outcome EvalState.empty [(.atom 25, 1)] [.metaRef "op"] true with
  | .error (.notAnAlgorithm _), .error (.notAnAlgorithm _) => true
  | _, _ => false

end KatLang.SupplyCorrespondenceGuards
