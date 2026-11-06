import KatLangArityLaws.CacheReentrancy

open KatLang KatLang.CacheReentrancy KatLang.PropertyInvocationLaws

/-!
# FG-K1 executable evidence: reentrant requests never publish their own key

Beside the kernel theorems of `CacheReentrancy.lean`, two kinds of witness run the production
evaluator.

* **Programs** (§2–§5): whole runs through `runResultM` of hand-written ASTs whose source form each
  comment gives; C# pins the recursive shapes through its front end with the `tock` host operation
  (`OutermostPropertyCachePublicationTests`). `tick()` makes a same-key reentrant read terminate
  with a result different from its owner's, so these separate outer-owner publication from the
  superseded inner-first rule. They read the full counted entries, the owner set and the counter.
* **Scenes** (§1, §6, §7): SYNTHETIC keys and states built by hand, never evidence of front-end
  admissibility.

§8 is the axiom audit.
-/

namespace KatLang.CacheReentrancyGuards

def add (a b : Expr) : Expr := .binary .add a b
def dv (a b : Expr) : Expr := .binary .div a b
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def tickBelow (n : Int) : Expr := .compare .lt (callN "tick" []) (.num n)
def readA : Expr := .resolve "A"
def callA : Expr := callN "A" []
def atoms (values : List Int) : Result := .sequenceValue (values.map Result.atom)

/-- The outcome, the full counted entries (property name, value, count, in publication order), the
    owner-set size and the tick counter of a run. The state is kept on failure too. -/
def run (decls : List (Ident × Algorithm)) (rows : List Expr) :
    Except Error Result × List (Ident × Result × Nat) × Nat × Nat :=
  let (result, state) := (runResultM (.algorithmExpr (algPrivate [] [] decls rows))).runState EvalState.empty
  (result,
   state.zeroArgPropertyCache.map (fun (e : ZeroArgPropertyCacheKey × CountedResult) => (e.1.propertyName, e.2)),
   state.activeZeroArgProperties.length, state.tickCounter)

def okRun (outcome : Except Error Result × List (Ident × Result × Nat) × Nat × Nat) (value : Result)
    (entries : List (Ident × Result × Nat)) (ticks : Nat) : Bool :=
  match outcome with
  | (.ok v, cache, active, n) => v == value && cache == entries && active == 0 && n == ticks
  | _ => false

def innermost : Error → Error
  | .withContext _ inner => innermost inner
  | e => e

def failedRun (outcome : Except Error Result × List (Ident × Result × Nat) × Nat × Nat)
    (entries : List (Ident × Result × Nat)) (ticks : Nat) : Bool :=
  match outcome with
  | (.error e, cache, active, n) =>
      (match innermost e with | .divByZero => true | _ => false)
        && cache == entries && active == 0 && n == ticks
  | _ => false

/-! ## 1. Key equality (synthetic keys) -/

def baseKey : ZeroArgPropertyCacheKey :=
  { accessKind := .lexical, owner := "o", hostOwners := [(1, 2)], componentOwners := [(3, 4)],
    propertyName := "P", propertyAlgorithm := "a", valEnv := some "e", bindingContext := some 1 }

#guard baseKey == { baseKey with owner := "o" }
#guard !(baseKey == { baseKey with accessKind := .structural })
#guard !(baseKey == { baseKey with owner := "p" })
#guard !(baseKey == { baseKey with hostOwners := [(1, 3)] })
#guard !(baseKey == { baseKey with hostOwners := [] })
#guard !(baseKey == { baseKey with componentOwners := [(3, 5)] })
#guard !(baseKey == { baseKey with propertyName := "Q" })
#guard !(baseKey == { baseKey with propertyAlgorithm := "b" })
#guard !(baseKey == { baseKey with valEnv := none })
#guard !(baseKey == { baseKey with bindingContext := some 2 })
#guard !(baseKey == { baseKey with bindingContext := none })

-- The Boolean comparison is propositional equality, and the owner-set test is membership.
example (a b : ZeroArgPropertyCacheKey) (h : (a == b) = true) : a = b := eq_of_beq h
example (a : ZeroArgPropertyCacheKey) : (a == a) = true := beq_self_eq_true a
example (l : List ZeroArgPropertyCacheKey) (a : ZeroArgPropertyCacheKey) (h : a ∈ l) :
    l.contains a = true := (contains_iff_mem l a).2 h

def ownerAlg : Algorithm := alg [] [] [] []
def localP (body : Algorithm) : PropDef := privateLocalProp "P" (.localCapturedAncestorParams ["x"]) body
def body1 : Algorithm := alg [] [] [] [.num 1]
def keyWith (k : ZeroArgPropertyAccessKind) (context : Option Nat) : ZeroArgPropertyCacheKey :=
  zeroArgPropertyCacheKey k ownerAlg (localP body1) EvalCtx.empty [] context

-- The real constructor: the spelling normalizes, the owner context does not.
#guard keyWith .lexical (some 1) == keyWith .structural (some 1)
#guard !(keyWith .lexical (some 1) == keyWith .lexical (some 2))

/-! ## 2. Nested same-key success: the owner wins -/

/-- `A = if(tick() < 3, A + 1, 0)`. -/
def recursiveRead : Algorithm := alg [] [] [] [callN "if" [tickBelow 3, add readA (.num 1), .num 0]]
/-- `A = if(tick() < 3, A() + 1, 0)`. -/
def recursiveInvoke : Algorithm := alg [] [] [] [callN "if" [tickBelow 3, add callA (.num 1), .num 0]]
/-- `A = (if(tick() < 2, [A, 7], [5]))*`: the reentrant result counts ONE output, the owner's two. -/
def recursiveCount : Algorithm :=
  alg [] [] [] [.sequenceSpread (callN "if" [tickBelow 2, .listLiteral [readA, .num 7], .listLiteral [.num 5]])]

-- `A, A`: the reentrant runs return 0 then 1, the owner's 2 is published and reused. The superseded
-- inner-first rule stored the 0: `S[2, 0]`.
#guard okRun (run [("A", recursiveRead)] [readA, readA]) (atoms [2, 2]) [("A", .atom 2, 1)] 3
-- Inner and outer counted results differ in COUNT as well as in value: the entry is the owner's pair.
#guard okRun (run [("A", recursiveCount)] [readA]) (atoms [5, 7]) [("A", atoms [5, 7], 2)] 2

/-! ## 3. Mixed requests share one ownership rule -/

-- Invocation owner, reentrant read.
#guard okRun (run [("A", recursiveRead)] [callA, readA]) (atoms [2, 2]) [("A", .atom 2, 1)] 3
-- Invocation owner, reentrant invocation.
#guard okRun (run [("A", recursiveInvoke)] [callA, readA]) (atoms [2, 2]) [("A", .atom 2, 1)] 3
-- Read owner, reentrant invocation; the later `A()` is fresh (its 0, a fourth tick) and the
-- established 2 stays: an established entry suppresses no invocation and is not replaced by one.
#guard okRun (run [("A", recursiveInvoke)] [readA, readA, callA, readA]) (atoms [2, 2, 0, 2])
  [("A", .atom 2, 1)] 4
-- An invocation owner publishes the property-level pair; its caller's value boundary is a separate
-- recount of the same execution, here from two outputs to one (`user_call_is_its_output_recounted`).
#guard okRun (run [("A", recursiveCount)] [callA, readA]) (.sequenceValue [atoms [5, 7], atoms [5, 7]])
  [("A", atoms [5, 7], 2)] 2
#guard (reCountValueBoundary (atoms [5, 7], 2)).snd == 1

/-! ## 4. A failing owner -/

def seven : Algorithm := alg [] [] [] [add (.num 3) (.num 4)]
/-- `A = if(tick() < 2, Seven + A + 1 / 0, 0)`: the reentrant `A` SUCCEEDS with 0, then the owner fails. -/
def failingOwner (inner : Expr) : Algorithm :=
  alg [] [] [] [callN "if" [tickBelow 2, add (add (.resolve "Seven") inner) (dv (.num 1) (.num 0)), .num 0]]

-- Through a read and through an invocation, and with either reentrant request: the inner success
-- is not published, `Seven`'s entry survives (no rollback), and the owner set is restored.
#guard failedRun (run [("Seven", seven), ("A", failingOwner readA)] [readA]) [("Seven", .atom 7, 1)] 2
#guard failedRun (run [("Seven", seven), ("A", failingOwner callA)] [readA]) [("Seven", .atom 7, 1)] 2
#guard failedRun (run [("Seven", seven), ("A", failingOwner readA)] [callA]) [("Seven", .atom 7, 1)] 2
#guard failedRun (run [("Seven", seven), ("A", failingOwner callA)] [callA]) [("Seven", .atom 7, 1)] 2

/-! ## 5. Nested owners of different keys -/

/-- `A = if(tick() < 3, B + 1, 0)`, `B = A + 1`. -/
def pairDecls : List (Ident × Algorithm) :=
  [("A", alg [] [] [] [callN "if" [tickBelow 3, add (.resolve "B") (.num 1), .num 0]]),
   ("B", alg [] [] [] [add readA (.num 1)])]

-- B's owner marks, reads A reentrantly, publishes 3 and restores; A's protection survives all of it
-- and A's owner publishes 4 AFTER B. Entered through B the owners swap.
#guard okRun (run pairDecls [readA, readA, .resolve "B", .resolve "B"]) (atoms [4, 4, 3, 3])
  [("B", .atom 3, 1), ("A", .atom 4, 1)] 3
#guard okRun (run pairDecls [.resolve "B", readA]) (atoms [5, 4]) [("A", .atom 4, 1), ("B", .atom 5, 1)] 3

/-! ## 6. One request from a hand-built state (synthetic scenes)

`key` is the request's entry-state key. Everything below observes `key` itself. -/

def key : ZeroArgPropertyCacheKey := keyAt .lexical ownerAlg (localP body1) body1 EvalCtx.empty [] EvalState.empty
def request (r : ZeroArgPropertyRequest) : EvalM CountedResult :=
  evalZeroArgPropertyAccessCounted .lexical ownerAlg (localP body1) body1 EvalCtx.empty [] r
def holds (r : ZeroArgPropertyRequest) (s : EvalState) : Option CountedResult :=
  ZeroArgPropertyCache.lookup ((request r).runState s).2.zeroArgPropertyCache key
def outcomeIs (r : ZeroArgPropertyRequest) (s : EvalState) (v : CountedResult) : Bool :=
  match ((request r).runState s).1 with
  | .ok counted => counted == v
  | .error _ => false

def active : EvalState := { activeZeroArgProperties := [key] }
def established : EvalState := { zeroArgPropertyCache := [(key, (.atom 9, 3))] }

-- Reentrant: each request returns its own result and leaves the key absent and active.
#guard outcomeIs .read active (.atom 1, 1) && (holds .read active).isNone
#guard outcomeIs (.invoke "P") active (.atom 1, 1) && (holds (.invoke "P") active).isNone
#guard ((request .read).runState active).2.activeZeroArgProperties == [key]
-- Owner: the entry holds the full counted result, and the mark is gone.
#guard holds .read EvalState.empty == some (.atom 1, 1)
#guard holds (.invoke "P") EvalState.empty == some (.atom 1, 1)
#guard ((request .read).runState EvalState.empty).2.activeZeroArgProperties.isEmpty
-- Established: a read is the entry; an invocation is fresh and keeps the entry.
#guard outcomeIs .read established (.atom 9, 3) && holds .read established == some (.atom 9, 3)
#guard outcomeIs (.invoke "P") established (.atom 1, 1) && holds (.invoke "P") established == some (.atom 9, 3)

/-! ## 7. The incomplete boundary (synthetic scenes)

`fuelExhausted` is the model's incomplete outcome: not a language failure, not cancellation. -/

def isIncomplete {α : Type} (o : Except Error α) : Bool := o.isIncomplete

def body (rec : EvalRec) (r : ZeroArgPropertyRequest) : EvalM CountedResult :=
  EvalBody.evalZeroArgPropertyAccessCounted rec .lexical ownerAlg (localP body1) body1 EvalCtx.empty [] r
def coreCall (r : ZeroArgPropertyRequest) : EvalCall :=
  .evalZeroArgPropertyAccessCounted .lexical ownerAlg (localP body1) body1 EvalCtx.empty [] r

/-- An answer that keeps the state, so that the raw body's own exit is visible. -/
def stall : EvalRec := fun _ => ⟨fun s => (.error .fuelExhausted, s)⟩

-- A RAW body over a stalled answer is incomplete, publishes nothing and KEEPS its mark: no cleanup
-- (`owner_incomplete_keeps_mark`).
#guard isIncomplete ((body stall .read).runState EvalState.empty).1
#guard ((body stall .read).runState EvalState.empty).2.activeZeroArgProperties == [key]
#guard ((body stall .read).runState EvalState.empty).2.zeroArgPropertyCache.isEmpty
-- A core run with too little fuel forgets its state, the protected key's mark included: the reason
-- `active_protected_core` needs `Completes` (`incomplete_core_is_unprotected`). This is neither a
-- release nor a failure of the owner.
#guard isIncomplete ((evalFuel 1 (coreCall .read)).runState active).1
#guard ((evalFuel 1 (coreCall .read)).runState active).2.activeZeroArgProperties.isEmpty
-- With enough fuel the same request completes and the protection holds.
#guard !isIncomplete ((evalFuel 8 (coreCall .read)).runState active).1
#guard ((evalFuel 8 (coreCall .read)).runState active).2.activeZeroArgProperties == [key]
#guard ZeroArgPropertyCache.lookup ((evalFuel 8 (coreCall .read)).runState active).2.zeroArgPropertyCache key == none

/-! ## 8. Axiom audit of the principal declarations -/

/-- info: 'KatLang.CacheReentrancy.active_protected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.active_protected

/-- info: 'KatLang.CacheReentrancy.active_protected_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.active_protected_core

/-- info: 'KatLang.CacheReentrancy.protected_property_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.protected_property_step

/-- info: 'KatLang.CacheReentrancy.active_miss_stays_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.active_miss_stays_absent

/-- info: 'KatLang.CacheReentrancy.reentrant_request_stays_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.reentrant_request_stays_absent

/-- info: 'KatLang.CacheReentrancy.reentrant_request_returns_its_calculation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.reentrant_request_returns_its_calculation

/-- info: 'KatLang.CacheReentrancy.owner_calculation_keeps_key_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.owner_calculation_keeps_key_absent

/-- info: 'KatLang.CacheReentrancy.owner_success_establishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.owner_success_establishes

/-- info: 'KatLang.CacheReentrancy.owner_failure_leaves_no_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.owner_failure_leaves_no_entry

/-- info: 'KatLang.CacheReentrancy.established_entry_stays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.established_entry_stays

/-- info: 'KatLang.CacheReentrancy.established_entry_read_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.established_entry_read_after

/-- info: 'KatLang.CacheReentrancy.owner_incomplete_keeps_mark' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.owner_incomplete_keeps_mark

/-- info: 'KatLang.CacheReentrancy.lookup_insert_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.lookup_insert_missing

/-- info: 'KatLang.CacheReentrancy.lookup_insert_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.CacheReentrancy.lookup_insert_other


end KatLang.CacheReentrancyGuards
