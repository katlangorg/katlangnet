import KatLangArityLaws.OwnerContextStability

open KatLang KatLang.WhileRoundProduction KatLang.OwnerContextStability

/-!
# FG-K2 executable evidence: a retained owner context across evaluation

Beside the kernel theorems of `OwnerContextStability.lean`, two kinds of witness run the production
evaluator.

* **Scenes** (§1, §6): SYNTHETIC host states built with the production operations
  (`needBindingContext`, `enterAlgorithmBody`, `childOfInContext`, `selectNeedFamilyBranch`,
  `evalZeroArgPropertyAccessCounted`), observing records, owner lookup, entries and states directly.
  They also pin, on these inputs, the `scopeInContext` selection the theorems keep as a premise.
* **Programs** (§2–§5): whole runs through `runResultM` of ASTs whose source form each comment gives.
  `tick()` tells reuse from recomputation, which a repeated constant could not.

§7 holds the dangling-reference negative control and §8 the axiom audit.
-/

namespace KatLang.OwnerContextStabilityGuards

def add (a b : Expr) : Expr := .binary .add a b
def sub (a b : Expr) : Expr := .binary .sub a b
def mul (a b : Expr) : Expr := .binary .mul a b
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def tickCall : Expr := callN "tick" []
def local' (name : Ident) (a : Algorithm) : PropDef :=
  privateLocalProp name (.localCapturedAncestorParams ["x"]) a

/-- `Q = tick() + x`, local to the owner of parameter `x`. -/
def localQ : PropDef := local' "Q" (alg [] [] [] [add tickCall (.param "x")])

/-- `Deep(y) = { L = y ⏎ L + y }`: a nested call recording activations of its own. -/
def deepAlg : Algorithm :=
  alg ["y"] [] [privateLocalProp "L" (.localCapturedAncestorParams ["y"]) (alg [] [] [] [.param "y"])]
    [add (.resolve "L") (.param "y")]

/-- A Boolean reading of `OwnerSearchValid`, so a guard can observe it. -/
def searchValid : Option ScopeCtx → EvalState → Bool
  | none, _ => true
  | some (.mk parent _ _ _ _ _ activation _), s =>
      match activation with
      | some id => decide (id < s.lexicalActivations.size)
      | none => searchValid parent s

theorem searchValid_iff : ∀ (chain : Option ScopeCtx) (s : EvalState),
    searchValid chain s = true ↔ OwnerSearchValid chain s
  | none, _ => by simp [searchValid, OwnerSearchValid]
  | some (.mk parent _ _ _ _ _ activation _), s => by
      cases activation with
      | some id => simp [searchValid, OwnerSearchValid]
      | none =>
        simp only [searchValid, OwnerSearchValid]
        exact searchValid_iff parent s

/-- The earlier array is an unchanged prefix of the later one, whole records compared. -/
def prefixKept (s t : EvalState) : Bool :=
  decide (s.lexicalActivations.size ≤ t.lexicalActivations.size) &&
    reprStr s.lexicalActivations.toList ==
      reprStr (t.lexicalActivations.toList.take s.lexicalActivations.size)

/-! ## 1. Scenes over one entered owner -/

/-- `Own(x) = { Q = tick() + x ⏎ Q }`, wired under the prelude. -/
def ownAlg : Algorithm := wireToCaller { callStack := [preludeAlg] } (alg ["x"] [] [localQ] [.resolve "Q"])

/-- What a scene observes between a publication and a later read. -/
structure Scene where
  first : Except Error CountedResult
  between : Except Error Unit
  second : Except Error CountedResult
  chainValid : Bool
  contextAtPublication : Option Nat
  contextAtRead : Option Nat
  entryContext : Nat
  recordsAdded : Nat
  recordsKept : Bool
  readLeftStateAlone : Bool
  ticks : Nat
  entries : Nat

/-- Publish `Q` in the context `pushed`, run `between` there, read `Q` again from an UNRELATED
    consumer context and environment. -/
def observe (owner : Algorithm) (pushed : EvalCtx) (entryContext : Nat)
    (between : EvalCtx → EvalM Unit) : EvalM Scene := do
  let resolved := childOfInContext owner localQ.alg pushed
  let first ← evalAttempt (evalZeroArgPropertyAccessCounted .lexical owner localQ resolved pushed [])
  let published ← get
  let between ← evalAttempt (between pushed)
  let later ← get
  let second ← evalAttempt (evalZeroArgPropertyAccessCounted .structural owner localQ resolved
    { callStack := [owner, preludeAlg], bindingContext := 999 } [("unrelated", .atom 1)])
  let final ← get
  pure {
    first, between, second, entryContext
    chainValid := searchValid resolved.parent published
    contextAtPublication := propertyOwnerBindingContext resolved.parent published
    contextAtRead := propertyOwnerBindingContext resolved.parent later
    recordsAdded := later.lexicalActivations.size - published.lexicalActivations.size
    recordsKept := prefixKept published later
    readLeftStateAlone := reprStr later == reprStr final
    ticks := final.tickCounter
    entries := (final.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == "Q")).length }

/-- `Own(10)` entered through the production binder and body entry. -/
def ownScene (between : EvalCtx → EvalM Unit) : Option Scene :=
  let run : EvalM Scene := do
    let cell ← readyNeed (.atom 10, 1)
    let bound ← needBindingContext { callStack := [preludeAlg] } [("x", cell)]
    let pushed ← enterAlgorithmBody ownAlg bound []
    observe ownAlg pushed bound.bindingContext between
  match run.runState EvalState.empty with
  | (.ok scene, _) => some scene
  | _ => none

/-- The body of a clause family: `Fam(0) = 0`, `Fam(x) = { Q = tick() + x ⏎ Q }`. -/
def famAlg : Algorithm :=
  wireToCaller { callStack := [preludeAlg] } (.conditional none [] [
    ⟨.litInt 0, alg [] [] [] [.num 0]⟩,
    ⟨.bind "x", alg [] [] [localQ] [.resolve "Q"]⟩])

/-- `Fam(10)`: the selected body as the dispatcher activated it, entered once. `exitValid` observes
    the dispatcher's own exit state. -/
def famScene (between : EvalCtx → EvalM Unit) : Option (Scene × Bool × Bool) :=
  let run : EvalM (Scene × Bool × Bool) := do
    let cell ← readyNeed (.atom 10, 1)
    let (body, next, values) ← selectNeedFamilyBranch bindingChannels famAlg [cell]
      { callStack := [preludeAlg] } [] "Fam"
    let exit ← get
    let exitValid := searchValid body.parent exit
    let exitContext := propertyOwnerBindingContext body.parent exit == some next.bindingContext
    let pushed ← enterAlgorithmBody body next values
    let scene ← observe body pushed next.bindingContext between
    pure (scene, exitValid, exitContext)
  match run.runState EvalState.empty with
  | (.ok r, _) => some r
  | _ => none

/-- Several nested calls, each recording its own activations. -/
def nestedCalls (ctx : EvalCtx) : EvalM Unit := do
  let call (n : Int) : Expr := .call (.algorithmExpr (wireToCaller ctx deepAlg)) [.num n]
  let _ ← formOutputRow ctx [] (call 1)
  let _ ← formOutputRow ctx [] (call 2)
  let _ ← formOutputRow ctx [] (call 3)

/-- A nested allocation of activations, then an ordinary failure. -/
def nestedThenFailure (ctx : EvalCtx) : EvalM Unit := do
  let call : Expr := .call (.algorithmExpr (wireToCaller ctx deepAlg)) [.num 1]
  let _ ← formOutputRow ctx [] (.binary .add call (.binary .div (.num 1) (.num 0)))

def reusedAcross (scene : Scene) (records : Nat) : Bool :=
  (match scene.first, scene.second with
   | .ok v, .ok w => v == w
   | _, _ => false)
  && scene.chainValid
  && scene.contextAtPublication == some scene.entryContext
  && scene.contextAtRead == scene.contextAtPublication
  && scene.recordsAdded == records
  && scene.recordsKept
  && scene.readLeftStateAlone
  && scene.ticks == 1
  && scene.entries == 1

/-- Success scenes must complete their intervening calls, not merely retain the entry. -/
def succeededAcross (scene : Scene) (records : Nat) : Bool :=
  reusedAcross scene records && match scene.between with | .ok _ => true | .error _ => false

/-- Failure witnesses pin the ordinary division error, ignoring only its diagnostic frames. -/
def innermostDivByZero : Error → Bool
  | .withContext _ inner => innermostDivByZero inner
  | .divByZero => true
  | _ => false

-- Intervening nested calls append activations; old records, the selected owner context and the
-- counted entry stay, and an unrelated consumer's read returns it without touching the state.
#guard (ownScene nestedCalls).any (succeededAcross · 3)
-- An empty intervening step: the same reuse.
#guard (ownScene (fun _ => pure ())).any (succeededAcross · 0)
-- Ordinary failure after nested allocation: the failure is observed, and the records and the entry
-- stand. A post-state query only: it does not mean a language run continues past the failure.
#guard (ownScene nestedThenFailure).any fun scene =>
  reusedAcross scene 1 && match scene.between with | .error e => innermostDivByZero e | .ok _ => false
-- The selected clause's production activation supplies the valid chain, in the dispatcher's exit
-- state; the body's own entry and rows then share one entry.
#guard (famScene nestedCalls).any fun r => succeededAcross r.1 3 && r.2.1 && r.2.2
-- An activation's INDEX is not its binding context: the entry's record lands at index 0 and stores
-- the binder's fresh context 1.
#guard (ownScene (fun _ => pure ())).any fun scene => scene.contextAtPublication == some 1
#guard (recordsActivation (alg [] [] [privateProp "E" (alg [] [] [] [.num 1])] [.num 1])) == false

/-! ## 2. Whole programs: nested calls and consumers -/

/-- `Own(x) = { Q = tick() + x ⏎ Q, Deep(1), Deep(2), Q }`. -/
def ownRows : Algorithm := alg ["x"] [] [localQ]
  [.resolve "Q", callN "Deep" [.num 1], callN "Deep" [.num 2], .resolve "Q"]

/-- CONTROL: `Fresh(x) = { Q = tick() + x ⏎ Q(), Deep(1), Q() }`: written calls never read. -/
def freshRows : Algorithm := alg ["x"] [] [localQ]
  [callN "Q" [], callN "Deep" [.num 1], callN "Q" []]

/-- `Cons(x) = { Q = tick() + x ⏎ Help(y) = y + Q ⏎ Q, Help(0), [0].map{ n + Q }[0] }`. -/
def consRows : Algorithm := alg ["x"] []
  [localQ, local' "Help" (alg ["y"] [] [] [add (.param "y") (.resolve "Q")])]
  [.resolve "Q", callN "Help" [.num 0],
   .index (.dotCall (.listLiteral [.num 0]) "map"
     (some [.algorithmExpr (alg ["n"] [] [] [add (.param "n") (.resolve "Q")])])) [.num 0]]

/-- `Rd(x) = { B = { V = tick() + x ⏎ V } ⏎ B, [0].map{ n + B }[0], B.V }`: a read-owned owner. -/
def rdRows : Algorithm := alg ["x"] []
  [local' "B" (alg [] [] [local' "V" (alg [] [] [] [add tickCall (.param "x")])] [.resolve "V"])]
  [.resolve "B",
   .index (.dotCall (.listLiteral [.num 0]) "map"
     (some [.algorithmExpr (alg ["n"] [] [] [add (.param "n") (.resolve "B")])])) [.num 0],
   .dotCall (.resolve "B") "V" none]

/-- The same with a collecting-only owner `B(*xs)`: the read binds the empty supply, whose fresh
    context must not become the cache identity. -/
def collectRows : Algorithm := alg ["x"] []
  [local' "B" (algWithParameters [{ name := "xs", kind := .collecting }] []
    [local' "V" (alg [] [] [] [add tickCall (.param "x")])] [.resolve "V"])]
  [.resolve "B",
   .index (.dotCall (.listLiteral [.num 0]) "map"
     (some [.algorithmExpr (alg ["n"] [] [] [add (.param "n") (.resolve "B")])])) [.num 0]]

/-- `Sq(x) = { Q = tick() * 0 + x ⏎ Q - 1, Q > 1 }`: discovery reads `Q`, the transition reuses it. -/
def localFlagQ : PropDef := local' "Q" (alg [] [] [] [add (mul tickCall (.num 0)) (.param "x")])
def gt (a : Expr) (n : Int) : Expr := .comparison a [⟨.gt, .num n⟩]
def sqRows : Algorithm := alg ["x"] [] [localFlagQ] [sub (.resolve "Q") (.num 1), gt (.resolve "Q") 1]

/-- CONTROL: `Sx(x) = { Q = … ⏎ Q() - 1, Q() > 1 }`. -/
def sxRows : Algorithm := alg ["x"] [] [localFlagQ] [sub (callN "Q" []) (.num 1), gt (callN "Q" []) 1]

/-- `Sk(x) = { Q = … ⏎ tick() - tick(), Q > 1 }`: a transition row that ticks. -/
def skRows : Algorithm := alg ["x"] [] [localFlagQ] [sub tickCall tickCall, gt (.resolve "Q") 1]

/-- `Fl(x) = { Q = tick() + x ⏎ Q, Deep(1), 1 / (x - x) }`. -/
def flRows : Algorithm := alg ["x"] [] [localQ]
  [.resolve "Q", callN "Deep" [.num 1], .binary .div (.num 1) (sub (.param "x") (.param "x"))]

def program (rows : List Expr) : Expr :=
  .algorithmExpr (algPrivate [] []
    [("Deep", deepAlg), ("Own", ownRows), ("Fresh", freshRows), ("Cons", consRows), ("Rd", rdRows),
     ("Coll", collectRows), ("Sq", sqRows), ("Sx", sxRows), ("Sk", skRows), ("Fl", flRows)] rows)

def run (rows : List Expr) : Except Error Result × EvalState :=
  (runResultM (program rows)).runState EvalState.empty

def entriesOf (name : Ident) (s : EvalState) : Nat :=
  (s.zeroArgPropertyCache.filter (fun e => e.fst.propertyName == name)).length

/-- The outcome is `value`, `tick()` ran `ticks` times, and `name` has `entries` entries. -/
def observed (rows : List Expr) (value : Result) (ticks : Nat) (name : Ident) (entries : Nat) : Bool :=
  let (outcome, state) := run rows
  (match outcome with | .ok v => v == value | .error _ => false)
    && state.tickCounter == ticks && entriesOf name state == entries

def seqOf (values : List Int) : Result := .sequenceValue (values.map Result.atom)

-- Nested calls between two reads: one execution, one entry, equal rows.
#guard observed [callN "Own" [.num 10]] (seqOf [11, 2, 4, 11]) 1 "Q" 1
-- CONTROL: written calls run twice beside the same nested call.
#guard observed [callN "Fresh" [.num 10]] (seqOf [11, 2, 12]) 2 "Q" 1
-- Consumer independence: the body, a helper call and a callback share one entry.
#guard observed [callN "Cons" [.num 10]] (seqOf [11, 11, 11]) 1 "Q" 1
-- A read-owned owner retains the declaring identity across all three spellings.
#guard observed [callN "Rd" [.num 10]] (seqOf [11, 11, 11]) 1 "V" 1
-- A collecting-only owner binds the empty supply and keeps that identity too.
#guard observed [callN "Coll" [.num 10]] (seqOf [11, 11]) 1 "V" 1

/-! ## 3. Fresh owner activations stay separate -/

-- Equal argument values in separate calls: two entries, two executions.
#guard
  let state := (run [callN "Own" [.num 5], callN "Own" [.num 5]]).2
  state.tickCounter == 2 && entriesOf "Q" state == 2
-- The two entries carry two contexts.
#guard
  let keys := (run [callN "Own" [.num 5], callN "Own" [.num 5]]).2.zeroArgPropertyCache.filter
    (fun e => e.fst.propertyName == "Q")
  match keys.map (fun e => e.fst.bindingContext) with
  | [some a, some b] => a != b
  | _ => false

/-! ## 4. The condition-first round -/

def whileOf (step : String) (state : List Expr) : Expr := callN "while" [callN step state]

-- From 3: rounds 3 and 2 accept, 1 stops. ONE execution of `Q` per round, discovery and transition.
#guard observed [whileOf "Sq" [.num 3]] (.atom 1) 3 "Q" 3
-- CONTROL: three flags and two transitions, each a written call.
#guard observed [whileOf "Sx" [.num 3]] (.atom 1) 5 "Q" 3
-- A false continuation forms no transition: only `Q`'s own execution, and the entry is published.
#guard observed [whileOf "Sk" [.num 1]] (.atom 1) 1 "Q" 1
-- A true round forms its ticking row exactly once (two ticks), beside `Q`'s one per round; the next
-- state -1 stops.
#guard observed [whileOf "Sk" [.num 2]] (.atom (-1)) 4 "Q" 2

/-! ## 5. Failure -/

-- The run fails after the nested call; the final state keeps the entry and the records.
#guard
  let (outcome, state) := run [callN "Fl" [.num 10]]
  (match outcome with | .error e => innermostDivByZero e | .ok _ => false)
    && state.tickCounter == 1 && entriesOf "Q" state == 1 && state.lexicalActivations.size == 2

/-! ## 6. The host fallback keeps its input conditions -/

def envA : ValEnv := [("h", .atom 1)]
def envB : ValEnv := [("h", .atom 2)]
def hostCtx : EvalCtx := { callStack := [preludeAlg], bindingContext := 4 }
def hostBinding : PropDef := privateLocalProp "H" (.localCapturedAncestorParams ["h"]) (alg [] [] [] [tickCall])
def hostOwner : Algorithm := alg [] [] [hostBinding] []

-- A retained context ignores the environment; without one the environment splits the key.
#guard zeroArgPropertyCacheKey .lexical hostOwner hostBinding hostCtx envA (some 3) ==
  zeroArgPropertyCacheKey .lexical hostOwner hostBinding hostCtx envB (some 3)
#guard !(zeroArgPropertyCacheKey .lexical hostOwner hostBinding hostCtx envA none ==
  zeroArgPropertyCacheKey .lexical hostOwner hostBinding hostCtx envB none)

/-- The chain is one unactivated level: valid, and it answers `none`. -/
def hostResolved : Algorithm := hostBinding.alg.withParent (some preludeAlg.asScopeCtx)

#guard searchValid hostResolved.parent EvalState.empty
#guard propertyOwnerBindingContext hostResolved.parent EvalState.empty == none

/-- Reads of a binding with NO activated level, under `first` then `second`: how many ticks ran. -/
def hostTicks (first second : ValEnv) : Nat :=
  let read (env : ValEnv) := evalZeroArgPropertyAccessCounted .lexical hostOwner hostBinding
    hostResolved hostCtx env
  ((do let _ ← read first; read second : EvalM _).runState EvalState.empty).2.tickCounter

#guard hostTicks envA envA == 1
#guard hostTicks envA envB == 2

/-! ## 7. NEGATIVE CONTROL: a dangling reference

Synthetic states: this bounds the theorem and shows no reachable language bug. The kernel statement
is `dangling_reference_breaks_stability`. -/

#guard propertyOwnerBindingContext danglingChain danglingBefore == some 10
#guard propertyOwnerBindingContext danglingChain danglingAfter == some 20
#guard prefixKept danglingBefore danglingAfter
#guard !searchValid danglingChain danglingBefore
-- The same chain with the record present before the append is valid and does not move.
#guard searchValid danglingChain danglingAfter
#guard propertyOwnerBindingContext danglingChain
  { danglingAfter with
    lexicalActivations := danglingAfter.lexicalActivations.push { values := [], bindingContext := 30 } } ==
  propertyOwnerBindingContext danglingChain danglingAfter

/-! ## 8. Axiom audit of the principal declarations -/

/-- info: 'KatLang.OwnerContextStability.activations_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.OwnerContextStability.activations_kept

/-- info: 'KatLang.OwnerContextStability.activations_kept_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.OwnerContextStability.activations_kept_core

/-- info: 'KatLang.OwnerContextStability.owner_context_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.OwnerContextStability.owner_context_stable

/-- info: 'KatLang.OwnerContextStability.local_publication_reused_after_production' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.OwnerContextStability.local_publication_reused_after_production

/-- info: 'KatLang.OwnerContextStability.entered_body_shares_local_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.OwnerContextStability.entered_body_shares_local_entry

/-- info: 'KatLang.OwnerContextStability.dispatched_body_shares_local_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.OwnerContextStability.dispatched_body_shares_local_entry

/-- info: 'KatLang.OwnerContextStability.round_exit_reads_discovery_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.OwnerContextStability.round_exit_reads_discovery_entry

/-- info: 'KatLang.OwnerContextStability.false_continuation_keeps_local_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.OwnerContextStability.false_continuation_keeps_local_entry

/-- info: 'KatLang.OwnerContextStability.structural_read_reuses_lexical_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.OwnerContextStability.structural_read_reuses_lexical_entry

end KatLang.OwnerContextStabilityGuards
