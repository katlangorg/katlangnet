import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algPrivate runResultM Algorithm Error Result EvalState)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- Q-37 (owner decision, October 11 2026): the OUTERMOST successful property-style
-- evaluation of a cache key owns its entry
--------------------------------------------------------------------------------
-- THE PUBLICATION LAW (`evalZeroArgPropertyAccessCounted` over
-- `EvalState.activeZeroArgProperties`; C# `ZeroArgPropertyPublications`): a miss on a
-- key that is not active makes the access the key's OWNER; a miss on an ACTIVE key
-- (the same binding reached again before its owner finished, directly or through
-- other properties and calls) is RE-ENTRANT — it evaluates and returns its own result
-- but publishes nothing; only a successful owner publishes; a failed owner publishes
-- nothing for its key while other keys' published entries stay. This supersedes the
-- first-successful-completion rule, under which the INNERMOST re-entrant completion
-- was stored first and the outer results never replaced it.
--
-- Evidence technique (EXPORTED-DETACHED, November 2026). `P` is a parameterless EXPORTED
-- property, so every read of it has ONE cache key, and its body is SELF-CONTAINED, as an
-- exported property must be: successive evaluations differ through the run's `tick()`
-- counter alone:
--
--   P = if(tick() > 1, 1, G(0) + 100)     G(x) = P
--
-- `G(1), G(5)`: G(1)'s read of P is P's owner (tick 1); it calls G(0), whose read of P is
-- RE-ENTRANT (tick 2) and returns 1; the owner returns and publishes 101; G(5)'s read hits
-- the owner's 101. Under the superseded rule the re-entrant 1 was stored first, so G(5)
-- read 1 (`S[101, 1]`). A reader's argument is never read: it only tells the rows apart.
-- (Until November 2026 these guards used `P = if(x == 0, 1, G(x - 1) + 100)`, where `P`
-- read `x` — a name it does not bind — dynamically from whichever caller evaluated it. An
-- exported property is now evaluated DETACHED and that read is `unknownName`:
-- `pubDynamicReadIsRefused` below. The same law over counted entries and its kernel
-- theorems are `KatLangArityLaws/CacheReentrancyGuards.lean` and `CacheReentrancy.lean`;
-- C# pins the surface reproductions with `tock` and the seeded stream,
-- `OutermostPropertyCachePublicationTests`.)

/-- `G(x) = P` — and its variants: every algorithm whose output is ONE read of a property. -/
def pubReader (property : String) : Algorithm := alg ["x"] [] [] [resolve property]

def pubTick : KatLang.Expr := .call (resolve "tick") []

/-- `P = if(tick() > depth, base, Reader(0) + 100)`: the first `depth` evaluations of the run
    recurse through the reader, every later one is the base case. -/
def pubRecursive (reader : String) (base : KatLang.Expr) (step : KatLang.Expr → KatLang.Expr)
    (depth : Int := 1) : Algorithm :=
  alg [] [] [] [.call (resolve "if")
    [.compare .gt pubTick (num depth), base, step (.call (resolve reader) [num 0])]]

def pubPlus100 (inner : KatLang.Expr) : KatLang.Expr := .binary .add inner (num 100)

def pubRoot (out : List KatLang.Expr) (depth : Int := 1) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [ -- Direct recursion: P = if(tick() > depth, 1, G(0) + 100), G(x) = P.
      ("P", pubRecursive "G" (num 1) pubPlus100 depth), ("G", pubReader "P")
      -- H(x) = P(): an explicit zero-supply invocation of P (CACHE-PUB-1: it may own P's key).
    , ("H", alg ["x"] [] [] [.call (resolve "P") []])
      -- CACHE-PUB-1 explicit-call recursion: PC = if(tick() > 1, 1, HC(0) + 100), HC(x) = PC(),
      -- GC(x) = PC.
    , ("PC", pubRecursive "HC" (num 1) pubPlus100)
    , ("HC", alg ["x"] [] [] [.call (resolve "PC") []]), ("GC", pubReader "PC")
      -- A read owning an inner explicit call: PR = if(tick() > 1, 1, HR(0) + 100), HR(x) = PR(),
      -- GR(x) = PR.
    , ("PR", pubRecursive "HR" (num 1) pubPlus100)
    , ("HR", alg ["x"] [] [] [.call (resolve "PR") []]), ("GR", pubReader "PR")
      -- A failing explicit owner after an inner success, and after another key published:
      -- PFC = if(tick() > 1, 1, HFC(0) + 1 / 0), HFC(x) = PFC();
      -- PSC = if(tick() > 1, 1, Seven + HSC(0) + 1 / 0), HSC(x) = PSC().
    , ("PFC", pubRecursive "HFC" (num 1) (fun inner => .binary .add inner (.binary .div (num 1) (num 0))))
    , ("HFC", alg ["x"] [] [] [.call (resolve "PFC") []])
    , ("PSC", pubRecursive "HSC" (num 1)
        (fun inner => .binary .add (.binary .add (resolve "Seven") inner) (.binary .div (num 1) (num 0))))
    , ("HSC", alg ["x"] [] [] [.call (resolve "PSC") []])
      -- Re-entrance through an explicit-call frame:
      -- R = if(tick() > 1, 1, L(0) + 100), L(x) = M(), M = R, LR(x) = R.
    , ("R", pubRecursive "L" (num 1) pubPlus100)
    , ("L", alg ["x"] [] [] [.call (resolve "M") []])
    , ("M", alg [] [] [] [resolve "R"]), ("LR", pubReader "R")
      -- Indirect recursion IA → IB → IA: IA = if(tick() > 1, 1, IB + 100), IB = IG(0),
      -- IG(x) = IA, IGB(x) = IB.
    , ("IA", alg [] [] [] [.call (resolve "if")
        [.compare .gt pubTick (num 1), num 1, .binary .add (resolve "IB") (num 100)]])
    , ("IB", alg [] [] [] [.call (resolve "IG") [num 0]])
    , ("IG", pubReader "IA"), ("IGB", pubReader "IB")
      -- A failing owner after an inner same-key success:
      -- PF = if(tick() > 1, 1, GF(0) + 1 / 0), GF(x) = PF.
    , ("PF", pubRecursive "GF" (num 1) (fun inner => .binary .add inner (.binary .div (num 1) (num 0))))
    , ("GF", pubReader "PF")
      -- The same, after ANOTHER key (Seven) published inside the failed attempt:
      -- PS = if(tick() > 1, 1, Seven + GS(0) + 1 / 0), GS(x) = PS, Seven = 3 + 4.
    , ("Seven", alg [] [] [] [.binary .add (num 3) (num 4)])
    , ("PS", pubRecursive "GS" (num 1)
        (fun inner => .binary .add (.binary .add (resolve "Seven") inner) (.binary .div (num 1) (num 0))))
    , ("GS", pubReader "PS")
      -- Sibling re-entrant reads, each with its own value:
      -- PB = if(tick() > 1, tick() * 10, GB(0) + GB(0)), GB(x) = PB.
    , ("PB", alg [] [] [] [.call (resolve "if")
        [.compare .gt pubTick (num 1), .binary .mul pubTick (num 10),
         .binary .add (.call (resolve "GB") [num 0]) (.call (resolve "GB") [num 0])]])
    , ("GB", pubReader "PB")
      -- The former technique: PX reads `x`, which it does not bind, from its caller.
    , ("PX", alg [] [] [] [param "x"]), ("GX", pubReader "PX") ]
    out)

/-- A run's outcome, the property names and values its cache holds (in publication
    order), and how many keys are still active — kept for a FAILED run too (`runState`
    retains the state exactly as `evalAttempt` does). -/
def pubRun (out : List KatLang.Expr) (depth : Int := 1) : Except Error Result × List (String × Result) × Nat :=
  let (result, state) := (runResultM (pubRoot out depth)).runState EvalState.empty
  (result, state.zeroArgPropertyCache.map (fun entry => (entry.fst.propertyName, entry.snd.fst)),
   state.activeZeroArgProperties.length)

def pubCall (name : String) (x : Int) : KatLang.Expr := .call (resolve name) [num x]

def pubAtoms (values : List Int) : Result := Result.sequenceValue (values.map Result.atom)

/-- `G(1), G(5)`: the owner's 101 is published and reused — `S[101, 101]` (formerly `S[101, 1]`). -/
def pubOutermostOwnsTheEntry : Bool :=
  match pubRun [pubCall "G" 1, pubCall "G" 5] with
  | (.ok result, cache, 0) => result == pubAtoms [101, 101] && cache == [("P", Result.atom 101)]
  | _ => false

#guard pubOutermostOwnsTheEntry

/-- Deeper: three re-entrant levels below the owner (ticks 1 to 4); the owner's 301 is the
    only entry and later reads reuse it. -/
def pubDeeperRecursion : Bool :=
  match pubRun [pubCall "G" 3, pubCall "G" 9, pubCall "G" 0] 3 with
  | (.ok result, cache, 0) => result == pubAtoms [301, 301, 301] && cache == [("P", Result.atom 301)]
  | _ => false

#guard pubDeeperRecursion

/-- CACHE-PUB-1 (owner decision October 22 2026, superseding "an explicit call owns nothing"):
    the explicit zero-supply invocation `P()` (tick 1) is P's OWNER — the key is empty and inactive
    — so the property-style read of P inside it (tick 2, through G) is RE-ENTRANT: it returns 1 and
    publishes nothing, and `P()`'s own success publishes 101, which G(5) reuses. Under the
    superseded rule the inner read owned the key and published 1 (`S[101, 1]`). -/
def pubExplicitCallOwnsTheEntry : Bool :=
  match pubRun [pubCall "H" 1, pubCall "G" 5] with
  | (.ok result, cache, 0) => result == pubAtoms [101, 101] && cache == [("P", Result.atom 101)]
  | _ => false

#guard pubExplicitCallOwnsTheEntry

/-- Re-entrance is detected through an explicit-call frame: R's owner (tick 1) calls L(0),
    whose explicit `M()` reads R property-style while R is active — re-entrant, 1, not
    published; R's owner publishes 101. The explicit `M()` is M's owning zero-supply invocation:
    it establishes M's entry with the 1 it computed (CACHE-PUB-1; formerly M stayed empty). -/
def pubReentranceThroughExplicitCall : Bool :=
  match pubRun [pubCall "LR" 1, pubCall "LR" 5] with
  | (.ok result, cache, 0) =>
      result == pubAtoms [101, 101] && cache == [("M", Result.atom 1), ("R", Result.atom 101)]
  | _ => false

#guard pubReentranceThroughExplicitCall

/-! ### CACHE-PUB-1: explicit zero-supply invocations share the ONE ownership domain -/

/-- An explicit call owning another explicit call of the same key: HC(1)'s `PC()` owns PC's key;
    the inner `PC()` of the HC(0) it calls is re-entrant (1, unpublished); the owner publishes 101,
    which a later bare read (GC(5)) reuses. -/
def pubExplicitOwnerInnerExplicitCall : Bool :=
  match pubRun [pubCall "HC" 1, pubCall "GC" 5] with
  | (.ok result, cache, 0) => result == pubAtoms [101, 101] && cache == [("PC", Result.atom 101)]
  | _ => false

#guard pubExplicitOwnerInnerExplicitCall

/-- A property-style read owning an inner explicit call: GR(1)'s read of PR owns the key, the
    `PR()` of the HR(0) it calls is re-entrant (1, unpublished) and the read publishes 101. A later
    explicit `PR()` (the row HR(0)) is FRESH — it returns its own 1 (tick 3) — and leaves the
    established 101 unchanged. -/
def pubReadOwnerInnerExplicitCall : Bool :=
  match pubRun [pubCall "GR" 1, pubCall "HR" 0, pubCall "GR" 5] with
  | (.ok result, cache, 0) => result == pubAtoms [101, 1, 101] && cache == [("PR", Result.atom 101)]
  | _ => false

#guard pubReadOwnerInnerExplicitCall

/-- An established entry is never replaced by a fresh explicit invocation: G(1) publishes 101;
    H(0)'s `P()` (tick 3) executes and returns 1 without reading or replacing it; G(5) still reads
    101. -/
def pubEstablishedEntryUnchangedByFreshCall : Bool :=
  match pubRun [pubCall "G" 1, pubCall "H" 0, pubCall "G" 5] with
  | (.ok result, cache, 0) => result == pubAtoms [101, 1, 101] && cache == [("P", Result.atom 101)]
  | _ => false

#guard pubEstablishedEntryUnchangedByFreshCall

/-- A failed explicit owner publishes nothing for its key — the inner re-entrant `PFC()` completed
    with 1, which never survives — and releases the key. -/
def pubFailedExplicitOwnerPublishesNothing : Bool :=
  match pubRun [pubCall "HFC" 1] with
  | (.error err, cache, 0) => innermostIsDivByZero err && cache.isEmpty
  | _ => false

#guard pubFailedExplicitOwnerPublishesNothing

/-- …while another key's owner that completed inside the failed explicit attempt keeps its entry. -/
def pubFailedExplicitOwnerKeepsOtherEntries : Bool :=
  match pubRun [pubCall "HSC" 1] with
  | (.error err, cache, 0) => innermostIsDivByZero err && cache == [("Seven", Result.atom 7)]
  | _ => false

#guard pubFailedExplicitOwnerKeepsOtherEntries

/-- Indirect recursion IA → IB → IA: IB's owner publishes the 1 it computed from IA's
    re-entrant read, then IA's owner publishes 101 (formerly IA held the re-entrant 1). -/
def pubIndirectRecursion : Bool :=
  match pubRun [pubCall "IG" 1, pubCall "IG" 5, pubCall "IGB" 9] with
  | (.ok result, cache, 0) =>
      result == pubAtoms [101, 101, 1] && cache == [("IB", Result.atom 1), ("IA", Result.atom 101)]
  | _ => false

#guard pubIndirectRecursion

/-- Sibling re-entrant reads each EVALUATE, since neither publishes: PB's owner (tick 1) reads PB
    twice; the first sibling takes ticks 2 and 3 and returns 30, the second takes ticks 4 and 5 and
    returns 50, so the owner returns 30 + 50 = 80 and publishes it. This separates the law from both
    alternatives: under first-completion-wins the first sibling's 30 was stored and the second hit it
    (`S[60, 30]`); under a last-writer-wins publication the second sibling hit the first's entry and
    the owner replaced it (`S[60, 60]`). -/
def pubSiblingReentrantReadsEachEvaluate : Bool :=
  match pubRun [pubCall "GB" 2, pubCall "GB" 7] with
  | (.ok result, cache, 0) => result == pubAtoms [80, 80] && cache == [("PB", Result.atom 80)]
  | _ => false

#guard pubSiblingReentrantReadsEachEvaluate

/-- EXPORTED-DETACHED (November 2026): an exported property is evaluated DETACHED from its reader,
    so `PX = x` — a body that reads a name it does not bind — finds no binding whichever caller
    reads it, and nothing is published or left active. Formerly `GX(1), GX(5)` was `S[1, 1]`: the
    first caller's `x`, shared run-wide. -/
def pubDynamicReadIsRefused : Bool :=
  match pubRun [pubCall "GX" 1, pubCall "GX" 5] with
  | (.error err, cache, 0) => innermostIsUnknownName "x" err && cache.isEmpty
  | _ => false

#guard pubDynamicReadIsRefused

/-- Ownership is per cache KEY, never per name: a local-only `P` of a RECURSIVE owner is a new key in
    every activation, so the nested `Outer(0)`'s `P` is that key's owner — not a re-entrant read of
    `Outer(1)`'s still-running `P` — publishes `1`, and its second read hits. Both activations' entries
    exist afterwards (`P` and `P`), and the result is `Outer(1)` = `12 + 12` = `24`. An active set keyed
    by the property's name would treat the inner `P` as re-entrant and leave only one entry. -/
def pubOwnershipIsPerKeyNotPerName : Bool :=
  let root := algPrivate [] [] [
    ("Outer", alg ["x"] [] [
      KatLang.privateLocalProp "P" (.localCapturedAncestorParams ["x"])
        (alg [] [] [] [.call (resolve "if")
          [.compare .eq (param "x") (num 0), num 1,
           .binary .add (.call (resolve "Outer") [.binary .sub (param "x") (num 1)]) (num 10)]])
    ] [.binary .add (resolve "P") (resolve "P")])
  ] [.call (resolve "Outer") [num 1]]
  match (KatLang.runResultM (.algorithmExpr root)).runState EvalState.empty with
  | (.ok (Result.atom 24), state) =>
      state.activeZeroArgProperties.isEmpty
        && (state.zeroArgPropertyCache.filter (fun entry => entry.fst.propertyName == "P")).map (·.snd.fst)
             == [Result.atom 1, Result.atom 12]
  | _ => false

#guard pubOwnershipIsPerKeyNotPerName

/-- A failed owner publishes nothing for its key, although its re-entrant read completed
    with 1 (formerly that 1 was stored), and releases its key: nothing stays active, so no
    later read could be mistaken for a re-entrant one. -/
def pubFailedOwnerPublishesNothing : Bool :=
  match pubRun [pubCall "GF" 1] with
  | (.error err, cache, 0) => innermostIsDivByZero err && cache.isEmpty
  | _ => false

#guard pubFailedOwnerPublishesNothing

/-- …while another key's owner that completed inside the failed attempt keeps its entry. -/
def pubFailedOwnerKeepsOtherEntries : Bool :=
  match pubRun [pubCall "GS" 1] with
  | (.error err, cache, 0) => innermostIsDivByZero err && cache == [("Seven", Result.atom 7)]
  | _ => false

#guard pubFailedOwnerKeepsOtherEntries

-- A past reader's admission remains part of the source's judgment. Its establishment
-- watermark cuts off its own work, and an attached demand may read even an earlier input.
private def retainedReadAfterReaderReturned : KatLang.CellRecords :=
  { records := [(0, { watermark := 10, refusal := .divByZero, forwards := [1] }),
                (1, { watermark := 5, refusal := .divByZero, readers := [4, 6] })],
    serving := [4, 6] }

#guard retainedReadAfterReaderReturned.lateRefused 0 4
#guard !retainedReadAfterReaderReturned.lateRefused 0 6
-- Equal-sized sets can name different owners. Each side must detach this very read.
#guard !({ retainedReadAfterReaderReturned with serving := [3, 6] } : KatLang.CellRecords).lateRefused 0 4
#guard !({ retainedReadAfterReaderReturned with serving := [3, 6] } : KatLang.CellRecords).lateRefused 0 3
#guard !({ retainedReadAfterReaderReturned with serving := [] } : KatLang.CellRecords).lateRefused 0 4

-- A member access uses both owners. Refusing the later one rejects the whole access.
#guard match retainedReadAfterReaderReturned.noteReads 0 [3, 4] .divByZero with
  | .error .divByZero => true
  | _ => false
#guard match ({ retainedReadAfterReaderReturned with serving := [] } : KatLang.CellRecords).noteReads 0 [3, 4] .divByZero with
  | .ok (_, inputs) => match KatLang.cellInputsAt? 0 inputs.records with
    | some record => record.dependsFor 8 [3] && record.dependsFor 8 [4]
    | none => false
  | _ => false

end KatLangTests
