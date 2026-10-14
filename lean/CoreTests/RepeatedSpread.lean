import KatLang
import CoreTests.Common

/-!
# Repeated spread routes through the total reopening helpers (Q-66 item 4, October 2026)

`KatLangArityLaws.lean` § Repeated spread over the real model proves the post-evaluation value
operation of a repeated spread as theorems over the TOTAL production helpers:
`reopenSpreadItems` (one further layer, `spread(capture(items))`), `reopenSpreadLayers` (one
step per extra written star), `spreadSupplyResult` (a spread expression's counted result), and
the grouped layer through the capture arm's `countedTopLevelValues` / `combineOutputSlots`
(`grouped_spread_layer_is_reopen`). That the `partial` evaluator APPLIES them is a fact of its
source — `evalSequenceSpreadCounted` evaluates the operand once and returns
`spreadSupplyResult (reopenSpreadLayers (layers - 1) supplied)`, and a written capture combines
its spread row's recovered slots shallowly. These guards pin that routing executably:

1. for every mixed spelling with one to three written stars (`A*`, `A**`, `(A*)*`, `A***`,
   `(A**)*`, `(A*)**`, `((A*)*)*`), every adversarial operand value, and every way of writing the
   operand (a literal, a property, a block, a call), the supply the spelling hands a collector is
   the helpers' prediction over the operand value's own spread view — so all spellings with the
   same number of stars agree, the stacked and grouped ones included;
2. a direct (root-free) evaluation of a spread over a literal operand returns exactly the
   predicted counted result (value AND emitted count);
3. hand-written expected supplies pin the observable shapes independently of the helpers: zero
   stays zero, a multi-item first spread is a fixed point that never flattens, and a lone
   structured item opens exactly one more boundary per star;
4. the operand is EVALUATED ONCE whatever the number of stars or groupings: every user call opens
   one binding context (`EvalState.nextBindingContext`), so a fresh call operand `Id(v)` opens
   one context under every spelling, including operands whose supply changes across layers;
5. the INTERNAL join (`sequenceConstruct`, host-built only) reads a spread leaf exactly as a
   written capture reads a spread row (`evalCounted` + `countedTopLevelValues`, never re-spread):
   with the non-empty second leaf `3`, the join equals the written capture in value and emitted
   count for every operand value and every spelling;
6. hand-written join shapes, independent of the capture route: a lone structured item stays
   whole, a lone spread-produced `()` stays an item, a stacked leaf opens one boundary per star,
   and a NON-spread `()` leaf is still dropped.

C# twins: `StarSyntaxTests` (`RepeatedSpread_*`), `ListValueTests.StackedSpread_*` (1–4);
`SequenceConstructContainmentTests` (`DirectSequenceConstruct_*`) and the `internal__sc_spread_*`
explorer cases (5–6).
-/

namespace KatLangTests.RepeatedSpread
open KatLang

def n (i : Int) : Expr := .num i
def lit (items : List Expr) : Expr := .listLiteral items
def tup (items : List Expr) : Expr := .capture items
def unit : Expr := .emptySequence 0

/-- The adversarial operand values, as written expressions. -/
def operandValues : List Expr :=
  [ n 7, unit, lit [], tup [n 1, n 2], lit [n 1, n 2],
    lit [lit [n 7]], lit [lit [lit [n 7]]], lit [lit [n 1, n 2], lit [n 3, n 4]],
    lit [unit, lit []], lit [unit], lit [lit []], lit [tup [n 1, n 2]], lit [lit [unit]],
    lit [lit [n 1, n 2], n 3], tup [lit [n 1, n 2], lit [n 3, n 4]] ]

/-- Every mixed spelling of one to three written stars over the operand, with the number of
REOPENING layers it denotes (its stars minus one). -/
def spellings : List (Nat × (Expr -> Expr)) :=
  [ (0, fun a => .sequenceSpread a),
    (1, fun a => .sequenceSpread (.sequenceSpread a)),
    (1, fun a => .sequenceSpread (.capture [.sequenceSpread a])),
    (2, fun a => .sequenceSpread (.sequenceSpread (.sequenceSpread a))),
    (2, fun a => .sequenceSpread (.capture [.sequenceSpread (.sequenceSpread a)])),
    (2, fun a => .sequenceSpread (.sequenceSpread (.capture [.sequenceSpread a]))),
    (2, fun a => .sequenceSpread (.capture [.sequenceSpread (.capture [.sequenceSpread a])])) ]

/-- `Coll(*xs) = xs`: the exact list of the supplied items. -/
def collAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] [] [param "xs"]

/-- `Id(y) = y`: one binding context per call. -/
def idAlg : Algorithm := alg ["y"] [] [] [param "y"]

/-- A root with `Coll`, `Id` and the property `A` (whose body is the operand value). -/
def root (value : Expr) (out : List Expr) : Expr :=
  .algorithmExpr (algPrivate [] []
    [("Coll", collAlg), ("Id", idAlg), ("A", alg [] [] [] [value])] out)

/-- The ways of writing the operand: a literal, a property, a block, a fresh call. -/
def operandForms (value : Expr) : List Expr :=
  [ value, resolve "A", .algorithmExpr (alg [] [] [] [value]), .call (resolve "Id") [value] ]

/-- What the helpers predict a collector receives from `layers` reopening layers over the
operand value `v`: the spread row's recovered slots of `spreadSupplyResult`. -/
def predictedSupply (layers : Nat) (v : Result) : Result :=
  .listValue (countedTopLevelValues (spreadSupplyResult (reopenSpreadLayers layers v.spreadItems)))

/-- 1. Every spelling, operand value and operand form hands the collector the predicted supply. -/
def everySpellingCollectsThePredictedSupply : Bool :=
  operandValues.all fun value =>
    match runResult (root value [resolve "A"]) with
    | .ok v =>
        (operandForms value).all fun operand =>
          spellings.all fun (layers, spell) =>
            (runResult (root value [.call (resolve "Coll") [spell operand]])).toOption
              == some (predictedSupply layers v)
    | .error _ => false

#guard everySpellingCollectsThePredictedSupply

/-- Evaluate one expression directly (no root), counted. -/
def counted (e : Expr) : Except Error CountedResult :=
  runEvalM (evalCounted e { callStack := [preludeAlg] } [])

/-- 2. A direct spread over a literal operand returns exactly `spreadSupplyResult` of the
reopened supply — value and emitted count. -/
def directSpreadReturnsThePredictedCountedResult : Bool :=
  operandValues.all fun value =>
    match counted value with
    | .ok (v, _) =>
        spellings.all fun (layers, spell) =>
          match counted (spell value) with
          | .ok (result, count) =>
              let predicted := spreadSupplyResult (reopenSpreadLayers layers v.spreadItems)
              result == predicted.fst && count == predicted.snd
          | .error _ => false
    | .error _ => false

#guard directSpreadReturnsThePredictedCountedResult

/-- The supply a collector receives from `spell` over the property `A = value`. -/
def collected (value : Expr) (spell : Expr -> Expr) : Option Result :=
  (runResult (root value [.call (resolve "Coll") [spell (resolve "A")]])).toOption

def stacked2 (a : Expr) : Expr := .sequenceSpread (.sequenceSpread a)
def grouped2 (a : Expr) : Expr := .sequenceSpread (.capture [.sequenceSpread a])
def stacked3 (a : Expr) : Expr := .sequenceSpread (.sequenceSpread (.sequenceSpread a))
def grouped3 (a : Expr) : Expr :=
  .sequenceSpread (.capture [.sequenceSpread (.capture [.sequenceSpread a])])

def atomList (items : List Int) : Result := .listValue (items.map Result.atom)

/-- 3. Hand-written supplies, independent of the helpers. -/
def repeatedSpreadSuppliesHaveTheirPinnedShapes : Bool :=
  -- ZERO stays zero: `()**` and `[]**` supply nothing (their first spread is already empty).
  [unit, lit []].all (fun value =>
    collected value stacked2 == some (.listValue []) &&
    collected value grouped2 == some (.listValue [])) &&
  -- A LONE visible empty reopens to nothing (the singleton law with a lone `()` or `[]`):
  -- `[()]**` and `[[]]**`, and `[[()]]***` one star later — whose lone `()` is still one
  -- visible item at `[[()]]**`.
  [lit [unit], lit [lit []]].all (fun value =>
    collected value stacked2 == some (.listValue []) &&
    collected value grouped2 == some (.listValue [])) &&
  collected (lit [lit [unit]]) stacked3 == some (.listValue []) &&
  collected (lit [lit [unit]]) grouped3 == some (.listValue []) &&
  collected (lit [lit [unit]]) stacked2 == some (.listValue [.sequenceValue []]) &&
  -- MULTI-ITEM first spreads are fixed points whose items are never opened: `[[1, 2], [3, 4]]`
  -- keeps its two inner lists at every layer (never `1, 2, 3, 4`).
  [stacked2, grouped2, stacked3, grouped3].all (fun spell =>
    collected (lit [lit [n 1, n 2], lit [n 3, n 4]]) spell
      == some (.listValue [atomList [1, 2], atomList [3, 4]])) &&
  collected (lit [unit, lit []]) stacked2
    == some (.listValue [.sequenceValue [], .listValue []]) &&
  collected (lit [unit, lit []]) grouped2
    == some (.listValue [.sequenceValue [], .listValue []]) &&
  -- A LONE structured item opens exactly one more boundary per star: `[[[7]]]` supplies
  -- `[[7]]`, then `[7]`, then `7`; a lone sequence `(1, 2)` or list `[1, 2]` opens one level.
  collected (lit [lit [lit [n 7]]]) (fun a => .sequenceSpread a)
    == some (.listValue [.listValue [atomList [7]]]) &&
  collected (lit [lit [lit [n 7]]]) stacked2 == some (.listValue [atomList [7]]) &&
  collected (lit [lit [lit [n 7]]]) stacked3 == some (atomList [7]) &&
  collected (lit [lit [lit [n 7]]]) grouped3 == some (atomList [7]) &&
  collected (lit [tup [n 1, n 2]]) stacked2 == some (atomList [1, 2]) &&
  collected (lit [lit [n 1, n 2]]) grouped2 == some (atomList [1, 2]) &&
  -- A lone scalar is itself at every layer.
  collected (lit [n 7]) stacked3 == some (atomList [7])

#guard repeatedSpreadSuppliesHaveTheirPinnedShapes

/-- The binding contexts a SUCCESSFUL root run opens (`none` for a failed run). -/
def contextsOpened (value : Expr) (out : List Expr) : Option Nat :=
  match (runResultM (root value out)).runState EvalState.empty with
  | (.ok _, state) => some (state.nextBindingContext - 1)
  | (.error _, _) => none

/-- 4. A fresh call operand `Id(v)` runs ONCE under every spelling — also when its supply changes
across the layers (a lone structured item) — while writing the call twice runs it twice. -/
def operandIsEvaluatedOnceUnderEverySpelling : Bool :=
  let call (value : Expr) : Expr := .call (resolve "Id") [value]
  [lit [lit [lit [n 7]]], lit [unit], lit [tup [n 1, n 2]], lit [lit [n 1, n 2], lit [n 3, n 4]]].all
    fun value =>
      contextsOpened value [call value] == some 1 &&
      contextsOpened value [call value, call value] == some 2 &&
      spellings.all fun (_, spell) => contextsOpened value [spell (call value)] == some 1

#guard operandIsEvaluatedOnceUnderEverySpelling

/-- 5. The INTERNAL join (`sequenceConstruct`, host-built only) reads a spread leaf exactly as a
written capture reads a spread row: the spread expression's items, one boundary per written star,
never reopened. The join differs from written parentheses ONLY in dropping a non-spread `()` leaf,
so with the non-empty second leaf `3` the two agree — value and emitted count — for every operand
value and every spelling. -/
def joinSpreadLeafSuppliesExactlyTheSpreadItems : Bool :=
  operandValues.all fun value =>
    spellings.all fun (_, spell) =>
      match counted (.sequenceConstruct (spell value) (n 3)), counted (.capture [spell value, n 3]) with
      | .ok (joined, joinedCount), .ok (captured, capturedCount) =>
          joined == captured && joinedCount == capturedCount
      | _, _ => false

#guard joinSpreadLeafSuppliesExactlyTheSpreadItems

/-- 6. Hand-written join observations, independent of the capture route: a LONE structured item
stays whole, a lone spread-produced `()` stays an item, a stacked leaf opens one boundary per
star — while a NON-spread `()` leaf is still dropped (join semantics). -/
def joinSpreadLeafShapesArePinned : Bool :=
  let join (leaf : Expr) : Option Result :=
    match counted (.sequenceConstruct leaf (n 3)) with
    | .ok (value, 1) => some value
    | _ => none
  join (.sequenceSpread (lit [lit [n 7]])) == some (.sequenceValue [atomList [7], .atom 3]) &&
  join (.sequenceSpread (lit [unit])) == some (.sequenceValue [.sequenceValue [], .atom 3]) &&
  join (.sequenceSpread (lit [tup [n 1, n 2]]))
    == some (.sequenceValue [.sequenceValue [.atom 1, .atom 2], .atom 3]) &&
  join (stacked2 (lit [lit [lit [n 7]]])) == some (.sequenceValue [atomList [7], .atom 3]) &&
  join (.sequenceSpread (tup [n 1, n 2])) == some (.sequenceValue [.atom 1, .atom 2, .atom 3]) &&
  join unit == some (.atom 3)

#guard joinSpreadLeafShapesArePinned

/-- A join's spread leaf evaluates its FRESH call operand once, under every spelling.
The twice-written control opens two binding contexts; property caching cannot mask replay. -/
def joinSpreadLeafEvaluatesItsOperandOnce : Bool :=
  [lit [lit [lit [n 7]]], lit [unit], lit [tup [n 1, n 2]]].all fun value =>
    let call := Expr.call (resolve "Id") [value]
    spellings.all fun (_, spell) =>
      contextsOpened value [.sequenceConstruct (spell call) (n 3)] == some 1 &&
      contextsOpened value [.sequenceConstruct (spell call) (.sequenceConstruct (spell call) (n 3))]
        == some 2

#guard joinSpreadLeafEvaluatesItsOperandOnce

end KatLangTests.RepeatedSpread
