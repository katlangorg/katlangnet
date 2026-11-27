import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate runResult Algorithm Error Result)

--------------------------------------------------------------------------------
-- Lazy finite collections and pipelines (issue #204, November 2026)
--------------------------------------------------------------------------------
-- A list evaluates its elements on demand. A list literal defers every non-constant,
-- non-spread element in its own environment; `map` defers one mapped element per source
-- position; `filter` discovers its matches by scanning the source in order, one memoized
-- verdict per candidate; `take` keeps a prefix of positions. Each position is ONE need cell,
-- so every reader of one collection instance shares its completed values, its ordinary
-- failures and its in-flight demands. The consumers read exactly what their result needs:
-- `count` the cardinality, `first` / `last` / selection the selected positions, structural
-- patterns the positions (bound unread), an explicit spread and the strict builtins one whole
-- level, evaluator equality and the run result the whole value.
--
-- Programs are written as the core AST the C# front end elaborates to; the source spelling of
-- each is in its comment.

namespace LazyCollections

private def tick : KatLang.Expr := .call (.resolve "tick") []
/-- `1 / 0`. -/
private def bad : KatLang.Expr := .binary .div (.num 1) (.num 0)
private def lst (xs : List KatLang.Expr) : KatLang.Expr := .listLiteral xs
private def dot (target : KatLang.Expr) (name : String) (args : Option (List KatLang.Expr) := none) : KatLang.Expr :=
  .dotCall target name args
/-- `{param => body}`: the block `{body}` over its one implicit parameter. -/
private def block (param : String) (body : KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (alg [param] [] [] [body])
private def n : KatLang.Expr := .param "n"
private def gt (a b : KatLang.Expr) : KatLang.Expr := .comparison a [{ op := .gt, operand := b }]
private def lt (a b : KatLang.Expr) : KatLang.Expr := .comparison a [{ op := .lt, operand := b }]
private def eq (a b : KatLang.Expr) : KatLang.Expr := .comparison a [{ op := .eq, operand := b }]
private def call (name : String) (args : List KatLang.Expr) : KatLang.Expr := .call (.resolve name) args

/-- A program: private properties, then its output rows. -/
private def program (props : List (String × Algorithm)) (rows : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] props rows)

private def value (rows : List KatLang.Expr) (props : List (String × Algorithm) := []) :
    Except Error Result := runResult (program props rows)

private def gives (r : Except Error Result) (expected : Result) : Bool :=
  match r with
  | .ok v => v == expected
  | .error _ => false

private def failsWith (check : Error → Bool) (r : Except Error Result) : Bool :=
  match r with
  | .ok _ => false
  | .error e => check e

private def innermostIsDemandCycle : Error → Bool
  | .withContext _ inner => innermostIsDemandCycle inner
  | .demandCycle => true
  | _ => false

private def atoms (xs : List Int) : Result := .listValue (xs.map Result.atom)

/-! ## The acceptance examples of the issue -/

-- [10, 1 / 0][0]
#guard gives (value [.index (lst [.num 10, bad]) [.num 0]]) (.atom 10)

-- [1, 2].map{if(n == 1, 10, 1 / 0)}.first
#guard gives
  (value [dot (dot (lst [.num 1, .num 2]) "map" (some [block "n" (call "if" [eq n (.num 1), .num 10, bad])])) "first"])
  (.atom 10)

-- [1, 0].filter{1 / n > 0}.take(1)
#guard gives
  (value [dot (dot (lst [.num 1, .num 0]) "filter" (some [block "n" (gt (.binary .div (.num 1) n) (.num 0))]))
    "take" (some [.num 1])])
  (atoms [1])

/-! ## Sharing and demand order -/

/-- `L = [tick(), tick(), tick()]`. -/
private def threeTicks : Algorithm := alg [] [] [] [lst [tick, tick, tick]]

-- L[2, 0, 2], L[0], tick(): the positions run in the order they are first selected, a repeated
-- selector and a later read reuse the completed position, and the row `tick()` runs last.
#guard gives
  (value [.index (.resolve "L") [.num 2, .num 0, .num 2], .index (.resolve "L") [.num 0], tick] [("L", threeTicks)])
  (.sequenceValue [.sequenceValue [.atom 1, .atom 2, .atom 1], .atom 2, .atom 3])

-- L = [tick()] with the rows `L, tick()`: the scalar row runs while the output is assembled;
-- the run result then materializes the list.
#guard gives (value [.resolve "L", tick] [("L", alg [] [] [] [lst [tick]])])
  (.sequenceValue [atoms [2], .atom 1])

-- A position read through a forwarded argument, a dotted read and the property share one
-- completion: `Head(xs) = xs[0]` with the rows `Head(L), L.first, L[0], tick()`.
#guard gives
  (value [call "Head" [.resolve "L"], dot (.resolve "L") "first", .index (.resolve "L") [.num 0], tick]
    [("L", threeTicks), ("Head", alg ["xs"] [] [] [.index (.param "xs") [.num 0]])])
  (.sequenceValue [.atom 1, .atom 1, .atom 1, .atom 2])

-- A fresh invocation builds a fresh collection: `Make() = [tick()]` with `Make()[0], Make()[0]`.
#guard gives (value [.index (call "Make" []) [.num 0], .index (call "Make" []) [.num 0]]
    [("Make", alg [] [] [] [lst [tick]])])
  (.sequenceValue [.atom 1, .atom 2])

/-! ## List literals -/

-- A written constant is its value and an explicit spread is formed during construction:
-- `[(1 / 0)*].count` fails, `[1 / 0].count` is 1.
#guard failsWith innermostIsDivByZero (value [dot (lst [.sequenceSpread (.capture [bad])]) "count"])
#guard gives (value [dot (lst [bad]) "count"]) (.atom 1)

-- Each position holds one whole value: `[(), [], [1 / 0]].count` is 3 and the nested list's
-- element stays unread by `[[1, 1 / 0], 2][0][0]`.
#guard gives (value [dot (lst [.emptySequence 0, lst [], lst [bad]]) "count"]) (.atom 3)
#guard gives (value [.index (.index (lst [lst [.num 1, bad], .num 2]) [.num 0]) [.num 0]]) (.atom 1)

-- An unread element's failure never surfaces: `[1 / 0, 7].last` is 7.
#guard gives (value [dot (lst [bad, .num 7]) "last"]) (.atom 7)

/-! ## map -/

-- Counting a map of known length reads neither an element nor the mapper: `count(map([1, 2], 7))`.
#guard gives (value [call "count" [call "map" [lst [.num 1, .num 2], .num 7]]]) (.atom 2)

-- A mapped position reads its source item FIRST, then projects the mapper:
-- `first(map([1 / 0], 7))` is the division, `first(map([1], 7))` the mapper's rejection.
#guard failsWith innermostIsDivByZero (value [call "first" [call "map" [lst [bad], .num 7]]])
#guard failsWith (innermostIsNotAnAlgorithm "map transform") (value [call "first" [call "map" [lst [.num 1], .num 7]]])

-- An empty collection is `[]` at once: `map([], 7)`.
#guard gives (value [call "map" [lst [], .num 7]]) (atoms [])

-- The mapper runs once per demanded position and its result is shared:
-- `M = [1, 2, 3].map{n * tick()}` with `M[2], M[2], M[0], tick()`.
#guard gives
  (value [.index (.resolve "M") [.num 2], .index (.resolve "M") [.num 2], .index (.resolve "M") [.num 0], tick]
    [("M", alg [] [] [] [dot (lst [.num 1, .num 2, .num 3]) "map" (some [block "n" (.binary .mul n tick)])])])
  (.sequenceValue [.atom 3, .atom 3, .atom 2, .atom 3])

/-! ## filter -/

/-- `Big(n) = tick() > 0 and n > 2`: every invocation is one `tick`. -/
private def bigAlg : Algorithm :=
  alg ["n"] [] [] [.binary .and (gt tick (.num 0)) (gt n (.num 2))]

/-- `F = [1, 2, 3, 4].filter(Big)`. -/
private def filteredAlg : Algorithm :=
  alg [] [] [] [dot (lst [.num 1, .num 2, .num 3, .num 4]) "filter" (some [.resolve "Big"])]

private def filterProps : List (String × Algorithm) := [("Big", bigAlg), ("F", filteredAlg)]

-- The scan stops at the requested match and a repeated read invokes nothing:
-- `F.first, F.first, tick()` is `3, 3, 4` (three predicate calls).
#guard gives (value [dot (.resolve "F") "first", dot (.resolve "F") "first", tick] filterProps)
  (.sequenceValue [.atom 3, .atom 3, .atom 4])

-- It resumes after the candidates already inspected, rejections included:
-- `F[0], F[1], tick()` is `3, 4, 5`.
#guard gives (value [.index (.resolve "F") [.num 0], .index (.resolve "F") [.num 1], tick] filterProps)
  (.sequenceValue [.atom 3, .atom 4, .atom 5])

-- `count` scans to exhaustion once: `F.count, F.first, F.last, tick()` is `2, 3, 4, 5`.
#guard gives
  (value [dot (.resolve "F") "count", dot (.resolve "F") "first", dot (.resolve "F") "last", tick] filterProps)
  (.sequenceValue [.atom 2, .atom 3, .atom 4, .atom 5])

-- A position that does not exist is `badIndex` after the scan: `F[2]`.
#guard failsWith innermostIsBadIndex (value [.index (.resolve "F") [.num 2]] filterProps)

-- The first failure ends the scan; a read that stops before it succeeds:
-- `[1, 0, 5].filter{1 / n > 0}` has `[0]` = 1 while its count fails.
private def failing : KatLang.Expr :=
  dot (lst [.num 1, .num 0, .num 5]) "filter" (some [block "n" (gt (.binary .div (.num 1) n) (.num 0))])
#guard gives (value [.index failing [.num 0]]) (.atom 1)
#guard failsWith innermostIsDivByZero (value [dot failing "count"])

-- The predicate must return a Boolean value: `[1].filter{n}.count`.
#guard failsWith (innermostIsBooleanRequired "filter predicate result" "numeric value 1")
  (value [dot (dot (lst [.num 1]) "filter" (some [block "n" n])) "count"])

-- An empty or unused stage projects no callback: `[].filter(7)` is `[]` and
-- `[1].filter(7).take(0)` is `[]`; a demanded verdict reports the predicate.
#guard gives (value [dot (lst []) "filter" (some [.num 7])]) (atoms [])
#guard gives (value [dot (dot (lst [.num 1]) "filter" (some [.num 7])) "take" (some [.num 0])]) (atoms [])
#guard failsWith (innermostIsNotAnAlgorithm "filter predicate")
  (value [dot (dot (lst [.num 1]) "filter" (some [.num 7])) "count"])

-- The kept items are the source's own positions: `[tick(), tick()].filter{n > 0}` reads each
-- source element once, however often the result is read.
#guard gives
  (value [dot (.resolve "K") "count", .resolve "K", tick]
    [("K", alg [] [] [] [dot (lst [tick, tick]) "filter" (some [block "n" (gt n (.num 0))])])])
  (.sequenceValue [.atom 2, atoms [1, 2], .atom 3])

/-! ## Pipelines -/

-- Alternating stages stop at the requested prefix:
-- `[1, 2, 3, 4, 1 / 0].filter{n > 1}.map{n * 10}.filter{n < 40}.take(2)` is `[20, 30]`.
#guard gives
  (value [dot
    (dot (dot (dot (lst [.num 1, .num 2, .num 3, .num 4, bad]) "filter" (some [block "n" (gt n (.num 1))]))
      "map" (some [block "n" (.binary .mul n (.num 10))]))
      "filter" (some [block "n" (lt n (.num 40))]))
    "take" (some [.num 2])])
  (atoms [20, 30])

-- A pipeline built in one call and consumed in another:
-- `Evens(xs) = xs.filter{n mod 2 == 0}.map{n * n}` with `Evens([1, 2, 3, 4, 1 / 0])[1]` is 16.
#guard gives
  (value [.index (call "Evens" [lst [.num 1, .num 2, .num 3, .num 4, bad]]) [.num 1]]
    [("Evens", alg ["xs"] [] [] [dot
      (dot (.param "xs") "filter" (some [block "n" (eq (.binary .mod n (.num 2)) (.num 0))]))
      "map" (some [block "n" (.binary .mul n n)])])])
  (.atom 16)

-- A mapped pending list is discovered by the source's verdicts alone:
-- `[1, 2, 3].filter{n > 1}.map(7).count` is 2 (the mapper is never projected).
#guard gives
  (value [dot (dot (dot (lst [.num 1, .num 2, .num 3]) "filter" (some [block "n" (gt n (.num 1))])) "map"
    (some [.num 7])) "count"])
  (.atom 2)

/-! ## take -/

-- `take` validates its count before any position: `[1 / 0].take(true)` is the count's kind error.
#guard failsWith (fun e => !innermostIsDivByZero e) (value [dot (lst [bad]) "take" (some [.boolLiteral true])])

-- It returns a prefix of positions sharing upstream state: `[1 / 0, 2].take(1).count` is 1,
-- and `[tick(), tick()].take(5)` is `[1, 2]`.
#guard gives (value [dot (dot (lst [bad, .num 2]) "take" (some [.num 1])) "count"]) (.atom 1)
#guard gives (value [dot (lst [tick, tick]) "take" (some [.num 5])]) (atoms [1, 2])

-- A non-positive count reads nothing: `F.take(0), tick()` is `[], 1`.
#guard gives (value [dot (.resolve "F") "take" (some [.num 0]), tick] filterProps)
  (.sequenceValue [atoms [], .atom 1])

-- A downstream `first` stops at the first match however large the count:
-- `F.take(100).first, tick()` is `3, 4`.
#guard gives (value [dot (dot (.resolve "F") "take" (some [.num 100])) "first", tick] filterProps)
  (.sequenceValue [.atom 3, .atom 4])

-- A filled quota ends the scan: `F.take(1).count, tick()` is `1, 4` (three predicate calls).
#guard gives (value [dot (dot (.resolve "F") "take" (some [.num 1])) "count", tick] filterProps)
  (.sequenceValue [.atom 1, .atom 4])

/-! ## Postfix selection -/

-- Bounds are checked against a known cardinality before any element is read:
-- `[1 / 0, 2][5]` is `badIndex`, `[1 / 0, 2][true]` the selector's kind error.
#guard failsWith innermostIsBadIndex (value [.index (lst [bad, .num 2]) [.num 5]])
#guard failsWith (fun e => !innermostIsDivByZero e && !innermostIsBadIndex e)
  (value [.index (lst [bad, .num 2]) [.boolLiteral true]])

-- The selectors run in written order and the first failure ends the selection:
-- `[tick(), 1 / 0, tick()][2, 1, 0]` fails after one `tick`; `[7, 1 / 0][0, 0]` is `(7, 7)`.
#guard failsWith innermostIsDivByZero (value [.index (lst [tick, bad, tick]) [.num 2, .num 1, .num 0]])
#guard gives (value [.index (lst [.num 7, bad]) [.num 0, .num 0]]) (.sequenceValue [.atom 7, .atom 7])

/-! ## Structural patterns -/

/-- `Fst([x, y]) = x`. -/
private def fstAlg : Algorithm :=
  algWithParameterPatterns [.listValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"]
/-- `Snd([x, y]) = y`. -/
private def sndAlg : Algorithm :=
  algWithParameterPatterns [.listValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"]
/-- `Rest([x, *rest]) = rest.count`. -/
private def restAlg : Algorithm :=
  algWithParameterPatterns
    [.listValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] []
    [dot (.param "rest") "count"]
/-- `Pair((x, y)) = x`. -/
private def pairAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"]

-- Names bind to the original positions, unread: `Fst([1, 1 / 0])` is 1, `Snd([1, 1 / 0])` fails.
#guard gives (value [call "Fst" [lst [.num 1, bad]]] [("Fst", fstAlg)]) (.atom 1)
#guard failsWith innermostIsDivByZero (value [call "Snd" [lst [.num 1, bad]]] [("Snd", sndAlg)])

-- Cardinality is checked before any field: `Fst([1 / 0])` is the group's arity error.
#guard failsWith (innermostIsArityMismatch 2 1) (value [call "Fst" [lst [bad]]] [("Fst", fstAlg)])

-- A collecting binding collects positions, not values: `Rest([1, 1 / 0, 1 / 0])` is 2.
#guard gives (value [call "Rest" [lst [.num 1, bad, bad]]] [("Rest", restAlg)]) (.atom 2)

-- The kind is checked without reading an element: `Pair([1 / 0, 2])` is the kind error.
#guard failsWith (fun e => !innermostIsDivByZero e) (value [call "Pair" [lst [bad, .num 2]]] [("Pair", pairAlg)])

-- A bound position shares the list's completion: `Twice([x, y]) = x + x` over `[tick(), tick()]`.
#guard gives
  (value [call "Twice" [.resolve "L"], .index (.resolve "L") [.num 0], tick]
    [("L", threeTicks),
     ("Twice", algWithParameterPatterns
        [.listValue [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]] [] []
        [.binary .add (.param "x") (.param "x")])])
  (.sequenceValue [.atom 2, .atom 1, .atom 2])

/-- `Kind(0) = 100` / `Kind(xs) = 7`: a scalar literal clause, then a plain binder. -/
private def kindFamily : Algorithm :=
  .conditional none [] [
    ⟨.litInt 0, alg [] [] [] [.num 100]⟩,
    ⟨.bind "xs", alg [] [] [] [.num 7]⟩]

-- A scalar literal rejects a list by kind WITHOUT scanning it: the pending list's predicate
-- would fail on its first candidate, and `Kind` never invokes it.
#guard gives
  (value [call "Kind" [dot (lst [.num 1, .num 2]) "filter" (some [block "n" (gt bad (.num 0))])]]
    [("Kind", kindFamily)])
  (.atom 7)

/-- `Shape([]) = 0` / `Shape([a, r]) = a`. -/
private def shapeFamily : Algorithm :=
  .conditional none [] [
    ⟨.listValue [], alg [] [] [] [.num 0]⟩,
    ⟨.listValue [.bind "a", .bind "r"], alg [] [] [] [.param "a"]⟩]

-- A list pattern discovers a pending list's positions (the empty-list pattern needs its
-- length) and the clause attempts share that discovery:
-- `Shape([1, 2, 3].filter(Big2))` with `Big2(n) = tick() > 0 and n > 1` is 2 after three calls.
#guard gives
  (value [call "Shape" [dot (lst [.num 1, .num 2, .num 3]) "filter" (some [.resolve "Big2"])], tick]
    [("Big2", alg ["n"] [] [] [.binary .and (gt tick (.num 0)) (gt n (.num 1))]), ("Shape", shapeFamily)])
  (.sequenceValue [.atom 2, .atom 4])

/-- `Same(x, x) = 1`. -/
private def sameAlg : Algorithm := alg ["x", "x"] [] [] [.num 1]

-- Repeated-name agreement compares WHOLE values: `Same([1, 1 + 1], [1, 2])` agrees, and
-- `Same([1], [1 / 0])` reads the second list's element.
#guard gives (value [call "Same" [lst [.num 1, .binary .add (.num 1) (.num 1)], lst [.num 1, .num 2]]]
    [("Same", sameAlg)]) (.atom 1)
#guard failsWith innermostIsDivByZero (value [call "Same" [lst [.num 1], lst [bad]]] [("Same", sameAlg)])

/-! ## Explicit spread and the strict builtins -/

/-- `Count(*xs) = xs.count`. -/
private def countAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] [] [dot (.param "xs") "count"]

-- A spread reads the level it opens, in order, and keeps nested values as they are:
-- `Count([1 / 0, 2]*)` fails, `Count([[1 / 0], 2]*)` is 2.
#guard failsWith innermostIsDivByZero
  (value [call "Count" [.sequenceSpread (lst [bad, .num 2])]] [("Count", countAlg)])
#guard gives (value [call "Count" [.sequenceSpread (lst [lst [bad], .num 2])]] [("Count", countAlg)]) (.atom 2)

-- A spread discovers a pending list: `Count(F*)` is 2.
#guard gives (value [call "Count" [.sequenceSpread (.resolve "F")]] (("Count", countAlg) :: filterProps))
  (.atom 2)

-- A strict builtin reads every position of its collection, in order:
-- `sum([1, 2 * 3])` is 7 and `skip([1 / 0, 2], 1)` fails.
#guard gives (value [call "sum" [lst [.num 1, .binary .mul (.num 2) (.num 3)]]]) (.atom 7)
#guard failsWith innermostIsDivByZero (value [call "skip" [lst [bad, .num 2], .num 1]])

-- `reduce` obtains the complete collection before its reducer runs:
-- `reduce([1, 1 / 0], Pick, 0)` with `Pick(item, acc) = 5` fails.
#guard failsWith innermostIsDivByZero
  (value [call "reduce" [lst [.num 1, bad], .resolve "Pick", .num 0]]
    [("Pick", alg ["item", "acc"] [] [] [.num 5])])

/-! ## Evaluator equality -/

-- `==` / `!=` compare whole values: `[1, 1 + 1] == [1, 2]`, `[[1 + 1]] != [[3]]`.
#guard gives (value [eq (lst [.num 1, .binary .add (.num 1) (.num 1)]) (lst [.num 1, .num 2])]) (.bool true)
#guard gives
  (value [.comparison (lst [lst [.binary .add (.num 1) (.num 1)]]) [{ op := .ne, operand := lst [lst [.num 3]] }]])
  (.bool true)

-- The left operand is materialized before the right one:
-- `[tick()] == [tick()]` compares `[1]` with `[2]`.
#guard gives (value [eq (lst [tick]) (lst [tick])]) (.bool false)
#guard failsWith innermostIsDivByZero (value [eq (lst [.num 1]) (lst [bad])])

-- `contains` and `distinct` compare whole values too.
#guard gives (value [dot (lst [lst [.num 1, .binary .add (.num 1) (.num 1)]]) "contains" (some [lst [.num 1, .num 2]])])
  (.bool true)
#guard gives
  (value [dot (dot (lst [lst [.binary .add (.num 0) (.num 1)], lst [.num 1]]) "distinct") "count"]) (.atom 1)

/-! ## The run result -/

-- Within a value each position is completed before the next, left to right and depth first:
-- `[[tick(), tick()], tick()], [tick()]` is `[[1, 2], 3], [4]`.
#guard gives (value [lst [lst [tick, tick], tick], lst [tick]])
  (.sequenceValue [.listValue [atoms [1, 2], .atom 3], atoms [4]])

-- A pending list in the output is discovered and read candidate by candidate:
-- `[tick(), tick()].filter{tick() > 0}` reads element, verdict, element, verdict: `[1, 3]`.
#guard gives (value [dot (lst [tick, tick]) "filter" (some [block "n" (gt tick (.num 0))])]) (atoms [1, 3])

-- A failing position fails the run: `[1, 1 / 0]`.
#guard failsWith innermostIsDivByZero (value [lst [.num 1, bad]])

/-! ## Demand cycles -/

-- A position that needs itself is a demand cycle: `L = [L[0]]` with `L[0]`.
#guard failsWith innermostIsDemandCycle
  (value [.index (.resolve "L") [.num 0]] [("L", alg [] [] [] [lst [.index (.resolve "L") [.num 0]]])])

-- A list may hold itself through a deferred position: `L = [L]` has one element, and
-- materializing it meets its own position again.
#guard gives (value [dot (.resolve "L") "count"] [("L", alg [] [] [] [lst [.resolve "L"]])]) (.atom 1)
#guard failsWith innermostIsDemandCycle (value [.resolve "L"] [("L", alg [] [] [] [lst [.resolve "L"]])])

-- A filter whose predicate reads the collection being scanned re-enters its own verdict:
-- `S = [1].filter{S.count > 0}` with `S.count`.
#guard failsWith innermostIsDemandCycle
  (value [dot (.resolve "S") "count"]
    [("S", alg [] [] [] [dot (lst [.num 1]) "filter" (some [block "n" (gt (dot (.resolve "S") "count") (.num 0))])])])

/-! ## The C#-only boundaries

`SEMANTIC-ALIGNMENT.md` records three C#-only behaviors of lazy collections. Each C# observation is
the Lean one below plus one host policy; these guards pin the Lean side, `LazyCollectionTests`
checks the paired C# programs, and `KatLangArityLaws/LazyCollectionBoundaries.lean` states
the Lean law each one rests on. -/

-- STAGE-SITE FRAMES (`discover_verdict_failure`). `count(filter([1, 2], {x}))` reports the consumer's
-- frame around the step's own failure, and no frame for the written `filter` call: C# adds exactly
-- `while evaluating call to filter` between them.
#guard match value [call "count" [call "filter" [lst [.num 1, .num 2], block "x" (.param "x")]]] with
  | .error (.withContext "while evaluating call to count"
      (.typeMismatch "filter predicate result must be a Boolean value (true or false), but was numeric value 1")) =>
    true
  | _ => false
-- `[1, 2].map{x / 0}.first`: the consumer's frame, the step's own `map transform` frame, the division.
-- C# adds `while evaluating dotCall .map of [1, 2]` between the first two.
#guard match value [dot (dot (lst [.num 1, .num 2]) "map" (some [block "x" (.binary .div (.param "x") (.num 0))])) "first"] with
  | .error (.withContext _ (.withContext step .divByZero)) => step.startsWith "while evaluating map transform"
  | _ => false

-- RESERVATIONS (`mapItems_positions`, `filterItems_candidates`). A literal's and a `map` stage's
-- cardinality is known when it is built, and counting reads no position: `[1, 2, 3].map{x / 0}.count`
-- is 3 — C# reserves 3 + 3 positions then, so a cumulative budget below 6 refuses the run before any
-- position is read. A `filter`'s cardinality is its accepted candidates': `[1, 2, 3].filter{x > 1}.count`
-- is 2 — C# reserves those 2 when the scan completes (budget 3 + 2).
#guard gives (value [dot (lst [.num 1, .num 2, .num 3]) "count"]) (.atom 3)
#guard gives (value [dot (dot (lst [.num 1, .num 2, .num 3]) "map" (some [block "x" (.binary .div (.param "x") (.num 0))]))
  "count"]) (.atom 3)
#guard gives (value [dot (dot (lst [.num 1, .num 2, .num 3]) "filter" (some [block "x" (gt (.param "x") (.num 1))]))
  "count"]) (.atom 2)

-- A map over the same pending scan: counting discovers two matches; reading the map whole also
-- computes their two mapped values. C# reserves 5 positions for the count and 7 for the whole read.
private def mappedScan : KatLang.Expr :=
  dot (dot (lst [.num 1, .num 2, .num 3]) "filter" (some [block "x" (gt (.param "x") (.num 1))]))
    "map" (some [block "x" (.binary .add (.param "x") (.num 1))])
#guard gives (value [dot mappedScan "count"]) (.atom 2)
#guard gives (value [mappedScan]) (atoms [3, 4])

-- READ GENERATIONS (`materializePosition_on_path`, `materializePosition_fresh`,
-- `recursiveMap_wholeRead_incomplete`). Lean has no depth bound:
-- `Nest(n) = if(n == 0, [7], [Nest(n - 1)])` read whole is `[7]` at 100 AND at 200 nested calls, while C#
-- ends `atoms(Nest(200))` with `EvaluationDepthExceeded` after 128 read generations.
private def nestAlg : Algorithm :=
  alg ["n"] [] [] [call "if" [eq n (.num 0), lst [.num 7], lst [call "Nest" [.binary .sub n (.num 1)]]]]
#guard gives (value [call "atoms" [call "Nest" [.num 100]]] [("Nest", nestAlg)]) (atoms [7])
#guard gives (value [call "atoms" [call "Nest" [.num 200]]] [("Nest", nestAlg)]) (atoms [7])

/-- The run's core VALUE read at a fixed fuel. Exhaustion describes this approximation. -/
private def fuelValue (fuel : Nat) (rows : List KatLang.Expr) (props : List (String × Algorithm)) :
    Except Error Result :=
  let e := (KatLang.identifyPropertyExpr (program props rows)).run' 0
  match (KatLang.evalFuel fuel (.evalRunValue e { callStack := [KatLang.preludeAlg] } [])).runState
      KatLang.EvalState.empty with
  | (r, _) => r

-- Building and counting F(1) leaves its one mapped position suspended. Reading that position
-- invokes F and returns a list with a fresh position. C# ends the whole read with
-- `EvaluationDepthExceeded`. A self-containing list (`L = [L]`, above) is `demandCycle` in both.
private def fAlg : Algorithm := alg ["x"] [] [] [dot (lst [.param "x"]) "map" (some [.resolve "F"])]

/-- The fixed-fuel whole read of `F(1)` for `F(x) = [x].map(F)`. The finite guard below and
    `RecursiveMapWholeRead.fuelValue_F1_incomplete` both use this observation. -/
def recursiveMapWholeReadAt (fuel : Nat) : Except Error Result :=
  fuelValue fuel [call "F" [.num 1]] [("F", fAlg)]

-- The count is the positive control, both through runResult and at fuel 1,000.
#guard gives (value [dot (call "F" [.num 1]) "count"] [("F", fAlg)]) (.atom 1)
#guard [50, 200, 1000].all fun fuel =>
  match recursiveMapWholeReadAt fuel with
  | .error .fuelExhausted => true
  | _ => false
#guard gives (fuelValue 1000 [dot (call "F" [.num 1]) "count"] [("F", fAlg)]) (.atom 1)

end LazyCollections

end KatLangTests
