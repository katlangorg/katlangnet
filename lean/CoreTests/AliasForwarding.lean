import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameterPatterns algPrivate runResultM Algorithm Error Result EvalState
  ParameterPattern Pattern sourceCall bareForwardingRow bareForwardingArguments)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- Aliases, bare forwarding and written calls (FWD-02, decided 2026-09-29–30)
--------------------------------------------------------------------------------
-- A body whose ONE written row is a bare reference to a callable that declares
-- parameters (`aliasesLoneBareReference`) is not a formula:
--   * `A = F` is an EXACT ALIAS: `A` takes `F`'s parameter patterns verbatim and
--     calls `F` with them rebuilt (`sourceCall F signature`), so `A(S)` behaves as
--     `F(S)` for every argument supply `S`;
--   * `G(params) = F` is BARE FORWARDING: each of `F`'s parameters is supplied from an
--     EXISTING compatible binding of the SAME NAME (`bareForwardingRow`) — G's own
--     top-level parameter, else an enclosing parameter binding (Q-04) — never renamed,
--     never matched by position, never added to G's closed list, and never reshaped
--     from same-named leaves; a parameter nothing supplies rejects the definition;
--   * `G(params) = F(exprs)` is an ORDINARY WRITTEN CALL, whose arguments need not
--     match F's names — deliberately NOT the same thing as the bare row;
--   * `G = F(exprs)` is a FORMULA whose parameters are the free names written in
--     `exprs`: `G = Add((x, y))` is `G(x, y) = Add((x, y))`, whatever `Add` calls its
--     binders.
-- Lean models no elaboration (no parameter detection, no signature construction):
-- the alias and bare-forwarding trees below are BUILT with the Lean specification
-- functions, the written-call trees are the detector's output, hand-encoded, and the
-- guards evaluate them. The C# front end produces the same trees
-- (`ImplicitArgumentResolver.TryCompleteLoneCalleeRow`), which the derived programs of
-- the `alias-*`, `bare-forwarding-*` and `written-call-*` spec cases and the `alias*` /
-- `bareForwarding*` / `writtenCall*` explorer specials check against Lean.
--
-- Evaluation-count evidence without host operations (as in
-- `RepeatedNameConstraints.lean`): every user call whose parameters BIND opens one
-- binding context, so an alias or a forwarding definition adds exactly ONE context —
-- its own — and an argument whose evaluation opens contexts (`Id(7)`) is evaluated once
-- however many levels hand it on.

def afCap (name : String) : ParameterPattern := .capture { name := name }

def afColl (name : String) : ParameterPattern := .capture { name := name, kind := .collecting }

/-- `Single([x]) = x`: one list parameter. -/
def afSingleSignature : List ParameterPattern := [.listValue [afCap "x"]]

/-- `Add((a, b)) = a + b` and its binder-renamed twin `AddR((left, right)) = left + right`. -/
def afAddSignature : List ParameterPattern := [.sequenceValue [afCap "a", afCap "b"]]

/-- `P(x, x) = x`: a repeated-name constraint (Q-05). -/
def afPSignature : List ParameterPattern := [afCap "x", afCap "x"]

/-- `E((), []) = 1`: two binderless structural parameters. -/
def afESignature : List ParameterPattern := [.sequenceValue [], .listValue []]

/-- `Coll(*xs) = xs`: a collector-only callee — it works with no arguments too. -/
def afCollSignature : List ParameterPattern := [afColl "xs"]

/-- `LC([*xs]) = xs` and `SC((*xs)) = xs`: the one-list and the one-sequence collectors. -/
def afLCSignature : List ParameterPattern := [.listValue [afColl "xs"]]

def afSCSignature : List ParameterPattern := [.sequenceValue [afColl "xs"]]

/-- `Mid([first, *middle, last]) = [first, middle, last]`. -/
def afMidSignature : List ParameterPattern := [.listValue [afCap "first", afColl "middle", afCap "last"]]

/-- `Sub(y, x) = y - x`: its parameters in the order opposite to `G(x, y)`'s. -/
def afSubSignature : List ParameterPattern := [afCap "y", afCap "x"]

/-- The elaborated exact alias of `callee`, whose signature is `signature`. -/
def afAlias (callee : String) (signature : List ParameterPattern) : Algorithm :=
  algWithParameterPatterns signature [] [] [sourceCall callee signature]

/-- The names a closed parameter list binds, at any depth. -/
def afNames (own : List ParameterPattern) : List String :=
  (own.flatMap ParameterPattern.captures).map (fun parameter => parameter.name)

/-- The row bare forwarding elaborates `name(own) = callee` to, for a callee whose signature is
    `signature`, with `captured` the enclosing parameter bindings (Q-04). A rejected row would
    read an undeclared name, so a guard that evaluates it fails loudly. -/
def afBareRow (callee : String) (own : List ParameterPattern) (signature : List ParameterPattern)
    (captured : List KatLang.CallableParameter := []) : KatLang.Expr :=
  (bareForwardingRow callee own (afNames own) captured signature).getD (resolve "$rejected")

/-- The elaborated bare-forwarding definition `name(own) = callee`. -/
def afBare (callee : String) (own : List ParameterPattern) (signature : List ParameterPattern)
    (captured : List KatLang.CallableParameter := []) : Algorithm :=
  algWithParameterPatterns own [] [] [afBareRow callee own signature captured]

def afCall (callee : String) (args : List KatLang.Expr) : KatLang.Expr := .call (resolve callee) args

/-- A bare-forwarding clause branch `name(head) = callee`, elaborated. -/
def afBranch (callee : String) (head : Pattern) (signature : List ParameterPattern) : KatLang.CondBranch :=
  { pattern := head
    body := alg [] [] []
      [(bareForwardingRow callee (Pattern.bareForwardingOwn head) head.boundNames [] signature).getD
        (resolve "$rejected")] }

def afRoot (out : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [ ("Single", algWithParameterPatterns afSingleSignature [] [] [param "x"])
    , ("Add", algWithParameterPatterns afAddSignature [] [] [.binary .add (param "a") (param "b")])
    , ("AddR", algWithParameterPatterns [.sequenceValue [afCap "left", afCap "right"]] [] []
        [.binary .add (param "left") (param "right")])
    , ("P", algWithParameterPatterns afPSignature [] [] [param "x"])
    , ("E", algWithParameterPatterns afESignature [] [] [num 1])
    , ("Coll", algWithParameterPatterns afCollSignature [] [] [param "xs"])
    , ("LC", algWithParameterPatterns afLCSignature [] [] [param "xs"])
    , ("SC", algWithParameterPatterns afSCSignature [] [] [param "xs"])
    , ("Mid", algWithParameterPatterns afMidSignature [] []
        [.listLiteral [param "first", param "middle", param "last"]])
    , ("Id", alg ["v"] [] [] [param "v"])
    , ("Bad", alg [] [] [] [.binary .div (.call (resolve "Id") [num 1]) (num 0)])
    , ("Inc", alg ["z"] [] [] [.binary .add (param "z") (num 1)])
    , ("Double", alg ["x"] [] [] [.binary .mul (param "x") (num 2)])
    , ("Other", alg ["y"] [] [] [.binary .mul (param "y") (num 2)])
    , ("Sub", algWithParameterPatterns afSubSignature [] [] [.binary .sub (param "y") (param "x")])
    , ("Ten", alg [] [] [] [num 10])
    , ("F10", alg ["n"] [] [] [.binary .mul (param "n") (num 10)])
    -- Exact aliases, among them a three-level chain.
    , ("A", afAlias "Single" afSingleSignature), ("B", afAlias "A" afSingleSignature)
    , ("C", afAlias "B" afSingleSignature)
    , ("AAdd", afAlias "Add" afAddSignature), ("AP", afAlias "P" afPSignature)
    , ("AE", afAlias "E" afESignature), ("AColl", afAlias "Coll" afCollSignature)
    , ("ALC", afAlias "LC" afLCSignature), ("ASC", afAlias "SC" afSCSignature)
    , ("AMid", afAlias "Mid" afMidSignature)
    -- Bare forwarding by name.
    , ("Forward", afBare "Double" [afCap "x"] [afCap "x"])
    , ("ForwardUnused", afBare "Double" [afCap "x", afCap "unused"] [afCap "x"])
    , ("GSub", afBare "Sub" [afCap "x", afCap "y"] afSubSignature)
    , ("SameShape", afBare "Single" afSingleSignature afSingleSignature)
    , ("GPair", afBare "Add" afAddSignature afAddSignature)
    , ("GColl", afBare "Coll" [afColl "xs"] afCollSignature)
    , ("GOne", afBare "Coll" [afCap "xs"] afCollSignature)
    , ("GList", afBare "Id" [afColl "v"] [afCap "v"])
    , ("GMid", afBare "Mid" afMidSignature afMidSignature)
    , ("GP", afBare "P" [afCap "x"] afPSignature)
    , ("GRead", afBare "Coll" [afCap "p"] afCollSignature)
    , ("Always", alg ["p"] [] [] [resolve "Ten"])
    , ("W", Algorithm.elaborateClauseGroup
        [{ pattern := .litInt 0, body := alg [] [] [] [num 0] }, afBranch "F10" (.bind "n") [afCap "n"]])
    -- Q-04: a name the local list does not bind is the enclosing parameter binding; a local
    -- parameter of the same name is nearer.
    , ("OuterX", algPrivate ["v"] []
        [("Local", afBare "Id" [afCap "y"] [afCap "v"] [{ name := "v" }])] [afCall "Local" [num 5]])
    , ("OuterOwn", algPrivate ["v"] []
        [("Local", afBare "Id" [afCap "v"] [afCap "v"] [{ name := "v" }])] [afCall "Local" [num 5]])
    -- Explicit calls and written-call formulas: the detector's trees, hand-encoded.
    , ("Explicit", alg ["x"] [] [] [.call (resolve "Single") [param "x"]])
    , ("ExplicitOther", alg ["x"] [] [] [.call (resolve "Other") [param "x"]])
    , ("GSubExplicit", alg ["x", "y"] [] [] [.call (resolve "Sub") [param "x", param "y"]])
    , ("Construct", alg ["x"] [] [] [.call (resolve "Single") [.listLiteral [param "x"]]])
    , ("F", alg ["x", "y"] [] [] [.call (resolve "Add") [.capture [param "x", param "y"]]])
    , ("FR", alg ["x", "y"] [] [] [.call (resolve "AddR") [.capture [param "x", param "y"]]])
    -- Formula lifting (H): `Formula = Double + 1` is `Formula(x) = Double(x) + 1`.
    , ("Formula", alg ["x"] [] [] [.binary .add (.call (resolve "Double") [param "x"]) (num 1)]) ]
    out)

/-- The outcome of a run AND the binding contexts it opened, kept for a FAILED run too. -/
def afRun (out : List KatLang.Expr) : Except Error Result × Nat :=
  let (result, state) := (runResultM (afRoot out)).runState EvalState.empty
  (result, state.nextBindingContext - 1)

def afSucceedsWith (out : List KatLang.Expr) (expected : Result) : Bool :=
  match (afRun out).fst with
  | .ok value => value == expected
  | .error _ => false

def afFailsWith (check : Error -> Bool) (out : List KatLang.Expr) : Bool :=
  match (afRun out).fst with
  | .error err => check err
  | .ok _ => false

def afInnermost : Error -> Error
  | .withContext _ inner => afInnermost inner
  | error => error

/-- Two outcomes agree modulo evaluation-context frames: the same value, or the same innermost
    error (an alias is its own callable, so its call adds one frame of its own). -/
def afSameOutcome : Except Error Result -> Except Error Result -> Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => reprStr (afInnermost left) == reprStr (afInnermost right)
  | _, _ => false

-- 1. The alias's reconstruction: one argument per inherited pattern, each as its own kind.
#guard reprStr (ParameterPattern.sourceArguments afSingleSignature) == reprStr [KatLang.Expr.listLiteral [param "x"]]
#guard reprStr (ParameterPattern.sourceArguments afPSignature) == reprStr [param "x", param "x"]
#guard reprStr (ParameterPattern.sourceArguments afESignature)
  == reprStr [KatLang.Expr.emptySequence 0, .listLiteral []]
#guard reprStr (ParameterPattern.sourceArguments afMidSignature)
  == reprStr [KatLang.Expr.listLiteral [param "first", .sequenceSpread (param "middle"), param "last"]]
#guard reprStr (ParameterPattern.sourceArguments [.sequenceValue [afColl "xs"]])
  == reprStr [KatLang.Expr.capture [.sequenceSpread (param "xs")]]

-- 2. THE ALIAS LAW: an alias — directly and through a three-level chain — has its callee's
--    outcome for every supply: the same value, or the same failure.
def afSupplies : List (List KatLang.Expr) :=
  [ [], [num 7], [num 7, num 7], [num 7, num 8], [.listLiteral [num 7]], [.listLiteral [.listLiteral [num 7]]]
  , [.capture [num 2, num 3]], [.listLiteral [num 2, num 3]], [.capture [num 1, num 2, num 3]]
  , [.listLiteral [num 1, num 2, num 3]], [.emptySequence 0, .listLiteral []], [.listLiteral [], .emptySequence 0]
  , [.emptySequence 0], [.listLiteral []], [resolve "Bad"], [resolve "Inc"], [num 7, resolve "Bad"]
  , [.listLiteral [.call (resolve "Id") [num 7]]] ]

def afAliasPairs : List (String × String) :=
  [ ("Single", "A"), ("Single", "C"), ("Add", "AAdd"), ("P", "AP"), ("E", "AE"), ("Coll", "AColl")
  , ("LC", "ALC"), ("SC", "ASC"), ("Mid", "AMid") ]

#guard afAliasPairs.all fun (callee, alias) =>
  afSupplies.all fun supply => afSameOutcome (afRun [afCall alias supply]).fst (afRun [afCall callee supply]).fst

-- An alias adds exactly its OWN binding context per level and evaluates no argument twice: the
-- `Id(7)` inside the argument opens one context in every run.
#guard (afRun [afCall "A" [.listLiteral [.call (resolve "Id") [num 7]]]]).snd
  == (afRun [afCall "Single" [.listLiteral [.call (resolve "Id") [num 7]]]]).snd + 1
#guard (afRun [afCall "C" [.listLiteral [.call (resolve "Id") [num 7]]]]).snd
  == (afRun [afCall "Single" [.listLiteral [.call (resolve "Id") [num 7]]]]).snd + 3

-- 3. The required alias examples (A, and the structural and binderless signatures; the
--    repeated-name alias `Some = P` is RepeatedNameConstraints.lean §15): the alias keeps the
--    callee's structural kinds and binderless groups.
#guard afSucceedsWith [afCall "A" [.listLiteral [num 7]]] (.atom 7)
#guard afSucceedsWith [afCall "C" [.listLiteral [.listLiteral [num 7]]]] (.listValue [.atom 7])
#guard afFailsWith innermostIsAnyTypeMismatch [afCall "C" [num 7]]
#guard afSucceedsWith [afCall "AAdd" [.capture [num 2, num 3]]] (.atom 5)
#guard afFailsWith innermostIsAnyTypeMismatch [afCall "AAdd" [.listLiteral [num 2, num 3]]]
#guard afSucceedsWith [afCall "AE" [.emptySequence 0, .listLiteral []]] (.atom 1)
#guard afFailsWith (innermostIsArityMismatch 2 0) [afCall "AE" []]
#guard afSucceedsWith [afCall "AColl" [num 1, num 2]] (.listValue [.atom 1, .atom 2])
#guard afSucceedsWith [afCall "AColl" []] (.listValue [])
#guard afSucceedsWith [afCall "ALC" [.listLiteral [num 1, num 2]]] (.listValue [.atom 1, .atom 2])
#guard afSucceedsWith [afCall "ASC" [.capture [num 1, num 2]]] (.listValue [.atom 1, .atom 2])
#guard afFailsWith innermostIsAnyTypeMismatch [afCall "ALC" [.capture [num 1, num 2]]]

-- 4. THE BARE-FORWARDING DECISION: by name, never renamed, never positional, never added to the
--    closed list, never reshaped from same-named leaves.
-- (B) `F(p)` / `A(p) = F` forwards; (C) `F(q)` / `A(p) = F` is rejected, never `F(p)`.
#guard reprStr (bareForwardingRow "Double" [afCap "x"] ["x"] [] [afCap "x"])
  == reprStr (some (afCall "Double" [param "x"]))
#guard (bareForwardingRow "Other" [afCap "x"] ["x"] [] [afCap "y"]).isNone
-- (F) `F(p, q)` / `A(p) = F` is rejected, never an inferred `q`; (G) an unused `A` parameter is fine.
#guard (bareForwardingRow "F" [afCap "p"] ["p"] [] [afCap "p", afCap "q"]).isNone
#guard reprStr (bareForwardingRow "Double" [afCap "x", afCap "unused"] ["x", "unused"] [] [afCap "x"])
  == reprStr (some (afCall "Double" [param "x"]))
-- Not positional: `G(x, y) = Sub` with `Sub(y, x)` is `Sub(y, x)`.
#guard reprStr (bareForwardingArguments [afCap "x", afCap "y"] ["x", "y"] [] afSubSignature)
  == reprStr (some [param "y", param "x"])
-- Structural compatibility is whole-pattern: `G(x) = Single` and `G(x, y) = Add` are rejected,
-- `G([x]) = Single` and `G((a, b)) = Add` forward the same pattern rebuilt as its own kind.
#guard (bareForwardingRow "Single" [afCap "x"] ["x"] [] afSingleSignature).isNone
#guard (bareForwardingRow "Add" [afCap "a", afCap "b"] ["a", "b"] [] afAddSignature).isNone
#guard reprStr (bareForwardingRow "Single" afSingleSignature ["x"] [] afSingleSignature)
  == reprStr (some (afCall "Single" [.listLiteral [param "x"]]))
#guard (bareForwardingRow "Add" [.sequenceValue [afCap "x", afCap "y"]] ["x", "y"] [] afAddSignature).isNone
-- A whole value needs a top-level binding: `F(v)` / `G([v]) = F` is rejected.
#guard (bareForwardingRow "Id" [.listValue [afCap "v"]] ["v"] [] [afCap "v"]).isNone
-- Renaming the callee's binders may invalidate bare forwarding (intentional), never an explicit call.
#guard (bareForwardingRow "Double" [afCap "x"] ["x"] [] [afCap "value"]).isNone
-- A collector nothing of its name supplies receives nothing, so the row is the bare name (Q-03).
#guard reprStr (bareForwardingRow "Coll" [afCap "p"] ["p"] [] afCollSignature) == reprStr (some (resolve "Coll"))
-- A clause branch forwards the binders of its own pattern: `W(n) = F10` forwards, `W(0) = Id`
-- (a pattern that binds no `v`) is rejected.
#guard (bareForwardingRow "Id" (Pattern.bareForwardingOwn (.litInt 0)) (Pattern.boundNames (.litInt 0))
  [] [afCap "v"]).isNone

-- 5. THE BARE-FORWARDING LAW, evaluated: the rebuilt call reads the existing bindings.
#guard afSucceedsWith [afCall "Forward" [num 5]] (.atom 10)
#guard afFailsWith (innermostIsArityMismatch 1 2) [afCall "Forward" [num 5, num 6]]
#guard afSucceedsWith [afCall "ForwardUnused" [num 5, num 999]] (.atom 10)
#guard afSucceedsWith [afCall "GSub" [num 10, num 3]] (.atom (-7))
#guard afSucceedsWith [afCall "GSubExplicit" [num 10, num 3]] (.atom 7)
#guard afSucceedsWith [afCall "SameShape" [.listLiteral [num 7]]] (.atom 7)
#guard afSucceedsWith [afCall "SameShape" [.listLiteral [.listLiteral [num 7]]]] (.listValue [.atom 7])
#guard afFailsWith innermostIsAnyTypeMismatch [afCall "SameShape" [num 7]]
#guard afSucceedsWith [afCall "GPair" [.capture [num 2, num 3]]] (.atom 5)
-- A collector re-spreads its supplied range, 0, 1 and N arguments alike; the SOURCE kind decides.
#guard afSucceedsWith [afCall "GColl" []] (.listValue [])
#guard afSucceedsWith [afCall "GColl" [num 1]] (.listValue [.atom 1])
#guard afSucceedsWith [afCall "GColl" [num 1, num 2]] (.listValue [.atom 1, .atom 2])
#guard afSucceedsWith [afCall "GOne" [.capture [num 1, num 2]]] (.listValue [.sequenceValue [.atom 1, .atom 2]])
#guard afSucceedsWith [afCall "GList" [num 1, num 2]] (.listValue [.atom 1, .atom 2])
-- A structural source rebuilds its own kind and shape.
#guard afSucceedsWith [afCall "GMid" [.listLiteral [num 1, num 2, num 3, num 4]]]
  (.listValue [.atom 1, .listValue [.atom 2, .atom 3], .atom 4])
-- Repeated names: Q's one binding reaches both occurrences, `P(x, x)`.
#guard afSucceedsWith [afCall "GP" [num 7]] (.atom 7)
-- (E) A callee that needs nothing is read; a collector-only callee receiving nothing is its value.
#guard afSucceedsWith [afCall "Always" [num 999]] (.atom 10)
#guard afSucceedsWith [afCall "GRead" [num 9]] (.listValue [])
-- A clause branch forwards its binder.
#guard afSucceedsWith [afCall "W" [num 0]] (.atom 0)
#guard afSucceedsWith [afCall "W" [num 3]] (.atom 30)
-- Q-04: the enclosing binding is reused when the local list does not declare the name, and a
-- local parameter of the same name is nearer.
#guard afSucceedsWith [afCall "OuterX" [num 100]] (.atom 100)
#guard afSucceedsWith [afCall "OuterOwn" [num 100]] (.atom 5)
-- Bare forwarding adds exactly its OWN binding context and evaluates the argument once.
#guard (afRun [afCall "Forward" [.call (resolve "Id") [num 5]]]).snd
  == (afRun [afCall "Double" [.call (resolve "Id") [num 5]]]).snd + 1

-- 6. EXPLICIT CALLS ARE DIFFERENT (D): `ExplicitOther(x) = Other(x)` passes its argument whatever
--    Other calls its parameter, and `Explicit(x) = Single(x)` passes its whole x as Single's list.
#guard afSucceedsWith [afCall "ExplicitOther" [num 5]] (.atom 10)
#guard afSucceedsWith [afCall "Explicit" [.listLiteral [num 7]]] (.atom 7)
#guard afFailsWith innermostIsAnyTypeMismatch [afCall "Explicit" [num 7]]

-- 7. FORMULA LIFTING (H) is a separate mechanism: the open formula takes Double's `x`.
#guard afSucceedsWith [afCall "Formula" [num 5]] (.atom 11)

-- 8. THE WRITTEN-CALL LAW (J): a formula's parameters are the names written in it, and the
--    callee's binder names are encapsulated — renaming Add's binders changes no outcome.
#guard afSucceedsWith [afCall "Construct" [num 7]] (.atom 7)
#guard afSucceedsWith [afCall "F" [num 2, num 3]] (.atom 5)
#guard [[num 2, num 3], [num 7], [.capture [num 1, num 2]], [num 2, resolve "Bad"]].all fun supply =>
  afSameOutcome (afRun [afCall "F" supply]).fst (afRun [afCall "FR" supply]).fst

-- 9. A host-built unpacking receiver has no written delimiters. Its display can coincide
-- with its children, but its contract cannot: list [x, y] and list [unpacking [x, y]]
-- consume different structures. The same distinction matters for binderless groups.
-- C# twin: HostBuiltBareForwarding_ComparesStructureRatherThanDisplay.
#guard [[], [afCap "x", afCap "y"]].all fun items =>
  let flat : ParameterPattern := .listValue items
  let nested : ParameterPattern := .listValue [.unpacking items]
  !flat.sameContract nested && !nested.sameContract flat &&
  (bareForwardingRow "F" [flat] (afNames [flat]) [] [nested]).isNone &&
  (bareForwardingRow "F" [nested] (afNames [nested]) [] [flat]).isNone

end KatLangTests
