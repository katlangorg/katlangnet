import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameterPatterns algPrivate runResultM Algorithm Error Result EvalState
  ParameterPattern Pattern bareForwardingRow bareForwardingArguments bareForwardingRowOf
  BareForwardingRejection)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- Callable aliases, bare forwarding and written calls (FWD-02; binding
-- indirection decided 2026-10-01)
--------------------------------------------------------------------------------
-- A body whose ONE written row is a bare reference to a callable that declares
-- parameterized callable structure (`Algorithm.declaresParameterizedStructure`) is
-- not a formula:
--   * `A = F` is a CALLABLE ALIAS (`Algorithm.alias`): BINDING INDIRECTION. `A` keeps
--     its own binding — declaration, zero-argument cache key — while every callable
--     use of `A` is `F`'s, resolved in `A`'s own scope (`resolveAliasTarget`): a call
--     through `A` IS `F`'s call, for every builtin (the adapters, `if`'s laziness, a
--     callback slot's non-demand, a loop's minimum arity), every user shape and every
--     clause family — nameable or not. No wrapper is invoked: an alias opens no
--     binding context and evaluates nothing;
--   * `G(params) = F` is BARE FORWARDING: each of `F`'s parameters is supplied from an
--     EXISTING compatible binding of the SAME NAME (`bareForwardingRow`) — never
--     renamed, never matched by position, never added to G's closed list, never
--     reshaped from same-named leaves — and a target with NO forwarding contract (an
--     unnameable family, through any alias) is the front-end error
--     (`bareForwardingRowOf`, narrowed Q-77);
--   * `G(params) = F(exprs)` is an ORDINARY WRITTEN CALL, whose arguments need not
--     match F's names — deliberately NOT the same thing as the bare row;
--   * `G = F(exprs)` is a FORMULA whose parameters are the free names written in
--     `exprs`: `G = Add((x, y))` is `G(x, y) = Add((x, y))`.
-- Lean models no elaboration: the alias and bare-forwarding trees below are BUILT
-- with the Lean specification (`Algorithm.alias`, `bareForwardingRow`), the
-- written-call trees are the detector's output, hand-encoded, and the guards
-- evaluate them. The C# front end produces the same trees
-- (`ImplicitArgumentResolver.TryCompleteLoneCalleeRow`), which the derived programs of
-- the `alias-*`, `bare-forwarding-*` and `written-call-*` spec cases and the `alias*` /
-- `bareForwarding*` / `writtenCall*` explorer specials check against Lean.
--
-- Evaluation-count evidence without host operations (as in
-- `RepeatedNameConstraints.lean`): every user call whose parameters BIND opens one
-- binding context, so a forwarding definition adds exactly ONE context — its own —
-- an alias adds NONE (it is no invocation), and an argument whose evaluation opens
-- contexts (`Id(7)`) is evaluated once however many levels hand it on.

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

/-- The elaborated callable alias `A = callee`: binding indirection, nothing synthesized. -/
def afAlias (callee : String) : Algorithm := .alias none [] [] (resolve callee)

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

/-- `Fact(0) = 1` / `Fact(n) = n * Fact(n - 1)`: a nameable clause family. -/
def afFact : Algorithm :=
  Algorithm.elaborateClauseGroup
    [ { pattern := .litInt 0, body := alg [] [] [] [num 1] }
    , { pattern := .bind "n"
        body := alg [] [] [] [.binary .mul (param "n") (afCall "Fact" [.binary .sub (param "n") (num 1)])] } ]

/-- `S(1) = 1` / `S(-1) = -1`: an UNNAMEABLE family — no clause names its position. -/
def afSign : Algorithm :=
  Algorithm.elaborateClauseGroup
    [ { pattern := .litInt 1, body := alg [] [] [] [num 1] }
    , { pattern := .litInt (-1), body := alg [] [] [] [num (-1)] } ]

/-- Every builtin of the prelude, by its written name. -/
def afBuiltinNames : List String :=
  [ "if", "while", "repeat", "atoms", "range", "filter", "map", "order", "orderDesc", "count", "contains"
  , "first", "last", "distinct", "take", "skip", "min", "max", "sum", "avg", "reduce" ]

/-- The alias `A_<b> = <b>` of every builtin. -/
def afBuiltinAliases : List (String × Algorithm) :=
  afBuiltinNames.map fun name => ("A_" ++ name, afAlias name)

/-- `L0 = Single`, `L1 = L0`, …, `L<n-1> = L<n-2>`: an `n`-link alias chain. -/
def afChain (n : Nat) : List (String × Algorithm) :=
  (List.range n).map fun i => (s!"L{i}", afAlias (if i == 0 then "Single" else s!"L{i - 1}"))

def afRoot (out : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    ([ ("Single", algWithParameterPatterns afSingleSignature [] [] [param "x"])
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
    , ("Acc", alg ["item", "acc"] [] [] [.binary .add (param "item") (param "acc")])
    , ("Double", alg ["x"] [] [] [.binary .mul (param "x") (num 2)])
    , ("Other", alg ["y"] [] [] [.binary .mul (param "y") (num 2)])
    , ("Sub", algWithParameterPatterns afSubSignature [] [] [.binary .sub (param "y") (param "x")])
    , ("Ten", alg [] [] [] [num 10])
    , ("F10", alg ["n"] [] [] [.binary .mul (param "n") (num 10)])
    -- Callable aliases, among them a three-level chain.
    , ("A", afAlias "Single"), ("B", afAlias "A"), ("C", afAlias "B")
    , ("AAdd", afAlias "Add"), ("AP", afAlias "P")
    , ("AE", afAlias "E"), ("AColl", afAlias "Coll")
    , ("ALC", afAlias "LC"), ("ASC", afAlias "SC")
    , ("AMid", afAlias "Mid")
    -- Families: a nameable one with its alias and an alias chain, an unnameable one with its alias.
    , ("Fact", afFact), ("AFact", afAlias "Fact"), ("BFact", afAlias "AFact")
    , ("S", afSign), ("SA", afAlias "S")
    -- A builtin alias chain.
    , ("CountA", afAlias "count"), ("CountB", afAlias "CountA"), ("CountC", afAlias "CountB")
    -- Callable identity (§11): `PF(f, f) = f(7)` with `Only(*xs) = 0` and `OnlyA = Only`.
    , ("PF", alg ["f", "f"] [] [] [.call (param "f") [num 7]])
    , ("Only", algWithParameterPatterns [afColl "xs"] [] [] [.call (resolve "Id") [num 0]])
    , ("OnlyA", afAlias "Only")
    -- A zero-parameter target is READ, never aliased: `ZA = Z` is an ordinary property.
    , ("Z", alg [] [] [] [.call (resolve "Id") [num 3]])
    , ("ZA", alg [] [] [] [resolve "Z"])
    -- Navigation: `Lib(x) = { K = 5 ⏎ x }` declares K; its alias `LibA = Lib` declares nothing,
    -- while a callable passed through the alias IS Lib (`Navigate(f) = f.K`).
    , ("Lib", algPrivate ["x"] [] [("K", alg [] [] [] [num 5])] [param "x"])
    , ("LibA", afAlias "Lib")
    , ("Navigate", alg ["f"] [] [] [.dotMember (param "f") "K" (resolve "K") none])
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
    -- Bare forwarding THROUGH an alias reads the target's contract: `W(collection) = CountC`.
    , ("WCount", afBare "CountC" [afCap "collection"] [afCap "collection"])
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
    ++ afBuiltinAliases)
    out)

/-- The root with an `n`-link alias chain over `Single` (kept out of `afRoot`: every run validates
    the whole tree, and the static cycle check chases each link). -/
def afChainRoot (n : Nat) (out : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    ([ ("Single", algWithParameterPatterns afSingleSignature [] [] [param "x"])
     , ("Id", alg ["v"] [] [] [param "v"]) ] ++ afChain n)
    out)

def afChainRun (n : Nat) (out : List KatLang.Expr) : Except Error Result × Nat :=
  let (result, state) := (runResultM (afChainRoot n out)).runState EvalState.empty
  (result, state.nextBindingContext - 1)

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
    error. -/
def afSameOutcome : Except Error Result -> Except Error Result -> Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => reprStr (afInnermost left) == reprStr (afInnermost right)
  | _, _ => false

-- 1. THE ALIAS LAW (`alias_call_is_target_call`): an alias — directly and through a chain —
--    has its callee's outcome for every supply: the same value, or the same failure.
def afSupplies : List (List KatLang.Expr) :=
  [ [], [num 7], [num 7, num 7], [num 7, num 8], [.listLiteral [num 7]], [.listLiteral [.listLiteral [num 7]]]
  , [.capture [num 2, num 3]], [.listLiteral [num 2, num 3]], [.capture [num 1, num 2, num 3]]
  , [.listLiteral [num 1, num 2, num 3]], [.emptySequence 0, .listLiteral []], [.listLiteral [], .emptySequence 0]
  , [.emptySequence 0], [.listLiteral []], [resolve "Bad"], [resolve "Inc"], [num 7, resolve "Bad"]
  , [.listLiteral [.call (resolve "Id") [num 7]]] ]

def afAliasPairs : List (String × String) :=
  [ ("Single", "A"), ("Single", "C"), ("Add", "AAdd"), ("P", "AP"), ("E", "AE")
  , ("Coll", "AColl"), ("LC", "ALC"), ("SC", "ASC"), ("Mid", "AMid") ]

#guard afAliasPairs.all fun (callee, alias) =>
  afSupplies.all fun supply => afSameOutcome (afRun [afCall alias supply]).fst (afRun [afCall callee supply]).fst

-- ... and through a 100-link chain (`alias_chain_normalizes`).
#guard afSupplies.all fun supply =>
  afSameOutcome (afChainRun 100 [afCall "L99" supply]).fst (afChainRun 100 [afCall "Single" supply]).fst

-- 2. EVERY BUILTIN through its alias is the builtin itself: its adapter, its laziness, its
--    callback non-demand, its minimum arity — for every supply below, the same outcome.
def afBuiltinSupplies : List (List KatLang.Expr) :=
  [ [], [num 3], [.listLiteral [num 3, num 1, num 2]], [.listLiteral [num 3, num 1, num 2], num 2]
  , [.listLiteral [num 1, num 2, num 3], resolve "Inc"], [.listLiteral [num 1, num 2], resolve "Acc", num 0]
  , [.boolLiteral true, num 1, resolve "Bad"], [.boolLiteral false, resolve "Bad", num 2]
  , [resolve "Inc", num 2, num 0], [resolve "Inc"], [num 1, num 4], [.listLiteral [], resolve "Bad"]
  , [.listLiteral [.listLiteral [num 1, num 2], num 3]], [.capture [num 1, num 2]] ]

#guard afBuiltinNames.all fun name =>
  afBuiltinSupplies.all fun supply =>
    afSameOutcome (afRun [afCall ("A_" ++ name) supply]).fst (afRun [afCall name supply]).fst

-- The §33 witnesses: `count`'s adapter, `if`'s laziness, `map`'s callback non-demand, `repeat`'s
-- own minimum arity, and a builtin alias chain.
#guard afSucceedsWith [afCall "A_count" [.listLiteral [num 1, num 2, num 3]]] (.atom 3)
#guard afSucceedsWith [afCall "A_if" [.boolLiteral true, num 1, .binary .div (num 1) (num 0)]] (.atom 1)
#guard afSucceedsWith [afCall "A_map" [.listLiteral [], resolve "Bad"]] (.listValue [])
#guard afSameOutcome (afRun [afCall "A_repeat" [resolve "Inc"]]).fst (afRun [afCall "repeat" [resolve "Inc"]]).fst
#guard afFailsWith innermostIsAnyArityMismatch [afCall "A_repeat" [resolve "Inc"]]
#guard afSucceedsWith [afCall "CountC" [.listLiteral [num 1, num 2]]] (.atom 2)
-- A builtin alias as a CALLBACK step and as a callback argument: the callable is the builtin.
#guard afSucceedsWith [afCall "map" [.listLiteral [.listLiteral [num 1], .listLiteral [num 1, num 2]], resolve "CountC"]]
  (.listValue [.atom 1, .atom 2])

-- 3. FAMILY DISPATCH through an alias is the family's own: `F = Fact` / `F(1, 2)` is
--    `noMatchingBranch` exactly like `Fact(1, 2)` (named by the WRITTEN callee), recursion inside
--    the target refers to the target, and an alias chain dispatches alike.
#guard afSucceedsWith [afCall "AFact" [num 4]] (.atom 24)
#guard afSucceedsWith [afCall "BFact" [num 3]] (.atom 6)
#guard afFailsWith (innermostIsNoMatchingBranch "AFact") [afCall "AFact" [num 1, num 2]]
#guard afFailsWith (innermostIsNoMatchingBranch "Fact") [afCall "Fact" [num 1, num 2]]

-- 4. AN UNNAMEABLE FAMILY CAN BE ALIASED (`unnameable_family_can_be_aliased`): the alias dispatches
--    as the family ...
#guard afSucceedsWith [afCall "SA" [num 1]] (.atom 1)
#guard afSucceedsWith [afCall "SA" [num (-1)]] (.atom (-1))
#guard afFailsWith (innermostIsNoMatchingBranch "SA") [afCall "SA" [num 0]]
-- ... while a CLOSED lone row asking it for bare forwarding is the front-end error
-- (`alias_without_forwarding_contract_cannot_bare_forward`, narrowed Q-77) — and a nameable
-- target forwards by its own names through every alias of it.
def afRejectedWith (rejection : BareForwardingRejection) : Except BareForwardingRejection KatLang.Expr -> Bool
  | .error actual => actual == rejection
  | .ok _ => false

#guard afRejectedWith .noForwardingContract (bareForwardingRowOf "SA" [afCap "x"] ["x"] [] afSign)
#guard (bareForwardingRowOf "CountC" [afCap "collection"] ["collection"] [] (.builtin .countBuiltin)).toOption.isSome
#guard afRejectedWith .unforwardableParameter
  (bareForwardingRowOf "CountC" [afCap "items"] ["items"] [] (.builtin .countBuiltin))
#guard afSucceedsWith [afCall "WCount" [.listLiteral [num 1, num 2, num 3]]] (.atom 3)

-- 5. AN ALIAS IS NO INVOCATION: it opens no binding context of its own at any chain length, and
--    evaluates no argument twice (the `Id(7)` inside the argument opens one context in every run).
#guard (afRun [afCall "A" [.listLiteral [.call (resolve "Id") [num 7]]]]).snd
  == (afRun [afCall "Single" [.listLiteral [.call (resolve "Id") [num 7]]]]).snd
#guard (afRun [afCall "C" [.listLiteral [.call (resolve "Id") [num 7]]]]).snd
  == (afRun [afCall "Single" [.listLiteral [.call (resolve "Id") [num 7]]]]).snd
#guard (afChainRun 100 [afCall "L99" [.listLiteral [.call (resolve "Id") [num 7]]]]).snd
  == (afChainRun 100 [afCall "Single" [.listLiteral [.call (resolve "Id") [num 7]]]]).snd

-- 6. CALLABLE IDENTITY IS THE TARGET'S (`alias_callable_identity_is_target`): `PF(OnlyA, Only)`
--    binds the repeated `f` to ONE callable — the alias IS Only's callable — while two different
--    callables are still rejected.
#guard afSucceedsWith [afCall "PF" [resolve "OnlyA", resolve "Only"]] (.atom 0)
#guard afSucceedsWith [afCall "PF" [resolve "Only", resolve "OnlyA"]] (.atom 0)
#guard afFailsWith (fun _ => true) [afCall "PF" [resolve "OnlyA", resolve "Inc"]]

-- 7. THE CACHE KEY IS THE ALIAS BINDING'S (`alias_cache_key_is_alias_binding`): a bare read of the
--    alias `OnlyA` is Only's zero-supply demand stored under OnlyA's OWN entry, so `OnlyA, Only,
--    OnlyA` evaluates Only's body twice (one evaluation per binding: Only binds its empty supply
--    and calls `Id`, two contexts each) and reuses OnlyA's entry; an explicit `OnlyA()` is fresh
--    and populates nothing.
#guard afSucceedsWith [resolve "OnlyA", resolve "Only", resolve "OnlyA"] (.sequenceValue [.atom 0, .atom 0, .atom 0])
#guard (afRun [resolve "OnlyA", resolve "Only", resolve "OnlyA"]).snd == 4
#guard (afRun [afCall "OnlyA" [], resolve "OnlyA"]).snd == 4
#guard (afRun [resolve "OnlyA", afCall "OnlyA" []]).snd == 4
-- A ZERO-PARAMETER target is READ, never aliased (`alias_zero_parameter_target_is_read`):
-- `ZA = Z` reads Z's own cached value, so `ZA, Z, ZA` evaluates Z's body once.
#guard afSucceedsWith [resolve "ZA", resolve "Z", resolve "ZA"] (.sequenceValue [.atom 3, .atom 3, .atom 3])
#guard (afRun [resolve "ZA", resolve "Z", resolve "ZA"]).snd == 1

-- 8. NAVIGATION: written `LibA.K` does NOT navigate the target's members (an alias declares only its
--    own), while `Lib.K` does, and a callable passed THROUGH the alias is the target, so
--    `Navigate(LibA)` navigates Lib's K exactly like `Navigate(Lib)`.
#guard afSucceedsWith [.dotMember (resolve "Lib") "K" (resolve "K") none] (.atom 5)
#guard afFailsWith (fun _ => true) [.dotMember (resolve "LibA") "K" (resolve "K") none]
#guard afSucceedsWith [afCall "Navigate" [resolve "Lib"]] (.atom 5)
#guard afSucceedsWith [afCall "Navigate" [resolve "LibA"]] (.atom 5)

-- 9. HOST-BUILT ALIAS TREES the surface pass never forms are rejected before evaluation: a cycle
--    (`staticAliasCycle`) and a target that is not a static path.
def afHostRoot (props : List (String × Algorithm)) (out : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] props out)

def afHostFails (props : List (String × Algorithm)) (out : List KatLang.Expr) (message : String) : Bool :=
  match KatLang.runResult (afHostRoot props out) with
  | .error err => innermostIsIllegalInEval message err
  | .ok _ => false

#guard afHostFails [("X", afAlias "Y"), ("Y", afAlias "X")] [afCall "X" [num 1]] KatLang.aliasCycleMessage
#guard afHostFails [("X", afAlias "X")] [afCall "X" [num 1]] KatLang.aliasCycleMessage
#guard afHostFails [("X", .alias none [] [] (num 1))] [afCall "X" []]
  (KatLang.aliasTargetNotStaticPathMessage "(num)")

def afHostScopeCycle (cyclicFirst : Bool) : KatLang.Expr :=
  let shared := afAlias "F"
  let terminal := alg ["x"] [] [] [param "x"]
  let safe := algPrivate [] [] [("A", shared), ("F", terminal)] []
  let cyclic := algPrivate [] [] [("A", shared), ("F", afAlias "A")] []
  let owners := if cyclicFirst then [("Cyclic", cyclic), ("Safe", safe)]
    else [("Safe", safe), ("Cyclic", cyclic)]
  afHostRoot owners [num 99]

#guard [false, true].all fun cyclicFirst =>
  match KatLang.runResult (afHostScopeCycle cyclicFirst) with
  | .error error => innermostIsIllegalInEval KatLang.aliasCycleMessage error
  | .ok _ => false

def afHostScopeRevisit : KatLang.Expr :=
  let shared := afAlias "F"
  let terminal := alg ["x"] [] [] [param "x"]
  let lib := algPrivate [] [] [("A", shared), ("F", terminal)] []
  let indirect := Algorithm.alias none [] [] (.dotMember (resolve "Lib") "A" (resolve "A") none)
  afHostRoot [("A", shared), ("F", indirect), ("Lib", lib)] [afCall "A" [num 5]]

#guard match KatLang.runResult afHostScopeRevisit with
  | .ok value => value == .atom 5
  | .error _ => false

-- 10. THE BARE-FORWARDING DECISION: by name, never renamed, never positional, never added to the
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

-- 11. THE BARE-FORWARDING LAW, evaluated: the rebuilt call reads the existing bindings.
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

-- 12. EXPLICIT CALLS ARE DIFFERENT (D): `ExplicitOther(x) = Other(x)` passes its argument whatever
--    Other calls its parameter, and `Explicit(x) = Single(x)` passes its whole x as Single's list.
#guard afSucceedsWith [afCall "ExplicitOther" [num 5]] (.atom 10)
#guard afSucceedsWith [afCall "Explicit" [.listLiteral [num 7]]] (.atom 7)
#guard afFailsWith innermostIsAnyTypeMismatch [afCall "Explicit" [num 7]]

-- 13. FORMULA LIFTING (H) is a separate mechanism: the open formula takes Double's `x`.
#guard afSucceedsWith [afCall "Formula" [num 5]] (.atom 11)

-- 14. THE WRITTEN-CALL LAW (J): a formula's parameters are the names written in it, and the
--    callee's binder names are encapsulated — renaming Add's binders changes no outcome.
#guard afSucceedsWith [afCall "Construct" [num 7]] (.atom 7)
#guard afSucceedsWith [afCall "F" [num 2, num 3]] (.atom 5)
#guard [[num 2, num 3], [num 7], [.capture [num 1, num 2]], [num 2, resolve "Bad"]].all fun supply =>
  afSameOutcome (afRun [afCall "F" supply]).fst (afRun [afCall "FR" supply]).fst

-- 15. A host-built unpacking receiver has no written delimiters. Its display can coincide
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
