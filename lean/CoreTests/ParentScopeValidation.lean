import KatLang
import CoreTests.Common

namespace KatLangTests.ParentScopeValidation
open KatLang (alg algWithParameterPatterns publicProp privateProp runResult Algorithm Error Result
  ParameterPattern Pattern ScopeCtx PropDef)
open KatLang (resolve param num call)

--------------------------------------------------------------------------------
-- Host-built parent scopes are validated before evaluation (owner decision, 2026-10-12)
--
-- `Algorithm.mk`, `.conditional` and `.alias` carry an optional PARENT scope. No front end
-- builds one, but a host may. Wiring a property or a program root replaces it
-- (`Algorithm.withParent`), while an `open` block target that already has one KEEPS it
-- (`wireOpenBlockToGlobalScope`). Through that route the scope's members are reachable at
-- run time: the opened block's members resolve names in it.
--
-- The pre-evaluation pass (`validateAlgorithmTree`) therefore walks every parent scope a tree
-- carries (`validateScopeTree`), wherever the scope sits and whether or not anything reads it.
-- It walks each scope's `open` targets and property algorithms, after the carrying algorithm's
-- own content, then the scope's own parent. The members are validated against the scope chain
-- they resolve names in (`ScopeCtx.staticChain`).
--
-- Formerly the walk never entered a parent scope. An invalid member there skipped every
-- pre-evaluation rule, which is how an unbuildable loop step reached the planner (F7-D6).
-- C#: `PreEvaluationValidationWalker.VisitParentScopes`, `HostBuiltParentScopeValidationTests`.
--------------------------------------------------------------------------------

def cap (name : String) : ParameterPattern := .capture { name := name }
def coll (name : String) : ParameterPattern := .capture { name := name, kind := .collecting }

/-- A host-built scope declaring `props` (and opening `opens`), with `outer` its own parent. -/
def hostScope (props : List PropDef) (outer : Option ScopeCtx := none) (opens : List KatLang.Expr := [])
    : ScopeCtx :=
  .mk outer [] opens props [] [] none none

/-- REACHABLE: the program `open { public Run = row }`, run as `Run`, whose opened block carries
    `scope`. The open-block route keeps the block's own parent, so `row` resolves names in
    `scope`. `own` adds further properties to the block itself. -/
def openedThrough (scope : ScopeCtx) (row : KatLang.Expr) (own : List PropDef := []) : KatLang.Expr :=
  .algorithmExpr (alg []
    [.algorithmExpr (.mk (some scope) [] [] (publicProp "Run" (alg [] [] [] [row]) :: own) [])]
    [] [resolve "Run"])

/-- DISCARDED: the program holding `P`, an algorithm carrying `scope`. Wiring `P` to its owner
    replaces that parent, so nothing ever reads `scope`, but the pass validates the whole tree. -/
def heldBy (scope : ScopeCtx) : KatLang.Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (.mk (some scope) [] [] [] [num 1])] [num 42])

/-- The pre-evaluation pass's own verdict on a program (`runResultM` runs it before evaluation). -/
def preEvaluation (e : KatLang.Expr) : Except Error Unit :=
  KatLang.runEvalM (KatLang.validateExplicitParamOutputInvariantExpr e)

/-- The pass refuses `e` with an error satisfying `check`, and so does the run. -/
def refusedWith (check : Error -> Bool) (e : KatLang.Expr) : Bool :=
  (match preEvaluation e with
   | .error err => check err
   | .ok _ => false) &&
  (match runResult e with
   | .error err => check err
   | .ok _ => false)

/-- The pass accepts `e` and the run produces `expected`. -/
def acceptedAs (expected : Result) (e : KatLang.Expr) : Bool :=
  (match preEvaluation e with
   | .ok _ => true
   | .error _ => false) &&
  (match runResult e with
   | .ok value => value == expected
   | .error _ => false)

--------------------------------------------------------------------------------
-- 1. Valid parent scopes keep working: the opened block reads the scope's members, a
--    grandparent's too, through a valid callable and through a valid alias chain.
--------------------------------------------------------------------------------

def valueMember : PropDef := privateProp "V" (alg [] [] [] [num 7])
def stepMember : PropDef := privateProp "Step" (alg ["x"] [] [] [.binary .add (param "x") (num 1)])

#guard acceptedAs (.atom 7) (openedThrough (hostScope [valueMember]) (resolve "V"))
#guard acceptedAs (.atom 5) (openedThrough (hostScope [stepMember]) (call (resolve "Step") [num 4]))
#guard acceptedAs (.atom 7) (openedThrough (hostScope [] (some (hostScope [valueMember]))) (resolve "V"))
#guard acceptedAs (.atom 42) (heldBy (hostScope [valueMember]))

-- The alias count the static chase runs on (`Algorithm.aliasCount`) includes the parent scopes
-- the pass walks. A valid two-alias chain there is no cycle: with the scopes left uncounted the
-- chase ran out of fuel on its first alias and reported one.
def aliasChain : List PropDef :=
  [privateProp "A" (.alias none [] [] (resolve "B")), privateProp "B" (.alias none [] [] (resolve "F")),
   privateProp "F" (alg ["x"] [] [] [param "x"])]

#guard acceptedAs (.atom 5) (openedThrough (hostScope aliasChain) (call (resolve "A") [num 5]))
#guard acceptedAs (.atom 42) (heldBy (hostScope aliasChain))
-- An alias whose target the OUTER scope declares: the chain the members resolve in.
#guard acceptedAs (.atom 5)
  (openedThrough (hostScope [privateProp "A" (.alias none [] [] (resolve "F"))]
    (some (hostScope [privateProp "F" (alg ["x"] [] [] [param "x"])]))) (call (resolve "A") [num 5]))

--------------------------------------------------------------------------------
-- 2. Every rule holds in a parent scope, in every placement, with the error the same member
--    gets as an ordinary property.
--------------------------------------------------------------------------------

/-- One invalid member set per pre-evaluation rule, with the rejection it must produce. -/
def invalidMembers : List (List PropDef × (Error -> Bool)) := [
  ([privateProp "Bad" (algWithParameterPatterns [coll "a", coll "b"] [] [] [param "a"])],
    innermostIsIllegalInEval KatLang.multipleCollectingBindingsPerLevelMessage),
  ([privateProp "Bad" (algWithParameterPatterns [.sequenceValue [cap "x"]] [] [] [param "x"])],
    innermostIsIllegalInEval KatLang.singletonSequencePatternMessage),
  ([privateProp "Bad" (algWithParameterPatterns [cap "x", coll "x"] [] [] [param "x"])],
    innermostIsIllegalInEval KatLang.repeatedNameIncludesCollectingMessage),
  ([privateProp "Bad" (alg ["x"] [] [] [])],
    innermostIsExplicitParamsRequireOutput),
  ([privateProp "Bad" (.conditional none [] [
      ⟨ .litInt 0, alg [] [] [] [num 1] ⟩,
      ⟨ .sequenceValue [.bind "x", .bind "y"], alg [] [] [] [param "x"] ⟩])],
    innermostIsBranchArityMismatch "Bad" 1 2),
  ([privateProp "Bad" (.conditional none [] [
      ⟨ .litInt 0, alg [] [] [] [num 1] ⟩,
      ⟨ .bind "x", alg [] [] [] [param "x", param "x"] ⟩])],
    innermostIsBranchOutputArityMismatch "Bad" 1 2),
  ([privateProp "Bad" (.alias none [] [] (num 1))],
    innermostIsIllegalInEval (KatLang.aliasTargetNotStaticPathMessage "(num)")),
  ([privateProp "X" (.alias none [] [] (resolve "Y")), privateProp "Y" (.alias none [] [] (resolve "X"))],
    innermostIsIllegalInEval KatLang.aliasCycleMessage)
]

/-- Where a member set can sit: an ordinary property of the root (the CONTROL), the opened
    block's parent scope (REACHABLE), a property's parent scope (DISCARDED), the parent of the
    opened block's parent (GRANDPARENT), a family's, an alias's and a block row's parent scope,
    and the program root's own. -/
def placements : List (List PropDef -> KatLang.Expr) := [
  fun props => .algorithmExpr (alg [] [] props [num 7]),
  fun props => openedThrough (hostScope props) (num 7),
  fun props => heldBy (hostScope props),
  fun props => openedThrough (hostScope [] (some (hostScope props))) (num 7),
  fun props => .algorithmExpr (alg [] [] [privateProp "P"
    (.conditional (some (hostScope props)) [] [⟨ .bind "x", alg [] [] [] [param "x"] ⟩])] [num 42]),
  fun props => .algorithmExpr (alg [] [] [privateProp "F" (alg ["x"] [] [] [param "x"]),
    privateProp "P" (.alias (some (hostScope props)) [] [] (resolve "F"))] [num 42]),
  fun props => .algorithmExpr (alg [] [] [] [.algorithmExpr (.mk (some (hostScope props)) [] [] [] [num 7])]),
  fun props => .algorithmExpr (.mk (some (hostScope props)) [] [] [] [num 42])
]

#guard invalidMembers.all fun (members, check) =>
  placements.all fun place => refusedWith check (place members)

-- Valid members pass in every placement, so the refusals above are the rules'.
#guard placements.all fun place =>
  match preEvaluation (place [valueMember, stepMember]) with
  | .ok _ => true
  | .error _ => false

--------------------------------------------------------------------------------
-- 3. A scope's own `open` targets are validated too, against the scope's chain.
--------------------------------------------------------------------------------

def badBlock : KatLang.Expr :=
  .algorithmExpr (alg [] [] [publicProp "Bad" (algWithParameterPatterns [coll "a", coll "b"] [] [] [param "a"])] [])

#guard refusedWith (innermostIsIllegalInEval KatLang.multipleCollectingBindingsPerLevelMessage)
  (openedThrough (hostScope [valueMember] none [badBlock]) (resolve "V"))
#guard refusedWith (innermostIsIllegalInEval KatLang.multipleCollectingBindingsPerLevelMessage)
  (heldBy (hostScope [] none [badBlock]))

--------------------------------------------------------------------------------
-- 4. Order: the carrying algorithm's own content first, then its parent scope (innermost
--    first), and within a scope its opens before its properties. Two violations, the first
--    reported.
--------------------------------------------------------------------------------

def multiCollector : PropDef :=
  privateProp "Bad" (algWithParameterPatterns [coll "a", coll "b"] [] [] [param "a"])
def singleton : PropDef :=
  privateProp "Odd" (algWithParameterPatterns [.sequenceValue [cap "x"]] [] [] [param "x"])
def multiCollectorFirst : Error -> Bool :=
  innermostIsIllegalInEval KatLang.multipleCollectingBindingsPerLevelMessage
def singletonFirst : Error -> Bool :=
  innermostIsIllegalInEval KatLang.singletonSequencePatternMessage

-- The block's own member before its parent scope's, in both orders.
#guard refusedWith multiCollectorFirst (openedThrough (hostScope [singleton]) (num 7) [multiCollector])
#guard refusedWith singletonFirst (openedThrough (hostScope [multiCollector]) (num 7) [singleton])
-- The inner scope before the outer one.
#guard refusedWith multiCollectorFirst
  (openedThrough (hostScope [multiCollector] (some (hostScope [singleton]))) (num 7))
#guard refusedWith singletonFirst
  (openedThrough (hostScope [singleton] (some (hostScope [multiCollector]))) (num 7))
-- A scope's opens before its properties.
def singletonBlock : KatLang.Expr := .algorithmExpr (alg [] [] [publicProp "Odd" singleton.alg] [])
#guard refusedWith singletonFirst (heldBy (hostScope [multiCollector] none [singletonBlock]))
-- An earlier property's parent scope before a later property: the walk is depth-first.
#guard refusedWith singletonFirst
  (.algorithmExpr (alg [] [] [privateProp "P" (.mk (some (hostScope [singleton])) [] [] [] [num 1]), multiCollector]
    [num 42]))
-- An inner scope's declarations shadow its outer scope's (the chain is outermost first): a cycle
-- among inner aliases is found although the outer scope declares terminal callables of the same
-- names.
def shadowedCycle : ScopeCtx :=
  hostScope [privateProp "A" (.alias none [] [] (resolve "F")), privateProp "F" (.alias none [] [] (resolve "A"))]
    (some (hostScope [privateProp "A" (alg ["x"] [] [] [param "x"]), privateProp "F" (alg ["x"] [] [] [param "x"])]))
#guard refusedWith (innermostIsIllegalInEval KatLang.aliasCycleMessage) (openedThrough shadowedCycle (num 7))
-- The converse: an outer scope's members resolve in the outer chain only, never in an inner scope.
-- A cycle among outer aliases is found although the inner scope declares terminal callables of
-- the same names.
def outerCycle : ScopeCtx :=
  hostScope [privateProp "A" (alg ["x"] [] [] [param "x"]), privateProp "F" (alg ["x"] [] [] [param "x"])]
    (some (hostScope [privateProp "A" (.alias none [] [] (resolve "F")), privateProp "F" (.alias none [] [] (resolve "A"))]))
#guard refusedWith (innermostIsIllegalInEval KatLang.aliasCycleMessage) (openedThrough outerCycle (num 7))
-- The enclosing chain survives a parent scope: a cycle among later root properties is still found.
#guard refusedWith (innermostIsIllegalInEval KatLang.aliasCycleMessage)
  (.algorithmExpr (alg [] [] [privateProp "P" (.mk (some (hostScope [valueMember])) [] [] [] [num 1]),
    privateProp "X" (.alias none [] [] (resolve "Y")), privateProp "Y" (.alias none [] [] (resolve "X"))] [num 42]))

--------------------------------------------------------------------------------
-- 5. One alias object shared by two parent scopes is judged in each scope's chain: `A = F`
--    sits in a scope whose `F` is terminal and in one whose `F = A`, a cycle. The cycle is
--    reported whichever block the root opens first (the C# walker keys its alias memo by the
--    scope chain, so settling `A` in the safe scope must not excuse it in the cyclic one).
--------------------------------------------------------------------------------

def sharedAlias : Algorithm := .alias none [] [] (resolve "F")
def safeScope : ScopeCtx :=
  hostScope [privateProp "A" sharedAlias, privateProp "F" (alg ["x"] [] [] [param "x"])]
def cyclicScope : ScopeCtx :=
  hostScope [privateProp "A" sharedAlias, privateProp "F" (.alias none [] [] (resolve "A"))]
def openingAll (scopes : List ScopeCtx) : KatLang.Expr :=
  .algorithmExpr (alg [] (scopes.map fun s => .algorithmExpr (.mk (some s) [] [] [] [])) [] [num 7])

#guard refusedWith (innermostIsIllegalInEval KatLang.aliasCycleMessage) (openingAll [cyclicScope, safeScope])
#guard refusedWith (innermostIsIllegalInEval KatLang.aliasCycleMessage) (openingAll [safeScope, cyclicScope])
#guard match preEvaluation (openingAll [safeScope]) with
  | .ok _ => true
  | .error _ => false

-- An inner A = B selects the outer B = A, whose A is the outer terminal step. The repeated
-- spelling is no cycle: every hop uses its declaring scope. Loop admission sees the target.
def shadowedAncestorChain : ScopeCtx :=
  hostScope [privateProp "A" (.alias none [] [] (resolve "B"))]
    (some (hostScope [privateProp "A" stepMember.alg,
      privateProp "B" (.alias none [] [] (resolve "A"))]))

#guard acceptedAs (.atom 3) (openedThrough shadowedAncestorChain
  (call (.algorithmExpr (.builtin .repeatBuiltin)) [resolve "A", num 3, num 0]))

-- A shared outer scope is entered at the earlier property edge, before an inner scope's later
-- invalid property. Merely scheduling the outer parent is not the same as having validated it.
def sharedOuterOrder (earlierEdge : Bool) : ScopeCtx :=
  let outer := hostScope [multiCollector]
  hostScope [privateProp "P" (.mk (if earlierEdge then some outer else none) [] [] [] [num 1]), singleton]
    (some outer)

#guard refusedWith singletonFirst (openedThrough (sharedOuterOrder false) (num 7))
#guard refusedWith multiCollectorFirst (openedThrough (sharedOuterOrder true) (num 7))

end KatLangTests.ParentScopeValidation
