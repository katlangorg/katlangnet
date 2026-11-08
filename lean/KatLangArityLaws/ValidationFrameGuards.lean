import KatLangArityLaws.ValidationFrame

open KatLang KatLang.ValidationFrame

/-!
# E-6 Tier 2 guards: the total validation on host-built trees

Executable evidence for `KatLangArityLaws/ValidationFrame.lean`: the now-total
`validateExplicitParamOutputInvariantExpr` runs on host-built trees that hit each
`ValidatorError` constructor, from two different entry states, and each guard checks the exact
error, that the state is returned unchanged, and that the two outcomes agree. The fixtures are
those of `CoreTests/ParentScopeValidation.lean`, `CoreTests/HostScopeIdentity.lean` and
`KatLangArityLaws/CallReferenceGuards.lean`; each is ALSO refused by `runResult` with the same
innermost error (the validator runs before evaluation), checked in the last section.
-/

namespace KatLang.ValidationFrameGuards

def cap (name : String) : ParameterPattern := .capture { name := name }
def coll (name : String) : ParameterPattern := .capture { name := name, kind := .collecting }
def metaParam (name : Ident) : CallableParameter := { name := name, kind := .metaRef }

/-- A program root holding the private member `bad` and returning `7`. -/
def holding (bad : List PropDef) : Expr := .algorithmExpr (alg [] [] bad [num 7])

/-- An ownerless host level with the host-scope token `token`. -/
def hostAt (token : Nat) (props : List PropDef := []) (parent : Option ScopeCtx := none) : ScopeCtx :=
  .mk parent [] [] props [] [] none (some (.host token))

def pShared : PropDef :=
  { privateProp "P" ((alg [] [] [] [.param "x"]).withDeclarationId (some (.shared 887))) with
    identity := some (.shared 888) }
def gReader : PropDef := publicProp "G" (alg ["x"] [] [] [.resolve "P"])

/-- Two opened blocks under the host levels `a` and `b`. -/
def twoOpened (a b : ScopeCtx) : Expr :=
  .algorithmExpr (alg []
    [.algorithmExpr (.mk (some a) [] [] [publicProp "RunA" (alg [] [] [] [.call (.resolve "G") [.num 1]]), gReader] []),
     .algorithmExpr (.mk (some b) [] [] [publicProp "RunB" (alg [] [] [] [.call (.resolve "G") [.num 2]]), gReader] [])]
    [] [.resolve "RunA", .resolve "RunB"])

/-- A second entry state, distinct from the empty one. -/
def busy : EvalState := { tickCounter := 5 }

/-- The validator refuses `e` with `expected` from both entry states and returns each unchanged. -/
def refuses (e : Expr) (expected : Error) : Bool :=
  let v := validateExplicitParamOutputInvariantExpr e
  let r₀ := v.runState EvalState.empty
  let r₁ := v.runState busy
  (match r₀.1, r₁.1 with
   | .error a, .error b => reprStr a == reprStr expected && reprStr b == reprStr expected
   | _, _ => false) &&
  reprStr r₀.2 == reprStr EvalState.empty && reprStr r₁.2 == reprStr busy

/-- The validator accepts `e` from both entry states and returns each unchanged. -/
def accepts (e : Expr) : Bool :=
  let v := validateExplicitParamOutputInvariantExpr e
  let r₀ := v.runState EvalState.empty
  let r₁ := v.runState busy
  (match r₀.1, r₁.1 with
   | .ok _, .ok _ => true
   | _, _ => false) &&
  reprStr r₀.2 == reprStr EvalState.empty && reprStr r₁.2 == reprStr busy

/-! ## One fixture per `ValidatorError` constructor -/

-- hostMisplaced
def hostOnAlgorithm : Expr := .algorithmExpr ((alg [] [] [] [.num 1]).withDeclarationId (some (.host 0)))
#guard refuses hostOnAlgorithm (.illegalInEval hostIdentityMisplacedMessage)
-- hostIncoherent
def hostReused : Expr := twoOpened (hostAt 0 [pShared]) (hostAt 0)
#guard refuses hostReused (.illegalInEval (hostProvenanceIncoherentMessage 0))
-- illegal: the five fixed messages
def singletonPattern : Expr :=
  holding [privateProp "Bad" (algWithParameterPatterns [.sequenceValue [cap "x"]] [] [] [param "x"])]
#guard refuses singletonPattern (.illegalInEval singletonSequencePatternMessage)
def twoCollectors : Expr :=
  holding [privateProp "Bad" (algWithParameterPatterns [coll "a", coll "b"] [] [] [param "a"])]
#guard refuses twoCollectors (.illegalInEval multipleCollectingBindingsPerLevelMessage)
def repeatedCollector : Expr :=
  holding [privateProp "Bad" (algWithParameterPatterns [cap "x", coll "x"] [] [] [param "x"])]
#guard refuses repeatedCollector (.illegalInEval repeatedNameIncludesCollectingMessage)
def nestedMeta : Expr :=
  holding [privateProp "Bad" (algWithParameterPatterns [.listValue [.capture (metaParam "x")]] [] [] [.num 1])]
#guard refuses nestedMeta (.illegalInEval invalidMetaParameterMessage)
def aliasLoop : Expr :=
  holding [privateProp "X" (.alias none [] [] (resolve "Y")), privateProp "Y" (.alias none [] [] (resolve "X"))]
#guard refuses aliasLoop (.illegalInEval aliasCycleMessage)
-- aliasTarget
def numberAlias : Expr := holding [privateProp "Bad" (.alias none [] [] (num 1))]
#guard refuses numberAlias (.illegalInEval (aliasTargetNotStaticPathMessage "(num)"))
-- explicitParams
def noOutput : Expr := holding [privateProp "Bad" (alg ["x"] [] [] [])]
#guard refuses noOutput .explicitParamsRequireOutput
-- branchArity
def unevenHeads : Expr := holding [privateProp "Bad" (.conditional none [] [
  ⟨ .litInt 0, alg [] [] [] [num 1] ⟩,
  ⟨ .sequenceValue [.bind "x", .bind "y"], alg [] [] [] [param "x"] ⟩])]
#guard refuses unevenHeads (.branchArityMismatch "Bad" 1 2)
-- branchOutputArity
def unevenOutputs : Expr := holding [privateProp "Bad" (.conditional none [] [
  ⟨ .litInt 0, alg [] [] [] [num 1] ⟩,
  ⟨ .bind "x", alg [] [] [] [param "x", param "x"] ⟩])]
#guard refuses unevenOutputs (.branchOutputArityMismatch "Bad" 1 2)

/-! ## The first error is the first in traversal order, and valid trees pass -/

-- The host check runs first: a host-marked algorithm that ALSO lacks output.
#guard refuses (.algorithmExpr ((alg ["x"] [] [] []).withDeclarationId (some (.host 0))))
  (.illegalInEval hostIdentityMisplacedMessage)
-- Left to right: the earlier property's violation is reported.
#guard refuses (holding [privateProp "A" (alg ["x"] [] [] []),
    privateProp "B" (algWithParameterPatterns [coll "a", coll "b"] [] [] [param "a"])])
  .explicitParamsRequireOutput
#guard refuses (holding [privateProp "B" (algWithParameterPatterns [coll "a", coll "b"] [] [] [param "a"]),
    privateProp "A" (alg ["x"] [] [] [])])
  (.illegalInEval multipleCollectingBindingsPerLevelMessage)
-- Within one algorithm the singleton check precedes the collector check.
#guard refuses (holding [privateProp "Bad"
    (algWithParameterPatterns [.sequenceValue [cap "x"], coll "a", coll "b"] [] [] [param "x"])])
  (.illegalInEval singletonSequencePatternMessage)
-- Within one algorithm the singleton check precedes the explicit-parameter check.
#guard refuses (holding [privateProp "Bad" (algWithParameterPatterns [.sequenceValue [cap "x"]] [] [] [])])
  (.illegalInEval singletonSequencePatternMessage)
#guard accepts (holding [privateProp "F" (alg ["x"] [] [] [param "x"]),
  privateProp "A" (.alias none [] [] (resolve "F"))])
#guard accepts (twoOpened (hostAt 0 [pShared]) (hostAt 0 [pShared]))

/-! ## The run refuses each fixture with the same innermost error -/

def innermost : Error → Error
  | .withContext _ inner => innermost inner
  | err => err

def runRefuses (e : Expr) (expected : Error) : Bool :=
  match runResult e with
  | .error err => reprStr (innermost err) == reprStr expected
  | .ok _ => false

#guard runRefuses hostOnAlgorithm (.illegalInEval hostIdentityMisplacedMessage)
#guard runRefuses hostReused (.illegalInEval (hostProvenanceIncoherentMessage 0))
#guard runRefuses singletonPattern (.illegalInEval singletonSequencePatternMessage)
#guard runRefuses twoCollectors (.illegalInEval multipleCollectingBindingsPerLevelMessage)
#guard runRefuses repeatedCollector (.illegalInEval repeatedNameIncludesCollectingMessage)
#guard runRefuses nestedMeta (.illegalInEval invalidMetaParameterMessage)
#guard runRefuses aliasLoop (.illegalInEval aliasCycleMessage)
#guard runRefuses numberAlias (.illegalInEval (aliasTargetNotStaticPathMessage "(num)"))
#guard runRefuses noOutput .explicitParamsRequireOutput
#guard runRefuses unevenHeads (.branchArityMismatch "Bad" 1 2)
#guard runRefuses unevenOutputs (.branchOutputArityMismatch "Bad" 1 2)

end KatLang.ValidationFrameGuards
