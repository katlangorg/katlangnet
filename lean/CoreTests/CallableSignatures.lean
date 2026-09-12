import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)

--------------------------------------------------------------------------------
-- callable signature validation tests
--------------------------------------------------------------------------------

def callableSignatureValidates (signature : KatLang.CallableSignature) : Bool :=
  match KatLang.CallableSignature.validate signature with
  | .ok () => true
  | .error _ => false

def callableSignatureValidationRejectsMultipleCollecting : Bool :=
  let signature : KatLang.CallableSignature := {
    name := "Bad"
    parameters := [
      { name := "a", kind := KatLang.ParameterKind.collecting },
      { name := "b", kind := KatLang.ParameterKind.collecting }
    ]
  }
  match KatLang.CallableSignature.validate signature with
  | .error (.illegalInEval message) =>
      message = "Callable signature `Bad` cannot contain more than one collecting parameter."
  | _ => false

#guard callableSignatureValidationRejectsMultipleCollecting

def callableSignatureValidationRejectsInvalidParameterName : Bool :=
  let signature : KatLang.CallableSignature := {
    name := "Bad"
    parameters := [{ name := "initial accumulator" }]
  }
  match KatLang.CallableSignature.validate signature with
  | .error (.illegalInEval message) =>
      message = "Callable signature `Bad` contains invalid parameter name `initial accumulator`."
  | _ => false

#guard callableSignatureValidationRejectsInvalidParameterName

def callableSignatureValidationRejectsDuplicateParameterName : Bool :=
  let signature : KatLang.CallableSignature := {
    name := "Bad"
    parameters := [{ name := "x" }, { name := "x" }]
  }
  match KatLang.CallableSignature.validate signature with
  | .error (.illegalInEval message) =>
      message = "Callable signature `Bad` contains duplicate parameter name `x`."
  | _ => false

#guard callableSignatureValidationRejectsDuplicateParameterName

def builtinSequenceSignaturesValidate : Bool :=
  let builtins := [
    KatLang.Builtin.sumBuiltin,
    KatLang.Builtin.countBuiltin,
    KatLang.Builtin.mapBuiltin,
    KatLang.Builtin.filterBuiltin,
    KatLang.Builtin.reduceBuiltin,
    KatLang.Builtin.takeBuiltin,
    KatLang.Builtin.skipBuiltin
  ]
  builtins.all fun builtin =>
    match KatLang.sequenceBuiltinMetadata? builtin with
    | some metadata =>
        callableSignatureValidates (metadata.signature (KatLang.builtinDisplayName builtin))
    | none => false

#guard builtinSequenceSignaturesValidate

def algorithmParametersPreserveNameAndKindTogether : Bool :=
  let algorithm := algWithParameters [
    { name := "values", kind := .collecting },
    { name := "factor", kind := .normal }
  ] [] [] [.param "values"]
  Algorithm.parameters algorithm == [
    { name := "values", kind := .collecting },
    { name := "factor", kind := .normal }
  ]
  && Algorithm.params algorithm == ["values", "factor"]
  && Algorithm.paramKinds algorithm == [.collecting, .normal]

#guard algorithmParametersPreserveNameAndKindTogether

-- Test 1: Structural property access (0-param) → value access
-- a.X where X has 0 params → evaluates property directly
def propAlg : Algorithm :=
  alg [] [] [] [.num 42]

def receiver1 : Algorithm :=
  algPrivate [] [] [("X", propAlg)] []

def test1 : Bool :=
  match runFlat (.dotCall (.algorithmExpr receiver1) "X" none) with
  | Except.ok [42] => true
  | _ => false

#guard test1
-- EXPECTED: Except.ok [42]
#eval runFlat (.dotCall (.algorithmExpr receiver1) "X" none)

-- Test 2: Structural property with params, no args → arity mismatch (navigation-only)
-- a.F where F(x) = x + 1, no args → error (no receiver injection)
def receiver2 : Algorithm :=
  algPrivate [] [] [("F", incAlg)] [.num 10]

def test2a : Bool :=
  match runResult (.dotCall (.algorithmExpr receiver2) "F" none) with
  | Except.error _ => true   -- arity mismatch: F expects 1 arg, got 0
  | Except.ok _ => false

#guard test2a
-- EXPECTED: Except.error (arityMismatch 1 0)
#eval runResult (.dotCall (.algorithmExpr receiver2) "F" none)

-- Test 2b: Structural property with explicit args → direct binding (navigation-only)
-- a.F(10) where F(x) = x + 1 → 11
def test2b : Bool :=
  match runFlat (.dotCall (.algorithmExpr receiver2) "F" (some [.num 10])) with
  | Except.ok [11] => true
  | _ => false

#guard test2b
-- EXPECTED: Except.ok [11]
#eval runFlat (.dotCall (.algorithmExpr receiver2) "F" (some [.num 10]))

-- Test 2c: Bare use of a parameterized property → arity mismatch with property context
def receiver2c : Algorithm :=
  algPrivate [] [] [("A", alg ["x"] [] [] [.param "x"])] [.resolve "A"]

def test2c : Bool :=
  match runResult (.algorithmExpr receiver2c) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard test2c
-- EXPECTED: Except.error (withContext "while evaluating property A" (arityMismatch 1 0))
#eval runResult (.algorithmExpr receiver2c)

-- direct-call ordinary algorithm tests
--------------------------------------------------------------------------------

def directCallAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

def directCallRoot : Algorithm :=
  algPrivate [] [] [("Algo", directCallAlg)] [
    .call (.resolve "Algo") [.num 6]
  ]

def directCallWorks : Bool :=
  match runFlat (.algorithmExpr directCallRoot) with
  | Except.ok [7] => true
  | _ => false

#guard directCallWorks

def directCallArityRoot : Algorithm :=
  algPrivate [] [] [("Algo", directCallAlg)] [
    .call (.resolve "Algo") []
  ]

def directCallUsesOwnArity : Bool :=
  match runResult (.algorithmExpr directCallArityRoot) with
  | Except.error err =>
      hasContext "while evaluating call to Algo" err
      && innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard directCallUsesOwnArity

def zeroArgOutputAlg : Algorithm :=
  algPrivate [] [] [] [.num 5]

def zeroArgOutputCallRoot : Algorithm :=
  algPrivate [] [] [("Algo", zeroArgOutputAlg)] [
    .call (.resolve "Algo") []
  ]

def zeroArgOutputCallWorks : Bool :=
  match runFlat (.algorithmExpr zeroArgOutputCallRoot) with
  | Except.ok [5] => true
  | _ => false

#guard zeroArgOutputCallWorks

def zeroArgOutputRejectsExtraArgsRoot : Algorithm :=
  algPrivate [] [] [("Algo", zeroArgOutputAlg)] [
    .call (.resolve "Algo") [.num 6]
  ]

def zeroArgOutputRejectsExtraArgs : Bool :=
  match runResult (.algorithmExpr zeroArgOutputRejectsExtraArgsRoot) with
  | Except.error err => innermostIsArityMismatch 0 1 err
  | Except.ok _ => false

#guard zeroArgOutputRejectsExtraArgs

def zeroArgPropertyCacheCountedOutputRoot : Algorithm :=
  algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2])
  ] [.resolve "A"]

def zeroArgPropertyCachePreservesCountedOutput : Bool :=
  match KatLang.runResultWithState (.algorithmExpr zeroArgPropertyCacheCountedOutputRoot) with
  | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2], state) =>
      match state.zeroArgPropertyCache with
      | [(_, (Result.sequenceValue [Result.atom 1, Result.atom 2], 2))] => true
      | _ => false
  | _ => false

#guard zeroArgPropertyCachePreservesCountedOutput

def zeroArgPropertyAndExplicitCallRoot : Algorithm :=
  algPrivate [] [] [
    ("A", alg [] [] [] [.binary .add (.num 1) (.num 2)])
  ] [
    .resolve "A",
    .call (.resolve "A") []
  ]

def zeroArgPropertyAndExplicitCallStillEvaluate : Bool :=
  match KatLang.runResultWithState (.algorithmExpr zeroArgPropertyAndExplicitCallRoot) with
  | Except.ok (Result.sequenceValue [Result.atom 3, Result.atom 3], state) =>
      state.zeroArgPropertyCache.length == 1
  | _ => false

#guard zeroArgPropertyAndExplicitCallStillEvaluate

def zeroArgOuterFreshNestedPropertyStyleRoot : Algorithm :=
  algPrivate [] [] [
    ("A", alg [] [] [] [.num 3]),
    ("B", alg [] [] [] [.resolve "A", .resolve "A"])
  ] [
    .call (.resolve "B") []
  ]

def zeroArgOuterFreshCallKeepsNestedPropertyStyleCache : Bool :=
  match KatLang.runResultWithState (.algorithmExpr zeroArgOuterFreshNestedPropertyStyleRoot) with
  | Except.ok (Result.sequenceValue [Result.atom 3, Result.atom 3], state) =>
      match state.zeroArgPropertyCache with
      | [(key, (Result.atom 3, 1))] =>
          key.propertyName == "A" && key.accessKind == .lexical
      | _ => false
  | _ => false

#guard zeroArgOuterFreshCallKeepsNestedPropertyStyleCache

def zeroArgStructuralPropertyCacheRoot : Algorithm :=
  let box := alg [] [] [publicProp "A" (alg [] [] [] [.num 4])] []
  algPrivate [] [] [("Box", box)] [
    .dotCall (.resolve "Box") "A" none,
    .dotCall (.resolve "Box") "A" none
  ]

def zeroArgStructuralPropertyAccessUsesCache : Bool :=
  match KatLang.runResultWithState (.algorithmExpr zeroArgStructuralPropertyCacheRoot) with
  | Except.ok (Result.sequenceValue [Result.atom 4, Result.atom 4], state) =>
      match state.zeroArgPropertyCache with
      | [(key, (Result.atom 4, 1))] =>
          key.propertyName == "A" && key.accessKind == .lexical
      | _ => false
  | _ => false

#guard zeroArgStructuralPropertyAccessUsesCache

def zeroArgBuiltinPropertyCacheRoot : Algorithm :=
  algPrivate [] [] [("E", alg [] [] [] [.emptySequence 0])] [
    .resolve "E",
    .resolve "E"
  ]

def zeroArgBuiltinPropertyAccessUsesCache : Bool :=
  match KatLang.runResultWithState (.algorithmExpr zeroArgBuiltinPropertyCacheRoot) with
  | Except.ok (_, state) =>
      match state.zeroArgPropertyCache with
      | [(key, (Result.sequenceValue [], _))] =>
          key.propertyName == "E" && key.accessKind == .lexical
      | _ => false
  | _ => false

#guard zeroArgBuiltinPropertyAccessUsesCache

def zeroArgExplicitNestedFreshCallsRoot : Algorithm :=
  algPrivate [] [] [
    ("A", alg [] [] [] [.num 3]),
    ("C", alg [] [] [] [
      .call (.resolve "A") [],
      .call (.resolve "A") []
    ])
  ] [
    .call (.resolve "C") []
  ]

def zeroArgExplicitNestedCallsBypassDirectCache : Bool :=
  match KatLang.runResultWithState (.algorithmExpr zeroArgExplicitNestedFreshCallsRoot) with
  | Except.ok (Result.sequenceValue [Result.atom 3, Result.atom 3], state) =>
      state.zeroArgPropertyCache.isEmpty
  | _ => false

#guard zeroArgExplicitNestedCallsBypassDirectCache

def zeroArgCacheKeyDistinguishesLexicalContextRoot : Algorithm :=
  algPrivate [] [] [
    ("Left", algPrivate [] [] [("A", alg [] [] [] [.num 1])] [.resolve "A"]),
    ("Right", algPrivate [] [] [("A", alg [] [] [] [.num 2])] [.resolve "A"])
  ] [
    .resolve "Left",
    .resolve "Right"
  ]

def zeroArgCacheKeyDistinguishesLexicalContext : Bool :=
  match KatLang.runResultWithState (.algorithmExpr zeroArgCacheKeyDistinguishesLexicalContextRoot) with
  | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2], state) =>
      let aEntries := state.zeroArgPropertyCache.filter (fun entry => entry.fst.propertyName == "A")
      aEntries.length == 2
  | _ => false

#guard zeroArgCacheKeyDistinguishesLexicalContext

-- The cache's SCOPE law (F3): an EXPORTED property is self-contained, so its key
-- carries no environment components and ONE entry serves every property-style
-- access — here `Big` read from two calls of `F(x)` with different bindings.
def zeroArgExportedPropertyAcrossCallsRoot : Algorithm :=
  algPrivate [] [] [
    ("Big", alg [] [] [] [.binary .add (.num 1) (.num 2)]),
    ("F", alg ["x"] [] [] [.binary .add (.resolve "Big") (.param "x")])
  ] [
    .call (.resolve "F") [.num 1],
    .call (.resolve "F") [.num 2]
  ]

def zeroArgExportedPropertyIsEvaluatedOncePerRunAcrossCalls : Bool :=
  match KatLang.runResultWithState (.algorithmExpr zeroArgExportedPropertyAcrossCallsRoot) with
  | Except.ok (Result.sequenceValue [Result.atom 4, Result.atom 5], state) =>
      match state.zeroArgPropertyCache with
      | [(key, (Result.atom 3, 1))] =>
          key.propertyName == "Big" && key.accessKind == .lexical
            && key.valEnv == none && key.algEnv == none && key.countedParamEnv == none
      | _ => false
  | _ => false

#guard zeroArgExportedPropertyIsEvaluatedOncePerRunAcrossCalls

-- A LOCAL-ONLY property reads an input its owner's call binds, so its key carries
-- the environments at the access: two activations of `Outer` never share `P`,
-- while the two reads within one activation do.
def zeroArgLocalOnlyPropertyPerActivationRoot : Algorithm :=
  algPrivate [] [] [
    ("Outer", alg ["x"] [] [
      privateLocalProp "P" .localCapturedAncestorParams
        (alg [] [] [] [.binary .mul (.param "x") (.num 10)])
    ] [.binary .add (.resolve "P") (.resolve "P")])
  ] [
    .call (.resolve "Outer") [.num 2],
    .call (.resolve "Outer") [.num 10]
  ]

def zeroArgLocalOnlyPropertyIsKeyedByBindingContext : Bool :=
  match KatLang.runResultWithState (.algorithmExpr zeroArgLocalOnlyPropertyPerActivationRoot) with
  | Except.ok (Result.sequenceValue [Result.atom 40, Result.atom 200], state) =>
      let pEntries := state.zeroArgPropertyCache.filter (fun entry => entry.fst.propertyName == "P")
      pEntries.length == 2
        && pEntries.all (fun entry =>
          entry.fst.valEnv.isSome && entry.fst.algEnv.isSome && entry.fst.countedParamEnv.isSome)
  | _ => false

#guard zeroArgLocalOnlyPropertyIsKeyedByBindingContext

-- Equal argument values do not identify an activation. This used to leave one
-- entry because `reprStr env` erased the difference between the two bindings.
def zeroArgLocalOnlyEqualActivations : Bool :=
  let root := alg [] [] (Algorithm.props zeroArgLocalOnlyPropertyPerActivationRoot) [
      .call (.resolve "Outer") [.num 2],
      .call (.resolve "Outer") [.num 2]]
  match KatLang.runResultWithState (.algorithmExpr root) with
  | .ok (_, state) =>
      let entries := state.zeroArgPropertyCache.filter (fun entry => entry.fst.propertyName == "P")
      entries.length == 2 && (entries.map (fun entry => entry.fst.bindingContext)).eraseDups.length == 2
  | _ => false

#guard zeroArgLocalOnlyEqualActivations

-- A property read pushes a lexical scope but binds no new parameters. The
-- ancestor lookup inside Q must share P's entry with its direct owner read.
def zeroArgLocalOnlyNestedPropertyRead : Bool :=
  let root := algPrivate [] [] [("Outer", alg ["x"] [] [
    privateLocalProp "P" .localCapturedAncestorParams (alg [] [] [] [.param "x"]),
    privateLocalProp "Q" .localCapturedAncestorParams (alg [] [] [] [.resolve "P", .resolve "P"])
  ] [.resolve "P", .resolve "Q", .resolve "P"])] [.call (.resolve "Outer") [.num 1]]
  match KatLang.runResultWithState (.algorithmExpr root) with
  | .ok (_, state) =>
      (state.zeroArgPropertyCache.filter (fun entry => entry.fst.propertyName == "P")).length == 1
  | _ => false

#guard zeroArgLocalOnlyNestedPropertyRead

-- Selecting A's algorithm body binds no arguments. Rebuilt resolution owners
-- are still one declaring scope in the same Outer binding context.
def zeroArgLocalOnlyAlgorithmArgumentReads : Bool :=
  let root := algPrivate [] [] [("Outer", alg ["x"] [] [
    privateLocalProp "A" .localCapturedAncestorParams (alg [] [] [
      privateLocalProp "P" .localCapturedAncestorParams (alg [] [] [] [.param "x"])
    ] [.resolve "P"])
  ] [.call (.resolve "if") [.num 1, .resolve "A", .num 0],
     .call (.resolve "if") [.num 1, .resolve "A", .num 0]])]
    [.call (.resolve "Outer") [.num 1]]
  match KatLang.runResultWithState (.algorithmExpr root) with
  | .ok (_, state) =>
      (state.zeroArgPropertyCache.filter (fun entry => entry.fst.propertyName == "P")).length == 1
  | _ => false

#guard zeroArgLocalOnlyAlgorithmArgumentReads

-- Recursive reads can finish before an earlier read of the same property.
-- The insertion law preserves that first completion, even when the pending
-- outer evaluation eventually produces a different result.
def zeroArgFirstSuccessfulStoreWins : Bool :=
  let binding := privateProp "A" (alg [] [] [] [.num 7])
  let key := KatLang.zeroArgPropertyCacheKey .lexical
    (alg [] [] [binding] []) binding KatLang.EvalCtx.empty []
  let cache := KatLang.ZeroArgPropertyCache.insert [] key (Result.atom 7, 1)
  let cache := KatLang.ZeroArgPropertyCache.insert cache key (Result.atom 8, 1)
  KatLang.ZeroArgPropertyCache.lookup cache key == some (Result.atom 7, 1)

#guard zeroArgFirstSuccessfulStoreWins

-- An open and a structural edge select the same declaration, in either order.
def zeroArgMixedAccessSpellings (structuralFirst : Bool) : Bool :=
  let lexical : KatLang.Expr := .resolve "A"
  let structural : KatLang.Expr := .dotCall (.resolve "Lib") "A" none
  let root := alg [] [.resolve "Lib"] [
    privateProp "Lib" (alg [] [] [publicProp "A" (alg [] [] [] [.num 7])] [])
  ] (if structuralFirst then [structural, lexical] else [lexical, structural])
  match KatLang.runResultWithState (.algorithmExpr root) with
  | .ok (Result.sequenceValue [Result.atom 7, Result.atom 7], state) =>
      state.zeroArgPropertyCache.length == 1
  | _ => false

#guard zeroArgMixedAccessSpellings false
#guard zeroArgMixedAccessSpellings true

-- A direct owner and the scope-only owner reconstructed for ancestor lookup
-- identify the same declaring scope. Its executable output is not key data.
def zeroArgRootAndNestedAccess : Bool :=
  let root := algPrivate [] [] [
    ("A", alg [] [] [] [.num 7]),
    ("F", alg [] [] [] [.resolve "A"])
  ] [.resolve "A", .call (.resolve "F") [], .resolve "A"]
  match KatLang.runResultWithState (.algorithmExpr root) with
  | .ok (_, state) => state.zeroArgPropertyCache.length == 1
  | _ => false

#guard zeroArgRootAndNestedAccess

-- The value probe fails, but the algorithm channel lets Ignore accept Bad.
-- A completed successfully inside that probe: failure of its parent must not
-- roll back A's first successful run entry (C# keeps it as well).
def zeroArgSuccessfulChildSurvivesFailedProbe : Bool :=
  let root := algPrivate [] [] [
    ("A", alg [] [] [] [.num 7]),
    ("Bad", alg [] [] [] [.resolve "A", .binary .div (.num 1) (.num 0)]),
    ("Ignore", alg ["f"] [] [] [.num 0])
  ] [.call (.resolve "Ignore") [.resolve "Bad"]]
  match KatLang.runResultWithState (.algorithmExpr root) with
  | .ok (Result.atom 0, state) =>
      match state.zeroArgPropertyCache with
      | [(key, (Result.atom 7, 1))] => key.propertyName == "A"
      | _ => false
  | _ => false

#guard zeroArgSuccessfulChildSurvivesFailedProbe

def zeroArgDistinctIdenticalDeclarations : Bool :=
  let body := algPrivate ["x"] [] [("P", alg [] [] [] [.num 7])]
    [.binary .add (.resolve "P") (.param "x")]
  let root := algPrivate [] [] [("F", body), ("G", body)] [
    .call (.resolve "F") [.num 1], .call (.resolve "G") [.num 1]]
  match KatLang.runResultWithState (.algorithmExpr root) with
  | .ok (_, state) => state.zeroArgPropertyCache.length == 2
  | _ => false

#guard zeroArgDistinctIdenticalDeclarations

-- Host DAGs express sharing explicitly. Without that identity these are two
-- inline declaration sites, just as two written `{ A = 4 }` blocks are.
def zeroArgInlineDeclarationIdentity (shared : Bool) : Bool :=
  let member := publicProp "A" (alg [] [] [] [.num 4])
  let member := if shared then { member with identity := some (.shared 0) } else member
  let box := alg [] [] [member] []
  let root := alg [] [] [] [
    .dotCall (.algorithmExpr box) "A" none,
    .dotCall (.algorithmExpr box) "A" none]
  match KatLang.runResultWithState (.algorithmExpr root) with
  | .ok (_, state) => state.zeroArgPropertyCache.length == (if shared then 1 else 2)
  | _ => false

#guard zeroArgInlineDeclarationIdentity false
#guard zeroArgInlineDeclarationIdentity true

-- An explicit outer call `B()` re-evaluates B on every call, and the property-style
-- `A` inside it keeps its one run-wide entry across both calls.
def zeroArgNestedPropertyAcrossExplicitOuterCallsRoot : Algorithm :=
  algPrivate [] [] [
    ("A", alg [] [] [] [.num 3]),
    ("B", alg [] [] [] [.resolve "A", .resolve "A"])
  ] [
    .call (.resolve "B") [],
    .call (.resolve "B") []
  ]

def zeroArgNestedPropertyKeepsOneEntryAcrossExplicitOuterCalls : Bool :=
  match KatLang.runResultWithState (.algorithmExpr zeroArgNestedPropertyAcrossExplicitOuterCallsRoot) with
  | Except.ok (Result.sequenceValue [
        Result.sequenceValue [Result.atom 3, Result.atom 3],
        Result.sequenceValue [Result.atom 3, Result.atom 3]], state) =>
      state.zeroArgPropertyCache.length == 1
  | _ => false

#guard zeroArgNestedPropertyKeepsOneEntryAcrossExplicitOuterCalls

def helperOutputAlg : Algorithm :=
  algPrivate [] [] [
    ("Helper", alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)])
  ] [.num 5]

def helperDotCallRoot : Algorithm :=
  algPrivate [] [] [("Algo", helperOutputAlg)] [
    .dotCall (.resolve "Algo") "Helper" (some [.num 6])
  ]

def helperDotCallStillWorks : Bool :=
  match runFlat (.algorithmExpr helperDotCallRoot) with
  | Except.ok [12] => true
  | _ => false

#guard helperDotCallStillWorks

def capturedLocalHelperAlg : Algorithm :=
  alg ["x"] [] [
    privateLocalProp "Prop" .localCapturedAncestorParams
      (alg [] [] [] [.binary .add (.param "x") (.num 1)])
  ] [
    .binary .mul (.resolve "Prop") (.num 2)
  ]

def capturedLocalHelperRoot : Algorithm :=
  algPrivate [] [] [("Algo", capturedLocalHelperAlg)] [
    .call (.resolve "Algo") [.num 6]
  ]

def capturedLocalHelperStillWorks : Bool :=
  match runFlat (.algorithmExpr capturedLocalHelperRoot) with
  | Except.ok [14] => true
  | _ => false

#guard capturedLocalHelperStillWorks

def capturedLocalOnlyAlg : Algorithm :=
  alg ["x"] [] [
    privateLocalProp "Prop" .localCapturedAncestorParams
      (alg [] [] [] [.binary .add (.param "x") (.num 1)])
  ] [
    .param "x"
  ]

def capturedLocalOnlyDotRoot : Algorithm :=
  algPrivate [] [] [("Algo", capturedLocalOnlyAlg)] [
    .dotCall (.resolve "Algo") "Prop" none
  ]

def capturedLocalOnlyDotRejected : Bool :=
  match runResult (.algorithmExpr capturedLocalOnlyDotRoot) with
  | Except.error err => innermostIsLocalOnlyProperty "Algo" "Prop" .localCapturedAncestorParams err
  | Except.ok _ => false

#guard capturedLocalOnlyDotRejected

def capturedLocalOnlyDotCallRoot : Algorithm :=
  algPrivate [] [] [("Algo", capturedLocalOnlyAlg)] [
    .dotCall (.resolve "Algo") "Prop" (some [.num 6])
  ]

def capturedLocalOnlyDotCallRejected : Bool :=
  match runResult (.algorithmExpr capturedLocalOnlyDotCallRoot) with
  | Except.error err => innermostIsLocalOnlyProperty "Algo" "Prop" .localCapturedAncestorParams err
  | Except.ok _ => false

#guard capturedLocalOnlyDotCallRejected

def helperDirectCallStillFailsRoot : Algorithm :=
  algPrivate [] [] [("Algo", helperOutputAlg)] [
    .call (.resolve "Algo") [.num 6]
  ]

def helperDirectCallStillFails : Bool :=
  match runResult (.algorithmExpr helperDirectCallStillFailsRoot) with
  | Except.error err => innermostIsArityMismatch 0 1 err
  | Except.ok _ => false

#guard helperDirectCallStillFails

def parametrizedValuePositionRoot : Algorithm :=
  algPrivate [] [] [("Algo", directCallAlg)] [
    .resolve "Algo"
  ]

def parametrizedValuePositionRejectsBareUse : Bool :=
  match runResult (.algorithmExpr parametrizedValuePositionRoot) with
  | Except.error err =>
      hasContext "while evaluating property Algo" err
      && innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard parametrizedValuePositionRejectsBareUse

def innerDirectAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 10)]

def outerDirectCallAlg : Algorithm :=
  algPrivate [] [] [("Inner", innerDirectAlg)] [
    .call (.resolve "Inner") [.num 5]
  ]

def nestedDirectCallRoot : Algorithm :=
  algPrivate [] [] [("Outer", outerDirectCallAlg)] [
    .resolve "Outer",
    .dotCall (.resolve "Outer") "Inner" (some [.num 5])
  ]

def nestedDirectCallWorks : Bool :=
  match runFlat (.algorithmExpr nestedDirectCallRoot) with
  | Except.ok [15, 15] => true
  | _ => false

#guard nestedDirectCallWorks

def conditionalLocalInnerAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0,
      alg [] [] [
        privateLocalProp "Inner" .localConditional (alg [] [] [] [.num 1])
      ] [.num 0] ⟩,
    ⟨ .bind "x",
      alg [] [] [
        privateLocalProp "Inner" .localConditional
          (alg [] [] [] [.binary .add (.param "x") (.num 1)])
      ] [.param "x"] ⟩
  ]

def conditionalLocalInnerRoot : Algorithm :=
  algPrivate [] [] [("Outer", conditionalLocalInnerAlg)] [
    .dotCall (.resolve "Outer") "Inner" none
  ]

def conditionalLocalInnerRejected : Bool :=
  match runResult (.algorithmExpr conditionalLocalInnerRoot) with
  | Except.error err => innermostIsLocalOnlyProperty "Outer" "Inner" .localConditional err
  | Except.ok _ => false

#guard conditionalLocalInnerRejected

def conditionalSplitHelpersAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0,
      alg [] [] [
        privateLocalProp "First" .localConditional (alg [] [] [] [.num 1])
      ] [.num 0] ⟩,
    ⟨ .bind "x",
      alg [] [] [
        privateLocalProp "Second" .localConditional
          (alg [] [] [] [.binary .add (.param "x") (.num 1)])
      ] [.param "x"] ⟩
  ]

def conditionalSplitHelpersRoot : Algorithm :=
  algPrivate [] [] [("Outer", conditionalSplitHelpersAlg)] [
    .dotCall (.resolve "Outer") "Second" none
  ]

def conditionalSplitHelpersRejected : Bool :=
  match runResult (.algorithmExpr conditionalSplitHelpersRoot) with
  | Except.error err => innermostIsLocalOnlyProperty "Outer" "Second" .localConditional err
  | Except.ok _ => false

#guard conditionalSplitHelpersRejected

-- `Output` is an ordinary identifier: a property named `Output` follows the
-- same structural dot-call rules as any other property name.

def outputNamedCallablePropertyAlg : Algorithm :=
  algPrivate [] [] [("Output", alg ["x"] [] [] [.binary .add (.param "x") (.num 1)])] []

def outputDotCallOrdinaryRoot : Algorithm :=
  algPrivate [] [] [("Algo", outputNamedCallablePropertyAlg)] [
    .dotCall (.resolve "Algo") "Output" (some [.num 6])
  ]

def outputDotCallOrdinaryWorks : Bool :=
  match runFlat (.algorithmExpr outputDotCallOrdinaryRoot) with
  | Except.ok [7] => true
  | _ => false

#guard outputDotCallOrdinaryWorks

def outputNamedZeroArgPropertyAlg : Algorithm :=
  algPrivate [] [] [("Output", alg [] [] [] [.num 9])] []

def bareOutputAccessOrdinaryRoot : Algorithm :=
  algPrivate [] [] [("Algo", outputNamedZeroArgPropertyAlg)] [
    .dotCall (.resolve "Algo") "Output" none
  ]

def bareOutputAccessOrdinaryWorks : Bool :=
  match runFlat (.algorithmExpr bareOutputAccessOrdinaryRoot) with
  | Except.ok [9] => true
  | _ => false

#guard bareOutputAccessOrdinaryWorks

def missingOutputMemberRoot : Algorithm :=
  algPrivate [] [] [("Algo", zeroArgOutputAlg)] [
    .dotCall (.resolve "Algo") "Output" none
  ]

def missingOutputMemberIsOrdinaryUnknownName : Bool :=
  match runResult (.algorithmExpr missingOutputMemberRoot) with
  | Except.error err => innermostIsUnknownName "Output" err
  | Except.ok _ => false

#guard missingOutputMemberIsOrdinaryUnknownName

def stringLiteralSatisfiesInvariant : Bool :=
  KatLang.postElabInvariant (.stringLiteral "abc")

#guard stringLiteralSatisfiesInvariant

def stringOutputAlgSatisfiesInvariant : Bool :=
  KatLang.postElabInvariantAlg (alg [] [] [] [.stringLiteral "abc"])

#guard stringOutputAlgSatisfiesInvariant

def unresolvedLoadViolatesInvariant : Bool :=
  !KatLang.postElabInvariant
    (.call (.resolve "load") [.stringLiteral "https://katlang.org/lib.kat"])

#guard unresolvedLoadViolatesInvariant

def outputDotCallSatisfiesInvariant : Bool :=
  KatLang.postElabInvariant (.dotCall (.resolve "Algo") "Output" none)

#guard outputDotCallSatisfiesInvariant

-- The elaborated dot-edge contract (C#: DotCallElaborationInvariant): the
-- stored lexical fallback must be `.resolve`/`.param` naming the SAME member.
-- The `Expr.dotCall` sugar and an explicit coherent `.param` fallback satisfy
-- it; name mismatches and non-name fallback expressions are rejected.
def dotMemberFallbackCoherenceEnforced : Bool :=
  KatLang.postElabInvariant (.dotCall (.num 1) "t" none)
  && KatLang.postElabInvariant (.dotMember (.num 1) "t" (.param "t") none)
  && KatLang.postElabInvariant (.dotMember (.num 1) "t" (.resolve "t") (some [.num 2]))
  && !(KatLang.postElabInvariant (.dotMember (.num 1) "t" (.resolve "u") none))
  && !(KatLang.postElabInvariant (.dotMember (.num 1) "t" (.param "u") none))
  && !(KatLang.postElabInvariant (.dotMember (.num 1) "t" (.num 5) none))

#guard dotMemberFallbackCoherenceEnforced

def outputNamedPropertySatisfiesInvariant : Bool :=
  KatLang.postElabInvariantAlg
    (alg [] [] [privateProp "Output" (alg [] [] [] [.num 1])] [.num 2])

#guard outputNamedPropertySatisfiesInvariant

def helperPropertySatisfiesInvariant : Bool :=
  KatLang.postElabInvariantAlg
    (alg [] [] [privateProp "Helper" (alg [] [] [] [.num 1])] [.stringLiteral "abc"])

#guard helperPropertySatisfiesInvariant

end KatLangTests
