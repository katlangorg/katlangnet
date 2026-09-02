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
  alg [] [] [] [
    .dotCall (.algorithmExpr box) "A" none,
    .dotCall (.algorithmExpr box) "A" none
  ]

def zeroArgStructuralPropertyAccessUsesCache : Bool :=
  match KatLang.runResultWithState (.algorithmExpr zeroArgStructuralPropertyCacheRoot) with
  | Except.ok (Result.sequenceValue [Result.atom 4, Result.atom 4], state) =>
      match state.zeroArgPropertyCache with
      | [(key, (Result.atom 4, 1))] =>
          key.propertyName == "A" && key.accessKind == .structural
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
