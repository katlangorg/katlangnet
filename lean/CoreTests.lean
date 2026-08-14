import KatLang

--------------------------------------------------------------------------------
-- dotCall semantics tests
--------------------------------------------------------------------------------

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)

def sequenceConstruct (left right : KatLang.Expr) : KatLang.Expr :=
  .sequenceConstruct left right

def sequenceItems : List KatLang.Expr -> KatLang.Expr
  | [] => KatLang.emptyResultExpr
  | first :: rest => rest.foldl (fun acc item => .sequenceConstruct acc item) first

def hasContext (target : String) : Error -> Bool
  | .withContext msg inner => msg = target || hasContext target inner
  | _ => false

def innermostIsBadArity : Error -> Bool
  | .withContext _ inner => innermostIsBadArity inner
  | .badArity => true
  | _ => false

def innermostIsBadIndex : Error -> Bool
  | .withContext _ inner => innermostIsBadIndex inner
  | .badIndex => true
  | _ => false

def innermostIsArityMismatch (expected actual : Nat) : Error -> Bool
  | .withContext _ inner => innermostIsArityMismatch expected actual inner
  | .arityMismatch e a => e = expected && a = actual
  | _ => false

def innermostIsTypeMismatch (expected : String) : Error -> Bool
  | .withContext _ inner => innermostIsTypeMismatch expected inner
  | .typeMismatch actual => actual = expected
  | _ => false

def innermostIsMissingOutput : Error -> Bool
  | .withContext _ inner => innermostIsMissingOutput inner
  | .missingOutput => true
  | _ => false

def innermostIsDivByZero : Error -> Bool
  | .withContext _ inner => innermostIsDivByZero inner
  | .divByZero => true
  | _ => false

def innermostIsSpreadMissingOutput : Error -> Bool
  | .withContext _ inner => innermostIsSpreadMissingOutput inner
  | .spreadMissingOutput => true
  | _ => false

def innermostIsExplicitParamsRequireOutput : Error -> Bool
  | .withContext _ inner => innermostIsExplicitParamsRequireOutput inner
  | .explicitParamsRequireOutput => true
  | _ => false

def innermostIsIllegalInEval (target : String) : Error -> Bool
  | .withContext _ inner => innermostIsIllegalInEval target inner
  | .illegalInEval actual => actual = target
  | _ => false

def innermostIsUnknownName (target : String) : Error -> Bool
  | .withContext _ inner => innermostIsUnknownName target inner
  | .unknownName name => name = target
  | _ => false

def innermostIsNoMatchingBranch (target : String) : Error -> Bool
  | .withContext _ inner => innermostIsNoMatchingBranch target inner
  | .noMatchingBranch name => name = target
  | _ => false

def innermostIsNotAnAlgorithm (desc : String) : Error -> Bool
  | .withContext _ inner => innermostIsNotAnAlgorithm desc inner
  | .notAnAlgorithm actual => actual = desc
  | _ => false

def innermostIsAnyTypeMismatch : Error -> Bool
  | .withContext _ inner => innermostIsAnyTypeMismatch inner
  | .typeMismatch _ => true
  | _ => false

def innermostIsAnyArityMismatch : Error -> Bool
  | .withContext _ inner => innermostIsAnyArityMismatch inner
  | .arityMismatch _ _ => true
  | _ => false

def innermostIsBranchArityMismatch (target : String) (expected actual : Nat) : Error -> Bool
  | .withContext _ inner => innermostIsBranchArityMismatch target expected actual inner
  | .branchArityMismatch name e a => name = target && e = expected && a = actual
  | _ => false

def innermostIsBranchOutputArityMismatch (target : String) (expected actual : Nat) : Error -> Bool
  | .withContext _ inner => innermostIsBranchOutputArityMismatch target expected actual inner
  | .branchOutputArityMismatch name e a => name = target && e = expected && a = actual
  | _ => false

def innermostIsNotPublicProperty (owner : String) (name : String) : Error -> Bool
  | .withContext _ inner => innermostIsNotPublicProperty owner name inner
  | .notPublicProperty actualOwner actualName => actualOwner = owner && actualName = name
  | _ => false

def innermostIsLocalOnlyProperty (owner : String) (name : String) (exposure : PropExposure) : Error -> Bool
  | .withContext _ inner => innermostIsLocalOnlyProperty owner name exposure inner
  | .localOnlyProperty actualOwner actualName actualExposure =>
      actualOwner = owner && actualName = name && actualExposure = exposure
  | _ => false

def innermostIsIllegalInOpen (msg : String) : Error -> Bool
  | .withContext _ inner => innermostIsIllegalInOpen msg inner
  | .illegalInOpen actual => actual = msg
  | _ => false

def innermostIsBadOpenForm (msg : String) : Error -> Bool
  | .withContext _ inner => innermostIsBadOpenForm msg inner
  | .badOpenForm actual => actual = msg
  | _ => false

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
def incAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

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

--------------------------------------------------------------------------------
-- missingOutput semantics tests
--------------------------------------------------------------------------------

def noOutputBraceAlg : Algorithm :=
  algPrivate [] [] [("X", alg [] [] [] [.num 1])] []

def missingOutputRootOnlyDefinitions : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] []

def missingOutputRootOnlyDefinitionsFails : Bool :=
  match runResult (.algorithmExpr missingOutputRootOnlyDefinitions) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputRootOnlyDefinitionsFails

def missingOutputRootWithTrailingOutput : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("T", alg [] [] [] [.num 4])] [
    .resolve "T"
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard missingOutputRootWithTrailingOutput

def missingOutputRootWithExplicitEmptyOutput : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("T", alg [] [] [] [.num 4])] [
    .emptySequence 0
  ])) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard missingOutputRootWithExplicitEmptyOutput

def missingOutputRootValueDoesNotEqualEmpty : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("T", alg [] [] [] [.num 4])] [
    .binary .eq (.resolve "T") (.emptySequence 0)
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard missingOutputRootValueDoesNotEqualEmpty

def missingOutputMultipleDefinitionsRoot : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Price", alg [] [] [] [.num 10]),
    ("Tax", alg [] [] [] [.num 2]),
    ("Total", alg [] [] [] [.binary .add (.resolve "Price") (.resolve "Tax")])
  ] [])) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputMultipleDefinitionsRoot

def missingOutputMultipleDefinitionsWithOutput : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Price", alg [] [] [] [.num 10]),
    ("Tax", alg [] [] [] [.num 2]),
    ("Total", alg [] [] [] [.binary .add (.resolve "Price") (.resolve "Tax")])
  ] [
    .resolve "Total"
  ])) with
  | Except.ok [12] => true
  | _ => false

#guard missingOutputMultipleDefinitionsWithOutput

def missingOutputValid2Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [
    .dotCall (.resolve "A") "X" none
  ]

def missingOutputValid2 : Bool :=
  match runFlat (.algorithmExpr missingOutputValid2Root) with
  | Except.ok [1] => true
  | _ => false

#guard missingOutputValid2

def applyMissingOutputAlg : Algorithm :=
  alg ["f"] [] [] [
    .call (.param "f") [.num 4]
  ]

def incMissingOutputAlg : Algorithm :=
  alg ["x"] [] [] [
    .binary .add (.param "x") (.num 1)
  ]

def missingOutputValid3Root : Algorithm :=
  algPrivate [] [] [("Apply", applyMissingOutputAlg), ("Inc", incMissingOutputAlg)] [
    .call (.resolve "Apply") [.resolve "Inc"]
  ]

def missingOutputValid3 : Bool :=
  match runFlat (.algorithmExpr missingOutputValid3Root) with
  | Except.ok [5] => true
  | _ => false

#guard missingOutputValid3

def holderMissingOutputAlg : Algorithm :=
  algPrivate [] [] [("F", noOutputBraceAlg)] [.num 0]

def missingOutputValid4Root : Algorithm :=
  algPrivate [] [] [("Holder", holderMissingOutputAlg)] [.resolve "Holder"]

def missingOutputValid4 : Bool :=
  match runFlat (.algorithmExpr missingOutputValid4Root) with
  | Except.ok [0] => true
  | _ => false

#guard missingOutputValid4

def missingOutputError5Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [.resolve "A"]

def missingOutputError5 : Bool :=
  match runResult (.algorithmExpr missingOutputError5Root) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError5

def missingOutputError6Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [
    .call (.resolve "A") []
  ]

def missingOutputError6 : Bool :=
  match runResult (.algorithmExpr missingOutputError6Root) with
  | Except.error err =>
      hasContext "while evaluating call to A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError6

def missingOutputError6bRoot : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [
    .call (.resolve "A") [.num 6]
  ]

def missingOutputError6b : Bool :=
  match runResult (.algorithmExpr missingOutputError6bRoot) with
  | Except.error err =>
      hasContext "while evaluating call to A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError6b

def missingOutputError7Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [
    .binary .add (.resolve "A") (.num 1)
  ]

def missingOutputError7 : Bool :=
  match runResult (.algorithmExpr missingOutputError7Root) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError7

def missingOutputError8Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [
    .unary .minus (.resolve "A")
  ]

def missingOutputError8 : Bool :=
  match runResult (.algorithmExpr missingOutputError8Root) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError8

def missingOutputError9Root : Algorithm :=
  algPrivate [] [] [
    ("A", noOutputBraceAlg),
    ("B", alg [] [] [] [.resolve "A"])
  ] [
    .resolve "B"
  ]

def missingOutputError9 : Bool :=
  match runResult (.algorithmExpr missingOutputError9Root) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError9

def useMissingOutputAlg : Algorithm :=
  alg ["f"] [] [] [.num 0]

def missingOutputValid10Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg), ("Use", useMissingOutputAlg)] [
    .call (.resolve "Use") [.resolve "A"]
  ]

def missingOutputValid10 : Bool :=
  match runFlat (.algorithmExpr missingOutputValid10Root) with
  | Except.ok [0] => true
  | _ => false

#guard missingOutputValid10

--------------------------------------------------------------------------------
-- empty sequence value () tests
--------------------------------------------------------------------------------

def explicitEmptyExpr : KatLang.Expr := .emptySequence 0

-- Spread. Surface spreading is the named `spread` intrinsic (`expr*`
-- and `expr*` are equivalent spellings); both lower to the unary node
-- `sequenceSpread expr`, which never takes a right operand. This helper
-- builds that node. The C# surface parser parses source `A* B` as the
-- expression-list slots `A*`, `B`. The `sequenceConstruct` form here is
-- only an internal/test semantic value and is NOT produced from any surface
-- spread spelling.
def sequenceSpread (expr : KatLang.Expr) : KatLang.Expr :=
  .sequenceSpread expr

def sequenceSpreadReceiver (expr : KatLang.Expr) : KatLang.Expr :=
  .capture [sequenceSpread expr]

def explicitEmptyOutputBody : KatLang.Expr :=
  .algorithmExpr (alg [] [] [] [explicitEmptyExpr])

def missingOutputBodyExpr : KatLang.Expr :=
  .algorithmExpr (alg [] [] [] [])

def explicitEmptyIsEvenAlg : Algorithm :=
  alg ["x"] [] [] [
    .binary .eq (.binary .mod (.param "x") (.num 2)) (.num 0)
  ]

def explicitEmptyNoOutputContainer : Algorithm :=
  algPrivate [] [] [("Prop", alg [] [] [] [.num 7])] []

def explicitEmptyProducesZeroValues : Bool :=
  match runResult explicitEmptyExpr, runFlat explicitEmptyExpr with
  | Except.ok (.sequenceValue []), Except.ok [] => true
  | _, _ => false

#guard explicitEmptyProducesZeroValues

def explicitEmptyCountsAsZero : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [explicitEmptyExpr])] [
    .dotCall explicitEmptyExpr "count" none,
    .call (.resolve "count") [explicitEmptyExpr],
    .dotCall explicitEmptyOutputBody "count" none,
    .dotCall (.algorithmExpr (alg [] [] [] [explicitEmptyExpr])) "count" none,
    .dotCall (.resolve "A") "count" none
  ])) with
  | Except.ok [0, 0, 0, 0, 0] => true
  | _ => false

#guard explicitEmptyCountsAsZero

def explicitEmptyEquality : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .binary .eq explicitEmptyExpr explicitEmptyExpr,
    .binary .ne explicitEmptyExpr explicitEmptyExpr,
    .binary .eq explicitEmptyExpr explicitEmptyOutputBody,
    .binary .eq explicitEmptyOutputBody explicitEmptyExpr,
    -- Collection builtins materialize exact lists, so an all-rejected filter
    -- and an all-skipped skip yield `[]`, which is NOT the empty sequence `()`.
    .binary .eq
      (.call (.resolve "filter") [
        .sequenceConstruct (.num 1) (.sequenceConstruct (.num 3) (.num 5)),
        .algorithmExpr explicitEmptyIsEvenAlg
      ])
      explicitEmptyExpr,
    .binary .eq
      explicitEmptyExpr
      (.call (.resolve "filter") [
        .sequenceConstruct (.num 1) (.sequenceConstruct (.num 3) (.num 5)),
        .algorithmExpr explicitEmptyIsEvenAlg
      ]),
    .binary .eq
      (.dotCall (.num 0) "skip" (some [.num 1]))
      explicitEmptyExpr
  ])) with
  | Except.ok [1, 0, 1, 1, 0, 0, 0] => true
  | _ => false

#guard explicitEmptyEquality

-- Internal sequence construction of spreads:
-- `sequenceConstruct (sequenceConstruct (sequenceSpread 1) empty) (sequenceSpread 2)`.
-- The `empty` contribution adds no items (join semantics), so the flat
-- result is [1, 2].
def spreadEmptyJoinContributesNoItems : Bool :=
  match runFlat (.sequenceConstruct
      (.sequenceConstruct (sequenceSpread (.num 1)) explicitEmptyExpr)
      (sequenceSpread (.num 2))) with
  | Except.ok [1, 2] => true
  | _ => false

#guard spreadEmptyJoinContributesNoItems

-- `()*` spreads the empty sequence value, contributing zero items.
def spreadOfEmptyContributesNoItems : Bool :=
  match runFlat (sequenceSpread explicitEmptyExpr) with
  | Except.ok [] => true
  | _ => false

#guard spreadOfEmptyContributesNoItems

-- A written sequence value with a spread beside a sibling slot splices the
-- spread items: source `A = 1, 2` then `(A*, 99)` is `(1, 2, 99)`, never the
-- grouped `((1, 2), 99)`. This pins `evalAlgOutputCore` as the value
-- projection of `evalAlgOutputCountedCore` (July 2026 fix): the plain and
-- counted evaluators must agree on value-position block output.
def valuePositionSpreadWithSiblingSplices : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2])] [
    .capture [sequenceSpread (.resolve "A"), .num 99]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 99]) => true
  | _ => false

#guard valuePositionSpreadWithSiblingSplices

-- The same splicing holds for the root program output observed through the
-- plain `runResult` path: `A*, 99` is three root slots `1, 2, 99`.
def rootSpreadWithSiblingSplices : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2])] [
    sequenceSpread (.resolve "A"), .num 99
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 99]) => true
  | _ => false

#guard rootSpreadWithSiblingSplices

-- Splicing spreads never erases a written non-spread `()` slot between them:
-- `(1*, (), 2*)` keeps the empty sequence value as a visible item.
def spreadSiblingsKeepWrittenEmptySlot : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .capture [sequenceSpread (.num 1), explicitEmptyExpr, sequenceSpread (.num 2)]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [], .atom 2]) => true
  | _ => false

#guard spreadSiblingsKeepWrittenEmptySlot

-- Structural equality observes the spliced value through the plain
-- (non-counted) evaluation path used for binary operands.
def spreadSeqLiteralEqualsFlatLiteral : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("P", alg [] [] [] [.num 1, .num 2])] [
    .binary .eq (.capture [sequenceSpread (.resolve "P"), .num 99])
      (.capture [.num 1, .num 2, .num 99])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard spreadSeqLiteralEqualsFlatLiteral

-- Spreading a DIRECT written block whose output is missing reports the
-- spread-specific error, exactly like the generic operand arm (T4-2, Aug
-- 2026): `{X = 1}*` is `spreadMissingOutput`, never raw `missingOutput`,
-- and the rule holds at every spread position — root row, list element,
-- and call-argument slot. C#: `EvalSequenceSpreadOperandItems` Block arm.
def directBlockSpreadMissingOutput : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [sequenceSpread (.algorithmExpr noOutputBraceAlg)])) with
  | Except.error err => innermostIsSpreadMissingOutput err
  | _ => false

#guard directBlockSpreadMissingOutput

def directBlockSpreadInListMissingOutput : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [sequenceSpread (.algorithmExpr noOutputBraceAlg)]])) with
  | Except.error err => innermostIsSpreadMissingOutput err
  | _ => false

#guard directBlockSpreadInListMissingOutput

def directBlockSpreadCallArgMissingOutput : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", alg ["a"] [] [] [.param "a"])] [
    .call (.resolve "F") [sequenceSpread (.algorithmExpr noOutputBraceAlg)]
  ])) with
  | Except.error err => innermostIsSpreadMissingOutput err
  | _ => false

#guard directBlockSpreadCallArgMissingOutput

-- Control: the resolved-name operand keeps its established behavior —
-- `Bad = {X = 1}` then `Bad*` reports the same spread-specific error, so
-- the direct-block and resolved spellings agree.
def resolvedSpreadMissingOutput : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", noOutputBraceAlg)] [
    sequenceSpread (.resolve "Bad")
  ])) with
  | Except.error err => innermostIsSpreadMissingOutput err
  | _ => false

#guard resolvedSpreadMissingOutput

-- Control: only the missing-output failure is translated — any other
-- error from a direct block spread operand propagates unchanged.
def directBlockSpreadOtherErrorPropagates : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    sequenceSpread (.algorithmExpr (alg [] [] [] [.resolve "nope"]))
  ])) with
  | Except.error err => innermostIsUnknownName "nope" err && !innermostIsSpreadMissingOutput err
  | _ => false

#guard directBlockSpreadOtherErrorPropagates

-- INTERNAL-NODE CONTAINMENT (July 2026 audit). `sequenceConstruct` is an
-- internal join node — NOT the representation of written parentheses, which
-- parse to `capture` nodes since the OutputBundle split. Its value evaluation
-- DROPS `()` leaves (join semantics: an empty contribution adds no items);
-- written parentheses always keep a non-spread `()` item visible. The guards
-- below pin that intentional difference structurally so any change to either
-- side — including a parser/desugaring change that routes surface syntax
-- through the internal node — is caught. C# twins live in
-- SequenceConstructContainmentTests; Lean/C# agreement on these exact ASTs
-- is enforced by the generated SemanticExplorerCases internal-node section.

-- sequenceConstruct ((), 1) drops the `()` leaf and singleton-collapses to 1 …
def internalSequenceConstructDropsEmptyLeafAndCollapses : Bool :=
  match runResult (.sequenceConstruct (.emptySequence 0) (.num 1)) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard internalSequenceConstructDropsEmptyLeafAndCollapses

-- … while the written form `((), 1)` (a surviving capture) keeps the
-- empty item visible. This pair is the intentional-difference contrast.
def writtenParenthesesKeepEmptyItemVisible : Bool :=
  match runResult (.capture [.emptySequence 0, .num 1]) with
  | Except.ok (.sequenceValue [.sequenceValue [], .atom 1]) => true
  | _ => false

#guard writtenParenthesesKeepEmptyItemVisible

-- sequenceConstruct ((), ()) drops both leaves to the empty sequence value.
def internalSequenceConstructBothEmptyLeavesDropToEmpty : Bool :=
  match runResult (.sequenceConstruct (.emptySequence 0) (.emptySequence 0)) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard internalSequenceConstructBothEmptyLeavesDropToEmpty

-- sequenceConstruct ((1, 2), ()) drops `()` and collapses to the pair; the
-- written `((1, 2), ())` keeps both items.
def internalSequenceConstructDropsEmptyBesidePair : Bool :=
  match
    runResult (.sequenceConstruct (.capture [.num 1, .num 2]) (.emptySequence 0)),
    runResult (.algorithmExpr (alg [] [] [] [.capture [.capture [.num 1, .num 2], .emptySequence 0]]))
  with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]),
    Except.ok (.sequenceValue [.sequenceValue [.atom 1, .atom 2], .sequenceValue []]) => true
  | _, _ => false

#guard internalSequenceConstructDropsEmptyBesidePair

-- A lone sequenceConstruct argument to a builtin is an ordinary value
-- expression: it evaluates to ONE grouped value and counts as ONE fixed-arity
-- argument — the same as the written grouped form. take(SC[1, 2, 5]) is one
-- argument where `take(collection, count)` expects two, exactly like surface
-- `take((1, 2, 5))`; with an explicit count both forms agree, and
-- sequenceConstruct still drops its `()` leaves (sum(SC[(), 1, 2]) is 3).
-- (C# once had a legacy reshape that special-cased this shape and diverged;
-- it was removed in the July 2026 containment audit.)
def internalSequenceConstructLoneBuiltinArgBindsLikeGroupedForm : Bool :=
  let loneScErrsLikeGroupedSurfaceForm :=
    match
      runResult (.call (.resolve "take") [
        .sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 5)]),
      runResult (.call (.resolve "take") [
        .capture [.num 1, .num 2, .num 5]])
    with
    | Except.error scErr, Except.error groupedErr =>
        innermostIsArityMismatch 2 1 scErr && innermostIsArityMismatch 2 1 groupedErr
    | _, _ => false
  let scBindsLikeGroupedForm :=
    match
      runResult (.call (.resolve "take") [
        .sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 5), .num 2]),
      runResult (.call (.resolve "sum") [
        .sequenceConstruct (.num 1) (.num 2)])
    with
    | Except.ok (.listValue [.atom 1, .atom 2]), Except.ok (.atom 3) => true
    | _, _ => false
  let scStillDropsEmptyLeaves :=
    match runResult (.call (.resolve "sum") [
      .sequenceConstruct (.sequenceConstruct (.emptySequence 0) (.num 1)) (.num 2)]) with
    | Except.ok (.atom 3) => true
    | _ => false
  loneScErrsLikeGroupedSurfaceForm && scBindsLikeGroupedForm && scStillDropsEmptyLeaves

#guard internalSequenceConstructLoneBuiltinArgBindsLikeGroupedForm

-- Repeated ordinary parentheses around the empty sequence canonicalize to `()`.
def emptyVsNestedEmptyEquality : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .binary .eq (.emptySequence 0) (.emptySequence 0),
    .binary .eq (.emptySequence 0) (.emptySequence 1),
    .binary .ne (.emptySequence 0) (.emptySequence 1)
  ])) with
  | Except.ok [1, 1, 0] => true
  | _ => false

#guard emptyVsNestedEmptyEquality

-- The empty sequence value has zero items; redundant empty nesting does too.
def emptyAndNestedEmptyCount : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (.resolve "count") [.emptySequence 0],
    .call (.resolve "count") [.emptySequence 1]
  ])) with
  | Except.ok [0, 0] => true
  | _ => false

#guard emptyAndNestedEmptyCount

-- (()) and ((())) evaluate to the canonical empty sequence value.
def nestedEmptyStructureCanonicalizes : Bool :=
  match runResult (.emptySequence 1) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard nestedEmptyStructureCanonicalizes

-- `empty` is no longer reserved: it is an ordinary identifier that can be defined.
def emptyIsOrdinaryIdentifier : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("empty", alg [] [] [] [.num 123])] [
    .resolve "empty"
  ])) with
  | Except.ok [123] => true
  | _ => false

#guard emptyIsOrdinaryIdentifier

-- Block/root output preserves visible empty sequence slots, but redundant empty
-- nesting has already canonicalized to `()`.
def blockOutputCanonicalizesNestedEmptyDepth : Bool :=
  match
    runResult (.emptySequence 0),
    runResult (.emptySequence 1),
    runResult (.algorithmExpr (alg [] [] [] [.emptySequence 0])),
    runResult (.algorithmExpr (alg [] [] [] [.emptySequence 1])),
    runResult (.algorithmExpr (alg [] [] [] [.emptySequence 2]))
  with
  | Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []) => true
  | _, _, _, _, _ => false

#guard blockOutputCanonicalizesNestedEmptyDepth

-- Mixed output: a normal non-spread `()` output is a VISIBLE slot, not dropped, so it sits
-- beside other outputs. (Only an explicit spread `()*` contributes zero items.) These would
-- fail if evalAlgOutputCore dropped count-0 non-spread slots.
def mixedOutputKeepsLeadingEmptySlot : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.emptySequence 0, .num 1])) with
  | Except.ok (.sequenceValue [.sequenceValue [], .atom 1]) => true
  | _ => false

#guard mixedOutputKeepsLeadingEmptySlot

def mixedOutputKeepsMiddleEmptySlot : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.num 1, .emptySequence 0, .num 2])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [], .atom 2]) => true
  | _ => false

#guard mixedOutputKeepsMiddleEmptySlot

-- An explicit spread of `()` still contributes zero items, so it does NOT add a slot:
-- `(()*, 1)` is just `1`.
def mixedOutputSpreadOfEmptyContributesNoSlot : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [sequenceSpread (.emptySequence 0), .num 1])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard mixedOutputSpreadOfEmptyContributesNoSlot

-- Redundant empty nesting is not a surface way to construct a one-item
-- collection containing `()`; collection builtins see it as the empty collection.
def collectionBuiltinAlwaysTrue : KatLang.Expr := .algorithmExpr (alg ["x"] [] [] [.num 1])

def filterNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "filter") [.emptySequence 1, collectionBuiltinAlwaysTrue]) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard filterNestedEmptyInputCanonicalizesToEmptyCollection

def countFilterNestedEmptyInputCanonicalizesToZero : Bool :=
  match runResult (.call (.resolve "count") [
        .call (.resolve "filter") [.emptySequence 1, collectionBuiltinAlwaysTrue]
      ]) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard countFilterNestedEmptyInputCanonicalizesToZero

def takeNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "take") [.emptySequence 1, .num 1]) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard takeNestedEmptyInputCanonicalizesToEmptyCollection

def skipNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "skip") [.emptySequence 1, .num 0]) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard skipNestedEmptyInputCanonicalizesToEmptyCollection

def distinctNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "distinct") [.emptySequence 1]) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard distinctNestedEmptyInputCanonicalizesToEmptyCollection

-- Filtering a two-item collection down to one kept `(1, 2)` materializes the
-- exact one-element list `[(1, 2)]`: collection-producing builtins never apply
-- singleton-boundary erasure to their list results — the kept sequence value
-- stays one exact element (`[(1, 2)]` is a writable KatLang value).
def filterSingleKeptSequenceValueItemStaysExactElement : Bool :=
  let keepFirstPair : KatLang.Expr := .algorithmExpr (alg ["pair"] [] [] [
    .binary .eq (.index (.param "pair") (.num 0)) (.num 1)
  ])
  match runResult (.call (.resolve "filter") [
        sequenceItems [
          .capture [.num 1, .num 2],
          .capture [.num 3, .num 4]
        ],
        keepFirstPair
      ]) with
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard filterSingleKeptSequenceValueItemStaysExactElement

-- An internal `sequenceConstruct (sequenceSpread A) B` is ONE sequence-value argument in
-- fixed-arity call-argument position and therefore fails to bind a two-parameter
-- call. Surface `A* B` is an expression list, not this constructed value.
def spreadThenJoinIsOneSequenceValueArgument : Bool :=
  let useTwo := alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")]
  let joined := algPrivate [] [] [("A", alg [] [] [] [.num 1]), ("F", useTwo)] [
    .call (.resolve "F") [.sequenceConstruct (sequenceSpread (.resolve "A")) (.num 2)]
  ]
  match runFlat (.algorithmExpr joined) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | _ => false

#guard spreadThenJoinIsOneSequenceValueArgument

-- An internal `sequenceConstruct` node in call-FUNCTION position cannot
-- resolve to an algorithm; the structured payload is exactly
-- "sequence construct expression" on both sides of the differential
-- (T4-3, Aug 2026 — the C# `ResolveAlg` description must match verbatim).
def sequenceConstructCallFunctionNotAnAlgorithm : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (.sequenceConstruct (.num 1) (.num 2)) [.num 3]
  ])) with
  | Except.error err => innermostIsNotAnAlgorithm "sequence construct expression" err
  | _ => false

#guard sequenceConstructCallFunctionNotAnAlgorithm

-- Source `1` followed by `depth` attached spread markers is the unary chain
-- `sequenceSpread (sequenceSpread (... (num 1)))`. Built tail-recursively to
-- avoid overflow while constructing the term.
partial def buildNestedSpread (depth : Nat) (acc : KatLang.Expr) : KatLang.Expr :=
  if depth = 0 then acc
  else buildNestedSpread (depth - 1) (KatLang.Expr.sequenceSpread acc)

def deeplyNestedSpreadExpr (depth : Nat) : KatLang.Expr :=
  buildNestedSpread depth (KatLang.Expr.num 1)

-- Deeply-nested unary spread must stay stack-safe: `evalSequenceSpreadCounted`
-- peels the nesting iteratively via `peelSequenceSpread` rather than recursing
-- once per level. A recursive peel would overflow at this depth. Each level
-- spreads the same single item, so the flat result is `[1]` with count 1.
def deepNestedSequenceSpreadIsStackSafe : Bool :=
  match KatLang.runEvalM (KatLang.evalCounted (deeplyNestedSpreadExpr 8192)
      { callStack := [KatLang.preludeAlg], algEnv := [] } []) with
  | Except.ok (value, count) => KatLang.Result.atoms value == [1] && count == 1
  | _ => false

#guard deepNestedSequenceSpreadIsStackSafe

def sequenceConstructEmitsOneConstructedSequenceValue : Bool :=
  match runResult (.sequenceConstruct (.num 1) (.num 2)),
        runFlat (.sequenceConstruct (.num 1) (.num 2)) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]), Except.ok [1, 2] => true
  | _, _ => false

#guard sequenceConstructEmitsOneConstructedSequenceValue

def sequenceConstructCommaPriorityConstructsOneValue : Bool :=
  let joined := .sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3)
  match runResult (.algorithmExpr (alg [] [] [] [joined])),
        KatLang.runEvalM (KatLang.evalCounted joined { callStack := [KatLang.preludeAlg], algEnv := [] } []) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]),
    Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3], 1) => true
  | _, _ => false

#guard sequenceConstructCommaPriorityConstructsOneValue

def sequenceConstructExplicitSequenceValueBoundaryProtected : Bool :=
  let joined := .sequenceConstruct (.capture [.num 1, .num 2]) (.num 3)
  match runResult (.algorithmExpr (alg [] [] [] [joined])),
        KatLang.runEvalM (KatLang.evalCounted joined { callStack := [KatLang.preludeAlg], algEnv := [] } []) with
  | Except.ok (.sequenceValue [.sequenceValue [.atom 1, .atom 2], .atom 3]),
    Except.ok (.sequenceValue [.sequenceValue [.atom 1, .atom 2], .atom 3], 1) => true
  | _, _ => false

#guard sequenceConstructExplicitSequenceValueBoundaryProtected

def sequenceConstructMaterializedCommaRows : Bool :=
  let leftRow := .capture [.num 1, .num 2, .num 3]
  let rightRow := .capture [.num 4, .num 5, .num 6]
  let table := .sequenceConstruct leftRow rightRow
  match runResult (.algorithmExpr (alg [] [] [] [table])),
        KatLang.runEvalM (KatLang.evalCounted table { callStack := [KatLang.preludeAlg], algEnv := [] } []) with
  | Except.ok (.sequenceValue [
      .sequenceValue [.atom 1, .atom 2, .atom 3],
      .sequenceValue [.atom 4, .atom 5, .atom 6]
    ]),
    Except.ok (.sequenceValue [
      .sequenceValue [.atom 1, .atom 2, .atom 3],
      .sequenceValue [.atom 4, .atom 5, .atom 6]
    ], 1) => true
  | _, _ => false

#guard sequenceConstructMaterializedCommaRows

def sequenceConstructNestedAssociativeAtConstructedValueLevel : Bool :=
  let leftNested := .sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3)
  let rightNested := .sequenceConstruct (.num 1) (.sequenceConstruct (.num 2) (.num 3))
  match runResult (.algorithmExpr (alg [] [] [] [leftNested])), runResult (.algorithmExpr (alg [] [] [] [rightNested])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]),
    Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]) => true
  | _, _ => false

#guard sequenceConstructNestedAssociativeAtConstructedValueLevel

def explicitSequenceValueTripleStaysOneTopLevelValue : Bool :=
  let sequenceValueTriple := .capture [.num 1, .num 2, .num 3]
  let constructedTriple := .sequenceConstruct (.num 1) (.sequenceConstruct (.num 2) (.num 3))
  let sequenceValueCount := .call (.resolve "count") [sequenceValueTriple]
  let constructedCount := .call (.resolve "count") [constructedTriple]
  match runResult (.algorithmExpr (alg [] [] [] [sequenceValueTriple])), runFlat sequenceValueCount, runFlat constructedCount with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]), Except.ok [3], Except.ok [3] => true
  | _, _, _ => false

#guard explicitSequenceValueTripleStaysOneTopLevelValue

def mixedCommaSequenceConstructPreservesRootSlots : Bool :=
  let mixed := alg [] [] [] [.num 1, .sequenceConstruct (.num 2) (.num 3)]
  match runResult (.algorithmExpr mixed) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) => true
  | _ => false

#guard mixedCommaSequenceConstructPreservesRootSlots

def sequenceSpreadAfterSequenceConstructMatchesSequenceValueForm : Bool :=
  let concise :=
    sequenceSpread (.sequenceConstruct (.num 1) (.num 2))
  let sequenceValue :=
    sequenceSpread (.capture [.sequenceConstruct (.num 1) (.num 2)])
  match runFlat concise, runFlat sequenceValue with
  | Except.ok [1, 2], Except.ok [1, 2] => true
  | _, _ => false

#guard sequenceSpreadAfterSequenceConstructMatchesSequenceValueForm

-- Single-collecting `X(*values)` collects the supplied argument slots as one exact
-- list: the explicit-spread form `X((1, b)*)` supplies two items
-- (`values = [1, (2, 3)]`, count 2), while the constructed sequence-value form
-- `X((1, b))` supplies ONE grouped argument (`values = [(1, (2, 3))]`,
-- count 1). Exact segment collection removed the old grouped/spread coincidence.
def sequenceSpreadAfterSequenceConstructMatchesConstructedSequenceValue : Bool :=
  let countValues := algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .dotCall (.param "values") "count" none
  ]
  let multiB := alg [] [] [] [.num 2, .num 3]
  let explicitSpreadForm := algPrivate [] [] [("b", multiB), ("X", countValues)] [
    .call (.resolve "X") [
      sequenceSpread (.sequenceConstruct (.num 1) (.resolve "b"))
    ]
  ]
  let constructedArgForm := algPrivate [] [] [("b", multiB), ("X", countValues)] [
    .call (.resolve "X") [
      .sequenceConstruct (.num 1) (.resolve "b")
    ]
  ]
  let explicitSpreadOk :=
    match runFlat (.algorithmExpr explicitSpreadForm) with
    | Except.ok [2] => true
    | _ => false
  let constructedArgOk :=
    match runFlat (.algorithmExpr constructedArgForm) with
    | Except.ok [1] => true
    | _ => false
  explicitSpreadOk && constructedArgOk

#guard sequenceSpreadAfterSequenceConstructMatchesConstructedSequenceValue

def missingOutputBodyAsResultStillFails : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [missingOutputBodyExpr])) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputBodyAsResultStillFails

def missingOutputBodyCountStillFails : Bool :=
  let dotCount :=
    match runResult (.dotCall missingOutputBodyExpr "count" none) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  let plainCount :=
    match runResult (.call (.resolve "count") [missingOutputBodyExpr]) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  dotCount && plainCount

#guard missingOutputBodyCountStillFails

def missingOutputBodyEqualityStillFails : Bool :=
  let leftMissing :=
    match runResult (.binary .eq missingOutputBodyExpr explicitEmptyExpr) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  let rightMissing :=
    match runResult (.binary .eq explicitEmptyExpr missingOutputBodyExpr) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  let bothMissing :=
    match runResult (.binary .eq missingOutputBodyExpr missingOutputBodyExpr) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  leftMissing && rightMissing && bothMissing

#guard missingOutputBodyEqualityStillFails

def missingOutputContainerPropertyStillFails : Bool :=
  let countFails :=
    match runResult (.algorithmExpr (algPrivate [] [] [("Lib", explicitEmptyNoOutputContainer)] [
      .dotCall (.resolve "Lib") "count" none
    ])) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  let equalityFails :=
    match runResult (.algorithmExpr (algPrivate [] [] [("Lib", explicitEmptyNoOutputContainer)] [
      .binary .eq (.resolve "Lib") explicitEmptyExpr
    ])) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  countFails && equalityFails

#guard missingOutputContainerPropertyStillFails

--------------------------------------------------------------------------------
-- explicit algorithm params require output
--------------------------------------------------------------------------------

def noOutputHelperContainer : Algorithm :=
  algPrivate [] [] [("Prop", alg [] [] [] [.num 7])] []

def invalidExplicitParamClauseAlg : Algorithm :=
  Algorithm.elaborateClauseDefinition (KatLang.Pattern.bind "x") noOutputHelperContainer

def explicitParamsWithoutOutputRejected : Bool :=
  match KatLang.runEvalM (KatLang.validateExplicitParamOutputInvariant invalidExplicitParamClauseAlg) with
  | Except.error Error.explicitParamsRequireOutput => true
  | _ => false

#guard explicitParamsWithoutOutputRejected

def explicitParamsWithoutOutputRejectedAtRun : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Algo", invalidExplicitParamClauseAlg)] [.num 0])) with
  | Except.error err => innermostIsExplicitParamsRequireOutput err
  | Except.ok _ => false

#guard explicitParamsWithoutOutputRejectedAtRun

-- The stored Algorithm.mk field is the parameter-pattern LIST: a legal pattern
-- with ZERO captures (sequenceValue []) is still one explicit parameter
-- pattern, so an algorithm carrying it with empty output violates the
-- invariant in both root and property placement. C# twin:
-- ExplicitParameterOutputValidationTests (the C# walker must test the stored
-- ParameterPatterns list, not the flattened capture list).
def zeroCaptureAlg : Algorithm :=
  .mk none [KatLang.ParameterPattern.sequenceValue []] [] [] []

def zeroCapturePatternWithoutOutputRejectedAtRoot : Bool :=
  match runResult (.algorithmExpr zeroCaptureAlg) with
  | Except.error err => innermostIsExplicitParamsRequireOutput err
  | Except.ok _ => false

#guard zeroCapturePatternWithoutOutputRejectedAtRoot

def zeroCapturePatternWithoutOutputRejectedInPropertyPosition : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("G", zeroCaptureAlg)] [.num 7])) with
  | Except.error err => innermostIsExplicitParamsRequireOutput err
  | Except.ok _ => false

#guard zeroCapturePatternWithoutOutputRejectedInPropertyPosition

def parameterizedChildPropertyContainer : Algorithm :=
  algPrivate [] [] [("Prop", alg ["x", "y"] [] [] [.num 7])] []

def parameterizedChildPropertyWithoutOuterParamsStillValid : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Algo", parameterizedChildPropertyContainer)] [
    .dotCall (.resolve "Algo") "Prop" (some [.num 1, .num 2])
  ])) with
  | Except.ok [7] => true
  | _ => false

#guard parameterizedChildPropertyWithoutOuterParamsStillValid

-- Test 3: Ordinary-dot lexical fallback
-- Receiver has no G, but lexical scope defines G(x) = x * 2
-- Receiver output = 5 → 10
def lexicalGAlg : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]

def outer3 : Algorithm :=
  algPrivate [] [] [("G", lexicalGAlg)] [
    .dotCall (.algorithmExpr (alg [] [] [] [.num 5])) "G" none
  ]

def test3 : Bool :=
  match runFlat (.algorithmExpr outer3) with
  | Except.ok [10] => true
  | _ => false

#guard test3
-- EXPECTED: Except.ok [10]
#eval runFlat (.algorithmExpr outer3)

--------------------------------------------------------------------------------
-- Higher-order dot fallback: the ELABORATED lexical-fallback identity
-- After structural member lookup fails, `receiver.F(args...)` invokes the dot
-- edge's STORED fallback — `.param "F"` after front-end elaboration decides
-- the member is a parameter reference, `.resolve "F"` otherwise — through
-- canonical `resolveAlg`.
-- No runtime environment reconstructs the Param-vs-Resolve decision.
--------------------------------------------------------------------------------

-- `{a+1}`: the one-parameter increment algorithm passed as the `t` argument.
def higherOrderDotIncrement : Algorithm :=
  alg ["a"] [] [] [.binary .add (.param "a") (.num 1)]

-- K(a, t) = t(a) — plain-call control.
def higherOrderPlainCallK : Algorithm :=
  alg ["a", "t"] [] [] [.call (.param "t") [.param "a"]]

def higherOrderPlainCallControl : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", higherOrderPlainCallK)] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard higherOrderPlainCallControl

-- K(a, t) = a.t — elaborated form: the member's fallback identity is
-- `.param "t"` (the front-end's decision), so the dot spelling agrees with
-- `t(a)` by consuming the same canonical parameter resolution.
def higherOrderDotParamK : Algorithm :=
  alg ["a", "t"] [] [] [.dotMember (.param "a") "t" (.param "t") none]

def higherOrderDotParamMemberResolvesStoredParamFallback : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", higherOrderDotParamK)] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard higherOrderDotParamMemberResolvesStoredParamFallback

-- K(a, t) = {a.t} — nested scope: the front-end still elaborates the member's
-- fallback to `.param "t"` (captured ancestor parameter), and the stored
-- identity rides the node regardless of the runtime scope topology.
def higherOrderDotCapturedParamK : Algorithm :=
  alg ["a", "t"] [] [] [
    .algorithmExpr (alg [] [] [] [.dotMember (.param "a") "t" (.param "t") none])
  ]

def higherOrderDotParamMemberResolvesCapturedParameter : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", higherOrderDotCapturedParamK)] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard higherOrderDotParamMemberResolvesCapturedParameter

-- Ordinary lexical fallback uses the same ownership-first lookup as a direct
-- callee name when the callable is owned by the dot-call algorithm's immediate
-- parent. Both output rows must therefore select the same `t` declaration.
def higherOrderImmediateParentT : Algorithm :=
  alg ["a"] [] [] [.binary .add (.param "a") (.num 2)]

def higherOrderImmediateParentK : Algorithm :=
  alg ["a"] [] [] [
    .dotCall (.param "a") "t" none,
    .call (.resolve "t") [.param "a"]
  ]

def higherOrderImmediateParentLexicalFallbackMatchesDirectCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Outer", algPrivate [] [] [
      ("t", higherOrderImmediateParentT),
      ("K", higherOrderImmediateParentK)
    ] [.call (.resolve "K") [.num 7]])
  ] [.resolve "Outer"])) with
  | Except.ok [9, 9] => true
  | _ => false

#guard higherOrderImmediateParentLexicalFallbackMatchesDirectCall

-- The same law crosses more than one lexical parent and obeys nearest-owner
-- shadowing: K is owned by Inner, the nearer `t` is owned by Outer, and the
-- root's same-name property must not win for either spelling.
def higherOrderGrandparentRootT : Algorithm :=
  alg ["a"] [] [] [.binary .add (.param "a") (.num 100)]

def higherOrderGrandparentNearT : Algorithm :=
  alg ["a"] [] [] [.binary .add (.param "a") (.num 10)]

def higherOrderGrandparentLexicalFallbackMatchesDirectCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("t", higherOrderGrandparentRootT),
    ("Outer", algPrivate [] [] [
      ("t", higherOrderGrandparentNearT),
      ("Inner", algPrivate [] [] [
        ("K", higherOrderImmediateParentK)
      ] [.call (.resolve "K") [.num 7]])
    ] [.resolve "Inner"])
  ] [.resolve "Outer"])) with
  | Except.ok [17, 17] => true
  | _ => false

#guard higherOrderGrandparentLexicalFallbackMatchesDirectCall

-- Value-bound parameter parity: `K(7, 5)` fails with the SAME canonical
-- parameter-resolution error for `t(a)` and `a.t` — notAnAlgorithm "param(t)".
def higherOrderValueBoundPlainCallIsParamError : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("K", higherOrderPlainCallK)] [
    .call (.resolve "K") [.num 7, .num 5]
  ])) with
  | Except.error err => innermostIsNotAnAlgorithm "param(t)" err
  | Except.ok _ => false

#guard higherOrderValueBoundPlainCallIsParamError

def higherOrderValueBoundDotCallIsParamError : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("K", higherOrderDotParamK)] [
    .call (.resolve "K") [.num 7, .num 5]
  ])) with
  | Except.error err => innermostIsNotAnAlgorithm "param(t)" err
  | Except.ok _ => false

#guard higherOrderValueBoundDotCallIsParamError

-- Shadow rule (front-end elaborated): inside G(x) = x.t, `t` is NOT a
-- parameter of G and the visible property `t = 5` keeps the member's fallback
-- identity `.resolve "t"` (the `Expr.dotCall` sugar), so the fallback stays
-- LEXICAL: calling the zero-parameter property with the injected receiver is
-- arityMismatch 0 1 — exactly like the plain form `t(x)` written in G's body.
def higherOrderShadowG : Algorithm :=
  alg ["x"] [] [] [.dotCall (.param "x") "t" none]

def higherOrderShadowK : Algorithm :=
  alg ["a", "t"] [] [] [.call (.resolve "G") [.param "a"]]

def higherOrderShadowedDotMemberStaysLexical : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("t", alg [] [] [] [.num 5]),
    ("G", higherOrderShadowG),
    ("K", higherOrderShadowK)
  ] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.error err => innermostIsArityMismatch 0 1 err
  | Except.ok _ => false

#guard higherOrderShadowedDotMemberStaysLexical

-- Local parameter precedence: the front-end stores `.param "t"` for a member
-- that is a parameter of the current algorithm even when a same-name property
-- is visible, so the parameter wins exactly as for a bare callee name.
def higherOrderLocalParamBeatsProperty : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("t", alg [] [] [] [.num 5]),
    ("K", higherOrderDotParamK)
  ] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard higherOrderLocalParamBeatsProperty

-- A parameter bound to a BUILTIN algorithm takes the stored-Param channel too:
-- `K((1, 2, 3), count)` with `K(a, t) = a.t` calls builtin `count` with the
-- receiver as its one ordinary collection argument — the same boundary the
-- plain form `t(a)` uses (NOT the sequence-builtin dot-receiver view).
def higherOrderBuiltinBoundParamDotCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", higherOrderDotParamK)] [
    .call (.resolve "K") [.capture [.num 1, .num 2, .num 3], .resolve "count"]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard higherOrderBuiltinBoundParamDotCall

-- An UNELABORATED (hand-built) dot edge keeps plain lexical-fallback
-- semantics: the `Expr.dotCall` sugar stores `.resolve "t"`, so with no
-- lexical `t` in sight the member fails as unknownName even though a
-- dynamically visible `t` binding exists — the stored identity, not the
-- runtime environment, decides.
def higherOrderUnelaboratedDotKeepsLexicalFallback : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("K", alg ["a", "t"] [] [] [.dotCall (.param "a") "t" none])
  ] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.error err => innermostIsUnknownName "t" err
  | Except.ok _ => false

#guard higherOrderUnelaboratedDotKeepsLexicalFallback

--------------------------------------------------------------------------------
-- Grace composed with DotCall (`a~.t` / `a.~t`)
-- The C# front end consumes ordinary postfix Grace on receiver `a` or ordinary
-- prefix Grace on fallback occurrence `t`. Base source order (a,t) becomes
-- (t,a) in either graced form through the one general Grace pass. All three
-- sources encode the SAME `dotMember` body here; Lean has no Grace construct
-- and no source-spelling-specific evaluation rule.
--------------------------------------------------------------------------------

-- `K = a.t`, `K = a~.t`, and `K = a.~t` share this ONE body.
def graceDotBody : KatLang.Expr :=
  .dotMember (.param "a") "t" (.param "t") none

def ordinaryDotEdgeK : Algorithm :=
  alg ["a", "t"] [] [] [graceDotBody]

def postfixGraceDotK : Algorithm :=
  alg ["t", "a"] [] [] [graceDotBody]

def prefixMemberGraceDotK : Algorithm :=
  alg ["t", "a"] [] [] [graceDotBody]

-- Direct source `K = t(a)` has its own occurrence order (t, a), even though
-- the dot fallback arm later invokes the same callable/receiver arrangement.
-- Invocation order does not determine the containing algorithm's parameters.
def sourceOrderedDirectCallK : Algorithm :=
  alg ["t", "a"] [] [] [.call (.param "t") [.param "a"]]

def sourceOrderedDirectCallInvokesBoundAlgorithm : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", sourceOrderedDirectCallK)] [
    .call (.resolve "K") [.algorithmExpr higherOrderDotIncrement, .num 7]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard sourceOrderedDirectCallInvokesBoundAlgorithm

def graceDotMemberInvokesBoundAlgorithm : Bool :=
  let ordinary :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("K", ordinaryDotEdgeK)] [
      .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
    ])) with
    | Except.ok [8] => true
    | _ => false
  let postfixGraced :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("K", postfixGraceDotK)] [
      .call (.resolve "K") [.algorithmExpr higherOrderDotIncrement, .num 7]
    ])) with
    | Except.ok [8] => true
    | _ => false
  let prefixGraced :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("K", prefixMemberGraceDotK)] [
      .call (.resolve "K") [.algorithmExpr higherOrderDotIncrement, .num 7]
    ])) with
    | Except.ok [8] => true
    | _ => false
  ordinary && postfixGraced && prefixGraced

#guard graceDotMemberInvokesBoundAlgorithm

-- Structural precedence is SHARED: `Obj.V` and `Obj~.V` are the same edge, so
-- both read Obj's structural property (42) even though a lexical `V` exists.
-- Only the written CALL `V(Obj)` reaches the lexical declaration (99).
-- Obj also defines output so the call form binds Obj's value.
def graceDotSplitObj : Algorithm :=
  algPrivate [] [] [("V", alg [] [] [] [.num 42])] [.num 0]

def graceDotSplitLexicalV : Algorithm :=
  alg ["x"] [] [] [.num 99]

def graceDotSplitRoot (edge : KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("V", graceDotSplitLexicalV),
    ("Obj", graceDotSplitObj)
  ] [edge])

def ordinaryDotKeepsStructuralPrecedence : Bool :=
  match runFlat (graceDotSplitRoot (.dotCall (.resolve "Obj") "V" none)) with
  | Except.ok [42] => true
  | _ => false

#guard ordinaryDotKeepsStructuralPrecedence

def writtenCallReachesLexicalDeclaration : Bool :=
  match runFlat (graceDotSplitRoot
    (.call (.resolve "V") [.resolve "Obj"])) with
  | Except.ok [99] => true
  | _ => false

#guard writtenCallReachesLexicalDeclaration

-- Extra explicit arguments follow the receiver: `v~.F(1, 2)` is the ordinary
-- dot edge `v.F(1, 2)`, whose fallback arm calls `F(v, 1, 2)` (encoded here
-- with the receiver value inline).
def graceDotExtraArgs : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("F", alg ["x", "y", "z"] [] [] [
      .binary .add
        (.binary .add
          (.binary .mul (.param "x") (.num 100))
          (.binary .mul (.param "y") (.num 10)))
        (.param "z")])
  ] [
    .dotMember (.num 3) "F" (.resolve "F") (some [.num 1, .num 2])
  ])) with
  | Except.ok [312] => true
  | _ => false

#guard graceDotExtraArgs

-- Receiver-segment supply is ordinary dot semantics, so Grace inherits
-- it unchanged: a WRITTEN GROUP receiver supplies its rows to the flat
-- collecting parameter (count 2), while a NAMED receiver supplies one item
-- (count 1). A written group is not eligible for postfix Grace; the executable
-- named edge remains the same ordinary dot.
def graceDotCountItemsAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [
    .dotCall (.param "items") "count" none
  ]

def graceDotCountItemsRoot (edge : KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("S", alg [] [] [] [.num 1, .num 2]),
    ("CountItems", graceDotCountItemsAlg)
  ] [edge])

def namedReceiverSuppliesOneItem : Bool :=
  match runFlat (graceDotCountItemsRoot
    (.dotCall (.resolve "S") "CountItems" none)) with
  | Except.ok [1] => true
  | _ => false

#guard namedReceiverSuppliesOneItem

def writtenGroupReceiverSegmentSupplyContrast : Bool :=
  match runFlat (graceDotCountItemsRoot
    (.dotCall (.capture [.num 1, .num 2]) "CountItems" none)) with
  | Except.ok [2] => true
  | _ => false

#guard writtenGroupReceiverSegmentSupplyContrast

-- Chaining composes by ordinary rules: `a~.t.string` is the ordinary chain
-- `a.t.string` — an ordinary `.string` dot on the first edge's result.
def graceDotChainOrdinaryString : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("K",
    alg ["t", "a"] [] [] [
      .dotCall (.dotMember (.param "a") "t" (.param "t") none) "string" none
    ])
  ] [
    .call (.resolve "K") [.algorithmExpr higherOrderDotIncrement, .num 7]
  ])) with
  | Except.ok (KatLang.Result.str "8") => true
  | _ => false

#guard graceDotChainOrdinaryString

-- The `.string` value intrinsic is dot-only. Grace does NOT switch
-- channels: `v~.string` is the ordinary dot edge, so
-- it keeps the intrinsic ("5") even when a lexical `string` callable is
-- visible — only the written CALL reaches that declaration (105).
def dotStringIntrinsicIsSharedByBothSpellings : Bool :=
  let stringFn : Algorithm := alg ["x"] [] [] [.binary .add (.param "x") (.num 100)]
  let root (edge : KatLang.Expr) : KatLang.Expr :=
    .algorithmExpr (algPrivate [] [] [("string", stringFn)] [edge])
  let dotEdgeIntrinsic :=
    match runResult (root (.dotCall (.num 5) "string" none)) with
    | Except.ok (KatLang.Result.str "5") => true
    | _ => false
  let writtenCallReachesDeclaration :=
    match runResult (root (.call (.resolve "string") [.num 5])) with
    | Except.ok (KatLang.Result.atom 105) => true
    | _ => false
  let callWithoutDeclaration :=
    match runResult (.algorithmExpr (algPrivate [] [] [] [
      .call (.resolve "string") [.num 5]
    ])) with
    | Except.error err => innermostIsUnknownName "string" err
    | Except.ok _ => false
  dotEdgeIntrinsic && writtenCallReachesDeclaration && callWithoutDeclaration

#guard dotStringIntrinsicIsSharedByBothSpellings

-- A grace-marked open target (`open M~.C`) is a C# parse error — `open`
-- consumes structural algorithm identity and has no parameter inference to
-- reorder — so it never reaches Lean. The ORDINARY dotted open target is the
-- valid form and resolves through the argumentless dot path. The body must
-- reference an opened name so the (lazy) open resolution runs.
def ordinaryDottedOpenTargetResolves : Bool :=
  let inner : Algorithm :=
    Algorithm.mk none [] [] [publicProp "V" (alg [] [] [] [.num 5])] []
  let outer : Algorithm :=
    Algorithm.mk none [] [] [publicProp "C" inner] []
  match runFlat (.algorithmExpr (Algorithm.mk none []
    [.dotCall (.resolve "M") "C" none]
    [privateProp "M" outer]
    [.resolve "V"])) with
  | Except.ok [5] => true
  | _ => false

#guard ordinaryDottedOpenTargetResolves

def userCollectingDotCallCountItemsAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [
    .dotCall (.param "items") "count" none
  ]

def userCollectingDotCallCountItemsRoot : Algorithm :=
  algPrivate [] [] [("CountItems", userCollectingDotCallCountItemsAlg)] [
    .dotCall (.capture [.num 1, .num 2]) "CountItems" none
  ]

-- Ordinary dot-call receiver injection under the general segment rule:
-- `(1, 2).CountItems` injects the written group as ONE leading segment, and
-- the collecting parameter allocated that segment consumes the segment's raw
-- row supply, so `items = [1, 2]` and `items.count` is 2. (A direct call
-- `CountItems((1, 2))` still collects the one written grouped argument.)
def userCollectingDotCallReceiverSuppliesRowItems : Bool :=
  match runFlat (.algorithmExpr userCollectingDotCallCountItemsRoot) with
  | Except.ok [2] => true
  | _ => false

#guard userCollectingDotCallReceiverSuppliesRowItems

def userCollectingDotCallMeanAlg : Algorithm :=
  algWithParameters [{ name := "vector", kind := .collecting }] [] [] [
    .dotCall (.param "vector") "sum" none
  ]

def userCollectingDotCallMeanRoot : Algorithm :=
  algPrivate [] [] [("Mean", userCollectingDotCallMeanAlg)] [
    .dotCall (.capture [.num 1, .num 2]) "Mean" none
  ]

-- `(1, 2).Mean` binds `vector = [1, 2]` — the collector consumes the written
-- group receiver's row supply — so `vector.sum` is 3. This is the headline
-- correction of the general segment rule (formerly the receiver was one
-- captured sequence element and the sum hit the numeric constraint).
def userCollectingDotCallReceiverSumsSuppliedItems : Bool :=
  match runFlat (.algorithmExpr userCollectingDotCallMeanRoot) with
  | Except.ok [3] => true
  | _ => false

#guard userCollectingDotCallReceiverSumsSuppliedItems

def userNonCollectingDotCallCountOneAlg : Algorithm :=
  alg ["value"] [] [] [
    .dotCall (.param "value") "count" none
  ]

def userNonCollectingDotCallCountOneRoot : Algorithm :=
  algPrivate [] [] [("CountOne", userNonCollectingDotCallCountOneAlg)] [
    .dotCall (.capture [.num 1, .num 2]) "CountOne" none
  ]

def userNonCollectingDotCallReceiverIsOneSequenceArgument : Bool :=
  match runFlat (.algorithmExpr userNonCollectingDotCallCountOneRoot) with
  | Except.ok [2] => true
  | _ => false

#guard userNonCollectingDotCallReceiverIsOneSequenceArgument

def flatCollectingSlotQmeanAlg : Algorithm :=
  algWithParameters [{ name := "args", kind := .collecting }] [] [] [
    .binary .div
      (.dotCall (.param "args") "sum" none)
      (.dotCall (.param "args") "count" none)
  ]

def flatCollectingSlotVectorAlg : Algorithm :=
  alg [] [] [] [.call (.resolve "range") [.num 1, .num 3]]

def flatCollectingSlotQmeanNormalRoot : Algorithm :=
  algPrivate [] [] [("Vector", flatCollectingSlotVectorAlg), ("Qmean", flatCollectingSlotQmeanAlg)] [
    .call (.resolve "Qmean") [.resolve "Vector"]
  ]

-- `Qmean(Vector)` supplies ONE grouped argument, so the collecting parameter collects
-- `args = [Vector]` and `args.sum` hits the numeric element constraint.
-- Supplying the items is the explicit-spread call `Qmean(Vector*)` below.
def flatCollectingSlotQmeanSingleGroupedArgumentIsNumericConstraintError : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotQmeanNormalRoot) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard flatCollectingSlotQmeanSingleGroupedArgumentIsNumericConstraintError

def flatCollectingSlotQmeanExplicitRoot : Algorithm :=
  algPrivate [] [] [("Vector", flatCollectingSlotVectorAlg), ("Qmean", flatCollectingSlotQmeanAlg)] [
    .call (.resolve "Qmean") [sequenceSpread (.resolve "Vector")]
  ]

-- The explicit-spread call `Qmean(Vector*)` supplies Vector's items as
-- separate argument slots, so `args = [1, 2, 3]` and the mean is 2.
def flatCollectingSlotQmeanExplicitSpreadSuppliesItems : Bool :=
  match runFlat (.algorithmExpr flatCollectingSlotQmeanExplicitRoot) with
  | Except.ok [2] => true
  | _ => false

#guard flatCollectingSlotQmeanExplicitSpreadSuppliesItems

def flatCollectingSlotQmeanDotRoot : Algorithm :=
  algPrivate [] [] [("Vector", flatCollectingSlotVectorAlg), ("Qmean", flatCollectingSlotQmeanAlg)] [
    .dotCall (.resolve "Vector") "Qmean" none
  ]

-- `Vector.Qmean` is `Qmean(Vector)`: the receiver is one leading argument
-- slot, so the grouped-argument numeric-constraint error matches the plain
-- call above.
def flatCollectingSlotQmeanDotCallMatchesGroupedCall : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotQmeanDotRoot) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard flatCollectingSlotQmeanDotCallMatchesGroupedCall

def flatCollectingSlotCountAlg : Algorithm :=
  algWithParameters [{ name := "args", kind := .collecting }] [] [] [
    .dotCall (.param "args") "count" none
  ]

def flatCollectingSlotValuesAlg : Algorithm :=
  alg [] [] [] [.num 10, .num 20]

def flatCollectingSlotCountValuesRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Count", flatCollectingSlotCountAlg)] [
    .call (.resolve "Count") [.resolve "Values"]
  ]

-- `Count(Values)` with a multi-output property supplies ONE argument boundary
-- (a property reference is a value boundary), so the collecting parameter collects
-- `args = [(10, 20)]` and the count is 1; `Count(Values*)` supplies 2 items.
def flatCollectingSlotMultiOutputPropertyIsOneCapturedSlot : Bool :=
  match runFlat (.algorithmExpr flatCollectingSlotCountValuesRoot) with
  | Except.ok [1] => true
  | _ => false

#guard flatCollectingSlotMultiOutputPropertyIsOneCapturedSlot

def flatCollectingSlotSequenceValuePairAlg : Algorithm :=
  alg [] [] [] [.capture [.num 10, .num 20]]

def flatCollectingSlotCountSequenceValuePairRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatCollectingSlotSequenceValuePairAlg), ("Count", flatCollectingSlotCountAlg)] [
    .call (.resolve "Count") [.resolve "Pair"]
  ]

-- A visible sequence-value property is likewise ONE captured argument slot:
-- `Count(Pair)` collects `args = [(10, 20)]`, so the count is 1.
def flatCollectingSlotVisibleSequenceValueIsOneCapturedSlot : Bool :=
  match runFlat (.algorithmExpr flatCollectingSlotCountSequenceValuePairRoot) with
  | Except.ok [1] => true
  | _ => false

#guard flatCollectingSlotVisibleSequenceValueIsOneCapturedSlot

def flatCollectingSlotSumAlg : Algorithm :=
  algWithParameters [
    { name := "values", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .binary .add (.dotCall (.param "values") "sum" none) (.param "last")
  ]

def flatCollectingSlotSumNormalRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Sum", flatCollectingSlotSumAlg)] [
    .call (.resolve "Sum") [.resolve "Values", .num 7]
  ]

-- `Sum(Values, 7)`: the suffix takes `last = 7` and the collecting parameter collects the one
-- grouped argument (`values = [(10, 20)]`), so `values.sum` hits the numeric
-- element constraint. `Sum(Values*, 7)` below is the item-supplying form.
def flatCollectingSlotGroupedMiddleArgumentIsNumericConstraintError : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotSumNormalRoot) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard flatCollectingSlotGroupedMiddleArgumentIsNumericConstraintError

def flatCollectingSlotSumExplicitRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Sum", flatCollectingSlotSumAlg)] [
    .call (.resolve "Sum") [sequenceSpread (.resolve "Values")]
  ]

def flatCollectingSlotExplicitSpreadCanSatisfySuffix : Bool :=
  match runFlat (.algorithmExpr flatCollectingSlotSumExplicitRoot) with
  | Except.ok [30] => true
  | _ => false

#guard flatCollectingSlotExplicitSpreadCanSatisfySuffix

def flatCollectingSlotSumSingleNormalRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Sum", flatCollectingSlotSumAlg)] [
    .call (.resolve "Sum") [.resolve "Values"]
  ]

-- Sum(*values, last) receives one sequence-valued argument. Function-call
-- binding does not implicitly open it, so `last` receives the sequence value and
-- the old numeric body no longer succeeds.
def flatCollectingSlotNormalSegmentDoesNotSatisfySuffixBySpreading : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotSumSingleNormalRoot) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard flatCollectingSlotNormalSegmentDoesNotSatisfySuffixBySpreading

def flatCollectingSlotSumDotMissingSuffixRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Sum", flatCollectingSlotSumAlg)] [
    .dotCall (.resolve "Values") "Sum" none
  ]

-- Same boundary through a dot-call receiver: Values.Sum passes the receiver as
-- one leading argument unless explicit spread is used.
def flatCollectingSlotDotReceiverDoesNotSatisfySuffixBySpreading : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotSumDotMissingSuffixRoot) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard flatCollectingSlotDotReceiverDoesNotSatisfySuffixBySpreading

def flatCollectingSlotSumDotSuffixRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Sum", flatCollectingSlotSumAlg)] [
    .dotCall (.resolve "Values") "Sum" (some [.num 7])
  ]

-- `Values.Sum(7)` is `Sum(Values, 7)`: the receiver is one leading argument
-- slot, so the grouped-middle numeric-constraint error matches the plain call.
def flatCollectingSlotDotReceiverWithSuffixMatchesGroupedCall : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotSumDotSuffixRoot) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard flatCollectingSlotDotReceiverWithSuffixMatchesGroupedCall

def flatFixedSlotAddAlg : Algorithm :=
  alg ["x", "y"] [] [] [.binary .add (.param "x") (.param "y")]

def flatFixedSlotAddPairRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatCollectingSlotValuesAlg), ("Add", flatFixedSlotAddAlg)] [
    .call (.resolve "Add") [.resolve "Pair"]
  ]

def flatFixedCallStillDoesNotAutoSpread : Bool :=
  match runResult (.algorithmExpr flatFixedSlotAddPairRoot) with
  | Except.error _ => true
  | Except.ok _ => false

#guard flatFixedCallStillDoesNotAutoSpread

def flatFixedSlotAddPairExplicitRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatCollectingSlotValuesAlg), ("Add", flatFixedSlotAddAlg)] [
    .call (.resolve "Add") [sequenceSpread (.resolve "Pair")]
  ]

def flatFixedCallExplicitSpreadStillWorks : Bool :=
  match runFlat (.algorithmExpr flatFixedSlotAddPairExplicitRoot) with
  | Except.ok [30] => true
  | _ => false

#guard flatFixedCallExplicitSpreadStillWorks

def collectingForwardingCountItemsAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [
    .dotCall (.param "items") "count" none
  ]

-- Collecting-parameter forwarding is ordinary list spread: `Use(*values) =
-- CountItems(values*)` re-supplies exactly the collected items
-- (spread(collect(xs)) = xs). The root call spreads its grouped sequence so the
-- collecting parameter collects the three items.
def collectingForwardingUseValuesAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .call (.resolve "CountItems") [sequenceSpread (.param "values")]
  ]

def collectingForwardingTopLevelRoot : Algorithm :=
  algPrivate [] [] [("CountItems", collectingForwardingCountItemsAlg), ("Use", collectingForwardingUseValuesAlg)] [
    .call (.resolve "Use") [sequenceSpread (sequenceItems [.num 1, .num 2, .num 3])]
  ]

def collectingForwardingTopLevelCaptureStillWorks : Bool :=
  match runFlat (.algorithmExpr collectingForwardingTopLevelRoot) with
  | Except.ok [3] => true
  | _ => false

#guard collectingForwardingTopLevelCaptureStillWorks

-- The bare-name forward `CountItems(values)` passes the collected list as ONE
-- list argument, so the callee's collecting parameter holds one element (the list): forwarding
-- items requires the explicit spread above.
def collectingForwardingBareNameUseValuesAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .call (.resolve "CountItems") [.param "values"]
  ]

def collectingForwardingBareNamePassesOneListArgument : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountItems", collectingForwardingCountItemsAlg),
    ("Use", collectingForwardingBareNameUseValuesAlg)
  ] [
    .call (.resolve "Use") [.num 1, .num 2, .num 3]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard collectingForwardingBareNamePassesOneListArgument

def collectingForwardingUseSequenceValueHistoryAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }]
  ] [] [] [
    .call (.resolve "CountItems") [sequenceSpread (.param "history")]
  ]

def collectingForwardingSequenceValueRoot : Algorithm :=
  algPrivate [] [] [("CountItems", collectingForwardingCountItemsAlg), ("Use", collectingForwardingUseSequenceValueHistoryAlg)] [
    .call (.resolve "Use") [.capture [.num 1, .num 2, .num 3]]
  ]

def collectingForwardingSequenceValueCaptureStillWorks : Bool :=
  match runFlat (.algorithmExpr collectingForwardingSequenceValueRoot) with
  | Except.ok [3] => true
  | _ => false

#guard collectingForwardingSequenceValueCaptureStillWorks

def sequenceValueCollectingBoundaryCountSequenceValueAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "items", kind := .collecting }]
  ] [] [] [
    .dotCall (.param "items") "count" none
  ]

def sequenceValueCollectingBoundaryRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatCollectingSlotValuesAlg), ("CountSequenceValue", sequenceValueCollectingBoundaryCountSequenceValueAlg)] [
    .call (.resolve "CountSequenceValue") [.resolve "Pair"]
  ]

def sequenceValueCollectingBoundaryDoesNotUseFlatSlotSpread : Bool :=
  match runFlat (.algorithmExpr sequenceValueCollectingBoundaryRoot) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceValueCollectingBoundaryDoesNotUseFlatSlotSpread

def explicitCallSiteSequenceValue123 : Nat -> KatLang.Expr
  | 0 => .capture [.num 1, .num 2, .num 3]
  | Nat.succ depth => .capture [explicitCallSiteSequenceValue123 depth]

def explicitCallSiteSequenceValueLeftNested : KatLang.Expr :=
  .capture [.capture [.num 1, .num 2], .num 3]

def explicitCallSiteSequenceValueRightNested : KatLang.Expr :=
  .capture [.num 1, .capture [.num 2, .num 3]]

def explicitCallSiteSequenceValueCountSequenceValue1Alg : Algorithm :=
  algWithParameterPatterns [
    .capture { name := "values", kind := .collecting }
  ] [] [] [
    .dotCall (.param "values") "count" none
  ]

def explicitCallSiteSequenceValueCountSequenceValue2Alg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "values", kind := .collecting }]
  ] [] [] [
    .dotCall (.param "values") "count" none
  ]

def explicitCallSiteSequenceValueCountSequenceValue3Alg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.sequenceValue [.capture { name := "values", kind := .collecting }]]
  ] [] [] [
    .dotCall (.param "values") "count" none
  ]

def explicitCallSiteSequenceValueMatrixRoot : Algorithm :=
  algPrivate [] [] [
    ("CountSequenceValue1", explicitCallSiteSequenceValueCountSequenceValue1Alg),
    ("CountSequenceValue2", explicitCallSiteSequenceValueCountSequenceValue2Alg),
    ("CountSequenceValue3", explicitCallSiteSequenceValueCountSequenceValue3Alg)
  ] [
    .call (.resolve "CountSequenceValue1") [explicitCallSiteSequenceValue123 0],
    .call (.resolve "CountSequenceValue1") [explicitCallSiteSequenceValue123 1],
    .call (.resolve "CountSequenceValue2") [explicitCallSiteSequenceValue123 0],
    .call (.resolve "CountSequenceValue2") [explicitCallSiteSequenceValue123 1],
    .call (.resolve "CountSequenceValue2") [explicitCallSiteSequenceValue123 2],
    .call (.resolve "CountSequenceValue3") [explicitCallSiteSequenceValue123 1],
    .call (.resolve "CountSequenceValue3") [explicitCallSiteSequenceValue123 2],
    .call (.resolve "CountSequenceValue2") [explicitCallSiteSequenceValueLeftNested],
    .call (.resolve "CountSequenceValue2") [explicitCallSiteSequenceValueRightNested]
  ]

-- CountSequenceValue1 (flat collecting) collects the ONE grouped argument, so both
-- written depths count 1. CountSequenceValue2/3 (sequence-value patterns) open
-- exactly as many written grouping levels as they declare: at matching depth
-- the spread items collect to a three-element collected list (count 3), while one
-- EXTRA written level leaves a single grouped item in the collected list (count 1).
def sequenceValueCollectingParameterRespectsExplicitCallSiteSequenceValueDepth : Bool :=
  match runFlat (.algorithmExpr explicitCallSiteSequenceValueMatrixRoot) with
  | Except.ok [1, 1, 3, 1, 1, 3, 3, 2, 2] => true
  | _ => false

#guard sequenceValueCollectingParameterRespectsExplicitCallSiteSequenceValueDepth

def nestedSequenceValueCollectingParameterRejectsTooShallowExplicitSequenceValue : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("CountSequenceValue3", explicitCallSiteSequenceValueCountSequenceValue3Alg)
  ] [
    .call (.resolve "CountSequenceValue3") [explicitCallSiteSequenceValue123 0]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 3 err
  | _ => false

#guard nestedSequenceValueCollectingParameterRejectsTooShallowExplicitSequenceValue

def explicitPropertyReferenceSequenceValueRoot : Algorithm :=
  algPrivate [] [] [
    ("Inner", alg [] [] [] [explicitCallSiteSequenceValue123 0]),
    ("CountSequenceValue2", explicitCallSiteSequenceValueCountSequenceValue2Alg)
  ] [
    .call (.resolve "CountSequenceValue2") [.resolve "Inner"],
    .call (.resolve "CountSequenceValue2") [.capture [.resolve "Inner"]],
    .call (.resolve "CountSequenceValue2") [.capture [.capture [.resolve "Inner"]]]
  ]

-- A bare property reference opens through the deconstruction pattern
-- (count 3), while each written parenthes level around it is one grouped item
-- for the pattern's collecting binding (count 1): written grouping is not erased by segment
-- collection.
def explicitPropertyReferenceSequenceValueIsSourceBacked : Bool :=
  match runFlat (.algorithmExpr explicitPropertyReferenceSequenceValueRoot) with
  | Except.ok [3, 1, 1] => true
  | _ => false

#guard explicitPropertyReferenceSequenceValueIsSourceBacked

-- Test 4: Ambiguous ordinary-dot lexical fallback via opens (error case)
-- Two opens both export G → ambiguousOpen error
def libA : Algorithm :=
  alg [] [] [publicProp "G" (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)])] []

def libB : Algorithm :=
  alg [] [] [publicProp "G" (alg ["x"] [] [] [.binary .add (.param "x") (.num 2)])] []

def caller4 : Algorithm :=
  alg [] [.algorithmExpr libA, .algorithmExpr libB] [] [
    .dotCall (.algorithmExpr (alg [] [] [] [.num 5])) "G" none
  ]

def test4 : Bool :=
  match runResult (.algorithmExpr caller4) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test4
-- EXPECTED: Expect.error (Error.ambiguousOpen "G" [...])
#eval runResult (.algorithmExpr caller4)

-- Open resolution regressions
--------------------------------------------------------------------------------

def openPrivateHeadLib : Algorithm :=
  alg [] []
    [ publicProp "X" (alg [] [] [] [.num 1])
    , privateProp "Hidden" (alg [] [] [] [.num 2])
    , privateProp "PrivateSub" (alg [] [] [publicProp "Y" (alg [] [] [] [.num 3])] [])
    ]
    []

-- Models the surface form:
--   open Lib
--   Lib = { ... }
-- where the open appears first and `Lib` is defined later in the same body.
def openPrivateHeadLaterRoot : Algorithm :=
  algPrivate [] [.resolve "Lib"] [("Lib", openPrivateHeadLib)] [.resolve "X"]

def openPrivateHeadLaterWorks : Bool :=
  match runFlat (.algorithmExpr openPrivateHeadLaterRoot) with
  | Except.ok [1] => true
  | _ => false

#guard openPrivateHeadLaterWorks

def openDoesNotExposePrivateMemberRoot : Algorithm :=
  algPrivate [] [.resolve "Lib"] [("Lib", openPrivateHeadLib)] [.resolve "Hidden"]

def openDoesNotExposePrivateMember : Bool :=
  match runResult (.algorithmExpr openDoesNotExposePrivateMemberRoot) with
  | Except.error err => innermostIsUnknownName "Hidden" err
  | Except.ok _ => false

#guard openDoesNotExposePrivateMember

def openMissingHeadRoot : Algorithm :=
  alg [] [.resolve "Missing"] [] [.resolve "X"]

def openMissingHeadStillErrors : Bool :=
  match runResult (.algorithmExpr openMissingHeadRoot) with
  | Except.error err =>
      hasContext "while resolving open: Missing" err
      && innermostIsUnknownName "Missing" err
  | Except.ok _ => false

#guard openMissingHeadStillErrors

def openBuiltinTargetRoot : Algorithm :=
  alg [] [.resolve "if"] [] [.resolve "X"]

def openBuiltinTargetStillIllegal : Bool :=
  match runResult (.algorithmExpr openBuiltinTargetRoot) with
  | Except.error err =>
      hasContext "while resolving open: if" err
      && innermostIsIllegalInOpen "builtin 'if'" err
  | Except.ok _ => false

#guard openBuiltinTargetStillIllegal

def openQualifiedPrivatePathRoot : Algorithm :=
  algPrivate [] [.dotCall (.resolve "Lib") "PrivateSub" none] [("Lib", openPrivateHeadLib)] [.resolve "Y"]

def openQualifiedPrivatePathStillRestricted : Bool :=
  match runResult (.algorithmExpr openQualifiedPrivatePathRoot) with
  | Except.error err =>
      hasContext "while resolving open: Lib.PrivateSub" err
      && innermostIsNotPublicProperty "Lib" "PrivateSub" err
  | Except.ok _ => false

#guard openQualifiedPrivatePathStillRestricted

def publicWrapperPrivateHelperAlg : Algorithm :=
  alg ["Candidate"] [] [
    privateLocalProp "Step" .localCapturedAncestorParams
      (alg [] [] [] [.binary .add (.param "Candidate") (.num 1)])
  ] [.resolve "Step"]

def publicWrapperPrivateHelperApi : Algorithm :=
  alg ["N"] [] [] [
    .call (.resolve "PrivateHelper") [.param "N"]
  ]

def publicWrapperPrivateHelperLib : Algorithm :=
  alg [] [] [
    privateProp "PrivateHelper" publicWrapperPrivateHelperAlg,
    publicProp "PublicApi" publicWrapperPrivateHelperApi
  ] []

def publicWrapperPrivateHelperOpenRoot : Algorithm :=
  alg [] [.algorithmExpr publicWrapperPrivateHelperLib] [] [
    .call (.resolve "PublicApi") [.num 5]
  ]

def publicWrapperPrivateHelperImportsPublicApi : Bool :=
  match runFlat (.algorithmExpr publicWrapperPrivateHelperOpenRoot) with
  | Except.ok [6] => true
  | _ => false

#guard publicWrapperPrivateHelperImportsPublicApi

def publicWrapperPrivateHelperHiddenRoot : Algorithm :=
  alg [] [.algorithmExpr publicWrapperPrivateHelperLib] [] [
    .call (.resolve "PrivateHelper") [.num 5]
  ]

def publicWrapperPrivateHelperKeepsPrivateHelperHidden : Bool :=
  match runResult (.algorithmExpr publicWrapperPrivateHelperHiddenRoot) with
  | Except.error err => innermostIsUnknownName "PrivateHelper" err
  | Except.ok _ => false

#guard publicWrapperPrivateHelperKeepsPrivateHelperHidden

def openedMemberBuiltinIfAlg : Algorithm :=
  alg ["x"] [] [] [
    .call (.resolve "if") [
      .binary .gt (.param "x") (.num 0),
      .num 1,
      .num 0
    ]
  ]

def openedMemberBuiltinIfVec : Algorithm :=
  alg [] [] [publicProp "Test" openedMemberBuiltinIfAlg] []

def openedMemberBuiltinIfRoot : Algorithm :=
  algPrivate [] [.resolve "Vec"] [("Vec", openedMemberBuiltinIfVec)] [
    .call (.resolve "Test") [.num 35]
  ]

def openedMemberBuiltinIfWorks : Bool :=
  match runFlat (.algorithmExpr openedMemberBuiltinIfRoot) with
  | Except.ok [1] => true
  | _ => false

#guard openedMemberBuiltinIfWorks

def openedMemberBuiltinSumVec : Algorithm :=
  alg [] [] [publicProp "SumPair" (alg ["x", "y"] [] [] [
    .dotCall (.capture [.param "x", .param "y"]) "sum" none
  ])] []

def openedMemberBuiltinSumRoot : Algorithm :=
  algPrivate [] [.resolve "Vec"] [("Vec", openedMemberBuiltinSumVec)] [
    .call (.resolve "SumPair") [.num 3, .num 4]
  ]

def openedMemberBuiltinSumWorks : Bool :=
  match runFlat (.algorithmExpr openedMemberBuiltinSumRoot) with
  | Except.ok [7] => true
  | _ => false

#guard openedMemberBuiltinSumWorks

def inlineOpenedMemberBuiltinSumVec : Algorithm :=
  alg [] [] [publicProp "SumPair" (alg ["x", "y"] [] [] [
    .dotCall (.capture [.param "x", .param "y"]) "sum" none
  ])] []

def inlineOpenedMemberBuiltinSumRoot : Algorithm :=
  alg [] [.algorithmExpr inlineOpenedMemberBuiltinSumVec] [] [
    .call (.resolve "SumPair") [.num 3, .num 4]
  ]

def inlineOpenedMemberBuiltinSumWorks : Bool :=
  match runFlat (.algorithmExpr inlineOpenedMemberBuiltinSumRoot) with
  | Except.ok [7] => true
  | _ => false

#guard inlineOpenedMemberBuiltinSumWorks

def inlineOpenedMemberBuiltinSumShadowVec : Algorithm :=
  alg [] [] [publicProp "Use" (alg [] [] [] [
    .dotCall (.capture [.num 1, .num 2]) "sum" none
  ])] []

def inlineOpenedMemberBuiltinSumShadowRoot : Algorithm :=
  algPrivate [] [.algorithmExpr inlineOpenedMemberBuiltinSumShadowVec] [
    ("sum", alg [] [] [] [.num 99])
  ] [.resolve "Use"]

def inlineOpenedMemberBuiltinSumIgnoresOpenerShadow : Bool :=
  match runFlat (.algorithmExpr inlineOpenedMemberBuiltinSumShadowRoot) with
  | Except.ok [3] => true
  | _ => false

#guard inlineOpenedMemberBuiltinSumIgnoresOpenerShadow

def openedMemberDefinitionSiteCaptureVec : Algorithm :=
  alg [] [] [
    publicProp "Test" (alg ["x"] [] [] [.binary .add (.resolve "A") (.param "x")])
  ] []

def openedMemberDefinitionSiteCaptureScope : Algorithm :=
  algPrivate [] [.resolve "Vec"] [("A", alg [] [] [] [.num 100])] [
    .call (.resolve "Test") [.num 5]
  ]

def openedMemberDefinitionSiteCaptureRoot : Algorithm :=
  algPrivate [] [] [
    ("A", alg [] [] [] [.num 10]),
    ("Vec", openedMemberDefinitionSiteCaptureVec),
    ("Scope", openedMemberDefinitionSiteCaptureScope)
  ] [.resolve "Scope"]

def openedMemberUsesDefinitionSiteNotOpenerSite : Bool :=
  match runFlat (.algorithmExpr openedMemberDefinitionSiteCaptureRoot) with
  | Except.ok [15] => true
  | _ => false

#guard openedMemberUsesDefinitionSiteNotOpenerSite

-- Test 5: Structural property takes precedence over ordinary-dot lexical fallback
-- a.G where G(x) = x+1 is structural on receiver, no args → arity mismatch (navigation-only)
-- Even though lexical scope also defines G, structural match takes priority → error, not fallback
def lexicalG : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.num 100)]

def receiver5 : Algorithm :=
  algPrivate [] [] [("G", incAlg)] [.num 5]

def outer5 : Algorithm :=
  algPrivate [] [] [("G", lexicalG)] [
    .dotCall (.algorithmExpr receiver5) "G" none
  ]

def test5a : Bool :=
  match runResult (.algorithmExpr outer5) with
  | Except.error _ => true   -- structural G found but arity mismatch (no fallback to lexical)
  | Except.ok _ => false

#guard test5a
-- EXPECTED: Except.error (arityMismatch 1 0)
#eval runResult (.algorithmExpr outer5)

-- Test 5b: Structural property with explicit args → navigation wins over lexical
-- a.G(5) where structural G(x)=x+1 → 6 (not lexicalG which would give 500)
def test5b : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("G", lexicalG)] [
    .dotCall (.algorithmExpr receiver5) "G" (some [.num 5])
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test5b
-- EXPECTED: Except.ok [6] (structural incAlg wins, not lexicalG)
#eval runFlat (.algorithmExpr (algPrivate [] [] [("G", lexicalG)] [
    .dotCall (.algorithmExpr receiver5) "G" (some [.num 5])
  ]))

-- Test 6: Numbers.count as algorithm argument to Repeat
-- Repeat(step, Numbers.count, init) where Numbers = [10,20,30]
-- step(x) = x + 1, init = 0, count = Numbers.count = 3
-- Result: 0 → 1 → 2 → 3
open KatLang (resolve param num)

def numbersAlg : Algorithm :=
  alg [] [] [] [.num 10, .num 20, .num 30]

-- step: single-param algorithm that adds 1
def stepAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

-- Root algorithm that calls Repeat(step, Numbers.count, init)
def repeatArityRoot : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg), ("Step", stepAlg)] [
    .call (resolve "repeat") [
        resolve "Step",
        .dotCall (resolve "Numbers") "count" none,
        .num 0
      ]
  ]

def test6 : Bool :=
  match runFlat (.algorithmExpr repeatArityRoot) with
  | Except.ok [3] => true
  | _ => false

#guard test6
-- EXPECTED: Except.ok [3] (step applied 3 times: 0→1→2→3)
#eval runFlat (.algorithmExpr repeatArityRoot)

-- Test 7: Numbers.count as Repeat count (comprehensive)
-- Uses 6 output expressions to verify correct count
def numbersAlg7 : Algorithm :=
  alg [] [] [] [.num 3, .num 5, .num 9, .num 1, .num 0, .num 6]

def testAlg7 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg7)] [
    .call (resolve "repeat") [
        .algorithmExpr (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),  -- step: increment
        .dotCall (resolve "Numbers") "count" none,                      -- count: 6
        .num 0                                   -- init: 0
      ]
  ]

def test7 : Bool :=
  match runFlat (.algorithmExpr testAlg7) with
  | Except.ok [6] => true
  | _ => false

#guard test7
-- EXPECTED: Except.ok [6] (step applied 6 times: 0→1→2→3→4→5→6)
#eval runFlat (.algorithmExpr testAlg7)

-- Test 8: 0-param structural property used as Algorithm argument
-- a.X in algorithm position where X has 0 params, returns 42
def xAlg : Algorithm :=
  alg [] [] [] [.num 42]

def receiver8 : Algorithm :=
  algPrivate [] [] [("X", xAlg)] []

-- Use Atoms to force evaluation of the arg algorithm
def test8 : Bool :=
  match runFlat (.call (.resolve "atoms") [.dotCall (.algorithmExpr receiver8) "X" none]) with
  | Except.ok [42] => true
  | _ => false

#guard test8
#eval runFlat (.call (.resolve "atoms") [.dotCall (.algorithmExpr receiver8) "X" none])

-- Test 9: Structural property with params, no args → arity mismatch (navigation-only)
-- a.Inc where Inc(x) = x + 1, no args → error
def incAlg9 : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

def receiver9 : Algorithm :=
  algPrivate [] [] [("Inc", incAlg9)] [.num 5]

def test9a : Bool :=
  match runResult (.dotCall (.algorithmExpr receiver9) "Inc" none) with
  | Except.error _ => true   -- arity mismatch: Inc expects 1 arg, got 0
  | Except.ok _ => false

#guard test9a
#eval runResult (.dotCall (.algorithmExpr receiver9) "Inc" none)

-- Test 9b: Structural property with explicit args → direct binding
-- a.Inc(5) where Inc(x) = x + 1 → 6
def test9b : Bool :=
  match runFlat (.dotCall (.algorithmExpr receiver9) "Inc" (some [.num 5])) with
  | Except.ok [6] => true
  | _ => false

#guard test9b
#eval runFlat (.dotCall (.algorithmExpr receiver9) "Inc" (some [.num 5]))

-- Test 10: dotCall with args (a.X(extra)) passed as builtin argument (navigation-only)
-- Repeat(step, a.Count(bias), init)
-- a has Count(b) = 2 + b, bias = 1 → count = 3
-- step(x) = x + 10, init = 0 → 0→10→20→30
-- Note: Count takes 1 param; no receiver injection in navigation-only semantics
def countAlg : Algorithm :=
  alg ["b"] [] [] [.binary .add (.num 2) (.param "b")]

def receiver10 : Algorithm :=
  algPrivate [] [] [("Count", countAlg)] [.num 99]

def test10 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("R", receiver10)] [
    .call (resolve "repeat") [
        .algorithmExpr (alg ["x"] [] [] [.binary .add (.param "x") (.num 10)]),  -- step
        .dotCall (resolve "R") "Count" (some [.num 1]),   -- count: R.Count(1) = 3
        .num 0                                     -- init
      ]
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard test10
#eval runFlat (.algorithmExpr (algPrivate [] [] [("R", receiver10)] [
  .call (resolve "repeat") [
      .algorithmExpr (alg ["x"] [] [] [.binary .add (.param "x") (.num 10)]),
      .dotCall (resolve "R") "Count" (some [.num 1]),
      .num 0
    ]
]))

-- Test 11: dotCall none syntax for count in Repeat argument position
-- Repeat(Add, Numbers.count, 0, 0) where Numbers.count is encoded as .dotCall
-- Numbers = [3,5,9,1,0,6] → count = 6
-- Add(a,sum) = (a+1, sum + Numbers[a])
-- Result: sum of all Numbers = 3+5+9+1+0+6 = 24, extracted via index 1
def numbersAlg11 : Algorithm :=
  alg [] [] [] [.num 3, .num 5, .num 9, .num 1, .num 0, .num 6]

def addAlg11 : Algorithm :=
  alg ["a", "sum"] [] [] [
    .binary .add (.param "a") (.num 1),
    .binary .add (.param "sum") (.index (resolve "Numbers") (.param "a"))
  ]

def testAlg11 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg11), ("Add", addAlg11)] [
    .index
      (.call (resolve "repeat") [
          resolve "Add",
          .dotCall (resolve "Numbers") "count" none,     -- ← no-arg dotCall
          .num 0,
          .num 0
        ])
      (.num 1)
  ]

def test11 : Bool :=
  match runFlat (.algorithmExpr testAlg11) with
  | Except.ok [24] => true
  | _ => false

#guard test11
-- EXPECTED: Except.ok [24]
#eval runFlat (.algorithmExpr testAlg11)

-- Test 12: dotCall count as Repeat count (simple increment)
-- Same as Test 7 but with dotCall none syntax
-- Numbers has 3 outputs → count = 3, step(x) = x + 1, init = 0 → 3
def numbersAlg12 : Algorithm :=
  alg [] [] [] [.num 10, .num 20, .num 30]

def testAlg12 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg12)] [
    .call (resolve "repeat") [
        .algorithmExpr (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),  -- step
        .dotCall (resolve "Numbers") "count" none,                       -- ← no-arg dotCall
        .num 0                                   -- init
      ]
  ]

def test12 : Bool :=
  match runFlat (.algorithmExpr testAlg12) with
  | Except.ok [3] => true
  | _ => false

#guard test12
-- EXPECTED: Except.ok [3]
#eval runFlat (.algorithmExpr testAlg12)

-- Regression: recursive dot-call arguments bind both value and algorithm views,
-- but builtin argument preparation must use the current parameter value when it
-- exists. Otherwise atoms(values) re-enters list.skip(1) while list is computing.
-- `atoms` now traverses list values directly (issue #136); the explicit spread
-- (`rest = list.skip(1)*`) is kept because a sequence-shaped recursion
-- argument is what exercises the current-value binding — mirroring the C#
-- regression test.
def recursiveDotCallListAlg : Algorithm :=
  alg [] [] [] [
    .call (resolve "atoms") [.param "values"]
  ]

def recursiveDotCallRestAlg : Algorithm :=
  alg [] [] [] [
    .sequenceSpread (.dotCall (resolve "list") "skip" (some [.num 1]))
  ]

def recursiveDotCallReduceCollectionAlg : Algorithm :=
  algPrivate ["values"] [] [
    ("list", recursiveDotCallListAlg),
    ("rest", recursiveDotCallRestAlg)
  ] [
    .call (resolve "if") [
      .binary .le (.dotCall (resolve "list") "count" none) (.num 1),
      resolve "list",
      .dotCall (resolve "rest") "reduceCollection" none
    ]
  ]

def recursiveDotCallRoot : Algorithm :=
  algPrivate [] [] [("reduceCollection", recursiveDotCallReduceCollectionAlg)] [
    .call (resolve "reduceCollection") [
      .capture [.num 1, .num 2, .num 3, .num 4]
    ]
  ]

def test12a : Bool :=
  match runFlat (.algorithmExpr recursiveDotCallRoot) with
  | Except.ok [4] => true
  | _ => false

#guard test12a

-- Test 13: named multi-output receiver no longer exposes arity
def arityRemovedRoot13 : Algorithm :=
  algPrivate [] [] [("Data", alg [] [] [] [.num 1, .num 7])] [
    .dotCall (resolve "Data") "arity" none
  ]

def test13 : Bool :=
  match runResult (.algorithmExpr arityRemovedRoot13) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#guard test13
#eval runResult (.algorithmExpr arityRemovedRoot13)

-- Test 14: inline sequence-value receiver no longer exposes arity
def test14 : Bool :=
  match runResult (.dotCall (.capture [.num 1, .num 7]) "arity" none) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#guard test14
#eval runResult (.dotCall (.capture [.num 1, .num 7]) "arity" none)

-- Test 14a: extra sequence-value receiver layer no longer exposes arity
def test14a : Bool :=
  match runResult (.dotCall (.capture [.capture [.num 1, .num 7]]) "arity" none) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#guard test14a
#eval runResult (.dotCall (.capture [.capture [.num 1, .num 7]]) "arity" none)

-- Test 14b: count still works for named, inline, and nested sequence-value receivers
def countReceiverRoot14b : Algorithm :=
  algPrivate [] [] [("Data", alg [] [] [] [.num 1, .num 7])] [
    .dotCall (resolve "Data") "count" none,
    .dotCall (.capture [.num 1, .num 7]) "count" none,
    .dotCall (.capture [.capture [.num 1, .num 7]]) "count" none
  ]

def test14b : Bool :=
  match runFlat (.algorithmExpr countReceiverRoot14b) with
  | Except.ok [2, 2, 2] => true
  | _ => false

#guard test14b
#eval runFlat (.algorithmExpr countReceiverRoot14b)

-- Test 14d: old length intrinsic name is no longer recognized
def test14d : Bool :=
  match runResult (.dotCall (.capture [.num 1, .num 2]) "length" none) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test14d
#eval runResult (.dotCall (.capture [.num 1, .num 2]) "length" none)

-- Test 15: user-defined higher-order call keeps eager value ABI
-- ApplyTwice(f, x) = f(f(x)); passing Inc as an algorithm argument should work.
def incAlg15 : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

def applyTwiceAlg15 : Algorithm :=
  alg ["f", "x"] [] [] [
    .call (.param "f") [
      .call (.param "f") [.param "x"]
    ]
  ]

def test15 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("ApplyTwice", applyTwiceAlg15)] [
    .call (resolve "ApplyTwice") [resolve "Inc", .num 10]
  ])) with
  | Except.ok [12] => true
  | _ => false

#guard test15
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("ApplyTwice", applyTwiceAlg15)] [
  .call (resolve "ApplyTwice") [resolve "Inc", .num 10]
]))

-- Test 16: higher-order args preserve flat fixed expression boundaries.
-- UsePair(f, x, y) = f(x) + y; a sequence-value second argument is one argument
-- expression, while a spread of a multi-output value
-- spreads x and y explicitly as separate argument slots.
def usePairAlg16 : Algorithm :=
  alg ["f", "x", "y"] [] [] [
    .binary .add
      (.call (.param "f") [.param "x"])
      (.param "y")
  ]

def pairArg16 : Algorithm :=
  alg [] [] [] [.num 10, .num 20]

-- Source: `UsePair(Inc, Pair)` where Pair = 10, 20 — the named property's
-- sequence value is ONE argument expression.
def test16SequenceValueArgDoesNotUnpack : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("Inc", incAlg15), ("UsePair", usePairAlg16), ("Pair", pairArg16)] [
    .call (resolve "UsePair") [resolve "Inc", resolve "Pair"]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard test16SequenceValueArgDoesNotUnpack

-- Source: `UsePair(Inc, Pair*)` where Pair = 10, 20. The spread
-- `Pair*` spreads the pair's two values into the x and y argument slots:
-- Inc(10) + 20 = 31.
def test16SpreadSpreadsValues : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] []
    [("Inc", incAlg15), ("UsePair", usePairAlg16), ("Pair", pairArg16)] [
    .call (resolve "UsePair") [resolve "Inc", sequenceSpread (resolve "Pair")]
  ])) with
  | Except.ok [31] => true
  | _ => false

#guard test16SpreadSpreadsValues
#eval runFlat (.algorithmExpr (algPrivate [] []
  [("Inc", incAlg15), ("UsePair", usePairAlg16), ("Pair", pairArg16)] [
  .call (resolve "UsePair") [resolve "Inc", sequenceSpread (resolve "Pair")]
]))

-- Test 16a: ordinary dot-call fallback preserves receiver as one argument boundary.
def dotCallBoundaryAddAlg16a : Algorithm :=
  alg ["a", "b"] [] [] [
    .binary .add (.param "a") (.param "b")
  ]

def dotCallBoundaryPairReceiverAlg16a : Algorithm :=
  alg [] [] [] [.num 3, .num 7]

def dotCallBoundaryNormalCallsStillWork16a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .call (resolve "F") [.num 3, .num 7]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard dotCallBoundaryNormalCallsStillWork16a

def dotCallBoundarySequenceValueDirectCallDoesNotUnpack16a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .call (resolve "F") [.algorithmExpr dotCallBoundaryPairReceiverAlg16a]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard dotCallBoundarySequenceValueDirectCallDoesNotUnpack16a

def dotCallBoundaryScalarReceiverStillWorks16a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.num 3) "F" (some [.num 7])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard dotCallBoundaryScalarReceiverStillWorks16a

def dotCallBoundaryMultiOutputReceiverNoArgsFails16a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "F" none
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard dotCallBoundaryMultiOutputReceiverNoArgsFails16a

def dotCallBoundaryMultiOutputReceiverEmptyArgsFails16a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "F" (some [])
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard dotCallBoundaryMultiOutputReceiverEmptyArgsFails16a

def dotCallBoundaryCountedPathDoesNotSpread16a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall
      (.dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "F" none)
      "count"
      none
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard dotCallBoundaryCountedPathDoesNotSpread16a

def dotCallBoundarySequenceValueReceiverAlg16a : Algorithm :=
  alg ["x"] [] [] [.param "x"]

def dotCallBoundaryOneParamGetsSequenceValueReceiver16a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("G", dotCallBoundarySequenceValueReceiverAlg16a)] [
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "G" none
  ])) with
  | Except.ok (.sequenceValue [.atom 3, .atom 7]) => true
  | _ => false

#guard dotCallBoundaryOneParamGetsSequenceValueReceiver16a

def dotCallBoundaryFinalExplicitSequenceValueArgDoesNotUnpack16a : Bool :=
  let hAlg := alg ["a", "b", "c"] [] [] [
    .binary .add
      (.binary .add (.param "a") (.param "b"))
      (.param "c")
  ]
  match runResult (.algorithmExpr (algPrivate [] [] [("H", hAlg)] [
    .dotCall (.num 3) "H" (some [
      .capture [.num 4, .num 5]
    ])
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard dotCallBoundaryFinalExplicitSequenceValueArgDoesNotUnpack16a

def dotCallBoundarySequenceSpreadSpreadsExtraArgs16a : Bool :=
  let hAlg := alg ["a", "b", "c"] [] [] [
    .binary .add
      (.binary .add (.param "a") (.param "b"))
      (.param "c")
  ]
  match runFlat (.algorithmExpr (algPrivate [] [] [("H", hAlg)] [
    .dotCall (.num 3) "H" (some [
      sequenceSpread (.capture [.num 4, .num 5])
    ])
  ])) with
  | Except.ok [12] => true
  | _ => false

#guard dotCallBoundarySequenceSpreadSpreadsExtraArgs16a

def flatFixedIssue101PairAlg : Algorithm :=
  alg [] [] [] [.num 10, .num 20]

def flatFixedIssue101SequenceValuePairAlg : Algorithm :=
  alg [] [] [] [.algorithmExpr flatFixedIssue101PairAlg]

def flatFixedIssue101AddAlg : Algorithm :=
  alg ["x", "y"] [] [] [.binary .add (.param "x") (.param "y")]

def flatFixedIssue101UseAlg : Algorithm :=
  alg ["a", "b", "c"] [] [] [
    .binary .add
      (.binary .add (.param "a") (.param "b"))
      (.param "c")
  ]

def flatFixedIssue101PairDoesNotUnpack : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") [resolve "Pair"]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101PairDoesNotUnpack

def flatFixedIssue101AtomsDoesNotSpread : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Pair", flatFixedIssue101SequenceValuePairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") [.dotCall (resolve "Pair") "atoms" none]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101AtomsDoesNotSpread

def flatFixedIssue101SeparateArgsWork : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") [.num 10, .num 20]
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard flatFixedIssue101SeparateArgsWork

def flatFixedIssue101ExplicitIndexingWorks : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") [
      .index (resolve "Pair") (.num 0),
      .index (resolve "Pair") (.num 1)
    ]
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard flatFixedIssue101ExplicitIndexingWorks

def flatFixedIssue101MixedPrefixDoesNotUnpack : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Tail", alg [] [] [] [.num 2, .num 3]), ("Use", flatFixedIssue101UseAlg)] [
    .call (resolve "Use") [.num 1, resolve "Tail"]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101MixedPrefixDoesNotUnpack

-- Source `Use(1, Tail*)`: a plain leading argument `1` followed by `Tail*`
-- which spreads Tail's items 2, 3. Three call arguments → 1 + 2 + 3 = 6.
def flatFixedIssue101SequenceSpreadSpreadsArgs : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Tail", alg [] [] [] [.num 2, .num 3]), ("Use", flatFixedIssue101UseAlg)] [
    .call (resolve "Use") [.num 1, sequenceSpread (resolve "Tail")]
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard flatFixedIssue101SequenceSpreadSpreadsArgs

def collectingParameterForwardingCountItemAlg : Algorithm :=
  algWithParameters [
    { name := "values", kind := .collecting },
    { name := "item", kind := .normal }
  ] [] [] [
    .dotCall
      (.dotCall (.param "values") "filter" (some [
        .algorithmExpr (alg ["value"] [] [] [
          .binary .eq (.param "value") (.param "item")
        ])
      ]))
      "count"
      none
  ]

-- Forwarding a collected list into another collecting callable is explicit list
-- spread (`CountItem(values*, candidate)`): spread(collect(xs)) = xs, so the
-- callee re-collects exactly the caller's items.
def collectingParameterForwardingModeFreqsExpr : KatLang.Expr :=
  .dotCall
    (.dotCall (.param "values") "distinct" none)
    "map"
    (some [
      .algorithmExpr (alg ["candidate"] [] [] [
        .call (resolve "CountItem") [sequenceSpread (.param "values"), .param "candidate"]
      ])
    ])

def collectingParameterForwardingDirectUseAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .call (resolve "CountItem") [sequenceSpread (.param "values"), .num 1]
  ]

def collectingParameterForwardingDirectCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountItem", collectingParameterForwardingCountItemAlg),
    ("Use", collectingParameterForwardingDirectUseAlg)
  ] [
    .call (resolve "Use") [sequenceSpread (sequenceItems [.num 1, .num 1, .num 2, .num 4, .num 4])]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard collectingParameterForwardingDirectCall

def collectingParameterForwardingFreqsAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    collectingParameterForwardingModeFreqsExpr
  ]

def collectingParameterForwardingCallbackBody : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountItem", collectingParameterForwardingCountItemAlg),
    ("Mode", collectingParameterForwardingFreqsAlg)
  ] [
    .call (resolve "Mode") [sequenceSpread (sequenceItems [.num 1, .num 1, .num 2, .num 4, .num 4])]
  ])) with
  | Except.ok [2, 1, 2] => true
  | _ => false

#guard collectingParameterForwardingCallbackBody

def collectingParameterForwardingModeAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [
    privateProp "Freqs" (alg [] [] [] [collectingParameterForwardingModeFreqsExpr]),
    privateProp "MaxFreq" (alg [] [] [] [.dotCall (resolve "Freqs") "max" none])
  ] [
    .dotCall
      (.dotCall (.param "values") "distinct" none)
      "filter"
      (some [
        .algorithmExpr (alg ["candidate"] [] [] [
          .binary .eq
            (.call (resolve "CountItem") [sequenceSpread (.param "values"), .param "candidate"])
            (resolve "MaxFreq")
        ])
      ])
  ]

def collectingParameterForwardingFullMode : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountItem", collectingParameterForwardingCountItemAlg),
    ("Mode", collectingParameterForwardingModeAlg)
  ] [
    .call (resolve "Mode") [sequenceSpread (sequenceItems [.num 1, .num 1, .num 2, .num 4, .num 4])]
  ])) with
  | Except.ok [1, 4] => true
  | _ => false

#guard collectingParameterForwardingFullMode

def collectingParameterForwardingNonVariadicCollectAlg : Algorithm :=
  alg ["list"] [] [] [.dotCall (.param "list") "count" none]

def collectingParameterForwardingNonVariadicUseAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .call (resolve "Collect") [.param "values"]
  ]

-- Passing the collected list WITHOUT spread passes one list argument: `Collect(values)`
-- binds the fixed parameter to the collected list, and `list.count` opens it
-- (the ForwardAsOne shape).
def collectingParameterForwardingNonVariadicCalleeConsumesCollectedList : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Collect", collectingParameterForwardingNonVariadicCollectAlg),
    ("Use", collectingParameterForwardingNonVariadicUseAlg)
  ] [
    .call (resolve "Use") [sequenceSpread (sequenceItems [.num 10, .num 20, .num 30])]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard collectingParameterForwardingNonVariadicCalleeConsumesCollectedList

def collectingParameterForwardingCountSequenceValueAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "values", kind := .collecting }]
  ] [] [] [.dotCall (.param "values") "count" none]

def collectingParameterForwardingSequenceValueUseAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .call (resolve "CountSequenceValue") [.param "values"]
  ]

-- A deconstruction-shaped callee (`CountSequenceValue((*values))`) opens a
-- bare-forwarded collected LIST through its lone-structure rule, so the unspread
-- forward still reaches the items.
def collectingParameterForwardingSequenceValueVariadicPatternPreservesBehavior : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountSequenceValue", collectingParameterForwardingCountSequenceValueAlg),
    ("Use", collectingParameterForwardingSequenceValueUseAlg)
  ] [
    .call (resolve "Use") [sequenceSpread (sequenceItems [.num 10, .num 20, .num 30])]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard collectingParameterForwardingSequenceValueVariadicPatternPreservesBehavior

def collectingParameterForwardingSequenceValueHistoryArg : KatLang.Expr :=
  .capture [.num 1, .num 2, .num 3]

def collectingParameterForwardingFindNextAlg : Algorithm :=
  algWithParameters [
    { name := "history", kind := .collecting },
    { name := "pre1", kind := .normal },
    { name := "pre2", kind := .normal }
  ] [] [] [
    .binary .add
      (.binary .add (.dotCall (.param "history") "count" none) (.param "pre1"))
      (.param "pre2")
  ]

def collectingParameterForwardingSequenceValueStepAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "pre2", kind := .normal },
    .capture { name := "pre1", kind := .normal }
  ] [] [] [
    .call (resolve "FindNext") [sequenceSpread (.param "history"), .param "pre1", .param "pre2"]
  ]

def collectingParameterForwardingSequenceValueVariadicCaptureSpreadsCompatibleSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("FindNext", collectingParameterForwardingFindNextAlg),
    ("YSStep", collectingParameterForwardingSequenceValueStepAlg)
  ] [
    .call (resolve "YSStep") [collectingParameterForwardingSequenceValueHistoryArg, .num 2, .num 3]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard collectingParameterForwardingSequenceValueVariadicCaptureSpreadsCompatibleSlot

def collectingParameterForwardingCountItemsByOtherNameAlg : Algorithm :=
  algWithParameters [
    { name := "items", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .binary .add (.dotCall (.param "items") "count" none) (.param "last")
  ]

def collectingParameterForwardingSequenceValueHistoryUseOtherNameAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "last", kind := .normal }
  ] [] [] [
    .call (resolve "CountItems") [sequenceSpread (.param "history"), .param "last"]
  ]

-- Spread forwarding is pure value semantics: the callee's collecting parameter may use any
-- parameter name — there is no name-based or provenance-based special path.
def collectingParameterForwardingSequenceValueCaptureSpreadForwardsUnderAnyName : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountItems", collectingParameterForwardingCountItemsByOtherNameAlg),
    ("Use", collectingParameterForwardingSequenceValueHistoryUseOtherNameAlg)
  ] [
    .call (resolve "Use") [collectingParameterForwardingSequenceValueHistoryArg, .num 7]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard collectingParameterForwardingSequenceValueCaptureSpreadForwardsUnderAnyName

def collectingParameterForwardingSequenceValueHistoryNonVariadicUseAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "marker", kind := .normal }
  ] [] [] [
    .call (resolve "Collect") [.param "history"]
  ]

def collectingParameterForwardingSequenceValueCaptureForwardsSequenceValue : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Collect", collectingParameterForwardingNonVariadicCollectAlg),
    ("Use", collectingParameterForwardingSequenceValueHistoryNonVariadicUseAlg)
  ] [
    .call (resolve "Use") [collectingParameterForwardingSequenceValueHistoryArg, .num 99]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard collectingParameterForwardingSequenceValueCaptureForwardsSequenceValue

def collectingParameterForwardingTakeLastAlg : Algorithm :=
  algWithParameters [
    { name := "first", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .dotCall (.param "first") "count" none
  ]

def collectingParameterForwardingSequenceValueHistoryTakeLastUseAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "marker", kind := .normal }
  ] [] [] [
    .call (resolve "TakeLast") [.num 0, .param "history"]
  ]

def collectingParameterForwardingSequenceValueCaptureOnlyExpandsInTargetVariadicSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("TakeLast", collectingParameterForwardingTakeLastAlg),
    ("Use", collectingParameterForwardingSequenceValueHistoryTakeLastUseAlg)
  ] [
    .call (resolve "Use") [collectingParameterForwardingSequenceValueHistoryArg, .num 99]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard collectingParameterForwardingSequenceValueCaptureOnlyExpandsInTargetVariadicSlot

def collectingParameterForwardingSequenceValueLoopStepAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "pre2", kind := .normal },
    .capture { name := "pre1", kind := .normal }
  ] [] [] [
    .call (resolve "FindNext") [sequenceSpread (.param "history"), .param "pre1", .param "pre2"],
    .param "pre1",
    .param "pre2"
  ]

def collectingParameterForwardingLoopStepSequenceValueCaptureSpreadsCompatibleSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("FindNext", collectingParameterForwardingFindNextAlg),
    ("YSStep", collectingParameterForwardingSequenceValueLoopStepAlg)
  ] [
    .index
      (.dotCall (resolve "YSStep") "repeat" (some [
        .num 1, collectingParameterForwardingSequenceValueHistoryArg, .num 2, .num 3
      ]))
      (.num 0)
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard collectingParameterForwardingLoopStepSequenceValueCaptureSpreadsCompatibleSlot

def flatFixedIssue101NestedSequenceValueBoundaryPreserved : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1, .capture [.num 2, .num 3]])] [
    resolve "A"
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) => true
  | _ => false

#guard flatFixedIssue101NestedSequenceValueBoundaryPreserved

def flatFixedIssue101ExplicitOuterBodyGroupingEquivalent : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.capture [.num 1, .capture [.num 2, .num 3]]])] [
    resolve "A"
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) => true
  | _ => false

#guard flatFixedIssue101ExplicitOuterBodyGroupingEquivalent

-- Internal value shaped like sequence-value source `(1, (2, 3)*)`: a leading `1`
-- combined with a spread of the sequence value (2, 3), whose items 2 and
-- 3 are flattened by the spread.
def flatFixedIssue101SequenceSpreadFlattensNestedBlock : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.sequenceConstruct (.num 1) (sequenceSpread (.capture [.num 2, .num 3]))])] [
    resolve "A"
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard flatFixedIssue101SequenceSpreadFlattensNestedBlock

def flatFixedIssue101DotReceiverDoesNotUnpack : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .dotCall (resolve "Pair") "Add" none
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101DotReceiverDoesNotUnpack

def flatFixedIssue101SequenceSpreadDotReceiverDoesNotUnpack : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .dotCall (sequenceSpreadReceiver (resolve "Pair")) "Add" none
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101SequenceSpreadDotReceiverDoesNotUnpack

def dotCallBoundarySequenceBuiltinsStillExpand16a : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "sum" none,
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "count" none,
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "first" none,
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "last" none
  ])) with
  | Except.ok [10, 2, 3, 7] => true
  | _ => false

#guard dotCallBoundarySequenceBuiltinsStillExpand16a

-- Test 17: extra higher-order args are not silently ignored
-- TakeFunc(f) called with two algorithm args should raise arity mismatch.
def takeFuncAlg17 : Algorithm :=
  alg ["f"] [] [] [.num 0]

def test17 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("TakeFunc", takeFuncAlg17)] [
    .call (resolve "TakeFunc") [resolve "Inc", resolve "Inc"]
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test17
#eval runResult (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("TakeFunc", takeFuncAlg17)] [
  .call (resolve "TakeFunc") [resolve "Inc", resolve "Inc"]
]))

-- Test 18: structural property calls share higher-order binding semantics
-- Receiver.ApplyTwice(Inc, 10) should bind Inc through AlgEnv and return 12.
def receiver18 : Algorithm :=
  algPrivate [] [] [("ApplyTwice", applyTwiceAlg15)] []

def outer18 : Algorithm :=
  algPrivate [] [] [("Inc", incAlg15), ("Receiver", receiver18)] [
    .dotCall (resolve "Receiver") "ApplyTwice" (some [resolve "Inc", .num 10])
  ]

def test18 : Bool :=
  match runFlat (.algorithmExpr outer18) with
  | Except.ok [12] => true
  | _ => false

#guard test18
#eval runFlat (.algorithmExpr outer18)

-- Test 19: an inline algorithm block ALWAYS provides its contained Algorithm
-- on the algorithm channel, regardless of parameter/declaration/output count —
-- `{42}` is as much an Algorithm as `{a + 1}`. Reading the bound parameter as
-- a value still observes the block's value; calling it invokes the algorithm.
-- (A capture, by contrast, never crosses: see captureSuppressesCallableIdentity.)
def constSevenAlg19 : Algorithm :=
  alg [] [] [] [.num 7]

def twoValueAlg19 : Algorithm :=
  alg [] [] [] [.num 1, .num 2]

def readInlineArgAlg19 : Algorithm :=
  alg ["f"] [] [] [
    .param "f"
  ]

def callInlineArgAlg19 : Algorithm :=
  alg ["f"] [] [] [
    .call (.param "f") []
  ]

def test19 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
    .call (resolve "Apply") [.algorithmExpr constSevenAlg19]
  ])) with
  | Except.ok [7] => true
  | _ => false

#guard test19
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
  .call (resolve "Apply") [.algorithmExpr constSevenAlg19]
]))

-- `Call0({7})`: the zero-parameter inline block crosses the higher-order
-- boundary and `f()` invokes it — exactly like a named zero-parameter
-- property (`Call0(Const)`).
def test19SingleOutputBlockCrossesHigherOrderBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
    .call (resolve "Apply") [.algorithmExpr constSevenAlg19]
  ])) with
  | Except.ok [7] => true
  | _ => false

#guard test19SingleOutputBlockCrossesHigherOrderBoundary
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
  .call (resolve "Apply") [.algorithmExpr constSevenAlg19]
]))

def test19MultiOutput : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
    .call (resolve "Apply") [.algorithmExpr twoValueAlg19]
  ])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard test19MultiOutput
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
  .call (resolve "Apply") [.algorithmExpr twoValueAlg19]
]))

-- Multi-output blocks cross identically: output count never gates algorithm
-- identity, and `f()` emits the block algorithm's two outputs.
def test19MultiOutputBlockCrossesHigherOrderBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
    .call (resolve "Apply") [.algorithmExpr twoValueAlg19]
  ])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard test19MultiOutputBlockCrossesHigherOrderBoundary
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
  .call (resolve "Apply") [.algorithmExpr twoValueAlg19]
]))

-- Test 19a: same-name clause-group elaboration classifies a sole plain-binder
-- clause as an ordinary algorithm, not a conditional.
def applyClauseBody19a : Algorithm :=
  alg [] [] [] [
    .call (.param "f") [.param "x"]
  ]

def applyClauseAlg19a : Algorithm :=
  Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [KatLang.Pattern.bind "x", KatLang.Pattern.bind "f"]
    body := applyClauseBody19a
  }]

def test19aShape : Bool :=
  match applyClauseAlg19a with
  | .mk _ [.capture { name := "x", kind := .normal }, .capture { name := "f", kind := .normal }] _ _ _ => true
  | _ => false

#guard test19aShape

def test19aRun : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("Apply", applyClauseAlg19a)] [
    .call (resolve "Apply") [.num 9, resolve "Inc"]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test19aRun

def idClauseAlg19a : Algorithm :=
  Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.bind "x"
    body := alg [] [] [] [.param "x"]
  }]

def test19aSingleBinderShape : Bool :=
  match Algorithm.elaborateClauseGroup [{
      pattern := KatLang.Pattern.bind "x"
      body := alg [] [] [] [.param "x"]
    }] with
  | .mk _ [.capture { name := "x", kind := .normal }] _ _ _ => true
  | _ => false

#guard test19aSingleBinderShape

def test19aSingleBinderRun : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Id", idClauseAlg19a)] [
    .call (resolve "Id") [.num 7]
  ])) with
  | Except.ok [7] => true
  | _ => false

#guard test19aSingleBinderRun

def fallbackClauseAlg19a : Algorithm :=
  Algorithm.elaborateClauseGroup [
    {
      pattern := KatLang.Pattern.litInt 0
      body := alg [] [] [] [.num 0]
    },
    {
      pattern := KatLang.Pattern.bind "x"
      body := alg [] [] [] [.num 1]
    }
  ]

def test19aMultiClauseShape : Bool :=
  match fallbackClauseAlg19a with
  | .conditional _ _ [_, _] => true
  | _ => false

#guard test19aMultiClauseShape

def test19aMultiClauseRun : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", fallbackClauseAlg19a)] [
    .call (resolve "F") [.num 2]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test19aMultiClauseRun

def test19aLiteralPatternIsConditional : Bool :=
  match Algorithm.elaborateClauseGroup [{
      pattern := KatLang.Pattern.litInt 1
      body := alg [] [] [] [.num 42]
    }] with
  | .conditional _ _ [_] => true
  | _ => false

#guard test19aLiteralPatternIsConditional

def test19aSequenceValuePatternIsOrdinaryStructuredParameter : Bool :=
  match Algorithm.elaborateClauseGroup [{
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.bind "x",
        KatLang.Pattern.sequenceValue [KatLang.Pattern.bind "acc", KatLang.Pattern.bind "counter"]
      ]
      body := alg [] [] [] [.param "x"]
    }] with
  | .mk _ [.capture { name := "x" }, .sequenceValue [.capture { name := "acc" }, .capture { name := "counter" }]] _ _ _ => true
  | _ => false

#guard test19aSequenceValuePatternIsOrdinaryStructuredParameter

def repeatedFlatClauseAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [
      KatLang.Pattern.bind "x",
      KatLang.Pattern.bind "x"
    ]
    body := alg [] [] [] [.param "x"]
  }]

def repeatedFlatClauseEqualArgumentsMatch : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", repeatedFlatClauseAlg)] [
    .call (resolve "F") [.num 1, .num 1]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard repeatedFlatClauseEqualArgumentsMatch

def repeatedFlatClauseUnequalArgumentsFail : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", repeatedFlatClauseAlg)] [
    .call (resolve "F") [.num 1, .num 2]
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard repeatedFlatClauseUnequalArgumentsFail

def repeatedSequenceValueClauseAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [
      KatLang.Pattern.sequenceValue [
        KatLang.Pattern.bind "x",
        KatLang.Pattern.bind "x"
      ]
    ]
    body := alg [] [] [] [.param "x"]
  }]

def repeatedSequenceValueClauseMatchesOnlyEqualItems : Bool :=
  let equalCall :=
    runFlat (.algorithmExpr (algPrivate [] [] [("F", repeatedSequenceValueClauseAlg)] [
      .call (resolve "F") [
        .capture [.num 1, .num 1]
      ]
    ]))
  let unequalCall :=
    runResult (.algorithmExpr (algPrivate [] [] [("F", repeatedSequenceValueClauseAlg)] [
      .call (resolve "F") [
        .capture [.num 1, .num 2]
      ]
    ]))
  match equalCall, unequalCall with
  | Except.ok [1], Except.error err => innermostIsBadArity err
  | _, _ => false

#guard repeatedSequenceValueClauseMatchesOnlyEqualItems

def repeatedAcrossNestedClauseAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [
      KatLang.Pattern.bind "x",
      KatLang.Pattern.sequenceValue [KatLang.Pattern.bind "x"]
    ]
    body := alg [] [] [] [.param "x"]
  }]

def repeatedAcrossNestedClauseMatchesOnlyEqualItems : Bool :=
  let equalCall :=
    runFlat (.algorithmExpr (algPrivate [] [] [("F", repeatedAcrossNestedClauseAlg)] [
      .call (resolve "F") [
        .num 1,
        .capture [.num 1]
      ]
    ]))
  let unequalCall :=
    runResult (.algorithmExpr (algPrivate [] [] [("F", repeatedAcrossNestedClauseAlg)] [
      .call (resolve "F") [
        .num 1,
        .capture [.num 2]
      ]
    ]))
  match equalCall, unequalCall with
  | Except.ok [1], Except.error err => innermostIsBadArity err
  | _, _ => false

#guard repeatedAcrossNestedClauseMatchesOnlyEqualItems

def repeatedFlatClauseUsesStructuralSequenceValueEquality : Bool :=
  let sequenceValueAlg := Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [
      KatLang.Pattern.bind "x",
      KatLang.Pattern.bind "x"
    ]
    body := alg [] [] [] [.param "x"]
  }]
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2],
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard repeatedFlatClauseUsesStructuralSequenceValueEquality

def repeatedPatternProducesOneBinding : Bool :=
  match KatLang.matchPattern
      (.sequenceValue [.bind "x", .bind "x"])
      (.sequenceValue [.atom 4, .atom 4]) with
  | some bindings => bindings == [("x", .atom 4)]
  | none => false

#guard repeatedPatternProducesOneBinding

def repeatedAlgorithmOnlyArgumentsAreUnsupported : Bool :=
  let applySame := Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [
      KatLang.Pattern.bind "f",
      KatLang.Pattern.bind "f"
    ]
    body := alg [] [] [] [
      .call (.param "f") [.num 1]
    ]
  }]
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Inc", incAlg15),
    ("ApplySame", applySame)
  ] [
    .call (resolve "ApplySame") [resolve "Inc", resolve "Inc"]
  ])) with
  | Except.error err =>
      innermostIsTypeMismatch
        "Repeated bind equality is not supported for algorithm-only arguments"
        err
  | _ => false

#guard repeatedAlgorithmOnlyArgumentsAreUnsupported

def repeatedConditionalFallbackAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.bind "x",
        KatLang.Pattern.bind "x"
      ]
      body := alg [] [] [] [.num 1]
    },
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.bind "x",
        KatLang.Pattern.bind "y"
      ]
      body := alg [] [] [] [.num 0]
    }
  ]

def repeatedConditionalFallbackWorks : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Equal", repeatedConditionalFallbackAlg)] [
    .call (resolve "Equal") [.num 1, .num 1],
    .call (resolve "Equal") [.num 1, .num 2]
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard repeatedConditionalFallbackWorks

def repeatedSequenceValueConditionalFallbackWorks : Bool :=
  let samePair := Algorithm.elaborateClauseGroup [
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.sequenceValue [
          KatLang.Pattern.bind "x",
          KatLang.Pattern.bind "x"
        ]
      ]
      body := alg [] [] [] [.num 1]
    },
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.sequenceValue [
          KatLang.Pattern.bind "x",
          KatLang.Pattern.bind "y"
        ]
      ]
      body := alg [] [] [] [.num 0]
    }
  ]
  match runFlat (.algorithmExpr (algPrivate [] [] [("SamePair", samePair)] [
    .call (resolve "SamePair") [
      .capture [.num 5, .num 5]
    ],
    .call (resolve "SamePair") [
      .capture [.num 5, .num 6]
    ]
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard repeatedSequenceValueConditionalFallbackWorks

-- Repeated-bind equality must also hold on the counted callback path
-- (map/filter/reduce), not only on direct user calls. The non-counted guards
-- above exercise `mergeEqualValEnv` / `matchCallPattern`; these guards exercise
-- the counted matchers (`mergeEqualCountedParamEnv`, `matchCountedPatternInto`)
-- so both paths stay aligned with C# EvaluatorTests.Eval_Callback_Repeated*.

-- Ordinary sequenceValue repeated binder reused as a map callback: equal pair items
-- bind once and project the shared value.
def repeatedSequenceValueBinderCallbackEqualItemsMap : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Same", repeatedSequenceValueClauseAlg)] [
    .call (resolve "map") [
      sequenceItems [
        .capture [.num 1, .num 1],
        .capture [.num 2, .num 2]
      ],
      .resolve "Same"
    ]
  ])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard repeatedSequenceValueBinderCallbackEqualItemsMap

-- An unequal pair item fails the equality constraint with the same badArity
-- shape as the direct-call path.
def repeatedSequenceValueBinderCallbackUnequalItemMapFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Same", repeatedSequenceValueClauseAlg)] [
    .call (resolve "map") [
      sequenceItems [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 3]
      ],
      .resolve "Same"
    ]
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard repeatedSequenceValueBinderCallbackUnequalItemMapFails

-- Conditional sequenceValue repeated binder reused as a map callback: the equality
-- branch matches equal pairs while unequal pairs fall through to the next clause.
def repeatedSequenceValueConditionalCallbackAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.sequenceValue [
          KatLang.Pattern.bind "x",
          KatLang.Pattern.bind "x"
        ]
      ]
      body := alg [] [] [] [.num 1]
    },
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.sequenceValue [
          KatLang.Pattern.bind "x",
          KatLang.Pattern.bind "y"
        ]
      ]
      body := alg [] [] [] [.num 0]
    }
  ]

def repeatedSequenceValueConditionalCallbackFallthroughMap : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Equal", repeatedSequenceValueConditionalCallbackAlg)] [
    .call (resolve "map") [
      sequenceItems [
        .capture [.num 1, .num 1],
        .capture [.num 1, .num 2]
      ],
      .resolve "Equal"
    ]
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard repeatedSequenceValueConditionalCallbackFallthroughMap

-- A map callback whose parameter name collides with an enclosing call parameter
-- must not recurse without bound. `Wrap(x)` shares the name `x` with `Pick`'s
-- pattern variable; the bad map shape (`Pick` over scalar items) makes the
-- `Wrap` argument fail, which previously deferred it as a self-referential thunk
-- that re-entered the same map call forever (C#: process-crashing stack
-- overflow). The evaluator must instead terminate with a structured error.
-- Mirrors C# SequenceCallbackArgumentTests.CallbackArgumentInsideUserCall_FailsCleanly.
def callbackParamCollisionWrapAlg : Algorithm :=
  alg ["x"] [] [] [.param "x"]

def callbackParamCollisionPickAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x", kind := .normal }, .capture { name := "y", kind := .normal }]
  ] [] [] [.param "x"]

def callbackParamCollisionProgram : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("Wrap", callbackParamCollisionWrapAlg),
    ("Pick", callbackParamCollisionPickAlg)
  ] [
    .call (resolve "Wrap") [
      .dotCall
        (.dotCall (sequenceItems [.num 1, .num 2]) "map" (some [resolve "Pick"]))
        "sum" none
    ]
  ])

-- The key property is termination: it returns a structured error rather than
-- looping. (Before the fix the Lean model was non-terminating on this shape.)
def callbackParamCollisionFailsCleanly : Bool :=
  match runResult callbackParamCollisionProgram with
  | Except.error _ => true
  | _ => false

#guard callbackParamCollisionFailsCleanly

-- Test 19b: compatibility fallback for a manually constructed single-branch
-- flat-binder conditional still preserves higher-order args in the core AST.
def applyCondAlg19b : Algorithm :=
  .conditional none [] [
    ⟨ KatLang.Pattern.sequenceValue [KatLang.Pattern.bind "x", KatLang.Pattern.bind "f"],
      alg [] [] [] [
        .call (.param "f") [.param "x"]
      ] ⟩
  ]

def test19b : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("Apply", applyCondAlg19b)] [
    .call (resolve "Apply") [.num 9, resolve "Inc"]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test19b
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("Apply", applyCondAlg19b)] [
  .call (resolve "Apply") [.num 9, resolve "Inc"]
]))

-- Test 19c: structural property call preserves higher-order args for the same subset
def receiver19c : Algorithm :=
  algPrivate [] [] [("Apply", applyCondAlg19b)] []

def test19c : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("Receiver", receiver19c)] [
    .dotCall (resolve "Receiver") "Apply" (some [.num 9, resolve "Inc"])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test19c
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("Receiver", receiver19c)] [
  .dotCall (resolve "Receiver") "Apply" (some [.num 9, resolve "Inc"])
]))

-- Test 19d: sequenceValue eager values stay whole when a sibling argument binds only
-- through AlgEnv. The occurrence count is the kept-item count: filter materializes an
-- exact list ([(1, 2)] here) and count opens exactly that one list boundary, so one
-- kept pair counts as 1.
def evenPredicateAlg19d : Algorithm :=
  alg ["n"] [] [] [
    .binary .eq
      (.binary .mod (.index (.param "n") (.num 1)) (.num 2))
      (.num 0)
  ]

def occurrenceCountAlg19d : Algorithm :=
  alg ["values", "predicate"] [] [] [
    .dotCall
      (.call (.resolve "filter") [.param "values", .param "predicate"])
      "count"
      none
  ]

def test19d : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("OccurrenceCount", occurrenceCountAlg19d)
  ] [
    .call (.resolve "OccurrenceCount") [
      sequenceItems [
        .capture [.num 1, .num 2],
        .capture [.num 1, .num 3]
      ],
      .algorithmExpr evenPredicateAlg19d
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test19d
#eval runFlat (.algorithmExpr (algPrivate [] [] [
  ("OccurrenceCount", occurrenceCountAlg19d)
] [
  .call (.resolve "OccurrenceCount") [
    sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 1, .num 3]
    ],
    .algorithmExpr evenPredicateAlg19d
  ]
]))

-- Test 19e: inline predicate captures an outer value parameter rather than
-- re-declaring it as a local parameter.
--
-- The fixed collection argument is a grouped collection of explicit pair
-- items. One pair matches the target, so the
-- filter(...).count occurrence count is the kept-item count 1 (the kept pair
-- stays one exact list element; count opens only the list boundary).
def occurrenceCountAlg19e : Algorithm :=
  alg ["target"] [] [] [
    .dotCall
      (.call (.resolve "filter") [
        sequenceItems [
          .capture [.num 1, .num 10],
          .capture [.num 2, .num 20],
          .capture [.num 2, .num 30]
        ],
        .algorithmExpr (alg ["item"] [] [] [
          .binary .eq
            (.index (.param "item") (.num 1))
            (.index (.param "target") (.num 1))
        ])
      ])
      "count"
      none
  ]

def test19e : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("OccurrenceCount", occurrenceCountAlg19e)
  ] [
    .call (.resolve "OccurrenceCount") [
      .capture [.num 2, .num 20]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test19e
#eval runFlat (.algorithmExpr (algPrivate [] [] [
  ("OccurrenceCount", occurrenceCountAlg19e)
] [
  .call (.resolve "OccurrenceCount") [
    .capture [.num 2, .num 20]
  ]
]))

-- if builtin tests
-- if(cond, whenTrue, whenFalse): the only supported form.
--------------------------------------------------------------------------------

-- Test 20: 3-arg if true → produce then-branch value
-- if(1, 5, 6) → [5]
def test20 : Bool :=
  match runFlat (.call (resolve "if") [.num 1, .num 5, .num 6]) with
  | Except.ok [5] => true
  | _ => false

#guard test20
#eval runFlat (.call (resolve "if") [.num 1, .num 5, .num 6])

-- Test 21: 3-arg if false → produce else-branch value
-- if(0, 5, 6) → [6]
def test21 : Bool :=
  match runFlat (.call (resolve "if") [.num 0, .num 5, .num 6]) with
  | Except.ok [6] => true
  | _ => false

#guard test21
#eval runFlat (.call (resolve "if") [.num 0, .num 5, .num 6])

--------------------------------------------------------------------------------
-- Conditional algorithm tests
--------------------------------------------------------------------------------

open KatLang (Pattern CondBranch)

-- Test 22: K combinator via conditional algorithm
-- K(a, b) = a  →  K(10, 20) => 10
def kAlg : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.bind "a", .bind "b"],
      alg [] [] [] [.param "a"] ⟩
  ]

def test34 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", kAlg)] [
    .call (resolve "K") [.num 10, .num 20]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test34
#eval runFlat (.algorithmExpr (algPrivate [] [] [("K", kAlg)] [
  .call (resolve "K") [.num 10, .num 20]
]))

-- Test 35: Multiple branches with literal match
-- Else(1, (a, b)) = a
-- Else(c, (a, b)) = b
def elseAlg : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.litInt 1, .sequenceValue [.bind "a", .bind "b"]],
      alg [] [] [] [.param "a"] ⟩,
    ⟨ .sequenceValue [.bind "c", .sequenceValue [.bind "a", .bind "b"]],
      alg [] [] [] [.param "b"] ⟩
  ]

-- Else(1, (2, 3)) → first branch matches → a = 2
def test35a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Else", elseAlg)] [
    .call (resolve "Else") [.num 1, .capture [.num 2, .num 3]]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test35a

-- Else(0, (2, 3)) → second branch matches → b = 3
def test35b : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Else", elseAlg)] [
    .call (resolve "Else") [.num 0, .capture [.num 2, .num 3]]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test35b

-- Test 36: Non-exhaustive — no match → error
-- Sign(1) = 1; Sign(-1) = -1;  Sign(0) → noMatchingBranch
def signAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 1,  alg [] [] [] [.num 1] ⟩,
    ⟨ .litInt (-1), alg [] [] [] [.num (-1)] ⟩
  ]

def test36 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Sign", signAlg)] [
    .call (resolve "Sign") [.num 0]
  ])) with
  | Except.error _ => true    -- noMatchingBranch
  | Except.ok _    => false

#guard test36

-- Test 37: First-match-wins
-- F(x) = 1  (catch-all, always matches)
-- F(1) = 2  (never reached)
-- F(1) → 1
def firstMatchAlg : Algorithm :=
  .conditional none [] [
    ⟨ .bind "x", alg [] [] [] [.num 1] ⟩,
    ⟨ .litInt 1,  alg [] [] [] [.num 2] ⟩
  ]

def test37 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", firstMatchAlg)] [
    .call (resolve "F") [.num 1]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test37

-- Test 22: 2-arg if is rejected
def test22 : Bool :=
  match runResult (.call (resolve "if") [.num 1, .num 5]) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test22
#eval runResult (.call (resolve "if") [.num 1, .num 5])

-- Test 23: 2-arg if in addition is rejected
def test23 : Bool :=
  match runResult (.binary .add (.num 10) (.call (resolve "if") [.num 1, .num 5])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test23
#eval runResult (.binary .add (.num 10) (.call (resolve "if") [.num 1, .num 5]))

-- Test 24: 2-arg if in multiplication is rejected
def test24 : Bool :=
  match runResult (.binary .mul (.num 10) (.call (resolve "if") [
    .binary .lt (.num 7) (.num 6),
    .num 1
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test24
#eval runResult (.binary .mul (.num 10) (.call (resolve "if") [
  .binary .lt (.num 7) (.num 6),
  .num 1
]))

-- The `if` arity payload is NORMATIVE: `if` requires exactly three arguments,
-- so every reachable `if` arity failure carries expected = 3 (never the
-- generic-builtin placeholder 0) with actual = the assembled argument count.
-- Dot-call reproducers (`A = 1` / `A.if(2)`): the receiver is one leading
-- argument, so the assembled arities are 2 and 4. C# twin:
-- IfBuiltinArityPayloadTests (`WrongBuiltinArity` populates expected 3 for
-- `if` alone; other builtins keep the placeholder on both sides).
def ifDotCallUnderArityProgram : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1])] [
    .dotCall (resolve "A") "if" (some [.num 2])
  ])

def ifDotCallUnderArityCarriesExpectedThree : Bool :=
  match runResult ifDotCallUnderArityProgram with
  | Except.error err =>
      hasContext "while evaluating dotCall .if of A" err
        && hasContext "expected 3 arguments" err
        && innermostIsArityMismatch 3 2 err
  | Except.ok _ => false

#guard ifDotCallUnderArityCarriesExpectedThree
#eval runResult ifDotCallUnderArityProgram

def ifDotCallOverArityProgram : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1])] [
    .dotCall (resolve "A") "if" (some [.num 2, .num 3, .num 4])
  ])

def ifDotCallOverArityCarriesExpectedThree : Bool :=
  match runResult ifDotCallOverArityProgram with
  | Except.error err =>
      hasContext "while evaluating dotCall .if of A" err
        && hasContext "expected 3 arguments" err
        && innermostIsArityMismatch 3 4 err
  | Except.ok _ => false

#guard ifDotCallOverArityCarriesExpectedThree
#eval runResult ifDotCallOverArityProgram

-- Exactly three assembled arguments through the same dot-call surface still
-- dispatch: `A.if(20, 30)` is `if(A, 20, 30)` = `if(1, 20, 30)` → 20.
def ifDotCallExactArityStillDispatches : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1])] [
    .dotCall (resolve "A") "if" (some [.num 20, .num 30])
  ])) with
  | Except.ok [20] => true
  | _ => false

#guard ifDotCallExactArityStillDispatches

-- Test 25: Spread of an internal constructed sequence `(1, if(0, 2, 9), 3)*` with a
-- 3-arg if that selects the else branch → [1, 9, 3]
def test25 : Bool :=
  match runFlat (sequenceSpread (.sequenceConstruct (.sequenceConstruct (.num 1) (.call (resolve "if") [.num 0, .num 2, .num 9])) (.num 3))) with
  | Except.ok [1, 9, 3] => true
  | _ => false

#guard test25
#eval runFlat (sequenceSpread (.sequenceConstruct (.sequenceConstruct (.num 1) (.call (resolve "if") [.num 0, .num 2, .num 9])) (.num 3)))

-- Internal sequence `(1, 2, 3, 4)*`: spread over the constructed sequence value.
def sequenceSpread1234 : KatLang.Expr :=
  sequenceSpread (.sequenceConstruct (.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3)) (.num 4))

def test25a : Bool :=
  let sequence1234 := .sequenceConstruct (.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3)) (.num 4)
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [sequence1234],
    .call (resolve "count") [sequence1234],
    .call (resolve "first") [sequence1234],
    .call (resolve "last") [sequence1234]
  ])) with
  | Except.ok [10, 4, 1, 4] => true
  | _ => false

#guard test25a

def test25b : Bool :=
  -- Internal constructed-sequence variants of `count(((1, 2)*, 3))` and
  -- `count((1, (2, 3)*))`: a flattening spread contributes inside the one
  -- sequence-valued argument.
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [
      sequenceItems [sequenceSpread (.capture [.num 1, .num 2]), .num 3]
    ],
    .call (resolve "count") [
      sequenceItems [.num 1, sequenceSpread (.capture [.num 2, .num 3])]
    ]
  ])) with
  | Except.ok [3, 3] => true
  | _ => false

#guard test25b

def test25bNestedSequenceValues : Bool :=
  let nestedLeft := .sequenceConstruct (sequenceSpread (.capture [.capture [.num 1, .num 2]])) (.num 3)
  let nestedMiddle := .sequenceConstruct (sequenceSpread (.capture [.num 1, .capture [.num 2, .num 3]])) (.num 4)
  match runResult (.algorithmExpr (alg [] [] [] [nestedLeft, nestedMiddle])) with
  | Except.ok value =>
      value == Result.sequenceValue [
        Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3],
        Result.sequenceValue [Result.atom 1, Result.sequenceValue [Result.atom 2, Result.atom 3], Result.atom 4]
      ]
  | _ => false

#guard test25bNestedSequenceValues

def sequenceSpreadNamedSequenceValueOperandPreservesBoundary : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.capture [.num 1, .num 2]])
  ] [
    .sequenceConstruct (sequenceSpread (resolve "A")) (.num 3)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]) => true
  | _ => false

#guard sequenceSpreadNamedSequenceValueOperandPreservesBoundary

def test25bCommaSimilarity : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("B", alg [] [] [] [sequenceSpread (.sequenceConstruct (.num 1) (.num 2))])
  ] [
    .dotCall (resolve "A") "count" none,
    .dotCall (resolve "B") "count" none
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test25bCommaSimilarity

def test25c : Bool :=
  -- Internal sequence `(P*, 3, 4, 5)` where P = 1, 2 is ONE collection argument,
  -- opened by the post-binding one-level collection view; sum 15.
  let pThenMore := sequenceItems [sequenceSpread (resolve "P"), .num 3, .num 4, .num 5]
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("P", alg [] [] [] [.num 1, .num 2]),
    ("X", alg [] [] [] [.call (resolve "sum") [pThenMore]])
  ] [
    resolve "X"
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test25c

def test25dResultShape : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("F", alg ["a"] [] [] [.param "a", .num 3])
  ] [
    .dotCall (resolve "A") "F" none
  ])) with
  | Except.ok value =>
      value == Result.sequenceValue [Result.sequenceValue [Result.atom 1, Result.atom 2], Result.atom 3]
  | _ => false

#guard test25dResultShape

def test25e : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("F", alg ["a"] [] [] [.sequenceConstruct (sequenceSpread (.param "a")) (.num 3)])
  ] [
    .dotCall (resolve "A") "F" none
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test25e

def test25f : Bool :=
  let a := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] [.num 10]
  let b := alg [] [] [publicProp "Y" (alg [] [] [] [.num 2])] [.num 20]
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", a),
    ("B", b),
    ("C", alg [] [] [] [.sequenceConstruct (sequenceSpread (resolve "A")) (sequenceSpread (resolve "B"))])
  ] [
    resolve "C"
  ])) with
  | Except.ok [10, 20] => true
  | _ => false

#guard test25f

def test25g : Bool :=
  let a := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] [.num 10]
  let b := alg [] [] [publicProp "Y" (alg [] [] [] [.num 2])] [.num 20]
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", a),
    ("B", b),
    ("C", alg [] [] [] [.sequenceConstruct (sequenceSpread (resolve "A")) (sequenceSpread (resolve "B"))])
  ] [
    .dotCall (resolve "C") "X" none
  ])) with
  | Except.error err => innermostIsUnknownName "X" err
  | _ => false

#guard test25g

-- A spread of a no-output operand fails with the spread
-- missing-output diagnostic: source `bad*` is `sequenceSpread bad`, whose
-- single operand produces no output. The direct `.algorithmExpr` operand reports
-- the spread-specific error, exactly like a resolved operand (T4-2).
def test25h : Bool :=
  let bad := .algorithmExpr (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])
  match runFlat (sequenceSpread bad) with
  | Except.error err => innermostIsSpreadMissingOutput err
  | _ => false

#guard test25h

-- A spread is not a valid open target. Source `open A*`
-- is the spread node `sequenceSpread (resolve "A")`, rendered `A*`.
def test25j : Bool :=
  let a := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] []
  let b := alg [] [] [publicProp "Y" (alg [] [] [] [.num 2])] []
  match runFlat (.algorithmExpr (algPrivate [] [sequenceSpread (resolve "A")] [
    ("A", a),
    ("B", b)
  ] [
    .binary .add (resolve "X") (resolve "Y")
  ])) with
  | Except.error err => innermostIsBadOpenForm "spread: A*" err
  | _ => false

#guard test25j

-- Test 26: Nested 3-arg if uses the selected inner branch
-- if(1, if(1, 5, 6), 9) → [5]
def test26 : Bool :=
  match runFlat (.call (resolve "if") [
    .num 1,
    .call (resolve "if") [.num 1, .num 5, .num 6],
    .num 9
  ]) with
  | Except.ok [5] => true
  | _ => false

#guard test26

-- Test 27: Nested 3-arg if uses the outer else branch
-- if(0, if(1, 5, 6), 9) → [9]
def test27 : Bool :=
  match runFlat (.call (resolve "if") [
    .num 0,
    .call (resolve "if") [.num 1, .num 5, .num 6],
    .num 9
  ]) with
  | Except.ok [9] => true
  | _ => false

#guard test27

-- Test 28: 3-arg if still works — if(1, 10, 20) → [10]
def test28 : Bool :=
  match runFlat (.call (resolve "if") [.num 1, .num 10, .num 20]) with
  | Except.ok [10] => true
  | _ => false

#guard test28

-- Test 29: 3-arg if false → if(0, 10, 20) → [20]
def test29 : Bool :=
  match runFlat (.call (resolve "if") [.num 0, .num 10, .num 20]) with
  | Except.ok [20] => true
  | _ => false

#guard test29

-- Test 30: 3-arg if with non-zero condition → true
-- if(42, 7, 9) → [7]
def test30 : Bool :=
  match runFlat (.call (resolve "if") [.num 42, .num 7, .num 9]) with
  | Except.ok [7] => true
  | _ => false

#guard test30

-- Test 31: 3-arg if with negative condition → true
-- if(-1, 7, 9) → [7]
def test31 : Bool :=
  match runFlat (.call (resolve "if") [.num (-1), .num 7, .num 9]) with
  | Except.ok [7] => true
  | _ => false

#guard test31

--------------------------------------------------------------------------------
-- string intrinsic tests
--------------------------------------------------------------------------------

-- Test 52: string intrinsic on positive integer via algorithm
-- (block [123]).string → Result.str "123"
def test52 : Bool :=
  match runResult (.dotCall (.algorithmExpr (alg [] [] [] [.num 123])) "string" none) with
  | Except.ok (Result.str "123") => true
  | _ => false

#guard test52
#eval runResult (.dotCall (.algorithmExpr (alg [] [] [] [.num 123])) "string" none)

-- Test 53: string intrinsic on zero
-- (block [0]).string → Result.str "0"
def test53 : Bool :=
  match runResult (.dotCall (.algorithmExpr (alg [] [] [] [.num 0])) "string" none) with
  | Except.ok (Result.str "0") => true
  | _ => false

#guard test53

-- Test 54: string intrinsic on negative integer
-- (block [-5]).string → Result.str "-5"
def test54 : Bool :=
  match runResult (.dotCall (.algorithmExpr (alg [] [] [] [.num (-5)])) "string" none) with
  | Except.ok (Result.str "-5") => true
  | _ => false

#guard test54

-- Test 55: string intrinsic on a named property
-- A = 123; A.string → Result.str "123"
def test55 : Bool :=
  let innerAlg := algPrivate [] [] [("A", alg [] [] [] [.num 123])] [
    .dotCall (.resolve "A") "string" none
  ]
  match runResult (.algorithmExpr innerAlg) with
  | Except.ok (Result.str "123") => true
  | _ => false

#guard test55

-- Test 56: string intrinsic on numeric literal (notAnAlgorithm path)
-- (.num 42).string → Result.str "42"
def test56 : Bool :=
  match runResult (.dotCall (.num 42) "string" none) with
  | Except.ok (Result.str "42") => true
  | _ => false

#guard test56

-- Test 57: string intrinsic on string literal → typeMismatch error
-- ("hello").string → Error.typeMismatch
def test57 : Bool :=
  match runResult (.dotCall (.stringLiteral "hello") "string" none) with
  | Except.error _ => true
  | _ => false

#guard test57

-- Test 58: string intrinsic on multi-output → typeMismatch error
-- (1, 2).string -> Error (sequence value is not a numeric atom)
def test58 : Bool :=
  match runResult (.dotCall (.capture [.num 1, .num 2]) "string" none) with
  | Except.error _ => true
  | _ => false

#guard test58

--------------------------------------------------------------------------------
-- range builtin tests
--------------------------------------------------------------------------------

-- Test 59: ascending inclusive range
def test59 : Bool :=
  match runFlat (.call (resolve "range") [.num 1, .num 10]) with
  | Except.ok [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] => true
  | _ => false

#guard test59

-- Test 60: descending inclusive range
def test60 : Bool :=
  match runFlat (.call (resolve "range") [.num 10, .num 1]) with
  | Except.ok [10, 9, 8, 7, 6, 5, 4, 3, 2, 1] => true
  | _ => false

#guard test60

-- Test 61: equal bounds produce a singleton
def test61 : Bool :=
  match runFlat (.call (resolve "range") [.num 5, .num 5]) with
  | Except.ok [5] => true
  | _ => false

#guard test61

-- Test 62: negative to positive bounds remain inclusive and ordered
def test62 : Bool :=
  match runFlat (.call (resolve "range") [.num (-2), .num 2]) with
  | Except.ok [-2, -1, 0, 1, 2] => true
  | _ => false

#guard test62

-- Test 32: Unary / binary composition with 2-arg if is rejected
def test32 : Bool :=
  match runResult (.binary .add (.num 10) (.unary .minus (.call (resolve "if") [.num 0, .num 5]))) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test32

-- Test 33: if arity mismatch — 1 arg → error
def test33 : Bool :=
  match runResult (.call (resolve "if") [.num 1]) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test33

--------------------------------------------------------------------------------
-- spread builtin-argument evaluation ORDER tests
-- `expandSequenceSpreadBuiltinArguments`: SPREAD-MARKED argument slots are forced
-- exactly once, in left-to-right written order, and expanding a spread slot is
-- part of evaluating that slot. Non-spread slots keep their written position but
-- remain builtin-lazy algorithms at this stage — the builtin decides whether and
-- when to evaluate them (an unselected `if` branch never runs). The helper
-- formerly recursed into the remaining slots BEFORE evaluating the current spread
-- slot, so two failing spread arguments reported the RIGHTMOST failure while C#
-- reported the leftmost. C# parity:
-- tests/KatLang.Tests/SpreadArgumentEvaluationOrderTests.cs and the generated
-- LanguageSpecCases guards `spread-arguments-fail-left-to-right` /
-- `spread-arguments-keep-written-order`.
--------------------------------------------------------------------------------

-- Two spread slots failing with DIFFERENT errors: the reported error identifies
-- which slot was evaluated first, so each shape is pinned in both spellings.
def spreadBuiltinArgumentFailingProps : List (Prod String Algorithm) :=
  [("P", alg [] [] [] [.binary .div (.num 1) (.num 0)]),
   ("Q", alg [] [] [] [.binary .add (.stringLiteral "x") (.num 1)])]

def spreadBuiltinArgumentProgram (callee : String) (args : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] spreadBuiltinArgumentFailingProps [
    .call (resolve callee) args
  ])

def spreadP : KatLang.Expr := sequenceSpread (resolve "P")
def spreadQ : KatLang.Expr := sequenceSpread (resolve "Q")

-- range(P*, Q*) → the leftmost slot's division by zero.
def spreadBuiltinArgumentsRangeFailLeftToRight : Bool :=
  match runResult (spreadBuiltinArgumentProgram "range" [spreadP, spreadQ]) with
  | Except.error err => innermostIsDivByZero err
  | _ => false

#guard spreadBuiltinArgumentsRangeFailLeftToRight

-- range(Q*, P*) → the mirrored spelling reports the type mismatch instead, so this
-- is an ORDER rule, not an error-precedence rule.
def spreadBuiltinArgumentsRangeMirroredFailsFirstSlot : Bool :=
  match runResult (spreadBuiltinArgumentProgram "range" [spreadQ, spreadP]) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard spreadBuiltinArgumentsRangeMirroredFailsFirstSlot

-- if(P*, Q*, 0) / if(Q*, P*, 0) — expansion runs before `if` selects a branch.
def spreadBuiltinArgumentsIfFailLeftToRight : Bool :=
  match runResult (spreadBuiltinArgumentProgram "if" [spreadP, spreadQ, .num 0]) with
  | Except.error err => innermostIsDivByZero err
  | _ => false

#guard spreadBuiltinArgumentsIfFailLeftToRight

def spreadBuiltinArgumentsIfMirroredFailsFirstSlot : Bool :=
  match runResult (spreadBuiltinArgumentProgram "if" [spreadQ, spreadP, .num 0]) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard spreadBuiltinArgumentsIfMirroredFailsFirstSlot

-- repeat(P*, Q*, 1) / repeat(Q*, P*, 1) — expansion runs before the loop's own
-- step/count/state binding.
def spreadBuiltinArgumentsRepeatFailLeftToRight : Bool :=
  match runResult (spreadBuiltinArgumentProgram "repeat" [spreadP, spreadQ, .num 1]) with
  | Except.error err => innermostIsDivByZero err
  | _ => false

#guard spreadBuiltinArgumentsRepeatFailLeftToRight

def spreadBuiltinArgumentsRepeatMirroredFailsFirstSlot : Bool :=
  match runResult (spreadBuiltinArgumentProgram "repeat" [spreadQ, spreadP, .num 1]) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard spreadBuiltinArgumentsRepeatMirroredFailsFirstSlot

-- Correcting the evaluation ORDER must not reorder the expanded argument VALUES:
-- each slot still contributes its items in place.
def spreadBuiltinArgumentBoundsProps : List (Prod String Algorithm) :=
  [("Lo", alg [] [] [] [.num 2]), ("Hi", alg [] [] [] [.num 4])]

def spreadBuiltinArgumentsKeepWrittenOrder : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] spreadBuiltinArgumentBoundsProps [
    .call (resolve "range") [sequenceSpread (resolve "Lo"), sequenceSpread (resolve "Hi")]
  ])) with
  | Except.ok [2, 3, 4] => true
  | _ => false

#guard spreadBuiltinArgumentsKeepWrittenOrder

def spreadBuiltinArgumentsMirroredOrderSwapsArguments : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] spreadBuiltinArgumentBoundsProps [
    .call (resolve "range") [sequenceSpread (resolve "Hi"), sequenceSpread (resolve "Lo")]
  ])) with
  | Except.ok [4, 3, 2] => true
  | _ => false

#guard spreadBuiltinArgumentsMirroredOrderSwapsArguments

-- One spread slot supplying BOTH arguments keeps its items in order too.
def spreadBuiltinArgumentsSingleSlotKeepsItemOrder : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Bounds", alg [] [] [] [.num 2, .num 4])] [
    .call (resolve "range") [sequenceSpread (resolve "Bounds")]
  ])) with
  | Except.ok [2, 3, 4] => true
  | _ => false

#guard spreadBuiltinArgumentsSingleSlotKeepsItemOrder

--------------------------------------------------------------------------------
-- String literal tests (first-class string values)
--------------------------------------------------------------------------------

-- Test 38: String literal evaluates to Result.str
def test38 : Bool :=
  match runResult (.stringLiteral "hello") with
  | Except.ok (.str "hello") => true
  | _ => false

#guard test38

-- Test 39: String equality — same values
def test39 : Bool :=
  match runFlat (.binary .eq (.stringLiteral "a") (.stringLiteral "a")) with
  | Except.ok [1] => true
  | _ => false

#guard test39

-- Test 40: String equality — different values
def test40 : Bool :=
  match runFlat (.binary .eq (.stringLiteral "a") (.stringLiteral "b")) with
  | Except.ok [0] => true
  | _ => false

#guard test40

-- Test 41: String inequality
def test41 : Bool :=
  match runFlat (.binary .ne (.stringLiteral "a") (.stringLiteral "b")) with
  | Except.ok [1] => true
  | _ => false

#guard test41

-- Test 42: String equality is case-sensitive
def test42 : Bool :=
  match runFlat (.binary .eq (.stringLiteral "Apples") (.stringLiteral "apples")) with
  | Except.ok [0] => true
  | _ => false

#guard test42

-- Test 43: Unsupported binary operation on strings → typeMismatch
def test43 : Bool :=
  match runResult (.binary .add (.stringLiteral "a") (.stringLiteral "b")) with
  | Except.error (Error.typeMismatch _) => true
  | _ => false

#guard test43

-- Test 44: Mixed string/number in binary → typeMismatch
def test44 : Bool :=
  match runResult (.binary .add (.num 1) (.stringLiteral "a")) with
  | Except.error (Error.typeMismatch _) => true
  | _ => false

#guard test44

-- Test 45: Unary minus on string → typeMismatch
def test45 : Bool :=
  match runResult (.unary .minus (.stringLiteral "hello")) with
  | Except.error (Error.typeMismatch _) => true
  | _ => false

#guard test45

def numericScalarModLeftSequenceValueMessage : String :=
  "operator `mod` expects numeric scalar operands, but the left operand was a sequence value with 4 sequence elements: (3, 4, 5, 6)"

def numericScalarModRightSequenceValueMessage : String :=
  "operator `mod` expects numeric scalar operands, but the right operand was a sequence value with 4 sequence elements: (3, 4, 5, 6)"

-- Test 45a: sequenceValue left operand in a numeric operator reports scalar shape
def test45a : Bool :=
  match runResult (.binary .mod
    (.capture [.num 3, .num 4, .num 5, .num 6])
    (.num 2)) with
  | Except.error err =>
      hasContext "while evaluating `(3, 4, 5, 6) mod 2`" err &&
      innermostIsTypeMismatch numericScalarModLeftSequenceValueMessage err
  | _ => false

#guard test45a

-- Test 45b: sequenceValue right operand in a numeric operator reports scalar shape
def test45b : Bool :=
  match runResult (.binary .mod
    (.num 2)
    (.capture [.num 3, .num 4, .num 5, .num 6])) with
  | Except.error err =>
      hasContext "while evaluating `2 mod (3, 4, 5, 6)`" err &&
      innermostIsTypeMismatch numericScalarModRightSequenceValueMessage err
  | _ => false

#guard test45b

-- Structural value equality for `==` / `!=` ----------------------------------
-- `==` and `!=` compare KatLang values structurally across all value kinds:
-- numbers by value, strings by exact value, and sequence values by length plus
-- recursive pairwise equality. Different value kinds compare unequal rather than
-- raising a type mismatch. Arithmetic and ordering keep the numeric-scalar path
-- (Test 45a/45b above already cover sequence-operand rejection for `mod`).

-- Helper: a written sequence-value group in operand position,
-- e.g. `seqVal [1, 2]` stands in for `(1, 2)`.
def seqVal (xs : List Int) : KatLang.Expr :=
  .capture (xs.map (fun n => KatLang.Expr.num n))

-- Test 45c: structurally identical sequence values compare equal.
def sequenceValueEqualitySameElements : Bool :=
  match runFlat (.binary .eq (seqVal [1, 2]) (seqVal [1, 2])) with
  | Except.ok [1] => true
  | _ => false

#guard sequenceValueEqualitySameElements

-- Test 45d: sequence values differing in an element compare unequal.
def sequenceValueEqualityDifferentElement : Bool :=
  match runFlat (.binary .eq (seqVal [1, 2]) (seqVal [1, 3])) with
  | Except.ok [0] => true
  | _ => false

#guard sequenceValueEqualityDifferentElement

-- Test 45e: sequence values of different lengths compare unequal.
def sequenceValueEqualityDifferentLength : Bool :=
  match runFlat (.binary .eq (seqVal [1, 2]) (seqVal [1, 2, 3])) with
  | Except.ok [0] => true
  | _ => false

#guard sequenceValueEqualityDifferentLength

-- Test 45f: nested sequence values compare recursively (equal).
def nestedSequenceValueEqualityEqual : Bool :=
  let left  := .capture [.num 1, seqVal [2, 3]]
  let right := .capture [.num 1, seqVal [2, 3]]
  match runFlat (.binary .eq left right) with
  | Except.ok [1] => true
  | _ => false

#guard nestedSequenceValueEqualityEqual

-- Test 45g: nested sequence values compare recursively (unequal inner element).
def nestedSequenceValueEqualityDifferentInner : Bool :=
  let left  := .capture [.num 1, seqVal [2, 3]]
  let right := .capture [.num 1, seqVal [2, 4]]
  match runFlat (.binary .eq left right) with
  | Except.ok [0] => true
  | _ => false

#guard nestedSequenceValueEqualityDifferentInner

-- Test 45h: equality between different value kinds returns 0, never a type error.
def numberVsSequenceValueEqualityDifferentKinds : Bool :=
  match runFlat (.binary .eq (.num 1) (seqVal [1, 2])) with
  | Except.ok [0] => true
  | _ => false

#guard numberVsSequenceValueEqualityDifferentKinds

-- Test 45i: inequality is the negation of structural equality across kinds.
def numberVsSequenceValueInequalityDifferentKinds : Bool :=
  match runFlat (.binary .ne (.num 1) (seqVal [1, 2])) with
  | Except.ok [1] => true
  | _ => false

#guard numberVsSequenceValueInequalityDifferentKinds

-- Test 45j: `!=` negates structural equality for equal sequence values.
def sequenceValueInequalitySameElements : Bool :=
  match runFlat (.binary .ne (seqVal [1, 2]) (seqVal [1, 2])) with
  | Except.ok [0] => true
  | _ => false

#guard sequenceValueInequalitySameElements

-- Test 45k: mixed number/string equality returns 0 (different kinds, not a type
-- mismatch). Contrast with Test 44, where `+` on number/string still type-errors.
def mixedNumberStringEqualityDifferentKinds : Bool :=
  match runFlat (.binary .eq (.num 1) (.stringLiteral "a")) with
  | Except.ok [0] => true
  | _ => false

#guard mixedNumberStringEqualityDifferentKinds

def mixedNumberStringInequalityDifferentKinds : Bool :=
  match runFlat (.binary .ne (.num 1) (.stringLiteral "a")) with
  | Except.ok [1] => true
  | _ => false

#guard mixedNumberStringInequalityDifferentKinds

-- Test 45l: ordering operators still reject sequence-value operands.
def numericScalarLtLeftSequenceValueMessage : String :=
  "operator `<` expects numeric scalar operands, but the left operand was a sequence value with 2 sequence elements: (1, 2)"

def orderingSequenceValueOperandStillRejected : Bool :=
  match runResult (.binary .lt (seqVal [1, 2]) (seqVal [1, 2])) with
  | Except.error err =>
      hasContext "while evaluating `(1, 2) < (1, 2)`" err &&
      innermostIsTypeMismatch numericScalarLtLeftSequenceValueMessage err
  | _ => false

#guard orderingSequenceValueOperandStillRejected

-- Test 45m: arithmetic operators still reject sequence-value operands.
def numericScalarAddLeftSequenceValueMessage : String :=
  "operator `+` expects numeric scalar operands, but the left operand was a sequence value with 2 sequence elements: (1, 2)"

def arithmeticSequenceValueOperandStillRejected : Bool :=
  match runResult (.binary .add (seqVal [1, 2]) (seqVal [1, 2])) with
  | Except.error err =>
      hasContext "while evaluating `(1, 2) + (1, 2)`" err &&
      innermostIsTypeMismatch numericScalarAddLeftSequenceValueMessage err
  | _ => false

#guard arithmeticSequenceValueOperandStillRejected

-- Test 45n: structural equality preserves nesting; it must not flatten sequence
-- values. `(1, (2, 3))` has shape [1, [2, 3]] and `((1, 2), 3)` has shape
-- [[1, 2], 3]; they flatten to the same atoms but are structurally unequal.
def nestedSequenceValueEqualityDoesNotFlatten : Bool :=
  let left  := .capture [.num 1, seqVal [2, 3]]
  let right := .capture [seqVal [1, 2], .num 3]
  match runFlat (.binary .eq left right) with
  | Except.ok [0] => true
  | _ => false

#guard nestedSequenceValueEqualityDoesNotFlatten

-- Test 45o: sequence equality is ordered pairwise equality, not set equality.
def sequenceValueEqualityIsOrderSensitive : Bool :=
  match runFlat (.binary .eq (seqVal [1, 2]) (seqVal [2, 1])) with
  | Except.ok [0] => true
  | _ => false

#guard sequenceValueEqualityIsOrderSensitive

-- Test 45p: empty sequence equality is stable across independently bound properties.
-- A = (); B = (); A == B → 1.
def emptyPropertyToPropertyEquality : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
      ("A", alg [] [] [] [.emptySequence 0]),
      ("B", alg [] [] [] [.emptySequence 0])
    ] [
      .binary .eq (.resolve "A") (.resolve "B")
    ])) with
  | Except.ok [1] => true
  | _ => false

#guard emptyPropertyToPropertyEquality

-- Test 46: Conditional algorithm with string literal pattern
-- Price('apples') = 0.80  (using Int for simplicity: 80)
def priceAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litString "apples",  alg [] [] [] [.num 80] ⟩,
    ⟨ .litString "tomatoes", alg [] [] [] [.num 120] ⟩
  ]

def test46 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Price", priceAlg)] [
    .call (resolve "Price") [.stringLiteral "apples"]
  ])) with
  | Except.ok [80] => true
  | _ => false

#guard test46

-- Test 47: Conditional algorithm with string pattern — no match
def test47 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Price", priceAlg)] [
    .call (resolve "Price") [.stringLiteral "bananas"]
  ])) with
  | Except.error _ => true   -- noMatchingBranch
  | Except.ok _    => false

#guard test47

-- Test 48: String passed as algorithm argument
-- Echo = x, Echo('hello') → 'hello'
def echoAlg : Algorithm := alg ["x"] [] [] [.param "x"]
def test48 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Echo", echoAlg)] [
    .call (resolve "Echo") [.stringLiteral "hello"]
  ])) with
  | Except.ok (.str "hello") => true
  | _ => false

#guard test48

-- Test 49: String stored in property and returned
-- Name = 'KatLang', output = Name
def test49 : Bool :=
  let nameAlg := alg [] [] [] [.stringLiteral "KatLang"]
  match runResult (.algorithmExpr (algPrivate [] [] [("Name", nameAlg)] [resolve "Name"])) with
  | Except.ok (.str "KatLang") => true
  | _ => false

#guard test49

-- Test 50: Pattern matching — litString in isMatchEquivalent
def test50a : Bool := Pattern.isMatchEquivalent (.litString "a") (.litString "a")
def test50b : Bool := !Pattern.isMatchEquivalent (.litString "a") (.litString "b")
def test50c : Bool := !Pattern.isMatchEquivalent (.litString "a") (.litInt 1)
def test50d : Bool := !Pattern.isMatchEquivalent (.litString "a") (.bind "x")

#guard test50a
#guard test50b
#guard test50c
#guard test50d

-- Test 51: Block with unresolved implicit params → unresolvedImplicitParams error
-- A block whose algorithm has params (unresolved names become params) should
-- produce unresolvedImplicitParams, not arityMismatch.
def test51 : Bool :=
  -- param "x" makes the block have params=["x"]
  match runResult (.algorithmExpr (alg ["x"] [] [] [.param "x"])) with
  | Except.error (Error.unresolvedImplicitParams ["x"]) => true
  | _ => false

#guard test51

--------------------------------------------------------------------------------
-- filter builtin tests
--------------------------------------------------------------------------------

def isEvenAlg63 : Algorithm :=
  alg ["x"] [] [] [.binary .eq (.binary .mod (.param "x") (.num 2)) (.num 0)]

def isPositiveAlg64 : Algorithm :=
  alg ["x"] [] [] [.binary .gt (.param "x") (.num 0)]

def isNegativeAlg65 : Algorithm :=
  alg ["x"] [] [] [.binary .lt (.param "x") (.num 0)]

def badTruthAlg66 : Algorithm :=
  alg ["x"] [] [] [.stringLiteral "not-a-number"]

def alwaysFalseAlg66a : Algorithm :=
  alg ["x"] [] [] [.num 0]

def keepTenSequenceValueAlg66b : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [
        .sequenceValue [
          .bind "a", .bind "b", .bind "c", .bind "d", .bind "e",
          .bind "f", .bind "g", .bind "h", .bind "i", .bind "j"
        ]
      ],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def keepFourSequenceValueAlg66c : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c", .bind "d"]],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def rejectFourSequenceValueAlg66d : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c", .bind "d"]],
      alg [] [] [] [.num 0] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 1] ⟩
  ]

def markThreeSequenceValueAlg66e : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c"]],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def keepPairAlg67 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.bind "tag", .bind "value"],
      alg [] [] [] [.binary .eq (.binary .mod (.param "tag") (.num 2)) (.num 0)] ⟩
  ]

def badMultiFalseAlg68 : Algorithm :=
  alg ["x"] [] [] [.num 0, .num 999]

def badMultiTrueAlg69 : Algorithm :=
  alg ["x"] [] [] [.num 5, .num 0]

def badSequenceValueAlg70 : Algorithm :=
  alg ["x"] [] [] [.capture [.num 1, .num 0]]

-- `take(x, 0)` returns the exact list `[]`: one value, but a list has no truth
-- value, so a predicate built from a collection builtin is rejected.
def listTruthAlg71 : Algorithm :=
  alg ["x"] [] [] [
    .call (resolve "take") [
      .param "x",
      .num 0
    ]
  ]

-- Test 63: plain-call filter iterates emitted range items
def test63 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("KeepTenSequenceValue", keepTenSequenceValueAlg66b)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 10],
      .resolve "KeepTenSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test63

-- Test 64: descending ranges iterate emitted items in plain-call filter
def test64 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("KeepTenSequenceValue", keepTenSequenceValueAlg66b)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 10, .num 1],
      .resolve "KeepTenSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test64

-- Test 65: a sequence-value-only predicate does not match scalar emitted range items
def test65 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("KeepFourSequenceValue", keepFourSequenceValueAlg66c)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 4],
      .resolve "KeepFourSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test65

-- Test 66: a sequence-value-only rejection predicate keeps scalar emitted range items
def test66 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("RejectFourSequenceValue", rejectFourSequenceValueAlg66d)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 4],
      .resolve "RejectFourSequenceValue"
    ]
  ])) with
  | Except.ok [1, 2, 3, 4] => true
  | _ => false

#guard test66

-- Fixed-arity collection builtin binding: the ONE bound collection argument is read
-- through the one-level collection view after binding, while sibling arguments are
-- never merged into one collection (extra siblings are ordinary arity errors).

-- Sibling arguments are never flattened into one collection: filter(range(3, 6), 8, IsEven)
-- supplies three arguments where `filter(collection, predicate)` expects two, so the call
-- reports an ordinary arity error (never a silently merged collection).
def sequenceBoundaryLawFilterCommaRangeSourcePreservesBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg63)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 3, .num 6],
      .num 8,
      .resolve "IsEven"
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 3 err
  | Except.ok _ => false

#guard sequenceBoundaryLawFilterCommaRangeSourcePreservesBoundary

-- A single grouped argument `(range(3, 6)*, 8)` is ONE collection value; the post-binding
-- one-level collection view opens it, so filter's collection is [3, 4, 5, 6, 8] and keeps
-- the even items [4, 6, 8].
def sequenceBoundaryLawFilterSequenceSpreadRangeSourceExpands : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg63)] [
    .call (resolve "filter") [
      sequenceItems [sequenceSpread (.call (resolve "range") [.num 3, .num 6]), .num 8],
      .resolve "IsEven"
    ]
  ])) with
  | Except.ok [4, 6, 8] => true
  | _ => false

#guard sequenceBoundaryLawFilterSequenceSpreadRangeSourceExpands

-- A named multi-output source `Data` is ONE collection argument; the post-binding one-level
-- collection view opens it, so filter's collection is [3, 4, 5, 6].
def sequenceBoundaryLawFilterNamedSingleSourcePreservesBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .call (resolve "filter") [
      .resolve "Data",
      .resolve "IsEven"
    ]
  ])) with
  | Except.ok [4, 6] => true
  | _ => false

#guard sequenceBoundaryLawFilterNamedSingleSourcePreservesBoundary

-- A dot-call receiver `Data` binds the fixed collection parameter; the post-binding
-- one-level collection view opens it, so filter iterates [3, 4, 5, 6].
def sequenceBoundaryLawFilterDotReceiverExpands : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .dotCall (.resolve "Data") "filter" (some [.resolve "IsEven"])
  ])) with
  | Except.ok [4, 6] => true
  | _ => false

#guard sequenceBoundaryLawFilterDotReceiverExpands

-- Named multi-output plus a comma-separated scalar are two sibling arguments ((3, 4, 5, 6)
-- and 8), so `filter(collection, predicate)` receives three arguments and reports an
-- ordinary arity error (sibling preservation, never silent flattening).
def sequenceBoundaryLawFilterCommaNamedSourcePreservesBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .call (resolve "filter") [
      .resolve "Data",
      .num 8,
      .resolve "IsEven"
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 3 err
  | Except.ok _ => false

#guard sequenceBoundaryLawFilterCommaNamedSourcePreservesBoundary

-- A single grouped argument `(Data*, 8)` is ONE collection value opened by the
-- post-binding one-level collection view, so filter's collection is [3, 4, 5, 6, 8]
-- and keeps the even items [4, 6, 8].
def sequenceBoundaryLawFilterSequenceSpreadNamedSourceExpands : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .call (resolve "filter") [
      sequenceItems [sequenceSpread (.resolve "Data"), .num 8],
      .resolve "IsEven"
    ]
  ])) with
  | Except.ok [4, 6, 8] => true
  | _ => false

#guard sequenceBoundaryLawFilterSequenceSpreadNamedSourceExpands

-- Test 67: filtering an already-empty sequence-value boundary stays empty
def test67 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("KeepFourSequenceValue", keepFourSequenceValueAlg66c), ("RejectFourSequenceValue", rejectFourSequenceValueAlg66d)] [
    .call (resolve "filter") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "RejectFourSequenceValue"
      ],
      .resolve "KeepFourSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test67

-- Test 68: kept sequence values are preserved whole and in order as exact list elements
def test68 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("KeepPair", keepPairAlg67)] [
    .call (resolve "filter") [sequenceItems [
      .capture [.num 1, .num 10],
      .capture [.num 2, .num 20],
      .capture [.num 3, .num 30],
      .capture [.num 4, .num 40]],
      .resolve "KeepPair"
    ]
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 2, .atom 20],
      .sequenceValue [.atom 4, .atom 40]
    ]) => true
  | _ => false

#guard test68

-- Test 69: multi-output predicate starting with 0 is rejected
def test69 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", badMultiFalseAlg68)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test69

-- Test 70: multi-output predicate starting with nonzero is also rejected
def test70 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", badMultiTrueAlg69)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test70

-- Test 71: sequenceValue predicate result is rejected
def test71 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", badSequenceValueAlg70)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test71

-- Test 72: exact-list predicate result is rejected (a collection builtin used
-- as a filter predicate returns a list, never an atomic numeric value)
def test72 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", listTruthAlg71)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test72

-- Test 73: string predicate result is rejected
def test73 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("BadTruth", badTruthAlg66)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "BadTruth"
    ]
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test73

-- Test 74: builtin arity mismatch still follows normal conventions
def test74 : Bool :=
  match runResult (.call (resolve "filter") []) with
  | Except.error _ => true
  | _ => false

#guard test74

-- Test 75: filter predicate arity mismatch explains the implicit item argument
def test75 : Bool :=
  match runResult (.dotCall
    (.call (resolve "range") [.num 1, .num 5])
    "filter"
    (some [.num 1])) with
  | Except.error err =>
      hasContext "while evaluating filter predicate for item 0: 1 (filter passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)" err &&
      innermostIsArityMismatch 0 1 err
  | _ => false

#guard test75

--------------------------------------------------------------------------------
-- reduce builtin tests
--------------------------------------------------------------------------------

def addAlg76 : Algorithm :=
  alg ["x", "total"] [] [] [.binary .add (.param "x") (.param "total")]

def mulAlg77 : Algorithm :=
  alg ["x", "total"] [] [] [
    .binary .add
      (.binary .mul (.param "total") (.num 10))
      (.dotCall (.param "x") "count" none)
  ]

def digitsAlg78 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [
        .sequenceValue [.bind "a", .bind "b", .bind "c", .bind "d"],
        .bind "acc"
      ],
      alg [] [] [] [
        .binary .add
          (.binary .mul (.param "a") (.num 1000))
          (.binary .add
            (.binary .mul (.param "b") (.num 100))
            (.binary .add
              (.binary .mul (.param "c") (.num 10))
              (.param "d")))
      ] ⟩,
    ⟨ .sequenceValue [.bind "x", .bind "acc"],
      alg [] [] [] [.num 0] ⟩
  ]

def reduceSequenceValueItemAlg79 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "tag", .bind "value"], .bind "acc"],
      alg [] [] [] [.binary .add (.param "acc") (.param "value")] ⟩
  ]

def reduceStatsAlg80 : Algorithm :=
  alg ["x", "acc"] [] [] [
    .capture [
      .binary .add (.dotCall (.param "x") "count" none) (.index (.param "acc") (.num 0)),
      .binary .add (.index (.param "acc") (.num 1)) (.num 1)
    ]
  ]

def reduceEmptyBoundaryAlg80a : Algorithm :=
  alg ["x", "acc"] [] [] [
    .binary .add
      (.binary .add (.param "acc") (.num 100))
      (.dotCall (.param "x") "count" none)
  ]

def reduceEmptyBoundarySequenceValueAccAlg80b : Algorithm :=
  alg ["x", "acc"] [] [] [
    .capture [
      .binary .add
        (.binary .add (.index (.param "acc") (.num 0)) (.num 100))
        (.dotCall (.param "x") "count" none),
      .binary .add (.index (.param "acc") (.num 1)) (.num 1)
    ]
  ]

def addItemCountAlg80c : Algorithm :=
  alg ["x", "acc"] [] [] [
    .binary .add
      (.dotCall (.param "x") "count" none)
      (.param "acc")
  ]

-- A literal `()` body keeps testing the empty-step failure: `take(x, 0)` now
-- returns the exact list `[]`, which is ONE valid accumulator value.
def reduceEmptyAlg81 : Algorithm :=
  alg ["x", "acc"] [] [] [.emptySequence 0]

def reduceMultiAlg82 : Algorithm :=
  alg ["x", "acc"] [] [] [.param "acc", .param "x"]

def sequenceBoundaryLawAocCountMatchStepAlg : Algorithm :=
  algPrivate ["element", "tt"] [] [
    ("T", alg [] [] [] [
      .call (resolve "atoms") [.param "tt"]
    ])
  ] [
    .capture [
      .dotCall (resolve "T") "first" none,
      .binary .add
        (.index (resolve "T") (.num 1))
        (.call (resolve "if") [
          .binary .eq (.param "element") (.dotCall (resolve "T") "first" none),
          .num 1,
          .num 0
        ])
    ]
  ]

-- Exact AoC-style regression: Right is a named multi-output property bound as
-- reduce's collection argument, so the collection view must iterate its items.
def sequenceBoundaryLawAocNamedReduceSource : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Left", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]),
    ("Right", alg [] [] [] [.num 4, .num 3, .num 5, .num 3, .num 9, .num 3]),
    ("CountMatchStep", sequenceBoundaryLawAocCountMatchStepAlg),
    ("MatchCount", alg ["value"] [] [] [
      .index
        (.call (resolve "reduce") [
          resolve "Right",
          resolve "CountMatchStep",
          .capture [.param "value", .num 0]
        ])
        (.num 1)
    ]),
    ("SimilarityAt", alg ["value"] [] [] [
      .binary .mul
        (.param "value")
        (.call (resolve "MatchCount") [.param "value"])
    ]),
    ("Part2", alg [] [] [] [
      .dotCall
        (.dotCall (resolve "Left") "map" (some [resolve "SimilarityAt"]))
        "sum"
        none
    ])
  ] [
    resolve "Part2"
  ])) with
  | Except.ok [31] => true
  | _ => false

#guard sequenceBoundaryLawAocNamedReduceSource

-- Test 76: dot-call reduce over range with additive step
def test76 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Add", addAlg76)] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "reduce"
      (some [.resolve "Add", .num 0])
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test76

-- Test 77: plain-call reduce iterates emitted range items
def test77 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Mul", mulAlg77)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 1, .num 4],
      .resolve "Mul",
      .num 1
    ]
  ])) with
  | Except.ok [11111] => true
  | _ => false

#guard test77

-- Test 77a: plain-call reduce can still observe sequence-value range content explicitly
def test77a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AddItemCount", addItemCountAlg80c)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 3, .num 6],
      .resolve "AddItemCount",
      .num 0
    ]
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test77a

-- Test 78: sequence-value-only reduce branches do not match scalar emitted range items
def test78 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Digits", digitsAlg78)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 1, .num 4],
      .resolve "Digits",
      .num 0
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test78

-- Test 79: reducing an empty plain-call collection returns the initial accumulator
def test79 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a), ("MarkEmptyBoundary", reduceEmptyBoundaryAlg80a)] [
    .call (resolve "reduce") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ],
      .resolve "MarkEmptyBoundary",
      .num 0
    ]
  ])) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard test79

-- Test 80: sequence-value accumulators also stay unchanged when reducing an empty collection
def test80 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a), ("MarkEmptyBoundary", reduceEmptyBoundarySequenceValueAccAlg80b)] [
    .call (resolve "reduce") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ],
      .resolve "MarkEmptyBoundary",
      .capture [.num 7, .num 9]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 7, .atom 9]) => true
  | _ => false

#guard test80

-- Test 81: sequenceValue collection elements are passed to the step as whole values
def test81 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("TakeValue", reduceSequenceValueItemAlg79)] [
    .call (resolve "reduce") [sequenceItems [
      .capture [.num 1, .num 10],
      .capture [.num 2, .num 20],
      .capture [.num 3, .num 30]],
      .resolve "TakeValue",
      .num 0
    ]
  ])) with
  | Except.ok [60] => true
  | _ => false

#guard test81

-- Test 82: sequence-value accumulators keep their shape while emitted range items are reduced
def test82 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Stats", reduceStatsAlg80)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 1, .num 4],
      .resolve "Stats",
      .capture [.num 0, .num 0]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 4, .atom 4]) => true
  | _ => false

#guard test82

-- Test 83: reduce step must not return an empty result
def test83 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", reduceEmptyAlg81)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad",
      .num 0
    ]
  ])) with
  | Except.error err => hasContext "reduce step must return a single accumulator value" err && innermostIsBadArity err
  | _ => false

#guard test83

-- Test 84: reduce step must not return multiple top-level outputs
def test84 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", reduceMultiAlg82)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad",
      .num 0
    ]
  ])) with
  | Except.error err => hasContext "reduce step must return a single accumulator value" err && innermostIsBadArity err
  | _ => false

#guard test84

-- Test 84a: reduce is an ordinary fixed-arity callable — reduce(1) supplies one
-- argument where `reduce(collection, reducer, initial)` expects three.
def test84a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Add", addAlg76)] [
    .call (resolve "reduce") [
      .num 1
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 3 1 err
  | _ => false

#guard test84a

-- Test 84b: reduce((1, 2, 3), Add) supplies two of the three fixed arguments —
-- an ordinary arity error, with no suffix-binding reinterpretation of the
-- argument list.
def test84b : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Add", addAlg76)] [
    .call (resolve "reduce") [
      sequenceItems [.num 1, .num 2, .num 3],
      .resolve "Add"
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 3 2 err
  | _ => false

#guard test84b

-- Test 84c: the dotted missing-initial hint is reserved for a visibly
-- parameterized reducer. An ordinary value in the sole control slot follows
-- the fixed signature and reports the ordinary three-versus-two arity error.
def test84c : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [
    sequenceItems [.num 1, .num 2, .num 3]
  ])] [
    .dotCall (resolve "Values") "reduce" (some [.num 0])
  ])) with
  | Except.error err => innermostIsArityMismatch 3 2 err
  | _ => false

#guard test84c

--------------------------------------------------------------------------------
-- map builtin tests
--------------------------------------------------------------------------------

def doubleAlg85 : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]

def takeMiddleSequenceValueAlg85a : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c", .bind "d", .bind "e"]],
      alg [] [] [] [.param "c"] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def squareAlg86 : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.param "x")]

def tagAlg87 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "first", .bind "b", .bind "c", .bind "d", .bind "last"]],
      alg [] [] [] [
        .binary .add (.binary .mul (.param "first") (.num 10)) (.param "last")
      ] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def countMembersAlg88a : Algorithm :=
  alg ["x"] [] [] [
    .dotCall (.param "x") "count" none
  ]

def takePairValueAlg89 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.bind "tag", .bind "value"],
      alg [] [] [] [.param "value"] ⟩
  ]

def pairWithSquareAlg90 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "first", .bind "middle", .bind "last"]],
      alg [] [] [] [
        .capture [
          .param "first",
          .param "last"
        ]
      ] ⟩,
    ⟨ .bind "x",
      alg [] [] [] [
        .capture [.num 0, .num 0]
      ] ⟩
  ]

-- A literal `()` body keeps testing the empty-transform failure: `take(x, 0)` now
-- returns the exact list `[]`, which is ONE valid element.
def mapEmptyAlg91 : Algorithm :=
  alg ["x"] [] [] [.emptySequence 0]

def mapMultiAlg92 : Algorithm :=
  alg ["x"] [] [] [
    .param "x",
    .num 0
  ]

-- Test 85: dot-call map doubles each range element left-to-right
def test85 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Double", doubleAlg85)] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "map"
      (some [.resolve "Double"])
  ])) with
  | Except.ok [2, 4, 6, 8, 10] => true
  | _ => false

#guard test85

def factorialMapAlg85a : Algorithm :=
  alg ["n"] [] [] [
    .call (resolve "if") [
      .binary .eq (.param "n") (.num 0),
      .num 1,
      .binary .mul
        (.call (resolve "Factorial") [
          .binary .sub (.param "n") (.num 1)
        ])
        (.param "n")
    ]
  ]

def test85a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Factorial", factorialMapAlg85a)] [
    .dotCall
      (.capture [.num 0, .num 1, .num 2, .num 3, .num 4])
      "map"
      (some [.resolve "Factorial"])
  ])) with
  | Except.ok [1, 1, 2, 6, 24] => true
  | _ => false

#guard test85a

-- Test 86: plain-call map iterates emitted range items
def test86 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("TakeMiddle", takeMiddleSequenceValueAlg85a)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 1, .num 5],
      .resolve "TakeMiddle"
    ]
  ])) with
  | Except.ok [0, 0, 0, 0, 0] => true
  | _ => false

#guard test86

-- Test 86a: plain-call map applies scalar transforms to emitted range items
def test86a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Double", doubleAlg85)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 1, .num 5],
      .resolve "Double"
    ]
  ])) with
  | Except.ok [2, 4, 6, 8, 10] => true
  | _ => false

#guard test86a

-- Test 87: sequence-value-only map branches do not match scalar emitted range items
def test87 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Tag", tagAlg87)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 5, .num 1],
      .resolve "Tag"
    ]
  ])) with
  | Except.ok [0, 0, 0, 0, 0] => true
  | _ => false

#guard test87

-- Test 88: mapping over an empty filter-result list yields the exact empty list `[]`
def test88 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a), ("CountMembers", countMembersAlg88a)] [
    .call (resolve "map") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ],
      .resolve "CountMembers"
    ]
  ])) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard test88

-- Test 89: sequenceValue collection elements are passed to the transform as whole values
def test89 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("TakeValue", takePairValueAlg89)] [
    .call (resolve "map") [sequenceItems [
      .capture [.num 1, .num 10],
      .capture [.num 2, .num 20],
      .capture [.num 3, .num 30]],
      .resolve "TakeValue"
    ]
  ])) with
  | Except.ok [10, 20, 30] => true
  | _ => false

#guard test89

-- Test 90: sequence-value mapped results are accepted for emitted range items
def test90 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("PairWithSquare", pairWithSquareAlg90)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "PairWithSquare"
    ]
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 0, .atom 0],
      .sequenceValue [.atom 0, .atom 0],
      .sequenceValue [.atom 0, .atom 0]
    ]) => true
  | _ => false

#guard test90

-- Test 91: map transform must not return an empty result
def test91 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", mapEmptyAlg91)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "map transform must return a single element" err && innermostIsBadArity err
  | _ => false

#guard test91

-- Test 92: map transform must not return multiple top-level outputs
def test92 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", mapMultiAlg92)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "map transform must return a single element" err && innermostIsBadArity err
  | _ => false

#guard test92

--------------------------------------------------------------------------------
-- sum builtin tests
--------------------------------------------------------------------------------

def isEvenAlg93 : Algorithm :=
  alg ["x"] [] [] [
    .binary .eq (.binary .mod (.param "x") (.num 2)) (.num 0)
  ]

-- Test 93: plain-call sum adds expanded range items
def test93 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test93

-- Test 94: dot-call sum uses receiver injection with no explicit args
def test94 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "sum"
      none
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test94

-- Test 95: descending ranges also expand for plain-call sum
def test95 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [
      .call (resolve "range") [.num 5, .num 1]
    ]
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test95

-- Test 96: sum composes with filter and preserves strict top-level semantics
def test96 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 10])
        "filter"
        (some [.resolve "IsEven"]))
      "sum"
      none
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard test96

-- Test 97: sum composes with map and sums the mapped top-level elements
def test97 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Square", squareAlg86)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 4])
        "map"
        (some [.resolve "Square"]))
      "sum"
      none
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard test97

-- Test 98: plain-call sum of an empty collection returns zero
def test98 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "sum") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test98

-- Test 99: a single atomic value is treated as a one-element collection
def test99 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [.num 5]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test99

-- Test 100: sequenceValue top-level elements are rejected rather than flattened
def test100 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [sequenceValuePairs]
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test100

-- Test 101: string elements are rejected by sum
def test101 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [.stringLiteral "hello"]
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test101

--------------------------------------------------------------------------------
-- count builtin tests
--------------------------------------------------------------------------------

-- Test 102: plain-call count counts expanded range items
def test102 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test102

-- Test 103: dot-call count uses receiver injection with no explicit args
def test103 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "count"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test103

-- Test 103a: dot-call count matches the shared sequence-value receiver examples
def countReceiverNormalizationRoot103a : Algorithm :=
  algPrivate [] [] [
    ("Data1", alg [] [] [] [.num 1, .num 7]),
    ("Data2", alg [] [] [] [.capture [.num 1, .num 7]])
  ] [
    .dotCall (.resolve "Data1") "count" none,
    .dotCall (.resolve "Data2") "count" none,
    .dotCall (.capture [.num 1, .num 7]) "count" none,
    .dotCall (.capture [
      .capture [.num 1, .num 7]
    ]) "count" none
  ]

def test103a : Bool :=
  match runFlat (.algorithmExpr countReceiverNormalizationRoot103a) with
  | Except.ok [2, 2, 2, 2] => true
  | _ => false

#guard test103a

-- Test 103b: nested sequence-value receiver boundaries are preserved after one strip
def test103b : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall sequenceValuePairs "count" none,
    .dotCall (.capture [sequenceValuePairs]) "count" none
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test103b

-- Test 104: descending ranges still count all expanded top-level items
def test104 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [
      .call (resolve "range") [.num 5, .num 1]
    ]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test104

-- Test 105: count composes with filter over kept top-level elements
def test105 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 10])
        "filter"
        (some [.resolve "IsEven"]))
      "count"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test105

-- Test 106: count composes with map and counts mapped top-level elements
def test106 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Square", squareAlg86)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 4])
        "map"
        (some [.resolve "Square"]))
      "count"
      none
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test106

-- Test 107: plain-call count of an empty collection is zero
def test107 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "count") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test107

-- Test 107a: dot-call count of an empty filtered receiver is zero
def test107a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .dotCall
      (.dotCall
        (.capture [.num 1, .num 5, .num 3])
        "filter"
        (some [.resolve "AlwaysFalse"]))
      "count"
      none
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test107a

-- Test 107b: count(collection) is an ordinary fixed-arity callable, so an empty
-- call is an arity error — absence of an argument is never an empty collection
-- (the explicit empty-collection call `count(())` counts zero).
def test107b : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") []
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | _ => false

#guard test107b

--------------------------------------------------------------------------------
-- Fixed-arity collection builtin calls (mirrors the C# fixed collection-object
-- binding tests): a collection builtin is an ordinary fixed-arity callable
-- (`sum(collection)`, `contains(collection, item)`) whose ONE bound collection
-- value is read through the one-level collection view after binding.
--------------------------------------------------------------------------------

-- sum(collection): one grouped value is the collection argument; inline
-- multi-item calls and empty calls are ordinary arity errors.
def builtinSumTakesOneCollectionArgument : Bool :=
  let inlineErrs :=
    match runResult (.algorithmExpr (alg [] [] [] [
      .call (resolve "sum") [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]
    ])) with
    | Except.error err => innermostIsArityMismatch 1 6 err
    | _ => false
  let grouped :=
    match runFlat (.algorithmExpr (alg [] [] [] [
      .call (resolve "sum") [.capture [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]]
    ])) with
    | Except.ok [16] => true
    | _ => false
  let emptyErrs :=
    match runResult (.algorithmExpr (alg [] [] [] [.call (resolve "sum") []])) with
    | Except.error err => innermostIsArityMismatch 1 0 err
    | _ => false
  inlineErrs && grouped && emptyErrs

#guard builtinSumTakesOneCollectionArgument

-- Multiple sibling arguments are never flattened into one collection: sum(A, B) with
-- A = (1, 2) and B = (3, 4) is a two-argument arity error, and sum(A*, B*) opens the
-- spreads into FOUR ordinary argument slots (also an arity error). The concatenation
-- rewrite groups the spreads into ONE collection argument: sum((*A, *B)) = 10.
def builtinSumSiblingsNotFlattened : Bool :=
  let siblingsErr :=
    match runResult (.algorithmExpr (algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4])
    ] [ .call (resolve "sum") [resolve "A", resolve "B"] ])) with
    | Except.error err => innermostIsArityMismatch 1 2 err
    | _ => false
  let spreadSiblingsErr :=
    match runResult (.algorithmExpr (algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4])
    ] [ .call (resolve "sum") [sequenceSpread (resolve "A"), sequenceSpread (resolve "B")] ])) with
    | Except.error err => innermostIsArityMismatch 1 4 err
    | _ => false
  let groupedConcatenates :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4])
    ] [ .call (resolve "sum") [
          .capture [sequenceSpread (resolve "A"), sequenceSpread (resolve "B")]] ])) with
    | Except.ok [10] => true
    | _ => false
  siblingsErr && spreadSiblingsErr && groupedConcatenates

#guard builtinSumSiblingsNotFlattened

-- contains(collection, item): the first argument is the collection and the second is the
-- item. The inline multi-item call is an arity error; the grouped form binds.
def builtinContainsTakesCollectionAndItem : Bool :=
  let inlineErrs :=
    match runResult (.algorithmExpr (alg [] [] [] [
      .call (resolve "contains") [.num 1, .num 2, .num 3, .num 2]
    ])) with
    | Except.error err => innermostIsArityMismatch 2 4 err
    | _ => false
  let grouped :=
    match runFlat (.algorithmExpr (alg [] [] [] [
      .call (resolve "contains") [.capture [.num 1, .num 2, .num 3], .num 2]
    ])) with
    | Except.ok [1] => true
    | _ => false
  inlineErrs && grouped

#guard builtinContainsTakesCollectionAndItem

-- A collection builtin is NOT a user variadic: sum(3, 4, 2, 1, 3, 3) is an arity error
-- under `sum(collection)`, while a user variadic G(*values) = values.sum captures the
-- same inline items and sums them; the grouped call sum((3, 4, 2, 1, 3, 3)) is the
-- builtin twin.
def builtinFixedArityDiffersFromUserVariadic : Bool :=
  let builtinInlineErrs :=
    match runResult (.algorithmExpr (alg [] [] [] [
      .call (resolve "sum") [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]
    ])) with
    | Except.error err => innermostIsArityMismatch 1 6 err
    | _ => false
  let builtinGrouped :=
    match runFlat (.algorithmExpr (alg [] [] [] [
      .call (resolve "sum") [.capture [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]]
    ])) with
    | Except.ok [16] => true
    | _ => false
  let userSumAlg : Algorithm :=
    algWithParameters [{ name := "values", kind := .collecting }] [] [] [
      .dotCall (.param "values") "sum" none
    ]
  let viaUser :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("G", userSumAlg)] [
      .call (resolve "G") [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]
    ])) with
    | Except.ok [16] => true
    | _ => false
  builtinInlineErrs && builtinGrouped && viaUser

#guard builtinFixedArityDiffersFromUserVariadic

-- Test 108: count's one bound sequence-valued argument is opened by the
-- one-level collection view — two nested pairs are two items.
def test108 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [sequenceValuePairs]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test108

-- Test 108a: plain-call `count(filter(X, pred))` destructures the one filtered
-- sequence argument and counts its kept items.
def test108aPlainCountFilterCountsOneSequenceValueResult : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .call (resolve "count") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "IsEven"
      ]
    ]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test108aPlainCountFilterCountsOneSequenceValueResult

-- Test 109: a single atomic value is treated as a one-element collection
def test109 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [.num 5]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test109

-- Test 110: string elements are valid top-level elements for count
def test110 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [.stringLiteral "hello"]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110

-- Test 110a: plain-call contains searches expanded range items
def test110a : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "contains") [
      .call (resolve "range") [.num 1, .num 5],
      .num 3
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110a

-- Test 110b: contains returns zero when no top-level item matches
def test110b : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "contains") [
      .call (resolve "range") [.num 1, .num 5],
      .num 9
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test110b

-- Test 110c: dot-call contains matches plain-call receiver semantics
def test110c : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "contains"
      (some [.num 4])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110c

-- Test 110d: contains compares sequence-value top-level elements structurally
def test110d : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "contains") [
      sequenceItems [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ],
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110d

-- Test 110e: contains searches top-level items only, not nested sequence elements
def test110e : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  let nestedCollection := sequenceItems [sequenceValuePairs, .num 0]
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "contains") [
      nestedCollection,
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test110e

-- Test 110f: selection-projected content follows the same contains rules in both call styles
def containsProjectionRoot110f : Algorithm :=
  algPrivate [] [] [
    ("Data", alg [] [] [] [
      .capture [.num 7, .num 6, .num 4, .num 2, .num 1],
      .capture [.num 1, .num 2, .num 3, .num 4, .num 5]
    ])
  ] [
    .call (resolve "contains") [
      .index (.resolve "Data") (.num 0),
      .num 4
    ],
    .dotCall (.index (.resolve "Data") (.num 0)) "contains" (some [.num 4])
  ]

def test110f : Bool :=
  match runFlat (.algorithmExpr containsProjectionRoot110f) with
  | Except.ok [1, 1] => true
  | _ => false

#guard test110f

-- Test 110g: contains's item argument stays outside the collection — a
-- multi-output helper bound to `item` is compared as one grouped value.
def test110g : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Item", alg [] [] [] [.num 1, .num 2])
  ] [
    .call (resolve "contains") [
      .capture [.num 1, .num 2],
      .resolve "Item"
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test110g

--------------------------------------------------------------------------------
-- min builtin tests
--------------------------------------------------------------------------------

def negateAlg111 : Algorithm :=
  alg ["x"] [] [] [
    .unary .minus (.param "x")
  ]

-- Test 111: plain-call min compares expanded range items
def test111 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test111

-- Test 112: dot-call min uses receiver injection with no explicit args
def test112 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "min"
      none
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test112

-- Test 113: descending ranges also expand for plain-call min
def test113 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [
      .call (resolve "range") [.num 5, .num 1]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test113

-- Test 114: min composes with filter over kept top-level elements
def test114 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 10])
        "filter"
        (some [.resolve "IsEven"]))
      "min"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test114

-- Test 115: min composes with map and compares mapped top-level elements
def test115 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Negate", negateAlg111)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 4])
        "map"
        (some [.resolve "Negate"]))
      "min"
      none
  ])) with
  | Except.ok [-4] => true
  | _ => false

#guard test115

-- Test 116: plain-call min requires a non-empty collection
def test116 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "min") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "min requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test116

-- Test 117: a single atomic value is treated as a one-element collection
def test117 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [.num 5]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test117

-- Test 118: sequenceValue top-level elements are rejected rather than flattened
def test118 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [sequenceValuePairs]
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test118

-- Test 119: string elements are rejected by min
def test119 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [.stringLiteral "hello"]
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test119

--------------------------------------------------------------------------------
-- max builtin tests
--------------------------------------------------------------------------------

-- Test 120: plain-call max compares expanded range items
def test120 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test120

-- Test 121: dot-call max uses receiver injection with no explicit args
def test121 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "max"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test121

-- Test 122: descending ranges also expand for plain-call max
def test122 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [
      .call (resolve "range") [.num 5, .num 1]
    ]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test122

-- Test 123: max composes with filter over kept top-level elements
def test123 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 10])
        "filter"
        (some [.resolve "IsEven"]))
      "max"
      none
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test123

-- Test 124: max composes with map and compares mapped top-level elements
def test124 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Negate", negateAlg111)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 4])
        "map"
        (some [.resolve "Negate"]))
      "max"
      none
  ])) with
  | Except.ok [-1] => true
  | _ => false

#guard test124

-- Test 125: plain-call max requires a non-empty collection
def test125 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "max") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "max requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test125

-- Test 126: a single atomic value is treated as a one-element collection
def test126 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [.num 5]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test126

-- Test 127: sequenceValue top-level elements are rejected rather than flattened
def test127 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [sequenceValuePairs]
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test127

-- Test 128: string elements are rejected by max
def test128 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [.stringLiteral "hello"]
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test128

-- Test 129: plain-call avg averages expanded range items
def test129 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test129

-- Test 130: dot-call avg uses receiver injection with no explicit args
def test130 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "avg"
      none
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test130

-- Test 131: descending ranges also expand for plain-call avg
def test131 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [
      .call (resolve "range") [.num 5, .num 1]
    ]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test131

-- Test 132: avg composes with filter over kept top-level elements
def test132 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 10])
        "filter"
        (some [.resolve "IsEven"]))
      "avg"
      none
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test132

-- Test 133: avg composes with map and averages mapped top-level elements
def test133 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Double", doubleAlg85)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 4])
        "map"
        (some [.resolve "Double"]))
      "avg"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test133

-- Test 134: plain-call avg requires a non-empty collection
def test134 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "avg") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "avg requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test134

-- Test 135: a single atomic value is treated as a one-element collection
def test135 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [.num 5]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test135

-- Test 136: sequenceValue top-level elements are rejected rather than flattened
def test136 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [sequenceValuePairs]
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test136

-- Test 137: string elements are rejected by avg
def test137 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [.stringLiteral "hello"]
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test137

--------------------------------------------------------------------------------
-- order builtins tests
--------------------------------------------------------------------------------

-- Test 138: ordinary builtin-call order sorts direct multi-argument inputs ascending and preserves duplicates
def test138 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [sequenceItems [
      .num 3,
      .num 4,
      .num 2,
      .num 1,
      .num 3,
      .num 3
    ]]
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test138

-- Test 139: dot-call order sorts property output ascending
def test139 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .dotCall (.resolve "Values") "order" none
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test139

-- Test 140: dot-call orderDesc sorts descending and preserves duplicates
def test140 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .dotCall (.resolve "Values") "orderDesc" none
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#guard test140

-- Test 141: sorting a descending range returns ascending output for order
def test141 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 5, .num 1])
      "order"
      none
  ])) with
  | Except.ok [1, 2, 3, 4, 5] => true
  | _ => false

#guard test141

-- Test 142: dot-call order preserves empty receiver outputs
def test142 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .dotCall
      (.call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ])
      "order"
      none
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test142

-- Test 143: unsupported sortable elements are rejected by order
def test143 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [
      .capture [.num 1, .stringLiteral "hello"]
    ]
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 1 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test143

--------------------------------------------------------------------------------
-- first/last builtin tests
--------------------------------------------------------------------------------

-- Test 144: plain-call first returns the first expanded range item
def test144 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "first") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test144

-- Test 145: dot-call first uses receiver injection with no explicit args
def test145 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "first"
      none
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test145

-- Test 146: plain-call last returns the last expanded range item
def test146 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "last") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test146

-- Test 147: dot-call last uses receiver injection with no explicit args
def test147 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "last"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test147

-- Test 148: first returns the first item of the grouped collection (opened by the one-level collection view)
def test148 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "first") [sequenceValuePairs]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard test148

-- Test 149: last returns the last item of the grouped collection (opened by the one-level collection view)
def test149 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "last") [sequenceValuePairs]
  ])) with
  | Except.ok (.sequenceValue [.atom 3, .atom 4]) => true
  | _ => false

#guard test149

-- Test 150: plain-call first requires a non-empty collection
def test150 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "first") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "first requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test150

-- Test 151: plain-call last requires a non-empty collection
def test151 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "last") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "last requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test151

-- Additional sequence-input builtin regression tests

def test151a : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [sequenceItems [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]]
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test151a

def test151b : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "orderDesc") [sequenceItems [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]]
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#guard test151b

def test151c : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2])] [
    .call (resolve "order") [sequenceItems [sequenceSpread (.resolve "Values"), .num 1, .num 3]]
  ])) with
  | Except.ok [1, 2, 3, 3, 4] => true
  | _ => false

#guard test151c

def test151d : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]]
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151d

def test151e : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "orderDesc") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]]
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151e

def test151f : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "first") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard test151f

def test151g : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "last") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]]
  ])) with
  | Except.ok (.sequenceValue [.atom 3, .atom 4]) => true
  | _ => false

#guard test151g

def test151h : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [sequenceItems [.num 10, .num 20, .num 30]]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test151h

def test151i : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test151i

def test151j : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [sequenceItems [.num 10, .num 20, .num 30]]
  ])) with
  | Except.ok [60] => true
  | _ => false

#guard test151j

def test151k : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [sequenceItems [.num 10, .num 4, .num 7]]
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test151k

def test151l : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [sequenceItems [.num 10, .num 4, .num 7]]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test151l

def test151m : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [sequenceItems [.num 10, .num 20, .num 30]]
  ])) with
  | Except.ok [20] => true
  | _ => false

#guard test151m

def test151n : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("KeepFourSequenceValue", keepFourSequenceValueAlg66c)] [
    .call (resolve "filter") [
      sequenceItems [.num 1, .num 2, sequenceSpread (.call (resolve "range") [.num 3, .num 6])],
      .resolve "KeepFourSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test151n

def test151o : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("MarkThreeSequenceValue", markThreeSequenceValueAlg66e)] [
    .call (resolve "map") [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") [.num 2, .num 4])],
      .resolve "MarkThreeSequenceValue"
    ]
  ])) with
  | Except.ok [0, 0, 0, 0] => true
  | _ => false

#guard test151o

-- SequenceValue source `map((1, range(2, 4)*), MarkThreeSequenceValue)`: spread
-- contributes inside the single grouped value, opened by the collection view.
def test151ob : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("MarkThreeSequenceValue", markThreeSequenceValueAlg66e)] [
    .call (resolve "map") [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") [.num 2, .num 4])],
      .resolve "MarkThreeSequenceValue"
    ]
  ])) with
  | Except.ok [0, 0, 0, 0] => true
  | _ => false

#guard test151ob

-- SequenceValue source `filter((1, range(2, 4)*), MarkThreeSequenceValue)`: spread
-- contributes inside the single grouped value, opened by the collection view.
def test151oc : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("MarkThreeSequenceValue", markThreeSequenceValueAlg66e)] [
    .call (resolve "filter") [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") [.num 2, .num 4])],
      .resolve "MarkThreeSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test151oc

def markSequenceValueRangeDirectCallAlg151oa : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c"]],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

-- `range(1, 3)` is now an exact list value, and multi-clause conditional groups
-- match sequence values only (list patterns are deferred), so the list argument
-- takes the fallback clause.
def test151oa : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("MarkSequenceValueRange", markSequenceValueRangeDirectCallAlg151oa)] [
    .call (resolve "MarkSequenceValueRange") [
      .call (resolve "range") [.num 1, .num 3]
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test151oa

def test151p : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AddItemCount", addItemCountAlg80c)] [
    .call (resolve "reduce") [
      sequenceItems [.num 1, .num 2, sequenceSpread (.call (resolve "range") [.num 3, .num 4])],
      .resolve "AddItemCount",
      .num 0
    ]
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test151p

def addSequenceValueRangeAlg151pb : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c"], .bind "acc"],
      alg [] [] [] [.binary .add (.param "acc") (.num 100)] ⟩,
    ⟨ .sequenceValue [.bind "x", .bind "acc"],
      alg [] [] [] [.binary .add (.param "acc") (.param "x")] ⟩
  ]

def test151pb : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AddSequenceValueRange", addSequenceValueRangeAlg151pb)] [
    .call (resolve "reduce") [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") [.num 2, .num 4])],
      .resolve "AddSequenceValueRange",
      .num 0
    ]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test151pb

-- SequenceValue source `reduce((1, range(2, 4)*), AddSequenceValueRange, 0)`:
-- the spread marker contributes inside the single grouped value, opened by the collection view.
def test151pc : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AddSequenceValueRange", addSequenceValueRangeAlg151pb)] [
    .call (resolve "reduce") [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") [.num 2, .num 4])],
      .resolve "AddSequenceValueRange",
      .num 0
    ]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test151pc

def test151q : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [
      sequenceItems [.capture [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3], .num 0]
    ]
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151q

def test151r : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .call (resolve "order") [.resolve "Values"]
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test151r

def test151s : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.capture [.num 3, .num 4, .num 2]])] [
    .call (resolve "order") [.resolve "Values"]
  ])) with
  | Except.ok [2, 3, 4] => true
  | _ => false

#guard test151s

def test151t : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "orderDesc") [
      sequenceItems [.capture [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3], .num 0]
    ]
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151t

def test151u : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .call (resolve "orderDesc") [.resolve "Values"]
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#guard test151u

def test151v : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.capture [.num 3, .num 4, .num 2]])] [
    .call (resolve "orderDesc") [.resolve "Values"]
  ])) with
  | Except.ok [4, 3, 2] => true
  | _ => false

#guard test151v

def test151w : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test151w

def test151x : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "first") [
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard test151x

def test151y : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "last") [
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok (.atom 2) => true
  | _ => false

#guard test151y

-- Additional uniform sequence-extraction wrapper regressions

def test152 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("KeepSecondEven", evenPredicateAlg19d),
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 1, .num 3]
    ])
  ] [
    .call (resolve "filter") [
      .resolve "Values",
      .resolve "KeepSecondEven"
    ]
  ])) with
  -- One sequence-valued item is kept; the exact-list materializer keeps it as one
  -- list element, so the result is `[(1, 2)]` (never erased to the item itself).
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard test152

def test153 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("TakeValue", takePairValueAlg89),
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .call (resolve "map") [
      .resolve "Values",
      .resolve "TakeValue"
    ]
  ])) with
  | Except.ok [2, 4] => true
  | _ => false

#guard test153

def test154 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("AddValue", reduceSequenceValueItemAlg79),
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .call (resolve "reduce") [
      .resolve "Values",
      .resolve "AddValue",
      .num 0
    ]
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test154

def test155 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2, .num 3]
    ])
  ] [
    .call (resolve "count") [.resolve "Values"]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test155

def test156 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .call (resolve "count") [.resolve "Values"]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test156

def test157 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2]
    ])
  ] [
    .call (resolve "first") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard test157

def test158 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2]
    ])
  ] [
    .call (resolve "last") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 2) => true
  | _ => false

#guard test158

def test159 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 10, .num 20, .num 30]
    ])
  ] [
    .call (resolve "sum") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 60) => true
  | _ => false

#guard test159

def test160 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 10, .num 20, .num 30]
    ])
  ] [
    .call (resolve "min") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 10) => true
  | _ => false

#guard test160

def test161 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 10, .num 20, .num 30]
    ])
  ] [
    .call (resolve "max") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 30) => true
  | _ => false

#guard test161

def test162 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 10, .num 20, .num 30]
    ])
  ] [
    .call (resolve "avg") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 20) => true
  | _ => false

#guard test162

def test163 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 20, .num 30])
  ] [
    .call (resolve "sum") [.resolve "Values"]
  ])) with
  | Except.ok [60] => true
  | _ => false

#guard test163

def test164 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 4, .num 7])
  ] [
    .call (resolve "min") [.resolve "Values"]
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test164

def test165 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 4, .num 7])
  ] [
    .call (resolve "max") [.resolve "Values"]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test165

def test166 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 20, .num 30])
  ] [
    .call (resolve "avg") [.resolve "Values"]
  ])) with
  | Except.ok [20] => true
  | _ => false

#guard test166

def test167 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .dotCall
      (.call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ])
      "orderDesc"
      none
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test167

-- avg(1, 2) = 3.tdiv 2 = 1 in the Lean Int core. The decimal runtime returns the
-- exact fractional average (1.5) instead; the integer result is a Lean model
-- limitation, not the C# runtime contract.
def test168 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [sequenceItems [.num 1, .num 2]]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test168

-- avg truncates its quotient toward zero (Int.tdiv), matching the truncating
-- division convention of `div`/`mod`: avg(-1, -2) = (-3).tdiv 2 = -1.
-- The decimal runtime keeps the exact fractional average (-1.5) instead.
def test169 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [sequenceItems [.num (-1), .num (-2)]]
  ])) with
  | Except.ok [-1] => true
  | _ => false

#guard test169

def test170 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test170

def test171 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "orderDesc") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test171

def test172 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test172

def test173 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test173

def test174 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test174

def test175 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test175

def test176 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [
      sequenceItems [.num 1, .num 2, .num 3, .num 4, .num 5],
      .num 3
    ]
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test176

def test177 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 1, .num 2, .num 3, .num 4, .num 5],
      .num 3
    ]
  ])) with
  | Except.ok [4, 5] => true
  | _ => false

#guard test177

def test178 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 0
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test178

def test179 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 0
    ]
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test179

def test180 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num (-2)
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test180

def test181 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num (-2)
    ]
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test181

def test182 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 10
    ]
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test182

def test183 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 10
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test183

def test184 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "take") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ],
      .num 3
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test184

def test185 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "skip") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ],
      .num 3
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test185

def test186 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]],
      .num 1
    ]
  ])) with
  -- Taking one sequence-valued item keeps it as one exact list element:
  -- the result is `[(1, 2)]` (`first` still selects the item itself).
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard test186

def test187 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]],
      .num 1
    ]
  ])) with
  -- Skipping to one remaining sequence-valued item keeps it as one exact list
  -- element: the result is `[(3, 4)]` (`last` still selects the item itself).
  | Except.ok (.listValue [.sequenceValue [.atom 3, .atom 4]]) => true
  | _ => false

#guard test187

-- Regression block for the exact-list builtin result boundary:
-- `T = take(((1, 2), (3, 4)), 1)` is the exact list `[(1, 2)]` — equal to the
-- list literal `[(1, 2)]`, NOT equal to the sequence `(1, 2)` (or its grouping
-- form `((1, 2))`), and counted as ONE kept item by `count(T)` and `T.count`
-- alike (count opens exactly the one list boundary).
def takeSingleKeptItemProgram (output : KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("T", alg [] [] [] [
      .call (resolve "take") [
        sequenceItems [
          .capture [.num 1, .num 2],
          .capture [.num 3, .num 4]
        ],
        .num 1
      ]
    ])
  ] [output])

def takeSingleKeptItemIsExactListValue : Bool :=
  match runResult (takeSingleKeptItemProgram (.resolve "T")) with
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard takeSingleKeptItemIsExactListValue

def takeSingleKeptItemCount : Bool :=
  match runResult (takeSingleKeptItemProgram
      (.call (resolve "count") [.resolve "T"])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard takeSingleKeptItemCount

def takeSingleKeptItemDotCount : Bool :=
  match runResult (takeSingleKeptItemProgram (.dotCall (.resolve "T") "count" none)) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard takeSingleKeptItemDotCount

def takeSingleKeptItemEqualsListLiteral : Bool :=
  match runResult (takeSingleKeptItemProgram
      (.binary .eq (.resolve "T") (.listLiteral [sequenceItems [.num 1, .num 2]]))) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard takeSingleKeptItemEqualsListLiteral

def takeSingleKeptItemNotEqualFlatLiteral : Bool :=
  match runResult (takeSingleKeptItemProgram
      (.binary .eq (.resolve "T") (sequenceItems [.num 1, .num 2]))) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard takeSingleKeptItemNotEqualFlatLiteral

def takeSingleKeptItemNotEqualWrappedLiteral : Bool :=
  match runResult (takeSingleKeptItemProgram
      (.binary .eq (.resolve "T")
        (.capture [sequenceItems [.num 1, .num 2]]))) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard takeSingleKeptItemNotEqualWrappedLiteral

-- A single kept empty-sequence item stays one exact list element:
-- `distinct(((), ()))` dedups the two equal `()` items of the one grouped
-- collection argument to one kept item and yields the exact list `[()]`
-- (count 1) — never erased to `()` itself. The ungrouped spelling
-- `distinct((), ())` is a two-argument arity error under `distinct(collection)`.
def distinctSingleKeptEmptyItemStaysExactElement : Bool :=
  match runResult (.call (resolve "distinct") [.capture [.emptySequence 0, .emptySequence 0]]) with
  | Except.ok (.listValue [.sequenceValue []]) => true
  | _ => false

#guard distinctSingleKeptEmptyItemStaysExactElement

def distinctTwoEmptyArgumentsIsArityError : Bool :=
  match runResult (.call (resolve "distinct") [.emptySequence 0, .emptySequence 0]) with
  | Except.error err => innermostIsArityMismatch 1 2 err
  | _ => false

#guard distinctTwoEmptyArgumentsIsArityError

def distinctSingleKeptEmptyItemCountsOne : Bool :=
  match runResult (.call (resolve "count") [
    .call (resolve "distinct") [.capture [.emptySequence 0, .emptySequence 0]]
  ]) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard distinctSingleKeptEmptyItemCountsOne

def distinctSingleKeptEmptyItemNotEqualEmpty : Bool :=
  match runResult (.binary .eq
      (.call (resolve "distinct") [.capture [.emptySequence 0, .emptySequence 0]])
      (.emptySequence 0)) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard distinctSingleKeptEmptyItemNotEqualEmpty

-- Multiple kept empty-sequence items keep their sibling boundaries as exact list
-- elements. `take(((), ()), 2)` is the two-element list `[(), ()]` with count 2 —
-- the materializer is exact and never collapses or drops meaningful sibling items.
def takeMultipleEmptyItemsPreservesSiblingBoundaries : Bool :=
  match runResult (.call (resolve "take") [.capture [.emptySequence 0, .emptySequence 0], .num 2]) with
  | Except.ok (.listValue [.sequenceValue [], .sequenceValue []]) => true
  | _ => false

#guard takeMultipleEmptyItemsPreservesSiblingBoundaries

def takeMultipleEmptyItemsCountsTwo : Bool :=
  match runResult (.call (resolve "count") [
    .call (resolve "take") [.capture [.emptySequence 0, .emptySequence 0], .num 2]
  ]) with
  | Except.ok (.atom 2) => true
  | _ => false

#guard takeMultipleEmptyItemsCountsTwo

-- The collection-result materializer is EXACT, unlike the canonical arity
-- combiners: zero items form `[]`, one item forms `[item]` (never erased),
-- nested structure is preserved raw, and the emitted count is always 1.
#guard KatLang.makeCollectionListResult [] == (Result.listValue [], 1)
#guard KatLang.makeCollectionListResult [.atom 7] == (Result.listValue [.atom 7], 1)
#guard KatLang.makeCollectionListResult [.str "a"] == (Result.listValue [.str "a"], 1)
#guard KatLang.makeCollectionListResult [.sequenceValue [.atom 1, .atom 2]]
  == (Result.listValue [.sequenceValue [.atom 1, .atom 2]], 1)
#guard KatLang.makeCollectionListResult [.sequenceValue []]
  == (Result.listValue [.sequenceValue []], 1)
#guard KatLang.makeCollectionListResult [.sequenceValue [], .sequenceValue []]
  == (Result.listValue [.sequenceValue [], .sequenceValue []], 1)
#guard KatLang.makeCollectionListResult [.listValue [.atom 1]]
  == (Result.listValue [.listValue [.atom 1]], 1)

def test188 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2, .num 3]
    ])
  ] [
    .call (resolve "take") [
      .resolve "Values",
      .num 1
    ]
  ])) with
  | Except.ok (.listValue [.atom 1]) => true
  | _ => false

#guard test188

def test189 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .call (resolve "take") [
      .resolve "Values",
      .num 1
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test189

def test190 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2, .num 3]
    ])
  ] [
    .call (resolve "skip") [
      .resolve "Values",
      .num 1
    ]
  ])) with
  | Except.ok [2, 3] => true
  | _ => false

#guard test190

def test191 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .call (resolve "skip") [
      .resolve "Values",
      .num 1
    ]
  ])) with
  | Except.ok [2, 3] => true
  | _ => false

#guard test191

def test192 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "take") [
      sequenceItems [.num 1, .num 2],
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "take count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#guard test192

def test193 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [
      sequenceItems [.num 3, .num 4],
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.error err => hasContext "take count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#guard test193

def test194 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 1, .num 2],
      .stringLiteral "hello"
    ]
  ])) with
  | Except.error err => hasContext "skip count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#guard test194

def test195 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 3, .num 4, .num 1],
      .num 2
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test195

def test196 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "distinct") [sequenceItems [
      .num 3,
      .num 1,
      .num 3,
      .num 2,
      .num 1,
      .num 2]
    ]
  ])) with
  | Except.ok [3, 1, 2] => true
  | _ => false

#guard test196

def test197 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "distinct") [sequenceItems [
      .num 4,
      .num 4,
      .num 4,
      .num 4]
    ]
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test197

def test198 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "distinct") [sequenceItems [
      .num 1,
      .num 2,
      .num 3]
    ]
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test198

def test199 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "distinct") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test199

def test200 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "distinct") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]]
    ]
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 1, .atom 2],
      .sequenceValue [.atom 3, .atom 4]
    ]) => true
  | _ => false

#guard test200

def test201 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ]
    ])
  ] [
    .call (resolve "distinct") [
      .resolve "Values"
    ]
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 1, .atom 2],
      .sequenceValue [.atom 3, .atom 4]
    ]) => true
  | _ => false

#guard test201

def test202 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .call (resolve "distinct") [
      .resolve "Values"
    ]
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 1, .atom 2],
      .sequenceValue [.atom 3, .atom 4]
    ]) => true
  | _ => false

#guard test202

def test203 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ]) "order" none) with
  | Except.ok [3, 3, 3, 5, 6] => true
  | _ => false

#guard test203

def test204 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ]) "orderDesc" none) with
  | Except.ok [6, 5, 3, 3, 3] => true
  | _ => false

#guard test204

def test205 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ]) "count" none) with
  | Except.ok [5] => true
  | _ => false

#guard test205

def test206 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 3,
    .num 5,
    .num 3
  ]) "sum" none) with
  | Except.ok [11] => true
  | _ => false

#guard test206

def test207 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 1,
    .num 2,
    .num 1,
    .num 3
  ]) "distinct" none) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test207

def test208 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 1,
    .num 2,
    .num 3
  ]) "take" (some [.num 2])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard test208

def test209 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 1,
    .num 2,
    .num 3
  ]) "skip" (some [.num 1])) with
  | Except.ok [2, 3] => true
  | _ => false

#guard test209

def test210 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Double", doubleAlg85)] [
    .dotCall (.capture [
      .num 1,
      .num 2,
      .num 3
    ]) "map" (some [.resolve "Double"])
  ])) with
  | Except.ok [2, 4, 6] => true
  | _ => false

#guard test210

def test211 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall (.capture [
      .num 1,
      .num 2,
      .num 3,
      .num 4
    ]) "filter" (some [.resolve "IsEven"])
  ])) with
  | Except.ok [2, 4] => true
  | _ => false

#guard test211

def test212 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Add", addAlg76)] [
    .dotCall (.capture [
      .num 1,
      .num 2,
      .num 3
    ]) "reduce" (some [
      .resolve "Add",
      .num 0
    ])
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test212

def test213 : Bool :=
  match runFlat (.dotCall (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 3, .num 1, .num 2])
  ] [
    .resolve "Values"
  ])) "order" none) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test213

def test214 : Bool :=
  let inlineReceiver := .capture [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ]
  let sequenceValueReceiver := .capture [inlineReceiver]
  let namedSequenceValueWorks :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("Data", alg [] [] [] [inlineReceiver])
    ] [
      .dotCall (.resolve "Data") "order" none
    ])) with
    | Except.ok [3, 3, 3, 5, 6] => true
    | _ => false
  let inlineReceiverWorks :=
    match runFlat (.dotCall inlineReceiver "order" none) with
    | Except.ok [3, 3, 3, 5, 6] => true
    | _ => false
  let doubleParenReceiverWorks :=
    match runFlat (.dotCall sequenceValueReceiver "order" none) with
    | Except.ok [3, 3, 3, 5, 6] => true
    | _ => false
  namedSequenceValueWorks && inlineReceiverWorks && doubleParenReceiverWorks

#guard test214

def test215 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Data", alg [] [] [] [
      .capture [.num 7, .num 6, .num 4, .num 2, .num 1],
      .capture [.num 1, .num 2, .num 3, .num 4, .num 5]
    ])
  ] [
    .call (resolve "count") [.index (.resolve "Data") (.num 0)],
    .dotCall (.index (.resolve "Data") (.num 0)) "count" none
    , .call (resolve "order") [.index (.resolve "Data") (.num 0)]
    , .dotCall (.index (.resolve "Data") (.num 0)) "order" none
  ])) with
  | Except.ok [5, 5, 1, 2, 4, 6, 7, 1, 2, 4, 6, 7] => true
  | _ => false

#guard test215

def test215a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 7, .num 8])
  ] [
    .index (.resolve "A") (.num 0)
  ])) with
  | Except.ok (.atom 7) => true
  | _ => false

#guard test215a

def test215b : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .index (.resolve "A") (.num 0)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard test215b

def test215c : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .call (resolve "count") [.index (.resolve "A") (.num 0)],
    .dotCall (.index (.resolve "A") (.num 0)) "count" none
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test215c

def test215cWrappedProjectionBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]),
    ("Projected", alg [] [] [] [
      .index (.resolve "A") (.num 0)
    ])
  ] [
    .call (resolve "count") [.index (.resolve "A") (.num 0)],
    .call (resolve "count") [.resolve "Projected"]
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test215cWrappedProjectionBoundary

def test215d : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ],
      .capture [
        .capture [.num 5, .num 6],
        .capture [.num 7, .num 8]
      ]
    ])
  ] [
    .index (.resolve "A") (.num 0)
  ])) with
  | Except.ok (.sequenceValue [
      .sequenceValue [.atom 1, .atom 2],
      .sequenceValue [.atom 3, .atom 4]
    ]) => true
  | _ => false

#guard test215d

def test215e : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ],
      .capture [
        .capture [.num 5, .num 6],
        .capture [.num 7, .num 8]
      ]
    ])
  ] [
    .index (.index (.resolve "A") (.num 0)) (.num 1)
  ])) with
  | Except.ok (.sequenceValue [.atom 3, .atom 4]) => true
  | _ => false

#guard test215e

def test215f : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ],
      .capture [
        .capture [.num 5, .num 6],
        .capture [.num 7, .num 8]
      ]
    ])
  ] [
    .call (resolve "count") [.index (.resolve "A") (.num 0)],
    .call (resolve "count") [.index (.index (.resolve "A") (.num 0)) (.num 1)]
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test215f

def test215g : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ],
      .capture [
        .capture [.num 5, .num 6],
        .capture [.num 7, .num 8]
      ]
    ])
  ] [
    .call (resolve "sum") [.index (.resolve "A") (.num 0)]
  ])) with
  | Except.error err =>
      hasContext "sum expects each collection element to be a single numeric value; item 0 was sequence value" err
        && innermostIsBadArity err
  | _ => false

#guard test215g

def test216 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 4, .num 5, .num 4, .num 6]
    ])
  ] [
    .dotCall (.resolve "Values") "first" none,
    .dotCall (.resolve "Values") "last" none,
    .dotCall (.resolve "Values") "distinct" none,
    .dotCall (.resolve "Values") "take" (some [.num 2]),
    .dotCall (.resolve "Values") "skip" (some [.num 1])
  ])) with
  | Except.ok (.sequenceValue [
      .atom 4,
      .atom 6,
      .listValue [.atom 4, .atom 5, .atom 6],
      .listValue [.atom 4, .atom 5],
      .listValue [.atom 5, .atom 4, .atom 6]
    ]) => true
  | _ => false

#guard test216

def test217 : Bool :=
  let runBuiltin := fun (name : String) =>
    runResult (.algorithmExpr (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .capture [.num 10, .num 20, .num 30]
      ])
    ] [
      .dotCall (.resolve "Values") name none
    ]))
  let minWorks :=
    match runBuiltin "min" with
    | Except.ok (.atom 10) => true
    | _ => false
  let maxWorks :=
    match runBuiltin "max" with
    | Except.ok (.atom 30) => true
    | _ => false
  let sumWorks :=
    match runBuiltin "sum" with
    | Except.ok (.atom 60) => true
    | _ => false
  let avgWorks :=
    match runBuiltin "avg" with
    | Except.ok (.atom 20) => true
    | _ => false
  let orderWorks :=
    match runBuiltin "order" with
    | Except.ok (.listValue [.atom 10, .atom 20, .atom 30]) => true
    | _ => false
  let orderDescWorks :=
    match runBuiltin "orderDesc" with
    | Except.ok (.listValue [.atom 30, .atom 20, .atom 10]) => true
    | _ => false
  minWorks && maxWorks && sumWorks && avgWorks && orderWorks && orderDescWorks

#guard test217

def test218 : Bool :=
  let keepSecondEven : Algorithm :=
    alg ["pair"] [] [] [
      .binary .eq
        (.binary .mod (.index (.param "pair") (.num 1)) (.num 2))
        (.num 0)
    ]
  let takeFirstAlg : Algorithm :=
    alg ["x"] [] [] [
      .index (.param "x") (.num 0)
    ]
  let addItemCount : Algorithm :=
    alg ["item", "acc"] [] [] [
      .binary .add
        (.dotCall (.param "item") "count" none)
        (.param "acc")
    ]
  let filterResult :=
    runResult (.algorithmExpr (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .capture [.num 1, .num 2],
        .capture [.num 1, .num 3]
      ]),
      ("KeepSecondEven", keepSecondEven)
    ] [
      .dotCall (.resolve "Values") "filter" (some [.resolve "KeepSecondEven"])
    ]))
  let mapResult :=
    runResult (.algorithmExpr (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .capture [.num 1, .num 2, .num 3],
        .capture [.num 4, .num 5, .num 6]
      ]),
      ("TakeFirst", takeFirstAlg)
    ] [
      .dotCall (.resolve "Values") "map" (some [.resolve "TakeFirst"])
    ]))
  let reduceResult :=
    runFlat (.algorithmExpr (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .capture [.num 1, .num 2, .num 3],
        .capture [.num 4, .num 5, .num 6]
      ]),
      ("AddItemCount", addItemCount)
    ] [
      .dotCall (.resolve "Values") "reduce" (some [.resolve "AddItemCount", .num 0])
    ]))
  let filterOk :=
    match filterResult with
    -- Filtering keeps one sequence-valued item; the exact-list result keeps it
    -- as one element, so the result is `[(1, 2)]`.
    | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
    | _ => false
  let mapOk :=
    match mapResult with
    | Except.ok (.listValue [.atom 1, .atom 4]) => true
    | _ => false
  let reduceOk :=
    match reduceResult with
    | Except.ok [6] => true
    | _ => false
  filterOk && mapOk && reduceOk

#guard test218

def test219 : Bool :=
  match runResult (.dotCall (.capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]) "sum" none) with
  | Except.error err =>
      hasContext "sum expects each collection element to be a single numeric value; item 0 was sequence value" err
        && innermostIsBadArity err
  | _ => false

#guard test219

--------------------------------------------------------------------------------
-- Sequence-boundary cleanup regressions
--------------------------------------------------------------------------------

def test228 : Bool :=
  match runFlat (.call (resolve "count") [
    sequenceItems [.num 3, .num 4, sequenceSpread (.call (resolve "range") [.num 1, .num 5]), .num 7]
  ]) with
  | Except.ok [8] => true
  | _ => false

#guard test228

def test229 : Bool :=
  let sequenceValueRange := .capture [.num 1, .num 2, .num 3, .num 4, .num 5]
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "contains") [
      sequenceItems [.num 3, .num 4, sequenceSpread (.call (resolve "range") [.num 1, .num 5]), .num 7],
      .num 5
    ],
    .call (resolve "contains") [
      sequenceItems [.num 3, .num 4, sequenceSpread (.call (resolve "range") [.num 1, .num 5]), .num 7],
      sequenceValueRange
    ]
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard test229

def test230 : Bool :=
  match runFlat (.call (resolve "order") [
    sequenceItems [.num 3, .num 4, sequenceSpread (.call (resolve "range") [.num 1, .num 5]), .num 7]
  ]) with
  | Except.ok [1, 2, 3, 3, 4, 4, 5, 7] => true
  | _ => false

#guard test230

    def test231 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Data", alg [] [] [] [
      .capture [.num 7, .num 6, .num 4, .num 2, .num 1],
      .capture [.num 1, .num 2, .num 3, .num 4, .num 5]
    ])
  ] [
    .call (resolve "count") [
      .index (.resolve "Data") (.num 0)
    ],
    .dotCall (.index (.resolve "Data") (.num 0)) "count" none,
    .call (resolve "order") [
      .index (.resolve "Data") (.num 0)
    ],
    .dotCall (.index (.resolve "Data") (.num 0)) "order" none
  ])) with
  | Except.ok [5, 5, 1, 2, 4, 6, 7, 1, 2, 4, 6, 7] => true
  | _ => false

#guard test231

def test232 : Bool :=
  let firstReport := .capture [.num 7, .num 6, .num 4, .num 2, .num 1]
  let secondReport := .capture [.num 1, .num 2, .num 7, .num 8, .num 9]
  let safeReportProjected : Algorithm :=
    let report := .param "report"
    let itemAt (i : Int) := .index report (.num i)
    let desc (i : Int) := .binary .gt (itemAt i) (itemAt (i + 1))
    let stepOk (i : Int) := .binary .le (.binary .sub (itemAt i) (itemAt (i + 1))) (.num 3)
    let descendingChecks :=
      .binary .and
        (desc 0)
        (.binary .and
          (desc 1)
          (.binary .and (desc 2) (desc 3)))
    let stepChecks :=
      .binary .and
        (stepOk 0)
        (.binary .and
          (stepOk 1)
          (.binary .and (stepOk 2) (stepOk 3)))
    alg ["report"] [] [] [
      .binary .and descendingChecks stepChecks
    ]
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("IsSafe", safeReportProjected)
  ] [
    .call (resolve "filter") [
      sequenceItems [firstReport, secondReport],
      .resolve "IsSafe"
    ]
  ])) with
  -- Only the first report is kept; the exact-list result keeps it as one element,
  -- so the result is `[(7, 6, 4, 2, 1)]`.
  | Except.ok (.listValue [.sequenceValue [.atom 7, .atom 6, .atom 4, .atom 2, .atom 1]]) => true
  | _ => false

#guard test232

def test233 : Bool :=
  let takeFirstProjected : Algorithm :=
    alg ["report"] [] [] [
      .index (.param "report") (.num 0)
    ]
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("TakeFirst", takeFirstProjected)
  ] [
    .call (resolve "map") [
      sequenceItems [
        .capture [.num 7, .num 6, .num 4, .num 2, .num 1],
        .capture [.num 1, .num 2, .num 7, .num 8, .num 9]],
      .resolve "TakeFirst"
    ]
  ])) with
  | Except.ok [7, 1] => true
  | _ => false

#guard test233

def test234 : Bool :=
  let countItem : Algorithm :=
    alg ["x"] [] [] [
      .dotCall (.param "x") "count" none
    ]
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Items", alg [] [] [] [
      .capture [.num 1, .num 2, .num 3],
      .capture [.num 7, .num 8, .num 9]
    ]),
    ("CountItem", countItem)
  ] [
    .dotCall (.resolve "Items") "count" none,
    .dotCall (.index (.resolve "Items") (.num 0)) "count" none,
    .dotCall (.index (.resolve "Items") (.num 1)) "count" none,
    .dotCall (.resolve "Items") "map" (some [.resolve "CountItem"])
  ])) with
  | Except.ok [2, 3, 3, 3, 3] => true
  | _ => false

#guard test234

def test235 : Bool :=
  let takeFirstProjected : Algorithm :=
    alg ["x"] [] [] [
      .index (.param "x") (.num 0)
    ]
  let hasThreeItems : Algorithm :=
    alg ["x"] [] [] [
      .binary .eq
        (.dotCall (.param "x") "count" none)
        (.num 3)
    ]
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Items", alg [] [] [] [
      .capture [.num 1, .num 2, .num 3],
      .capture [.num 7, .num 8, .num 9]
    ]),
    ("TakeFirst", takeFirstProjected),
    ("HasThreeItems", hasThreeItems)
  ] [
    .dotCall (.resolve "Items") "map" (some [.resolve "TakeFirst"]),
    .dotCall
      (.dotCall (.resolve "Items") "filter" (some [.resolve "HasThreeItems"]))
      "count"
      none
  ])) with
  | Except.ok [1, 7, 2] => true
  | _ => false

#guard test235

--------------------------------------------------------------------------------
-- Focused reduce callback projection regressions
--------------------------------------------------------------------------------

def reduceCurrentSelectionSignatureAlg236 : Algorithm :=
  alg ["current", "acc"] [] [] [
    .binary .add
      (.binary .mul (.param "acc") (.num 100))
      (.binary .add
        (.binary .mul (.dotCall (.param "current") "count" none) (.num 10))
        (.dotCall (.param "current") "sum" none))
  ]

def reduceCurrentOneLevelSignatureAlg237 : Algorithm :=
  alg ["current", "acc"] [] [] [
    .binary .add
      (.binary .mul (.param "acc") (.num 100))
      (.binary .add
        (.binary .mul (.dotCall (.param "current") "count" none) (.num 10))
        (.dotCall (.index (.param "current") (.num 0)) "count" none))
  ]

def reduceAccumulatorAsymmetryAlg238 : Algorithm :=
  alg ["current", "acc"] [] [] [
    .capture [
      .binary .add
        (.binary .mul (.index (.param "acc") (.num 0)) (.num 100))
        (.binary .add
          (.binary .mul (.dotCall (.param "current") "count" none) (.num 10))
          (.dotCall (.param "acc") "count" none)),
      .dotCall (.param "acc") "count" none
    ]
  ]

def test236 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Signature", reduceCurrentSelectionSignatureAlg236),
    ("Items", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .dotCall (.index (.resolve "Items") (.num 0)) "count" none,
    .dotCall (.index (.resolve "Items") (.num 0)) "sum" none,
    .dotCall (.index (.resolve "Items") (.num 1)) "count" none,
    .dotCall (.index (.resolve "Items") (.num 1)) "sum" none,
    .dotCall (.resolve "Items") "reduce" (some [.resolve "Signature", .num 0]),
    .call (.resolve "reduce") [
      sequenceItems [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]],
      .resolve "Signature",
      .num 0
    ]
  ])) with
  | Except.ok [2, 3, 2, 7, 2327, 2327] => true
  | _ => false

#guard test236

def test237 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Signature", reduceCurrentOneLevelSignatureAlg237),
    ("Items", alg [] [] [] [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ]
    ])
  ] [
    .dotCall (.index (.resolve "Items") (.num 0)) "count" none,
    .dotCall (.resolve "Items") "reduce" (some [.resolve "Signature", .num 0]),
    .call (.resolve "reduce") [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ],
      .resolve "Signature",
      .num 0
    ]
  ])) with
  | Except.ok [2, 2121, 2121] => true
  | _ => false

#guard test237

def test238 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Signature", reduceAccumulatorAsymmetryAlg238),
    ("Items", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .dotCall (.resolve "Items") "reduce" (some [
      .resolve "Signature",
      .capture [.num 0, .num 9, .num 8]
    ])
  ])) with
  | Except.ok (.sequenceValue [.atom 2322, .atom 2]) => true
  | _ => false

#guard test238

def reduceVariadicAppendAlg239 : Algorithm :=
  algWithParameters [{ name := "item" }, { name := "history", kind := .collecting }] [] [] [
    .capture [.sequenceConstruct (sequenceSpread (.param "history")) (.param "item")]
  ]

def reduceScalarSumAlg241 : Algorithm :=
  alg ["item", "total"] [] [] [
    .binary .add (.param "total") (.param "item")
  ]

def reduceStructuralAppendAlg242 : Algorithm :=
  alg ["item", "history"] [] [] [
    .capture [.sequenceConstruct (sequenceSpread (.param "history")) (.param "item")]
  ]

def reduceVariadicAccumulatorStateFlattens : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Append", reduceVariadicAppendAlg239)] [
    .call (resolve "reduce") [
      sequenceItems [.num 2, .num 3, .num 4],
      .resolve "Append",
      .num 1
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3, .atom 4]) => true
  | _ => false

#guard reduceVariadicAccumulatorStateFlattens

def reduceScalarReducerBehaviorRemainsUnchanged : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Sum", reduceScalarSumAlg241)] [
    .call (resolve "reduce") [
      sequenceItems [.num 2, .num 3, .num 4],
      .resolve "Sum",
      .num 1
    ]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard reduceScalarReducerBehaviorRemainsUnchanged

def reduceNonVariadicAccumulatorPreservesStructuralAccumulator : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Append", reduceStructuralAppendAlg242)] [
    .call (resolve "reduce") [
      sequenceItems [.num 2, .num 3, .num 4],
      .resolve "Append",
      .num 1
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3, .atom 4]) => true
  | _ => false

#guard reduceNonVariadicAccumulatorPreservesStructuralAccumulator

--------------------------------------------------------------------------------
-- Sequence builtin dot-call regression sweep
--------------------------------------------------------------------------------

private def dotSweepAtomsAlg (xs : List Int) : Algorithm :=
  alg [] [] [] (xs.map (fun value => .num value))

private def dotSweepSequenceValueExpr (xs : List Int) : KatLang.Expr :=
  KatLang.algorithmExpr (dotSweepAtomsAlg xs)

private def dotSweepSequenceValueAlg (xs : List Int) : Algorithm :=
  alg [] [] [] [dotSweepSequenceValueExpr xs]

private def dotSweepPairAlg (first second : List Int) : Algorithm :=
  alg [] [] [] [dotSweepSequenceValueExpr first, dotSweepSequenceValueExpr second]

private def dotSweepTopLevelItemCountAlg : Algorithm :=
  alg ["x"] [] [] [.dotCall (.param "x") "count" none]

private def dotSweepKeepCountThreeAlg : Algorithm :=
  alg ["x"] [] [] [
    .binary .eq (.dotCall (.param "x") "count" none) (.num 3)
  ]

private def dotSweepAddTopLevelItemCountAlg : Algorithm :=
  alg ["item", "acc"] [] [] [
    .binary .add (.dotCall (.param "item") "count" none) (.param "acc")
  ]

private def dotSweepAddOneAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

private def dotSweepIsGreaterThanOneAlg : Algorithm :=
  alg ["x"] [] [] [.binary .gt (.param "x") (.num 1)]

private def dotSweepAddAlg : Algorithm :=
  alg ["x", "total"] [] [] [.binary .add (.param "x") (.param "total")]

def sequenceBuiltinDotCallCountSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [1, 2, 3]),
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [3, 1, 2] [9, 8, 7])
  ] [
    .dotCall (resolve "Values") "count" none,
    .call (resolve "count") [resolve "Values"],
    .dotCall (resolve "SequenceValue") "count" none,
    .call (resolve "count") [resolve "SequenceValue"],
    .dotCall data0 "count" none,
    .call (resolve "count") [data0]
  ])) with
  | Except.ok [3, 3, 3, 3, 3, 3] => true
  | _ => false

#guard sequenceBuiltinDotCallCountSweep

def sequenceBuiltinDotCallContainsSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [1, 2, 3]),
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [3, 1, 2] [9, 8, 7])
  ] [
    .dotCall (resolve "Values") "contains" (some [.num 2]),
    .call (resolve "contains") [resolve "Values", .num 2],
    .dotCall (resolve "SequenceValue") "contains" (some [.num 2]),
    .dotCall (resolve "SequenceValue") "contains" (some [dotSweepSequenceValueExpr [1, 2, 3]]),
    .dotCall data0 "contains" (some [.num 2]),
    .call (resolve "contains") [data0, .num 2]
  ])) with
  | Except.ok [1, 1, 1, 0, 1, 1] => true
  | _ => false

#guard sequenceBuiltinDotCallContainsSweep

def sequenceBuiltinDotCallOrderSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [3, 1, 2]),
    ("Data", dotSweepPairAlg [3, 1, 2] [9, 8, 7])
  ] [
    .dotCall (resolve "Values") "order" none,
    .dotCall (resolve "Values") "orderDesc" none,
    .dotCall data0 "order" none,
    .call (resolve "order") [data0],
    .dotCall data0 "orderDesc" none,
    .call (resolve "orderDesc") [data0]
  ])) with
  | Except.ok [1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 3, 2, 1] => true
  | _ => false

#guard sequenceBuiltinDotCallOrderSweep

def sequenceBuiltinDotCallOrderBoundarySweep : Bool :=
  let orderValues :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [3, 1, 2])
    ] [
      .call (resolve "order") [resolve "Values"]
    ])) with
    | Except.ok [1, 2, 3] => true
    | _ => false
  let orderDescValues :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [3, 1, 2])
    ] [
      .call (resolve "orderDesc") [resolve "Values"]
    ])) with
    | Except.ok [3, 2, 1] => true
    | _ => false
  let sequenceValueOrder :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [3, 1, 2])
    ] [
      .dotCall (resolve "SequenceValue") "order" none
    ])) with
    | Except.ok [1, 2, 3] => true
    | _ => false
  let sequenceValueOrderDesc :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [3, 1, 2])
    ] [
      .dotCall (resolve "SequenceValue") "orderDesc" none
    ])) with
    | Except.ok [3, 2, 1] => true
    | _ => false
  orderValues && orderDescValues && sequenceValueOrder && sequenceValueOrderDesc

#guard sequenceBuiltinDotCallOrderBoundarySweep

def sequenceBuiltinDotCallFirstLastSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [5, 6, 7]),
    ("Data", dotSweepPairAlg [9, 8, 7] [3, 2, 1])
  ] [
    .dotCall (resolve "Values") "first" none,
    .dotCall (resolve "Values") "last" none,
    .dotCall data0 "first" none,
    .call (resolve "first") [data0],
    .dotCall data0 "last" none,
    .call (resolve "last") [data0]
  ])) with
  | Except.ok [5, 7, 9, 9, 7, 7] => true
  | _ => false

#guard sequenceBuiltinDotCallFirstLastSweep

def sequenceBuiltinDotCallFirstLastSequenceValueSweep : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("SequenceValue", dotSweepSequenceValueAlg [5, 6, 7])
  ] [
    .dotCall (resolve "SequenceValue") "first" none,
    .call (resolve "first") [resolve "SequenceValue"],
    .dotCall (resolve "SequenceValue") "last" none,
    .call (resolve "last") [resolve "SequenceValue"]
  ])) with
  | Except.ok (.sequenceValue [
      .atom 5,
      .atom 5,
      .atom 7,
      .atom 7
    ]) => true
  | _ => false

#guard sequenceBuiltinDotCallFirstLastSequenceValueSweep

def sequenceBuiltinDotCallDistinctSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [1, 2, 1, 3]),
    ("Data", dotSweepPairAlg [1, 2, 1, 3] [9, 8, 9])
  ] [
    .dotCall (resolve "Values") "distinct" none,
    .dotCall data0 "distinct" none,
    .call (resolve "distinct") [data0]
  ])) with
  | Except.ok [1, 2, 3, 1, 2, 3, 1, 2, 3] => true
  | _ => false

#guard sequenceBuiltinDotCallDistinctSweep

def sequenceBuiltinDotCallDistinctSequenceValueSweep : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 1, 3])
  ] [
    .dotCall (resolve "SequenceValue") "distinct" none,
    .call (resolve "distinct") [resolve "SequenceValue"]
  ])) with
  | Except.ok (.sequenceValue [
      .listValue [.atom 1, .atom 2, .atom 3],
      .listValue [.atom 1, .atom 2, .atom 3]
    ]) => true
  | _ => false

#guard sequenceBuiltinDotCallDistinctSequenceValueSweep

def sequenceBuiltinDotCallTakeSkipSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [7, 6, 4, 2, 1] [1, 2, 3, 4, 5])
  ] [
    .dotCall (resolve "Values") "take" (some [.num 2]),
    .call (resolve "take") [resolve "Values", .num 2],
    .dotCall (resolve "Values") "skip" (some [.num 1]),
    .call (resolve "skip") [resolve "Values", .num 1],
    .dotCall data0 "take" (some [.num 2]),
    .call (resolve "take") [data0, .num 2],
    .dotCall data0 "skip" (some [.num 2]),
    .call (resolve "skip") [data0, .num 2]
  ])) with
  | Except.ok [1, 2, 1, 2, 2, 3, 2, 3, 7, 6, 7, 6, 4, 2, 1, 4, 2, 1] => true
  | _ => false

#guard sequenceBuiltinDotCallTakeSkipSweep

def sequenceBuiltinDotCallTakeSkipSequenceValueSweep : Bool :=
  let takeOk :=
    match runResult (.algorithmExpr (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "SequenceValue") "take" (some [.num 2]),
      .call (resolve "take") [resolve "SequenceValue", .num 2]
    ])) with
    | Except.ok (.sequenceValue [
        .listValue [.atom 1, .atom 2],
        .listValue [.atom 1, .atom 2]
      ]) => true
    | _ => false
  let skipDotOk :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "SequenceValue") "skip" (some [.num 1])
    ])) with
    | Except.ok [2, 3] => true
    | _ => false
  let skipPlainOk :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .call (resolve "skip") [resolve "SequenceValue", .num 1]
    ])) with
    | Except.ok [2, 3] => true
    | _ => false
  takeOk && skipDotOk && skipPlainOk

#guard sequenceBuiltinDotCallTakeSkipSequenceValueSweep

def sequenceBuiltinDotCallNamedReceiverBoundarySweep : Bool :=
  let namedMulti :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("A", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .dotCall (resolve "A") "take" (some [.num 2]),
      .dotCall (resolve "A") "count" none
    ])) with
    | Except.ok [1, 2, 3] => true
    | _ => false
  let namedSequenceValue :=
    match runResult (.algorithmExpr (algPrivate [] [] [
      ("A", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "A") "take" (some [.num 2]),
      .dotCall (resolve "A") "count" none
    ])) with
    | Except.ok (.sequenceValue [.listValue [.atom 1, .atom 2], .atom 3]) => true
    | _ => false
  let spread :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("A", alg [] [] [] [sequenceSpread (.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3))])
    ] [
      .dotCall (resolve "A") "take" (some [.num 2])
    ])) with
    | Except.ok [1, 2] => true
    | _ => false
  namedMulti && namedSequenceValue && spread

#guard sequenceBuiltinDotCallNamedReceiverBoundarySweep

def sequenceBuiltinDotCallUserAndConditionalReceiverBoundarySweep : Bool :=
  let userCall :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("F", alg ["x"] [] [] [.param "x", .binary .add (.param "x") (.num 1), .binary .add (.param "x") (.num 2)]),
      ("G", alg ["x"] [] [] [.capture [.param "x", .binary .add (.param "x") (.num 1), .binary .add (.param "x") (.num 2)]])
    ] [
      .dotCall (.call (resolve "F") [.num 1]) "count" none,
      .dotCall (.call (resolve "F") [.num 1]) "take" (some [.num 2]),
      .dotCall (.call (resolve "G") [.num 1]) "count" none
    ])) with
    | Except.ok [3, 1, 2, 3] => true
    | _ => false
  let conditional :=
    let chooseMulti : Algorithm :=
      .conditional none [] [
        { pattern := KatLang.Pattern.litInt 1, body := alg [] [] [] [.num 1, .num 2, .num 3] },
        { pattern := KatLang.Pattern.bind "x", body := alg [] [] [] [.num 4, .num 5, .num 6] }
      ]
    let chooseSequenceValue : Algorithm :=
      .conditional none [] [
        { pattern := KatLang.Pattern.litInt 1, body := alg [] [] [] [.capture [.num 1, .num 2, .num 3]] },
        { pattern := KatLang.Pattern.bind "x", body := alg [] [] [] [.capture [.num 4, .num 5, .num 6]] }
      ]
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("ChooseMulti", chooseMulti),
      ("ChooseSequenceValue", chooseSequenceValue)
    ] [
      .dotCall (.call (resolve "ChooseMulti") [.num 1]) "take" (some [.num 2]),
      .dotCall (.call (resolve "ChooseSequenceValue") [.num 1]) "count" none
    ])) with
    | Except.ok [1, 2, 3] => true
    | _ => false
  userCall && conditional

#guard sequenceBuiltinDotCallUserAndConditionalReceiverBoundarySweep

def sequenceBuiltinDotCallInlineReceiverSweep : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("AddOne", dotSweepAddOneAlg),
    ("IsLarge", dotSweepIsGreaterThanOneAlg),
    ("Add", dotSweepAddAlg)
  ] [
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "count" none,
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "contains" (some [.num 2]),
    .dotCall (dotSweepSequenceValueExpr [3, 1, 2]) "order" none,
    .dotCall (dotSweepSequenceValueExpr [5, 6, 7]) "first" none,
    .dotCall (dotSweepSequenceValueExpr [5, 6, 7]) "last" none,
    .dotCall (dotSweepSequenceValueExpr [1, 2, 1, 3]) "distinct" none,
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "take" (some [.num 2]),
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "skip" (some [.num 1]),
    .dotCall (dotSweepSequenceValueExpr [10, 4, 7]) "min" none,
    .dotCall (dotSweepSequenceValueExpr [10, 4, 7]) "max" none,
    .dotCall (dotSweepSequenceValueExpr [3, 5, 3]) "sum" none,
    .dotCall (dotSweepSequenceValueExpr [10, 4, 7]) "avg" none,
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "map" (some [resolve "AddOne"]),
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3, 4]) "filter" (some [resolve "IsLarge"]),
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "reduce" (some [resolve "Add", .num 0])
  ])) with
  | Except.ok [3, 1, 1, 2, 3, 5, 7, 1, 2, 3, 1, 2, 2, 3, 4, 10, 11, 7, 2, 3, 4, 2, 3, 4, 6] => true
  | _ => false

#guard sequenceBuiltinDotCallInlineReceiverSweep

def sequenceBuiltinDotCallNumericAggregationSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [3, 1, 2] [9, 8, 7])
  ] [
    .dotCall (resolve "Values") "sum" none,
    .dotCall (resolve "Values") "avg" none,
    .dotCall (resolve "Values") "min" none,
    .dotCall (resolve "Values") "max" none,
    .dotCall data0 "sum" none,
    .call (resolve "sum") [data0],
    .dotCall data0 "avg" none,
    .call (resolve "avg") [data0],
    .dotCall data0 "min" none,
    .call (resolve "min") [data0],
    .dotCall data0 "max" none,
    .call (resolve "max") [data0]
  ])) with
  | Except.ok [6, 2, 1, 3, 6, 6, 2, 2, 1, 1, 3, 3] => true
  | _ => false

#guard sequenceBuiltinDotCallNumericAggregationSweep

def sequenceBuiltinDotCallNumericAggregationBoundarySweep : Bool :=
  let sumValues :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "sum") [resolve "Values"]
    ])) with
    | Except.ok [6] => true
    | _ => false
  let sumSequenceValue :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "SequenceValue") "sum" none
    ])) with
    | Except.ok [6] => true
    | _ => false
  let avgValues :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "avg") [resolve "Values"]
    ])) with
    | Except.ok [2] => true
    | _ => false
  let avgSequenceValue :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "SequenceValue") "avg" none
    ])) with
    | Except.ok [2] => true
    | _ => false
  let minValues :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "min") [resolve "Values"]
    ])) with
    | Except.ok [1] => true
    | _ => false
  let minSequenceValue :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "SequenceValue") "min" none
    ])) with
    | Except.ok [1] => true
    | _ => false
  let maxValues :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "max") [resolve "Values"]
    ])) with
    | Except.ok [3] => true
    | _ => false
  let maxSequenceValue :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "SequenceValue") "max" none
    ])) with
    | Except.ok [3] => true
    | _ => false
  sumValues && sumSequenceValue && avgValues && avgSequenceValue && minValues && minSequenceValue && maxValues && maxSequenceValue

#guard sequenceBuiltinDotCallNumericAggregationBoundarySweep

def sequenceBuiltinDotCallMapSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("ItemCount", dotSweepTopLevelItemCountAlg),
    ("AddOne", dotSweepAddOneAlg),
    ("Items", alg [] [] [] [dotSweepSequenceValueExpr [1, 2, 3], .num 7]),
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [1, 2, 3] [4, 5, 6])
  ] [
    .dotCall (resolve "Items") "map" (some [resolve "ItemCount"]),
    .call (resolve "map") [resolve "Items", resolve "ItemCount"],
    .dotCall (resolve "SequenceValue") "map" (some [resolve "ItemCount"]),
    .call (resolve "map") [resolve "SequenceValue", resolve "ItemCount"],
    .dotCall data0 "map" (some [resolve "AddOne"]),
    .call (resolve "map") [data0, resolve "AddOne"]
  ])) with
  | Except.ok [3, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 4] => true
  | _ => false

#guard sequenceBuiltinDotCallMapSweep

def sequenceBuiltinDotCallFilterSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("KeepCountThree", dotSweepKeepCountThreeAlg),
    ("IsLarge", dotSweepIsGreaterThanOneAlg),
    ("Items", alg [] [] [] [dotSweepSequenceValueExpr [1, 2, 3], dotSweepSequenceValueExpr [4, 5, 6], .num 7]),
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [1, 2, 3] [4, 5, 6])
  ] [
    .dotCall (.dotCall (resolve "Items") "filter" (some [resolve "KeepCountThree"])) "count" none,
    .dotCall (.call (resolve "filter") [resolve "Items", resolve "KeepCountThree"]) "count" none,
    .dotCall (.dotCall (resolve "SequenceValue") "filter" (some [resolve "KeepCountThree"])) "count" none,
    .dotCall (.call (resolve "filter") [resolve "SequenceValue", resolve "KeepCountThree"]) "count" none,
    .dotCall (.dotCall data0 "filter" (some [resolve "IsLarge"])) "count" none,
    .dotCall (.call (resolve "filter") [data0, resolve "IsLarge"]) "count" none
  ])) with
  | Except.ok [2, 2, 0, 0, 2, 2] => true
  | _ => false

#guard sequenceBuiltinDotCallFilterSweep

def sequenceBuiltinDotCallReduceSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("AddItemCount", dotSweepAddTopLevelItemCountAlg),
    ("Add", dotSweepAddAlg),
    ("Items", alg [] [] [] [dotSweepSequenceValueExpr [1, 2, 3], .num 7]),
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [1, 2, 3] [4, 5, 6])
  ] [
    .dotCall (resolve "Items") "reduce" (some [resolve "AddItemCount", .num 0]),
    .call (resolve "reduce") [resolve "Items", resolve "AddItemCount", .num 0],
    .dotCall (resolve "SequenceValue") "reduce" (some [resolve "AddItemCount", .num 0]),
    .call (resolve "reduce") [resolve "SequenceValue", resolve "AddItemCount", .num 0],
    .dotCall data0 "reduce" (some [resolve "Add", .num 0]),
    .call (resolve "reduce") [data0, resolve "Add", .num 0]
  ])) with
  | Except.ok [4, 4, 3, 3, 6, 6] => true
  | _ => false

#guard sequenceBuiltinDotCallReduceSweep

--------------------------------------------------------------------------------
-- collecting user-parameter tests
--------------------------------------------------------------------------------

def variadicCollectAlg : Algorithm :=
  algWithParameters [{ name := "list", kind := .collecting }] [] [] [.param "list"]

def normalCollectAlg : Algorithm :=
  alg ["list"] [] [] [.param "list"]

-- Internal sequence `(10, 20, 30)*`: spread over the constructed sequence value.
def sequenceSpread1230 : KatLang.Expr :=
  sequenceSpread (.sequenceConstruct (.sequenceConstruct (.num 10) (.num 20)) (.num 30))

def variadicSimpleRoot : Algorithm :=
  algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Collect", variadicCollectAlg)
  ] [
    .dotCall (.dotCall (resolve "Arg") "Collect" none) "count" none
  ]

-- `Arg.Collect` is `Collect(Arg)`: the receiver is ONE captured argument
-- slot, so the collecting parameter collects `list = [(1, 2, 3)]` and its count is 1.
def variadicDotCallReceiverIsOneCapturedSlot : Bool :=
  match runFlat (.algorithmExpr variadicSimpleRoot) with
  | Except.ok [1] => true
  | _ => false

#guard variadicDotCallReceiverIsOneCapturedSlot

def normalParameterStillPreservesBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Collect", normalCollectAlg)
  ] [
    .dotCall (.dotCall (resolve "Arg") "Collect" none) "count" none
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard normalParameterStillPreservesBoundary

def variadicNestedSequenceValuesRoot : Algorithm :=
  algPrivate [] [] [
    ("Arg", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]),
    ("Collect", variadicCollectAlg)
  ] [
    .dotCall (.dotCall (resolve "Arg") "Collect" none) "count" none,
    .dotCall (.call (resolve "atoms") [.dotCall (resolve "Arg") "Collect" none]) "count" none
  ]

-- The one captured receiver slot keeps its nested structure intact: `atoms`
-- still reaches all four numeric leaves through the collected list.
def variadicPreservesNestedSequenceValues : Bool :=
  match runFlat (.algorithmExpr variadicNestedSequenceValuesRoot) with
  | Except.ok [1, 4] => true
  | _ => false

#guard variadicPreservesNestedSequenceValues

def variadicScaleAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }, { name := "factor" }] [] [] [
    .dotCall (.param "values") "map" (some [
      .algorithmExpr (alg ["n"] [] [] [.binary .mul (.param "n") (.param "factor")])
    ])
  ]

def variadicTotalWithFeeAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }, { name := "fee" }] [] [] [
    .binary .add
      (.dotCall (.param "values") "sum" none)
      (.param "fee")
  ]

def variadicMeanAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .binary .div
      (.dotCall (.param "values") "sum" none)
      (.dotCall (.param "values") "count" none)
  ]

def variadicCountAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .dotCall (.param "values") "count" none
  ]

def variadicAtomsCountAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .dotCall (.call (resolve "atoms") [.param "values"]) "count" none
  ]

def ordinaryCountAlg : Algorithm :=
  alg ["list"] [] [] [
    .dotCall (.param "list") "count" none
  ]

-- Supplying a NAMED property's items to the variadic mean uses the explicit
-- spread call `Mean(Arg*)` or the grouped-spread receiver `(Arg*).Mean` (whose
-- segment supply is the spread items); both agree with the builtin sum/count
-- pipeline. (A stored receiver `Arg.Mean` supplies one item — see below.)
def variadicMeanMatchesBuiltinSumCount : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Mean", variadicMeanAlg),
    ("Direct", alg [] [] [] [
      .binary .div
        (.dotCall (resolve "Arg") "sum" none)
        (.dotCall (resolve "Arg") "count" none)
    ])
  ] [
    .call (resolve "Mean") [sequenceSpread (resolve "Arg")],
    .dotCall (.capture [sequenceSpread (resolve "Arg")]) "Mean" none,
    resolve "Direct"
  ])) with
  | Except.ok [2, 2, 2] => true
  | _ => false

#guard variadicMeanMatchesBuiltinSumCount

-- `CountViaVariadic(Arg)` and `Arg.CountViaVariadic` supply ONE argument, so
-- the collecting parameter collects `values = [Arg]` (count 1); the fixed-collection builtin
-- `Arg.count` opens the bound value (count 2); `atoms` recursively reaches
-- all four numeric leaves through the collected list.
def variadicNestedSequenceValuesAgreeWithBuiltinCountAndAtoms : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]),
    ("CountViaVariadic", variadicCountAlg),
    ("CountAtoms", variadicAtomsCountAlg)
  ] [
    .call (resolve "CountViaVariadic") [resolve "Arg"],
    .dotCall (resolve "Arg") "CountViaVariadic" none,
    .dotCall (resolve "Arg") "count" none,
    .call (resolve "CountAtoms") [resolve "Arg"]
  ])) with
  | Except.ok [1, 1, 2, 4] => true
  | _ => false

#guard variadicNestedSequenceValuesAgreeWithBuiltinCountAndAtoms

-- A fixed parameter binds the receiver value itself, so the collection
-- builtin opens it (count 3); a collecting parameter collects the receiver as one
-- list element (count 1). The two shapes are observably different.
def ordinaryAndVariadicCountStayStructurallyDifferent : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Ordinary", ordinaryCountAlg),
    ("Variadic", variadicCountAlg)
  ] [
    .dotCall (resolve "Arg") "Ordinary" none,
    .dotCall (resolve "Arg") "Variadic" none
  ])) with
  | Except.ok [3, 1] => true
  | _ => false

#guard ordinaryAndVariadicCountStayStructurallyDifferent

-- Scaling a named property's ITEMS uses the grouped-spread receiver
-- `(Arg*).Scale(10)`: the suffix takes the factor, and the collector consumes
-- the receiver segment's supply (Arg's three spread items).
def variadicBeforeSuffixSupportsDotCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Scale", variadicScaleAlg)
  ] [
    .dotCall (.capture [sequenceSpread (resolve "Arg")])
      "Scale" (some [.num 10])
  ])) with
  | Except.ok [10, 20, 30] => true
  | _ => false

#guard variadicBeforeSuffixSupportsDotCall

-- TotalWithFee(*values, fee) is a deconstruction parameter list. The inline
-- block receiver exposes its three top-level items (10, 20, 30), so with the
-- suffix the call supplies four items; the variadic captures [10, 20, 30] and
-- `fee` binds 5, giving sum 60 + 5 = 65.
def variadicInlineTupleDotCallWithSuffixCapturesReceiverItems : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (.capture [sequenceSpread1230])
      "TotalWithFee" (some [.num 5])
  ])) with
  | Except.ok (.atom 65) => true
  | _ => false

#guard variadicInlineTupleDotCallWithSuffixCapturesReceiverItems

-- `Data.TotalWithFee(5)` supplies the named receiver's value-boundary segment
-- (one item), so the collecting parameter collects `values = [(10, 20, 30)]`
-- and `values.sum` hits the numeric element constraint — unlike the written
-- group receivers above, whose raw row supply feeds the collector.
def collectingNamedMultiOutputDotCallWithSuffixIsGroupedArgument : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Data", alg [] [] [] [.num 10, .num 20, .num 30]),
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (resolve "Data") "TotalWithFee" (some [.num 5])
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard collectingNamedMultiOutputDotCallWithSuffixIsGroupedArgument

-- The named receiver's segment supply is one item (numeric-constraint error),
-- while the written grouped-spread receiver `(Data*)` supplies its three raw
-- row items: emission, not spelling, decides what the collector consumes.
def variadicInlineTupleSpreadReceiverDiffersFromNamedReceiver : Bool :=
  let named :=
    match runResult (.algorithmExpr (algPrivate [] [] [
      ("Data", alg [] [] [] [.num 10, .num 20, .num 30]),
      ("TotalWithFee", variadicTotalWithFeeAlg)
    ] [
      .dotCall (resolve "Data") "TotalWithFee" (some [.num 5])
    ])) with
    | Except.error err => innermostIsBadArity err
    | _ => false
  let spreadReceiver :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("Data", alg [] [] [] [.num 10, .num 20, .num 30]),
      ("TotalWithFee", variadicTotalWithFeeAlg)
    ] [
      .dotCall (.capture [sequenceSpread1230])
        "TotalWithFee" (some [.num 5])
    ])) with
    | Except.ok [65] => true
    | _ => false
  named && spreadReceiver

#guard variadicInlineTupleSpreadReceiverDiffersFromNamedReceiver

-- A nested inline tuple receiver `((10, 20, 30))` is likewise one grouped
-- argument slot: the collected list holds the sequence value, so `values.sum`
-- hits the numeric element constraint.
def variadicNestedInlineTupleDotCallIsGroupedArgument : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (.capture [
      .capture [.num 10, .num 20, .num 30]
    ]) "TotalWithFee" (some [.num 5])
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard variadicNestedInlineTupleDotCallIsGroupedArgument

def ordinaryInlineTupleDotCallStillPreservesReceiverBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Collect", ordinaryCountAlg)
  ] [
    .dotCall (.capture [.num 10, .num 20, .num 30]) "Collect" none
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard ordinaryInlineTupleDotCallStillPreservesReceiverBoundary

def sequenceBuiltinInlineTupleDotCallBehaviorUnchanged : Bool :=
  let inlineSum :=
    .dotCall (.capture [.num 10, .num 20, .num 30]) "sum" none
  let nestedSum :=
    .dotCall (.capture [
      .capture [.num 10, .num 20, .num 30]
    ]) "sum" none
  let inlineWorks :=
    match runFlat inlineSum with
    | Except.ok [60] => true
    | _ => false
  let nestedFails :=
    match runFlat nestedSum with
    | Except.ok [60] => true
    | _ => false
  inlineWorks && nestedFails

#guard sequenceBuiltinInlineTupleDotCallBehaviorUnchanged

-- `((Arg*).Scale(10), Arg.map{n * 10})*`: a spread over the
-- constructed pair of the spread-receiver variadic scale and the builtin map;
-- both produce the same scaled items.
def variadicScaleMatchesBuiltinMap : Bool :=
  let builtinMap := .dotCall (resolve "Arg") "map" (some [
    .algorithmExpr (alg ["n"] [] [] [.binary .mul (.param "n") (.num 10)])
  ])
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Scale", variadicScaleAlg)
  ] [
    sequenceSpread
      (.sequenceConstruct
        (.dotCall (.capture [sequenceSpread (resolve "Arg")])
          "Scale" (some [.num 10]))
        builtinMap)
  ])) with
  | Except.ok [10, 20, 30, 10, 20, 30] => true
  | _ => false

#guard variadicScaleMatchesBuiltinMap

def collectingBindingErrorRoot : Algorithm :=
  algPrivate [] [] [
    ("F", algWithParameters [{ name := "first" }, { name := "rest", kind := .collecting }, { name := "last" }] [] [] [
      .param "first", .param "rest", .param "last"
    ])
  ] [
    .call (resolve "F") [.num 1]
  ]

def collectingBindingErrorWhenNormalParamsCannotBind : Bool :=
  -- F(first, *rest, last) is a deconstruction parameter list. F(1) supplies one
  -- scalar item, which is not opened (rule 5); the matcher needs at least the two
  -- fixed bindings (first, last), so it reports arityMismatch 2 1.
  match runResult (.algorithmExpr collectingBindingErrorRoot) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | Except.ok _ => false

#guard collectingBindingErrorWhenNormalParamsCannotBind

def sequenceValueCollectingCountAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [.capture { name := "xs", kind := .collecting }]] [] [] [
    .dotCall (.param "xs") "count" none
  ]

def sequenceValueCollectingFirstAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [.capture { name := "xs", kind := .collecting }]] [] [] [
    .index (.param "xs") (.num 0)
  ]

def sequenceValueCollectingMixedAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "xs", kind := .collecting }],
    .capture { name := "a" },
    .capture { name := "b" }
  ] [] [] [
    .dotCall (.param "xs") "count" none,
    .param "a",
    .param "b"
  ]

def sequenceValueCollectingCapturesImmediateSequenceValueItems : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingCountAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2, .num 3]
    ]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard sequenceValueCollectingCapturesImmediateSequenceValueItems

def sequenceValueCollectingRemovesOnlyOneSequenceValueBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingCountAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2],
        .num 3
      ]
    ]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceValueCollectingRemovesOnlyOneSequenceValueBoundary

def sequenceValueCollectingPreservesNestedSequenceValueItem : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingFirstAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2],
        .num 3
      ]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValueCollectingPreservesNestedSequenceValueItem

def sequenceValueCollectingRequiresSequenceValueSlot : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingCountAlg)] [
    .call (resolve "F") [.num 1, .num 2, .num 3]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 3 err
  | Except.ok _ => false

#guard sequenceValueCollectingRequiresSequenceValueSlot

def sequenceValueCollectingWithMixedTopLevelParameters : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingMixedAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2, .num 3],
      .num 4,
      .num 5
    ]
  ])) with
  | Except.ok [3, 4, 5] => true
  | _ => false

#guard sequenceValueCollectingWithMixedTopLevelParameters

def sequenceValueSeparateVariadicsDifferentLevelsAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "inner", kind := .collecting }],
    .capture { name := "outer", kind := .collecting }
  ] [] [] [
    .dotCall (.param "inner") "count" none,
    .dotCall (.param "outer") "count" none
  ]

def sequenceValueSeparateVariadicsDifferentLevelsBindIndependently : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueSeparateVariadicsDifferentLevelsAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2],
      .num 3,
      .num 4
    ]
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard sequenceValueSeparateVariadicsDifferentLevelsBindIndependently

def sequenceValueHeadTailAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "head" },
      .capture { name := "tail", kind := .collecting }
    ]
  ] [] [] [
    .param "head",
    .dotCall (.param "tail") "count" none
  ]

def sequenceValueHeadTailPatternBindsWithinOneSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueHeadTailAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2, .num 3, .num 4]
    ]
  ])) with
  | Except.ok [1, 3] => true
  | _ => false

#guard sequenceValueHeadTailPatternBindsWithinOneSlot

def sequenceValueFirstMiddleLastAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "first" },
      .capture { name := "middle", kind := .collecting },
      .capture { name := "last" }
    ]
  ] [] [] [
    .param "first",
    .dotCall (.param "middle") "count" none,
    .param "last"
  ]

def sequenceValueFirstMiddleLastPatternBindsWithinOneSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueFirstMiddleLastAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2, .num 3, .num 4, .num 5]
    ]
  ])) with
  | Except.ok [1, 3, 5] => true
  | _ => false

#guard sequenceValueFirstMiddleLastPatternBindsWithinOneSlot

def sequenceValueCollectingWithSuffixInsideSequenceValueAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "history", kind := .collecting },
      .capture { name := "pre2" }
    ],
    .capture { name := "pre1" }
  ] [] [] [
    .dotCall (.param "history") "count" none,
    .param "pre2",
    .param "pre1"
  ]

def sequenceValueCollectingWithSuffixInsideSequenceValueBindsWithinOneSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingWithSuffixInsideSequenceValueAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2, .num 3],
      .num 4
    ]
  ])) with
  | Except.ok [2, 3, 4] => true
  | _ => false

#guard sequenceValueCollectingWithSuffixInsideSequenceValueBindsWithinOneSlot

def sequenceValueCollectingWithSuffixInsideSequenceValueRequiresSuffixValue : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValueCollectingWithSuffixInsideSequenceValueAlg)] [
    .call (resolve "F") [
      .emptySequence 0,
      .num 4
    ]
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard sequenceValueCollectingWithSuffixInsideSequenceValueRequiresSuffixValue

def sequenceValuePairFirstAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }, .capture { name := "y" }]
  ] [] [] [.param "x"]

/-- Regression: `F(((A), 6))` with `A = 5`. The written grouping `(A)` is one
    grouping level around a single already-evaluated item, so pattern binding
    receives the scalar `5` itself -- never a literal-unwritable orphan
    sequence value `(5)` that would compare unequal to `5`. Mirrors assignment
    deconstruction of the same right-hand side. -/
def sequenceValuePatternParenScalarPropertyItemIsNotOrphan : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 5]),
    ("F", sequenceValuePairFirstAlg)
  ] [
    .call (resolve "F") [
      .capture [
        .capture [.resolve "A"],
        .num 6
      ]
    ]
  ])) with
  | Except.ok (.atom 5) => true
  | _ => false

#guard sequenceValuePatternParenScalarPropertyItemIsNotOrphan

/-- Regression: `F(((A), 6))` with `A = (1, 2)`. The grouped property reference
    supplies the canonical `(1, 2)` as one item -- not an orphan `((1, 2))`. -/
def sequenceValuePatternParenSequencePropertyItemStaysCanonical : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("F", sequenceValuePairFirstAlg)
  ] [
    .call (resolve "F") [
      .capture [
        .capture [.resolve "A"],
        .num 6
      ]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValuePatternParenSequencePropertyItemStaysCanonical

/-- Regression: `F(((), 6))`. A non-spread `()` item is one visible item,
    exactly as in ordinary sequence-value construction, so the pattern sees
    `((), 6)` and binds `x` to the empty sequence value. -/
def sequenceValuePatternEmptySequenceSiblingItemIsPreserved : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [
      .capture [
        .emptySequence 0,
        .num 6
      ]
    ]
  ])) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard sequenceValuePatternEmptySequenceSiblingItemIsPreserved

/-- Regression: only an explicit spread contributes zero items. `F((E*, 6))`
    with `E = ()` spreads away the empty value, so the pattern sees the single
    item `6`. -/
def sequenceValuePatternSpreadOfEmptyStillContributesNoItems : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("E", alg [] [] [] [.emptySequence 0]),
    ("F", sequenceValueCollectingCountAlg)
  ] [
    .call (resolve "F") [
      .capture [
        .sequenceSpread (.resolve "E"),
        .num 6
      ]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard sequenceValuePatternSpreadOfEmptyStillContributesNoItems

/-- The shared prepared output pass retains the exact written-slot view while constructing
    the combined counted value: a nested written group stays one grouped item, a list
    stays opaque, and only the explicit spread contributes its immediate items. Patterned call
    assembly consumes this pair directly instead of evaluating the group a second time. -/
def preparedAlgorithmOutputRetainsWrittenSlots : Bool :=
  let nested := KatLang.Expr.capture [.num 1, .num 2]
  let spreadPair := KatLang.Expr.sequenceSpread
    (KatLang.Expr.capture [.num 5, .num 6])
  let output := alg [] [] [] [nested, .listLiteral [.num 3, .num 4], spreadPair]
  let ctx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }
  match (KatLang.evalAlgOutputPreparedCore output ctx []).run KatLang.EvalState.empty with
  | .ok ({
      counted := (.sequenceValue [
        .sequenceValue [.atom 1, .atom 2],
        .listValue [.atom 3, .atom 4],
        .atom 5,
        .atom 6], 4),
      outputSlots := [
        .sequenceValue [.atom 1, .atom 2],
        .listValue [.atom 3, .atom 4],
        .atom 5,
        .atom 6]
    }, _) => true
  | _ => false

#guard preparedAlgorithmOutputRetainsWrittenSlots

/-- Discriminator: a multi-emitting single output row stays ONE written slot in the
    prepared view. `((1, 2), (3, 4)):0` re-emits the selected pair with count 2, so
    recovering the slot view by decomposing the combined counted value would present
    `[1, 2]`; the retained accumulator keeps the one written slot `[(1, 2)]`. -/
def preparedAlgorithmOutputKeepsMultiEmittingSlotWhole : Bool :=
  let pairOfPairs := KatLang.Expr.capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  let output := alg [] [] [] [.index pairOfPairs (.num 0)]
  let ctx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }
  match (KatLang.evalAlgOutputPreparedCore output ctx []).run KatLang.EvalState.empty with
  | .ok ({
      counted := (.sequenceValue [.atom 1, .atom 2], 2),
      outputSlots := [.sequenceValue [.atom 1, .atom 2]]
    }, _) => true
  | _ => false

#guard preparedAlgorithmOutputKeepsMultiEmittingSlotWhole

def sequenceValueSingletonFirstAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }]
  ] [] [] [.param "x"]

/-- End-to-end: the patterned call consumes the retained written slot — the singleton
    pattern binds the whole selected pair even though the projection re-emits count 2
    inside the written group. (The C# surface parser folds redundant parentheses
    around a lone postfix expression, so this written group is exercised on the AST
    channel, mirroring `PatternedCallSingleEvaluationTests`.) -/
def sequenceValueSingletonPatternKeepsMultiEmittingWrittenSlotWhole : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("S", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]),
    ("F", sequenceValueSingletonFirstAlg)
  ] [
    .call (resolve "F") [
      .capture [.index (resolve "S") (.num 0)]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValueSingletonPatternKeepsMultiEmittingWrittenSlotWhole

/-- Regression: `F(((1, 2)))` with `F((x, y)) = x`. The inline-written argument
    `((1, 2))` is one written grouping level around the canonical item
    `(1, 2)`, so the pattern receives exactly ONE written slot and reports
    `arityMismatch 2 1`. Written slots stay authoritative for inline-written
    pattern arguments: binding neither mints an orphan `((1, 2))` nor silently
    opens the single written item. -/
def sequenceValuePatternLiteralWrappedPairReportsWrittenSlotArity : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2]
      ]
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | Except.ok _ => false

#guard sequenceValuePatternLiteralWrappedPairReportsWrittenSlotArity

/-- Regression: redundant grouping depth canonicalizes away shallowly at each
    level, so `F((((1, 2))))` still writes exactly one slot -- the canonical
    `(1, 2)` -- and reports the same `arityMismatch 2 1`. -/
def sequenceValuePatternDeeplyWrappedPairReportsWrittenSlotArity : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [
          .capture [.num 1, .num 2]
        ]
      ]
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | Except.ok _ => false

#guard sequenceValuePatternDeeplyWrappedPairReportsWrittenSlotArity

/-- Regression: `A = ((1, 2))` canonicalizes at property construction to
    `(1, 2)`; `F(A)` then opens the stored canonical sequence value for the
    pattern, so `F((x, y)) = x` binds `x = 1`. No hidden orphan `((1, 2))`
    distinguishes the stored value from the writable literal `(1, 2)`. -/
def sequenceValuePatternPropertyStoredWrappedPairOpensCanonically : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.capture [.num 1, .num 2]]),
    ("F", sequenceValuePairFirstAlg)
  ] [
    .call (resolve "F") [.resolve "A"]
  ])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard sequenceValuePatternPropertyStoredWrappedPairOpensCanonically

def sequenceValuePairFirstWithFixedSuffixAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }, .capture { name := "y" }],
    .capture { name := "z" }
  ] [] [] [.param "x"]

/-- Regression: `KeepFirst(((1, 2)), 3)` with `KeepFirst((x, y), z) = x`. The
    trailing fixed argument binds normally; the sequence-value pattern still
    receives one written slot for `((1, 2))` and reports `arityMismatch 2 1`. -/
def sequenceValuePatternWrappedPairWithFixedSuffixReportsWrittenSlotArity : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstWithFixedSuffixAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2]
      ],
      .num 3
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | Except.ok _ => false

#guard sequenceValuePatternWrappedPairWithFixedSuffixReportsWrittenSlotArity

def sequenceValueSingleCaptureAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }]
  ] [] [] [.param "x"]

/-- Regression: `IdSeq(((1, 2)))` with `IdSeq((x)) = x`. The one-capture
    sequence pattern consumes the single written slot, and that slot is the
    CANONICAL item `(1, 2)`: the shallow singleton-erasing combiner never
    materializes a literal-unwritable orphan `((1, 2))` around it. The
    structural match pins the exact shape. -/
def sequenceValuePatternSingleCaptureBindsWrappedPairAsCanonicalItem : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValueSingleCaptureAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2]
      ]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValuePatternSingleCaptureBindsWrappedPairAsCanonicalItem

def sequenceValueSingleCaptureCountAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x" }]
  ] [] [] [.dotCall (.param "x") "count" none]

/-- Regression: the canonically bound item observes consistently -- `x.count`
    for the `IdSeq(((1, 2)))` binding is 2, matching the structural shape
    `(1, 2)` (an orphan `((1, 2))` would count 1). -/
def sequenceValuePatternSingleCaptureWrappedPairCountsItems : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueSingleCaptureCountAlg)] [
    .call (resolve "F") [
      .capture [
        .capture [.num 1, .num 2]
      ]
    ]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceValuePatternSingleCaptureWrappedPairCountsItems

/-- Guard: the shallow combiner never drops empty-sequence siblings.
    `F(((), ()))` writes two items, so the pair pattern binds both empties
    positionally and `x` is the real empty sequence value. -/
def sequenceValuePatternTwoEmptySiblingItemsBindPositionally : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") [
      .capture [.emptySequence 0, .emptySequence 0]
    ]
  ])) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard sequenceValuePatternTwoEmptySiblingItemsBindPositionally

def sequenceValueCollectingIsNotTopLevelVariadic : Bool :=
  let sequenceValueCall :=
    runFlat (.algorithmExpr (algPrivate [] [] [("F", algWithParameterPatterns [
      .sequenceValue [.capture { name := "xs", kind := .collecting }], .capture { name := "y" }
    ] [] [] [
      .dotCall (.param "xs") "count" none,
      .param "y"
    ])] [
      .call (resolve "F") [
        .capture [.num 1, .num 2],
        .num 3
      ]
    ]))
  let flatCall :=
    runResult (.algorithmExpr (algPrivate [] [] [("F", algWithParameterPatterns [
      .sequenceValue [.capture { name := "xs", kind := .collecting }], .capture { name := "y" }
    ] [] [] [
      .dotCall (.param "xs") "count" none,
      .param "y"
    ])] [
      .call (resolve "F") [.num 1, .num 2, .num 3]
    ]))
  match sequenceValueCall, flatCall with
  | Except.ok [2, 3], Except.error err => innermostIsArityMismatch 2 3 err
  | _, _ => false

#guard sequenceValueCollectingIsNotTopLevelVariadic

-- Source `Step((*history), previous) = (history*, previous + 1), previous + 1`,
-- matching the C# regression `Eval_LoopStep_SequenceValueCommaHistorySlotUsesExplicitSpreadAcrossRepeat`.
-- The first output slot is the written sequence value `(history*, previous + 1)`:
-- a written group whose comma rows are `history*` (an explicit spread opening the
-- captured history one level) and `previous + 1`. The written spread splices its
-- items before the sibling slot — the same `(A*, 99)` = `(1, 2, 99)` rule as
-- every written sequence value — so the history slot GROWS FLAT by one item per
-- step. Starting from `(1, 2)` and stepping twice, `:0` selects the flat
-- `(1, 2, 3, 4)`. To deepen instead of flattening, write the history as a
-- non-spread item: `(history, previous + 1)`.
-- (Before the July 2026 alignment fix, `evalAlgOutputCore` kept a non-empty
-- spread output slot grouped as one un-expanded slot, so this program nested to
-- `(((1, 2), 3), 4)` — diverging from `evalAlgOutputCountedCore`, from the C#
-- evaluator, and from written-sequence spread semantics. This guard pins the
-- aligned flat behavior at the exact structural level.)
def sequenceValueCollectingLoopStepSpreadGrowsHistoryFlat : Bool :=
  let step := algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "previous" }
  ] [] [] [
    .capture [sequenceSpread (.param "history"), .binary .add (.param "previous") (.num 1)],
    .binary .add (.param "previous") (.num 1)
  ]
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", step)] [
    .index
      (.dotCall (resolve "Step") "repeat" (some [
        .num 2,
        .capture [.num 1, .num 2],
        .num 2
      ]))
      (.num 0)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3, .atom 4]) => true
  | _ => false

#guard sequenceValueCollectingLoopStepSpreadGrowsHistoryFlat

-- Source `Step((*history, previous), current) = (history*, current), current`.
-- Same shape as `sequenceValueCollectingLoopStepSpreadGrowsHistoryFlat`: the first output
-- slot is the sequence-value pair `(history*, current)` — a written group whose comma rows are
-- `history*` (sequence-spread) and `current` — so it is one next-state slot.
-- (Contrast a spread over `sequenceConstruct history current`, which is a different shape.)
def sequenceValueCollectingLoopStepWithSuffixInsideSequenceValuePreservesStateShape : Bool :=
  let step := algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "history", kind := .collecting },
      .capture { name := "previous" }
    ],
    .capture { name := "current" }
  ] [] [] [
    .capture [sequenceSpread (.param "history"), .param "current"],
    .param "current"
  ]
  -- Exact structural check. Here the sequence-value pattern `(*history, previous)`
  -- DESTRUCTURES the slot `(1, 2)` into atoms — history captures the leading atom
  -- `1` and `previous` the trailing `2` — so `history*` spreads a bare atom, not
  -- a nested sequence value. The next slot is therefore the FLAT pair `(1, 3)`, and it stays
  -- flat across iterations (dropping the previous `previous`, unlike the
  -- variadic-only `(*history)` capture in
  -- `sequenceValueCollectingLoopStepSpreadGrowsHistoryFlat`, which accumulates).
  -- Asserting the exact `Result` pins this flat shape.
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", step)] [
    .index
      (.dotCall (resolve "Step") "repeat" (some [
        .num 2,
        .capture [.num 1, .num 2],
        .num 3
      ]))
      (.num 0)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 3]) => true
  | _ => false

#guard sequenceValueCollectingLoopStepWithSuffixInsideSequenceValuePreservesStateShape

def loopVariadicHistoryLastExpr : KatLang.Expr :=
  .dotCall (.call (resolve "atoms") [.param "history"]) "last" none

def loopVariadicNextExpr : KatLang.Expr :=
  .binary .add loopVariadicHistoryLastExpr (.num 1)

def loopVariadicAppendNextAlg : Algorithm :=
  algWithParameters [{ name := "history", kind := .collecting }] [] [] [
    .sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr
  ]

def loopVariadicContinueFlagExpr : KatLang.Expr :=
  .call (resolve "if") [
    .binary .lt loopVariadicNextExpr (.num 6),
    .num 1,
    .num 0
  ]

def loopVariadicWhileAppendNextAlg : Algorithm :=
  algWithParameters [{ name := "history", kind := .collecting }] [] [] [
    .sequenceConstruct
      (.sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr)
      loopVariadicContinueFlagExpr
  ]

def loopVariadicInitialState : Algorithm :=
  alg [] [] [] [.num 1, .num 2, .num 4]

def variadicLoopStepRepeatOneIterationCapturesStateItems : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicAppendNextAlg)] [
    .dotCall (resolve "Step") "repeat" (some [
      .num 1,
      sequenceItems [.num 1, .num 2, .num 4]
    ])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5]) => true
  | _ => false

#guard variadicLoopStepRepeatOneIterationCapturesStateItems

def variadicLoopStepRepeatTwoIterationsKeepsExpandedState : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicAppendNextAlg)] [
    .dotCall (resolve "Step") "repeat" (some [
      .num 2,
      sequenceItems [.num 1, .num 2, .num 4]
    ])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5, .atom 6]) => true
  | _ => false

#guard variadicLoopStepRepeatTwoIterationsKeepsExpandedState

def variadicLoopStepWhileUsesExpandedState : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicWhileAppendNextAlg)] [
    .dotCall (resolve "Step") "while" (some [
      sequenceItems [.num 1, .num 2, .num 4]
    ])
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard variadicLoopStepWhileUsesExpandedState

def sequenceBuiltinDotCallVariadicRepeatReceiverTakeUsesFinalStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicAppendNextAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some [
        .num 3,
        sequenceItems [.num 1, .num 2, .num 4]
      ]))
      "take"
      (some [.num 5])
  ])) with
  | Except.ok [1, 2, 4, 5, 6] => true
  | _ => false

#guard sequenceBuiltinDotCallVariadicRepeatReceiverTakeUsesFinalStateSlots

-- Aspect 2 loop-state variadic binding (mirrors C# EvaluatorTests.Eval_VariadicLoopStep_*).
-- A top-level variadic loop interface binds state as an item supply: the fixed prefix
-- and suffix bind from the ends, and the collecting parameter collects the matched middle state slots
-- as one exact immutable list. The minimum is the FIXED (non-variadic) parameter count —
-- the collecting parameter may collect ZERO slots (empty collected list = `[]`), the same rule as every other collecting-binding
-- receiver — and the max is unbounded (extra middle slots are accepted).
def loopVariadicPrefixMiddleSuffixAlg : Algorithm :=
  algWithParameters [
    { name := "first" },
    { name := "middle", kind := .collecting },
    { name := "last" }
  ] [] [] [
    .param "first",
    .dotCall (.param "middle") "count" none,
    .param "last"
  ]

def loopVariadicPrefixMiddleSuffixIncrementAlg : Algorithm :=
  algWithParameters [
    { name := "first" },
    { name := "middle", kind := .collecting },
    { name := "last" }
  ] [] [] [
    .binary .add (.param "first") (.num 1),
    sequenceSpread (.param "middle"),
    .binary .add (.param "last") (.num 1)
  ]

-- Extra middle: 4 state slots bind first=10/last=40 from the ends, middle = [20, 30]
-- (count 2). Mirrors C# Eval_VariadicLoopStep_WithPrefixMiddleSuffix_PreservesDeclarationOrderBindings.
def variadicLoopStepCapturesExtraMiddleStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 10, .num 20, .num 30, .num 40])
  ])) with
  | Except.ok [10, 2, 40] => true
  | _ => false

#guard variadicLoopStepCapturesExtraMiddleStateSlots

-- Exact structural count: 3 state slots bind first=10/last=30 and middle = [20] (count 1).
def variadicLoopStepExactStructuralCountBinds : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 10, .num 20, .num 30])
  ])) with
  | Except.ok [10, 1, 30] => true
  | _ => false

#guard variadicLoopStepExactStructuralCountBinds

-- Empty collected segment: 2 state slots bind first=10/last=20 from the ends and the collecting parameter
-- collects ZERO middle slots (middle = [], count 0) — the same empty-segment rule
-- as every other collecting binding.
def variadicLoopStepEmptyMiddleBindsEmptyList : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 10, .num 20])
  ])) with
  | Except.ok [10, 0, 20] => true
  | _ => false

#guard variadicLoopStepEmptyMiddleBindsEmptyList

-- Fixed-minimum failure: only 1 state slot cannot satisfy the two FIXED
-- parameters first + last, so this is arityMismatch 2 1.
def variadicLoopStepBelowFixedMinimumFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 10])
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | _ => false

#guard variadicLoopStepBelowFixedMinimumFails

-- The exact reviewed case: Step(first, *middle, last) = first + 1, middle*, last + 1
-- with Step.repeat(2, 0, 5, 5, 10) binds first=0, middle=[5, 5] (the collected exact
-- list), last=10 and, after two iterations (the body re-spreads middle with
-- `.sequenceSpread (.param "middle")`),
-- yields 2, 5, 5, 12 (previously rejected by Lean as arityMismatch 3 4).
def variadicLoopStepExtraMiddleRepeatsTwice : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixIncrementAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 2, .num 0, .num 5, .num 5, .num 10])
  ])) with
  | Except.ok [2, 5, 5, 12] => true
  | _ => false

#guard variadicLoopStepExtraMiddleRepeatsTwice

def ordinaryRunStepStillRejectsMultiValueState : Bool :=
  match KatLang.runEvalM <| KatLang.runStep
      (alg ["history"] [] [] [.param "history"])
      KatLang.EvalCtx.empty
      []
      (.sequenceValue [.atom 1, .atom 2, .atom 4]) with
  | Except.error err => innermostIsArityMismatch 0 2 err
  | _ => false

#guard ordinaryRunStepStillRejectsMultiValueState

def loopBoundaryPairStepAlg : Algorithm :=
  alg ["a", "b"] [] [] [
    .param "b",
    .binary .add (.param "a") (.param "b")
  ]

def loopBoundaryPairWhileStepAlg : Algorithm :=
  alg ["a", "b"] [] [] [
    .binary .add (.param "a") (.num 1),
    .binary .add (.param "b") (.num 10),
    .binary .lt (.param "a") (.num 2)
  ]

def loopBoundarySequenceValueRepeatStepAlg : Algorithm :=
  alg ["x"] [] [] [
    .capture [.param "x", .binary .add (.param "x") (.num 1)]
  ]

def loopBoundarySequenceValueWhileStepAlg : Algorithm :=
  alg ["x"] [] [] [
    .capture [.param "x", .binary .add (.param "x") (.num 1)],
    .num 0
  ]

def sequenceBuiltinDotCallRepeatReceiverTakeUsesFinalStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryPairStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some [
        .num 1,
        .num 1,
        .num 2
      ]))
      "take"
      (some [.num 1])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallRepeatReceiverTakeUsesFinalStateSlots

def sequenceBuiltinDotCallRepeatReceiverCountUsesFinalStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryPairStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some [
        .num 1,
        .num 1,
        .num 2
      ]))
      "count"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallRepeatReceiverCountUsesFinalStateSlots

def sequenceBuiltinDotCallRepeatSequenceValueStateCountsOneItem : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundarySequenceValueRepeatStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some [
        .num 1,
        .num 1
      ]))
      "count"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallRepeatSequenceValueStateCountsOneItem

def sequenceBuiltinDotCallWhileReceiverTakeUsesFinalStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryPairWhileStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "while" (some [
        .num 0,
        .num 0
      ]))
      "take"
      (some [.num 1])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallWhileReceiverTakeUsesFinalStateSlots

def sequenceBuiltinDotCallWhileReceiverCountUsesFinalStateSlots : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryPairWhileStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "while" (some [
        .num 0,
        .num 0
      ]))
      "count"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallWhileReceiverCountUsesFinalStateSlots

def sequenceBuiltinDotCallWhileSequenceValueStateCountsOneItem : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Step", loopBoundarySequenceValueWhileStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "while" (some [
        .num 1
      ]))
      "count"
      none
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard sequenceBuiltinDotCallWhileSequenceValueStateCountsOneItem

def loopBoundarySumPairStepAlg : Algorithm :=
  alg ["a", "b"] [] [] [
    .binary .add (.param "a") (.param "b")
  ]

def loopBoundaryIdentityAlg : Algorithm :=
  alg ["history"] [] [] [.param "history"]

def loopBoundaryVariadicIdentityAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [.param "values"]

def loopBoundarySequenceValueHistoryStepAlg : Algorithm :=
  alg ["history"] [] [] [
    .capture [
      .sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr
    ]
  ]

def loopBoundarySpreadHistoryStepAlg : Algorithm :=
  alg ["history"] [] [] [
    .sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr
  ]

def loopInitialManyExplicitArgsCreateManySlots : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryPairStepAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 1, .num 2])
  ])) with
  | Except.ok (.sequenceValue [.atom 2, .atom 3]) => true
  | _ => false

#guard loopInitialManyExplicitArgsCreateManySlots

-- A single-collecting loop step binds many separate init slots as its item supply
-- (Aspect 2: matches C#). Step(*values) = values with repeat(1, 1, 2, 3) collects
-- values = [1, 2, 3] (one exact list) rather than rejecting the extra slots as the
-- old strict path did.
def loopInitialExplicitVariadicStepCapturesManySlots : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Step", loopBoundaryVariadicIdentityAlg)] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, .num 1, .num 2, .num 3])
  ])) with
  | Except.ok (.listValue [.atom 1, .atom 2, .atom 3]) => true
  | _ => false

#guard loopInitialExplicitVariadicStepCapturesManySlots

def loopInitialSequenceValuePropertyArgIsOneSlot : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundaryIdentityAlg),
    ("List", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, resolve "List"])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4]) => true
  | _ => false

#guard loopInitialSequenceValuePropertyArgIsOneSlot

def loopInitialSequenceValueArgDoesNotSatisfyTwoOrdinaryParams : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundarySumPairStepAlg),
    ("Pair", alg [] [] [] [.num 1, .num 2])
  ] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, resolve "Pair"])
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | _ => false

#guard loopInitialSequenceValueArgDoesNotSatisfyTwoOrdinaryParams

def loopInitialExplicitSelectionsSplitSequenceValueArg : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundarySumPairStepAlg),
    ("Pair", alg [] [] [] [.num 1, .num 2])
  ] [
    .dotCall (resolve "Step") "repeat" (some [
      .num 1,
      .index (resolve "Pair") (.num 0),
      .index (resolve "Pair") (.num 1)
    ])
  ])) with
  | Except.ok (.atom 3) => true
  | _ => false

#guard loopInitialExplicitSelectionsSplitSequenceValueArg

def loopInitialSequenceValueHistorySlotCanBePreservedAcrossRepeat : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundarySequenceValueHistoryStepAlg),
    ("List", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some [.num 2, resolve "List"])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5, .atom 6]) => true
  | _ => false

#guard loopInitialSequenceValueHistorySlotCanBePreservedAcrossRepeat

def loopInitialSpreadStepOutputStillBecomesNextStateSlots : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundarySpreadHistoryStepAlg),
    ("List", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some [.num 2, resolve "List"])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5, .atom 6]) => true
  | _ => false

#guard loopInitialSpreadStepOutputStillBecomesNextStateSlots

def loopInitialMultiOutputPropertyArgIsOneSlot : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundaryIdentityAlg),
    ("Values", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some [.num 1, resolve "Values"])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4]) => true
  | _ => false

#guard loopInitialMultiOutputPropertyArgIsOneSlot

-- Explicit selections that split a multi-output property into separate init slots are
-- bound by the single-collecting step as its item supply (Aspect 2: matches C#), so the
-- three split slots are collected as values = [1, 2, 4] instead of being rejected.
def loopInitialExplicitSelectionsSplitMultiOutputProperty : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Step", loopBoundaryVariadicIdentityAlg),
    ("Values", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some [
      .num 1,
      .index (resolve "Values") (.num 0),
      .index (resolve "Values") (.num 1),
      .index (resolve "Values") (.num 2)
    ])
  ])) with
  | Except.ok (.listValue [.atom 1, .atom 2, .atom 4]) => true
  | _ => false

#guard loopInitialExplicitSelectionsSplitMultiOutputProperty

--------------------------------------------------------------------------------
-- Numeric semantics: truncating division/modulo (C# reference parity)
--------------------------------------------------------------------------------

def binaryAtomResult? (op : KatLang.BinaryOp) (a b : Int) : Option Int :=
  match runResult (.binary op (.num a) (.num b)) with
  | Except.ok (.atom value) => some value
  | _ => none

-- Division truncates toward zero (Int.tdiv), matching the C# runtime
-- (`Math.Truncate` for `div`): -7 div 2 = -3, not the Euclidean -4.
def truncatingDivisionMatchesRuntime : Bool :=
  binaryAtomResult? .idiv 7 2 == some 3 &&
  binaryAtomResult? .idiv (-7) 2 == some (-3) &&
  binaryAtomResult? .idiv 7 (-2) == some (-3) &&
  binaryAtomResult? .idiv (-7) (-2) == some 3 &&
  binaryAtomResult? .div (-7) 2 == some (-3) &&
  binaryAtomResult? .div 7 (-2) == some (-3)

#guard truncatingDivisionMatchesRuntime

-- Modulo keeps the sign of the dividend (Int.tmod), matching the C# runtime
-- (decimal remainder): -7 mod 2 = -1, not the Euclidean 1.
def truncatingModuloMatchesRuntime : Bool :=
  binaryAtomResult? .mod 7 2 == some 1 &&
  binaryAtomResult? .mod (-7) 2 == some (-1) &&
  binaryAtomResult? .mod 7 (-2) == some 1 &&
  binaryAtomResult? .mod (-7) (-2) == some (-1)

#guard truncatingModuloMatchesRuntime

--------------------------------------------------------------------------------
-- Numeric semantics: negative exponents are never a silent 0
--------------------------------------------------------------------------------

-- Negative exponents with base 1 or -1 have exact integer reciprocals and
-- evaluate exactly, matching the C# runtime.
def negativeExponentExactCases : Bool :=
  binaryAtomResult? .pow 2 3 == some 8 &&
  binaryAtomResult? .pow 1 (-2) == some 1 &&
  binaryAtomResult? .pow (-1) (-3) == some (-1) &&
  binaryAtomResult? .pow (-1) (-2) == some 1

#guard negativeExponentExactCases

-- 0 ^ negative is a domain error (same message as the C# runtime).
def zeroToNegativeExponentIsDomainError : Bool :=
  match runResult (.binary .pow (.num 0) (.num (-1))) with
  | Except.error err =>
      innermostIsIllegalInEval "zero cannot be raised to a negative integer exponent" err
  | _ => false

#guard zeroToNegativeExponentIsDomainError

-- |base| >= 2 with a negative exponent has a fractional reciprocal
-- (2 ^ -1 = 0.5 in the decimal runtime). The Int core raises an explicit
-- error instead of silently truncating the reciprocal to 0.
def fractionalReciprocalExponentIsExplicitError : Bool :=
  (match runResult (.binary .pow (.num 2) (.num (-1))) with
   | Except.error (.illegalInEval _) => true
   | _ => false) &&
  (match runResult (.binary .pow (.num (-3)) (.num (-2))) with
   | Except.error (.illegalInEval _) => true
   | _ => false)

#guard fractionalReciprocalExponentIsExplicitError

--------------------------------------------------------------------------------
-- Conditional algorithms in value position fail like no-arg dot-call access
--------------------------------------------------------------------------------

def valueAccessConditionalAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 0] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 1] ⟩
  ]

-- Sanity: calling the conditional still selects branches normally.
def conditionalDirectCallStillSelectsBranch : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", valueAccessConditionalAlg)] [
    .call (resolve "F") [.num 0],
    .call (resolve "F") [.num 7]
  ])) with
  | Except.ok [0, 1] => true
  | _ => false

#guard conditionalDirectCallStillSelectsBranch

-- Bare property-style reference must raise noMatchingBranch, not return a
-- silently cached empty sequence value.
def bareConditionalPropertyReferenceFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", valueAccessConditionalAlg)] [
    resolve "F"
  ])) with
  | Except.error err => innermostIsNoMatchingBranch "F" err
  | _ => false

#guard bareConditionalPropertyReferenceFails

-- Dot-call access without arguments agrees with the bare reference.
def dotCallConditionalWithoutArgsFails : Bool :=
  match runResult (.dotCall (.algorithmExpr (algPrivate [] [] [
    ("F", valueAccessConditionalAlg)
  ] [.num 0])) "F" none) with
  | Except.error err => innermostIsNoMatchingBranch "F" err
  | _ => false

#guard dotCallConditionalWithoutArgsFails

-- Forcing a conditional through a sequence-builtin collection argument also
-- fails instead of silently contributing nothing.
def conditionalCollectionArgumentFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", valueAccessConditionalAlg)] [
    .call (resolve "sum") [resolve "F"]
  ])) with
  | Except.error err => innermostIsNoMatchingBranch "conditional" err
  | _ => false

#guard conditionalCollectionArgumentFails

-- A conditional bound as a higher-order argument fails when referenced as a
-- bare zero-argument thunk inside the callee body.
def conditionalHigherOrderThunkReferenceFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("F", valueAccessConditionalAlg),
    ("Apply", alg ["f"] [] [] [.param "f"])
  ] [
    .call (resolve "Apply") [resolve "F"]
  ])) with
  | Except.error err => innermostIsNoMatchingBranch "f" err
  | _ => false

#guard conditionalHigherOrderThunkReferenceFails

--------------------------------------------------------------------------------
-- Singleton sequence-value patterns match identically in direct and callback calls
--------------------------------------------------------------------------------

-- G((0)) = 100; G((x)) = x. Result normalization collapses singleton sequence values,
-- so the singleton sequence-value pattern must accept a plain scalar argument.
def singletonSequenceValueConditionalAlg : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.litInt 0]], alg [] [] [] [.num 100] ⟩,
    ⟨ .sequenceValue [.sequenceValue [.bind "x"]], alg [] [] [] [.param "x"] ⟩
  ]

def singletonSequenceValuePatternMatchesDirectCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("G", singletonSequenceValueConditionalAlg)] [
    .call (resolve "G") [.num 0],
    .call (resolve "G") [.num 5]
  ])) with
  | Except.ok [100, 5] => true
  | _ => false

#guard singletonSequenceValuePatternMatchesDirectCall

-- The same conditional must accept the same shapes through map callbacks.
def singletonSequenceValuePatternMatchesMapCallback : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("G", singletonSequenceValueConditionalAlg)] [
    .call (resolve "map") [sequenceItems [.num 0, .num 5], resolve "G"]
  ])) with
  | Except.ok [100, 5] => true
  | _ => false

#guard singletonSequenceValuePatternMatchesMapCallback

-- Multi-member sequence-value patterns still reject scalars; only the singleton
-- adaptation is permitted.
def multiMemberSequenceValuePatternStillRejectsScalars : Bool :=
  let pairFirst : Algorithm :=
    .conditional none [] [
      ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b"]], alg [] [] [] [.num 1] ⟩,
      ⟨ .sequenceValue [.bind "x"], alg [] [] [] [.num 2] ⟩
    ]
  match runFlat (.algorithmExpr (algPrivate [] [] [("H", pairFirst)] [
    .call (resolve "H") [.num 9]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard multiMemberSequenceValuePatternStillRejectsScalars

--------------------------------------------------------------------------------
-- Dot-call receiver symmetry for user-defined leading flat variadic callees
--------------------------------------------------------------------------------
-- The general segment rule: the dot-call receiver is ONE leading argument
-- segment for arity checking and fixed prefix/suffix allocation, and a flat
-- top-level collecting parameter allocated the segment consumes the segment's
-- evaluated top-level supply. A STORED property receiver evaluates at its
-- value boundary, so its segment supply is one item (`Pair.NItems` collects
-- [Pair]) and the dot form coincides with the canonical `NItems(Pair)`; a
-- WRITTEN group receiver — `(10, 20)` or `(Pair*)` — emits its raw row
-- supply, which the allocated collector consumes. A FIXED parameter allocated
-- the receiver segment always binds the segment's one captured value; the
-- receiver is never pre-expanded to satisfy prefix/suffix arity.

def expectFlat (result : Except Error (List Int)) (expected : List Int) : Bool :=
  match result with
  | Except.ok values => values == expected
  | _ => false

def expectInnermostTypeMismatch (result : Except Error (List Int)) : Bool :=
  match result with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

def expectInnermostArityMismatch (expected actual : Nat) (result : Except Error (List Int)) : Bool :=
  match result with
  | Except.error err => innermostIsArityMismatch expected actual err
  | _ => false

-- NItems(*values) = values.count
def receiverSymmetryNItemsAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] []
    [.dotCall (.param "values") "count" none]

-- BeforeLastCount(*values, last) = values.count
def receiverSymmetryBeforeLastCountAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }, { name := "last" }] [] []
    [.dotCall (.param "values") "count" none]

-- SumPlusLast(*values, last) = values.sum + last
def receiverSymmetrySumAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }, { name := "last" }] [] []
    [.binary .add (.dotCall (.param "values") "sum" none) (.param "last")]

-- Pair = (10, 20): one sequence value.
def sequenceValuePairReceiverProp : Prod String Algorithm :=
  ("Pair", alg [] [] [] [.capture [.num 10, .num 20]])

-- Values = 10, 20: two emitted top-level values.
def multiOutputValuesReceiverProp : Prod String Algorithm :=
  ("Values", alg [] [] [] [.num 10, .num 20])

def runReceiverSymmetryCase (receiverProp calleeProp : Prod String Algorithm)
    (out : KatLang.Expr) : Except Error (List Int) :=
  runFlat (.algorithmExpr (algPrivate [] [] [receiverProp, calleeProp] [out]))

-- Pair normalizes to the two-item sequence it contains; ordinary receiver and
-- canonical call agree on that ONE sequence-valued slot, which the collecting parameter
-- collects as a one-element list (count 1).
def sequenceValueReceiverLeadingVariadicIsOneSlot : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (resolve "Pair") "NItems" none)) [1] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") [resolve "Pair"])) [1]

#guard sequenceValueReceiverLeadingVariadicIsOneSlot

-- Pair* spreads two slots; single-collecting `NItems(*values)` collects those two
-- slots into one exact list of count 2.
def sequenceValueReceiverSpreadFeedsItemSupply : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Pair")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") [sequenceSpread (resolve "Pair")])) [2]

#guard sequenceValueReceiverSpreadFeedsItemSupply

-- BeforeLastCount(*values, last) binds the supplied item supply:
-- Pair.BeforeLastCount(99) and the canonical call pass ONE sequence-valued slot
-- plus the suffix (collected count 1). In the spread forms, the suffix takes
-- 99 and the collector receives Pair's two items — the dot form through the
-- grouped receiver segment's supply, the canonical form through ordinary
-- spread slots (collected count 2). Dot-call and canonical call agree within
-- each shape.
def sequenceValueReceiverWithSuffixMatchesCanonicalCalls : Bool :=
  let callee := ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg)
  let suffixArgs : List KatLang.Expr := [.num 99]
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (resolve "Pair") "BeforeLastCount" (some suffixArgs))) [1] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") [resolve "Pair", .num 99])) [1] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Pair")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpread (resolve "Pair"), .num 99])) [2]

#guard sequenceValueReceiverWithSuffixMatchesCanonicalCalls

-- Values emits two top-level values. The ordinary forms pass ONE sequence-valued
-- slot (collected count 1); the explicit spread forms supply two slots (collected count
-- 2). Dot-call and canonical call agree within each shape.
def multiOutputReceiverCountsMatchCanonicalCalls : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "NItems" none)) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") [resolve "Values"])) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") [sequenceSpread (resolve "Values")])) [2]

#guard multiOutputReceiverCountsMatchCanonicalCalls

-- BeforeLastCount(*values, last) binds the supplied item supply. The ordinary
-- and canonical forms pass ONE sequence-valued slot plus the suffix (collected
-- count 1); in the spread forms the suffix takes 99 and the collector receives
-- Values' two items — grouped receiver-segment supply on the dot side,
-- ordinary spread slots on the canonical side (collected count 2). Dot-call
-- and canonical call agree within each shape.
def multiOutputReceiverWithSuffixMatchesCanonicalCalls : Bool :=
  let callee := ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg)
  let suffixArgs : List KatLang.Expr := [.num 99]
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "BeforeLastCount" (some suffixArgs))) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") [resolve "Values", .num 99])) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpread (resolve "Values"), .num 99])) [2]

#guard multiOutputReceiverWithSuffixMatchesCanonicalCalls

-- SumPlusLast(*values, last) with no extra argument receives exactly one
-- grouped sequence value, so `last` gets that value and the numeric body fails.
-- Explicit spread below is the successful path.
def ordinaryMultiOutputReceiverStaysOneSlotAtSuffixAllocation : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "SumPlusLast" none)) &&
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [resolve "Values"]))

#guard ordinaryMultiOutputReceiverStaysOneSlotAtSuffixAllocation

-- Allocation precedes supply consumption, and a receiver is never
-- pre-expanded: with no extra argument, `(Values*).SumPlusLast` is ONE
-- receiver segment, so the fixed suffix `last` binds the segment's captured
-- value (10, 20) whole and the numeric body fails. The canonical spread-slot
-- call `SumPlusLast(Values*)` supplies 10 and 20 as ordinary slots before
-- allocation, so `last` binds 20 and the collector captures [10] — the two
-- spellings are observably different at a fixed suffix.
def groupedSpreadReceiverStaysOneSegmentAtSuffixAllocation : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "SumPlusLast" none)) &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [sequenceSpread (resolve "Values")])) [30]

#guard groupedSpreadReceiverStaysOneSegmentAtSuffixAllocation

-- With an extra written argument the suffix takes it from the back and the
-- collector consumes the grouped receiver segment's supply, agreeing with the
-- canonical spread-slot call: values = [10, 20], last = 5, sum = 35.
def groupedSpreadReceiverWithSuffixArgConsumesSupply : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "SumPlusLast" (some [.num 5]))) [35] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [sequenceSpread (resolve "Values"), .num 5])) [35]

#guard groupedSpreadReceiverWithSuffixArgConsumesSupply

-- A written inline group receiver emits its raw row supply as the receiver
-- segment's supply, so the allocated collector collects both rows (count 2).
-- The direct call `NItems((10, 20))` still collects one written grouped
-- argument — receiver segments and written argument slots are different
-- receivers.
def inlineGroupReceiverSuppliesRowItemsToLeadingVariadic : Bool :=
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("NItems", receiverSymmetryNItemsAlg)
  ] [
    .dotCall (.capture [.num 10, .num 20]) "NItems" none
  ]))) [2] &&
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("NItems", receiverSymmetryNItemsAlg)
  ] [
    .call (resolve "NItems") [.capture [.num 10, .num 20]]
  ]))) [1]

#guard inlineGroupReceiverSuppliesRowItemsToLeadingVariadic

--------------------------------------------------------------------------------
-- Dot-receiver segment rule: the required regression matrix
--------------------------------------------------------------------------------
-- Mean(*vector) = vector.sum / vector.count — the integer twin of the C#
-- headline example: the direct flat call and the written group receiver
-- produce the same mean (2 under integer division).
def dotReceiverSegmentMeanAlg : Algorithm :=
  algWithParameters [{ name := "vector", kind := .collecting }] [] [] [
    .binary .div
      (.dotCall (.param "vector") "sum" none)
      (.dotCall (.param "vector") "count" none)
  ]

def dotReceiverSegmentMeanIntegerTwin : Bool :=
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("Mean", dotReceiverSegmentMeanAlg)
  ] [
    .call (resolve "Mean") [.num 1, .num 2, .num 3],
    .dotCall (.capture [.num 1, .num 2, .num 3]) "Mean" none
  ]))) [2, 2]

#guard dotReceiverSegmentMeanIntegerTwin

def dotReceiverSegmentCollectAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [
    .param "items"
  ]

def runDotReceiverCollect (receiver : KatLang.Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] [
    ("Collect", dotReceiverSegmentCollectAlg),
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .dotCall receiver "Collect" none
  ]))

def expectCollectResult (receiver : KatLang.Expr) (expected : Result) : Bool :=
  match runDotReceiverCollect receiver with
  | Except.ok value => reprStr value == reprStr expected
  | _ => false

-- Boundary and cardinality matrix for the collector-consumes-segment-supply
-- rule. A written group receiver supplies its raw rows; one extra written
-- boundary survives as one item; `()` supplies zero items; exact lists stay
-- opaque; nothing is recursively flattened.
def dotReceiverSegmentCollectBoundaryMatrix : Bool :=
  expectCollectResult (.capture [.num 1, .num 2])
    (.listValue [.atom 1, .atom 2]) &&
  expectCollectResult (.capture [.capture [.num 1, .num 2]])
    (.listValue [.sequenceValue [.atom 1, .atom 2]]) &&
  expectCollectResult (.emptySequence 1)
    (.listValue []) &&
  expectCollectResult (.listLiteral [.num 1, .num 2])
    (.listValue [.listValue [.atom 1, .atom 2]]) &&
  expectCollectResult (.capture [.num 1, .capture [.num 2, .num 3]])
    (.listValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) &&
  expectCollectResult (.capture [sequenceSpread (resolve "Values"), .num 7])
    (.listValue [.atom 1, .atom 2, .atom 3, .atom 7]) &&
  expectCollectResult (.capture [.capture [sequenceSpread (resolve "Values"), .num 7]])
    (.listValue [.sequenceValue [.atom 1, .atom 2, .atom 3, .atom 7]]) &&
  expectCollectResult (.algorithmExpr (alg [] [] [] [.num 1, .num 2, .num 3]))
    (.listValue [.atom 1, .atom 2, .atom 3]) &&
  expectCollectResult (resolve "Values")
    (.listValue [.sequenceValue [.atom 1, .atom 2, .atom 3]])

#guard dotReceiverSegmentCollectBoundaryMatrix

-- Allocation precedes supply consumption. F(first, *middle, last) with the
-- written pair receiver and one extra argument binds the whole receiver value
-- to the fixed prefix, collects nothing, and takes the suffix from the back.
def dotReceiverSegmentPrefixSuffixAlg : Algorithm :=
  algWithParameters [
    { name := "first", kind := .normal },
    { name := "middle", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .param "first", .param "middle", .param "last"
  ]

def dotReceiverSegmentFixedPrefixBindsValue : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverSegmentPrefixSuffixAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2]) "F" (some [.num 9])
  ])) with
  | Except.ok value =>
      reprStr value ==
        reprStr (Result.sequenceValue [.sequenceValue [.atom 1, .atom 2], .listValue [], .atom 9])
  | _ => false

#guard dotReceiverSegmentFixedPrefixBindsValue

-- The receiver segment's item count never satisfies arity: one segment
-- against two required fixed parameters is the ordinary minimum-arity error.
def dotReceiverSegmentCountNeverSatisfiesArity : Bool :=
  expectInnermostArityMismatch 2 1 (runFlat (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverSegmentPrefixSuffixAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2]) "F" none
  ])))

#guard dotReceiverSegmentCountNeverSatisfiesArity

-- F(*middle, last) with only the receiver segment: the fixed suffix binds the
-- receiver's one captured value and the collector collects the empty middle.
def dotReceiverSegmentSuffixAlg : Algorithm :=
  algWithParameters [
    { name := "middle", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .param "middle", .param "last"
  ]

def dotReceiverSegmentSuffixTakesReceiverWhole : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverSegmentSuffixAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2]) "F" none
  ])) with
  | Except.ok value =>
      reprStr value ==
        reprStr (Result.sequenceValue [.listValue [], .sequenceValue [.atom 1, .atom 2]])
  | _ => false

#guard dotReceiverSegmentSuffixTakesReceiverWhole

-- Scale(*values, factor) with an extra argument: the suffix takes the factor
-- and the collector consumes the written group receiver's supply.
def dotReceiverSegmentScaleConsumesSupplyAfterSuffix : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Scale", dotReceiverSegmentSuffixAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2, .num 3]) "Scale" (some [.num 10])
  ])) with
  | Except.ok value =>
      reprStr value ==
        reprStr (Result.sequenceValue [.listValue [.atom 1, .atom 2, .atom 3], .atom 10])
  | _ => false

#guard dotReceiverSegmentScaleConsumesSupplyAfterSuffix

-- Nested sequence-value parameter patterns keep one-boundary destructuring:
-- the receiver's written slots destructure through the pattern, and the
-- nested collecting binding is NOT fed the segment supply.
def dotReceiverSegmentNestedPatternAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "x", kind := .normal },
      .capture { name := "y", kind := .collecting },
      .capture { name := "z", kind := .normal }]
  ] [] [] [
    .param "x", .param "y", .param "z"
  ]

def dotReceiverSegmentNestedPatternKeepsOneBoundary : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverSegmentNestedPatternAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2, .num 3, .num 4]) "F" none
  ])) with
  | Except.ok value =>
      reprStr value ==
        reprStr (Result.sequenceValue [.atom 1, .listValue [.atom 2, .atom 3], .atom 4])
  | _ => false

#guard dotReceiverSegmentNestedPatternKeepsOneBoundary

--------------------------------------------------------------------------------
-- User-call parameter binding (movable collecting binding, preserved argument boundaries)
--------------------------------------------------------------------------------
-- F(x, *y, z) is a mixed fixed/collecting parameter list. The supplied call slots
-- are matched prefix/collecting/suffix without implicitly opening a grouped argument;
-- the collecting parameter collects its assigned middle slots as one exact immutable list.

def deconstructSumAlg : Algorithm :=
  algWithParameters [
    { name := "x" }, { name := "y", kind := .collecting }, { name := "z" }
  ] [] [] [
    .binary .add (.binary .add (.param "x") (.dotCall (.param "y") "sum" none)) (.param "z")
  ]

def deconstructFiveItems : List KatLang.Expr := [.num 1, .num 2, .num 3, .num 4, .num 5]
def deconstructFiveArg : Algorithm := alg [] [] [] deconstructFiveItems

-- F(1, 2, 3, 4, 5): five direct item slots.
def deconstructionDirectItemSupply : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructSumAlg)] [
    .call (resolve "F") deconstructFiveItems
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard deconstructionDirectItemSupply

-- F(A) where A = 1, 2, 3, 4, 5: one sequence-valued argument is supplied.
-- Function-call binding does not implicitly open it, so the mixed fixed/variadic
-- shape is under-supplied.
def deconstructionSingleGroupedArgumentRequiresSpread : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("F", deconstructSumAlg)] [
    .call (resolve "F") [resolve "A"]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | _ => false

#guard deconstructionSingleGroupedArgumentRequiresSpread

-- F(A*): explicit spread supplies five slots.
def deconstructionSpreadArgument : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("F", deconstructSumAlg)] [
    .call (resolve "F") [sequenceSpread (resolve "A")]
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard deconstructionSpreadArgument

-- F(1, 2): the collecting parameter collects zero items, so x = 1, y = [], z = 2 and y.sum = 0.
def deconstructionEmptyRest : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructSumAlg)] [
    .call (resolve "F") [.num 1, .num 2]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard deconstructionEmptyRest

-- p1, p2, *rest, q1, q2 against seven items binds the middle three to rest.
def deconstructionMatchAlg : Algorithm :=
  algWithParameters [
    { name := "p1" }, { name := "p2" }, { name := "rest", kind := .collecting },
    { name := "q1" }, { name := "q2" }
  ] [] [] [
    .param "p1", .param "p2", .dotCall (.param "rest") "count" none, .param "q1", .param "q2"
  ]

def deconstructionMatchingAlgorithm : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructionMatchAlg)] [
    .call (resolve "F") [.num 1, .num 2, .num 3, .num 4, .num 5, .num 6, .num 7]
  ])) with
  | Except.ok [1, 2, 3, 6, 7] => true
  | _ => false

#guard deconstructionMatchingAlgorithm

-- A single scalar argument is a one-item supply: F(first, *tail) with 1 binds
-- first = 1 and the collecting parameter collects [] (tail.count = 0).
def deconstructFirstTailAlg : Algorithm :=
  algWithParameters [{ name := "first" }, { name := "tail", kind := .collecting }] [] [] [
    .param "first", .dotCall (.param "tail") "count" none
  ]

def deconstructionScalarArgument : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructFirstTailAlg)] [
    .call (resolve "F") [.num 1]
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard deconstructionScalarArgument

-- A sequence-value parameter pattern also normalizes a scalar to a one-item
-- supply: F((first, *tail)) with the scalar 1 binds first = 1, tail = [].
def deconstructSequenceValueFirstTailAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "first" }, .capture { name := "tail", kind := .collecting }]
  ] [] [] [
    .param "first", .dotCall (.param "tail") "count" none
  ]

def sequenceValuePatternScalarArgument : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructSequenceValueFirstTailAlg)] [
    .call (resolve "F") [.num 1]
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard sequenceValuePatternScalarArgument

-- Parity guard: callback deconstruction is intentionally deferred, so the counted
-- callback path keeps the strict singleton-only scalar fallback that C#
-- `BindCountedParameterPattern` uses. Applying the same sequence-value
-- deconstruction callback to scalar map elements must fail (badArity), NOT silently
-- deconstruct each scalar into first/tail. This keeps the counted callback path from
-- accepting callback deconstruction before the C# path does.
def sequenceValueDeconstructionCallbackOnScalarFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", deconstructSequenceValueFirstTailAlg)] [
    .call (resolve "map") [
      sequenceItems [.num 1, .num 2, .num 3],
      .resolve "F"
    ]
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard sequenceValueDeconstructionCallbackOnScalarFails

-- Aspect 2 callback boundary (positive parity, mirrors C#
-- DeconstructionBindingTests.CallbackDeconstruction_OnSequenceValueRows_BindsPerRow):
-- a deconstruction-shaped callback applied per sequence-value row binds x/*y/z
-- within each row. With Rows = (1, 2, 3), (4, 5, 6) and F(x, *y, z) = x + y.sum + z,
-- Rows.map(F) is 6 and 15. Row callbacks work while scalar-element deconstruction
-- stays strict (see sequenceValueDeconstructionCallbackOnScalarFails above).
def deconstructionRowsAlg : Algorithm :=
  alg [] [] [] [
    sequenceItems [.num 1, .num 2, .num 3],
    sequenceItems [.num 4, .num 5, .num 6]
  ]

def deconstructionCallbackOnSequenceValueRows : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Rows", deconstructionRowsAlg),
    ("F", deconstructSumAlg)
  ] [
    .dotCall (resolve "Rows") "map" (some [resolve "F"])
  ])) with
  | Except.ok [6, 15] => true
  | _ => false

#guard deconstructionCallbackOnSequenceValueRows

-- A single collecting parameter collects the supplied call argument slots as one
-- exact list. One grouped argument is one collected element (`Sum(A)` binds
-- `values = [A]`, so the numeric `sum` constraint rejects the sequence
-- element), while separate slots collect their items.
def restOnlyCollectAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .dotCall (.param "values") "sum" none
  ]

def restOnlyConsumesItemSupply : Bool :=
  let singleGroupedArg :=
    match runResult (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("Sum", restOnlyCollectAlg)] [
      .call (resolve "Sum") [resolve "A"]
    ])) with
    | Except.error err => innermostIsBadArity err
    | _ => false
  let multipleSlots :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("Sum", restOnlyCollectAlg)] [
      .call (resolve "Sum") [.num 1, .num 2, .num 3]
    ])) with
    | Except.ok [6] => true
    | _ => false
  singleGroupedArg && multipleSlots

#guard restOnlyConsumesItemSupply

-- A FUNCTION-shaped argument (a builtin here) reaching a collecting binding reports
-- the targeted typeMismatch: a collecting binding collects VALUES and has no dual
-- algorithm channel. C#: `BindParameterPatternList` (same kind; the C#
-- message additionally names the collecting parameter).
def restFunctionShapedArgumentReportsTypeMismatch : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("G", algWithParameters [{ name := "fs", kind := .collecting }] [] [] [.param "fs"])
  ] [
    .call (resolve "G") [resolve "sum"]
  ])) with
  | Except.error err =>
      innermostIsTypeMismatch
        "A collecting parameter collects values, but a supplied argument is a function. Pass a value, or call the function so its result is collected."
        err
  | _ => false

#guard restFunctionShapedArgumentReportsTypeMismatch

-- A zero-parameter VALUE property whose body fails is NOT function-shaped
-- (`Algorithm.isFunctionShaped`): the genuine evaluation error surfaces
-- through the collecting binding instead of the function diagnostic.
def restErroredValuePropertyArgumentSurfacesRealError : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Bad", alg [] [] [] [.binary .div (.num 1) (.num 0)]),
    ("G", algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])
  ] [
    .call (resolve "G") [resolve "Bad"]
  ])) with
  | Except.error err => innermostIsDivByZero err
  | _ => false

#guard restErroredValuePropertyArgumentSurfacesRealError

def mixedVariadicBoundaryAlg : Algorithm :=
  algWithParameters [{ name := "first" }, { name := "rest", kind := .collecting }] [] [] [
    .dotCall (.param "first") "count" none,
    .dotCall (.param "rest") "count" none
  ]

def mixedVariadicPlainSequenceArgumentPreservesBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2]), ("G", mixedVariadicBoundaryAlg)] [
    .call (resolve "G") [resolve "A"]
  ])) with
  | Except.ok [2, 0] => true
  | _ => false

#guard mixedVariadicPlainSequenceArgumentPreservesBoundary

def mixedVariadicExplicitSpreadOpensSequenceArgument : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2]), ("G", mixedVariadicBoundaryAlg)] [
    .call (resolve "G") [sequenceSpread (resolve "A")]
  ])) with
  | Except.ok [1, 1] => true
  | _ => false

#guard mixedVariadicExplicitSpreadOpensSequenceArgument

def itemSupplySumAlg : Algorithm :=
  algWithParameters [{ name := "x", kind := .collecting }] [] [] [
    .dotCall (.param "x") "sum" none
  ]

-- Single-collecting `G(*x)` distinguishes grouped from spread supplies: `G(A)` and
-- the written-tuple call bind ONE collected sequence element (numeric `sum`
-- constraint error), while `G(A*)` and separate slots supply the items and
-- sum to 15.
def restOnlyItemSupplyDistinguishesGroupedFromSpread : Bool :=
  let sumsTo15 (args : List KatLang.Expr) : Bool :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("G", itemSupplySumAlg)] [
      .call (resolve "G") args
    ])) with
    | Except.ok [15] => true
    | _ => false
  let groupedFails (args : List KatLang.Expr) : Bool :=
    match runResult (.algorithmExpr (algPrivate [] [] [("A", deconstructFiveArg), ("G", itemSupplySumAlg)] [
      .call (resolve "G") args
    ])) with
    | Except.error err => innermostIsBadArity err
    | _ => false
  groupedFails [resolve "A"]
    && sumsTo15 [sequenceSpread (resolve "A")]
    && sumsTo15 deconstructFiveItems
    && groupedFails [.capture [.num 1, .num 2, .num 3, .num 4, .num 5]]

#guard restOnlyItemSupplyDistinguishesGroupedFromSpread

-- An empty call binds an empty item supply (min arity 0): `G()` sums to 0.
def restOnlyEmptyCallSumsToZero : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("G", itemSupplySumAlg)] [
    .call (resolve "G") []
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard restOnlyEmptyCallSumsToZero

def itemSupplyCountAlg : Algorithm :=
  algWithParameters [{ name := "x", kind := .collecting }] [] [] [
    .dotCall (.param "x") "count" none
  ]

-- Multiple sibling grouped values are preserved (G(A, B) binds
-- x = [(1, 2), (3, 4)], count 2), not auto-flattened; only explicit spread
-- opens them into one item supply (G(A*, B*) binds x = [1, 2, 3, 4], count 4).
def restOnlyPreservesSiblingGroupedValues : Bool :=
  let twoItemRoot (argExprs : List KatLang.Expr) : Algorithm :=
    algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4]),
      ("G", itemSupplyCountAlg)
    ] [ .call (resolve "G") argExprs ]
  let preserved :=
    match runFlat (.algorithmExpr (twoItemRoot [resolve "A", resolve "B"])) with
    | Except.ok [2] => true
    | _ => false
  let opened :=
    match runFlat (.algorithmExpr (twoItemRoot [sequenceSpread (resolve "A"), sequenceSpread (resolve "B")])) with
    | Except.ok [4] => true
    | _ => false
  preserved && opened

#guard restOnlyPreservesSiblingGroupedValues

def restPrefixSumAlg : Algorithm :=
  algWithParameters [{ name := "x", kind := .collecting }, { name := "y" }] [] [] [
    .binary .add (.dotCall (.param "x") "sum" none) (.param "y")
  ]

-- `(((1, 2, 3, 4, 5)))` is a doubly-nested singleton sequence value: a capture
-- whose single row is a capture of the five items.
def nestedSingletonFive : KatLang.Expr :=
  .capture [.capture [.num 1, .num 2, .num 3, .num 4, .num 5]]

-- Repeated singleton grouping is useful-structure canonicalized as a value, but
-- a function call still receives one argument unless `value*` /
-- `value*` is written.
def repeatedSingletonBoundaryDoesNotImplicitlyOpenCallArgument : Bool :=
  let plainMixed :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructSumAlg)] [
      .call (resolve "F") [nestedSingletonFive]
    ])) with
    | Except.error err => innermostIsArityMismatch 2 1 err
    | _ => false
  let spreadMixed :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("F", deconstructSumAlg)] [
      .call (resolve "F") [sequenceSpread nestedSingletonFive]
    ])) with
    | Except.ok [15] => true
    | _ => false
  plainMixed && spreadMixed

#guard repeatedSingletonBoundaryDoesNotImplicitlyOpenCallArgument

--------------------------------------------------------------------------------
-- Conditional branch arity invariants are Lean-enforced before evaluation
--------------------------------------------------------------------------------
-- runResultM validates every conditional in the algorithm tree: all branches
-- must share one top-level pattern arity and one top-level output arity.
-- Mirrors the C# parser's clause-elaboration checks.

-- F(0) = 1; F(x, y) = x + y → top-level pattern arities 1 vs 2.
def branchInputArityMismatchIsRejected : Bool :=
  let cond : Algorithm := .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 1] ⟩,
    ⟨ .sequenceValue [.bind "x", .bind "y"], alg [] [] [] [.binary .add (.param "x") (.param "y")] ⟩
  ]
  match runResult (.algorithmExpr (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") [.num 0]
  ])) with
  | Except.error err => innermostIsBranchArityMismatch "F" 1 2 err
  | _ => false

#guard branchInputArityMismatchIsRejected

-- F(0) = 1; F(x) = 1, 2 → top-level output arities 1 vs 2.
def branchOutputArityMismatchIsRejected : Bool :=
  let cond : Algorithm := .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 1, .num 2] ⟩
  ]
  match runResult (.algorithmExpr (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") [.num 0]
  ])) with
  | Except.error err => innermostIsBranchOutputArityMismatch "F" 1 2 err
  | _ => false

#guard branchOutputArityMismatchIsRejected

-- F((0, y)) = y; F((x, y)) = x + y → both branches have ONE top-level
-- pattern (a sequence-value pair); nested substructure may vary.
def sequenceValuePatternsWithSameTopLevelArityPass : Bool :=
  let cond : Algorithm := .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.litInt 0, .bind "y"]], alg [] [] [] [.param "y"] ⟩,
    ⟨ .sequenceValue [.sequenceValue [.bind "x", .bind "y"]], alg [] [] [] [.binary .add (.param "x") (.param "y")] ⟩
  ]
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") [.capture [.num 0, .num 5]],
    .call (resolve "F") [.capture [.num 1, .num 2]]
  ])) with
  | Except.ok [5, 3] => true
  | _ => false

#guard sequenceValuePatternsWithSameTopLevelArityPass

-- F(0) = 1, 2; F(x) = x, x → both branches emit TWO top-level outputs.
def uniformBranchOutputArityPasses : Bool :=
  let cond : Algorithm := .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 1, .num 2] ⟩,
    ⟨ .bind "x", alg [] [] [] [.param "x", .param "x"] ⟩
  ]
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") [.num 0],
    .call (resolve "F") [.num 7]
  ])) with
  | Except.ok [1, 2, 7, 7] => true
  | _ => false

#guard uniformBranchOutputArityPasses

-- Validation covers nested local algorithms and runs before evaluation:
-- an arity-violating conditional nested inside an inner property is rejected
-- even though nothing ever references it.
def nestedUnusedConditionalIsStillValidated : Bool :=
  let badCond : Algorithm := .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 1] ⟩,
    ⟨ .sequenceValue [.bind "x", .bind "y"], alg [] [] [] [.param "x"] ⟩
  ]
  let outer : Algorithm := algPrivate [] [] [("Bad", badCond)] [.num 1]
  match runResult (.algorithmExpr (algPrivate [] [] [("Outer", outer)] [.num 42])) with
  | Except.error err => innermostIsBranchArityMismatch "Bad" 1 2 err
  | _ => false

#guard nestedUnusedConditionalIsStillValidated

--------------------------------------------------------------------------------
-- builtin arity parity guards
--------------------------------------------------------------------------------
-- `builtinAcceptsArity` is the normative arity spec (mirrored by the C#
-- `BuiltinRegistry.AcceptsArity`), while `applyBuiltinCounted` enforces
-- arities structurally via pattern-match fall-through (`applyBuiltin`
-- inherits them as its Result projection). Nothing in the
-- model itself forces the two encodings to agree, so these guards sweep every
-- builtin across argument counts 0..6 on both dispatch paths:
--   - a rejected count must fail with an arity-mismatch error, and
--   - an accepted count must never fail with one. It may still fail for
--     value/domain reasons; domain rejections (empty-collection policy,
--     numeric item shape) deliberately bottom out in `badArity`, not
--     `arityMismatch`, so the two directions stay distinguishable.

inductive BuiltinApplyOutcome where
  | succeeded
  | arityRejected
  | failedOtherwise
  deriving BEq, Repr

def builtinProbeCtx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }

/-- Apply a builtin through both the plain and the counted dispatch path. -/
def builtinApplyResults (b : KatLang.Builtin) (args : List Algorithm)
    : List (Except Error Unit) :=
  [ (KatLang.runEvalM (KatLang.applyBuiltin b args builtinProbeCtx [])).map (fun _ => ()),
    (KatLang.runEvalM (KatLang.applyBuiltinCounted b args builtinProbeCtx [])).map (fun _ => ()) ]

def classifyBuiltinApply : Except Error Unit -> BuiltinApplyOutcome
  | .ok _ => .succeeded
  | .error err =>
      if innermostIsAnyArityMismatch err then .arityRejected else .failedOtherwise

def applyBuiltinOutcomes (b : KatLang.Builtin) (args : List Algorithm)
    : List BuiltinApplyOutcome :=
  (builtinApplyResults b args).map classifyBuiltinApply

-- Dummy arguments chosen to be valid for each builtin, so accepted counts
-- exercise real success paths instead of failing for unrelated reasons.

/-- Zero-parameter algorithm producing one numeric value. -/
def builtinProbeValueArg (n : Int) : Algorithm := alg [] [] [] [.num n]

/-- `count` distinct single-value arguments `1, 2, ...`. -/
def builtinProbeValueArgs (count : Nat) : List Algorithm :=
  (List.range count).map (fun i => builtinProbeValueArg (Int.ofNat i + 1))

/-- Valid `map` transform: identity. -/
def builtinProbeMapperArg : Algorithm := alg ["x"] [] [] [.param "x"]

/-- Valid `filter` predicate: keep everything. -/
def builtinProbePredicateArg : Algorithm := alg ["x"] [] [] [.num 1]

/-- Valid `reduce` step: numeric addition. -/
def builtinProbeReducerArg : Algorithm :=
  alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")]

/-- Loop step whose single output slot is a `0` continuation flag, so accepted
    `while` counts terminate after one step probe and accepted `repeat` counts
    pair it with repeat count `0`. -/
def builtinProbeLoopStepArg (paramCount : Nat) : Algorithm :=
  alg ((List.range paramCount).map (fun i => s!"s{i}")) [] [] [.num 0]

/-- Builtin-shaped dummy argument lists: suffix arguments (callbacks, counts,
    searched values) sit in their declared trailing positions, loop steps lead,
    and every remaining slot is a plain numeric value. Counts below the
    builtin's structural minimum just produce plain value lists, since those
    must be rejected before any argument is interpreted. -/
def builtinProbeArgsFor (b : KatLang.Builtin) (argCount : Nat) : List Algorithm :=
  match b with
  | .mapBuiltin =>
      if argCount == 0 then []
      else builtinProbeValueArgs (argCount - 1) ++ [builtinProbeMapperArg]
  | .filterBuiltin =>
      if argCount == 0 then []
      else builtinProbeValueArgs (argCount - 1) ++ [builtinProbePredicateArg]
  | .reduceBuiltin =>
      if argCount < 2 then builtinProbeValueArgs argCount
      else builtinProbeValueArgs (argCount - 2) ++ [builtinProbeReducerArg, builtinProbeValueArg 0]
  | .containsBuiltin | .takeBuiltin | .skipBuiltin =>
      if argCount == 0 then []
      else builtinProbeValueArgs (argCount - 1) ++ [builtinProbeValueArg 1]
  | .whileBuiltin =>
      if argCount == 0 then []
      else builtinProbeLoopStepArg (argCount - 1) :: builtinProbeValueArgs (argCount - 1)
  | .repeatBuiltin =>
      if argCount == 0 then []
      else if argCount == 1 then [builtinProbeLoopStepArg 0]
      else builtinProbeLoopStepArg (argCount - 2) :: builtinProbeValueArg 0
        :: builtinProbeValueArgs (argCount - 2)
  | _ => builtinProbeValueArgs argCount

/-- Every builtin is swept for spec/dispatch arity parity. -/
def builtinArityParityTargets : List KatLang.Builtin :=
  [ .ifBuiltin, .whileBuiltin, .repeatBuiltin, .atomsBuiltin,
    .rangeBuiltin, .filterBuiltin, .mapBuiltin, .orderBuiltin, .orderDescBuiltin,
    .countBuiltin, .containsBuiltin, .firstBuiltin, .lastBuiltin, .distinctBuiltin,
    .takeBuiltin, .skipBuiltin, .minBuiltin, .maxBuiltin, .sumBuiltin,
    .avgBuiltin, .reduceBuiltin ]

/-- Compile-time exhaustiveness pin: this match is deliberately wildcard-free,
    so adding a `Builtin` constructor stops compiling here until the new
    builtin is routed into `builtinArityParityTargets`. -/
def builtinArityParitySweepCovers (b : KatLang.Builtin) : Bool :=
  match b with
  | .ifBuiltin | .whileBuiltin | .repeatBuiltin | .atomsBuiltin
  | .rangeBuiltin | .filterBuiltin | .mapBuiltin | .orderBuiltin | .orderDescBuiltin
  | .countBuiltin | .containsBuiltin | .firstBuiltin | .lastBuiltin | .distinctBuiltin
  | .takeBuiltin | .skipBuiltin | .minBuiltin | .maxBuiltin | .sumBuiltin
  | .avgBuiltin | .reduceBuiltin => builtinArityParityTargets.contains b

#guard builtinArityParityTargets.all builtinArityParitySweepCovers

/-- Spec/dispatch arity parity for one builtin across counts `0..maxArgCount`:
    `builtinAcceptsArity b n = false` must surface as an arity rejection, and
    `= true` must never. -/
def builtinArityParityHolds (b : KatLang.Builtin) (maxArgCount : Nat := 6) : Bool :=
  (List.range (maxArgCount + 1)).all fun argCount =>
    let expectAccepted := KatLang.builtinAcceptsArity b argCount
    (applyBuiltinOutcomes b (builtinProbeArgsFor b argCount)).all fun outcome =>
      if expectAccepted then outcome != .arityRejected else outcome == .arityRejected

/-- Display names of builtins violating arity parity; `#eval` this on guard
    failure to see which builtin and then probe its counts directly. -/
def builtinsFailingArityParity : List String :=
  (builtinArityParityTargets.filter (fun b => !(builtinArityParityHolds b))).map
    KatLang.builtinDisplayName

#guard builtinsFailingArityParity == []

-- Keep the probe arguments honest: representative accepted counts must
-- actually succeed (not merely avoid arity errors), so a silently broken
-- dummy argument cannot make the accepted direction of the sweep vacuous.
-- Covers each builtin's accepted count (fixed-arity builtins have exactly
-- one) plus one extra-argument count for the variable-arity loop builtins
-- (`while`/`repeat`).
def builtinAcceptedAritySpotCases : List (KatLang.Builtin × Nat) :=
  [ (.ifBuiltin, 3),
    (.whileBuiltin, 2), (.whileBuiltin, 4),
    (.repeatBuiltin, 3), (.repeatBuiltin, 5),
    (.atomsBuiltin, 1), (.rangeBuiltin, 2),
    (.countBuiltin, 1),
    (.sumBuiltin, 1),
    (.avgBuiltin, 1), (.minBuiltin, 1), (.maxBuiltin, 1),
    (.firstBuiltin, 1), (.lastBuiltin, 1),
    (.distinctBuiltin, 1),
    (.orderBuiltin, 1), (.orderDescBuiltin, 1),
    (.mapBuiltin, 2),
    (.filterBuiltin, 2),
    (.containsBuiltin, 2),
    (.takeBuiltin, 2),
    (.skipBuiltin, 2),
    (.reduceBuiltin, 3) ]

def builtinAcceptedAritySpotFailures : List String :=
  (builtinAcceptedAritySpotCases.filter (fun (b, argCount) =>
    (applyBuiltinOutcomes b (builtinProbeArgsFor b argCount)).any (· != .succeeded))).map
    (fun (b, argCount) => s!"{KatLang.builtinDisplayName b}@{argCount}")

#guard builtinAcceptedAritySpotFailures == []

-- Accepted count does not promise success: the empty-collection policy rejects
-- `first(())`-style calls at the accepted count 1 with a non-arity diagnostic.
-- Pin that distinction so the accepted direction of the sweep stays meaningful.
def builtinEmptyPolicyFailuresAreNotArityErrors : Bool :=
  let emptyArg := alg [] [] [] []
  [KatLang.Builtin.firstBuiltin, .lastBuiltin, .minBuiltin, .maxBuiltin, .avgBuiltin].all
    fun b =>
      KatLang.builtinAcceptsArity b 1
      && (applyBuiltinOutcomes b [emptyArg]).all (· == .failedOtherwise)

#guard builtinEmptyPolicyFailuresAreNotArityErrors

--------------------------------------------------------------------------------
-- builtin projection parity guards
--------------------------------------------------------------------------------
-- `applyBuiltin` must behave as the Result projection of `applyBuiltinCounted`:
--   applyBuiltin b args == Prod.fst <$> applyBuiltinCounted b args
-- including identical error diagnostics and identical final evaluator state
-- (per-run zero-arg property cache). These guards pin that equivalence so the
-- non-counted path can delegate to the counted path instead of duplicating
-- builtin semantics.

def builtinProjectionParityAt (b : KatLang.Builtin) (args : List Algorithm) : Bool :=
  let plain := (KatLang.applyBuiltin b args builtinProbeCtx []).run KatLang.EvalState.empty
  let counted := (KatLang.applyBuiltinCounted b args builtinProbeCtx []).run KatLang.EvalState.empty
  match plain, counted with
  | .ok (value, plainState), .ok ((countedValue, _), countedState) =>
      value == countedValue && reprStr plainState == reprStr countedState
  | .error plainErr, .error countedErr => reprStr plainErr == reprStr countedErr
  | _, _ => false

/-- Sweep the same builtin/argument-count matrix as the arity parity guards:
    valid calls, arity-rejected calls, and empty-collection domain failures
    must all project identically. -/
def builtinsFailingProjectionParity : List String :=
  (builtinArityParityTargets.filter (fun b =>
    !((List.range 7).all fun argCount =>
      builtinProjectionParityAt b (builtinProbeArgsFor b argCount)))).map
    KatLang.builtinDisplayName

#guard builtinsFailingProjectionParity == []

-- Probe shapes for cases the uniform matrix does not reach: branch forcing
-- through the counted/non-counted output cores, cache-writing property
-- access, loops that actually iterate, and per-builtin domain failures.

/-- Branch emitting two top-level outputs. -/
def builtinProbeMultiOutputArg : Algorithm := alg [] [] [] [.num 1, .num 2]

/-- Branch emitting one sequence value. -/
def builtinProbeSequenceValueOutputArg : Algorithm :=
  alg [] [] [] [.capture [.num 1, .num 2]]

/-- Branch with no output: forcing it raises `missingOutput`. -/
def builtinProbeEmptyOutputArg : Algorithm := alg [] [] [] []

/-- Branch whose output reads a cacheable zero-arg property twice, so both
    dispatch paths must leave the same per-run cache state behind. -/
def builtinProbeCachedPropArg : Algorithm :=
  algPrivate [] [] [("P", alg [] [] [] [.num 7])] [.resolve "P", .resolve "P"]

/-- `while` step `(x - 1, x - 1)`: iterates until the state reaches zero. -/
def builtinProbeDecrementStepArg : Algorithm :=
  alg ["x"] [] [] [.binary .sub (.param "x") (.num 1), .binary .sub (.param "x") (.num 1)]

/-- `repeat` step `x + 1`. -/
def builtinProbeIncrementStepArg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

/-- (label, builtin, args, expected outcome on both dispatch paths). The
    expected outcome keeps each case honest: a typo cannot silently turn an
    intended success case into two identical failures. -/
def builtinProjectionExplicitCases
    : List (String × KatLang.Builtin × List Algorithm × BuiltinApplyOutcome) :=
  [ ("if/multi-output-branch", .ifBuiltin,
      [builtinProbeValueArg 1, builtinProbeMultiOutputArg, builtinProbeValueArg 9], .succeeded),
    ("if/sequenceValue-else-branch", .ifBuiltin,
      [builtinProbeValueArg 0, builtinProbeValueArg 9, builtinProbeSequenceValueOutputArg], .succeeded),
    ("if/cached-property-branch", .ifBuiltin,
      [builtinProbeValueArg 1, builtinProbeCachedPropArg, builtinProbeValueArg 9], .succeeded),
    ("if/missing-output-branch", .ifBuiltin,
      [builtinProbeValueArg 1, builtinProbeEmptyOutputArg, builtinProbeValueArg 9], .failedOtherwise),
    -- `truthValue?` flattens the condition and reads its first numeric atom,
    -- so a sequence-value condition is truthy; only atom-free conditions are invalid.
    ("if/sequenceValue-condition-truthy", .ifBuiltin,
      [builtinProbeSequenceValueOutputArg, builtinProbeValueArg 1, builtinProbeValueArg 2], .succeeded),
    ("if/atom-free-condition", .ifBuiltin,
      [alg [] [] [] [.emptySequence 0], builtinProbeValueArg 1, builtinProbeValueArg 2],
      .failedOtherwise),
    ("while/iterates", .whileBuiltin,
      [builtinProbeDecrementStepArg, builtinProbeValueArg 2], .succeeded),
    ("repeat/iterates", .repeatBuiltin,
      [builtinProbeIncrementStepArg, builtinProbeValueArg 2, builtinProbeValueArg 5], .succeeded),
    ("repeat/negative-count", .repeatBuiltin,
      [builtinProbeLoopStepArg 1, builtinProbeValueArg (-1), builtinProbeValueArg 5], .failedOtherwise),
    ("order/sequenceValue-item", .orderBuiltin, [builtinProbeSequenceValueOutputArg], .succeeded),
    ("avg/empty-collection", .avgBuiltin, [builtinProbeEmptyOutputArg], .failedOtherwise),
    ("take/non-numeric-count", .takeBuiltin,
      [builtinProbeValueArg 1, builtinProbeSequenceValueOutputArg], .failedOtherwise) ]

def builtinProjectionExplicitCaseFailures : List String :=
  (builtinProjectionExplicitCases.filter (fun (_, b, args, expected) =>
    !(builtinProjectionParityAt b args
      && (applyBuiltinOutcomes b args).all (· == expected)))).map
    (fun (label, _, _, _) => label)

#guard builtinProjectionExplicitCaseFailures == []

--------------------------------------------------------------------------------
-- issue #130: counted `if` collapses a multi-output branch to one value
--------------------------------------------------------------------------------
-- The selected `if` branch is one argument expression, so `if` observes it as a
-- single value boundary -- exactly like value-position property access. A
-- multi-output branch property such as `X = 1, 2, 3` therefore yields the grouped
-- sequence value `(1, 2, 3)` with emitted count 1, not three separate outputs.
-- (Contrast `while`/`repeat`, whose multi-slot loop state is intentional.) These
-- guards pin the emitted count exactly, which the `.succeeded` projection-parity
-- cases above do not constrain.

/-- Branch property emitting three top-level outputs (`X = 1, 2, 3`). -/
def ifBranchThreeOutputs : Algorithm := alg [] [] [] [.num 1, .num 2, .num 3]

/-- Branch property emitting three other outputs (`Y = 10, 20, 30`). -/
def ifBranchThreeOutputsAlt : Algorithm := alg [] [] [] [.num 10, .num 20, .num 30]

/-- Already-grouped branch property (`X = (1, 2, 3)`). -/
def ifBranchSequenceValue : Algorithm :=
  alg [] [] [] [.capture [.num 1, .num 2, .num 3]]

/-- Run counted `if` with an integer condition and two branch algorithms. -/
def ifCountedResult (cond : Int) (t e : Algorithm) : Except KatLang.Error KatLang.CountedResult :=
  match (KatLang.applyBuiltinCounted .ifBuiltin
      [builtinProbeValueArg cond, t, e] builtinProbeCtx []).run KatLang.EvalState.empty with
  | .ok (counted, _) => .ok counted
  | .error err => .error err

def ifCountedCollapsesMultiOutputTrueBranch : Bool :=
  match ifCountedResult 1 ifBranchThreeOutputs ifBranchThreeOutputs with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard ifCountedCollapsesMultiOutputTrueBranch

def ifCountedCollapsesMultiOutputFalseBranch : Bool :=
  match ifCountedResult 0 ifBranchThreeOutputs ifBranchThreeOutputs with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard ifCountedCollapsesMultiOutputFalseBranch

def ifCountedDistinctBranchesTrueSelectsThen : Bool :=
  match ifCountedResult 1 ifBranchThreeOutputs ifBranchThreeOutputsAlt with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard ifCountedDistinctBranchesTrueSelectsThen

def ifCountedDistinctBranchesFalseSelectsElse : Bool :=
  match ifCountedResult 0 ifBranchThreeOutputs ifBranchThreeOutputsAlt with
  | .ok (Result.sequenceValue [Result.atom 10, Result.atom 20, Result.atom 30], 1) => true
  | _ => false

#guard ifCountedDistinctBranchesFalseSelectsElse

def ifCountedParenthesizedBranchStaysOneValue : Bool :=
  match ifCountedResult 1 ifBranchSequenceValue ifBranchSequenceValue with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard ifCountedParenthesizedBranchStaysOneValue

--------------------------------------------------------------------------------
-- issue #131: explicit spread opens a value into `if`'s three argument slots
--------------------------------------------------------------------------------
-- An explicit spread argument (`if(X*)`) has a runtime-only count. The C#
-- parser is the only layer that gated `if` arity statically; the shared
-- evaluator already expands spread before applying counted `if`, via
-- `applyBuiltinCountedResolved -> expandSequenceSpreadBuiltinArguments`. So a
-- spread of `1, 2, 3` opens into the three argument slots and selects `whenTrue`
-- (2) as one value, matching the user wrapper `MyIF(a, b, c) = if(a, b, c)`.
-- This guard witnesses that no Lean evaluator change was needed for #131.

/-- One spread argument whose value opens to three top-level items (`X*`). -/
def ifSpreadThreeItemsArg : KatLang.ResolvedArgumentAlgorithm :=
  { algorithm := ifBranchThreeOutputs, spreadsSequence := true }

/-- Run counted `if` through the resolved, spread-aware builtin entry point. -/
def ifCountedResolvedResult (args : List KatLang.ResolvedArgumentAlgorithm)
    : Except KatLang.Error KatLang.CountedResult :=
  match (KatLang.applyBuiltinCountedResolved .ifBuiltin args builtinProbeCtx []).run
      KatLang.EvalState.empty with
  | .ok (counted, _) => .ok counted
  | .error err => .error err

def ifSpreadArgumentOpensIntoThreeArguments : Bool :=
  match ifCountedResolvedResult [ifSpreadThreeItemsArg] with
  | .ok (Result.atom 2, 1) => true
  | _ => false

#guard ifSpreadArgumentOpensIntoThreeArguments

-- The same holds when the spread operand is an already-grouped (count-1) value
-- `(1, 2, 3)*`: the spread supplies its items, so the argument still expands to
-- three slots. This mirrors the C# engine test for `TrueResult = (1, 2, 3)`.
def ifSpreadGroupedOperandArg : KatLang.ResolvedArgumentAlgorithm :=
  { algorithm := alg [] [] [] [.sequenceSpread (.algorithmExpr ifBranchThreeOutputs)],
    spreadsSequence := true }

def ifSpreadGroupedOperandOpensIntoThreeArguments : Bool :=
  match ifCountedResolvedResult [ifSpreadGroupedOperandArg] with
  | .ok (Result.atom 2, 1) => true
  | _ => false

#guard ifSpreadGroupedOperandOpensIntoThreeArguments

--------------------------------------------------------------------------------
-- property/call/builtin boundary arity = 1 (reCountValueBoundary)
--------------------------------------------------------------------------------
-- A property/call/builtin RESULT boundary always returns ONE value: a body or
-- collection that internally produces an item supply is observed by the caller
-- as one sequence value (emitted count 1). Only an explicit caller-site
-- `value*` slot re-spreads it. Root output is NOT a call
-- boundary and keeps its slot count;
-- `while`/`repeat` loop state and the strict map/reduce callback paths are also
-- unchanged. These guards pin the emitted count exactly. Lean: reCountValueBoundary.

/-- Evaluate a whole program counted, mirroring `runResultM` but preserving the
    root emitted count, so a boundary returning one value shows count 1 while the
    root output list still shows its slot count. -/
def runCountedProgram (e : KatLang.Expr) : Except KatLang.Error KatLang.CountedResult :=
  let ctx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg], algEnv := [] }
  KatLang.runEvalM
    (match e with
     | .algorithmExpr a =>
         let wired := KatLang.wireToCaller ctx a
         if (KatLang.Algorithm.params wired).length = 0 then
           KatLang.evalAlgOutputCounted wired ctx []
         else
           .error (KatLang.Error.unresolvedImplicitParams (KatLang.Algorithm.params wired))
     | _ => KatLang.evalCounted e ctx [])

/-- `F(*a) = a` then `F(5, 9)`. -/
def boundaryVariadicReturnAlg : Algorithm :=
  algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"]

def boundaryVariadicReturnRoot (body : List KatLang.Expr) : Algorithm :=
  algPrivate [] [] [("F", algWithParameters [{ name := "a", kind := .collecting }] [] [] body)]
    [.call (.resolve "F") [.num 5, .num 9]]

def boundaryVariadicReturnIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (boundaryVariadicReturnRoot [.param "a"])) with
  | .ok (Result.listValue [Result.atom 5, Result.atom 9], 1) => true
  | _ => false

#guard boundaryVariadicReturnIsOneValue

/-- `F(*a) = a*` then `F(5, 9)` -- the body spread opens the capture, but the
    call boundary still returns one value. -/
def boundaryVariadicBodySpreadIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (boundaryVariadicReturnRoot [sequenceSpread (.param "a")])) with
  | .ok (Result.sequenceValue [Result.atom 5, Result.atom 9], 1) => true
  | _ => false

#guard boundaryVariadicBodySpreadIsOneValue

/-- `F(*a) = a, 0` then `F(5, 9)` -- the collected list stays one nested list value. -/
def boundaryVariadicCommaSlotGroupsCapture : Bool :=
  match runCountedProgram (.algorithmExpr (boundaryVariadicReturnRoot [.param "a", .num 0])) with
  | .ok (Result.sequenceValue [Result.listValue [Result.atom 5, Result.atom 9], Result.atom 0], 1) => true
  | _ => false

#guard boundaryVariadicCommaSlotGroupsCapture

/-- `F(*a) = a*, 0` then `F(5, 9)` -- body spread flattens, boundary still one value. -/
def boundaryVariadicBodySpreadThenSlotIsOneFlatValue : Bool :=
  match runCountedProgram (.algorithmExpr (boundaryVariadicReturnRoot [sequenceSpread (.param "a"), .num 0])) with
  | .ok (Result.sequenceValue [Result.atom 5, Result.atom 9, Result.atom 0], 1) => true
  | _ => false

#guard boundaryVariadicBodySpreadThenSlotIsOneFlatValue

/-- `F(*a) = a` then `F(5, 9)*` -- caller-site spread turns the returned value back into an item supply. -/
def boundaryCallerSpreadOpensReturnedValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("F", boundaryVariadicReturnAlg)]
      [sequenceSpread (.call (.resolve "F") [.num 5, .num 9])])) with
  | .ok (Result.sequenceValue [Result.atom 5, Result.atom 9], 2) => true
  | _ => false

#guard boundaryCallerSpreadOpensReturnedValue

/-- `X = 1, 2, 3` accessed three ways: lexical `X`, explicit call `X()`, and the
    multi-output property body. -/
def boundaryMultiOutputProp : Algorithm := alg [] [] [] [.num 1, .num 2, .num 3]

def boundaryLexicalAccessIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundaryMultiOutputProp)] [.resolve "X"])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryLexicalAccessIsOneValue

def boundaryExplicitZeroArgCallIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundaryMultiOutputProp)]
      [.call (.resolve "X") []])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryExplicitZeroArgCallIsOneValue

/-- Structural dot zero-arg access `M.P` now matches lexical access (count 1). -/
def boundaryStructuralHolder : Algorithm :=
  alg [] [] [publicProp "P" boundaryMultiOutputProp] [.num 0]

def boundaryStructuralDotAccessIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("M", boundaryStructuralHolder)]
      [.dotCall (.resolve "M") "P" none])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryStructuralDotAccessIsOneValue

/-- Collection-producing builtin `order` returns one exact list value; spread
    opens it. -/
def boundaryOrderIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", alg [] [] [] [.num 3, .num 1, .num 2])]
      [.dotCall (.resolve "X") "order" none])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryOrderIsOneValue

def boundaryOrderSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", alg [] [] [] [.num 3, .num 1, .num 2])]
      [sequenceSpread (.dotCall (.resolve "X") "order" none)])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryOrderSpreadOpensItems

/-- `range(1, 3)` is a collection-producing builtin: one exact list value,
    opened by spread. -/
def boundaryRangeIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] []
      [.call (.resolve "range") [.num 1, .num 3]])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryRangeIsOneValue

/-- `F(*a) = a.sum` sums the exact collected list through the builtin's
    post-binding collection view. -/
def boundaryVariadicForwardingUsesCollectedListView : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] []
      [("F", algWithParameters [{ name := "a", kind := .collecting }] [] []
        [.dotCall (.param "a") "sum" none])]
      [.call (.resolve "F") [.num 5, .num 9]])) with
  | .ok (Result.atom 14, 1) => true
  | _ => false

#guard boundaryVariadicForwardingUsesCollectedListView

/-- Regression: root output is NOT a call boundary and stays multi-output. -/
def boundaryRootOutputStaysMultiOutput : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [] [.num 1, .num 2, .num 3])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryRootOutputStaysMultiOutput

/-- Regression: redundant empty sequence nesting canonicalizes before the
    boundary re-count observes it. -/
def boundaryCanonicalizesNestedEmptySequence : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("F", alg [] [] [] [.emptySequence 1])] [.resolve "F"])) with
  | .ok (Result.sequenceValue [], 1) => true
  | _ => false

#guard boundaryCanonicalizesNestedEmptySequence

-- Collection-producing builtin parity: each returns one exact list value (count 1)
-- at the call/property boundary; caller-site `value*`
-- opens it into an item supply.
-- (`order` and `range` are covered by the guards above.)

def boundaryDesc312 : Algorithm := alg [] [] [] [.num 3, .num 1, .num 2]
def boundary123 : Algorithm := alg [] [] [] [.num 1, .num 2, .num 3]

/-- `X.orderDesc` is one value; `X.orderDesc*` opens it. -/
def boundaryOrderDescIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundaryDesc312)]
      [.dotCall (.resolve "X") "orderDesc" none])) with
  | .ok (Result.listValue [Result.atom 3, Result.atom 2, Result.atom 1], 1) => true
  | _ => false

#guard boundaryOrderDescIsOneValue

def boundaryOrderDescSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundaryDesc312)]
      [sequenceSpread (.dotCall (.resolve "X") "orderDesc" none)])) with
  | .ok (Result.sequenceValue [Result.atom 3, Result.atom 2, Result.atom 1], 3) => true
  | _ => false

#guard boundaryOrderDescSpreadOpensItems

/-- `X.distinct` is one value; `X.distinct*` opens it. -/
def boundaryDistinctIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", alg [] [] [] [.num 1, .num 1, .num 2, .num 3])]
      [.dotCall (.resolve "X") "distinct" none])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryDistinctIsOneValue

def boundaryDistinctSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", alg [] [] [] [.num 1, .num 1, .num 2, .num 3])]
      [sequenceSpread (.dotCall (.resolve "X") "distinct" none)])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryDistinctSpreadOpensItems

/-- `X.take(2)` is one value. -/
def boundaryTakeIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundary123)]
      [.dotCall (.resolve "X") "take" (some [.num 2])])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2], 1) => true
  | _ => false

#guard boundaryTakeIsOneValue

/-- `X.skip(1)` is one value; `X.skip(1)*` opens it. -/
def boundarySkipIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundary123)]
      [.dotCall (.resolve "X") "skip" (some [.num 1])])) with
  | .ok (Result.listValue [Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundarySkipIsOneValue

def boundarySkipSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundary123)]
      [sequenceSpread (.dotCall (.resolve "X") "skip" (some [.num 1]))])) with
  | .ok (Result.sequenceValue [Result.atom 2, Result.atom 3], 2) => true
  | _ => false

#guard boundarySkipSpreadOpensItems

/-- `X.filter(IsBig)` (with `IsBig(x) = x > 1`) is one value; caller-side spread opens it. -/
def boundaryFilterPredicate : Algorithm := alg ["x"] [] [] [.binary .gt (.param "x") (.num 1)]

def boundaryFilterIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("IsBig", boundaryFilterPredicate), ("X", boundary123)]
      [.dotCall (.resolve "X") "filter" (some [.resolve "IsBig"])])) with
  | .ok (Result.listValue [Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryFilterIsOneValue

def boundaryFilterSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("IsBig", boundaryFilterPredicate), ("X", boundary123)]
      [sequenceSpread (.dotCall (.resolve "X") "filter" (some [.resolve "IsBig"]))])) with
  | .ok (Result.sequenceValue [Result.atom 2, Result.atom 3], 2) => true
  | _ => false

#guard boundaryFilterSpreadOpensItems

/-- `X.map(Double)` (with `Double(x) = x * 2`) is one value; caller-side spread opens it. -/
def boundaryMapTransform : Algorithm := alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]

def boundaryMapIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("Double", boundaryMapTransform), ("X", boundary123)]
      [.dotCall (.resolve "X") "map" (some [.resolve "Double"])])) with
  | .ok (Result.listValue [Result.atom 2, Result.atom 4, Result.atom 6], 1) => true
  | _ => false

#guard boundaryMapIsOneValue

def boundaryMapSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("Double", boundaryMapTransform), ("X", boundary123)]
      [sequenceSpread (.dotCall (.resolve "X") "map" (some [.resolve "Double"]))])) with
  | .ok (Result.sequenceValue [Result.atom 2, Result.atom 4, Result.atom 6], 3) => true
  | _ => false

#guard boundaryMapSpreadOpensItems

/-- `atoms((1, (2, 3)))` is ONE exact list value `[1, 2, 3]`;
    `atoms(...)*` opens the one list boundary into three items. -/
def boundaryAtomsArg : List KatLang.Expr := [sequenceItems [.num 1, sequenceItems [.num 2, .num 3]]]

def boundaryAtomsIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] []
      [.call (.resolve "atoms") boundaryAtomsArg])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryAtomsIsOneValue

def boundaryAtomsSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] []
      [sequenceSpread (.call (.resolve "atoms") boundaryAtomsArg)])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryAtomsSpreadOpensItems

--------------------------------------------------------------------------------
-- atoms builtin: recursive list traversal and exact-list results (issue #136)
--------------------------------------------------------------------------------
-- `atoms` materializes ONE exact immutable list of the recursively collected
-- numeric atoms: sequence AND list boundaries open depth-first, left to right;
-- strings contribute no atoms; the result kind never depends on the input
-- kind, and the emitted count is always 1 (including the empty result `[]`).
-- Truth testing stays list-opaque (`Result.atoms`), so none of these guards
-- changes any `if` outcome — see the truth-value non-regression guards below.

def atomsCallOn (argBody : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [] [.call (.resolve "atoms") argBody])

def atomsNumberIsSingletonList : Bool :=
  match runCountedProgram (atomsCallOn [.num 7]) with
  | .ok (Result.listValue [Result.atom 7], 1) => true
  | _ => false

#guard atomsNumberIsSingletonList

def atomsStringIsEmptyList : Bool :=
  match runCountedProgram (atomsCallOn [.stringLiteral "text"]) with
  | .ok (Result.listValue [], 1) => true
  | _ => false

#guard atomsStringIsEmptyList

def atomsEmptySequenceIsEmptyList : Bool :=
  match runCountedProgram (atomsCallOn [.emptySequence 0]) with
  | .ok (Result.listValue [], 1) => true
  | _ => false

#guard atomsEmptySequenceIsEmptyList

def atomsEmptyListIsEmptyList : Bool :=
  match runCountedProgram (atomsCallOn [.listLiteral []]) with
  | .ok (Result.listValue [], 1) => true
  | _ => false

#guard atomsEmptyListIsEmptyList

-- atoms([1, 2]) → [1, 2] (lists are traversed, not opaque)
def atomsListTraversalIsExactList : Bool :=
  match runCountedProgram (atomsCallOn [.listLiteral [.num 1, .num 2]]) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2], 1) => true
  | _ => false

#guard atomsListTraversalIsExactList

-- atoms([[1, 2], [3, 4]]) → [1, 2, 3, 4]
def atomsNestedListsFlatten : Bool :=
  match runCountedProgram (atomsCallOn [.listLiteral [
      .listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]]) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3, Result.atom 4], 1) => true
  | _ => false

#guard atomsNestedListsFlatten

-- atoms([(1, 2), [3, [4]], 5]) → [1, 2, 3, 4, 5]
def atomsMixedStructuresFlatten : Bool :=
  match runCountedProgram (atomsCallOn [.listLiteral [
      .capture [.num 1, .num 2],
      .listLiteral [.num 3, .listLiteral [.num 4]],
      .num 5]]) with
  | .ok (Result.listValue
      [Result.atom 1, Result.atom 2, Result.atom 3, Result.atom 4, Result.atom 5], 1) => true
  | _ => false

#guard atomsMixedStructuresFlatten

-- atoms([3, (1, [4, 2])]) → [3, 1, 4, 2] (structural left-to-right order)
def atomsPreservesLeftToRightOrder : Bool :=
  match runCountedProgram (atomsCallOn [.listLiteral [
      .num 3,
      .capture [.num 1, .listLiteral [.num 4, .num 2]]]]) with
  | .ok (Result.listValue [Result.atom 3, Result.atom 1, Result.atom 4, Result.atom 2], 1) => true
  | _ => false

#guard atomsPreservesLeftToRightOrder

-- [1, 2, 3].skip(1).atoms → [2, 3] (builtin-produced lists compose directly)
def atomsComposesWithListProducingBuiltins : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] []
      [.dotCall (.dotCall (.listLiteral [.num 1, .num 2, .num 3]) "skip"
          (some [.num 1])) "atoms" none])) with
  | .ok (Result.listValue [Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard atomsComposesWithListProducingBuiltins

-- The three atom views stay distinct on a list-bearing value: language
-- collection opens lists, truth flattening does not, host flattening agrees
-- with language collection on numeric content.
def atomViewSeparationValue : Result :=
  Result.listValue [Result.atom 1, Result.sequenceValue [Result.atom 2], Result.str "s"]

#guard Result.languageAtoms atomViewSeparationValue == [1, 2]
#guard Result.atoms atomViewSeparationValue == []
#guard Result.hostAtoms atomViewSeparationValue == [1, 2]
#guard Result.truthValue? atomViewSeparationValue == none

--------------------------------------------------------------------------------
-- truth-value non-regression guards (atoms/#136 must not change truthiness)
--------------------------------------------------------------------------------
-- `truthValue?` still reads the sequence-only `Result.atoms` view: lists have
-- no truth value, and list elements inside sequence conditions are skipped.

def truthIfCall (cond : KatLang.Expr) : KatLang.Expr :=
  .call (.resolve "if") [cond, .num 10, .num 20]

def ifListConditionStillInvalid : Bool :=
  match runFlat (truthIfCall (.listLiteral [.num 1])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard ifListConditionStillInvalid

def ifEmptyListConditionStillInvalid : Bool :=
  match runFlat (truthIfCall (.listLiteral [])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard ifEmptyListConditionStillInvalid

def ifZeroListConditionStillInvalid : Bool :=
  match runFlat (truthIfCall (.listLiteral [.num 0])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard ifZeroListConditionStillInvalid

def ifNestedListConditionStillInvalid : Bool :=
  match runFlat (truthIfCall (.listLiteral [.listLiteral [.num 1]])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard ifNestedListConditionStillInvalid

-- if((1, [2]), 10, 20) → 10: the list element is skipped, first atom 1 decides
def ifMixedConditionReadsFirstNumericAtom : Bool :=
  match runFlat (truthIfCall (.capture [.num 1, .listLiteral [.num 2]])) with
  | Except.ok [10] => true
  | _ => false

#guard ifMixedConditionReadsFirstNumericAtom

-- if(([1], 0), 10, 20) → 20: the leading list is skipped, first atom 0 decides
def ifMixedConditionSkipsLeadingListElement : Bool :=
  match runFlat (truthIfCall (.capture [.listLiteral [.num 1], .num 0])) with
  | Except.ok [20] => true
  | _ => false

#guard ifMixedConditionSkipsLeadingListElement

-- if(atoms((1, 2)), 10, 20) is invalid: the atoms result is a list like any
-- other, so `atoms` introduces no list truthiness.
def ifAtomsResultConditionInvalid : Bool :=
  match runFlat (truthIfCall (.call (.resolve "atoms") [.capture [.num 1, .num 2]])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard ifAtomsResultConditionInvalid

--------------------------------------------------------------------------------
-- dot-call projection parity guards
--------------------------------------------------------------------------------
-- `evalDotCall` and `evalDotCallCounted` currently duplicate dot-call
-- dispatch: receiver resolution, structural lookup, lexical fallback with
-- receiver injection, zero-arg property access, conditional value-position
-- dispatch, and the receiver-spreading rules. These guards pin representative
-- projection parity
--   evalDotCall target name args == Prod.fst <$> evalDotCallCounted target name args
-- from identical initial state: equal Result values on success, equal error
-- diagnostics on failure (compared via Repr, so context wording is pinned),
-- and equal final evaluator state (per-run zero-arg property cache). They are
-- groundwork for a possible future delegation rewrite, which is deliberately
-- NOT performed here.

-- Choose(0, y) = y; Choose(x, y) = x + y
def dotCallParityChooseAlg : Algorithm := .conditional none [] [
  ⟨ .sequenceValue [.litInt 0, .bind "y"], alg [] [] [] [.param "y"] ⟩,
  ⟨ .sequenceValue [.bind "x", .bind "y"], alg [] [] [] [.binary .add (.param "x") (.param "y")] ⟩ ]

-- G((0)) = 100; G((x)) = x
def dotCallParitySingletonSequenceValueAlg : Algorithm := .conditional none [] [
  ⟨ .sequenceValue [.litInt 0], alg [] [] [] [.num 100] ⟩,
  ⟨ .sequenceValue [.bind "x"], alg [] [] [] [.param "x"] ⟩ ]

/-- One shared program providing every receiver, user callee, callback, and
    conditional used by the parity cases below. -/
def dotCallParityProg : Algorithm :=
  algPrivate [] [] [
    ("Double", alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]),
    ("KeepPositive", alg ["x"] [] [] [.binary .gt (.param "x") (.num 0)]),
    ("Add", alg ["item", "acc"] [] [] [.binary .add (.param "item") (.param "acc")]),
    ("NItems", receiverSymmetryNItemsAlg),
    ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg),
    ("FixedPairCount", alg ["values", "t"] [] [] [.dotCall (.param "values") "count" none]),
    ("Pair", alg [] [] [] [.capture [.num 10, .num 20]]),
    ("Values", alg [] [] [] [.num 10, .num 20]),
    ("Value", alg [] [] [] [.num 42]),
    ("Receiver", alg [] [] [] [.num 1]),
    ("Bad", alg [] [] [] [.binary .div (.num 1) (.num 0)]),
    ("Holder", alg [] [] [publicProp "Inner" (alg [] [] [] [.num 42])] [.num 1]),
    ("Choose", dotCallParityChooseAlg),
    ("G", dotCallParitySingletonSequenceValueAlg)
  ] [.num 0]

-- Inline `(…)` receivers expose their top-level output items.
def dotCallParityData123 : KatLang.Expr := .capture [.num 1, .num 2, .num 3]
def dotCallParityData312 : KatLang.Expr := .capture [.num 3, .num 1, .num 2]
def dotCallParityDataMixedSigns : KatLang.Expr :=
  .capture [.num (-1), .num 2, .num (-3)]

def dotCallArgs (items : List KatLang.Expr) : Option (List KatLang.Expr) :=
  some items

structure DotCallParityCase where
  label : String
  target : KatLang.Expr
  name : String
  argsOpt : Option (List KatLang.Expr) := none
  expected : BuiltinApplyOutcome := .succeeded
  expectedAtoms : Option (List Int) := none
  -- Elaborated dot-edge fact; the default mirrors the `Expr.dotCall` sugar
  -- (`.resolve name` fallback).
  fallback? : Option KatLang.Expr := none

/-- Lexical context mirroring `runResultM`: the program algorithm is wired
    onto the prelude and pushed, exactly as when its output expressions are
    evaluated, so dot-call targets resolve the program's properties and the
    builtin prelude. -/
def dotCallParityCtx (prog : Algorithm) : KatLang.EvalCtx :=
  let base : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }
  KatLang.EvalCtx.push (KatLang.wireToCaller base prog) base

/-- Run both dot-call twins from identical initial state and require:
    projection parity (value / error Repr / final state Repr), the expected
    outcome classification, and the expected atoms for success cases — the
    last two keep each case honest about what it exercises. Atoms are compared
    through the host-boundary view (`Result.hostAtoms`), which opens exact list
    values, so collection-builtin cases still assert their numeric contents. -/
def dotCallParityCaseHolds (c : DotCallParityCase) : Bool :=
  let ctx := dotCallParityCtx dotCallParityProg
  let fallback := c.fallback?.getD (.resolve c.name)
  let plain := (KatLang.evalDotCall c.target c.name fallback c.argsOpt ctx []).run KatLang.EvalState.empty
  let counted := (KatLang.evalDotCallCounted c.target c.name fallback c.argsOpt ctx []).run KatLang.EvalState.empty
  let parity :=
    match plain, counted with
    | .ok (value, plainState), .ok ((countedValue, _), countedState) =>
        value == countedValue && reprStr plainState == reprStr countedState
    | .error plainErr, .error countedErr => reprStr plainErr == reprStr countedErr
    | _, _ => false
  let outcome := classifyBuiltinApply (plain.map (fun _ => ()))
  let atomsMatch :=
    match c.expectedAtoms, plain with
    | some expected, .ok (value, _) => Result.hostAtoms value == expected
    | some _, .error _ => false
    | none, _ => true
  parity && outcome == c.expected && atomsMatch

def dotCallParityCases : List DotCallParityCase :=
  [ -- A: ordinary lexical user-defined dot-call, receiver injected as one
    -- leading argument: 5.Double == Double(5).
    { label := "A/lexical-user-callee", target := .num 5, name := "Double",
      expectedAtoms := some [10] },
    -- B: sequence-valued property receiver is ONE argument slot, never implicitly
    -- spread: Pair.NItems == NItems(Pair) collects `values = [Pair]`, count 1.
    { label := "B/sequenceValue-receiver-one-slot", target := resolve "Pair", name := "NItems",
      expectedAtoms := some [1] },
    -- C: explicit spread of a multi-output property spreads its emitted top-level
    -- values into the single-collecting `NItems(*values)` item supply: (Values*).NItems
    -- binds the two values, count 2.
    { label := "C/spread-multi-output-receiver",
      target := sequenceSpreadReceiver (resolve "Values"), name := "NItems",
      expectedAtoms := some [2] },
    -- D: explicit spread of a sequence-valued property opens it into the item
    -- supply the same way: (Pair*).NItems binds the two elements, count 2.
    { label := "D/spread-sequenceValue-receiver-stays-sequenceValue",
      target := sequenceSpreadReceiver (resolve "Pair"), name := "NItems",
      expectedAtoms := some [2] },
    -- E: leading variadic with suffix: Pair.BeforeLastCount(99) collects the
    -- sequence-value receiver as one collected element, count 1.
    { label := "E/leading-variadic-with-suffix", target := resolve "Pair",
      name := "BeforeLastCount", argsOpt := dotCallArgs [.num 99],
      expectedAtoms := some [1] },
    -- F/G: a receiver is ONE segment for arity checking regardless of its
    -- supply (the segment supply is consumed only by an allocated collector),
    -- so a fixed-arity callee receives the grouped-spread receiver as ONE
    -- slot and under-binds — for the multi-output and the sequence-valued
    -- property alike.
    { label := "F/spread-fixed-arity-multi-output",
      target := sequenceSpreadReceiver (resolve "Values"), name := "FixedPairCount",
      expected := .arityRejected },
    { label := "G/spread-fixed-arity-sequenceValue",
      target := sequenceSpreadReceiver (resolve "Pair"), name := "FixedPairCount",
      expected := .arityRejected },
    -- H: sequence builtin dot-calls.
    { label := "H/builtin-sum", target := dotCallParityData123, name := "sum",
      expectedAtoms := some [6] },
    { label := "H/builtin-count", target := dotCallParityData123, name := "count",
      expectedAtoms := some [3] },
    { label := "H/builtin-order", target := dotCallParityData312, name := "order",
      expectedAtoms := some [1, 2, 3] },
    -- I: sequence builtin dot-calls with suffix arguments.
    { label := "I/builtin-take-suffix", target := dotCallParityData123, name := "take",
      argsOpt := dotCallArgs [.num 2], expectedAtoms := some [1, 2] },
    { label := "I/builtin-skip-suffix", target := dotCallParityData123, name := "skip",
      argsOpt := dotCallArgs [.num 1], expectedAtoms := some [2, 3] },
    { label := "I/builtin-contains-suffix", target := dotCallParityData123, name := "contains",
      argsOpt := dotCallArgs [.num 2], expectedAtoms := some [1] },
    -- J: sequence builtin dot-calls with user callbacks.
    { label := "J/builtin-map-callback", target := dotCallParityData123, name := "map",
      argsOpt := dotCallArgs [resolve "Double"], expectedAtoms := some [2, 4, 6] },
    { label := "J/builtin-filter-callback", target := dotCallParityDataMixedSigns,
      name := "filter", argsOpt := dotCallArgs [resolve "KeepPositive"],
      expectedAtoms := some [2] },
    { label := "J/builtin-reduce-callback", target := dotCallParityData123, name := "reduce",
      argsOpt := dotCallArgs [resolve "Add", .num 0], expectedAtoms := some [6] },
    -- K: `Receiver.Value` falls back lexically and injects the receiver as
    -- one leading argument, so the zero-parameter property under-binds:
    -- arityMismatch 0 1 on both paths.
    { label := "K/lexical-zero-arg-prop-receiver-arity", target := resolve "Receiver",
      name := "Value", expected := .arityRejected },
    -- L: `1.Choose` injects one argument against two-argument clause
    -- patterns: noMatchingBranch "Choose" on both paths.
    { label := "L/conditional-receiver-underbinds", target := .num 1, name := "Choose",
      expected := .failedOtherwise },
    -- M: `1.G` SUCCEEDS: singleton sequence-value clause patterns match a non-sequence-value
    -- argument (`patternSequenceValueMembers?` adaptation), so G((x)) binds x = 1.
    { label := "M/singleton-sequence-value-conditional-matches", target := .num 1, name := "G",
      expectedAtoms := some [1] },
    -- N: unknown member: unknownName "DoesNotExist" on both paths.
    { label := "N/unknown-name", target := .num 1, name := "DoesNotExist",
      expected := .failedOtherwise },
    -- O: receiver evaluation failure (division by zero) propagates with the
    -- same diagnostic on both paths.
    { label := "O/receiver-evaluation-failure", target := resolve "Bad", name := "NItems",
      expected := .failedOtherwise },
    -- P: structural zero-arg property access through dot-call writes the
    -- per-run cache; both paths must leave the same cache state.
    { label := "P/structural-zero-arg-cache", target := resolve "Holder", name := "Inner",
      expectedAtoms := some [42] },
    -- Q: a stored `.param` fallback with NO algEnv binding fails with the
    -- canonical parameter-resolution error on both paths — the stored
    -- identity decides, never the runtime environment.
    { label := "Q/param-fallback-unbound", target := .num 5, name := "Missing",
      fallback? := some (.param "Missing"), expected := .failedOtherwise } ]

def dotCallParityCaseFailures : List String :=
  (dotCallParityCases.filter (fun c => !(dotCallParityCaseHolds c))).map
    (fun c => c.label)

#guard dotCallParityCaseFailures == []

-- The cache-sensitive cases must actually write the cache, so the final-state
-- comparison inside the parity helper is not vacuously `empty == empty`.
def dotCallParityCacheCasesWriteCache : Bool :=
  [ (resolve "Holder", "Inner") ].all
    fun (target, name) =>
      match (KatLang.evalDotCall target name (.resolve name) none
          (dotCallParityCtx dotCallParityProg) []).run
          KatLang.EvalState.empty with
      | .ok (_, state) => !state.zeroArgPropertyCache.isEmpty
      | .error _ => false

#guard dotCallParityCacheCasesWriteCache

--------------------------------------------------------------------------------
-- Exact immutable list values (`[]` syntax)
--------------------------------------------------------------------------------
-- C# parity: tests/KatLang.Tests/ListValueTests.cs. Binder laws:
-- KatLangArityLaws.lean list bridge laws (exact list values are
-- intentionally not modeled in the CoreArityAlgebra paper artifact).

-- `[1, 2, 3]` constructs ONE exact list value.
def listLiteralConstructsExactValue : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
  | _ => false

#guard listLiteralConstructsExactValue

-- `[]`, `[7]`, and `[[7]]` keep exact cardinality and nesting: no singleton
-- erasure and no empty canonicalization applies to list structure.
def listExactnessPreserved : Bool :=
  (match runResult (.algorithmExpr (alg [] [] [] [.listLiteral []])) with
   | Except.ok (Result.listValue []) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [.num 7]])) with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [.listLiteral [.num 7]]])) with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 7]]) => true | _ => false)

#guard listExactnessPreserved

-- Equality is structural, recursive, and kind-exact: a list never equals a
-- sequence value or the lone item it contains.
def listEqualityIsKindExact : Bool :=
  expectFlat (runFlat (.algorithmExpr (alg [] [] [] [
    .binary .eq (.listLiteral [.num 1, .num 2]) (.listLiteral [.num 1, .num 2]),
    .binary .eq (.listLiteral []) (.emptySequence 0),
    .binary .eq (.listLiteral [.num 7]) (.num 7),
    .binary .eq (.listLiteral [.num 1, .num 2]) (.capture [.num 1, .num 2])])))
    [1, 0, 0, 0]

#guard listEqualityIsKindExact

-- Ordinary parentheses stay a redundant SEQUENCE grouping around lists:
-- `([1, 2])` canonicalizes to the exact list itself.
def redundantParensAroundListCanonicalize : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [.num 1, .num 2]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard redundantParensAroundListCanonicalize

-- A non-spread `()` element stays one visible list element.
def listKeepsVisibleEmptyElement : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [.num 1, .emptySequence 0, .num 2]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.sequenceValue [], Result.atom 2]) => true
  | _ => false

#guard listKeepsVisibleEmptyElement

-- Spread opens exactly ONE list boundary; capturing the spread yields
-- the canonical sequence of the elements.
def spreadCaptureConvertsListToSequence : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("A", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]]),
     ("B", alg [] [] [] [sequenceSpread (.resolve "A")])]
    [.resolve "B"])) with
  | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
  | _ => false

#guard spreadCaptureConvertsListToSequence

-- Spread edge cases: `[]*` supplies zero items (captures as `()`),
-- `[7]*` supplies the item, `[[7]]*` supplies the inner list intact.
def listSpreadEdgeCasesOpenOneBoundary : Bool :=
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral []])] [sequenceSpread (.resolve "A")])) with
   | Except.ok (Result.sequenceValue []) => true | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.num 7]])] [sequenceSpread (.resolve "A")])) with
   | Except.ok (Result.atom 7) => true | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.listLiteral [.num 7]]])] [sequenceSpread (.resolve "A")])) with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false)

#guard listSpreadEdgeCasesOpenOneBoundary

-- List-literal elements use the ordinary expression-list model: spread
-- elements insert their item supply into the constructed list.
def listLiteralSpreadElements : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("A", alg [] [] [] [.num 1, .num 2, .num 3])]
    [.listLiteral [.num 0, sequenceSpread (.resolve "A"), .num 4]])) with
  | Except.ok (Result.listValue
      [Result.atom 0, Result.atom 1, Result.atom 2, Result.atom 3, Result.atom 4]) => true
  | _ => false

#guard listLiteralSpreadElements

-- Empty spreads contribute no elements; a NON-spread `[]` stays one element.
def emptyListSpreadIsNeutralInListLiteral : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.listLiteral [.num 1, sequenceSpread (.listLiteral []), .num 2]])) with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.listLiteral [.num 1, .listLiteral [], .num 2]])) with
   | Except.ok (Result.listValue [Result.atom 1, Result.listValue [], Result.atom 2]) => true
   | _ => false)

#guard emptyListSpreadIsNeutralInListLiteral

-- Calls preserve list boundaries: a list without spread is ONE argument.
def callPreservesListBoundary : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("F", alg ["a"] [] [] [.param "a"]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2]])]
    [.call (.resolve "F") [.resolve "A"]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard callPreservesListBoundary

-- Explicit spread supplies the elements as separate arguments.
def spreadOpensListIntoCallArguments : Bool :=
  expectFlat (runFlat (.algorithmExpr (algPrivate [] []
    [("F", alg ["a", "b", "c"] [] []
        [.binary .add (.binary .add (.param "a") (.param "b")) (.param "c")]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call (.resolve "F") [sequenceSpread (.resolve "A")]]))) [6]

#guard spreadOpensListIntoCallArguments

-- A fixed-arity callee rejects an unspread list (calls never open lists).
-- The list behaves exactly like any other single non-openable argument
-- (scalar, string): the Lean final-arg binding path reports the remaining
-- parameter/argument counts after the first binding step (`2 0`), a
-- pre-existing payload shape shared by `F(5)` and `F('xy')`; the C# runtime
-- reports the full signature counts (`3 1`). Both are category `arity`.
def callDoesNotImplicitlyOpenList : Bool :=
  expectInnermostArityMismatch 2 0 (runFlat (.algorithmExpr (algPrivate [] []
    [("F", alg ["a", "b", "c"] [] []
        [.binary .add (.binary .add (.param "a") (.param "b")) (.param "c")]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call (.resolve "F") [.resolve "A"]])))

#guard callDoesNotImplicitlyOpenList

-- Mixed fixed/variadic call: a lone list argument stays whole — `first` receives
-- the entire list, `rest` captures nothing.
def mixedVariadicCallKeepsLoneListWhole : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("F", algWithParameters [{ name := "first" }, { name := "rest", kind := .collecting }] [] []
        [.param "first"]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2]])]
    [.call (.resolve "F") [.resolve "A"]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard mixedVariadicCallKeepsLoneListWhole

-- Deconstruction (the sequence-value parameter pattern) opens a lone LIST
-- exactly like a lone sequence value: `x, y, z = [1, 2, 3]` binds elementwise.
def deconstructionOpensLoneList : Bool :=
  let helper := KatLang.Expr.algorithmExpr (algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]]
    [] [] [.param "y"])
  expectFlat (runFlat (.algorithmExpr (algPrivate [] []
    [("d", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call helper [.resolve "d"]]))) [2]

#guard deconstructionOpensLoneList

-- Collecting binding in deconstruction COLLECTS the remaining items as one exact
-- immutable list: `x, *rest = [1, 2, 3]` binds `rest = [2, 3]`.
def listCollectingCaptureCollectsExactList : Bool :=
  let helper := KatLang.Expr.algorithmExpr (algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]]
    [] [] [.param "rest"])
  match runResult (.algorithmExpr (algPrivate [] []
    [("d", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call helper [.resolve "d"]])) with
  | Except.ok (Result.listValue [Result.atom 2, Result.atom 3]) => true
  | _ => false

#guard listCollectingCaptureCollectsExactList

-- Deconstruction opens only the OUTER lone structure: nested lists stay whole.
def deconstructionDoesNotOpenListRecursively : Bool :=
  let helper := KatLang.Expr.algorithmExpr (algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]]
    [] [] [.param "x"])
  match runResult (.algorithmExpr (algPrivate [] []
    [("d", alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2], .num 3]])]
    [.call helper [.resolve "d"]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard deconstructionDoesNotOpenListRecursively

-- The builtin collection view opens a lone list like a lone sequence value:
-- the shared collection-item view opens ONE outer sequence or list boundary,
-- so `count([1, 2, 3])` counts three items.
def builtinLoneListCollectionOpens : Bool :=
  expectFlat (runFlat (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [.listLiteral [.num 1, .num 2, .num 3]]])))
    [3]

#guard builtinLoneListCollectionOpens

-- Opening is never recursive: two sibling lists grouped into ONE collection
-- argument are two items (`count(([], []))` is 2), the ungrouped `count([], [])`
-- is a two-argument arity error, and a nested list inside an opened lone list
-- stays one opaque item (`count([1, [2], 3])` is 3).
def builtinSiblingListsCountAsItems : Bool :=
  expectFlat (runFlat (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [.capture [.listLiteral [], .listLiteral []]]])))
    [2] &&
  (match runResult (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [.listLiteral [], .listLiteral []]])) with
   | Except.error err => innermostIsArityMismatch 1 2 err
   | _ => false)

#guard builtinSiblingListsCountAsItems

def builtinNestedListStaysOneItem : Bool :=
  expectFlat (runFlat (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [.listLiteral [.num 1, .listLiteral [.num 2], .num 3]]])))
    [3]

#guard builtinNestedListStaysOneItem

-- Spread keeps only its ordinary meaning at builtin calls: `count([1, 2, 3]*)`
-- opens the list into THREE ordinary argument slots, an arity error under
-- `count(collection)` (same for sum). Grouping the spread back into one
-- argument is the rewrite idiom: `count(([1, 2, 3]*))` is 3, and the
-- unspread `count([1, 2, 3])` stays the direct form (see
-- builtinLoneListCollectionOpens above).
def builtinSpreadListFollowsFixedArity : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])]])) with
   | Except.error err => innermostIsArityMismatch 1 3 err
   | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
    [.call (.resolve "sum") [sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])]])) with
   | Except.error err => innermostIsArityMismatch 1 3 err
   | _ => false) &&
  expectFlat (runFlat (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [.capture [sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])]]]))) [3]

#guard builtinSpreadListFollowsFixedArity

-- Indexing returns the selected element exactly as stored: selecting a list
-- ITEM from a sequence preserves the list (projection does not erase
-- listness).
def indexingPreservesSelectedList : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("A", alg [] [] [] [.capture [.num 0, .listLiteral [.num 1, .num 2]]])]
    [.index (.resolve "A") (.num 1)])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard indexingPreservesSelectedList

-- Indexing `:` opens a LIST TARGET to its immediate elements exactly like a
-- sequence target (`Result.projectionItems`): `[1, 2, 3]:0` is `1`, `[7]:0`
-- is `7`, and the selected element keeps its exact kind.
def listIndexingSelectsElement : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 0)])) with
   | Except.ok (Result.atom 1) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 1)])) with
   | Except.ok (Result.atom 2) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 2)])) with
   | Except.ok (Result.atom 3) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 7]) (.num 0)])) with
   | Except.ok (Result.atom 7) => true | _ => false)

#guard listIndexingSelectsElement

-- A selected LIST element stays one exact opaque list (no flattening, no
-- sequence conversion): `[[1, 2], [3, 4]]:0` is `[1, 2]` and `[[]]:0` is `[]`.
def listIndexingNestedElementStaysList : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral
        [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]) (.num 0)])) with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.listLiteral []]) (.num 0)])) with
   | Except.ok (Result.listValue []) => true | _ => false)

#guard listIndexingNestedElementStaysList

-- Chained projection peels one boundary per `:`: `[[1, 2], [3, 4]]:1:0` is `3`.
def listIndexingChainedSelectsOneLevelAtATime : Bool :=
  match runResult (.algorithmExpr (alg [] [] []
    [.index (.index (.listLiteral
      [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]) (.num 1)) (.num 0)])) with
  | Except.ok (Result.atom 3) => true
  | _ => false

#guard listIndexingChainedSelectsOneLevelAtATime

-- A selected SEQUENCE element inside a list projects one level with its item
-- count, exactly like the sequence-target twin; a selected `()` element stays
-- one visible empty row at root.
def listIndexingSequenceElementProjectsCounted : Bool :=
  (match runCountedProgram (.algorithmExpr (alg [] [] []
      [.index (.listLiteral
        [.capture [.num 1, .num 2],
         .capture [.num 3, .num 4]]) (.num 0)])) with
   | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2], 2) => true | _ => false) &&
  (match runCountedProgram (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.emptySequence 0]) (.num 0)])) with
   | .ok (Result.sequenceValue [], 1) => true | _ => false)

#guard listIndexingSequenceElementProjectsCounted

-- Empty and out-of-range list projection is the existing out-of-range
-- projection error: `[]:0`, `[1, 2]:2`, and `[1, 2]:100` are badIndex, and a
-- negative selector stays badIndex for list targets too. A selector beyond
-- the C# host int range (3000000000) is an ordinary out-of-range badIndex in
-- the unbounded-Int model — the twin of the C# int-cast guard — for both
-- target kinds.
def listIndexingOutOfRangeIsBadIndex : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral []) (.num 0)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.num 2)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.num 100)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.num (-1))])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 3000000000)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.capture [.num 1, .num 2, .num 3]) (.num 3000000000)])) with
   | Except.error err => innermostIsBadIndex err | _ => false)

#guard listIndexingOutOfRangeIsBadIndex

-- Selector validation is unchanged by list targets: a list-valued selector
-- never coerces to a number (badArity), and a string selector stays the
-- string type mismatch — identical to sequence targets.
def listIndexingSelectorValidationUnchanged : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.listLiteral [.num 0])])) with
   | Except.error err => innermostIsBadArity err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.stringLiteral "0")])) with
   | Except.error err => innermostIsTypeMismatch "Expected a number, got a string" err | _ => false)

#guard listIndexingSelectorValidationUnchanged

-- Diagnostic expression names use KatLang SOURCE syntax: an index renders as
-- `target:selector`, never `target[selector]` (`[...]` is exact list literal
-- syntax, so bracket text would read back as the adjacency `Rows, [0]`).
-- These pin the exact text C# produces; C#:
-- `Eval_Index_DiagnosticName_RendersSourceFaithfulColonSyntax` and
-- `Eval_Index_ChainedDiagnosticName_RendersEachSelector`.
def indexDiagnosticNameIsSourceFaithful : Bool :=
  (KatLang.exprDiagnosticName (.index (.resolve "Rows") (.num 0)) == "Rows:0") &&
  -- Chained projection is left-associative, so each selector renders in turn
  -- and the target needs no parentheses.
  (KatLang.exprDiagnosticName (.index (.index (.resolve "Rows") (.num 0)) (.num 1)) == "Rows:0:1") &&
  -- The renderer is syntax-based, so a list target renders the same way.
  (KatLang.exprDiagnosticName (.index (.listLiteral [.num 1, .num 2]) (.num 0)) == "[1, 2]:0")

#guard indexDiagnosticNameIsSourceFaithful

-- Operands that would rebind under the real precedence are parenthesized.
-- C#: `Eval_Index_DiagnosticName_ParenthesizesOperandsThatWouldRebind`.
def indexDiagnosticNameParenthesizesRebindingOperands : Bool :=
  -- Indexing binds tighter than unary and every binary operator.
  (KatLang.exprDiagnosticName (.index (.binary .add (.resolve "A") (.resolve "B")) (.num 0))
    == "(A + B):0") &&
  (KatLang.exprDiagnosticName (.index (.unary .minus (.resolve "A")) (.num 0)) == "(-A):0") &&
  (KatLang.exprDiagnosticName (.index (.resolve "Rows") (.binary .add (.resolve "i") (.num 1)))
    == "Rows:(i + 1)") &&
  -- The selector is a primary in source syntax, so anything that would continue
  -- the postfix chain (`.`, `:`, a call) rebinds to the target without parens.
  (KatLang.exprDiagnosticName (.index (.resolve "A") (.dotCall (.resolve "B") "C" none)) == "A:(B.C)") &&
  (KatLang.exprDiagnosticName (.index (.resolve "A") (.index (.resolve "B") (.resolve "C")))
    == "A:(B:C)") &&
  (KatLang.exprDiagnosticName (.index (.resolve "A") (.call (.resolve "f") [.num 0]))
    == "A:(f(...))") &&
  -- A bare negative literal is not selector syntax at all (`A:-1` is a parse
  -- error), so it keeps parentheses.
  (KatLang.exprDiagnosticName (.index (.resolve "A") (.num (-1))) == "A:(-1)")

#guard indexDiagnosticNameParenthesizesRebindingOperands

-- C#: `Eval_Spread_DiagnosticName_ParenthesizesOperandsThatWouldRebind`.
def spreadDiagnosticNameParenthesizesRebindingOperands : Bool :=
  (KatLang.exprDiagnosticName
      (.sequenceSpread (.unary .minus (.resolve "A"))) == "(-A)*") &&
  (KatLang.exprDiagnosticName
      (.sequenceSpread (.binary .add (.resolve "A") (.resolve "B"))) == "(A + B)*") &&
  (KatLang.exprDiagnosticName
      (.sequenceSpread (.sequenceSpread (.resolve "A"))) == "A**")

#guard spreadDiagnosticNameParenthesizesRebindingOperands

-- `openExprName` renders an index with source-faithful `:` rather than falling
-- back to the generic `(index)` kind word. Leaf kinds this minimal renderer
-- does not model still print as `(kind)` — a PRE-EXISTING divergence from C#'s
-- merged `OpenExprName`, uniform across `.dotCall`, `.sequenceSpread`, and
-- `.index` alike, and independent of indexing.
def openExprNameRendersIndexSourceFaithfully : Bool :=
  (KatLang.openExprName (.index (.resolve "Rows") (.resolve "i")) == "Rows:i") &&
  (KatLang.openExprName (.index (.index (.resolve "Rows") (.resolve "i")) (.resolve "j"))
    == "Rows:i:j") &&
  -- A selector this renderer prints BARE and that would continue the postfix
  -- chain is still parenthesized.
  (KatLang.openExprName (.index (.resolve "A") (.dotCall (.resolve "B") "C" none)) == "A:(B.C)") &&
  (KatLang.openExprName (.index (.resolve "A") (.index (.resolve "B") (.resolve "C")))
    == "A:(B:C)") &&
  -- Unmodelled leaf: the `(num)` fallback, not `(index)`.
  (KatLang.openExprName (.index (.resolve "Rows") (.num 0)) == "Rows:(num)") &&
  -- An unmodelled kind is ALREADY self-delimiting as `(kind)`, so it must not
  -- be parenthesized a second time into `A:((binary))`.
  (KatLang.openExprName (.index (.resolve "A") (.binary .add (.resolve "i") (.num 1)))
    == "A:(binary)") &&
  (KatLang.openExprName (.index (.resolve "A") (.num (-1))) == "A:(num)")

#guard openExprNameRendersIndexSourceFaithfully

-- Collection-producing builtin results are directly indexable:
-- `range(1, 3):2` is `3` and `[3, 1, 2].order:0` is `1`.
def listIndexingBuiltinResultsDirectlyIndexable : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.call (.resolve "range") [.num 1, .num 3]) (.num 2)])) with
   | Except.ok (Result.atom 3) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.dotCall (.listLiteral [.num 3, .num 1, .num 2]) "order" none) (.num 0)])) with
   | Except.ok (Result.atom 1) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.call (.resolve "take") [.listLiteral [.num 1, .num 2, .num 3], .num 2]) (.num 1)])) with
   | Except.ok (Result.atom 2) => true | _ => false)

#guard listIndexingBuiltinResultsDirectlyIndexable

-- Stacked spread is compositional: `A**` agrees with the value-boundary-
-- separated form `(A*)*` — each extra star spreads the value the previous
-- star's supply re-captures at the ordinary expression boundary. A LONE
-- structured item singleton-collapses at that capture, so a singleton-list
-- chain opens one more list boundary per written star, while a multi-item
-- supply is a fixed point (see the dedicated guards below).
def stackedSpreadAgreesWithGroupedCompositionalForm : Bool :=
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.listLiteral [.num 7]]])]
      [.sequenceSpread (.sequenceSpread (.resolve "A"))])) with
   | Except.ok (Result.atom 7) => true | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2]]])]
      [.sequenceSpread (.sequenceSpread (.resolve "A"))])) with
   | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.capture [.num 1, .num 2]])]
      [.sequenceSpread (.sequenceSpread (.resolve "A"))])) with
   | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2]) => true | _ => false)

#guard stackedSpreadAgreesWithGroupedCompositionalForm

-- The multi-item fixed point, asserted as DIRECT equality between the
-- stacked spelling `A**` and the grouped spelling `(A*)*` (`.capture` is the
-- written-parentheses boundary), plus the pinned value: the two inner lists
-- survive unopened. This guard is what stops a future refactor from
-- replacing capture-law composition with a concatMap-style per-item lift,
-- which would flatten to S[1, 2, 3, 4] here.
def stackedSpreadMultiItemFixedPoint : Bool :=
  let multiA : KatLang.Expr -> KatLang.Expr := fun output =>
    .algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral
        [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]])]
      [output])
  let stacked := runResult (multiA (.sequenceSpread (.sequenceSpread (.resolve "A"))))
  let grouped := runResult (multiA
    (.sequenceSpread (.capture [.sequenceSpread (.resolve "A")])))
  match stacked, grouped with
  | Except.ok s, Except.ok g =>
      s == g &&
      s == Result.sequenceValue
        [Result.listValue [Result.atom 1, Result.atom 2],
         Result.listValue [Result.atom 3, Result.atom 4]]
  | _, _ => false

#guard stackedSpreadMultiItemFixedPoint

-- A MIXED multi-item supply stays a fixed point too: the second star
-- re-spreads the captured pair; it does not selectively open the structured
-- member.
def stackedSpreadMixedSupplyStaysUnopened : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2], .num 3]])]
      [.sequenceSpread (.sequenceSpread (.resolve "A"))])) with
  | Except.ok r =>
      r == Result.sequenceValue [Result.listValue [Result.atom 1, Result.atom 2], Result.atom 3]
  | _ => false

#guard stackedSpreadMixedSupplyStaysUnopened

--------------------------------------------------------------------------------
-- Collecting bindings collect exact immutable lists (collectSegment)
--------------------------------------------------------------------------------
-- Required matrix for the collect model: capture / collect / open are distinct
-- operations. C# parity: tests/KatLang.Tests/DeconstructionBindingTests.cs and
-- EvaluatorTests variadic sections; binder laws: KatLangArityLaws.lean.

-- Parser-elaborated deconstruction helper: `targets = RHS` binds through an
-- inline sequence-value parameter pattern over the shared RHS value.
def collectDeconHelper (targets : List KatLang.ParameterPattern) (observed : String)
    : KatLang.Expr :=
  .algorithmExpr (algWithParameterPatterns [.sequenceValue targets] [] [] [.param observed])

def collectFix (name : String) : KatLang.ParameterPattern :=
  .capture { name := name }

def collectVar (name : String) : KatLang.ParameterPattern :=
  .capture { name := name, kind := .collecting }

def runCollectDecon (targets : List KatLang.ParameterPattern) (observed : String)
    (rhs : List KatLang.Expr) : Except KatLang.Error Result :=
  -- Mirror parser elaboration: the RHS is evaluated once into a shared
  -- property, and the pattern helper opens that single shared value.
  runResult (.algorithmExpr (algPrivate [] [] [("sharedRhs", alg [] [] [] rhs)]
    [.call (collectDeconHelper targets observed) [resolve "sharedRhs"]]))

-- Empty, singleton, and multi-item collection: `head, *rest = [1] / [1, 2] / [1, 2, 3]`.
def deconCollectingCollectsEmptySingletonMultiple : Bool :=
  (match runCollectDecon [collectFix "head", collectVar "rest"] "rest"
      [.listLiteral [.num 1]] with
   | Except.ok (Result.listValue []) => true | _ => false) &&
  (match runCollectDecon [collectFix "head", collectVar "rest"] "rest"
      [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.atom 2]) => true | _ => false) &&
  (match runCollectDecon [collectFix "head", collectVar "rest"] "rest"
      [.listLiteral [.num 1, .num 2, .num 3]] with
   | Except.ok (Result.listValue [Result.atom 2, Result.atom 3]) => true | _ => false)

#guard deconCollectingCollectsEmptySingletonMultiple

-- Collecting-binding positions: leading `*rest, last` and middle `first, *middle, last`.
def deconCollectingPositionsCollectLists : Bool :=
  (match runCollectDecon [collectVar "rest", collectFix "last"] "rest"
      [.listLiteral [.num 1, .num 2, .num 3]] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runCollectDecon [collectFix "first", collectVar "middle", collectFix "last"] "middle"
      [.listLiteral [.num 1, .num 2, .num 3, .num 4]] with
   | Except.ok (Result.listValue [Result.atom 2, Result.atom 3]) => true | _ => false) &&
  (match runCollectDecon [collectFix "first", collectVar "middle", collectFix "last"] "middle"
      [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue []) => true | _ => false)

#guard deconCollectingPositionsCollectLists

-- Structured singleton items are preserved exactly: a collected segment of one structured
-- item is a one-element list holding that structure, never the structure
-- itself, and zero items stay distinguishable from one empty structure.
def deconCollectingPreservesStructuredSingletons : Bool :=
  -- first, *rest = [[1, 2], [3, 4]]  =>  rest = [[3, 4]]
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 3, Result.atom 4]]) => true
   | _ => false) &&
  -- first, *rest = 1, [2, 3]  =>  rest = [[2, 3]]
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.num 1, .listLiteral [.num 2, .num 3]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 2, Result.atom 3]]) => true
   | _ => false) &&
  -- first, *rest = 1, (2, 3)  =>  rest = [(2, 3)]
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.num 1, .capture [.num 2, .num 3]] with
   | Except.ok (Result.listValue [Result.sequenceValue [Result.atom 2, Result.atom 3]]) => true
   | _ => false) &&
  -- first, *rest = 1, []  =>  rest = [[]]
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.num 1, .listLiteral []] with
   | Except.ok (Result.listValue [Result.listValue []]) => true | _ => false) &&
  -- first, *rest = 1, ()  =>  rest = [()]
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.num 1, .emptySequence 0] with
   | Except.ok (Result.listValue [Result.sequenceValue []]) => true | _ => false)

#guard deconCollectingPreservesStructuredSingletons

-- Deconstruction implicit opening agrees with explicit spread:
-- `first, *rest = [1, 2, 3]` and `first, *rest = [1, 2, 3]*`.
def deconCollectingImplicitOpeningMatchesSpread : Bool :=
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.listLiteral [.num 1, .num 2, .num 3]] with
   | Except.ok (Result.listValue [Result.atom 2, Result.atom 3]) => true | _ => false) &&
  (match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])] with
   | Except.ok (Result.listValue [Result.atom 2, Result.atom 3]) => true | _ => false)

#guard deconCollectingImplicitOpeningMatchesSpread

-- The receiver-level item-view law is not an unrestricted source rewrite:
-- a written deconstruction RHS spread first passes through the shared
-- property's ordinary capture boundary. Bare `x, y = [(1, 2)]` opens the
-- outer list once and has only one row for two targets (arity mismatch 2/1),
-- while `x, y = [(1, 2)]*` captures that one row as `(1, 2)` and the
-- deconstruction receiver then opens the row into `x = 1`, `y = 2`.
def deconSpreadCaptureCanOpenSingletonStructuredElementFurther : Bool :=
  (match runCollectDecon [collectFix "x", collectFix "y"] "x"
      [.listLiteral [.capture [.num 1, .num 2]]] with
   | Except.error err => innermostIsArityMismatch 2 1 err
   | _ => false) &&
  (match runCollectDecon [collectFix "x", collectFix "y"] "x"
      [.sequenceSpread (.listLiteral [.capture [.num 1, .num 2]])] with
   | Except.ok (Result.atom 1) => true
   | _ => false)

#guard deconSpreadCaptureCanOpenSingletonStructuredElementFurther

-- Provenance independence: `first, *rest = 1, [2, 3]*, (4, 5)*` collects
-- exactly the assembled item supply, regardless of the spread sources.
def deconCollectingProvenanceIndependent : Bool :=
  match runCollectDecon [collectFix "first", collectVar "rest"] "rest"
      [.num 1,
       .sequenceSpread (.listLiteral [.num 2, .num 3]),
       .sequenceSpread (.capture [.num 4, .num 5])] with
  | Except.ok (Result.listValue [Result.atom 2, Result.atom 3, Result.atom 4, Result.atom 5]) =>
      true
  | _ => false

#guard deconCollectingProvenanceIndependent

def collectInspectAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]

def runCollectInspect (args : List KatLang.Expr) : Except KatLang.Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] [("Inspect", collectInspectAlg)]
    [.call (resolve "Inspect") args]))

-- Variadic capture matrix: Inspect(*items) = items.
def variadicCaptureCollectsExactList : Bool :=
  (match runCollectInspect [] with
   | Except.ok (Result.listValue []) => true | _ => false) &&
  (match runCollectInspect [.num 7] with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false) &&
  (match runCollectInspect [.num 1, .num 2, .num 3] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
   | _ => false) &&
  -- Inspect([1, 2]) => [[1, 2]]; Inspect([1, 2]*) => [1, 2]
  (match runCollectInspect [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false) &&
  (match runCollectInspect [.sequenceSpread (.listLiteral [.num 1, .num 2])] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  -- Inspect((1, 2)) => [(1, 2)]; Inspect((1, 2)*) => [1, 2]
  (match runCollectInspect [.capture [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false) &&
  (match runCollectInspect [.sequenceSpread (.capture [.num 1, .num 2])] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false)

#guard variadicCaptureCollectsExactList

-- Empty-structure arguments: an unspread `()` or `[]` is ONE visible argument
-- slot (`Inspect(())` collects `[()]`, `Inspect([])` collects `[[]]`), while
-- the spreads contribute zero items (`Inspect(()*)` and `Inspect([]*)`
-- both collect `[]`) — zero-item-spread neutrality at the collect boundary.
def variadicCaptureEmptyStructureArguments : Bool :=
  (match runCollectInspect [.emptySequence 0] with
   | Except.ok (Result.listValue [Result.sequenceValue []]) => true | _ => false) &&
  (match runCollectInspect [.sequenceSpread (.emptySequence 0)] with
   | Except.ok (Result.listValue []) => true | _ => false) &&
  (match runCollectInspect [.listLiteral []] with
   | Except.ok (Result.listValue [Result.listValue []]) => true | _ => false) &&
  (match runCollectInspect [.sequenceSpread (.listLiteral [])] with
   | Except.ok (Result.listValue []) => true | _ => false)

#guard variadicCaptureEmptyStructureArguments

-- Middle collecting parameter, direct user call: `Middle(first, *middle, last) = middle`.
-- A grouped middle argument stays ONE collected slot with its boundary
-- (`Middle(10, (20, 30), 40)` collects `[(20, 30)]`), while the explicit
-- spread supplies the operand's items (`Middle(10, (20, 30)*, 40)` collects
-- `[20, 30]`).
def collectMiddleAlg : Algorithm :=
  algWithParameters
    [{ name := "first" }, { name := "middle", kind := .collecting }, { name := "last" }]
    [] [] [.param "middle"]

def runCollectMiddle (args : List KatLang.Expr) : Except KatLang.Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] [("Middle", collectMiddleAlg)]
    [.call (resolve "Middle") args]))

def middleVariadicGroupedAndSpreadDirectCall : Bool :=
  (match runCollectMiddle
      [.num 10, .capture [.num 20, .num 30], .num 40] with
   | Except.ok (Result.listValue [Result.sequenceValue [Result.atom 20, Result.atom 30]]) =>
       true
   | _ => false) &&
  (match runCollectMiddle
      [.num 10, .sequenceSpread (.capture [.num 20, .num 30]), .num 40] with
   | Except.ok (Result.listValue [Result.atom 20, Result.atom 30]) => true | _ => false)

#guard middleVariadicGroupedAndSpreadDirectCall

-- Variadic forwarding through ordinary list spread:
-- Target(*items) = items; Forward(*items) = Target(items*).
def collectTargetAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]

def collectForwardAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [
    .call (resolve "Target") [sequenceSpread (.param "items")]
  ]

def runCollectForward (args : List KatLang.Expr) : Except KatLang.Error Result :=
  runResult (.algorithmExpr (algPrivate [] []
    [("Target", collectTargetAlg), ("Forward", collectForwardAlg)]
    [.call (resolve "Forward") args]))

def collectingForwardingRoundTripsExactList : Bool :=
  (match runCollectForward [] with
   | Except.ok (Result.listValue []) => true | _ => false) &&
  (match runCollectForward [.num 7] with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false) &&
  (match runCollectForward [.num 1, .num 2] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runCollectForward [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false) &&
  (match runCollectForward [.sequenceSpread (.listLiteral [.num 1, .num 2])] with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false)

#guard collectingForwardingRoundTripsExactList

-- Forwarding the collected list WITHOUT spread passes one list argument:
-- TargetOne(item) = item; ForwardAsOne(*items) = TargetOne(items).
def variadicForwardAsOnePassesWholeList : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("TargetOne", alg ["item"] [] [] [.param "item"]),
     ("ForwardAsOne", algWithParameters [{ name := "items", kind := .collecting }] [] [] [
       .call (resolve "TargetOne") [.param "items"]
     ])]
    [.call (resolve "ForwardAsOne") [.num 1, .num 2]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard variadicForwardAsOnePassesWholeList

-- Receiver distinction: the call receiver preserves argument boundaries
-- (`Inspect(A)` is one collected element), while explicit spread supplies the
-- items — for lists and sequence values alike.
def variadicReceiverDistinctionObservable : Bool :=
  let inspect (arg : KatLang.Expr) : Except KatLang.Error Result :=
    runResult (.algorithmExpr (algPrivate [] []
      [("Inspect", collectInspectAlg),
       ("A", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]]),
       ("B", alg [] [] [] [.capture [.num 1, .num 2, .num 3]])]
      [.call (resolve "Inspect") [arg]]))
  (match inspect (resolve "A") with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]]) =>
       true
   | _ => false) &&
  (match inspect (sequenceSpread (resolve "A")) with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
   | _ => false) &&
  (match inspect (resolve "B") with
   | Except.ok (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]]) =>
       true
   | _ => false) &&
  (match inspect (sequenceSpread (resolve "B")) with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
   | _ => false)

#guard variadicReceiverDistinctionObservable

-- Dotted receiver injection: `A.Inspect` is `Inspect(A)` — the receiver is one
-- captured argument slot, so the collected list is `[[1, 2]]`.
def variadicDotReceiverCollectsOneSlot : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("Inspect", collectInspectAlg),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2]])]
    [.dotCall (resolve "A") "Inspect" none])) with
  | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
  | _ => false

#guard variadicDotReceiverCollectsOneSlot

-- Equality: collected results are exact list values, unequal to sequence values
-- and to differently-nested lists.
def collectedSegmentEqualityIsKindExact : Bool :=
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [("Inspect", collectInspectAlg)] [
    .binary .eq (.call (resolve "Inspect") []) (.listLiteral []),
    .binary .eq (.call (resolve "Inspect") [.num 7]) (.listLiteral [.num 7]),
    .binary .eq (.call (resolve "Inspect") [.num 1, .num 2])
      (.listLiteral [.num 1, .num 2]),
    .binary .eq (.call (resolve "Inspect") [.listLiteral [.num 1, .num 2]])
      (.listLiteral [.listLiteral [.num 1, .num 2]]),
    .binary .eq (.call (resolve "Inspect") [.listLiteral [.num 1, .num 2]])
      (.listLiteral [.num 1, .num 2]),
    .binary .eq (.call (resolve "Inspect") [.num 1, .num 2])
      (.capture [.num 1, .num 2])
  ]))) [1, 1, 1, 1, 0, 0]

#guard collectedSegmentEqualityIsKindExact

-- Collection composition: a collected list built inside a helper body composes with the
-- fixed-collection builtins exactly like a builtin-produced list.
def collectedSegmentComposesWithCollectionBuiltins : Bool :=
  let tailAlg : Algorithm := alg ["source"] [] [] [
    .call (collectDeconHelper [collectFix "first", collectVar "rest"] "rest") [.param "source"]
  ]
  let rows : KatLang.Expr :=
    .listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]
  (match runResult (.algorithmExpr (algPrivate [] [] [("Tail", tailAlg)]
      [.call (resolve "Tail") [rows]])) with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 3, Result.atom 4]]) => true
   | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] [] [("Tail", tailAlg)]
      [.dotCall (.call (resolve "Tail") [rows]) "count" none])) with
   | Except.ok (Result.atom 1) => true | _ => false) &&
  -- skip([[1, 2], [3, 4]], 1) agrees with the collected segment of the same source.
  (match runResult (.algorithmExpr (alg [] [] []
      [.call (resolve "skip") [rows, .num 1]])) with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 3, Result.atom 4]]) => true
   | _ => false)

#guard collectedSegmentComposesWithCollectionBuiltins

-- Scalar right-hand side: `first, *rest = 1` binds the empty list.
def deconCollectingScalarRhsCollectsEmptyList : Bool :=
  match runCollectDecon [collectFix "first", collectVar "rest"] "rest" [.num 1] with
  | Except.ok (Result.listValue []) => true
  | _ => false

#guard deconCollectingScalarRhsCollectsEmptyList

-- Ordinary capture is unchanged: `x = 1, 2, 3` captures a canonical sequence
-- value, and `x = [1, 2, 3]*` re-captures the spread items as a sequence —
-- capture and collect stay distinct operations.
def ordinaryCaptureStaysCanonicalSequence : Bool :=
  (match runResult (.algorithmExpr (algPrivate [] []
      [("x", alg [] [] [] [.num 1, .num 2, .num 3])] [resolve "x"])) with
   | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
   | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] []
      [("x", alg [] [] [] [.sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])])]
      [resolve "x"])) with
   | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
   | _ => false)

#guard ordinaryCaptureStaysCanonicalSequence

--------------------------------------------------------------------------------
-- Flat callbacks with collecting parameters bind through the shared binder
--------------------------------------------------------------------------------
-- A flat callee with a top-level collecting parameter routes through
-- bindCountedCallbackParameterPatternList: the callback supply keeps the
-- flat-callback row convention (a lone under-supplied final argument opens
-- into its items), then the shared prefix/collecting/suffix binder COLLECTS the
-- matched segment as one exact immutable list. A single-collecting callee keeps the whole
-- iterated element as one collected slot.
-- C# parity: EvaluatorTests callback sections and CollectingBindingTests.

def callbackCollectAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]

def runCallbackMap (props : List (String × Algorithm)) (collection : KatLang.Expr)
    (callbackName : String) : Except KatLang.Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] props
    [.call (resolve "map") [collection, resolve callbackName]]))

-- [7].map(Collect) => [[7]]; [7, 8].map(Collect) => [[7], [8]].
def restOnlyMapCallbackCollectsOneElementSlot : Bool :=
  (match runCallbackMap [("Collect", callbackCollectAlg)] (.listLiteral [.num 7]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 7]]) => true | _ => false) &&
  (match runCallbackMap [("Collect", callbackCollectAlg)]
      (.listLiteral [.num 7, .num 8]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 7],
       Result.listValue [Result.atom 8]]) => true
   | _ => false)

#guard restOnlyMapCallbackCollectsOneElementSlot

-- Structured elements stay one collected slot, preserving their exact kind:
-- [[1, 2]].map(Collect) => [[[1, 2]]]; [(1, 2)].map(Collect) => [[(1, 2)]];
-- [[]].map(Collect) => [[[]]]; [()].map(Collect) => [[()]].
def restOnlyMapCallbackPreservesElementKind : Bool :=
  (match runCallbackMap [("Collect", callbackCollectAlg)]
      (.listLiteral [.listLiteral [.num 1, .num 2]]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]]) =>
       true
   | _ => false) &&
  (match runCallbackMap [("Collect", callbackCollectAlg)]
      (.listLiteral [.capture [.num 1, .num 2]]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]]]) =>
       true
   | _ => false) &&
  (match runCallbackMap [("Collect", callbackCollectAlg)]
      (.listLiteral [.listLiteral []]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.listValue []]]) => true
   | _ => false) &&
  (match runCallbackMap [("Collect", callbackCollectAlg)]
      (.listLiteral [.emptySequence 1]) "Collect" with
   | Except.ok (Result.listValue [Result.listValue [Result.sequenceValue []]]) => true
   | _ => false)

#guard restOnlyMapCallbackPreservesElementKind

-- Dotted receiver form agrees: [7].map(Collect) via dotCall.
def restOnlyMapCallbackDottedReceiverAgrees : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Collect", callbackCollectAlg)]
    [.dotCall (.listLiteral [.num 7]) "map" (some [resolve "Collect"])])) with
  | Except.ok (Result.listValue [Result.listValue [Result.atom 7]]) => true
  | _ => false

#guard restOnlyMapCallbackDottedReceiverAgrees

-- Mixed flat variadic callbacks: the lone sequence element opens into row slots
-- (the flat-callback row convention), then the shared binder allocates
-- front/collecting/back — agreeing with the structured-pattern form.
def mixedVariadicMapCallbackBindsRowSlots : Bool :=
  let middleFlat : Algorithm := algWithParameters
    [{ name := "first" }, { name := "middle", kind := .collecting }, { name := "last" }]
    [] [] [.param "middle"]
  let middleStructured : Algorithm := algWithParameterPatterns
    [.sequenceValue [collectFix "first", collectVar "middle", collectFix "last"]]
    [] [] [.param "middle"]
  let headFlat : Algorithm := algWithParameters
    [{ name := "first" }, { name := "rest", kind := .collecting }] [] [] [.param "rest"]
  let initFlat : Algorithm := algWithParameters
    [{ name := "init", kind := .collecting }, { name := "last" }] [] [] [.param "init"]
  let row4 : KatLang.Expr := .listLiteral [.capture [.num 1, .num 2, .num 3, .num 4]]
  let row3 : KatLang.Expr := .listLiteral [.capture [.num 1, .num 2, .num 3]]
  -- [(1, 2, 3, 4)].map(F) with F(first, *middle, last) = middle => [[2, 3]]
  (match runCallbackMap [("F", middleFlat)] row4 "F" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 2, Result.atom 3]]) => true
   | _ => false) &&
  -- ... and the structured form F((first, *middle, last)) agrees.
  (match runCallbackMap [("F", middleStructured)] row4 "F" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 2, Result.atom 3]]) => true
   | _ => false) &&
  -- [(1, 2, 3)].map(Head) with Head(first, *rest) = rest => [[2, 3]]
  (match runCallbackMap [("Head", headFlat)] row3 "Head" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 2, Result.atom 3]]) => true
   | _ => false) &&
  -- [7].map(Head): the scalar row opens to one slot, the rest is empty => [[]]
  (match runCallbackMap [("Head", headFlat)] (.listLiteral [.num 7]) "Head" with
   | Except.ok (Result.listValue [Result.listValue []]) => true | _ => false) &&
  -- [(1, 2, 3)].map(Init) with Init(*init, last) = init => [[1, 2]]
  (match runCallbackMap [("Init", initFlat)] row3 "Init" with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false)

#guard mixedVariadicMapCallbackBindsRowSlots

-- Filter predicates observe the collected list kind: items == [7] holds only
-- when the collecting parameter collected exactly [7] — scalar 7 vs [7] is distinguishable.
def restOnlyFilterCallbackIsKindSensitive : Bool :=
  let isSingleSeven : Algorithm := algWithParameters
    [{ name := "items", kind := .collecting }] [] []
    [.binary .eq (.param "items") (.listLiteral [.num 7])]
  let isSingleSevenList : Algorithm := algWithParameters
    [{ name := "items", kind := .collecting }] [] []
    [.binary .eq (.param "items") (.listLiteral [.listLiteral [.num 7]])]
  (match runResult (.algorithmExpr (algPrivate [] [] [("IsSingleSeven", isSingleSeven)]
      [.call (resolve "filter") [.listLiteral [.num 7, .num 8], resolve "IsSingleSeven"]])) with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] [] [("P", isSingleSevenList)]
      [.call (resolve "filter") [.listLiteral [.listLiteral [.num 7], .listLiteral [.num 8]], resolve "P"]])) with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 7]]) => true | _ => false)

#guard restOnlyFilterCallbackIsKindSensitive

-- Reducer with the collecting parameter in ELEMENT position (before the accumulator boundary):
-- R(*items, acc) collects the projected element as [element] each step.
def reducerElementSideVariadicCollects : Bool :=
  let eqTen : Algorithm := algWithParameters
    [{ name := "items", kind := .collecting }, { name := "acc" }] [] []
    [.binary .eq (.param "items") (.listLiteral [.num 10])]
  let track : Algorithm := algWithParameters
    [{ name := "items", kind := .collecting }, { name := "acc" }] [] []
    [.capture [.sequenceSpread (.param "acc"), .param "items"]]
  -- reduce([10], R, 99) => 1: the single step observes items = [10], not 10.
  (match runResult (.algorithmExpr (algPrivate [] [] [("R", eqTen)]
      [.call (resolve "reduce") [.listLiteral [.num 10], resolve "R", .num 99]])) with
   | Except.ok (Result.atom 1) => true | _ => false) &&
  -- reduce((10, 20), R, ()) with R(*items, acc) = (acc*, items)
  -- => (10, [20]): each step appends the collected [element].
  (match runResult (.algorithmExpr (algPrivate [] [] [("R", track)]
      [.call (resolve "reduce") [.capture [.num 10, .num 20], resolve "R", .emptySequence 1]])) with
   | Except.ok (Result.sequenceValue [Result.atom 10, Result.listValue [Result.atom 20]]) => true
   | _ => false)

#guard reducerElementSideVariadicCollects

-- A genuine single-collecting reducer receives the callback's two ordinary slots,
-- element and accumulator, and collects both through the same shared binder.
-- This intentional widening follows the ordinary variadic call rule.
def restOnlyReducerCollectsElementAndAccumulatorSlots : Bool :=
  (match runResult (.algorithmExpr (algPrivate [] [] [("R", callbackCollectAlg)]
      [.call (resolve "reduce") [.listLiteral [.num 10], resolve "R", .num 99]])) with
   | Except.ok (Result.listValue [Result.atom 10, Result.atom 99]) => true
   | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] [] [("R", callbackCollectAlg)]
      [.call (resolve "reduce") [.listLiteral [.listLiteral [.num 1, .num 2]], resolve "R", .listLiteral []]])) with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2],
       Result.listValue []]) => true
   | _ => false)

#guard restOnlyReducerCollectsElementAndAccumulatorSlots

-- Explicit-argument semantics behind implicit forwarding elaboration: an
-- ordinary parameter passed UNSPREAD into a variadic callee stays one
-- argument boundary (`Use(items) = Target(items)`), while a collecting parameter
-- forwarded WITH spread re-supplies its collected items
-- (`Use(*items) = Target(items*)`). The front-end resolver synthesizes
-- exactly these two elaborated forms from the source binding kind.
def forwardingElaborationKindsObservable : Bool :=
  let useOrdinary : Algorithm := alg ["items"] [] [] [
    .call (resolve "Target") [.param "items"]
  ]
  let run (useAlg : Algorithm) (args : List KatLang.Expr) : Except KatLang.Error Result :=
    runResult (.algorithmExpr (algPrivate [] []
      [("Target", collectTargetAlg), ("Use", useAlg)]
      [.call (resolve "Use") args]))
  -- Use(items) = Target(items): Use([1, 2]) => [[1, 2]]; Use((1, 2)) => [(1, 2)].
  (match run useOrdinary [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false) &&
  (match run useOrdinary [.capture [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.sequenceValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false) &&
  (match run useOrdinary [.num 7] with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false) &&
  -- Use(*items) = Target(items*): Use([1, 2]) => [[1, 2]] (round trip).
  (match run collectForwardAlg [.listLiteral [.num 1, .num 2]] with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 1, Result.atom 2]]) => true
   | _ => false)

#guard forwardingElaborationKindsObservable

--------------------------------------------------------------------------------
-- OutputBundle split: algorithmExpr vs capture
--------------------------------------------------------------------------------
-- These guards pin the split itself: a capture is a normalized value boundary
-- over an OutputBundle, an algorithmExpr exposes algorithm identity, and the
-- two coincide observationally exactly on declaration-free content.

/-- A capture row captures its bundle canonically: `(1, 2)` grouping
    still observes the pair. -/
def captureValueBoundaryObservesPair : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.capture [.num 1, .num 2]])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard captureValueBoundaryObservesPair

/-- An empty bundle captures the empty sequence value (host-only shape:
    written `()` parses to the emptySequence node). -/
def emptyCaptureIsEmptySequence : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.capture []])) with
  | .ok (Result.sequenceValue []) => true
  | _ => false

#guard emptyCaptureIsEmptySequence

/-- Declaration-free content evaluates identically through both constructors —
    the shared output-row loop is the single implementation. -/
def captureAndZeroDeclBlockCoincide : Bool :=
  let rows : List KatLang.Expr := [.num 1, .capture [.num 2, .num 3], .emptySequence 0]
  match runResult (.algorithmExpr (alg [] [] [] [.capture rows])),
        runResult (.algorithmExpr (alg [] [] [] [.algorithmExpr (alg [] [] [] rows)])) with
  | .ok a, .ok b => a == b
  | _, _ => false

#guard captureAndZeroDeclBlockCoincide

/-- Capture is not algorithm identity: a grouped named callable argument stays
    on the value channel, so evaluating `(Increment)` calls the one-parameter
    property with zero arguments and fails with that arity error — Increment's
    callable identity never crosses the capture boundary. -/
def captureSuppressesCallableIdentity : Bool :=
  let increment := alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]
  let apply := alg ["f"] [] [] [.call (.param "f") [.num 9]]
  let root := algPrivate [] [] [("Apply", apply), ("Increment", increment)]
    [.call (resolve "Apply") [.capture [.resolve "Increment"]]]
  match runResult (.algorithmExpr root) with
  | .error e => innermostIsArityMismatch 1 0 e
  | _ => false

#guard captureSuppressesCallableIdentity

/-- The algorithm channel sees only a zero-parameter value thunk for a capture:
    calling a captured expression as a function is an arity error against the
    thunk, never a call of the inner algorithm. -/
def captureCalleeIsAValueThunk : Bool :=
  let f := alg ["x"] [] [] [.param "x"]
  let root := algPrivate [] [] [("F", f)]
    [.call (.capture [.resolve "F"]) [.num 1]]
  match runResult (.algorithmExpr root) with
  | .error e => innermostIsArityMismatch 0 1 e
  | _ => false

#guard captureCalleeIsAValueThunk

/-- `open` consumes algorithm/namespace identity, and a capture is a value
    boundary that never exposes the identity of what it encloses: a captured
    open target is rejected with the structured badOpenForm error (exactly
    like a spread-marked target), while a direct algorithm target opens. -/
def openCaptureTargetIsRejected : Bool :=
  let m := alg [] [] [] [.num 5]
  let lib := Algorithm.mk none [] [] [publicProp "C" (alg [] [] [] [.num 5])] []
  let direct := algPrivate [] [.algorithmExpr lib] [("M", m)] [.resolve "C"]
  let viaCapture := algPrivate [] [.capture [.resolve "M"]] [("M", m)] [.resolve "C"]
  (match runResult (.algorithmExpr direct) with
   | .ok (Result.atom 5) => true | _ => false) &&
  (match runResult (.algorithmExpr viaCapture) with
   | .error (Error.badOpenForm _) => true
   | .error (Error.withContext _ (Error.badOpenForm _)) => true
   | _ => false)

#guard openCaptureTargetIsRejected

--------------------------------------------------------------------------------
-- Boundary-policy contrast pins: capture never exposes enclosed identity
-- (open targets, higher-order arguments, receivers); algorithm blocks always
-- expose their contained algorithm.
--------------------------------------------------------------------------------

/-- `open ((M))` — a NESTED capture target is rejected identically: no
    capture depth restores the enclosed algorithm identity. -/
def openNestedCaptureTargetIsRejected : Bool :=
  let m := alg [] [] [] [.num 5]
  let viaNested := algPrivate [] [.capture [.capture [.resolve "M"]]] [("M", m)] [.resolve "C"]
  match runResult (.algorithmExpr viaNested) with
  | .error (Error.badOpenForm _) => true
  | .error (Error.withContext _ (Error.badOpenForm _)) => true
  | _ => false

#guard openNestedCaptureTargetIsRejected

/-- Nested grouping suppresses callable identity at every depth:
    `Apply(((Increment)))` fails with the same arity error as
    `Apply((Increment))` — the inner identity never crosses any capture layer. -/
def nestedCaptureStillSuppressesCallableIdentity : Bool :=
  let increment := alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]
  let apply := alg ["f"] [] [] [.call (.param "f") [.num 9]]
  let root := algPrivate [] [] [("Apply", apply), ("Increment", increment)]
    [.call (resolve "Apply") [.capture [.capture [.resolve "Increment"]]]]
  match runResult (.algorithmExpr root) with
  | .error e => innermostIsArityMismatch 1 0 e
  | _ => false

#guard nestedCaptureStillSuppressesCallableIdentity

/-- `(Obj).V` — a capture receiver exposes NO structural members. Structural
    lookup sees only the capture's value thunk (which owns nothing), the
    lexical fallback finds no `V`, and the member stays unresolved — capture
    is not algorithm identity on the receiver channel either. C# parity: the
    probe matrix pins the same failure ("Property 'V' was not found ...").
    Direct dot access on the NAMED property (`Obj.V`) still reaches the
    member. -/
def captureReceiverDoesNotExposeStructuralMembers : Bool :=
  let obj := Algorithm.mk none [] [] [publicProp "V" (alg [] [] [] [.num 7])] []
  let direct := algPrivate [] [] [("Obj", obj)] [.dotCall (.resolve "Obj") "V" none]
  let grouped := algPrivate [] [] [("Obj", obj)] [.dotCall (.capture [.resolve "Obj"]) "V" none]
  (match runResult (.algorithmExpr direct) with
   | .ok (Result.atom 7) => true | _ => false) &&
  (match runResult (.algorithmExpr grouped) with
   | .error _ => true
   | .ok _ => false)

#guard captureReceiverDoesNotExposeStructuralMembers

/-- The named/inline zero-parameter agreement family: a NAMED zero-parameter
    property crosses the higher-order boundary, the INLINE algorithm block
    crosses identically (test19SingleOutputBlockCrossesHigherOrderBoundary),
    and a CAPTURE of the named property does not cross — identity is
    structural (node kind), never a declaration-count taxonomy. -/
def namedZeroParamAlgorithmCrossesHigherOrderBoundary : Bool :=
  let apply := alg ["f"] [] [] [.call (.param "f") []]
  match runFlat (.algorithmExpr (algPrivate [] []
    [("Apply", apply), ("Const", alg [] [] [] [.num 42])] [
    .call (resolve "Apply") [.resolve "Const"]
  ])) with
  | Except.ok [42] => true
  | _ => false

#guard namedZeroParamAlgorithmCrossesHigherOrderBoundary

def capturedNamedZeroParamAlgorithmDoesNotCross : Bool :=
  let apply := alg ["f"] [] [] [.call (.param "f") []]
  match runResult (.algorithmExpr (algPrivate [] []
    [("Apply", apply), ("Const", alg [] [] [] [.num 42])] [
    .call (resolve "Apply") [.capture [.resolve "Const"]]
  ])) with
  | Except.error e => innermostIsNotAnAlgorithm "param(f)" e
  | _ => false

#guard capturedNamedZeroParamAlgorithmDoesNotCross

/-- Host-AST core invariant: a capture AROUND an algorithm block still
    suppresses the block's identity — source parentheses around braces
    normalize away, so this boundary is only reachable on the AST channel,
    and it must behave like every other capture. -/
def capturedAlgorithmExprDoesNotExposeInnerIdentity : Bool :=
  let apply := alg ["f"] [] [] [.call (.param "f") []]
  match runResult (.algorithmExpr (algPrivate [] [] [("Apply", apply)] [
    .call (resolve "Apply") [.capture [.algorithmExpr (alg [] [] [] [.num 42])]]
  ])) with
  | Except.error e => innermostIsNotAnAlgorithm "param(f)" e
  | _ => false

#guard capturedAlgorithmExprDoesNotExposeInnerIdentity

/-- Host-AST open invariant: a capture around an algorithm block is not an
    openable target either — the outer capture is the semantic boundary. -/
def openCapturedAlgorithmExprIsRejected : Bool :=
  let lib := Algorithm.mk none [] [] [publicProp "C" (alg [] [] [] [.num 5])] []
  let viaCapture := algPrivate [] [.capture [.algorithmExpr lib]] [] [.resolve "C"]
  match runResult (.algorithmExpr viaCapture) with
  | .error (Error.badOpenForm _) => true
  | .error (Error.withContext _ (Error.badOpenForm _)) => true
  | _ => false

#guard openCapturedAlgorithmExprIsRejected

end KatLangTests
