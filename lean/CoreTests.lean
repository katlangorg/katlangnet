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

def innermostIsSpreadMissingOutput : Error -> Bool
  | .withContext _ inner => innermostIsSpreadMissingOutput inner
  | .spreadMissingOutput => true
  | _ => false

def innermostIsExplicitParamsRequireOutput : Error -> Bool
  | .withContext _ inner => innermostIsExplicitParamsRequireOutput inner
  | .explicitParamsRequireOutput => true
  | _ => false

def innermostIsSpecialOutputAccess : Error -> Bool
  | .withContext _ inner => innermostIsSpecialOutputAccess inner
  | .specialOutputAccess => true
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

def callableSignatureValidationRejectsMultipleVariadic : Bool :=
  let signature : KatLang.CallableSignature := {
    name := "Bad"
    parameters := [
      { name := "a", kind := KatLang.ParameterKind.variadic },
      { name := "b", kind := KatLang.ParameterKind.variadic }
    ]
  }
  match KatLang.CallableSignature.validate signature with
  | .error (.illegalInEval message) =>
      message = "Callable signature `Bad` cannot contain more than one variadic parameter."
  | _ => false

#guard callableSignatureValidationRejectsMultipleVariadic

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
    { name := "values", kind := .variadic },
    { name := "factor", kind := .normal }
  ] [] [] [.param "values"]
  Algorithm.parameters algorithm == [
    { name := "values", kind := .variadic },
    { name := "factor", kind := .normal }
  ]
  && Algorithm.params algorithm == ["values", "factor"]
  && Algorithm.paramKinds algorithm == [.variadic, .normal]

#guard algorithmParametersPreserveNameAndKindTogether

-- Test 1: Structural property access (0-param) → value access
-- a.X where X has 0 params → evaluates property directly
def propAlg : Algorithm :=
  alg [] [] [] [.num 42]

def receiver1 : Algorithm :=
  algPrivate [] [] [("X", propAlg)] []

def test1 : Bool :=
  match runFlat (.dotCall (.block receiver1) "X" none) with
  | Except.ok [42] => true
  | _ => false

#guard test1
-- EXPECTED: Except.ok [42]
#eval runFlat (.dotCall (.block receiver1) "X" none)

-- Test 2: Structural property with params, no args → arity mismatch (navigation-only)
-- a.F where F(x) = x + 1, no args → error (no receiver injection)
def incAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

def receiver2 : Algorithm :=
  algPrivate [] [] [("F", incAlg)] [.num 10]

def test2a : Bool :=
  match runResult (.dotCall (.block receiver2) "F" none) with
  | Except.error _ => true   -- arity mismatch: F expects 1 arg, got 0
  | Except.ok _ => false

#guard test2a
-- EXPECTED: Except.error (arityMismatch 1 0)
#eval runResult (.dotCall (.block receiver2) "F" none)

-- Test 2b: Structural property with explicit args → direct binding (navigation-only)
-- a.F(10) where F(x) = x + 1 → 11
def test2b : Bool :=
  match runFlat (.dotCall (.block receiver2) "F" (some (alg [] [] [] [.num 10]))) with
  | Except.ok [11] => true
  | _ => false

#guard test2b
-- EXPECTED: Except.ok [11]
#eval runFlat (.dotCall (.block receiver2) "F" (some (alg [] [] [] [.num 10])))

-- Test 2c: Bare use of a parameterized property → arity mismatch with property context
def receiver2c : Algorithm :=
  algPrivate [] [] [("A", alg ["x"] [] [] [.param "x"])] [.resolve "A"]

def test2c : Bool :=
  match runResult (.block receiver2c) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard test2c
-- EXPECTED: Except.error (withContext "while evaluating property A" (arityMismatch 1 0))
#eval runResult (.block receiver2c)

-- direct-call ordinary algorithm tests
--------------------------------------------------------------------------------

def directCallAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

def directCallRoot : Algorithm :=
  algPrivate [] [] [("Algo", directCallAlg)] [
    .call (.resolve "Algo") (alg [] [] [] [.num 6])
  ]

def directCallWorks : Bool :=
  match runFlat (.block directCallRoot) with
  | Except.ok [7] => true
  | _ => false

#guard directCallWorks

def directCallArityRoot : Algorithm :=
  algPrivate [] [] [("Algo", directCallAlg)] [
    .call (.resolve "Algo") (alg [] [] [] [])
  ]

def directCallUsesOwnArity : Bool :=
  match runResult (.block directCallArityRoot) with
  | Except.error err =>
      hasContext "while evaluating call to Algo" err
      && innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard directCallUsesOwnArity

def zeroArgOutputAlg : Algorithm :=
  algPrivate [] [] [] [.num 5]

def zeroArgOutputCallRoot : Algorithm :=
  algPrivate [] [] [("Algo", zeroArgOutputAlg)] [
    .call (.resolve "Algo") (alg [] [] [] [])
  ]

def zeroArgOutputCallWorks : Bool :=
  match runFlat (.block zeroArgOutputCallRoot) with
  | Except.ok [5] => true
  | _ => false

#guard zeroArgOutputCallWorks

def zeroArgOutputRejectsExtraArgsRoot : Algorithm :=
  algPrivate [] [] [("Algo", zeroArgOutputAlg)] [
    .call (.resolve "Algo") (alg [] [] [] [.num 6])
  ]

def zeroArgOutputRejectsExtraArgs : Bool :=
  match runResult (.block zeroArgOutputRejectsExtraArgsRoot) with
  | Except.error err => innermostIsArityMismatch 0 1 err
  | Except.ok _ => false

#guard zeroArgOutputRejectsExtraArgs

def zeroArgPropertyCacheCountedOutputRoot : Algorithm :=
  algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2])
  ] [.resolve "A"]

def zeroArgPropertyCachePreservesCountedOutput : Bool :=
  match KatLang.runResultWithState (.block zeroArgPropertyCacheCountedOutputRoot) with
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
    .call (.resolve "A") (alg [] [] [] [])
  ]

def zeroArgPropertyAndExplicitCallStillEvaluate : Bool :=
  match KatLang.runResultWithState (.block zeroArgPropertyAndExplicitCallRoot) with
  | Except.ok (Result.sequenceValue [Result.atom 3, Result.atom 3], state) =>
      state.zeroArgPropertyCache.length == 1
  | _ => false

#guard zeroArgPropertyAndExplicitCallStillEvaluate

def zeroArgOuterFreshNestedPropertyStyleRoot : Algorithm :=
  algPrivate [] [] [
    ("A", alg [] [] [] [.num 3]),
    ("B", alg [] [] [] [.resolve "A", .resolve "A"])
  ] [
    .call (.resolve "B") (alg [] [] [] [])
  ]

def zeroArgOuterFreshCallKeepsNestedPropertyStyleCache : Bool :=
  match KatLang.runResultWithState (.block zeroArgOuterFreshNestedPropertyStyleRoot) with
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
    .dotCall (.block box) "A" none,
    .dotCall (.block box) "A" none
  ]

def zeroArgStructuralPropertyAccessUsesCache : Bool :=
  match KatLang.runResultWithState (.block zeroArgStructuralPropertyCacheRoot) with
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
  match KatLang.runResultWithState (.block zeroArgBuiltinPropertyCacheRoot) with
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
      .call (.resolve "A") (alg [] [] [] []),
      .call (.resolve "A") (alg [] [] [] [])
    ])
  ] [
    .call (.resolve "C") (alg [] [] [] [])
  ]

def zeroArgExplicitNestedCallsBypassDirectCache : Bool :=
  match KatLang.runResultWithState (.block zeroArgExplicitNestedFreshCallsRoot) with
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
  match KatLang.runResultWithState (.block zeroArgCacheKeyDistinguishesLexicalContextRoot) with
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
    .dotCall (.resolve "Algo") "Helper" (some (alg [] [] [] [.num 6]))
  ]

def helperDotCallStillWorks : Bool :=
  match runFlat (.block helperDotCallRoot) with
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
    .call (.resolve "Algo") (alg [] [] [] [.num 6])
  ]

def capturedLocalHelperStillWorks : Bool :=
  match runFlat (.block capturedLocalHelperRoot) with
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
  match runResult (.block capturedLocalOnlyDotRoot) with
  | Except.error err => innermostIsLocalOnlyProperty "Algo" "Prop" .localCapturedAncestorParams err
  | Except.ok _ => false

#guard capturedLocalOnlyDotRejected

def capturedLocalOnlyDotCallRoot : Algorithm :=
  algPrivate [] [] [("Algo", capturedLocalOnlyAlg)] [
    .dotCall (.resolve "Algo") "Prop" (some (alg [] [] [] [.num 6]))
  ]

def capturedLocalOnlyDotCallRejected : Bool :=
  match runResult (.block capturedLocalOnlyDotCallRoot) with
  | Except.error err => innermostIsLocalOnlyProperty "Algo" "Prop" .localCapturedAncestorParams err
  | Except.ok _ => false

#guard capturedLocalOnlyDotCallRejected

def helperDirectCallStillFailsRoot : Algorithm :=
  algPrivate [] [] [("Algo", helperOutputAlg)] [
    .call (.resolve "Algo") (alg [] [] [] [.num 6])
  ]

def helperDirectCallStillFails : Bool :=
  match runResult (.block helperDirectCallStillFailsRoot) with
  | Except.error err => innermostIsArityMismatch 0 1 err
  | Except.ok _ => false

#guard helperDirectCallStillFails

def parametrizedValuePositionRoot : Algorithm :=
  algPrivate [] [] [("Algo", directCallAlg)] [
    .resolve "Algo"
  ]

def parametrizedValuePositionRejectsBareUse : Bool :=
  match runResult (.block parametrizedValuePositionRoot) with
  | Except.error err =>
      hasContext "while evaluating property Algo" err
      && innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard parametrizedValuePositionRejectsBareUse

def innerDirectAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 10)]

def outerDirectCallAlg : Algorithm :=
  algPrivate [] [] [("Inner", innerDirectAlg)] [
    .call (.resolve "Inner") (alg [] [] [] [.num 5])
  ]

def nestedDirectCallRoot : Algorithm :=
  algPrivate [] [] [("Outer", outerDirectCallAlg)] [
    .resolve "Outer",
    .dotCall (.resolve "Outer") "Inner" (some (alg [] [] [] [.num 5]))
  ]

def nestedDirectCallWorks : Bool :=
  match runFlat (.block nestedDirectCallRoot) with
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
  match runResult (.block conditionalLocalInnerRoot) with
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
  match runResult (.block conditionalSplitHelpersRoot) with
  | Except.error err => innermostIsLocalOnlyProperty "Outer" "Second" .localConditional err
  | Except.ok _ => false

#guard conditionalSplitHelpersRejected

def publicOutputAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

def outputDotCallRejectedRoot : Algorithm :=
  algPrivate [] [] [("Algo", publicOutputAlg)] [
    .dotCall (.resolve "Algo") "Output" (some (alg [] [] [] [.num 6]))
  ]

def outputDotCallRejected : Bool :=
  match runResult (.block outputDotCallRejectedRoot) with
  | Except.error err => innermostIsSpecialOutputAccess err
  | Except.ok _ => false

#guard outputDotCallRejected

def nestedOutputDotCallRejectedRoot : Algorithm :=
  algPrivate [] [] [("Outer", outerDirectCallAlg)] [
    .dotCall (.dotCall (.resolve "Outer") "Inner" none) "Output" (some (alg [] [] [] [.num 6]))
  ]

def nestedOutputDotCallRejected : Bool :=
  match runResult (.block nestedOutputDotCallRejectedRoot) with
  | Except.error err => innermostIsSpecialOutputAccess err
  | Except.ok _ => false

#guard nestedOutputDotCallRejected

def bareOutputAccessRejectedRoot : Algorithm :=
  algPrivate [] [] [("Algo", zeroArgOutputAlg)] [
    .dotCall (.resolve "Algo") "Output" none
  ]

def bareOutputAccessRejected : Bool :=
  match runResult (.block bareOutputAccessRejectedRoot) with
  | Except.error err => innermostIsSpecialOutputAccess err
  | Except.ok _ => false

#guard bareOutputAccessRejected

def stringLiteralSatisfiesInvariant : Bool :=
  KatLang.postElabInvariant (.stringLiteral "abc")

#guard stringLiteralSatisfiesInvariant

def stringOutputAlgSatisfiesInvariant : Bool :=
  KatLang.postElabInvariantAlg (alg [] [] [] [.stringLiteral "abc"])

#guard stringOutputAlgSatisfiesInvariant

def unresolvedLoadViolatesInvariant : Bool :=
  !KatLang.postElabInvariant
    (.call (.resolve "load") (alg [] [] [] [.stringLiteral "https://katlang.org/lib.kat"]))

#guard unresolvedLoadViolatesInvariant

def outputDotCallViolatesInvariant : Bool :=
  !KatLang.postElabInvariant (.dotCall (.resolve "Algo") "Output" none)

#guard outputDotCallViolatesInvariant

def structuralOutputPropertyViolatesInvariant : Bool :=
  !KatLang.postElabInvariantAlg
    (alg [] [] [privateProp "Output" (alg [] [] [] [.num 1])] [.num 2])

#guard structuralOutputPropertyViolatesInvariant

def helperPropertySatisfiesInvariant : Bool :=
  KatLang.postElabInvariantAlg
    (alg [] [] [privateProp "Helper" (alg [] [] [] [.num 1])] [.stringLiteral "abc"])

#guard helperPropertySatisfiesInvariant

--------------------------------------------------------------------------------
-- missingOutput semantics tests
--------------------------------------------------------------------------------

def noOutputGroupAlg : Algorithm :=
  algPrivate [] [] [("X", alg [] [] [] [.num 1])] []

def missingOutputRootOnlyDefinitions : Algorithm :=
  algPrivate [] [] [("A", noOutputGroupAlg)] []

def missingOutputRootOnlyDefinitionsFails : Bool :=
  match runResult (.block missingOutputRootOnlyDefinitions) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputRootOnlyDefinitionsFails

def missingOutputRootWithTrailingOutput : Bool :=
  match runFlat (.block (algPrivate [] [] [("T", alg [] [] [] [.num 4])] [
    .resolve "T"
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard missingOutputRootWithTrailingOutput

def missingOutputRootWithExplicitEmptyOutput : Bool :=
  match runResult (.block (algPrivate [] [] [("T", alg [] [] [] [.num 4])] [
    .emptySequence 0
  ])) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard missingOutputRootWithExplicitEmptyOutput

def missingOutputRootValueDoesNotEqualEmpty : Bool :=
  match runFlat (.block (algPrivate [] [] [("T", alg [] [] [] [.num 4])] [
    .binary .eq (.resolve "T") (.emptySequence 0)
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard missingOutputRootValueDoesNotEqualEmpty

def missingOutputMultipleDefinitionsRoot : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Price", alg [] [] [] [.num 10]),
    ("Tax", alg [] [] [] [.num 2]),
    ("Total", alg [] [] [] [.binary .add (.resolve "Price") (.resolve "Tax")])
  ] [])) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputMultipleDefinitionsRoot

def missingOutputMultipleDefinitionsWithOutput : Bool :=
  match runFlat (.block (algPrivate [] [] [
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
  algPrivate [] [] [("A", noOutputGroupAlg)] [
    .dotCall (.resolve "A") "X" none
  ]

def missingOutputValid2 : Bool :=
  match runFlat (.block missingOutputValid2Root) with
  | Except.ok [1] => true
  | _ => false

#guard missingOutputValid2

def applyMissingOutputAlg : Algorithm :=
  alg ["f"] [] [] [
    .call (.param "f") (alg [] [] [] [.num 4])
  ]

def incMissingOutputAlg : Algorithm :=
  alg ["x"] [] [] [
    .binary .add (.param "x") (.num 1)
  ]

def missingOutputValid3Root : Algorithm :=
  algPrivate [] [] [("Apply", applyMissingOutputAlg), ("Inc", incMissingOutputAlg)] [
    .call (.resolve "Apply") (alg [] [] [] [.resolve "Inc"])
  ]

def missingOutputValid3 : Bool :=
  match runFlat (.block missingOutputValid3Root) with
  | Except.ok [5] => true
  | _ => false

#guard missingOutputValid3

def holderMissingOutputAlg : Algorithm :=
  algPrivate [] [] [("F", noOutputGroupAlg)] [.num 0]

def missingOutputValid4Root : Algorithm :=
  algPrivate [] [] [("Holder", holderMissingOutputAlg)] [.resolve "Holder"]

def missingOutputValid4 : Bool :=
  match runFlat (.block missingOutputValid4Root) with
  | Except.ok [0] => true
  | _ => false

#guard missingOutputValid4

def missingOutputError5Root : Algorithm :=
  algPrivate [] [] [("A", noOutputGroupAlg)] [.resolve "A"]

def missingOutputError5 : Bool :=
  match runResult (.block missingOutputError5Root) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError5

def missingOutputError6Root : Algorithm :=
  algPrivate [] [] [("A", noOutputGroupAlg)] [
    .call (.resolve "A") (alg [] [] [] [])
  ]

def missingOutputError6 : Bool :=
  match runResult (.block missingOutputError6Root) with
  | Except.error err =>
      hasContext "while evaluating call to A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError6

def missingOutputError6bRoot : Algorithm :=
  algPrivate [] [] [("A", noOutputGroupAlg)] [
    .call (.resolve "A") (alg [] [] [] [.num 6])
  ]

def missingOutputError6b : Bool :=
  match runResult (.block missingOutputError6bRoot) with
  | Except.error err =>
      hasContext "while evaluating call to A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError6b

def missingOutputError7Root : Algorithm :=
  algPrivate [] [] [("A", noOutputGroupAlg)] [
    .binary .add (.resolve "A") (.num 1)
  ]

def missingOutputError7 : Bool :=
  match runResult (.block missingOutputError7Root) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError7

def missingOutputError8Root : Algorithm :=
  algPrivate [] [] [("A", noOutputGroupAlg)] [
    .unary .minus (.resolve "A")
  ]

def missingOutputError8 : Bool :=
  match runResult (.block missingOutputError8Root) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError8

def missingOutputError9Root : Algorithm :=
  algPrivate [] [] [
    ("A", noOutputGroupAlg),
    ("B", alg [] [] [] [.resolve "A"])
  ] [
    .resolve "B"
  ]

def missingOutputError9 : Bool :=
  match runResult (.block missingOutputError9Root) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError9

def useMissingOutputAlg : Algorithm :=
  alg ["f"] [] [] [.num 0]

def missingOutputValid10Root : Algorithm :=
  algPrivate [] [] [("A", noOutputGroupAlg), ("Use", useMissingOutputAlg)] [
    .call (.resolve "Use") (alg [] [] [] [.resolve "A"])
  ]

def missingOutputValid10 : Bool :=
  match runFlat (.block missingOutputValid10Root) with
  | Except.ok [0] => true
  | _ => false

#guard missingOutputValid10

--------------------------------------------------------------------------------
-- empty sequence value () tests
--------------------------------------------------------------------------------

def explicitEmptyExpr : KatLang.Expr := .emptySequence 0

-- Postfix spread. `...` is POSTFIX-only source syntax (it never takes a
-- right operand); surface `expr...` is the unary node `sequenceSpread expr`.
-- This helper builds that postfix form. The C# surface parser parses source
-- `A...B` as the expression-list slots `A...`, `B`. The `sequenceConstruct`
-- form here is only an internal/test semantic value and is NOT produced from
-- surface `A...B`.
def sequenceSpread (expr : KatLang.Expr) : KatLang.Expr :=
  .sequenceSpread expr

def sequenceSpreadReceiver (expr : KatLang.Expr) : KatLang.Expr :=
  .block (alg [] [] [] [sequenceSpread expr])

def explicitEmptyOutputBody : KatLang.Expr :=
  .block (alg [] [] [] [explicitEmptyExpr])

def missingOutputBodyExpr : KatLang.Expr :=
  .block (alg [] [] [] [])

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
  match runFlat (.block (algPrivate [] [] [("A", alg [] [] [] [explicitEmptyExpr])] [
    .dotCall explicitEmptyExpr "count" none,
    .call (.resolve "count") (alg [] [] [] [explicitEmptyExpr]),
    .dotCall explicitEmptyOutputBody "count" none,
    .dotCall (.block (alg [] [] [] [explicitEmptyExpr])) "count" none,
    .dotCall (.resolve "A") "count" none
  ])) with
  | Except.ok [0, 0, 0, 0, 0] => true
  | _ => false

#guard explicitEmptyCountsAsZero

def explicitEmptyEquality : Bool :=
  match runFlat (.block (alg [] [] [] [
    .binary .eq explicitEmptyExpr explicitEmptyExpr,
    .binary .ne explicitEmptyExpr explicitEmptyExpr,
    .binary .eq explicitEmptyExpr explicitEmptyOutputBody,
    .binary .eq explicitEmptyOutputBody explicitEmptyExpr,
    -- Collection builtins materialize exact lists, so an all-rejected filter
    -- and an all-skipped skip yield `[]`, which is NOT the empty sequence `()`.
    .binary .eq
      (.call (.resolve "filter") (alg [] [] [] [
        .sequenceConstruct (.num 1) (.sequenceConstruct (.num 3) (.num 5)),
        .block explicitEmptyIsEvenAlg
      ]))
      explicitEmptyExpr,
    .binary .eq
      explicitEmptyExpr
      (.call (.resolve "filter") (alg [] [] [] [
        .sequenceConstruct (.num 1) (.sequenceConstruct (.num 3) (.num 5)),
        .block explicitEmptyIsEvenAlg
      ])),
    .binary .eq
      (.dotCall (.num 0) "skip" (some (alg [] [] [] [.num 1])))
      explicitEmptyExpr
  ])) with
  | Except.ok [1, 0, 1, 1, 0, 0, 0] => true
  | _ => false

#guard explicitEmptyEquality

-- Internal sequence construction of postfix spreads:
-- `sequenceConstruct (sequenceConstruct (sequenceSpread 1) empty) (sequenceSpread 2)`.
-- The `empty` contribution adds no items, so the flat result is [1, 2] — the same
-- flat values the removed two-operand spread form produced, now reached through internal
-- sequence construction of postfix spreads.
def postfixSpreadEmptyJoinContributesNoItems : Bool :=
  match runFlat (.sequenceConstruct
      (.sequenceConstruct (sequenceSpread (.num 1)) explicitEmptyExpr)
      (sequenceSpread (.num 2))) with
  | Except.ok [1, 2] => true
  | _ => false

#guard postfixSpreadEmptyJoinContributesNoItems

-- `()...` spreads the empty sequence value, contributing zero items.
def spreadOfEmptyContributesNoItems : Bool :=
  match runFlat (sequenceSpread explicitEmptyExpr) with
  | Except.ok [] => true
  | _ => false

#guard spreadOfEmptyContributesNoItems

-- A written sequence value with a spread beside a sibling slot splices the
-- spread items: source `A = 1, 2` then `(A..., 99)` is `(1, 2, 99)`, never the
-- grouped `((1, 2), 99)`. This pins `evalAlgOutputCore` as the value
-- projection of `evalAlgOutputCountedCore` (July 2026 fix): the plain and
-- counted evaluators must agree on value-position block output.
def valuePositionSpreadWithSiblingSplices : Bool :=
  match runResult (.block (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2])] [
    .block (alg [] [] [] [sequenceSpread (.resolve "A"), .num 99])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 99]) => true
  | _ => false

#guard valuePositionSpreadWithSiblingSplices

-- The same splicing holds for the root program output observed through the
-- plain `runResult` path: `A..., 99` is three root slots `1, 2, 99`.
def rootSpreadWithSiblingSplices : Bool :=
  match runResult (.block (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2])] [
    sequenceSpread (.resolve "A"), .num 99
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 99]) => true
  | _ => false

#guard rootSpreadWithSiblingSplices

-- Splicing spreads never erases a written non-spread `()` slot between them:
-- `(1..., (), 2...)` keeps the empty sequence value as a visible item.
def spreadSiblingsKeepWrittenEmptySlot : Bool :=
  match runResult (.block (alg [] [] [] [
    .block (alg [] [] [] [sequenceSpread (.num 1), explicitEmptyExpr, sequenceSpread (.num 2)])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [], .atom 2]) => true
  | _ => false

#guard spreadSiblingsKeepWrittenEmptySlot

-- Structural equality observes the spliced value through the plain
-- (non-counted) evaluation path used for binary operands.
def spreadSeqLiteralEqualsFlatLiteral : Bool :=
  match runFlat (.block (algPrivate [] [] [("P", alg [] [] [] [.num 1, .num 2])] [
    .binary .eq (.block (alg [] [] [] [sequenceSpread (.resolve "P"), .num 99]))
      (.block (alg [] [] [] [.num 1, .num 2, .num 99]))
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard spreadSeqLiteralEqualsFlatLiteral

-- INTERNAL-NODE CONTAINMENT (July 2026 audit). `sequenceConstruct` is an
-- internal join node — NOT the representation of written parentheses, which
-- parse to zero-parameter blocks. Its value evaluation DROPS `()` leaves
-- (join semantics: an empty contribution adds no items); written parentheses
-- always keep a non-spread `()` item visible. The guards below pin that
-- intentional difference structurally so any change to either side —
-- including a parser/desugaring change that routes surface syntax through
-- the internal node — is caught. C# twins live in
-- SequenceConstructContainmentTests; Lean/C# agreement on these exact ASTs
-- is enforced by the generated SemanticExplorerCases internal-node section.

-- sequenceConstruct ((), 1) drops the `()` leaf and singleton-collapses to 1 …
def internalSequenceConstructDropsEmptyLeafAndCollapses : Bool :=
  match runResult (.sequenceConstruct (.emptySequence 0) (.num 1)) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard internalSequenceConstructDropsEmptyLeafAndCollapses

-- … while the written form `((), 1)` (a zero-parameter block) keeps the
-- empty item visible. This pair is the intentional-difference contrast.
def writtenParenthesesKeepEmptyItemVisible : Bool :=
  match runResult (.block (alg [] [] [] [.emptySequence 0, .num 1])) with
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
    runResult (.sequenceConstruct (.block (alg [] [] [] [.num 1, .num 2])) (.emptySequence 0)),
    runResult (.block (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2]), .emptySequence 0]))
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
      runResult (.call (.resolve "take") (alg [] [] [] [
        .sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 5)])),
      runResult (.call (.resolve "take") (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2, .num 5])]))
    with
    | Except.error scErr, Except.error groupedErr =>
        innermostIsArityMismatch 2 1 scErr && innermostIsArityMismatch 2 1 groupedErr
    | _, _ => false
  let scBindsLikeGroupedForm :=
    match
      runResult (.call (.resolve "take") (alg [] [] [] [
        .sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 5), .num 2])),
      runResult (.call (.resolve "sum") (alg [] [] [] [
        .sequenceConstruct (.num 1) (.num 2)]))
    with
    | Except.ok (.listValue [.atom 1, .atom 2]), Except.ok (.atom 3) => true
    | _, _ => false
  let scStillDropsEmptyLeaves :=
    match runResult (.call (.resolve "sum") (alg [] [] [] [
      .sequenceConstruct (.sequenceConstruct (.emptySequence 0) (.num 1)) (.num 2)])) with
    | Except.ok (.atom 3) => true
    | _ => false
  loneScErrsLikeGroupedSurfaceForm && scBindsLikeGroupedForm && scStillDropsEmptyLeaves

#guard internalSequenceConstructLoneBuiltinArgBindsLikeGroupedForm

-- Repeated ordinary parentheses around the empty sequence canonicalize to `()`.
def emptyVsNestedEmptyEquality : Bool :=
  match runFlat (.block (alg [] [] [] [
    .binary .eq (.emptySequence 0) (.emptySequence 0),
    .binary .eq (.emptySequence 0) (.emptySequence 1),
    .binary .ne (.emptySequence 0) (.emptySequence 1)
  ])) with
  | Except.ok [1, 1, 0] => true
  | _ => false

#guard emptyVsNestedEmptyEquality

-- The empty sequence value has zero items; redundant empty nesting does too.
def emptyAndNestedEmptyCount : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (.resolve "count") (alg [] [] [] [.emptySequence 0]),
    .call (.resolve "count") (alg [] [] [] [.emptySequence 1])
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
  match runFlat (.block (algPrivate [] [] [("empty", alg [] [] [] [.num 123])] [
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
    runResult (.block (alg [] [] [] [.emptySequence 0])),
    runResult (.block (alg [] [] [] [.emptySequence 1])),
    runResult (.block (alg [] [] [] [.emptySequence 2]))
  with
  | Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []) => true
  | _, _, _, _, _ => false

#guard blockOutputCanonicalizesNestedEmptyDepth

-- Mixed output: a normal non-spread `()` output is a VISIBLE slot, not dropped, so it sits
-- beside other outputs. (Only an explicit spread `()...` contributes zero items.) These would
-- fail if evalAlgOutputCore dropped count-0 non-spread slots.
def mixedOutputKeepsLeadingEmptySlot : Bool :=
  match runResult (.block (alg [] [] [] [.emptySequence 0, .num 1])) with
  | Except.ok (.sequenceValue [.sequenceValue [], .atom 1]) => true
  | _ => false

#guard mixedOutputKeepsLeadingEmptySlot

def mixedOutputKeepsMiddleEmptySlot : Bool :=
  match runResult (.block (alg [] [] [] [.num 1, .emptySequence 0, .num 2])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [], .atom 2]) => true
  | _ => false

#guard mixedOutputKeepsMiddleEmptySlot

-- An explicit spread of `()` still contributes zero items, so it does NOT add a slot:
-- `(()..., 1)` is just `1`.
def mixedOutputSpreadOfEmptyContributesNoSlot : Bool :=
  match runResult (.block (alg [] [] [] [sequenceSpread (.emptySequence 0), .num 1])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard mixedOutputSpreadOfEmptyContributesNoSlot

-- Redundant empty nesting is not a surface way to construct a one-item
-- collection containing `()`; collection builtins see it as the empty collection.
def collectionBuiltinAlwaysTrue : KatLang.Expr := .block (alg ["x"] [] [] [.num 1])

def filterNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "filter")
      (alg [] [] [] [.emptySequence 1, collectionBuiltinAlwaysTrue])) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard filterNestedEmptyInputCanonicalizesToEmptyCollection

def countFilterNestedEmptyInputCanonicalizesToZero : Bool :=
  match runResult (.call (.resolve "count")
      (alg [] [] [] [
        .call (.resolve "filter") (alg [] [] [] [.emptySequence 1, collectionBuiltinAlwaysTrue])
      ])) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard countFilterNestedEmptyInputCanonicalizesToZero

def takeNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "take")
      (alg [] [] [] [.emptySequence 1, .num 1])) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard takeNestedEmptyInputCanonicalizesToEmptyCollection

def skipNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "skip")
      (alg [] [] [] [.emptySequence 1, .num 0])) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard skipNestedEmptyInputCanonicalizesToEmptyCollection

def distinctNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "distinct")
      (alg [] [] [] [.emptySequence 1])) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard distinctNestedEmptyInputCanonicalizesToEmptyCollection

-- Filtering a two-item collection down to one kept `(1, 2)` materializes the
-- exact one-element list `[(1, 2)]`: collection-producing builtins never apply
-- singleton-boundary erasure to their list results — the kept sequence value
-- stays one exact element (`[(1, 2)]` is a writable KatLang value).
def filterSingleKeptSequenceValueItemStaysExactElement : Bool :=
  let keepFirstPair : KatLang.Expr := .block (alg ["pair"] [] [] [
    .binary .eq (.index (.param "pair") (.num 0)) (.num 1)
  ])
  match runResult (.call (.resolve "filter")
      (alg [] [] [] [
        sequenceItems [
          .block (alg [] [] [] [.num 1, .num 2]),
          .block (alg [] [] [] [.num 3, .num 4])
        ],
        keepFirstPair
      ])) with
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard filterSingleKeptSequenceValueItemStaysExactElement

-- An internal `sequenceConstruct (sequenceSpread A) B` is ONE sequence-value argument in
-- fixed-arity call-argument position and therefore fails to bind a two-parameter
-- call. Surface `A...B` is now an expression list, not this constructed value.
-- The old binary `sequenceSpread A B` that spread two arguments is no longer
-- representable in the AST, so there is nothing to contrast against here.
def postfixSpreadThenJoinIsOneSequenceValueArgument : Bool :=
  let useTwo := alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")]
  let joined := algPrivate [] [] [("A", alg [] [] [] [.num 1]), ("F", useTwo)] [
    .call (.resolve "F") (alg [] [] [] [.sequenceConstruct (sequenceSpread (.resolve "A")) (.num 2)])
  ]
  match runFlat (.block joined) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | _ => false

#guard postfixSpreadThenJoinIsOneSequenceValueArgument

-- Source `1` followed by `depth` postfix `...` operators is the unary chain
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
  match runResult (.block (alg [] [] [] [joined])),
        KatLang.runEvalM (KatLang.evalCounted joined { callStack := [KatLang.preludeAlg], algEnv := [] } []) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]),
    Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3], 1) => true
  | _, _ => false

#guard sequenceConstructCommaPriorityConstructsOneValue

def sequenceConstructExplicitSequenceValueBoundaryProtected : Bool :=
  let joined := .sequenceConstruct (.block (alg [] [] [] [.num 1, .num 2])) (.num 3)
  match runResult (.block (alg [] [] [] [joined])),
        KatLang.runEvalM (KatLang.evalCounted joined { callStack := [KatLang.preludeAlg], algEnv := [] } []) with
  | Except.ok (.sequenceValue [.sequenceValue [.atom 1, .atom 2], .atom 3]),
    Except.ok (.sequenceValue [.sequenceValue [.atom 1, .atom 2], .atom 3], 1) => true
  | _, _ => false

#guard sequenceConstructExplicitSequenceValueBoundaryProtected

def sequenceConstructMaterializedCommaRows : Bool :=
  let leftRow := .block (alg [] [] [] [.num 1, .num 2, .num 3])
  let rightRow := .block (alg [] [] [] [.num 4, .num 5, .num 6])
  let table := .sequenceConstruct leftRow rightRow
  match runResult (.block (alg [] [] [] [table])),
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
  match runResult (.block (alg [] [] [] [leftNested])), runResult (.block (alg [] [] [] [rightNested])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]),
    Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]) => true
  | _, _ => false

#guard sequenceConstructNestedAssociativeAtConstructedValueLevel

def explicitSequenceValueTripleStaysOneTopLevelValue : Bool :=
  let sequenceValueTriple := .block (alg [] [] [] [.num 1, .num 2, .num 3])
  let constructedTriple := .sequenceConstruct (.num 1) (.sequenceConstruct (.num 2) (.num 3))
  let sequenceValueCount := .call (.resolve "count") (alg [] [] [] [sequenceValueTriple])
  let constructedCount := .call (.resolve "count") (alg [] [] [] [constructedTriple])
  match runResult (.block (alg [] [] [] [sequenceValueTriple])), runFlat sequenceValueCount, runFlat constructedCount with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]), Except.ok [3], Except.ok [3] => true
  | _, _, _ => false

#guard explicitSequenceValueTripleStaysOneTopLevelValue

def mixedCommaSequenceConstructPreservesRootSlots : Bool :=
  let mixed := alg [] [] [] [.num 1, .sequenceConstruct (.num 2) (.num 3)]
  match runResult (.block mixed) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) => true
  | _ => false

#guard mixedCommaSequenceConstructPreservesRootSlots

def sequenceSpreadAfterSequenceConstructMatchesSequenceValueForm : Bool :=
  let concise :=
    sequenceSpread (.sequenceConstruct (.num 1) (.num 2))
  let sequenceValue :=
    sequenceSpread (.block (alg [] [] [] [.sequenceConstruct (.num 1) (.num 2)]))
  match runFlat concise, runFlat sequenceValue with
  | Except.ok [1, 2], Except.ok [1, 2] => true
  | _, _ => false

#guard sequenceSpreadAfterSequenceConstructMatchesSequenceValueForm

-- Rest-only `X(values...)` consumes an item supply, so both the explicit-spread
-- form `X((1, b)...)` and the constructed sequence-value form `X((1, b))` bind the
-- same two top-level items [1, (2, 3)]: count 2.
def sequenceSpreadAfterSequenceConstructMatchesConstructedSequenceValue : Bool :=
  let countValues := algWithParameters [{ name := "values", kind := .variadic }] [] [] [
    .dotCall (.param "values") "count" none
  ]
  let multiB := alg [] [] [] [.num 2, .num 3]
  let explicitSpreadForm := algPrivate [] [] [("b", multiB), ("X", countValues)] [
    .call (.resolve "X") (alg [] [] [] [
      sequenceSpread (.sequenceConstruct (.num 1) (.resolve "b"))
    ])
  ]
  let constructedArgForm := algPrivate [] [] [("b", multiB), ("X", countValues)] [
    .call (.resolve "X") (alg [] [] [] [
      .sequenceConstruct (.num 1) (.resolve "b")
    ])
  ]
  let explicitSpreadOk :=
    match runFlat (.block explicitSpreadForm) with
    | Except.ok [2] => true
    | _ => false
  let constructedArgOk :=
    match runFlat (.block constructedArgForm) with
    | Except.ok [2] => true
    | _ => false
  explicitSpreadOk && constructedArgOk

#guard sequenceSpreadAfterSequenceConstructMatchesConstructedSequenceValue

def missingOutputBodyAsResultStillFails : Bool :=
  match runResult (.block (alg [] [] [] [missingOutputBodyExpr])) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputBodyAsResultStillFails

def missingOutputBodyCountStillFails : Bool :=
  let dotCount :=
    match runResult (.dotCall missingOutputBodyExpr "count" none) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  let plainCount :=
    match runResult (.call (.resolve "count") (alg [] [] [] [missingOutputBodyExpr])) with
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
    match runResult (.block (algPrivate [] [] [("Lib", explicitEmptyNoOutputContainer)] [
      .dotCall (.resolve "Lib") "count" none
    ])) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  let equalityFails :=
    match runResult (.block (algPrivate [] [] [("Lib", explicitEmptyNoOutputContainer)] [
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
  match runResult (.block (algPrivate [] [] [("Algo", invalidExplicitParamClauseAlg)] [.num 0])) with
  | Except.error err => innermostIsExplicitParamsRequireOutput err
  | Except.ok _ => false

#guard explicitParamsWithoutOutputRejectedAtRun

def parameterizedChildPropertyContainer : Algorithm :=
  algPrivate [] [] [("Prop", alg ["x", "y"] [] [] [.num 7])] []

def parameterizedChildPropertyWithoutOuterParamsStillValid : Bool :=
  match runFlat (.block (algPrivate [] [] [("Algo", parameterizedChildPropertyContainer)] [
    .dotCall (.resolve "Algo") "Prop" (some (alg [] [] [] [.num 1, .num 2]))
  ])) with
  | Except.ok [7] => true
  | _ => false

#guard parameterizedChildPropertyWithoutOuterParamsStillValid

-- Test 3: Extension property call (lexical fallback)
-- Receiver has no G, but lexical scope defines G(x) = x * 2
-- Receiver output = 5 → 10
def extAlg : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]

def outer3 : Algorithm :=
  algPrivate [] [] [("G", extAlg)] [
    .dotCall (.block (alg [] [] [] [.num 5])) "G" none
  ]

def test3 : Bool :=
  match runFlat (.block outer3) with
  | Except.ok [10] => true
  | _ => false

#guard test3
-- EXPECTED: Except.ok [10]
#eval runFlat (.block outer3)

def userVariadicDotCallCountItemsAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .variadic }] [] [] [
    .dotCall (.param "items") "count" none
  ]

def userVariadicDotCallCountItemsRoot : Algorithm :=
  algPrivate [] [] [("CountItems", userVariadicDotCallCountItemsAlg)] [
    .dotCall (.block (alg [] [] [] [.num 1, .num 2])) "CountItems" none
  ]

def userVariadicDotCallReceiverCountsTopLevelItems : Bool :=
  match runFlat (.block userVariadicDotCallCountItemsRoot) with
  | Except.ok [2] => true
  | _ => false

#guard userVariadicDotCallReceiverCountsTopLevelItems

def userVariadicDotCallMeanAlg : Algorithm :=
  algWithParameters [{ name := "vector", kind := .variadic }] [] [] [
    .dotCall (.param "vector") "sum" none
  ]

def userVariadicDotCallMeanRoot : Algorithm :=
  algPrivate [] [] [("Mean", userVariadicDotCallMeanAlg)] [
    .dotCall (.block (alg [] [] [] [.num 1, .num 2])) "Mean" none
  ]

def userVariadicDotCallReceiverBindsTopLevelItems : Bool :=
  match runFlat (.block userVariadicDotCallMeanRoot) with
  | Except.ok [3] => true
  | _ => false

#guard userVariadicDotCallReceiverBindsTopLevelItems

def userNonVariadicDotCallCountOneAlg : Algorithm :=
  alg ["value"] [] [] [
    .dotCall (.param "value") "count" none
  ]

def userNonVariadicDotCallCountOneRoot : Algorithm :=
  algPrivate [] [] [("CountOne", userNonVariadicDotCallCountOneAlg)] [
    .dotCall (.block (alg [] [] [] [.num 1, .num 2])) "CountOne" none
  ]

def userNonVariadicDotCallReceiverIsOneSequenceArgument : Bool :=
  match runFlat (.block userNonVariadicDotCallCountOneRoot) with
  | Except.ok [2] => true
  | _ => false

#guard userNonVariadicDotCallReceiverIsOneSequenceArgument

def flatVariadicSlotQmeanAlg : Algorithm :=
  algWithParameters [{ name := "args", kind := .variadic }] [] [] [
    .binary .div
      (.dotCall (.param "args") "sum" none)
      (.dotCall (.param "args") "count" none)
  ]

def flatVariadicSlotVectorAlg : Algorithm :=
  alg [] [] [] [.call (.resolve "range") (alg [] [] [] [.num 1, .num 3])]

def flatVariadicSlotQmeanNormalRoot : Algorithm :=
  algPrivate [] [] [("Vector", flatVariadicSlotVectorAlg), ("Qmean", flatVariadicSlotQmeanAlg)] [
    .call (.resolve "Qmean") (alg [] [] [] [.resolve "Vector"])
  ]

def flatVariadicSlotQmeanNormalCallWorks : Bool :=
  match runFlat (.block flatVariadicSlotQmeanNormalRoot) with
  | Except.ok [2] => true
  | _ => false

#guard flatVariadicSlotQmeanNormalCallWorks

def flatVariadicSlotQmeanExplicitRoot : Algorithm :=
  algPrivate [] [] [("Vector", flatVariadicSlotVectorAlg), ("Qmean", flatVariadicSlotQmeanAlg)] [
    .call (.resolve "Qmean") (alg [] [] [] [sequenceSpread (.resolve "Vector")])
  ]

-- Rest-only `Qmean(values...)` consumes an item supply, so the explicit-spread
-- form `Qmean(Vector...)` binds the same items as `Qmean(Vector)`: both give 2.
def flatVariadicSlotQmeanExplicitSpreadMatchesNormalCall : Bool :=
  match runFlat (.block flatVariadicSlotQmeanExplicitRoot) with
  | Except.ok [2] => true
  | _ => false

#guard flatVariadicSlotQmeanExplicitSpreadMatchesNormalCall

def flatVariadicSlotQmeanDotRoot : Algorithm :=
  algPrivate [] [] [("Vector", flatVariadicSlotVectorAlg), ("Qmean", flatVariadicSlotQmeanAlg)] [
    .dotCall (.resolve "Vector") "Qmean" none
  ]

def flatVariadicSlotQmeanDotCallStillWorks : Bool :=
  match runFlat (.block flatVariadicSlotQmeanDotRoot) with
  | Except.ok [2] => true
  | _ => false

#guard flatVariadicSlotQmeanDotCallStillWorks

def flatVariadicSlotCountAlg : Algorithm :=
  algWithParameters [{ name := "args", kind := .variadic }] [] [] [
    .dotCall (.param "args") "count" none
  ]

def flatVariadicSlotValuesAlg : Algorithm :=
  alg [] [] [] [.num 10, .num 20]

def flatVariadicSlotCountValuesRoot : Algorithm :=
  algPrivate [] [] [("Values", flatVariadicSlotValuesAlg), ("Count", flatVariadicSlotCountAlg)] [
    .call (.resolve "Count") (alg [] [] [] [.resolve "Values"])
  ]

def flatVariadicSlotMultiOutputPropertySpreadsItems : Bool :=
  match runFlat (.block flatVariadicSlotCountValuesRoot) with
  | Except.ok [2] => true
  | _ => false

#guard flatVariadicSlotMultiOutputPropertySpreadsItems

def flatVariadicSlotSequenceValuePairAlg : Algorithm :=
  alg [] [] [] [.block (alg [] [] [] [.num 10, .num 20])]

def flatVariadicSlotCountSequenceValuePairRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatVariadicSlotSequenceValuePairAlg), ("Count", flatVariadicSlotCountAlg)] [
    .call (.resolve "Count") (alg [] [] [] [.resolve "Pair"])
  ]

def flatVariadicSlotVisibleSequenceValueIsConsumedAsSequenceValue : Bool :=
  match runFlat (.block flatVariadicSlotCountSequenceValuePairRoot) with
  | Except.ok [2] => true
  | _ => false

#guard flatVariadicSlotVisibleSequenceValueIsConsumedAsSequenceValue

def flatVariadicSlotSumAlg : Algorithm :=
  algWithParameters [
    { name := "values", kind := .variadic },
    { name := "last", kind := .normal }
  ] [] [] [
    .binary .add (.dotCall (.param "values") "sum" none) (.param "last")
  ]

def flatVariadicSlotSumNormalRoot : Algorithm :=
  algPrivate [] [] [("Values", flatVariadicSlotValuesAlg), ("Sum", flatVariadicSlotSumAlg)] [
    .call (.resolve "Sum") (alg [] [] [] [.resolve "Values", .num 7])
  ]

def flatVariadicSlotPrefixSuffixAllocatedBeforeSpread : Bool :=
  match runFlat (.block flatVariadicSlotSumNormalRoot) with
  | Except.ok [37] => true
  | _ => false

#guard flatVariadicSlotPrefixSuffixAllocatedBeforeSpread

def flatVariadicSlotSumExplicitRoot : Algorithm :=
  algPrivate [] [] [("Values", flatVariadicSlotValuesAlg), ("Sum", flatVariadicSlotSumAlg)] [
    .call (.resolve "Sum") (alg [] [] [] [sequenceSpread (.resolve "Values")])
  ]

def flatVariadicSlotExplicitSpreadCanSatisfySuffix : Bool :=
  match runFlat (.block flatVariadicSlotSumExplicitRoot) with
  | Except.ok [30] => true
  | _ => false

#guard flatVariadicSlotExplicitSpreadCanSatisfySuffix

def flatVariadicSlotSumSingleNormalRoot : Algorithm :=
  algPrivate [] [] [("Values", flatVariadicSlotValuesAlg), ("Sum", flatVariadicSlotSumAlg)] [
    .call (.resolve "Sum") (alg [] [] [] [.resolve "Values"])
  ]

-- Sum(values..., last) receives one sequence-valued argument. Function-call
-- binding does not implicitly open it, so `last` receives the sequence value and
-- the old numeric body no longer succeeds.
def flatVariadicSlotNormalSegmentDoesNotSatisfySuffixBySpreading : Bool :=
  match runResult (.block flatVariadicSlotSumSingleNormalRoot) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard flatVariadicSlotNormalSegmentDoesNotSatisfySuffixBySpreading

def flatVariadicSlotSumDotMissingSuffixRoot : Algorithm :=
  algPrivate [] [] [("Values", flatVariadicSlotValuesAlg), ("Sum", flatVariadicSlotSumAlg)] [
    .dotCall (.resolve "Values") "Sum" none
  ]

-- Same boundary through a dot-call receiver: Values.Sum passes the receiver as
-- one leading argument unless explicit spread is used.
def flatVariadicSlotDotReceiverDoesNotSatisfySuffixBySpreading : Bool :=
  match runResult (.block flatVariadicSlotSumDotMissingSuffixRoot) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard flatVariadicSlotDotReceiverDoesNotSatisfySuffixBySpreading

def flatVariadicSlotSumDotSuffixRoot : Algorithm :=
  algPrivate [] [] [("Values", flatVariadicSlotValuesAlg), ("Sum", flatVariadicSlotSumAlg)] [
    .dotCall (.resolve "Values") "Sum" (some (alg [] [] [] [.num 7]))
  ]

def flatVariadicSlotDotReceiverWithSuffixWorks : Bool :=
  match runFlat (.block flatVariadicSlotSumDotSuffixRoot) with
  | Except.ok [37] => true
  | _ => false

#guard flatVariadicSlotDotReceiverWithSuffixWorks

def flatFixedSlotAddAlg : Algorithm :=
  alg ["x", "y"] [] [] [.binary .add (.param "x") (.param "y")]

def flatFixedSlotAddPairRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatVariadicSlotValuesAlg), ("Add", flatFixedSlotAddAlg)] [
    .call (.resolve "Add") (alg [] [] [] [.resolve "Pair"])
  ]

def flatFixedCallStillDoesNotAutoSpread : Bool :=
  match runResult (.block flatFixedSlotAddPairRoot) with
  | Except.error _ => true
  | Except.ok _ => false

#guard flatFixedCallStillDoesNotAutoSpread

def flatFixedSlotAddPairExplicitRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatVariadicSlotValuesAlg), ("Add", flatFixedSlotAddAlg)] [
    .call (.resolve "Add") (alg [] [] [] [sequenceSpread (.resolve "Pair")])
  ]

def flatFixedCallExplicitSpreadStillWorks : Bool :=
  match runFlat (.block flatFixedSlotAddPairExplicitRoot) with
  | Except.ok [30] => true
  | _ => false

#guard flatFixedCallExplicitSpreadStillWorks

def variadicForwardingCountItemsAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .variadic }] [] [] [
    .dotCall (.param "items") "count" none
  ]

def variadicForwardingUseValuesAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }] [] [] [
    .call (.resolve "CountItems") (alg [] [] [] [.param "values"])
  ]

def variadicForwardingTopLevelRoot : Algorithm :=
  algPrivate [] [] [("CountItems", variadicForwardingCountItemsAlg), ("Use", variadicForwardingUseValuesAlg)] [
    .call (.resolve "Use") (alg [] [] [] [sequenceItems [.num 1, .num 2, .num 3]])
  ]

def variadicForwardingTopLevelCaptureStillWorks : Bool :=
  match runFlat (.block variadicForwardingTopLevelRoot) with
  | Except.ok [3] => true
  | _ => false

#guard variadicForwardingTopLevelCaptureStillWorks

def variadicForwardingUseSequenceValueHistoryAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .variadic }]
  ] [] [] [
    .call (.resolve "CountItems") (alg [] [] [] [.param "history"])
  ]

def variadicForwardingSequenceValueRoot : Algorithm :=
  algPrivate [] [] [("CountItems", variadicForwardingCountItemsAlg), ("Use", variadicForwardingUseSequenceValueHistoryAlg)] [
    .call (.resolve "Use") (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2, .num 3])])
  ]

def variadicForwardingSequenceValueCaptureStillWorks : Bool :=
  match runFlat (.block variadicForwardingSequenceValueRoot) with
  | Except.ok [3] => true
  | _ => false

#guard variadicForwardingSequenceValueCaptureStillWorks

def sequenceValueVariadicBoundaryCountSequenceValueAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "items", kind := .variadic }]
  ] [] [] [
    .dotCall (.param "items") "count" none
  ]

def sequenceValueVariadicBoundaryRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatVariadicSlotValuesAlg), ("CountSequenceValue", sequenceValueVariadicBoundaryCountSequenceValueAlg)] [
    .call (.resolve "CountSequenceValue") (alg [] [] [] [.resolve "Pair"])
  ]

def sequenceValueVariadicBoundaryDoesNotUseFlatSlotSpread : Bool :=
  match runFlat (.block sequenceValueVariadicBoundaryRoot) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceValueVariadicBoundaryDoesNotUseFlatSlotSpread

def explicitCallSiteSequenceValue123 : Nat -> KatLang.Expr
  | 0 => .block (alg [] [] [] [.num 1, .num 2, .num 3])
  | Nat.succ depth => .block (alg [] [] [] [explicitCallSiteSequenceValue123 depth])

def explicitCallSiteSequenceValueLeftNested : KatLang.Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2]), .num 3])

def explicitCallSiteSequenceValueRightNested : KatLang.Expr :=
  .block (alg [] [] [] [.num 1, .block (alg [] [] [] [.num 2, .num 3])])

def explicitCallSiteSequenceValueCountSequenceValue1Alg : Algorithm :=
  algWithParameterPatterns [
    .capture { name := "values", kind := .variadic }
  ] [] [] [
    .dotCall (.param "values") "count" none
  ]

def explicitCallSiteSequenceValueCountSequenceValue2Alg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "values", kind := .variadic }]
  ] [] [] [
    .dotCall (.param "values") "count" none
  ]

def explicitCallSiteSequenceValueCountSequenceValue3Alg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.sequenceValue [.capture { name := "values", kind := .variadic }]]
  ] [] [] [
    .dotCall (.param "values") "count" none
  ]

def explicitCallSiteSequenceValueMatrixRoot : Algorithm :=
  algPrivate [] [] [
    ("CountSequenceValue1", explicitCallSiteSequenceValueCountSequenceValue1Alg),
    ("CountSequenceValue2", explicitCallSiteSequenceValueCountSequenceValue2Alg),
    ("CountSequenceValue3", explicitCallSiteSequenceValueCountSequenceValue3Alg)
  ] [
    .call (.resolve "CountSequenceValue1") (alg [] [] [] [explicitCallSiteSequenceValue123 0]),
    .call (.resolve "CountSequenceValue1") (alg [] [] [] [explicitCallSiteSequenceValue123 1]),
    .call (.resolve "CountSequenceValue2") (alg [] [] [] [explicitCallSiteSequenceValue123 0]),
    .call (.resolve "CountSequenceValue2") (alg [] [] [] [explicitCallSiteSequenceValue123 1]),
    .call (.resolve "CountSequenceValue2") (alg [] [] [] [explicitCallSiteSequenceValue123 2]),
    .call (.resolve "CountSequenceValue3") (alg [] [] [] [explicitCallSiteSequenceValue123 1]),
    .call (.resolve "CountSequenceValue3") (alg [] [] [] [explicitCallSiteSequenceValue123 2]),
    .call (.resolve "CountSequenceValue2") (alg [] [] [] [explicitCallSiteSequenceValueLeftNested]),
    .call (.resolve "CountSequenceValue2") (alg [] [] [] [explicitCallSiteSequenceValueRightNested])
  ]

def sequenceValueVariadicParameterRespectsExplicitCallSiteSequenceValueDepth : Bool :=
  match runFlat (.block explicitCallSiteSequenceValueMatrixRoot) with
  | Except.ok [3, 3, 3, 3, 3, 3, 3, 2, 2] => true
  | _ => false

#guard sequenceValueVariadicParameterRespectsExplicitCallSiteSequenceValueDepth

def nestedSequenceValueVariadicParameterRejectsTooShallowExplicitSequenceValue : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("CountSequenceValue3", explicitCallSiteSequenceValueCountSequenceValue3Alg)
  ] [
    .call (.resolve "CountSequenceValue3") (alg [] [] [] [explicitCallSiteSequenceValue123 0])
  ])) with
  | Except.error err => innermostIsArityMismatch 1 3 err
  | _ => false

#guard nestedSequenceValueVariadicParameterRejectsTooShallowExplicitSequenceValue

def explicitPropertyReferenceSequenceValueRoot : Algorithm :=
  algPrivate [] [] [
    ("Inner", alg [] [] [] [explicitCallSiteSequenceValue123 0]),
    ("CountSequenceValue2", explicitCallSiteSequenceValueCountSequenceValue2Alg)
  ] [
    .call (.resolve "CountSequenceValue2") (alg [] [] [] [.resolve "Inner"]),
    .call (.resolve "CountSequenceValue2") (alg [] [] [] [.block (alg [] [] [] [.resolve "Inner"])]),
    .call (.resolve "CountSequenceValue2") (alg [] [] [] [.block (alg [] [] [] [.block (alg [] [] [] [.resolve "Inner"])])])
  ]

def explicitPropertyReferenceSequenceValueIsSourceBacked : Bool :=
  match runFlat (.block explicitPropertyReferenceSequenceValueRoot) with
  | Except.ok [3, 3, 3] => true
  | _ => false

#guard explicitPropertyReferenceSequenceValueIsSourceBacked

-- Test 4: Ambiguous extension via opens (error case)
-- Two opens both export G → ambiguousOpen error
def libA : Algorithm :=
  alg [] [] [publicProp "G" (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)])] []

def libB : Algorithm :=
  alg [] [] [publicProp "G" (alg ["x"] [] [] [.binary .add (.param "x") (.num 2)])] []

def caller4 : Algorithm :=
  alg [] [.block libA, .block libB] [] [
    .dotCall (.block (alg [] [] [] [.num 5])) "G" none
  ]

def test4 : Bool :=
  match runResult (.block caller4) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test4
-- EXPECTED: Expect.error (Error.ambiguousOpen "G" [...])
#eval runResult (.block caller4)

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
  match runFlat (.block openPrivateHeadLaterRoot) with
  | Except.ok [1] => true
  | _ => false

#guard openPrivateHeadLaterWorks

def openDoesNotExposePrivateMemberRoot : Algorithm :=
  algPrivate [] [.resolve "Lib"] [("Lib", openPrivateHeadLib)] [.resolve "Hidden"]

def openDoesNotExposePrivateMember : Bool :=
  match runResult (.block openDoesNotExposePrivateMemberRoot) with
  | Except.error err => innermostIsUnknownName "Hidden" err
  | Except.ok _ => false

#guard openDoesNotExposePrivateMember

def openMissingHeadRoot : Algorithm :=
  alg [] [.resolve "Missing"] [] [.resolve "X"]

def openMissingHeadStillErrors : Bool :=
  match runResult (.block openMissingHeadRoot) with
  | Except.error err =>
      hasContext "while resolving open: Missing" err
      && innermostIsUnknownName "Missing" err
  | Except.ok _ => false

#guard openMissingHeadStillErrors

def openBuiltinTargetRoot : Algorithm :=
  alg [] [.resolve "if"] [] [.resolve "X"]

def openBuiltinTargetStillIllegal : Bool :=
  match runResult (.block openBuiltinTargetRoot) with
  | Except.error err =>
      hasContext "while resolving open: if" err
      && innermostIsIllegalInOpen "builtin 'if'" err
  | Except.ok _ => false

#guard openBuiltinTargetStillIllegal

def openQualifiedPrivatePathRoot : Algorithm :=
  algPrivate [] [.dotCall (.resolve "Lib") "PrivateSub" none] [("Lib", openPrivateHeadLib)] [.resolve "Y"]

def openQualifiedPrivatePathStillRestricted : Bool :=
  match runResult (.block openQualifiedPrivatePathRoot) with
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
    .call (.resolve "PrivateHelper") (alg [] [] [] [.param "N"])
  ]

def publicWrapperPrivateHelperLib : Algorithm :=
  alg [] [] [
    privateProp "PrivateHelper" publicWrapperPrivateHelperAlg,
    publicProp "PublicApi" publicWrapperPrivateHelperApi
  ] []

def publicWrapperPrivateHelperOpenRoot : Algorithm :=
  alg [] [.block publicWrapperPrivateHelperLib] [] [
    .call (.resolve "PublicApi") (alg [] [] [] [.num 5])
  ]

def publicWrapperPrivateHelperImportsPublicApi : Bool :=
  match runFlat (.block publicWrapperPrivateHelperOpenRoot) with
  | Except.ok [6] => true
  | _ => false

#guard publicWrapperPrivateHelperImportsPublicApi

def publicWrapperPrivateHelperHiddenRoot : Algorithm :=
  alg [] [.block publicWrapperPrivateHelperLib] [] [
    .call (.resolve "PrivateHelper") (alg [] [] [] [.num 5])
  ]

def publicWrapperPrivateHelperKeepsPrivateHelperHidden : Bool :=
  match runResult (.block publicWrapperPrivateHelperHiddenRoot) with
  | Except.error err => innermostIsUnknownName "PrivateHelper" err
  | Except.ok _ => false

#guard publicWrapperPrivateHelperKeepsPrivateHelperHidden

def openedMemberBuiltinIfAlg : Algorithm :=
  alg ["x"] [] [] [
    .call (.resolve "if") (alg [] [] [] [
      .binary .gt (.param "x") (.num 0),
      .num 1,
      .num 0
    ])
  ]

def openedMemberBuiltinIfVec : Algorithm :=
  alg [] [] [publicProp "Test" openedMemberBuiltinIfAlg] []

def openedMemberBuiltinIfRoot : Algorithm :=
  algPrivate [] [.resolve "Vec"] [("Vec", openedMemberBuiltinIfVec)] [
    .call (.resolve "Test") (alg [] [] [] [.num 35])
  ]

def openedMemberBuiltinIfWorks : Bool :=
  match runFlat (.block openedMemberBuiltinIfRoot) with
  | Except.ok [1] => true
  | _ => false

#guard openedMemberBuiltinIfWorks

def openedMemberBuiltinSumVec : Algorithm :=
  alg [] [] [publicProp "SumPair" (alg ["x", "y"] [] [] [
    .dotCall (.block (alg [] [] [] [.param "x", .param "y"])) "sum" none
  ])] []

def openedMemberBuiltinSumRoot : Algorithm :=
  algPrivate [] [.resolve "Vec"] [("Vec", openedMemberBuiltinSumVec)] [
    .call (.resolve "SumPair") (alg [] [] [] [.num 3, .num 4])
  ]

def openedMemberBuiltinSumWorks : Bool :=
  match runFlat (.block openedMemberBuiltinSumRoot) with
  | Except.ok [7] => true
  | _ => false

#guard openedMemberBuiltinSumWorks

def inlineOpenedMemberBuiltinSumVec : Algorithm :=
  alg [] [] [publicProp "SumPair" (alg ["x", "y"] [] [] [
    .dotCall (.block (alg [] [] [] [.param "x", .param "y"])) "sum" none
  ])] []

def inlineOpenedMemberBuiltinSumRoot : Algorithm :=
  alg [] [.block inlineOpenedMemberBuiltinSumVec] [] [
    .call (.resolve "SumPair") (alg [] [] [] [.num 3, .num 4])
  ]

def inlineOpenedMemberBuiltinSumWorks : Bool :=
  match runFlat (.block inlineOpenedMemberBuiltinSumRoot) with
  | Except.ok [7] => true
  | _ => false

#guard inlineOpenedMemberBuiltinSumWorks

def inlineOpenedMemberBuiltinSumShadowVec : Algorithm :=
  alg [] [] [publicProp "Use" (alg [] [] [] [
    .dotCall (.block (alg [] [] [] [.num 1, .num 2])) "sum" none
  ])] []

def inlineOpenedMemberBuiltinSumShadowRoot : Algorithm :=
  algPrivate [] [.block inlineOpenedMemberBuiltinSumShadowVec] [
    ("sum", alg [] [] [] [.num 99])
  ] [.resolve "Use"]

def inlineOpenedMemberBuiltinSumIgnoresOpenerShadow : Bool :=
  match runFlat (.block inlineOpenedMemberBuiltinSumShadowRoot) with
  | Except.ok [3] => true
  | _ => false

#guard inlineOpenedMemberBuiltinSumIgnoresOpenerShadow

def openedMemberDefinitionSiteCaptureVec : Algorithm :=
  alg [] [] [
    publicProp "Test" (alg ["x"] [] [] [.binary .add (.resolve "A") (.param "x")])
  ] []

def openedMemberDefinitionSiteCaptureScope : Algorithm :=
  algPrivate [] [.resolve "Vec"] [("A", alg [] [] [] [.num 100])] [
    .call (.resolve "Test") (alg [] [] [] [.num 5])
  ]

def openedMemberDefinitionSiteCaptureRoot : Algorithm :=
  algPrivate [] [] [
    ("A", alg [] [] [] [.num 10]),
    ("Vec", openedMemberDefinitionSiteCaptureVec),
    ("Scope", openedMemberDefinitionSiteCaptureScope)
  ] [.resolve "Scope"]

def openedMemberUsesDefinitionSiteNotOpenerSite : Bool :=
  match runFlat (.block openedMemberDefinitionSiteCaptureRoot) with
  | Except.ok [15] => true
  | _ => false

#guard openedMemberUsesDefinitionSiteNotOpenerSite

-- Test 5: Structural property takes precedence over lexical extension
-- a.G where G(x) = x+1 is structural on receiver, no args → arity mismatch (navigation-only)
-- Even though lexical scope also defines G, structural match takes priority → error, not fallback
def localExt : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.num 100)]

def receiver5 : Algorithm :=
  algPrivate [] [] [("G", incAlg)] [.num 5]

def outer5 : Algorithm :=
  algPrivate [] [] [("G", localExt)] [
    .dotCall (.block receiver5) "G" none
  ]

def test5a : Bool :=
  match runResult (.block outer5) with
  | Except.error _ => true   -- structural G found but arity mismatch (no fallback to lexical)
  | Except.ok _ => false

#guard test5a
-- EXPECTED: Except.error (arityMismatch 1 0)
#eval runResult (.block outer5)

-- Test 5b: Structural property with explicit args → navigation wins over lexical
-- a.G(5) where structural G(x)=x+1 → 6 (not localExt which would give 500)
def test5b : Bool :=
  match runFlat (.block (algPrivate [] [] [("G", localExt)] [
    .dotCall (.block receiver5) "G" (some (alg [] [] [] [.num 5]))
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test5b
-- EXPECTED: Except.ok [6] (structural incAlg wins, not localExt)
#eval runFlat (.block (algPrivate [] [] [("G", localExt)] [
    .dotCall (.block receiver5) "G" (some (alg [] [] [] [.num 5]))
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
    .call (resolve "repeat")
      (alg [] [] [] [
        resolve "Step",
        .dotCall (resolve "Numbers") "count" none,
        .block (alg [] [] [] [.num 0])
      ])
  ]

def test6 : Bool :=
  match runFlat (.block repeatArityRoot) with
  | Except.ok [3] => true
  | _ => false

#guard test6
-- EXPECTED: Except.ok [3] (step applied 3 times: 0→1→2→3)
#eval runFlat (.block repeatArityRoot)

-- Test 7: Numbers.count as Repeat count (comprehensive)
-- Uses 6 output expressions to verify correct count
def numbersAlg7 : Algorithm :=
  alg [] [] [] [.num 3, .num 5, .num 9, .num 1, .num 0, .num 6]

def testAlg7 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg7)] [
    .call (resolve "repeat")
      (alg [] [] [] [
        .block (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),  -- step: increment
        .dotCall (resolve "Numbers") "count" none,                      -- count: 6
        .block (alg [] [] [] [.num 0])                                   -- init: 0
      ])
  ]

def test7 : Bool :=
  match runFlat (.block testAlg7) with
  | Except.ok [6] => true
  | _ => false

#guard test7
-- EXPECTED: Except.ok [6] (step applied 6 times: 0→1→2→3→4→5→6)
#eval runFlat (.block testAlg7)

-- Test 8: 0-param structural property used as Algorithm argument
-- a.X in algorithm position where X has 0 params, returns 42
def xAlg : Algorithm :=
  alg [] [] [] [.num 42]

def receiver8 : Algorithm :=
  algPrivate [] [] [("X", xAlg)] []

-- Use Atoms to force evaluation of the arg algorithm
def test8 : Bool :=
  match runFlat (.call (.resolve "atoms") (alg [] [] [] [.dotCall (.block receiver8) "X" none])) with
  | Except.ok [42] => true
  | _ => false

#guard test8
#eval runFlat (.call (.resolve "atoms") (alg [] [] [] [.dotCall (.block receiver8) "X" none]))

-- Test 9: Structural property with params, no args → arity mismatch (navigation-only)
-- a.Inc where Inc(x) = x + 1, no args → error
def incAlg9 : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

def receiver9 : Algorithm :=
  algPrivate [] [] [("Inc", incAlg9)] [.num 5]

def test9a : Bool :=
  match runResult (.dotCall (.block receiver9) "Inc" none) with
  | Except.error _ => true   -- arity mismatch: Inc expects 1 arg, got 0
  | Except.ok _ => false

#guard test9a
#eval runResult (.dotCall (.block receiver9) "Inc" none)

-- Test 9b: Structural property with explicit args → direct binding
-- a.Inc(5) where Inc(x) = x + 1 → 6
def test9b : Bool :=
  match runFlat (.dotCall (.block receiver9) "Inc" (some (alg [] [] [] [.num 5]))) with
  | Except.ok [6] => true
  | _ => false

#guard test9b
#eval runFlat (.dotCall (.block receiver9) "Inc" (some (alg [] [] [] [.num 5])))

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
  match runFlat (.block (algPrivate [] [] [("R", receiver10)] [
    .call (resolve "repeat")
      (alg [] [] [] [
        .block (alg ["x"] [] [] [.binary .add (.param "x") (.num 10)]),  -- step
        .dotCall (resolve "R") "Count" (some (alg [] [] [] [.num 1])),   -- count: R.Count(1) = 3
        .block (alg [] [] [] [.num 0])                                     -- init
      ])
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard test10
#eval runFlat (.block (algPrivate [] [] [("R", receiver10)] [
  .call (resolve "repeat")
    (alg [] [] [] [
      .block (alg ["x"] [] [] [.binary .add (.param "x") (.num 10)]),
      .dotCall (resolve "R") "Count" (some (alg [] [] [] [.num 1])),
      .block (alg [] [] [] [.num 0])
    ])
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
      (.call (resolve "repeat")
        (alg [] [] [] [
          resolve "Add",
          .dotCall (resolve "Numbers") "count" none,     -- ← no-arg dotCall
          .num 0,
          .num 0
        ]))
      (.num 1)
  ]

def test11 : Bool :=
  match runFlat (.block testAlg11) with
  | Except.ok [24] => true
  | _ => false

#guard test11
-- EXPECTED: Except.ok [24]
#eval runFlat (.block testAlg11)

-- Test 12: dotCall count as Repeat count (simple increment)
-- Same as Test 7 but with dotCall none syntax
-- Numbers has 3 outputs → count = 3, step(x) = x + 1, init = 0 → 3
def numbersAlg12 : Algorithm :=
  alg [] [] [] [.num 10, .num 20, .num 30]

def testAlg12 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg12)] [
    .call (resolve "repeat")
      (alg [] [] [] [
        .block (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),  -- step
        .dotCall (resolve "Numbers") "count" none,                       -- ← no-arg dotCall
        .block (alg [] [] [] [.num 0])                                   -- init
      ])
  ]

def test12 : Bool :=
  match runFlat (.block testAlg12) with
  | Except.ok [3] => true
  | _ => false

#guard test12
-- EXPECTED: Except.ok [3]
#eval runFlat (.block testAlg12)

-- Regression: recursive dot-call arguments bind both value and algorithm views,
-- but builtin argument preparation must use the current parameter value when it
-- exists. Otherwise atoms(values) re-enters list.skip(1) while list is computing.
-- With exact-list builtin results, `atoms` stays list-opaque, so the recursion
-- spread-captures the skip result first (`rest = list.skip(1)...`) and recurses
-- on that canonical sequence — mirroring the C# regression test.
def recursiveDotCallListAlg : Algorithm :=
  alg [] [] [] [
    .call (resolve "atoms") (alg [] [] [] [.param "values"])
  ]

def recursiveDotCallRestAlg : Algorithm :=
  alg [] [] [] [
    .sequenceSpread (.dotCall (resolve "list") "skip" (some (alg [] [] [] [.num 1])))
  ]

def recursiveDotCallReduceCollectionAlg : Algorithm :=
  algPrivate ["values"] [] [
    ("list", recursiveDotCallListAlg),
    ("rest", recursiveDotCallRestAlg)
  ] [
    .call (resolve "if") (alg [] [] [] [
      .binary .le (.dotCall (resolve "list") "count" none) (.num 1),
      resolve "list",
      .dotCall (resolve "rest") "reduceCollection" none
    ])
  ]

def recursiveDotCallRoot : Algorithm :=
  algPrivate [] [] [("reduceCollection", recursiveDotCallReduceCollectionAlg)] [
    .call (resolve "reduceCollection") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4])
    ])
  ]

def test12a : Bool :=
  match runFlat (.block recursiveDotCallRoot) with
  | Except.ok [4] => true
  | _ => false

#guard test12a

-- Test 13: named multi-output receiver no longer exposes arity
def arityRemovedRoot13 : Algorithm :=
  algPrivate [] [] [("Data", alg [] [] [] [.num 1, .num 7])] [
    .dotCall (resolve "Data") "arity" none
  ]

def test13 : Bool :=
  match runResult (.block arityRemovedRoot13) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#guard test13
#eval runResult (.block arityRemovedRoot13)

-- Test 14: inline sequence-value receiver no longer exposes arity
def test14 : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.num 1, .num 7])) "arity" none) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#guard test14
#eval runResult (.dotCall (.block (alg [] [] [] [.num 1, .num 7])) "arity" none)

-- Test 14a: extra sequence-value receiver layer no longer exposes arity
def test14a : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 7])])) "arity" none) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#guard test14a
#eval runResult (.dotCall (.block (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 7])])) "arity" none)

-- Test 14b: count still works for named, inline, and nested sequence-value receivers
def countReceiverRoot14b : Algorithm :=
  algPrivate [] [] [("Data", alg [] [] [] [.num 1, .num 7])] [
    .dotCall (resolve "Data") "count" none,
    .dotCall (.block (alg [] [] [] [.num 1, .num 7])) "count" none,
    .dotCall (.block (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 7])])) "count" none
  ]

def test14b : Bool :=
  match runFlat (.block countReceiverRoot14b) with
  | Except.ok [2, 2, 2] => true
  | _ => false

#guard test14b
#eval runFlat (.block countReceiverRoot14b)

-- Test 14d: old length intrinsic name is no longer recognized
def test14d : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "length" none) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test14d
#eval runResult (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "length" none)

-- Test 15: user-defined higher-order call keeps eager value ABI
-- ApplyTwice(f, x) = f(f(x)); passing Inc as an algorithm argument should work.
def incAlg15 : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

def applyTwiceAlg15 : Algorithm :=
  alg ["f", "x"] [] [] [
    .call (.param "f") (alg [] [] [] [
      .call (.param "f") (alg [] [] [] [.param "x"])
    ])
  ]

def test15 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("ApplyTwice", applyTwiceAlg15)] [
    .call (resolve "ApplyTwice") (alg [] [] [] [resolve "Inc", .num 10])
  ])) with
  | Except.ok [12] => true
  | _ => false

#guard test15
#eval runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("ApplyTwice", applyTwiceAlg15)] [
  .call (resolve "ApplyTwice") (alg [] [] [] [resolve "Inc", .num 10])
]))

-- Test 16: higher-order args preserve flat fixed expression boundaries.
-- UsePair(f, x, y) = f(x) + y; a sequence-value second argument is one argument
-- expression, while a postfix spread of a multi-output value
-- spreads x and y explicitly as separate argument slots.
def usePairAlg16 : Algorithm :=
  alg ["f", "x", "y"] [] [] [
    .binary .add
      (.call (.param "f") (alg [] [] [] [.param "x"]))
      (.param "y")
  ]

def pairArg16 : Algorithm :=
  alg [] [] [] [.num 10, .num 20]

def test16SequenceValueArgDoesNotUnpack : Bool :=
  match runResult (.block (algPrivate [] [] [("Inc", incAlg15), ("UsePair", usePairAlg16)] [
    .call (resolve "UsePair") (alg [] [] [] [resolve "Inc", .block pairArg16])
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard test16SequenceValueArgDoesNotUnpack

-- Source: `UsePair(Inc, Pair...)` where Pair = 10, 20. The postfix spread
-- `Pair...` spreads the pair's two values into the x and y argument slots:
-- Inc(10) + 20 = 31. (Old binary `10...20` no longer exists as source syntax.)
def test16PostfixSpreadSpreadsValues : Bool :=
  match runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("UsePair", usePairAlg16)] [
    .call (resolve "UsePair") (alg [] [] [] [resolve "Inc", sequenceSpread (.block pairArg16)])
  ])) with
  | Except.ok [31] => true
  | _ => false

#guard test16PostfixSpreadSpreadsValues
#eval runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("UsePair", usePairAlg16)] [
  .call (resolve "UsePair") (alg [] [] [] [resolve "Inc", sequenceSpread (.block pairArg16)])
]))

-- Test 16a: ordinary dot-call fallback preserves receiver as one argument boundary.
def dotCallBoundaryAddAlg16a : Algorithm :=
  alg ["a", "b"] [] [] [
    .binary .add (.param "a") (.param "b")
  ]

def dotCallBoundaryPairReceiverAlg16a : Algorithm :=
  alg [] [] [] [.num 3, .num 7]

def dotCallBoundaryNormalCallsStillWork16a : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .call (resolve "F") (alg [] [] [] [.num 3, .num 7])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard dotCallBoundaryNormalCallsStillWork16a

def dotCallBoundarySequenceValueDirectCallDoesNotUnpack16a : Bool :=
  match runResult (.block (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .call (resolve "F") (alg [] [] [] [.block dotCallBoundaryPairReceiverAlg16a])
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard dotCallBoundarySequenceValueDirectCallDoesNotUnpack16a

def dotCallBoundaryScalarReceiverStillWorks16a : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.num 3) "F" (some (alg [] [] [] [.num 7]))
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard dotCallBoundaryScalarReceiverStillWorks16a

def dotCallBoundaryMultiOutputReceiverNoArgsFails16a : Bool :=
  match runResult (.block (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "F" none
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard dotCallBoundaryMultiOutputReceiverNoArgsFails16a

def dotCallBoundaryMultiOutputReceiverEmptyArgsFails16a : Bool :=
  match runResult (.block (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "F" (some (alg [] [] [] []))
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard dotCallBoundaryMultiOutputReceiverEmptyArgsFails16a

def dotCallBoundaryCountedPathDoesNotSpread16a : Bool :=
  match runResult (.block (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall
      (.dotCall (.block dotCallBoundaryPairReceiverAlg16a) "F" none)
      "count"
      none
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard dotCallBoundaryCountedPathDoesNotSpread16a

def dotCallBoundarySequenceValueReceiverAlg16a : Algorithm :=
  alg ["x"] [] [] [.param "x"]

def dotCallBoundaryOneParamGetsSequenceValueReceiver16a : Bool :=
  match runResult (.block (algPrivate [] [] [("G", dotCallBoundarySequenceValueReceiverAlg16a)] [
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "G" none
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
  match runResult (.block (algPrivate [] [] [("H", hAlg)] [
    .dotCall (.num 3) "H" (some (alg [] [] [] [
      .block (alg [] [] [] [.num 4, .num 5])
    ]))
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
  match runFlat (.block (algPrivate [] [] [("H", hAlg)] [
    .dotCall (.num 3) "H" (some (alg [] [] [] [
      sequenceSpread (.block (alg [] [] [] [.num 4, .num 5]))
    ]))
  ])) with
  | Except.ok [12] => true
  | _ => false

#guard dotCallBoundarySequenceSpreadSpreadsExtraArgs16a

def flatFixedIssue101PairAlg : Algorithm :=
  alg [] [] [] [.num 10, .num 20]

def flatFixedIssue101SequenceValuePairAlg : Algorithm :=
  alg [] [] [] [.block flatFixedIssue101PairAlg]

def flatFixedIssue101AddAlg : Algorithm :=
  alg ["x", "y"] [] [] [.binary .add (.param "x") (.param "y")]

def flatFixedIssue101UseAlg : Algorithm :=
  alg ["a", "b", "c"] [] [] [
    .binary .add
      (.binary .add (.param "a") (.param "b"))
      (.param "c")
  ]

def flatFixedIssue101PairDoesNotUnpack : Bool :=
  match runResult (.block (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") (alg [] [] [] [resolve "Pair"])
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101PairDoesNotUnpack

def flatFixedIssue101AtomsDoesNotSpread : Bool :=
  match runResult (.block (algPrivate [] [] [("Pair", flatFixedIssue101SequenceValuePairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") (alg [] [] [] [.dotCall (resolve "Pair") "atoms" none])
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101AtomsDoesNotSpread

def flatFixedIssue101SeparateArgsWork : Bool :=
  match runFlat (.block (algPrivate [] [] [("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") (alg [] [] [] [.num 10, .num 20])
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard flatFixedIssue101SeparateArgsWork

def flatFixedIssue101ExplicitIndexingWorks : Bool :=
  match runFlat (.block (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") (alg [] [] [] [
      .index (resolve "Pair") (.num 0),
      .index (resolve "Pair") (.num 1)
    ])
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard flatFixedIssue101ExplicitIndexingWorks

def flatFixedIssue101MixedPrefixDoesNotUnpack : Bool :=
  match runResult (.block (algPrivate [] [] [("Tail", alg [] [] [] [.num 2, .num 3]), ("Use", flatFixedIssue101UseAlg)] [
    .call (resolve "Use") (alg [] [] [] [.num 1, resolve "Tail"])
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101MixedPrefixDoesNotUnpack

-- Source `Use(1, Tail...)`: a plain leading argument `1` followed by `Tail...`
-- which spreads Tail's items 2, 3. Three call arguments → 1 + 2 + 3 = 6.
def flatFixedIssue101SequenceSpreadSpreadsArgs : Bool :=
  match runFlat (.block (algPrivate [] [] [("Tail", alg [] [] [] [.num 2, .num 3]), ("Use", flatFixedIssue101UseAlg)] [
    .call (resolve "Use") (alg [] [] [] [.num 1, sequenceSpread (resolve "Tail")])
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard flatFixedIssue101SequenceSpreadSpreadsArgs

def variadicParameterForwardingCountItemAlg : Algorithm :=
  algWithParameters [
    { name := "values", kind := .variadic },
    { name := "item", kind := .normal }
  ] [] [] [
    .dotCall
      (.dotCall (.param "values") "filter" (some (alg [] [] [] [
        .block (alg ["value"] [] [] [
          .binary .eq (.param "value") (.param "item")
        ])
      ])))
      "count"
      none
  ]

def variadicParameterForwardingModeFreqsExpr : KatLang.Expr :=
  .dotCall
    (.dotCall (.param "values") "distinct" none)
    "map"
    (some (alg [] [] [] [
      .block (alg ["candidate"] [] [] [
        .call (resolve "CountItem") (alg [] [] [] [.param "values", .param "candidate"])
      ])
    ]))

def variadicParameterForwardingDirectUseAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }] [] [] [
    .call (resolve "CountItem") (alg [] [] [] [.param "values", .num 1])
  ]

def variadicParameterForwardingDirectCall : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("CountItem", variadicParameterForwardingCountItemAlg),
    ("Use", variadicParameterForwardingDirectUseAlg)
  ] [
    .call (resolve "Use") (alg [] [] [] [sequenceItems [.num 1, .num 1, .num 2, .num 4, .num 4]])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard variadicParameterForwardingDirectCall

def variadicParameterForwardingFreqsAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }] [] [] [
    variadicParameterForwardingModeFreqsExpr
  ]

def variadicParameterForwardingCallbackBody : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("CountItem", variadicParameterForwardingCountItemAlg),
    ("Mode", variadicParameterForwardingFreqsAlg)
  ] [
    .call (resolve "Mode") (alg [] [] [] [sequenceItems [.num 1, .num 1, .num 2, .num 4, .num 4]])
  ])) with
  | Except.ok [2, 1, 2] => true
  | _ => false

#guard variadicParameterForwardingCallbackBody

def variadicParameterForwardingModeAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }] [] [
    privateProp "Freqs" (alg [] [] [] [variadicParameterForwardingModeFreqsExpr]),
    privateProp "MaxFreq" (alg [] [] [] [.dotCall (resolve "Freqs") "max" none])
  ] [
    .dotCall
      (.dotCall (.param "values") "distinct" none)
      "filter"
      (some (alg [] [] [] [
        .block (alg ["candidate"] [] [] [
          .binary .eq
            (.call (resolve "CountItem") (alg [] [] [] [.param "values", .param "candidate"]))
            (resolve "MaxFreq")
        ])
      ]))
  ]

def variadicParameterForwardingFullMode : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("CountItem", variadicParameterForwardingCountItemAlg),
    ("Mode", variadicParameterForwardingModeAlg)
  ] [
    .call (resolve "Mode") (alg [] [] [] [sequenceItems [.num 1, .num 1, .num 2, .num 4, .num 4]])
  ])) with
  | Except.ok [1, 4] => true
  | _ => false

#guard variadicParameterForwardingFullMode

def variadicParameterForwardingNonVariadicCollectAlg : Algorithm :=
  alg ["list"] [] [] [.dotCall (.param "list") "count" none]

def variadicParameterForwardingNonVariadicUseAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }] [] [] [
    .call (resolve "Collect") (alg [] [] [] [.param "values"])
  ]

def variadicParameterForwardingNonVariadicCalleeConsumesSequenceValue : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Collect", variadicParameterForwardingNonVariadicCollectAlg),
    ("Use", variadicParameterForwardingNonVariadicUseAlg)
  ] [
    .call (resolve "Use") (alg [] [] [] [sequenceItems [.num 10, .num 20, .num 30]])
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard variadicParameterForwardingNonVariadicCalleeConsumesSequenceValue

def variadicParameterForwardingCountSequenceValueAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "values", kind := .variadic }]
  ] [] [] [.dotCall (.param "values") "count" none]

def variadicParameterForwardingSequenceValueUseAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }] [] [] [
    .call (resolve "CountSequenceValue") (alg [] [] [] [.param "values"])
  ]

def variadicParameterForwardingSequenceValueVariadicPatternPreservesBehavior : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("CountSequenceValue", variadicParameterForwardingCountSequenceValueAlg),
    ("Use", variadicParameterForwardingSequenceValueUseAlg)
  ] [
    .call (resolve "Use") (alg [] [] [] [sequenceItems [.num 10, .num 20, .num 30]])
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard variadicParameterForwardingSequenceValueVariadicPatternPreservesBehavior

def variadicParameterForwardingSequenceValueHistoryArg : KatLang.Expr :=
  .block (alg [] [] [] [.num 1, .num 2, .num 3])

def variadicParameterForwardingFindNextAlg : Algorithm :=
  algWithParameters [
    { name := "history", kind := .variadic },
    { name := "pre1", kind := .normal },
    { name := "pre2", kind := .normal }
  ] [] [] [
    .binary .add
      (.binary .add (.dotCall (.param "history") "count" none) (.param "pre1"))
      (.param "pre2")
  ]

def variadicParameterForwardingSequenceValueStepAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .variadic }],
    .capture { name := "pre2", kind := .normal },
    .capture { name := "pre1", kind := .normal }
  ] [] [] [
    .call (resolve "FindNext") (alg [] [] [] [.param "history", .param "pre1", .param "pre2"])
  ]

def variadicParameterForwardingSequenceValueVariadicCaptureSpreadsCompatibleSlot : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("FindNext", variadicParameterForwardingFindNextAlg),
    ("YSStep", variadicParameterForwardingSequenceValueStepAlg)
  ] [
    .call (resolve "YSStep") (alg [] [] [] [variadicParameterForwardingSequenceValueHistoryArg, .num 2, .num 3])
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard variadicParameterForwardingSequenceValueVariadicCaptureSpreadsCompatibleSlot

def variadicParameterForwardingCountItemsByOtherNameAlg : Algorithm :=
  algWithParameters [
    { name := "items", kind := .variadic },
    { name := "last", kind := .normal }
  ] [] [] [
    .binary .add (.dotCall (.param "items") "count" none) (.param "last")
  ]

def variadicParameterForwardingSequenceValueHistoryUseOtherNameAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .variadic }],
    .capture { name := "last", kind := .normal }
  ] [] [] [
    .call (resolve "CountItems") (alg [] [] [] [.param "history", .param "last"])
  ]

def variadicParameterForwardingSequenceValueVariadicCaptureForwardsByProvenanceNotName : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("CountItems", variadicParameterForwardingCountItemsByOtherNameAlg),
    ("Use", variadicParameterForwardingSequenceValueHistoryUseOtherNameAlg)
  ] [
    .call (resolve "Use") (alg [] [] [] [variadicParameterForwardingSequenceValueHistoryArg, .num 7])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard variadicParameterForwardingSequenceValueVariadicCaptureForwardsByProvenanceNotName

def variadicParameterForwardingSequenceValueHistoryNonVariadicUseAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .variadic }],
    .capture { name := "marker", kind := .normal }
  ] [] [] [
    .call (resolve "Collect") (alg [] [] [] [.param "history"])
  ]

def variadicParameterForwardingSequenceValueCaptureForwardsSequenceValue : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Collect", variadicParameterForwardingNonVariadicCollectAlg),
    ("Use", variadicParameterForwardingSequenceValueHistoryNonVariadicUseAlg)
  ] [
    .call (resolve "Use") (alg [] [] [] [variadicParameterForwardingSequenceValueHistoryArg, .num 99])
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard variadicParameterForwardingSequenceValueCaptureForwardsSequenceValue

def variadicParameterForwardingTakeLastAlg : Algorithm :=
  algWithParameters [
    { name := "first", kind := .variadic },
    { name := "last", kind := .normal }
  ] [] [] [
    .dotCall (.param "first") "count" none
  ]

def variadicParameterForwardingSequenceValueHistoryTakeLastUseAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .variadic }],
    .capture { name := "marker", kind := .normal }
  ] [] [] [
    .call (resolve "TakeLast") (alg [] [] [] [.num 0, .param "history"])
  ]

def variadicParameterForwardingSequenceValueCaptureOnlyExpandsInTargetVariadicSlot : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("TakeLast", variadicParameterForwardingTakeLastAlg),
    ("Use", variadicParameterForwardingSequenceValueHistoryTakeLastUseAlg)
  ] [
    .call (resolve "Use") (alg [] [] [] [variadicParameterForwardingSequenceValueHistoryArg, .num 99])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard variadicParameterForwardingSequenceValueCaptureOnlyExpandsInTargetVariadicSlot

def variadicParameterForwardingSequenceValueLoopStepAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .variadic }],
    .capture { name := "pre2", kind := .normal },
    .capture { name := "pre1", kind := .normal }
  ] [] [] [
    .call (resolve "FindNext") (alg [] [] [] [.param "history", .param "pre1", .param "pre2"]),
    .param "pre1",
    .param "pre2"
  ]

def variadicParameterForwardingLoopStepSequenceValueCaptureSpreadsCompatibleSlot : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("FindNext", variadicParameterForwardingFindNextAlg),
    ("YSStep", variadicParameterForwardingSequenceValueLoopStepAlg)
  ] [
    .index
      (.dotCall (resolve "YSStep") "repeat" (some (alg [] [] [] [
        .num 1, variadicParameterForwardingSequenceValueHistoryArg, .num 2, .num 3
      ])))
      (.num 0)
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard variadicParameterForwardingLoopStepSequenceValueCaptureSpreadsCompatibleSlot

def flatFixedIssue101NestedBlockBoundaryPreserved : Bool :=
  match runResult (.block (algPrivate [] [] [("A", alg [] [] [] [.num 1, .block (alg [] [] [] [.num 2, .num 3])])] [
    resolve "A"
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) => true
  | _ => false

#guard flatFixedIssue101NestedBlockBoundaryPreserved

def flatFixedIssue101ExplicitOuterBodyBlockEquivalent : Bool :=
  match runResult (.block (algPrivate [] [] [("A", alg [] [] [] [.block (alg [] [] [] [.num 1, .block (alg [] [] [] [.num 2, .num 3])])])] [
    resolve "A"
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) => true
  | _ => false

#guard flatFixedIssue101ExplicitOuterBodyBlockEquivalent

-- Internal value shaped like sequence-value source `(1, (2, 3)...)`: a leading `1`
-- combined with a postfix spread of the sequenceValue block (2, 3), whose items 2 and
-- 3 are flattened by the spread.
def flatFixedIssue101SequenceSpreadFlattensNestedBlock : Bool :=
  match runFlat (.block (algPrivate [] [] [("A", alg [] [] [] [.sequenceConstruct (.num 1) (sequenceSpread (.block (alg [] [] [] [.num 2, .num 3])))])] [
    resolve "A"
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard flatFixedIssue101SequenceSpreadFlattensNestedBlock

def flatFixedIssue101DotReceiverDoesNotUnpack : Bool :=
  match runResult (.block (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .dotCall (resolve "Pair") "Add" none
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101DotReceiverDoesNotUnpack

def flatFixedIssue101SequenceSpreadDotReceiverDoesNotUnpack : Bool :=
  match runResult (.block (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .dotCall (sequenceSpreadReceiver (resolve "Pair")) "Add" none
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101SequenceSpreadDotReceiverDoesNotUnpack

def dotCallBoundarySequenceBuiltinsStillExpand16a : Bool :=
  match runFlat (.block (alg [] [] [] [
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "sum" none,
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "count" none,
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "first" none,
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "last" none
  ])) with
  | Except.ok [10, 2, 3, 7] => true
  | _ => false

#guard dotCallBoundarySequenceBuiltinsStillExpand16a

-- Test 17: extra higher-order args are not silently ignored
-- TakeFunc(f) called with two algorithm args should raise arity mismatch.
def takeFuncAlg17 : Algorithm :=
  alg ["f"] [] [] [.num 0]

def test17 : Bool :=
  match runResult (.block (algPrivate [] [] [("Inc", incAlg15), ("TakeFunc", takeFuncAlg17)] [
    .call (resolve "TakeFunc") (alg [] [] [] [resolve "Inc", resolve "Inc"])
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test17
#eval runResult (.block (algPrivate [] [] [("Inc", incAlg15), ("TakeFunc", takeFuncAlg17)] [
  .call (resolve "TakeFunc") (alg [] [] [] [resolve "Inc", resolve "Inc"])
]))

-- Test 18: structural property calls share higher-order binding semantics
-- Receiver.ApplyTwice(Inc, 10) should bind Inc through AlgEnv and return 12.
def receiver18 : Algorithm :=
  algPrivate [] [] [("ApplyTwice", applyTwiceAlg15)] []

def outer18 : Algorithm :=
  algPrivate [] [] [("Inc", incAlg15), ("Receiver", receiver18)] [
    .dotCall (resolve "Receiver") "ApplyTwice" (some (alg [] [] [] [resolve "Inc", .num 10]))
  ]

def test18 : Bool :=
  match runFlat (.block outer18) with
  | Except.ok [12] => true
  | _ => false

#guard test18
#eval runFlat (.block outer18)

-- Test 19: zero-parameter inline blocks passed to higher-order parameters are
-- treated uniformly as value/output structures.
-- Reading the parameter as a value works, but callability is not inferred from
-- having one output, and output count does not change that binding mode.
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
    .call (.param "f") (alg [] [] [] [])
  ]

def test19 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
    .call (resolve "Apply") (alg [] [] [] [.block constSevenAlg19])
  ])) with
  | Except.ok [7] => true
  | _ => false

#guard test19
#eval runFlat (.block (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
  .call (resolve "Apply") (alg [] [] [] [.block constSevenAlg19])
]))

def test19SingleOutputCallRejected : Bool :=
  match runFlat (.block (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
    .call (resolve "Apply") (alg [] [] [] [.block constSevenAlg19])
  ])) with
  | Except.error _ => true
  | _ => false

#guard test19SingleOutputCallRejected
#eval runFlat (.block (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
  .call (resolve "Apply") (alg [] [] [] [.block constSevenAlg19])
]))

def test19MultiOutput : Bool :=
  match runFlat (.block (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
    .call (resolve "Apply") (alg [] [] [] [.block twoValueAlg19])
  ])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard test19MultiOutput
#eval runFlat (.block (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
  .call (resolve "Apply") (alg [] [] [] [.block twoValueAlg19])
]))

def test19MultiOutputCallRejected : Bool :=
  match runFlat (.block (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
    .call (resolve "Apply") (alg [] [] [] [.block twoValueAlg19])
  ])) with
  | Except.error _ => true
  | _ => false

#guard test19MultiOutputCallRejected
#eval runFlat (.block (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
  .call (resolve "Apply") (alg [] [] [] [.block twoValueAlg19])
]))

-- Test 19a: same-name clause-group elaboration classifies a sole plain-binder
-- clause as an ordinary algorithm, not a conditional.
def applyClauseBody19a : Algorithm :=
  alg [] [] [] [
    .call (.param "f") (alg [] [] [] [.param "x"])
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
  match runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("Apply", applyClauseAlg19a)] [
    .call (resolve "Apply") (alg [] [] [] [.num 9, resolve "Inc"])
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
  match runFlat (.block (algPrivate [] [] [("Id", idClauseAlg19a)] [
    .call (resolve "Id") (alg [] [] [] [.num 7])
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
  match runFlat (.block (algPrivate [] [] [("F", fallbackClauseAlg19a)] [
    .call (resolve "F") (alg [] [] [] [.num 2])
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
  match runFlat (.block (algPrivate [] [] [("F", repeatedFlatClauseAlg)] [
    .call (resolve "F") (alg [] [] [] [.num 1, .num 1])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard repeatedFlatClauseEqualArgumentsMatch

def repeatedFlatClauseUnequalArgumentsFail : Bool :=
  match runResult (.block (algPrivate [] [] [("F", repeatedFlatClauseAlg)] [
    .call (resolve "F") (alg [] [] [] [.num 1, .num 2])
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
    runFlat (.block (algPrivate [] [] [("F", repeatedSequenceValueClauseAlg)] [
      .call (resolve "F") (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 1])
      ])
    ]))
  let unequalCall :=
    runResult (.block (algPrivate [] [] [("F", repeatedSequenceValueClauseAlg)] [
      .call (resolve "F") (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2])
      ])
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
    runFlat (.block (algPrivate [] [] [("F", repeatedAcrossNestedClauseAlg)] [
      .call (resolve "F") (alg [] [] [] [
        .num 1,
        .block (alg [] [] [] [.num 1])
      ])
    ]))
  let unequalCall :=
    runResult (.block (algPrivate [] [] [("F", repeatedAcrossNestedClauseAlg)] [
      .call (resolve "F") (alg [] [] [] [
        .num 1,
        .block (alg [] [] [] [.num 2])
      ])
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
  match runFlat (.block (algPrivate [] [] [("F", sequenceValueAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 1, .num 2])
    ])
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
      .call (.param "f") (alg [] [] [] [.num 1])
    ]
  }]
  match runResult (.block (algPrivate [] [] [
    ("Inc", incAlg15),
    ("ApplySame", applySame)
  ] [
    .call (resolve "ApplySame") (alg [] [] [] [resolve "Inc", resolve "Inc"])
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
  match runFlat (.block (algPrivate [] [] [("Equal", repeatedConditionalFallbackAlg)] [
    .call (resolve "Equal") (alg [] [] [] [.num 1, .num 1]),
    .call (resolve "Equal") (alg [] [] [] [.num 1, .num 2])
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
  match runFlat (.block (algPrivate [] [] [("SamePair", samePair)] [
    .call (resolve "SamePair") (alg [] [] [] [
      .block (alg [] [] [] [.num 5, .num 5])
    ]),
    .call (resolve "SamePair") (alg [] [] [] [
      .block (alg [] [] [] [.num 5, .num 6])
    ])
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
  match runFlat (.block (algPrivate [] [] [("Same", repeatedSequenceValueClauseAlg)] [
    .call (resolve "map") (alg [] [] [] [
      sequenceItems [
        .block (alg [] [] [] [.num 1, .num 1]),
        .block (alg [] [] [] [.num 2, .num 2])
      ],
      .resolve "Same"
    ])
  ])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard repeatedSequenceValueBinderCallbackEqualItemsMap

-- An unequal pair item fails the equality constraint with the same badArity
-- shape as the direct-call path.
def repeatedSequenceValueBinderCallbackUnequalItemMapFails : Bool :=
  match runResult (.block (algPrivate [] [] [("Same", repeatedSequenceValueClauseAlg)] [
    .call (resolve "map") (alg [] [] [] [
      sequenceItems [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 3, .num 3])
      ],
      .resolve "Same"
    ])
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
  match runFlat (.block (algPrivate [] [] [("Equal", repeatedSequenceValueConditionalCallbackAlg)] [
    .call (resolve "map") (alg [] [] [] [
      sequenceItems [
        .block (alg [] [] [] [.num 1, .num 1]),
        .block (alg [] [] [] [.num 1, .num 2])
      ],
      .resolve "Equal"
    ])
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
  .block (algPrivate [] [] [
    ("Wrap", callbackParamCollisionWrapAlg),
    ("Pick", callbackParamCollisionPickAlg)
  ] [
    .call (resolve "Wrap") (alg [] [] [] [
      .dotCall
        (.dotCall (sequenceItems [.num 1, .num 2]) "map" (some (alg [] [] [] [resolve "Pick"])))
        "sum" none
    ])
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
        .call (.param "f") (alg [] [] [] [.param "x"])
      ] ⟩
  ]

def test19b : Bool :=
  match runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("Apply", applyCondAlg19b)] [
    .call (resolve "Apply") (alg [] [] [] [.num 9, resolve "Inc"])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test19b
#eval runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("Apply", applyCondAlg19b)] [
  .call (resolve "Apply") (alg [] [] [] [.num 9, resolve "Inc"])
]))

-- Test 19c: structural property call preserves higher-order args for the same subset
def receiver19c : Algorithm :=
  algPrivate [] [] [("Apply", applyCondAlg19b)] []

def test19c : Bool :=
  match runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("Receiver", receiver19c)] [
    .dotCall (resolve "Receiver") "Apply" (some (alg [] [] [] [.num 9, resolve "Inc"]))
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test19c
#eval runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("Receiver", receiver19c)] [
  .dotCall (resolve "Receiver") "Apply" (some (alg [] [] [] [.num 9, resolve "Inc"]))
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
      (.call (.resolve "filter") (alg [] [] [] [.param "values", .param "predicate"]))
      "count"
      none
  ]

def test19d : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("OccurrenceCount", occurrenceCountAlg19d)
  ] [
    .call (.resolve "OccurrenceCount") (alg [] [] [] [
      sequenceItems [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 1, .num 3])
      ],
      .block evenPredicateAlg19d
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test19d
#eval runFlat (.block (algPrivate [] [] [
  ("OccurrenceCount", occurrenceCountAlg19d)
] [
  .call (.resolve "OccurrenceCount") (alg [] [] [] [
    sequenceItems [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 1, .num 3])
    ],
    .block evenPredicateAlg19d
  ])
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
      (.call (.resolve "filter") (alg [] [] [] [
        sequenceItems [
          .block (alg [] [] [] [.num 1, .num 10]),
          .block (alg [] [] [] [.num 2, .num 20]),
          .block (alg [] [] [] [.num 2, .num 30])
        ],
        .block (alg ["item"] [] [] [
          .binary .eq
            (.index (.param "item") (.num 1))
            (.index (.param "target") (.num 1))
        ])
      ]))
      "count"
      none
  ]

def test19e : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("OccurrenceCount", occurrenceCountAlg19e)
  ] [
    .call (.resolve "OccurrenceCount") (alg [] [] [] [
      .block (alg [] [] [] [.num 2, .num 20])
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test19e
#eval runFlat (.block (algPrivate [] [] [
  ("OccurrenceCount", occurrenceCountAlg19e)
] [
  .call (.resolve "OccurrenceCount") (alg [] [] [] [
    .block (alg [] [] [] [.num 2, .num 20])
  ])
]))

-- if builtin tests
-- if(cond, whenTrue, whenFalse): the only supported form.
--------------------------------------------------------------------------------

-- Test 20: 3-arg if true → produce then-branch value
-- if(1, 5, 6) → [5]
def test20 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 1, .num 5, .num 6])) with
  | Except.ok [5] => true
  | _ => false

#guard test20
#eval runFlat (.call (resolve "if") (alg [] [] [] [.num 1, .num 5, .num 6]))

-- Test 21: 3-arg if false → produce else-branch value
-- if(0, 5, 6) → [6]
def test21 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 0, .num 5, .num 6])) with
  | Except.ok [6] => true
  | _ => false

#guard test21
#eval runFlat (.call (resolve "if") (alg [] [] [] [.num 0, .num 5, .num 6]))

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
  match runFlat (.block (algPrivate [] [] [("K", kAlg)] [
    .call (resolve "K") (alg [] [] [] [.num 10, .num 20])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test34
#eval runFlat (.block (algPrivate [] [] [("K", kAlg)] [
  .call (resolve "K") (alg [] [] [] [.num 10, .num 20])
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
  match runFlat (.block (algPrivate [] [] [("Else", elseAlg)] [
    .call (resolve "Else") (alg [] [] [] [.num 1, .block (alg [] [] [] [.num 2, .num 3])])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test35a

-- Else(0, (2, 3)) → second branch matches → b = 3
def test35b : Bool :=
  match runFlat (.block (algPrivate [] [] [("Else", elseAlg)] [
    .call (resolve "Else") (alg [] [] [] [.num 0, .block (alg [] [] [] [.num 2, .num 3])])
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
  match runResult (.block (algPrivate [] [] [("Sign", signAlg)] [
    .call (resolve "Sign") (alg [] [] [] [.num 0])
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
  match runFlat (.block (algPrivate [] [] [("F", firstMatchAlg)] [
    .call (resolve "F") (alg [] [] [] [.num 1])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test37

-- Test 22: 2-arg if is rejected
def test22 : Bool :=
  match runResult (.call (resolve "if") (alg [] [] [] [.num 1, .num 5])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test22
#eval runResult (.call (resolve "if") (alg [] [] [] [.num 1, .num 5]))

-- Test 23: 2-arg if in addition is rejected
def test23 : Bool :=
  match runResult (.binary .add (.num 10) (.call (resolve "if") (alg [] [] [] [.num 1, .num 5]))) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test23
#eval runResult (.binary .add (.num 10) (.call (resolve "if") (alg [] [] [] [.num 1, .num 5])))

-- Test 24: 2-arg if in multiplication is rejected
def test24 : Bool :=
  match runResult (.binary .mul (.num 10) (.call (resolve "if") (alg [] [] [] [
    .binary .lt (.num 7) (.num 6),
    .num 1
  ]))) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test24
#eval runResult (.binary .mul (.num 10) (.call (resolve "if") (alg [] [] [] [
  .binary .lt (.num 7) (.num 6),
  .num 1
])))

-- Test 25: Spread of an internal constructed sequence `(1, if(0, 2, 9), 3)...` with a
-- 3-arg if that selects the else branch → [1, 9, 3]
def test25 : Bool :=
  match runFlat (sequenceSpread (.sequenceConstruct (.sequenceConstruct (.num 1) (.call (resolve "if") (alg [] [] [] [.num 0, .num 2, .num 9]))) (.num 3))) with
  | Except.ok [1, 9, 3] => true
  | _ => false

#guard test25
#eval runFlat (sequenceSpread (.sequenceConstruct (.sequenceConstruct (.num 1) (.call (resolve "if") (alg [] [] [] [.num 0, .num 2, .num 9]))) (.num 3)))

-- Internal sequence `(1, 2, 3, 4)...`: postfix spread over the constructed sequence value.
def sequenceSpread1234 : KatLang.Expr :=
  sequenceSpread (.sequenceConstruct (.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3)) (.num 4))

def test25a : Bool :=
  let sequence1234 := .sequenceConstruct (.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3)) (.num 4)
  match runFlat (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [sequence1234]),
    .call (resolve "count") (alg [] [] [] [sequence1234]),
    .call (resolve "first") (alg [] [] [] [sequence1234]),
    .call (resolve "last") (alg [] [] [] [sequence1234])
  ])) with
  | Except.ok [10, 4, 1, 4] => true
  | _ => false

#guard test25a

def test25b : Bool :=
  -- Internal constructed-sequence variants of `count(((1, 2)..., 3))` and
  -- `count((1, (2, 3)...))`: a flattening spread contributes inside the one
  -- sequence-valued argument.
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [
      sequenceItems [sequenceSpread (.block (alg [] [] [] [.num 1, .num 2])), .num 3]
    ]),
    .call (resolve "count") (alg [] [] [] [
      sequenceItems [.num 1, sequenceSpread (.block (alg [] [] [] [.num 2, .num 3]))]
    ])
  ])) with
  | Except.ok [3, 3] => true
  | _ => false

#guard test25b

def test25bNestedSequenceValues : Bool :=
  let nestedLeft := .sequenceConstruct (sequenceSpread (.block (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2])]))) (.num 3)
  let nestedMiddle := .sequenceConstruct (sequenceSpread (.block (alg [] [] [] [.num 1, .block (alg [] [] [] [.num 2, .num 3])]))) (.num 4)
  match runResult (.block (alg [] [] [] [nestedLeft, nestedMiddle])) with
  | Except.ok value =>
      value == Result.sequenceValue [
        Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3],
        Result.sequenceValue [Result.atom 1, Result.sequenceValue [Result.atom 2, Result.atom 3], Result.atom 4]
      ]
  | _ => false

#guard test25bNestedSequenceValues

def sequenceSpreadNamedSequenceValueOperandPreservesBoundary : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2])])
  ] [
    .sequenceConstruct (sequenceSpread (resolve "A")) (.num 3)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]) => true
  | _ => false

#guard sequenceSpreadNamedSequenceValueOperandPreservesBoundary

def test25bCommaSimilarity : Bool :=
  match runFlat (.block (algPrivate [] [] [
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
  -- Internal sequence `(P..., 3, 4, 5)` where P = 1, 2 is ONE collection argument,
  -- opened by the post-binding one-level collection view; sum 15.
  let pThenMore := sequenceItems [sequenceSpread (resolve "P"), .num 3, .num 4, .num 5]
  match runFlat (.block (algPrivate [] [] [
    ("P", alg [] [] [] [.num 1, .num 2]),
    ("X", alg [] [] [] [.call (resolve "sum") (alg [] [] [] [pThenMore])])
  ] [
    resolve "X"
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test25c

def test25dResultShape : Bool :=
  match runResult (.block (algPrivate [] [] [
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
  match runFlat (.block (algPrivate [] [] [
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
  match runFlat (.block (algPrivate [] [] [
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
  match runFlat (.block (algPrivate [] [] [
    ("A", a),
    ("B", b),
    ("C", alg [] [] [] [.sequenceConstruct (sequenceSpread (resolve "A")) (sequenceSpread (resolve "B"))])
  ] [
    .dotCall (resolve "C") "X" none
  ])) with
  | Except.error err => innermostIsUnknownName "X" err
  | _ => false

#guard test25g

-- Postfix spread of a no-output operand fails with the spread
-- missing-output diagnostic: source `bad...` is `sequenceSpread bad`, whose
-- single operand produces no output.
def test25h : Bool :=
  let bad := .block (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])
  match runFlat (sequenceSpread bad) with
  | Except.error err => innermostIsMissingOutput err
  | _ => false

#guard test25h

-- A spread is not a valid open target. Source `open A...` is the
-- postfix spread `sequenceSpread (resolve "A")`, rendered `A...`.
def test25j : Bool :=
  let a := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] []
  let b := alg [] [] [publicProp "Y" (alg [] [] [] [.num 2])] []
  match runFlat (.block (algPrivate [] [sequenceSpread (resolve "A")] [
    ("A", a),
    ("B", b)
  ] [
    .binary .add (resolve "X") (resolve "Y")
  ])) with
  | Except.error err => innermostIsBadOpenForm "spread: A..." err
  | _ => false

#guard test25j

-- Test 26: Nested 3-arg if uses the selected inner branch
-- if(1, if(1, 5, 6), 9) → [5]
def test26 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [
    .num 1,
    .call (resolve "if") (alg [] [] [] [.num 1, .num 5, .num 6]),
    .num 9
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test26

-- Test 27: Nested 3-arg if uses the outer else branch
-- if(0, if(1, 5, 6), 9) → [9]
def test27 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [
    .num 0,
    .call (resolve "if") (alg [] [] [] [.num 1, .num 5, .num 6]),
    .num 9
  ])) with
  | Except.ok [9] => true
  | _ => false

#guard test27

-- Test 28: 3-arg if still works — if(1, 10, 20) → [10]
def test28 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 1, .num 10, .num 20])) with
  | Except.ok [10] => true
  | _ => false

#guard test28

-- Test 29: 3-arg if false → if(0, 10, 20) → [20]
def test29 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 0, .num 10, .num 20])) with
  | Except.ok [20] => true
  | _ => false

#guard test29

-- Test 30: 3-arg if with non-zero condition → true
-- if(42, 7, 9) → [7]
def test30 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 42, .num 7, .num 9])) with
  | Except.ok [7] => true
  | _ => false

#guard test30

-- Test 31: 3-arg if with negative condition → true
-- if(-1, 7, 9) → [7]
def test31 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num (-1), .num 7, .num 9])) with
  | Except.ok [7] => true
  | _ => false

#guard test31

--------------------------------------------------------------------------------
-- string intrinsic tests
--------------------------------------------------------------------------------

-- Test 52: string intrinsic on positive integer via algorithm
-- (block [123]).string → Result.str "123"
def test52 : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.num 123])) "string" none) with
  | Except.ok (Result.str "123") => true
  | _ => false

#guard test52
#eval runResult (.dotCall (.block (alg [] [] [] [.num 123])) "string" none)

-- Test 53: string intrinsic on zero
-- (block [0]).string → Result.str "0"
def test53 : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.num 0])) "string" none) with
  | Except.ok (Result.str "0") => true
  | _ => false

#guard test53

-- Test 54: string intrinsic on negative integer
-- (block [-5]).string → Result.str "-5"
def test54 : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.num (-5)])) "string" none) with
  | Except.ok (Result.str "-5") => true
  | _ => false

#guard test54

-- Test 55: string intrinsic on a named property
-- A = 123; A.string → Result.str "123"
def test55 : Bool :=
  let innerAlg := algPrivate [] [] [("A", alg [] [] [] [.num 123])] [
    .dotCall (.resolve "A") "string" none
  ]
  match runResult (.block innerAlg) with
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
  match runResult (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "string" none) with
  | Except.error _ => true
  | _ => false

#guard test58

--------------------------------------------------------------------------------
-- range builtin tests
--------------------------------------------------------------------------------

-- Test 59: ascending inclusive range
def test59 : Bool :=
  match runFlat (.call (resolve "range") (alg [] [] [] [.num 1, .num 10])) with
  | Except.ok [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] => true
  | _ => false

#guard test59

-- Test 60: descending inclusive range
def test60 : Bool :=
  match runFlat (.call (resolve "range") (alg [] [] [] [.num 10, .num 1])) with
  | Except.ok [10, 9, 8, 7, 6, 5, 4, 3, 2, 1] => true
  | _ => false

#guard test60

-- Test 61: equal bounds produce a singleton
def test61 : Bool :=
  match runFlat (.call (resolve "range") (alg [] [] [] [.num 5, .num 5])) with
  | Except.ok [5] => true
  | _ => false

#guard test61

-- Test 62: negative to positive bounds remain inclusive and ordered
def test62 : Bool :=
  match runFlat (.call (resolve "range") (alg [] [] [] [.num (-2), .num 2])) with
  | Except.ok [-2, -1, 0, 1, 2] => true
  | _ => false

#guard test62

-- Test 32: Unary / binary composition with 2-arg if is rejected
def test32 : Bool :=
  match runResult (.binary .add (.num 10) (.unary .minus (.call (resolve "if") (alg [] [] [] [.num 0, .num 5])))) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test32

-- Test 33: if arity mismatch — 1 arg → error
def test33 : Bool :=
  match runResult (.call (resolve "if") (alg [] [] [] [.num 1])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test33

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
    (.block (alg [] [] [] [.num 3, .num 4, .num 5, .num 6]))
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
    (.block (alg [] [] [] [.num 3, .num 4, .num 5, .num 6]))) with
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

-- Helper: a multi-output block materializes as one sequence value in operand
-- position, e.g. `seqVal [1, 2]` stands in for `(1, 2)`.
def seqVal (xs : List Int) : KatLang.Expr :=
  .block (alg [] [] [] (xs.map (fun n => KatLang.Expr.num n)))

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
  let left  := .block (alg [] [] [] [.num 1, seqVal [2, 3]])
  let right := .block (alg [] [] [] [.num 1, seqVal [2, 3]])
  match runFlat (.binary .eq left right) with
  | Except.ok [1] => true
  | _ => false

#guard nestedSequenceValueEqualityEqual

-- Test 45g: nested sequence values compare recursively (unequal inner element).
def nestedSequenceValueEqualityDifferentInner : Bool :=
  let left  := .block (alg [] [] [] [.num 1, seqVal [2, 3]])
  let right := .block (alg [] [] [] [.num 1, seqVal [2, 4]])
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
  let left  := .block (alg [] [] [] [.num 1, seqVal [2, 3]])
  let right := .block (alg [] [] [] [seqVal [1, 2], .num 3])
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
  match runFlat (.block (algPrivate [] [] [
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
  match runFlat (.block (algPrivate [] [] [("Price", priceAlg)] [
    .call (resolve "Price") (alg [] [] [] [.stringLiteral "apples"])
  ])) with
  | Except.ok [80] => true
  | _ => false

#guard test46

-- Test 47: Conditional algorithm with string pattern — no match
def test47 : Bool :=
  match runResult (.block (algPrivate [] [] [("Price", priceAlg)] [
    .call (resolve "Price") (alg [] [] [] [.stringLiteral "bananas"])
  ])) with
  | Except.error _ => true   -- noMatchingBranch
  | Except.ok _    => false

#guard test47

-- Test 48: String passed as algorithm argument
-- Echo = x, Echo('hello') → 'hello'
def echoAlg : Algorithm := alg ["x"] [] [] [.param "x"]
def test48 : Bool :=
  match runResult (.block (algPrivate [] [] [("Echo", echoAlg)] [
    .call (resolve "Echo") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.ok (.str "hello") => true
  | _ => false

#guard test48

-- Test 49: String stored in property and returned
-- Name = 'KatLang', output = Name
def test49 : Bool :=
  let nameAlg := alg [] [] [] [.stringLiteral "KatLang"]
  match runResult (.block (algPrivate [] [] [("Name", nameAlg)] [resolve "Name"])) with
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
  match runResult (.block (alg ["x"] [] [] [.param "x"])) with
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
  alg ["x"] [] [] [.block (alg [] [] [] [.num 1, .num 0])]

-- `take(x, 0)` returns the exact list `[]`: one value, but a list has no truth
-- value, so a predicate built from a collection builtin is rejected.
def listTruthAlg71 : Algorithm :=
  alg ["x"] [] [] [
    .call (resolve "take") (alg [] [] [] [
      .param "x",
      .num 0
    ])
  ]

-- Test 63: plain-call filter iterates emitted range items
def test63 : Bool :=
  match runFlat (.block (algPrivate [] [] [("KeepTenSequenceValue", keepTenSequenceValueAlg66b)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 10]),
      .resolve "KeepTenSequenceValue"
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test63

-- Test 64: descending ranges iterate emitted items in plain-call filter
def test64 : Bool :=
  match runFlat (.block (algPrivate [] [] [("KeepTenSequenceValue", keepTenSequenceValueAlg66b)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 10, .num 1]),
      .resolve "KeepTenSequenceValue"
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test64

-- Test 65: a sequence-value-only predicate does not match scalar emitted range items
def test65 : Bool :=
  match runFlat (.block (algPrivate [] [] [("KeepFourSequenceValue", keepFourSequenceValueAlg66c)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "KeepFourSequenceValue"
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test65

-- Test 66: a sequence-value-only rejection predicate keeps scalar emitted range items
def test66 : Bool :=
  match runFlat (.block (algPrivate [] [] [("RejectFourSequenceValue", rejectFourSequenceValueAlg66d)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "RejectFourSequenceValue"
    ])
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
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg63)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 3, .num 6]),
      .num 8,
      .resolve "IsEven"
    ])
  ])) with
  | Except.error err => innermostIsArityMismatch 2 3 err
  | Except.ok _ => false

#guard sequenceBoundaryLawFilterCommaRangeSourcePreservesBoundary

-- A single grouped argument `(range(3, 6)..., 8)` is ONE collection value; the post-binding
-- one-level collection view opens it, so filter's collection is [3, 4, 5, 6, 8] and keeps
-- the even items [4, 6, 8].
def sequenceBoundaryLawFilterSequenceSpreadRangeSourceExpands : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg63)] [
    .call (resolve "filter") (alg [] [] [] [
      sequenceItems [sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 3, .num 6])), .num 8],
      .resolve "IsEven"
    ])
  ])) with
  | Except.ok [4, 6, 8] => true
  | _ => false

#guard sequenceBoundaryLawFilterSequenceSpreadRangeSourceExpands

-- A named multi-output source `Data` is ONE collection argument; the post-binding one-level
-- collection view opens it, so filter's collection is [3, 4, 5, 6].
def sequenceBoundaryLawFilterNamedSingleSourcePreservesBoundary : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .call (resolve "filter") (alg [] [] [] [
      .resolve "Data",
      .resolve "IsEven"
    ])
  ])) with
  | Except.ok [4, 6] => true
  | _ => false

#guard sequenceBoundaryLawFilterNamedSingleSourcePreservesBoundary

-- A dot-call receiver `Data` binds the fixed collection parameter; the post-binding
-- one-level collection view opens it, so filter iterates [3, 4, 5, 6].
def sequenceBoundaryLawFilterDotReceiverExpands : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .dotCall (.resolve "Data") "filter" (some (alg [] [] [] [.resolve "IsEven"]))
  ])) with
  | Except.ok [4, 6] => true
  | _ => false

#guard sequenceBoundaryLawFilterDotReceiverExpands

-- Named multi-output plus a comma-separated scalar are two sibling arguments ((3, 4, 5, 6)
-- and 8), so `filter(collection, predicate)` receives three arguments and reports an
-- ordinary arity error (sibling preservation, never silent flattening).
def sequenceBoundaryLawFilterCommaNamedSourcePreservesBoundary : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .call (resolve "filter") (alg [] [] [] [
      .resolve "Data",
      .num 8,
      .resolve "IsEven"
    ])
  ])) with
  | Except.error err => innermostIsArityMismatch 2 3 err
  | Except.ok _ => false

#guard sequenceBoundaryLawFilterCommaNamedSourcePreservesBoundary

-- A single grouped argument `(Data..., 8)` is ONE collection value opened by the
-- post-binding one-level collection view, so filter's collection is [3, 4, 5, 6, 8]
-- and keeps the even items [4, 6, 8].
def sequenceBoundaryLawFilterSequenceSpreadNamedSourceExpands : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .call (resolve "filter") (alg [] [] [] [
      sequenceItems [sequenceSpread (.resolve "Data"), .num 8],
      .resolve "IsEven"
    ])
  ])) with
  | Except.ok [4, 6, 8] => true
  | _ => false

#guard sequenceBoundaryLawFilterSequenceSpreadNamedSourceExpands

-- Test 67: filtering an already-empty sequence-value boundary stays empty
def test67 : Bool :=
  match runFlat (.block (algPrivate [] [] [("KeepFourSequenceValue", keepFourSequenceValueAlg66c), ("RejectFourSequenceValue", rejectFourSequenceValueAlg66d)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "RejectFourSequenceValue"
      ]),
      .resolve "KeepFourSequenceValue"
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test67

-- Test 68: kept sequence values are preserved whole and in order as exact list elements
def test68 : Bool :=
  match runResult (.block (algPrivate [] [] [("KeepPair", keepPairAlg67)] [
    .call (resolve "filter") (alg [] [] [] [sequenceItems [
      .block (alg [] [] [] [.num 1, .num 10]),
      .block (alg [] [] [] [.num 2, .num 20]),
      .block (alg [] [] [] [.num 3, .num 30]),
      .block (alg [] [] [] [.num 4, .num 40])],
      .resolve "KeepPair"
    ])
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 2, .atom 20],
      .sequenceValue [.atom 4, .atom 40]
    ]) => true
  | _ => false

#guard test68

-- Test 69: multi-output predicate starting with 0 is rejected
def test69 : Bool :=
  match runResult (.block (algPrivate [] [] [("Bad", badMultiFalseAlg68)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "Bad"
    ])
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test69

-- Test 70: multi-output predicate starting with nonzero is also rejected
def test70 : Bool :=
  match runResult (.block (algPrivate [] [] [("Bad", badMultiTrueAlg69)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "Bad"
    ])
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test70

-- Test 71: sequenceValue predicate result is rejected
def test71 : Bool :=
  match runResult (.block (algPrivate [] [] [("Bad", badSequenceValueAlg70)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "Bad"
    ])
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test71

-- Test 72: exact-list predicate result is rejected (a collection builtin used
-- as a filter predicate returns a list, never an atomic numeric value)
def test72 : Bool :=
  match runResult (.block (algPrivate [] [] [("Bad", listTruthAlg71)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "Bad"
    ])
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test72

-- Test 73: string predicate result is rejected
def test73 : Bool :=
  match runResult (.block (algPrivate [] [] [("BadTruth", badTruthAlg66)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "BadTruth"
    ])
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test73

-- Test 74: builtin arity mismatch still follows normal conventions
def test74 : Bool :=
  match runResult (.call (resolve "filter") (alg [] [] [] [])) with
  | Except.error _ => true
  | _ => false

#guard test74

-- Test 75: filter predicate arity mismatch explains the implicit item argument
def test75 : Bool :=
  match runResult (.dotCall
    (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
    "filter"
    (some (alg [] [] [] [.num 1]))) with
  | Except.error err =>
      hasContext "while evaluating filter predicate for item 0: 1 (filter passes each iterated collection item as collected; sequence parameters use values... top-level binding and nested sequence values stay intact)" err &&
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
    .block (alg [] [] [] [
      .binary .add (.dotCall (.param "x") "count" none) (.index (.param "acc") (.num 0)),
      .binary .add (.index (.param "acc") (.num 1)) (.num 1)
    ])
  ]

def reduceEmptyBoundaryAlg80a : Algorithm :=
  alg ["x", "acc"] [] [] [
    .binary .add
      (.binary .add (.param "acc") (.num 100))
      (.dotCall (.param "x") "count" none)
  ]

def reduceEmptyBoundarySequenceValueAccAlg80b : Algorithm :=
  alg ["x", "acc"] [] [] [
    .block (alg [] [] [] [
      .binary .add
        (.binary .add (.index (.param "acc") (.num 0)) (.num 100))
        (.dotCall (.param "x") "count" none),
      .binary .add (.index (.param "acc") (.num 1)) (.num 1)
    ])
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
      .call (resolve "atoms") (alg [] [] [] [.param "tt"])
    ])
  ] [
    .block (alg [] [] [] [
      .dotCall (resolve "T") "first" none,
      .binary .add
        (.index (resolve "T") (.num 1))
        (.call (resolve "if") (alg [] [] [] [
          .binary .eq (.param "element") (.dotCall (resolve "T") "first" none),
          .num 1,
          .num 0
        ]))
    ])
  ]

-- Exact AoC-style regression: Right is a named multi-output property bound as
-- reduce's collection argument, so the collection view must iterate its items.
def sequenceBoundaryLawAocNamedReduceSource : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Left", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]),
    ("Right", alg [] [] [] [.num 4, .num 3, .num 5, .num 3, .num 9, .num 3]),
    ("CountMatchStep", sequenceBoundaryLawAocCountMatchStepAlg),
    ("MatchCount", alg ["value"] [] [] [
      .index
        (.call (resolve "reduce") (alg [] [] [] [
          resolve "Right",
          resolve "CountMatchStep",
          .block (alg [] [] [] [.param "value", .num 0])
        ]))
        (.num 1)
    ]),
    ("SimilarityAt", alg ["value"] [] [] [
      .binary .mul
        (.param "value")
        (.call (resolve "MatchCount") (alg [] [] [] [.param "value"]))
    ]),
    ("Part2", alg [] [] [] [
      .dotCall
        (.dotCall (resolve "Left") "map" (some (alg [] [] [] [resolve "SimilarityAt"])))
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
  match runFlat (.block (algPrivate [] [] [("Add", addAlg76)] [
    .dotCall
      (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
      "reduce"
      (some (alg [] [] [] [.resolve "Add", .num 0]))
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test76

-- Test 77: plain-call reduce iterates emitted range items
def test77 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Mul", mulAlg77)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "Mul",
      .num 1
    ])
  ])) with
  | Except.ok [11111] => true
  | _ => false

#guard test77

-- Test 77a: plain-call reduce can still observe sequence-value range content explicitly
def test77a : Bool :=
  match runFlat (.block (algPrivate [] [] [("AddItemCount", addItemCountAlg80c)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 3, .num 6]),
      .resolve "AddItemCount",
      .num 0
    ])
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test77a

-- Test 78: sequence-value-only reduce branches do not match scalar emitted range items
def test78 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Digits", digitsAlg78)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "Digits",
      .num 0
    ])
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test78

-- Test 79: reducing an empty plain-call collection returns the initial accumulator
def test79 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a), ("MarkEmptyBoundary", reduceEmptyBoundaryAlg80a)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ]),
      .resolve "MarkEmptyBoundary",
      .num 0
    ])
  ])) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard test79

-- Test 80: sequence-value accumulators also stay unchanged when reducing an empty collection
def test80 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a), ("MarkEmptyBoundary", reduceEmptyBoundarySequenceValueAccAlg80b)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ]),
      .resolve "MarkEmptyBoundary",
      .block (alg [] [] [] [.num 7, .num 9])
    ])
  ])) with
  | Except.ok (.sequenceValue [.atom 7, .atom 9]) => true
  | _ => false

#guard test80

-- Test 81: sequenceValue collection elements are passed to the step as whole values
def test81 : Bool :=
  match runFlat (.block (algPrivate [] [] [("TakeValue", reduceSequenceValueItemAlg79)] [
    .call (resolve "reduce") (alg [] [] [] [sequenceItems [
      .block (alg [] [] [] [.num 1, .num 10]),
      .block (alg [] [] [] [.num 2, .num 20]),
      .block (alg [] [] [] [.num 3, .num 30])],
      .resolve "TakeValue",
      .num 0
    ])
  ])) with
  | Except.ok [60] => true
  | _ => false

#guard test81

-- Test 82: sequence-value accumulators keep their shape while emitted range items are reduced
def test82 : Bool :=
  match runResult (.block (algPrivate [] [] [("Stats", reduceStatsAlg80)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "Stats",
      .block (alg [] [] [] [.num 0, .num 0])
    ])
  ])) with
  | Except.ok (.sequenceValue [.atom 4, .atom 4]) => true
  | _ => false

#guard test82

-- Test 83: reduce step must not return an empty result
def test83 : Bool :=
  match runResult (.block (algPrivate [] [] [("Bad", reduceEmptyAlg81)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "Bad",
      .num 0
    ])
  ])) with
  | Except.error err => hasContext "reduce step must return a single accumulator value" err && innermostIsBadArity err
  | _ => false

#guard test83

-- Test 84: reduce step must not return multiple top-level outputs
def test84 : Bool :=
  match runResult (.block (algPrivate [] [] [("Bad", reduceMultiAlg82)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "Bad",
      .num 0
    ])
  ])) with
  | Except.error err => hasContext "reduce step must return a single accumulator value" err && innermostIsBadArity err
  | _ => false

#guard test84

-- Test 84a: reduce is an ordinary fixed-arity callable — reduce(1) supplies one
-- argument where `reduce(collection, reducer, initial)` expects three.
def test84a : Bool :=
  match runResult (.block (algPrivate [] [] [("Add", addAlg76)] [
    .call (resolve "reduce") (alg [] [] [] [
      .num 1
    ])
  ])) with
  | Except.error err => innermostIsArityMismatch 3 1 err
  | _ => false

#guard test84a

-- Test 84b: reduce((1, 2, 3), Add) supplies two of the three fixed arguments —
-- an ordinary arity error, with no suffix-binding reinterpretation of the
-- argument list.
def test84b : Bool :=
  match runResult (.block (algPrivate [] [] [("Add", addAlg76)] [
    .call (resolve "reduce") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, .num 3],
      .resolve "Add"
    ])
  ])) with
  | Except.error err => innermostIsArityMismatch 3 2 err
  | _ => false

#guard test84b

-- Test 84c: the dotted missing-initial hint is reserved for a visibly
-- parameterized reducer. An ordinary value in the sole control slot follows
-- the fixed signature and reports the ordinary three-versus-two arity error.
def test84c : Bool :=
  match runResult (.block (algPrivate [] [] [("Values", alg [] [] [] [
    sequenceItems [.num 1, .num 2, .num 3]
  ])] [
    .dotCall (resolve "Values") "reduce" (some (alg [] [] [] [.num 0]))
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
        .block (alg [] [] [] [
          .param "first",
          .param "last"
        ])
      ] ⟩,
    ⟨ .bind "x",
      alg [] [] [] [
        .block (alg [] [] [] [.num 0, .num 0])
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
  match runFlat (.block (algPrivate [] [] [("Double", doubleAlg85)] [
    .dotCall
      (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
      "map"
      (some (alg [] [] [] [.resolve "Double"]))
  ])) with
  | Except.ok [2, 4, 6, 8, 10] => true
  | _ => false

#guard test85

def factorialMapAlg85a : Algorithm :=
  alg ["n"] [] [] [
    .call (resolve "if") (alg [] [] [] [
      .binary .eq (.param "n") (.num 0),
      .num 1,
      .binary .mul
        (.call (resolve "Factorial") (alg [] [] [] [
          .binary .sub (.param "n") (.num 1)
        ]))
        (.param "n")
    ])
  ]

def test85a : Bool :=
  match runFlat (.block (algPrivate [] [] [("Factorial", factorialMapAlg85a)] [
    .dotCall
      (.block (alg [] [] [] [.num 0, .num 1, .num 2, .num 3, .num 4]))
      "map"
      (some (alg [] [] [] [.resolve "Factorial"]))
  ])) with
  | Except.ok [1, 1, 2, 6, 24] => true
  | _ => false

#guard test85a

-- Test 86: plain-call map iterates emitted range items
def test86 : Bool :=
  match runFlat (.block (algPrivate [] [] [("TakeMiddle", takeMiddleSequenceValueAlg85a)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5]),
      .resolve "TakeMiddle"
    ])
  ])) with
  | Except.ok [0, 0, 0, 0, 0] => true
  | _ => false

#guard test86

-- Test 86a: plain-call map applies scalar transforms to emitted range items
def test86a : Bool :=
  match runFlat (.block (algPrivate [] [] [("Double", doubleAlg85)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5]),
      .resolve "Double"
    ])
  ])) with
  | Except.ok [2, 4, 6, 8, 10] => true
  | _ => false

#guard test86a

-- Test 87: sequence-value-only map branches do not match scalar emitted range items
def test87 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Tag", tagAlg87)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1]),
      .resolve "Tag"
    ])
  ])) with
  | Except.ok [0, 0, 0, 0, 0] => true
  | _ => false

#guard test87

-- Test 88: mapping over an empty filter-result list yields the exact empty list `[]`
def test88 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a), ("CountMembers", countMembersAlg88a)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ]),
      .resolve "CountMembers"
    ])
  ])) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard test88

-- Test 89: sequenceValue collection elements are passed to the transform as whole values
def test89 : Bool :=
  match runFlat (.block (algPrivate [] [] [("TakeValue", takePairValueAlg89)] [
    .call (resolve "map") (alg [] [] [] [sequenceItems [
      .block (alg [] [] [] [.num 1, .num 10]),
      .block (alg [] [] [] [.num 2, .num 20]),
      .block (alg [] [] [] [.num 3, .num 30])],
      .resolve "TakeValue"
    ])
  ])) with
  | Except.ok [10, 20, 30] => true
  | _ => false

#guard test89

-- Test 90: sequence-value mapped results are accepted for emitted range items
def test90 : Bool :=
  match runResult (.block (algPrivate [] [] [("PairWithSquare", pairWithSquareAlg90)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "PairWithSquare"
    ])
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
  match runResult (.block (algPrivate [] [] [("Bad", mapEmptyAlg91)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "Bad"
    ])
  ])) with
  | Except.error err => hasContext "map transform must return a single element" err && innermostIsBadArity err
  | _ => false

#guard test91

-- Test 92: map transform must not return multiple top-level outputs
def test92 : Bool :=
  match runResult (.block (algPrivate [] [] [("Bad", mapMultiAlg92)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "Bad"
    ])
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
  match runFlat (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5])
    ])
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test93

-- Test 94: dot-call sum uses receiver injection with no explicit args
def test94 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .dotCall
      (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
      "sum"
      none
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test94

-- Test 95: descending ranges also expand for plain-call sum
def test95 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1])
    ])
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test95

-- Test 96: sum composes with filter and preserves strict top-level semantics
def test96 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") (alg [] [] [] [.num 1, .num 10]))
        "filter"
        (some (alg [] [] [] [.resolve "IsEven"])))
      "sum"
      none
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard test96

-- Test 97: sum composes with map and sums the mapped top-level elements
def test97 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Square", squareAlg86)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") (alg [] [] [] [.num 1, .num 4]))
        "map"
        (some (alg [] [] [] [.resolve "Square"])))
      "sum"
      none
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard test97

-- Test 98: plain-call sum of an empty collection returns zero
def test98 : Bool :=
  match runFlat (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "sum") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ])
    ])
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test98

-- Test 99: a single atomic value is treated as a one-element collection
def test99 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [.num 5])
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test99

-- Test 100: sequenceValue top-level elements are rejected rather than flattened
def test100 : Bool :=
  let sequenceValuePairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [sequenceValuePairs])
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test100

-- Test 101: string elements are rejected by sum
def test101 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test101

--------------------------------------------------------------------------------
-- count builtin tests
--------------------------------------------------------------------------------

-- Test 102: plain-call count counts expanded range items
def test102 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5])
    ])
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test102

-- Test 103: dot-call count uses receiver injection with no explicit args
def test103 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .dotCall
      (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
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
    ("Data2", alg [] [] [] [.block (alg [] [] [] [.num 1, .num 7])])
  ] [
    .dotCall (.resolve "Data1") "count" none,
    .dotCall (.resolve "Data2") "count" none,
    .dotCall (.block (alg [] [] [] [.num 1, .num 7])) "count" none,
    .dotCall (.block (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 7])
    ])) "count" none
  ]

def test103a : Bool :=
  match runFlat (.block countReceiverNormalizationRoot103a) with
  | Except.ok [2, 2, 2, 2] => true
  | _ => false

#guard test103a

-- Test 103b: nested sequence-value receiver boundaries are preserved after one strip
def test103b : Bool :=
  let sequenceValuePairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runFlat (.block (alg [] [] [] [
    .dotCall sequenceValuePairs "count" none,
    .dotCall (.block (alg [] [] [] [sequenceValuePairs])) "count" none
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test103b

-- Test 104: descending ranges still count all expanded top-level items
def test104 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1])
    ])
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test104

-- Test 105: count composes with filter over kept top-level elements
def test105 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") (alg [] [] [] [.num 1, .num 10]))
        "filter"
        (some (alg [] [] [] [.resolve "IsEven"])))
      "count"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test105

-- Test 106: count composes with map and counts mapped top-level elements
def test106 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Square", squareAlg86)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") (alg [] [] [] [.num 1, .num 4]))
        "map"
        (some (alg [] [] [] [.resolve "Square"])))
      "count"
      none
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test106

-- Test 107: plain-call count of an empty collection is zero
def test107 : Bool :=
  match runFlat (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "count") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ])
    ])
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test107

-- Test 107a: dot-call count of an empty filtered receiver is zero
def test107a : Bool :=
  match runFlat (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .dotCall
      (.dotCall
        (.block (alg [] [] [] [.num 1, .num 5, .num 3]))
        "filter"
        (some (alg [] [] [] [.resolve "AlwaysFalse"])))
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
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [])
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
    match runResult (.block (alg [] [] [] [
      .call (resolve "sum") (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])
    ])) with
    | Except.error err => innermostIsArityMismatch 1 6 err
    | _ => false
  let grouped :=
    match runFlat (.block (alg [] [] [] [
      .call (resolve "sum") (alg [] [] [] [.block (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])])
    ])) with
    | Except.ok [16] => true
    | _ => false
  let emptyErrs :=
    match runResult (.block (alg [] [] [] [.call (resolve "sum") (alg [] [] [] [])])) with
    | Except.error err => innermostIsArityMismatch 1 0 err
    | _ => false
  inlineErrs && grouped && emptyErrs

#guard builtinSumTakesOneCollectionArgument

-- Multiple sibling arguments are never flattened into one collection: sum(A, B) with
-- A = (1, 2) and B = (3, 4) is a two-argument arity error, and sum(A..., B...) opens the
-- spreads into FOUR ordinary argument slots (also an arity error). The concatenation
-- rewrite groups the spreads into ONE collection argument: sum((A..., B...)) = 10.
def builtinSumSiblingsNotFlattened : Bool :=
  let siblingsErr :=
    match runResult (.block (algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4])
    ] [ .call (resolve "sum") (alg [] [] [] [resolve "A", resolve "B"]) ])) with
    | Except.error err => innermostIsArityMismatch 1 2 err
    | _ => false
  let spreadSiblingsErr :=
    match runResult (.block (algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4])
    ] [ .call (resolve "sum") (alg [] [] [] [sequenceSpread (resolve "A"), sequenceSpread (resolve "B")]) ])) with
    | Except.error err => innermostIsArityMismatch 1 4 err
    | _ => false
  let groupedConcatenates :=
    match runFlat (.block (algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4])
    ] [ .call (resolve "sum") (alg [] [] [] [
          .block (alg [] [] [] [sequenceSpread (resolve "A"), sequenceSpread (resolve "B")])]) ])) with
    | Except.ok [10] => true
    | _ => false
  siblingsErr && spreadSiblingsErr && groupedConcatenates

#guard builtinSumSiblingsNotFlattened

-- contains(collection, item): the first argument is the collection and the second is the
-- item. The inline multi-item call is an arity error; the grouped form binds.
def builtinContainsTakesCollectionAndItem : Bool :=
  let inlineErrs :=
    match runResult (.block (alg [] [] [] [
      .call (resolve "contains") (alg [] [] [] [.num 1, .num 2, .num 3, .num 2])
    ])) with
    | Except.error err => innermostIsArityMismatch 2 4 err
    | _ => false
  let grouped :=
    match runFlat (.block (alg [] [] [] [
      .call (resolve "contains") (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2, .num 3]), .num 2])
    ])) with
    | Except.ok [1] => true
    | _ => false
  inlineErrs && grouped

#guard builtinContainsTakesCollectionAndItem

-- A collection builtin is NOT a user variadic: sum(3, 4, 2, 1, 3, 3) is an arity error
-- under `sum(collection)`, while a user variadic G(values...) = values.sum captures the
-- same inline items and sums them; the grouped call sum((3, 4, 2, 1, 3, 3)) is the
-- builtin twin.
def builtinFixedArityDiffersFromUserVariadic : Bool :=
  let builtinInlineErrs :=
    match runResult (.block (alg [] [] [] [
      .call (resolve "sum") (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])
    ])) with
    | Except.error err => innermostIsArityMismatch 1 6 err
    | _ => false
  let builtinGrouped :=
    match runFlat (.block (alg [] [] [] [
      .call (resolve "sum") (alg [] [] [] [.block (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])])
    ])) with
    | Except.ok [16] => true
    | _ => false
  let userSumAlg : Algorithm :=
    algWithParameters [{ name := "values", kind := .variadic }] [] [] [
      .dotCall (.param "values") "sum" none
    ]
  let viaUser :=
    match runFlat (.block (algPrivate [] [] [("G", userSumAlg)] [
      .call (resolve "G") (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])
    ])) with
    | Except.ok [16] => true
    | _ => false
  builtinInlineErrs && builtinGrouped && viaUser

#guard builtinFixedArityDiffersFromUserVariadic

-- Test 108: count's one bound sequence-valued argument is opened by the
-- one-level collection view — two nested pairs are two items.
def test108 : Bool :=
  let sequenceValuePairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [sequenceValuePairs])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test108

-- Test 108a: plain-call `count(filter(X, pred))` destructures the one filtered
-- sequence argument and counts its kept items.
def test108aPlainCountFilterCountsOneSequenceValueResult : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .call (resolve "count") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsEven"
      ])
    ])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test108aPlainCountFilterCountsOneSequenceValueResult

-- Test 109: a single atomic value is treated as a one-element collection
def test109 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [.num 5])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test109

-- Test 110: string elements are valid top-level elements for count
def test110 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110

-- Test 110a: plain-call contains searches expanded range items
def test110a : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "contains") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5]),
      .num 3
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110a

-- Test 110b: contains returns zero when no top-level item matches
def test110b : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "contains") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5]),
      .num 9
    ])
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test110b

-- Test 110c: dot-call contains matches plain-call receiver semantics
def test110c : Bool :=
  match runFlat (.block (alg [] [] [] [
    .dotCall
      (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
      "contains"
      (some (alg [] [] [] [.num 4]))
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110c

-- Test 110d: contains compares sequence-value top-level elements structurally
def test110d : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "contains") (alg [] [] [] [
      sequenceItems [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 3, .num 4])
      ],
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110d

-- Test 110e: contains searches top-level items only, not nested sequence elements
def test110e : Bool :=
  let sequenceValuePairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  let nestedCollection := sequenceItems [sequenceValuePairs, .num 0]
  match runFlat (.block (alg [] [] [] [
    .call (resolve "contains") (alg [] [] [] [
      nestedCollection,
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test110e

-- Test 110f: selection-projected content follows the same contains rules in both call styles
def containsProjectionRoot110f : Algorithm :=
  algPrivate [] [] [
    ("Data", alg [] [] [] [
      .block (alg [] [] [] [.num 7, .num 6, .num 4, .num 2, .num 1]),
      .block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])
    ])
  ] [
    .call (resolve "contains") (alg [] [] [] [
      .index (.resolve "Data") (.num 0),
      .num 4
    ]),
    .dotCall (.index (.resolve "Data") (.num 0)) "contains" (some (alg [] [] [] [.num 4]))
  ]

def test110f : Bool :=
  match runFlat (.block containsProjectionRoot110f) with
  | Except.ok [1, 1] => true
  | _ => false

#guard test110f

-- Test 110g: contains's item argument stays outside the collection — a
-- multi-output helper bound to `item` is compared as one grouped value.
def test110g : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Item", alg [] [] [] [.num 1, .num 2])
  ] [
    .call (resolve "contains") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .resolve "Item"
    ])
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
  match runFlat (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5])
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test111

-- Test 112: dot-call min uses receiver injection with no explicit args
def test112 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .dotCall
      (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
      "min"
      none
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test112

-- Test 113: descending ranges also expand for plain-call min
def test113 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1])
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test113

-- Test 114: min composes with filter over kept top-level elements
def test114 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") (alg [] [] [] [.num 1, .num 10]))
        "filter"
        (some (alg [] [] [] [.resolve "IsEven"])))
      "min"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test114

-- Test 115: min composes with map and compares mapped top-level elements
def test115 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Negate", negateAlg111)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") (alg [] [] [] [.num 1, .num 4]))
        "map"
        (some (alg [] [] [] [.resolve "Negate"])))
      "min"
      none
  ])) with
  | Except.ok [-4] => true
  | _ => false

#guard test115

-- Test 116: plain-call min requires a non-empty collection
def test116 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "min") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ])
    ])
  ])) with
  | Except.error err => hasContext "min requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test116

-- Test 117: a single atomic value is treated as a one-element collection
def test117 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [.num 5])
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test117

-- Test 118: sequenceValue top-level elements are rejected rather than flattened
def test118 : Bool :=
  let sequenceValuePairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [sequenceValuePairs])
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test118

-- Test 119: string elements are rejected by min
def test119 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test119

--------------------------------------------------------------------------------
-- max builtin tests
--------------------------------------------------------------------------------

-- Test 120: plain-call max compares expanded range items
def test120 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5])
    ])
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test120

-- Test 121: dot-call max uses receiver injection with no explicit args
def test121 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .dotCall
      (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
      "max"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test121

-- Test 122: descending ranges also expand for plain-call max
def test122 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1])
    ])
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test122

-- Test 123: max composes with filter over kept top-level elements
def test123 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") (alg [] [] [] [.num 1, .num 10]))
        "filter"
        (some (alg [] [] [] [.resolve "IsEven"])))
      "max"
      none
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test123

-- Test 124: max composes with map and compares mapped top-level elements
def test124 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Negate", negateAlg111)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") (alg [] [] [] [.num 1, .num 4]))
        "map"
        (some (alg [] [] [] [.resolve "Negate"])))
      "max"
      none
  ])) with
  | Except.ok [-1] => true
  | _ => false

#guard test124

-- Test 125: plain-call max requires a non-empty collection
def test125 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "max") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ])
    ])
  ])) with
  | Except.error err => hasContext "max requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test125

-- Test 126: a single atomic value is treated as a one-element collection
def test126 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [.num 5])
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test126

-- Test 127: sequenceValue top-level elements are rejected rather than flattened
def test127 : Bool :=
  let sequenceValuePairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [sequenceValuePairs])
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test127

-- Test 128: string elements are rejected by max
def test128 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test128

-- Test 129: plain-call avg averages expanded range items
def test129 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5])
    ])
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test129

-- Test 130: dot-call avg uses receiver injection with no explicit args
def test130 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .dotCall
      (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
      "avg"
      none
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test130

-- Test 131: descending ranges also expand for plain-call avg
def test131 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1])
    ])
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test131

-- Test 132: avg composes with filter over kept top-level elements
def test132 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") (alg [] [] [] [.num 1, .num 10]))
        "filter"
        (some (alg [] [] [] [.resolve "IsEven"])))
      "avg"
      none
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test132

-- Test 133: avg composes with map and averages mapped top-level elements
def test133 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Double", doubleAlg85)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") (alg [] [] [] [.num 1, .num 4]))
        "map"
        (some (alg [] [] [] [.resolve "Double"])))
      "avg"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test133

-- Test 134: plain-call avg requires a non-empty collection
def test134 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "avg") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ])
    ])
  ])) with
  | Except.error err => hasContext "avg requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test134

-- Test 135: a single atomic value is treated as a one-element collection
def test135 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [.num 5])
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test135

-- Test 136: sequenceValue top-level elements are rejected rather than flattened
def test136 : Bool :=
  let sequenceValuePairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [sequenceValuePairs])
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test136

-- Test 137: string elements are rejected by avg
def test137 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test137

--------------------------------------------------------------------------------
-- order builtins tests
--------------------------------------------------------------------------------

-- Test 138: ordinary builtin-call order sorts direct multi-argument inputs ascending and preserves duplicates
def test138 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [sequenceItems [
      .num 3,
      .num 4,
      .num 2,
      .num 1,
      .num 3,
      .num 3
    ]])
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test138

-- Test 139: dot-call order sorts property output ascending
def test139 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .dotCall (.resolve "Values") "order" none
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test139

-- Test 140: dot-call orderDesc sorts descending and preserves duplicates
def test140 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .dotCall (.resolve "Values") "orderDesc" none
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#guard test140

-- Test 141: sorting a descending range returns ascending output for order
def test141 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .dotCall
      (.call (resolve "range") (alg [] [] [] [.num 5, .num 1]))
      "order"
      none
  ])) with
  | Except.ok [1, 2, 3, 4, 5] => true
  | _ => false

#guard test141

-- Test 142: dot-call order preserves empty receiver outputs
def test142 : Bool :=
  match runFlat (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .dotCall
      (.call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ]))
      "order"
      none
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test142

-- Test 143: unsupported sortable elements are rejected by order
def test143 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .stringLiteral "hello"])
    ])
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 1 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test143

--------------------------------------------------------------------------------
-- first/last builtin tests
--------------------------------------------------------------------------------

-- Test 144: plain-call first returns the first expanded range item
def test144 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "first") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5])
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test144

-- Test 145: dot-call first uses receiver injection with no explicit args
def test145 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .dotCall
      (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
      "first"
      none
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test145

-- Test 146: plain-call last returns the last expanded range item
def test146 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "last") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5])
    ])
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test146

-- Test 147: dot-call last uses receiver injection with no explicit args
def test147 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .dotCall
      (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
      "last"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test147

-- Test 148: first returns the first item of the grouped collection (opened by the one-level collection view)
def test148 : Bool :=
  let sequenceValuePairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "first") (alg [] [] [] [sequenceValuePairs])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard test148

-- Test 149: last returns the last item of the grouped collection (opened by the one-level collection view)
def test149 : Bool :=
  let sequenceValuePairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "last") (alg [] [] [] [sequenceValuePairs])
  ])) with
  | Except.ok (.sequenceValue [.atom 3, .atom 4]) => true
  | _ => false

#guard test149

-- Test 150: plain-call first requires a non-empty collection
def test150 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "first") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ])
    ])
  ])) with
  | Except.error err => hasContext "first requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test150

-- Test 151: plain-call last requires a non-empty collection
def test151 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "last") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ])
    ])
  ])) with
  | Except.error err => hasContext "last requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test151

-- Additional sequence-input builtin regression tests

def test151a : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [sequenceItems [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]])
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test151a

def test151b : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "orderDesc") (alg [] [] [] [sequenceItems [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]])
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#guard test151b

def test151c : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2])] [
    .call (resolve "order") (alg [] [] [] [sequenceItems [sequenceSpread (.resolve "Values"), .num 1, .num 3]])
  ])) with
  | Except.ok [1, 2, 3, 3, 4] => true
  | _ => false

#guard test151c

def test151d : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [sequenceItems [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ]])
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151d

def test151e : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "orderDesc") (alg [] [] [] [sequenceItems [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ]])
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151e

def test151f : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "first") (alg [] [] [] [sequenceItems [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ]])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard test151f

def test151g : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "last") (alg [] [] [] [sequenceItems [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ]])
  ])) with
  | Except.ok (.sequenceValue [.atom 3, .atom 4]) => true
  | _ => false

#guard test151g

def test151h : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [sequenceItems [.num 10, .num 20, .num 30]])
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test151h

def test151i : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [sequenceItems [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ]])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test151i

def test151j : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [sequenceItems [.num 10, .num 20, .num 30]])
  ])) with
  | Except.ok [60] => true
  | _ => false

#guard test151j

def test151k : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [sequenceItems [.num 10, .num 4, .num 7]])
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test151k

def test151l : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [sequenceItems [.num 10, .num 4, .num 7]])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test151l

def test151m : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [sequenceItems [.num 10, .num 20, .num 30]])
  ])) with
  | Except.ok [20] => true
  | _ => false

#guard test151m

def test151n : Bool :=
  match runFlat (.block (algPrivate [] [] [("KeepFourSequenceValue", keepFourSequenceValueAlg66c)] [
    .call (resolve "filter") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 3, .num 6]))],
      .resolve "KeepFourSequenceValue"
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test151n

def test151o : Bool :=
  match runFlat (.block (algPrivate [] [] [("MarkThreeSequenceValue", markThreeSequenceValueAlg66e)] [
    .call (resolve "map") (alg [] [] [] [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 2, .num 4]))],
      .resolve "MarkThreeSequenceValue"
    ])
  ])) with
  | Except.ok [0, 0, 0, 0] => true
  | _ => false

#guard test151o

-- SequenceValue source `map((1, range(2, 4)...), MarkThreeSequenceValue)`: postfix spread
-- contributes inside the single grouped value, opened by the collection view.
def test151ob : Bool :=
  match runFlat (.block (algPrivate [] [] [("MarkThreeSequenceValue", markThreeSequenceValueAlg66e)] [
    .call (resolve "map") (alg [] [] [] [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 2, .num 4]))],
      .resolve "MarkThreeSequenceValue"
    ])
  ])) with
  | Except.ok [0, 0, 0, 0] => true
  | _ => false

#guard test151ob

-- SequenceValue source `filter((1, range(2, 4)...), MarkThreeSequenceValue)`: postfix spread
-- contributes inside the single grouped value, opened by the collection view.
def test151oc : Bool :=
  match runFlat (.block (algPrivate [] [] [("MarkThreeSequenceValue", markThreeSequenceValueAlg66e)] [
    .call (resolve "filter") (alg [] [] [] [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 2, .num 4]))],
      .resolve "MarkThreeSequenceValue"
    ])
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
  match runFlat (.block (algPrivate [] [] [("MarkSequenceValueRange", markSequenceValueRangeDirectCallAlg151oa)] [
    .call (resolve "MarkSequenceValueRange") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3])
    ])
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test151oa

def test151p : Bool :=
  match runFlat (.block (algPrivate [] [] [("AddItemCount", addItemCountAlg80c)] [
    .call (resolve "reduce") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 3, .num 4]))],
      .resolve "AddItemCount",
      .num 0
    ])
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
  match runFlat (.block (algPrivate [] [] [("AddSequenceValueRange", addSequenceValueRangeAlg151pb)] [
    .call (resolve "reduce") (alg [] [] [] [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 2, .num 4]))],
      .resolve "AddSequenceValueRange",
      .num 0
    ])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test151pb

-- SequenceValue source `reduce((1, range(2, 4)...), AddSequenceValueRange, 0)`: postfix
-- spread contributes inside the single grouped value, opened by the collection view.
def test151pc : Bool :=
  match runFlat (.block (algPrivate [] [] [("AddSequenceValueRange", addSequenceValueRangeAlg151pb)] [
    .call (resolve "reduce") (alg [] [] [] [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 2, .num 4]))],
      .resolve "AddSequenceValueRange",
      .num 0
    ])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test151pc

def test151q : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [
      sequenceItems [.block (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]), .num 0]
    ])
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151q

def test151r : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .call (resolve "order") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test151r

def test151s : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.block (alg [] [] [] [.num 3, .num 4, .num 2])])] [
    .call (resolve "order") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [2, 3, 4] => true
  | _ => false

#guard test151s

def test151t : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "orderDesc") (alg [] [] [] [
      sequenceItems [.block (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]), .num 0]
    ])
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151t

def test151u : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .call (resolve "orderDesc") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#guard test151u

def test151v : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.block (alg [] [] [] [.num 3, .num 4, .num 2])])] [
    .call (resolve "orderDesc") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [4, 3, 2] => true
  | _ => false

#guard test151v

def test151w : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test151w

def test151x : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "first") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard test151x

def test151y : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "last") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.ok (.atom 2) => true
  | _ => false

#guard test151y

-- Additional uniform sequence-extraction wrapper regressions

def test152 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("KeepSecondEven", evenPredicateAlg19d),
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 1, .num 3])
    ])
  ] [
    .call (resolve "filter") (alg [] [] [] [
      .resolve "Values",
      .resolve "KeepSecondEven"
    ])
  ])) with
  -- One sequence-valued item is kept; the exact-list materializer keeps it as one
  -- list element, so the result is `[(1, 2)]` (never erased to the item itself).
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard test152

def test153 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("TakeValue", takePairValueAlg89),
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ] [
    .call (resolve "map") (alg [] [] [] [
      .resolve "Values",
      .resolve "TakeValue"
    ])
  ])) with
  | Except.ok [2, 4] => true
  | _ => false

#guard test153

def test154 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("AddValue", reduceSequenceValueItemAlg79),
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ] [
    .call (resolve "reduce") (alg [] [] [] [
      .resolve "Values",
      .resolve "AddValue",
      .num 0
    ])
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test154

def test155 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3])
    ])
  ] [
    .call (resolve "count") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test155

def test156 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .call (resolve "count") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test156

def test157 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ] [
    .call (resolve "first") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard test157

def test158 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ] [
    .call (resolve "last") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok (.atom 2) => true
  | _ => false

#guard test158

def test159 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 10, .num 20, .num 30])
    ])
  ] [
    .call (resolve "sum") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok (.atom 60) => true
  | _ => false

#guard test159

def test160 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 10, .num 20, .num 30])
    ])
  ] [
    .call (resolve "min") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok (.atom 10) => true
  | _ => false

#guard test160

def test161 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 10, .num 20, .num 30])
    ])
  ] [
    .call (resolve "max") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok (.atom 30) => true
  | _ => false

#guard test161

def test162 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 10, .num 20, .num 30])
    ])
  ] [
    .call (resolve "avg") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok (.atom 20) => true
  | _ => false

#guard test162

def test163 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 20, .num 30])
  ] [
    .call (resolve "sum") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [60] => true
  | _ => false

#guard test163

def test164 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 4, .num 7])
  ] [
    .call (resolve "min") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test164

def test165 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 4, .num 7])
  ] [
    .call (resolve "max") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test165

def test166 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 20, .num 30])
  ] [
    .call (resolve "avg") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [20] => true
  | _ => false

#guard test166

def test167 : Bool :=
  match runFlat (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .dotCall
      (.call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ]))
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
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [sequenceItems [.num 1, .num 2]])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test168

-- avg truncates its quotient toward zero (Int.tdiv), matching the truncating
-- division convention of `div`/`mod`: avg(-1, -2) = (-3).tdiv 2 = -1.
-- The decimal runtime keeps the exact fractional average (-1.5) instead.
def test169 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [sequenceItems [.num (-1), .num (-2)]])
  ])) with
  | Except.ok [-1] => true
  | _ => false

#guard test169

def test170 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [sequenceItems [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ]])
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test170

def test171 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "orderDesc") (alg [] [] [] [sequenceItems [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ]])
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test171

def test172 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [sequenceItems [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ]])
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test172

def test173 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [sequenceItems [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ]])
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test173

def test174 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [sequenceItems [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ]])
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test174

def test175 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [sequenceItems [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ]])
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test175

def test176 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, .num 3, .num 4, .num 5],
      .num 3
    ])
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test176

def test177 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, .num 3, .num 4, .num 5],
      .num 3
    ])
  ])) with
  | Except.ok [4, 5] => true
  | _ => false

#guard test177

def test178 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 0
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test178

def test179 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 0
    ])
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test179

def test180 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, .num 3],
      .num (-2)
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test180

def test181 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, .num 3],
      .num (-2)
    ])
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test181

def test182 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 10
    ])
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test182

def test183 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 10
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test183

def test184 : Bool :=
  match runFlat (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "take") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ]),
      .num 3
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test184

def test185 : Bool :=
  match runFlat (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "skip") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ]),
      .num 3
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test185

def test186 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [sequenceItems [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])],
      .num 1
    ])
  ])) with
  -- Taking one sequence-valued item keeps it as one exact list element:
  -- the result is `[(1, 2)]` (`first` still selects the item itself).
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard test186

def test187 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [sequenceItems [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])],
      .num 1
    ])
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
  .block (algPrivate [] [] [
    ("T", alg [] [] [] [
      .call (resolve "take") (alg [] [] [] [
        sequenceItems [
          .block (alg [] [] [] [.num 1, .num 2]),
          .block (alg [] [] [] [.num 3, .num 4])
        ],
        .num 1
      ])
    ])
  ] [output])

def takeSingleKeptItemIsExactListValue : Bool :=
  match runResult (takeSingleKeptItemProgram (.resolve "T")) with
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard takeSingleKeptItemIsExactListValue

def takeSingleKeptItemCount : Bool :=
  match runResult (takeSingleKeptItemProgram
      (.call (resolve "count") (alg [] [] [] [.resolve "T"]))) with
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
        (.block (alg [] [] [] [sequenceItems [.num 1, .num 2]])))) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard takeSingleKeptItemNotEqualWrappedLiteral

-- A single kept empty-sequence item stays one exact list element:
-- `distinct(((), ()))` dedups the two equal `()` items of the one grouped
-- collection argument to one kept item and yields the exact list `[()]`
-- (count 1) — never erased to `()` itself. The ungrouped spelling
-- `distinct((), ())` is a two-argument arity error under `distinct(collection)`.
def distinctSingleKeptEmptyItemStaysExactElement : Bool :=
  match runResult (.call (resolve "distinct")
      (alg [] [] [] [.block (alg [] [] [] [.emptySequence 0, .emptySequence 0])])) with
  | Except.ok (.listValue [.sequenceValue []]) => true
  | _ => false

#guard distinctSingleKeptEmptyItemStaysExactElement

def distinctTwoEmptyArgumentsIsArityError : Bool :=
  match runResult (.call (resolve "distinct")
      (alg [] [] [] [.emptySequence 0, .emptySequence 0])) with
  | Except.error err => innermostIsArityMismatch 1 2 err
  | _ => false

#guard distinctTwoEmptyArgumentsIsArityError

def distinctSingleKeptEmptyItemCountsOne : Bool :=
  match runResult (.call (resolve "count") (alg [] [] [] [
    .call (resolve "distinct") (alg [] [] [] [.block (alg [] [] [] [.emptySequence 0, .emptySequence 0])])
  ])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard distinctSingleKeptEmptyItemCountsOne

def distinctSingleKeptEmptyItemNotEqualEmpty : Bool :=
  match runResult (.binary .eq
      (.call (resolve "distinct") (alg [] [] [] [.block (alg [] [] [] [.emptySequence 0, .emptySequence 0])]))
      (.emptySequence 0)) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard distinctSingleKeptEmptyItemNotEqualEmpty

-- Multiple kept empty-sequence items keep their sibling boundaries as exact list
-- elements. `take(((), ()), 2)` is the two-element list `[(), ()]` with count 2 —
-- the materializer is exact and never collapses or drops meaningful sibling items.
def takeMultipleEmptyItemsPreservesSiblingBoundaries : Bool :=
  match runResult (.call (resolve "take")
      (alg [] [] [] [.block (alg [] [] [] [.emptySequence 0, .emptySequence 0]), .num 2])) with
  | Except.ok (.listValue [.sequenceValue [], .sequenceValue []]) => true
  | _ => false

#guard takeMultipleEmptyItemsPreservesSiblingBoundaries

def takeMultipleEmptyItemsCountsTwo : Bool :=
  match runResult (.call (resolve "count") (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [.block (alg [] [] [] [.emptySequence 0, .emptySequence 0]), .num 2])
  ])) with
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
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3])
    ])
  ] [
    .call (resolve "take") (alg [] [] [] [
      .resolve "Values",
      .num 1
    ])
  ])) with
  | Except.ok (.listValue [.atom 1]) => true
  | _ => false

#guard test188

def test189 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .call (resolve "take") (alg [] [] [] [
      .resolve "Values",
      .num 1
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test189

def test190 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3])
    ])
  ] [
    .call (resolve "skip") (alg [] [] [] [
      .resolve "Values",
      .num 1
    ])
  ])) with
  | Except.ok [2, 3] => true
  | _ => false

#guard test190

def test191 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .call (resolve "skip") (alg [] [] [] [
      .resolve "Values",
      .num 1
    ])
  ])) with
  | Except.ok [2, 3] => true
  | _ => false

#guard test191

def test192 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "take") (alg [] [] [] [
      sequenceItems [.num 1, .num 2],
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ])
    ])
  ])) with
  | Except.error err => hasContext "take count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#guard test192

def test193 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [
      sequenceItems [.num 3, .num 4],
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.error err => hasContext "take count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#guard test193

def test194 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      sequenceItems [.num 1, .num 2],
      .stringLiteral "hello"
    ])
  ])) with
  | Except.error err => hasContext "skip count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#guard test194

def test195 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      sequenceItems [.num 3, .num 4, .num 1],
      .num 2
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test195

def test196 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "distinct") (alg [] [] [] [sequenceItems [
      .num 3,
      .num 1,
      .num 3,
      .num 2,
      .num 1,
      .num 2]
    ])
  ])) with
  | Except.ok [3, 1, 2] => true
  | _ => false

#guard test196

def test197 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "distinct") (alg [] [] [] [sequenceItems [
      .num 4,
      .num 4,
      .num 4,
      .num 4]
    ])
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test197

def test198 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "distinct") (alg [] [] [] [sequenceItems [
      .num 1,
      .num 2,
      .num 3]
    ])
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test198

def test199 : Bool :=
  match runFlat (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "distinct") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ])
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test199

def test200 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "distinct") (alg [] [] [] [sequenceItems [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])]
    ])
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 1, .atom 2],
      .sequenceValue [.atom 3, .atom 4]
    ]) => true
  | _ => false

#guard test200

def test201 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 3, .num 4])
      ])
    ])
  ] [
    .call (resolve "distinct") (alg [] [] [] [
      .resolve "Values"
    ])
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 1, .atom 2],
      .sequenceValue [.atom 3, .atom 4]
    ]) => true
  | _ => false

#guard test201

def test202 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ] [
    .call (resolve "distinct") (alg [] [] [] [
      .resolve "Values"
    ])
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 1, .atom 2],
      .sequenceValue [.atom 3, .atom 4]
    ]) => true
  | _ => false

#guard test202

def test203 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ])) "order" none) with
  | Except.ok [3, 3, 3, 5, 6] => true
  | _ => false

#guard test203

def test204 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ])) "orderDesc" none) with
  | Except.ok [6, 5, 3, 3, 3] => true
  | _ => false

#guard test204

def test205 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ])) "count" none) with
  | Except.ok [5] => true
  | _ => false

#guard test205

def test206 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [
    .num 3,
    .num 5,
    .num 3
  ])) "sum" none) with
  | Except.ok [11] => true
  | _ => false

#guard test206

def test207 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [
    .num 1,
    .num 2,
    .num 1,
    .num 3
  ])) "distinct" none) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test207

def test208 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [
    .num 1,
    .num 2,
    .num 3
  ])) "take" (some (alg [] [] [] [.num 2]))) with
  | Except.ok [1, 2] => true
  | _ => false

#guard test208

def test209 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [
    .num 1,
    .num 2,
    .num 3
  ])) "skip" (some (alg [] [] [] [.num 1]))) with
  | Except.ok [2, 3] => true
  | _ => false

#guard test209

def test210 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Double", doubleAlg85)] [
    .dotCall (.block (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3
    ])) "map" (some (alg [] [] [] [.resolve "Double"]))
  ])) with
  | Except.ok [2, 4, 6] => true
  | _ => false

#guard test210

def test211 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall (.block (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3,
      .num 4
    ])) "filter" (some (alg [] [] [] [.resolve "IsEven"]))
  ])) with
  | Except.ok [2, 4] => true
  | _ => false

#guard test211

def test212 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Add", addAlg76)] [
    .dotCall (.block (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3
    ])) "reduce" (some (alg [] [] [] [
      .resolve "Add",
      .num 0
    ]))
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test212

def test213 : Bool :=
  match runFlat (.dotCall (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 3, .num 1, .num 2])
  ] [
    .resolve "Values"
  ])) "order" none) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test213

def test214 : Bool :=
  let inlineReceiver := .block (alg [] [] [] [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ])
  let sequenceValueReceiver := .block (alg [] [] [] [inlineReceiver])
  let namedSequenceValueWorks :=
    match runFlat (.block (algPrivate [] [] [
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
  match runFlat (.block (algPrivate [] [] [
    ("Data", alg [] [] [] [
      .block (alg [] [] [] [.num 7, .num 6, .num 4, .num 2, .num 1]),
      .block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])
    ])
  ] [
    .call (resolve "count") (alg [] [] [] [.index (.resolve "Data") (.num 0)]),
    .dotCall (.index (.resolve "Data") (.num 0)) "count" none
    , .call (resolve "order") (alg [] [] [] [.index (.resolve "Data") (.num 0)])
    , .dotCall (.index (.resolve "Data") (.num 0)) "order" none
  ])) with
  | Except.ok [5, 5, 1, 2, 4, 6, 7, 1, 2, 4, 6, 7] => true
  | _ => false

#guard test215

def test215a : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [.num 7, .num 8])
  ] [
    .index (.resolve "A") (.num 0)
  ])) with
  | Except.ok (.atom 7) => true
  | _ => false

#guard test215a

def test215b : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ] [
    .index (.resolve "A") (.num 0)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard test215b

def test215c : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("A", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ] [
    .call (resolve "count") (alg [] [] [] [.index (.resolve "A") (.num 0)]),
    .dotCall (.index (.resolve "A") (.num 0)) "count" none
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test215c

def test215cWrappedProjectionBoundary : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("A", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ]),
    ("Projected", alg [] [] [] [
      .index (.resolve "A") (.num 0)
    ])
  ] [
    .call (resolve "count") (alg [] [] [] [.index (.resolve "A") (.num 0)]),
    .call (resolve "count") (alg [] [] [] [.resolve "Projected"])
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test215cWrappedProjectionBoundary

def test215d : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 3, .num 4])
      ]),
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 5, .num 6]),
        .block (alg [] [] [] [.num 7, .num 8])
      ])
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
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 3, .num 4])
      ]),
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 5, .num 6]),
        .block (alg [] [] [] [.num 7, .num 8])
      ])
    ])
  ] [
    .index (.index (.resolve "A") (.num 0)) (.num 1)
  ])) with
  | Except.ok (.sequenceValue [.atom 3, .atom 4]) => true
  | _ => false

#guard test215e

def test215f : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("A", alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 3, .num 4])
      ]),
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 5, .num 6]),
        .block (alg [] [] [] [.num 7, .num 8])
      ])
    ])
  ] [
    .call (resolve "count") (alg [] [] [] [.index (.resolve "A") (.num 0)]),
    .call (resolve "count") (alg [] [] [] [.index (.index (.resolve "A") (.num 0)) (.num 1)])
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test215f

def test215g : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 3, .num 4])
      ]),
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 5, .num 6]),
        .block (alg [] [] [] [.num 7, .num 8])
      ])
    ])
  ] [
    .call (resolve "sum") (alg [] [] [] [.index (.resolve "A") (.num 0)])
  ])) with
  | Except.error err =>
      hasContext "sum expects each collection element to be a single numeric value; item 0 was sequence value" err
        && innermostIsBadArity err
  | _ => false

#guard test215g

def test216 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 4, .num 5, .num 4, .num 6])
    ])
  ] [
    .dotCall (.resolve "Values") "first" none,
    .dotCall (.resolve "Values") "last" none,
    .dotCall (.resolve "Values") "distinct" none,
    .dotCall (.resolve "Values") "take" (some (alg [] [] [] [.num 2])),
    .dotCall (.resolve "Values") "skip" (some (alg [] [] [] [.num 1]))
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
    runResult (.block (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .block (alg [] [] [] [.num 10, .num 20, .num 30])
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
    runResult (.block (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 1, .num 3])
      ]),
      ("KeepSecondEven", keepSecondEven)
    ] [
      .dotCall (.resolve "Values") "filter" (some (alg [] [] [] [.resolve "KeepSecondEven"]))
    ]))
  let mapResult :=
    runResult (.block (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2, .num 3]),
        .block (alg [] [] [] [.num 4, .num 5, .num 6])
      ]),
      ("TakeFirst", takeFirstAlg)
    ] [
      .dotCall (.resolve "Values") "map" (some (alg [] [] [] [.resolve "TakeFirst"]))
    ]))
  let reduceResult :=
    runFlat (.block (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2, .num 3]),
        .block (alg [] [] [] [.num 4, .num 5, .num 6])
      ]),
      ("AddItemCount", addItemCount)
    ] [
      .dotCall (.resolve "Values") "reduce" (some (alg [] [] [] [.resolve "AddItemCount", .num 0]))
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
  match runResult (.dotCall (.block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])) "sum" none) with
  | Except.error err =>
      hasContext "sum expects each collection element to be a single numeric value; item 0 was sequence value" err
        && innermostIsBadArity err
  | _ => false

#guard test219

--------------------------------------------------------------------------------
-- Sequence-boundary cleanup regressions
--------------------------------------------------------------------------------

def test228 : Bool :=
  match runFlat (.call (resolve "count") (alg [] [] [] [
    sequenceItems [.num 3, .num 4, sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 1, .num 5])), .num 7]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard test228

def test229 : Bool :=
  let sequenceValueRange := .block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])
  match runFlat (.block (alg [] [] [] [
    .call (resolve "contains") (alg [] [] [] [
      sequenceItems [.num 3, .num 4, sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 1, .num 5])), .num 7],
      .num 5
    ]),
    .call (resolve "contains") (alg [] [] [] [
      sequenceItems [.num 3, .num 4, sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 1, .num 5])), .num 7],
      sequenceValueRange
    ])
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard test229

def test230 : Bool :=
  match runFlat (.call (resolve "order") (alg [] [] [] [
    sequenceItems [.num 3, .num 4, sequenceSpread (.call (resolve "range") (alg [] [] [] [.num 1, .num 5])), .num 7]
  ])) with
  | Except.ok [1, 2, 3, 3, 4, 4, 5, 7] => true
  | _ => false

#guard test230

    def test231 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Data", alg [] [] [] [
      .block (alg [] [] [] [.num 7, .num 6, .num 4, .num 2, .num 1]),
      .block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])
    ])
  ] [
    .call (resolve "count") (alg [] [] [] [
      .index (.resolve "Data") (.num 0)
    ]),
    .dotCall (.index (.resolve "Data") (.num 0)) "count" none,
    .call (resolve "order") (alg [] [] [] [
      .index (.resolve "Data") (.num 0)
    ]),
    .dotCall (.index (.resolve "Data") (.num 0)) "order" none
  ])) with
  | Except.ok [5, 5, 1, 2, 4, 6, 7, 1, 2, 4, 6, 7] => true
  | _ => false

#guard test231

def test232 : Bool :=
  let firstReport := .block (alg [] [] [] [.num 7, .num 6, .num 4, .num 2, .num 1])
  let secondReport := .block (alg [] [] [] [.num 1, .num 2, .num 7, .num 8, .num 9])
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
  match runResult (.block (algPrivate [] [] [
    ("IsSafe", safeReportProjected)
  ] [
    .call (resolve "filter") (alg [] [] [] [
      sequenceItems [firstReport, secondReport],
      .resolve "IsSafe"
    ])
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
  match runFlat (.block (algPrivate [] [] [
    ("TakeFirst", takeFirstProjected)
  ] [
    .call (resolve "map") (alg [] [] [] [
      sequenceItems [
        .block (alg [] [] [] [.num 7, .num 6, .num 4, .num 2, .num 1]),
        .block (alg [] [] [] [.num 1, .num 2, .num 7, .num 8, .num 9])],
      .resolve "TakeFirst"
    ])
  ])) with
  | Except.ok [7, 1] => true
  | _ => false

#guard test233

def test234 : Bool :=
  let countItem : Algorithm :=
    alg ["x"] [] [] [
      .dotCall (.param "x") "count" none
    ]
  match runFlat (.block (algPrivate [] [] [
    ("Items", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3]),
      .block (alg [] [] [] [.num 7, .num 8, .num 9])
    ]),
    ("CountItem", countItem)
  ] [
    .dotCall (.resolve "Items") "count" none,
    .dotCall (.index (.resolve "Items") (.num 0)) "count" none,
    .dotCall (.index (.resolve "Items") (.num 1)) "count" none,
    .dotCall (.resolve "Items") "map" (some (alg [] [] [] [.resolve "CountItem"]))
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
  match runFlat (.block (algPrivate [] [] [
    ("Items", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3]),
      .block (alg [] [] [] [.num 7, .num 8, .num 9])
    ]),
    ("TakeFirst", takeFirstProjected),
    ("HasThreeItems", hasThreeItems)
  ] [
    .dotCall (.resolve "Items") "map" (some (alg [] [] [] [.resolve "TakeFirst"])),
    .dotCall
      (.dotCall (.resolve "Items") "filter" (some (alg [] [] [] [.resolve "HasThreeItems"])))
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
    .block (alg [] [] [] [
      .binary .add
        (.binary .mul (.index (.param "acc") (.num 0)) (.num 100))
        (.binary .add
          (.binary .mul (.dotCall (.param "current") "count" none) (.num 10))
          (.dotCall (.param "acc") "count" none)),
      .dotCall (.param "acc") "count" none
    ])
  ]

def test236 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Signature", reduceCurrentSelectionSignatureAlg236),
    ("Items", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ] [
    .dotCall (.index (.resolve "Items") (.num 0)) "count" none,
    .dotCall (.index (.resolve "Items") (.num 0)) "sum" none,
    .dotCall (.index (.resolve "Items") (.num 1)) "count" none,
    .dotCall (.index (.resolve "Items") (.num 1)) "sum" none,
    .dotCall (.resolve "Items") "reduce" (some (alg [] [] [] [.resolve "Signature", .num 0])),
    .call (.resolve "reduce") (alg [] [] [] [
      sequenceItems [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 3, .num 4])],
      .resolve "Signature",
      .num 0
    ])
  ])) with
  | Except.ok [2, 3, 2, 7, 2327, 2327] => true
  | _ => false

#guard test236

def test237 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Signature", reduceCurrentOneLevelSignatureAlg237),
    ("Items", alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 3, .num 4])
      ])
    ])
  ] [
    .dotCall (.index (.resolve "Items") (.num 0)) "count" none,
    .dotCall (.resolve "Items") "reduce" (some (alg [] [] [] [.resolve "Signature", .num 0])),
    .call (.resolve "reduce") (alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2]),
        .block (alg [] [] [] [.num 3, .num 4])
      ]),
      .resolve "Signature",
      .num 0
    ])
  ])) with
  | Except.ok [2, 2121, 2121] => true
  | _ => false

#guard test237

def test238 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Signature", reduceAccumulatorAsymmetryAlg238),
    ("Items", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ] [
    .dotCall (.resolve "Items") "reduce" (some (alg [] [] [] [
      .resolve "Signature",
      .block (alg [] [] [] [.num 0, .num 9, .num 8])
    ]))
  ])) with
  | Except.ok (.sequenceValue [.atom 2322, .atom 2]) => true
  | _ => false

#guard test238

def reduceVariadicAppendAlg239 : Algorithm :=
  algWithParameters [{ name := "item" }, { name := "history", kind := .variadic }] [] [] [
    .block (alg [] [] [] [.sequenceConstruct (sequenceSpread (.param "history")) (.param "item")])
  ]

def reduceScalarSumAlg241 : Algorithm :=
  alg ["item", "total"] [] [] [
    .binary .add (.param "total") (.param "item")
  ]

def reduceStructuralAppendAlg242 : Algorithm :=
  alg ["item", "history"] [] [] [
    .block (alg [] [] [] [.sequenceConstruct (sequenceSpread (.param "history")) (.param "item")])
  ]

def reduceVariadicAccumulatorStateFlattens : Bool :=
  match runResult (.block (algPrivate [] [] [("Append", reduceVariadicAppendAlg239)] [
    .call (resolve "reduce") (alg [] [] [] [
      sequenceItems [.num 2, .num 3, .num 4],
      .resolve "Append",
      .num 1
    ])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3, .atom 4]) => true
  | _ => false

#guard reduceVariadicAccumulatorStateFlattens

def reduceScalarReducerBehaviorRemainsUnchanged : Bool :=
  match runFlat (.block (algPrivate [] [] [("Sum", reduceScalarSumAlg241)] [
    .call (resolve "reduce") (alg [] [] [] [
      sequenceItems [.num 2, .num 3, .num 4],
      .resolve "Sum",
      .num 1
    ])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard reduceScalarReducerBehaviorRemainsUnchanged

def reduceNonVariadicAccumulatorPreservesStructuralAccumulator : Bool :=
  match runResult (.block (algPrivate [] [] [("Append", reduceStructuralAppendAlg242)] [
    .call (resolve "reduce") (alg [] [] [] [
      sequenceItems [.num 2, .num 3, .num 4],
      .resolve "Append",
      .num 1
    ])
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
  KatLang.block (dotSweepAtomsAlg xs)

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
  match runFlat (.block (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [1, 2, 3]),
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [3, 1, 2] [9, 8, 7])
  ] [
    .dotCall (resolve "Values") "count" none,
    .call (resolve "count") (alg [] [] [] [resolve "Values"]),
    .dotCall (resolve "SequenceValue") "count" none,
    .call (resolve "count") (alg [] [] [] [resolve "SequenceValue"]),
    .dotCall data0 "count" none,
    .call (resolve "count") (alg [] [] [] [data0])
  ])) with
  | Except.ok [3, 3, 3, 3, 3, 3] => true
  | _ => false

#guard sequenceBuiltinDotCallCountSweep

def sequenceBuiltinDotCallContainsSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.block (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [1, 2, 3]),
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [3, 1, 2] [9, 8, 7])
  ] [
    .dotCall (resolve "Values") "contains" (some (alg [] [] [] [.num 2])),
    .call (resolve "contains") (alg [] [] [] [resolve "Values", .num 2]),
    .dotCall (resolve "SequenceValue") "contains" (some (alg [] [] [] [.num 2])),
    .dotCall (resolve "SequenceValue") "contains" (some (alg [] [] [] [dotSweepSequenceValueExpr [1, 2, 3]])),
    .dotCall data0 "contains" (some (alg [] [] [] [.num 2])),
    .call (resolve "contains") (alg [] [] [] [data0, .num 2])
  ])) with
  | Except.ok [1, 1, 1, 0, 1, 1] => true
  | _ => false

#guard sequenceBuiltinDotCallContainsSweep

def sequenceBuiltinDotCallOrderSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.block (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [3, 1, 2]),
    ("Data", dotSweepPairAlg [3, 1, 2] [9, 8, 7])
  ] [
    .dotCall (resolve "Values") "order" none,
    .dotCall (resolve "Values") "orderDesc" none,
    .dotCall data0 "order" none,
    .call (resolve "order") (alg [] [] [] [data0]),
    .dotCall data0 "orderDesc" none,
    .call (resolve "orderDesc") (alg [] [] [] [data0])
  ])) with
  | Except.ok [1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 3, 2, 1] => true
  | _ => false

#guard sequenceBuiltinDotCallOrderSweep

def sequenceBuiltinDotCallOrderBoundarySweep : Bool :=
  let orderValues :=
    match runFlat (.block (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [3, 1, 2])
    ] [
      .call (resolve "order") (alg [] [] [] [resolve "Values"])
    ])) with
    | Except.ok [1, 2, 3] => true
    | _ => false
  let orderDescValues :=
    match runFlat (.block (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [3, 1, 2])
    ] [
      .call (resolve "orderDesc") (alg [] [] [] [resolve "Values"])
    ])) with
    | Except.ok [3, 2, 1] => true
    | _ => false
  let sequenceValueOrder :=
    match runFlat (.block (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [3, 1, 2])
    ] [
      .dotCall (resolve "SequenceValue") "order" none
    ])) with
    | Except.ok [1, 2, 3] => true
    | _ => false
  let sequenceValueOrderDesc :=
    match runFlat (.block (algPrivate [] [] [
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
  match runFlat (.block (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [5, 6, 7]),
    ("Data", dotSweepPairAlg [9, 8, 7] [3, 2, 1])
  ] [
    .dotCall (resolve "Values") "first" none,
    .dotCall (resolve "Values") "last" none,
    .dotCall data0 "first" none,
    .call (resolve "first") (alg [] [] [] [data0]),
    .dotCall data0 "last" none,
    .call (resolve "last") (alg [] [] [] [data0])
  ])) with
  | Except.ok [5, 7, 9, 9, 7, 7] => true
  | _ => false

#guard sequenceBuiltinDotCallFirstLastSweep

def sequenceBuiltinDotCallFirstLastSequenceValueSweep : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("SequenceValue", dotSweepSequenceValueAlg [5, 6, 7])
  ] [
    .dotCall (resolve "SequenceValue") "first" none,
    .call (resolve "first") (alg [] [] [] [resolve "SequenceValue"]),
    .dotCall (resolve "SequenceValue") "last" none,
    .call (resolve "last") (alg [] [] [] [resolve "SequenceValue"])
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
  match runFlat (.block (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [1, 2, 1, 3]),
    ("Data", dotSweepPairAlg [1, 2, 1, 3] [9, 8, 9])
  ] [
    .dotCall (resolve "Values") "distinct" none,
    .dotCall data0 "distinct" none,
    .call (resolve "distinct") (alg [] [] [] [data0])
  ])) with
  | Except.ok [1, 2, 3, 1, 2, 3, 1, 2, 3] => true
  | _ => false

#guard sequenceBuiltinDotCallDistinctSweep

def sequenceBuiltinDotCallDistinctSequenceValueSweep : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 1, 3])
  ] [
    .dotCall (resolve "SequenceValue") "distinct" none,
    .call (resolve "distinct") (alg [] [] [] [resolve "SequenceValue"])
  ])) with
  | Except.ok (.sequenceValue [
      .listValue [.atom 1, .atom 2, .atom 3],
      .listValue [.atom 1, .atom 2, .atom 3]
    ]) => true
  | _ => false

#guard sequenceBuiltinDotCallDistinctSequenceValueSweep

def sequenceBuiltinDotCallTakeSkipSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.block (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [7, 6, 4, 2, 1] [1, 2, 3, 4, 5])
  ] [
    .dotCall (resolve "Values") "take" (some (alg [] [] [] [.num 2])),
    .call (resolve "take") (alg [] [] [] [resolve "Values", .num 2]),
    .dotCall (resolve "Values") "skip" (some (alg [] [] [] [.num 1])),
    .call (resolve "skip") (alg [] [] [] [resolve "Values", .num 1]),
    .dotCall data0 "take" (some (alg [] [] [] [.num 2])),
    .call (resolve "take") (alg [] [] [] [data0, .num 2]),
    .dotCall data0 "skip" (some (alg [] [] [] [.num 2])),
    .call (resolve "skip") (alg [] [] [] [data0, .num 2])
  ])) with
  | Except.ok [1, 2, 1, 2, 2, 3, 2, 3, 7, 6, 7, 6, 4, 2, 1, 4, 2, 1] => true
  | _ => false

#guard sequenceBuiltinDotCallTakeSkipSweep

def sequenceBuiltinDotCallTakeSkipSequenceValueSweep : Bool :=
  let takeOk :=
    match runResult (.block (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "SequenceValue") "take" (some (alg [] [] [] [.num 2])),
      .call (resolve "take") (alg [] [] [] [resolve "SequenceValue", .num 2])
    ])) with
    | Except.ok (.sequenceValue [
        .listValue [.atom 1, .atom 2],
        .listValue [.atom 1, .atom 2]
      ]) => true
    | _ => false
  let skipDotOk :=
    match runFlat (.block (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "SequenceValue") "skip" (some (alg [] [] [] [.num 1]))
    ])) with
    | Except.ok [2, 3] => true
    | _ => false
  let skipPlainOk :=
    match runFlat (.block (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .call (resolve "skip") (alg [] [] [] [resolve "SequenceValue", .num 1])
    ])) with
    | Except.ok [2, 3] => true
    | _ => false
  takeOk && skipDotOk && skipPlainOk

#guard sequenceBuiltinDotCallTakeSkipSequenceValueSweep

def sequenceBuiltinDotCallNamedReceiverBoundarySweep : Bool :=
  let namedMulti :=
    match runFlat (.block (algPrivate [] [] [
      ("A", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .dotCall (resolve "A") "take" (some (alg [] [] [] [.num 2])),
      .dotCall (resolve "A") "count" none
    ])) with
    | Except.ok [1, 2, 3] => true
    | _ => false
  let namedSequenceValue :=
    match runResult (.block (algPrivate [] [] [
      ("A", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "A") "take" (some (alg [] [] [] [.num 2])),
      .dotCall (resolve "A") "count" none
    ])) with
    | Except.ok (.sequenceValue [.listValue [.atom 1, .atom 2], .atom 3]) => true
    | _ => false
  let spread :=
    match runFlat (.block (algPrivate [] [] [
      ("A", alg [] [] [] [sequenceSpread (.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3))])
    ] [
      .dotCall (resolve "A") "take" (some (alg [] [] [] [.num 2]))
    ])) with
    | Except.ok [1, 2] => true
    | _ => false
  namedMulti && namedSequenceValue && spread

#guard sequenceBuiltinDotCallNamedReceiverBoundarySweep

def sequenceBuiltinDotCallUserAndConditionalReceiverBoundarySweep : Bool :=
  let userCall :=
    match runFlat (.block (algPrivate [] [] [
      ("F", alg ["x"] [] [] [.param "x", .binary .add (.param "x") (.num 1), .binary .add (.param "x") (.num 2)]),
      ("G", alg ["x"] [] [] [.block (alg [] [] [] [.param "x", .binary .add (.param "x") (.num 1), .binary .add (.param "x") (.num 2)])])
    ] [
      .dotCall (.call (resolve "F") (alg [] [] [] [.num 1])) "count" none,
      .dotCall (.call (resolve "F") (alg [] [] [] [.num 1])) "take" (some (alg [] [] [] [.num 2])),
      .dotCall (.call (resolve "G") (alg [] [] [] [.num 1])) "count" none
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
        { pattern := KatLang.Pattern.litInt 1, body := alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2, .num 3])] },
        { pattern := KatLang.Pattern.bind "x", body := alg [] [] [] [.block (alg [] [] [] [.num 4, .num 5, .num 6])] }
      ]
    match runFlat (.block (algPrivate [] [] [
      ("ChooseMulti", chooseMulti),
      ("ChooseSequenceValue", chooseSequenceValue)
    ] [
      .dotCall (.call (resolve "ChooseMulti") (alg [] [] [] [.num 1])) "take" (some (alg [] [] [] [.num 2])),
      .dotCall (.call (resolve "ChooseSequenceValue") (alg [] [] [] [.num 1])) "count" none
    ])) with
    | Except.ok [1, 2, 3] => true
    | _ => false
  userCall && conditional

#guard sequenceBuiltinDotCallUserAndConditionalReceiverBoundarySweep

def sequenceBuiltinDotCallInlineReceiverSweep : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("AddOne", dotSweepAddOneAlg),
    ("IsLarge", dotSweepIsGreaterThanOneAlg),
    ("Add", dotSweepAddAlg)
  ] [
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "count" none,
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "contains" (some (alg [] [] [] [.num 2])),
    .dotCall (dotSweepSequenceValueExpr [3, 1, 2]) "order" none,
    .dotCall (dotSweepSequenceValueExpr [5, 6, 7]) "first" none,
    .dotCall (dotSweepSequenceValueExpr [5, 6, 7]) "last" none,
    .dotCall (dotSweepSequenceValueExpr [1, 2, 1, 3]) "distinct" none,
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "take" (some (alg [] [] [] [.num 2])),
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "skip" (some (alg [] [] [] [.num 1])),
    .dotCall (dotSweepSequenceValueExpr [10, 4, 7]) "min" none,
    .dotCall (dotSweepSequenceValueExpr [10, 4, 7]) "max" none,
    .dotCall (dotSweepSequenceValueExpr [3, 5, 3]) "sum" none,
    .dotCall (dotSweepSequenceValueExpr [10, 4, 7]) "avg" none,
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "map" (some (alg [] [] [] [resolve "AddOne"])),
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3, 4]) "filter" (some (alg [] [] [] [resolve "IsLarge"])),
    .dotCall (dotSweepSequenceValueExpr [1, 2, 3]) "reduce" (some (alg [] [] [] [resolve "Add", .num 0]))
  ])) with
  | Except.ok [3, 1, 1, 2, 3, 5, 7, 1, 2, 3, 1, 2, 2, 3, 4, 10, 11, 7, 2, 3, 4, 2, 3, 4, 6] => true
  | _ => false

#guard sequenceBuiltinDotCallInlineReceiverSweep

def sequenceBuiltinDotCallNumericAggregationSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.block (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [3, 1, 2] [9, 8, 7])
  ] [
    .dotCall (resolve "Values") "sum" none,
    .dotCall (resolve "Values") "avg" none,
    .dotCall (resolve "Values") "min" none,
    .dotCall (resolve "Values") "max" none,
    .dotCall data0 "sum" none,
    .call (resolve "sum") (alg [] [] [] [data0]),
    .dotCall data0 "avg" none,
    .call (resolve "avg") (alg [] [] [] [data0]),
    .dotCall data0 "min" none,
    .call (resolve "min") (alg [] [] [] [data0]),
    .dotCall data0 "max" none,
    .call (resolve "max") (alg [] [] [] [data0])
  ])) with
  | Except.ok [6, 2, 1, 3, 6, 6, 2, 2, 1, 1, 3, 3] => true
  | _ => false

#guard sequenceBuiltinDotCallNumericAggregationSweep

def sequenceBuiltinDotCallNumericAggregationBoundarySweep : Bool :=
  let sumValues :=
    match runFlat (.block (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "sum") (alg [] [] [] [resolve "Values"])
    ])) with
    | Except.ok [6] => true
    | _ => false
  let sumSequenceValue :=
    match runFlat (.block (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "SequenceValue") "sum" none
    ])) with
    | Except.ok [6] => true
    | _ => false
  let avgValues :=
    match runFlat (.block (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "avg") (alg [] [] [] [resolve "Values"])
    ])) with
    | Except.ok [2] => true
    | _ => false
  let avgSequenceValue :=
    match runFlat (.block (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "SequenceValue") "avg" none
    ])) with
    | Except.ok [2] => true
    | _ => false
  let minValues :=
    match runFlat (.block (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "min") (alg [] [] [] [resolve "Values"])
    ])) with
    | Except.ok [1] => true
    | _ => false
  let minSequenceValue :=
    match runFlat (.block (algPrivate [] [] [
      ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3])
    ] [
      .dotCall (resolve "SequenceValue") "min" none
    ])) with
    | Except.ok [1] => true
    | _ => false
  let maxValues :=
    match runFlat (.block (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "max") (alg [] [] [] [resolve "Values"])
    ])) with
    | Except.ok [3] => true
    | _ => false
  let maxSequenceValue :=
    match runFlat (.block (algPrivate [] [] [
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
  match runFlat (.block (algPrivate [] [] [
    ("ItemCount", dotSweepTopLevelItemCountAlg),
    ("AddOne", dotSweepAddOneAlg),
    ("Items", alg [] [] [] [dotSweepSequenceValueExpr [1, 2, 3], .num 7]),
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [1, 2, 3] [4, 5, 6])
  ] [
    .dotCall (resolve "Items") "map" (some (alg [] [] [] [resolve "ItemCount"])),
    .call (resolve "map") (alg [] [] [] [resolve "Items", resolve "ItemCount"]),
    .dotCall (resolve "SequenceValue") "map" (some (alg [] [] [] [resolve "ItemCount"])),
    .call (resolve "map") (alg [] [] [] [resolve "SequenceValue", resolve "ItemCount"]),
    .dotCall data0 "map" (some (alg [] [] [] [resolve "AddOne"])),
    .call (resolve "map") (alg [] [] [] [data0, resolve "AddOne"])
  ])) with
  | Except.ok [3, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 4] => true
  | _ => false

#guard sequenceBuiltinDotCallMapSweep

def sequenceBuiltinDotCallFilterSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.block (algPrivate [] [] [
    ("KeepCountThree", dotSweepKeepCountThreeAlg),
    ("IsLarge", dotSweepIsGreaterThanOneAlg),
    ("Items", alg [] [] [] [dotSweepSequenceValueExpr [1, 2, 3], dotSweepSequenceValueExpr [4, 5, 6], .num 7]),
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [1, 2, 3] [4, 5, 6])
  ] [
    .dotCall (.dotCall (resolve "Items") "filter" (some (alg [] [] [] [resolve "KeepCountThree"]))) "count" none,
    .dotCall (.call (resolve "filter") (alg [] [] [] [resolve "Items", resolve "KeepCountThree"])) "count" none,
    .dotCall (.dotCall (resolve "SequenceValue") "filter" (some (alg [] [] [] [resolve "KeepCountThree"]))) "count" none,
    .dotCall (.call (resolve "filter") (alg [] [] [] [resolve "SequenceValue", resolve "KeepCountThree"])) "count" none,
    .dotCall (.dotCall data0 "filter" (some (alg [] [] [] [resolve "IsLarge"]))) "count" none,
    .dotCall (.call (resolve "filter") (alg [] [] [] [data0, resolve "IsLarge"])) "count" none
  ])) with
  | Except.ok [2, 2, 0, 0, 2, 2] => true
  | _ => false

#guard sequenceBuiltinDotCallFilterSweep

def sequenceBuiltinDotCallReduceSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.block (algPrivate [] [] [
    ("AddItemCount", dotSweepAddTopLevelItemCountAlg),
    ("Add", dotSweepAddAlg),
    ("Items", alg [] [] [] [dotSweepSequenceValueExpr [1, 2, 3], .num 7]),
    ("SequenceValue", dotSweepSequenceValueAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [1, 2, 3] [4, 5, 6])
  ] [
    .dotCall (resolve "Items") "reduce" (some (alg [] [] [] [resolve "AddItemCount", .num 0])),
    .call (resolve "reduce") (alg [] [] [] [resolve "Items", resolve "AddItemCount", .num 0]),
    .dotCall (resolve "SequenceValue") "reduce" (some (alg [] [] [] [resolve "AddItemCount", .num 0])),
    .call (resolve "reduce") (alg [] [] [] [resolve "SequenceValue", resolve "AddItemCount", .num 0]),
    .dotCall data0 "reduce" (some (alg [] [] [] [resolve "Add", .num 0])),
    .call (resolve "reduce") (alg [] [] [] [data0, resolve "Add", .num 0])
  ])) with
  | Except.ok [4, 4, 3, 3, 6, 6] => true
  | _ => false

#guard sequenceBuiltinDotCallReduceSweep

--------------------------------------------------------------------------------
-- variadic user-parameter tests
--------------------------------------------------------------------------------

def variadicCollectAlg : Algorithm :=
  algWithParameters [{ name := "list", kind := .variadic }] [] [] [.param "list"]

def normalCollectAlg : Algorithm :=
  alg ["list"] [] [] [.param "list"]

-- Internal sequence `(10, 20, 30)...`: postfix spread over the constructed sequence value.
def sequenceSpread1230 : KatLang.Expr :=
  sequenceSpread (.sequenceConstruct (.sequenceConstruct (.num 10) (.num 20)) (.num 30))

def variadicSimpleRoot : Algorithm :=
  algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Collect", variadicCollectAlg)
  ] [
    .dotCall (.dotCall (resolve "Arg") "Collect" none) "count" none
  ]

def variadicDotCallCapturesTopLevelItems : Bool :=
  match runFlat (.block variadicSimpleRoot) with
  | Except.ok [3] => true
  | _ => false

#guard variadicDotCallCapturesTopLevelItems

def normalParameterStillPreservesBoundary : Bool :=
  match runFlat (.block (algPrivate [] [] [
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
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ]),
    ("Collect", variadicCollectAlg)
  ] [
    .dotCall (.dotCall (resolve "Arg") "Collect" none) "count" none,
    .dotCall (.call (resolve "atoms") (alg [] [] [] [.dotCall (resolve "Arg") "Collect" none])) "count" none
  ]

def variadicPreservesNestedSequenceValues : Bool :=
  match runFlat (.block variadicNestedSequenceValuesRoot) with
  | Except.ok [2, 4] => true
  | _ => false

#guard variadicPreservesNestedSequenceValues

def variadicScaleAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }, { name := "factor" }] [] [] [
    .dotCall (.param "values") "map" (some (alg [] [] [] [
      .block (alg ["n"] [] [] [.binary .mul (.param "n") (.param "factor")])
    ]))
  ]

def variadicTotalWithFeeAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }, { name := "fee" }] [] [] [
    .binary .add
      (.dotCall (.param "values") "sum" none)
      (.param "fee")
  ]

def variadicMeanAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }] [] [] [
    .binary .div
      (.dotCall (.param "values") "sum" none)
      (.dotCall (.param "values") "count" none)
  ]

def variadicCountAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }] [] [] [
    .dotCall (.param "values") "count" none
  ]

def variadicAtomsCountAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }] [] [] [
    .dotCall (.call (resolve "atoms") (alg [] [] [] [.param "values"])) "count" none
  ]

def ordinaryCountAlg : Algorithm :=
  alg ["list"] [] [] [
    .dotCall (.param "list") "count" none
  ]

def variadicMeanMatchesBuiltinSumCount : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Mean", variadicMeanAlg),
    ("Direct", alg [] [] [] [
      .binary .div
        (.dotCall (resolve "Arg") "sum" none)
        (.dotCall (resolve "Arg") "count" none)
    ])
  ] [
    .call (resolve "Mean") (alg [] [] [] [resolve "Arg"]),
    .dotCall (resolve "Arg") "Mean" none,
    resolve "Direct"
  ])) with
  | Except.ok [2, 2, 2] => true
  | _ => false

#guard variadicMeanMatchesBuiltinSumCount

def variadicNestedSequenceValuesAgreeWithBuiltinCountAndAtoms : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Arg", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ]),
    ("CountViaVariadic", variadicCountAlg),
    ("CountAtoms", variadicAtomsCountAlg)
  ] [
    .call (resolve "CountViaVariadic") (alg [] [] [] [resolve "Arg"]),
    .dotCall (resolve "Arg") "CountViaVariadic" none,
    .dotCall (resolve "Arg") "count" none,
    .call (resolve "CountAtoms") (alg [] [] [] [resolve "Arg"])
  ])) with
  | Except.ok [2, 2, 2, 4] => true
  | _ => false

#guard variadicNestedSequenceValuesAgreeWithBuiltinCountAndAtoms

def ordinaryAndVariadicCountStayStructurallyDifferent : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Ordinary", ordinaryCountAlg),
    ("Variadic", variadicCountAlg)
  ] [
    .dotCall (resolve "Arg") "Ordinary" none,
    .dotCall (resolve "Arg") "Variadic" none
  ])) with
  | Except.ok [3, 3] => true
  | _ => false

#guard ordinaryAndVariadicCountStayStructurallyDifferent

def variadicBeforeSuffixSupportsDotCall : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Scale", variadicScaleAlg)
  ] [
    .dotCall (resolve "Arg") "Scale" (some (alg [] [] [] [.num 10]))
  ])) with
  | Except.ok [10, 20, 30] => true
  | _ => false

#guard variadicBeforeSuffixSupportsDotCall

-- TotalWithFee(values..., fee) is a deconstruction parameter list. The inline
-- block receiver exposes its three top-level items (10, 20, 30), so with the
-- suffix the call supplies four items; the variadic captures [10, 20, 30] and
-- `fee` binds 5, giving sum 60 + 5 = 65.
def variadicInlineTupleDotCallWithSuffixCapturesReceiverItems : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (.block (alg [] [] [] [sequenceSpread1230]))
      "TotalWithFee" (some (alg [] [] [] [.num 5]))
  ])) with
  | Except.ok (.atom 65) => true
  | _ => false

#guard variadicInlineTupleDotCallWithSuffixCapturesReceiverItems

def variadicNamedMultiOutputDotCallWithSuffixStillWorks : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Data", alg [] [] [] [.num 10, .num 20, .num 30]),
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (resolve "Data") "TotalWithFee" (some (alg [] [] [] [.num 5]))
  ])) with
  | Except.ok [65] => true
  | _ => false

#guard variadicNamedMultiOutputDotCallWithSuffixStillWorks

-- The named multi-output receiver is one grouped argument whose captured value
-- is consumed by `values.sum`; the inline block spread receiver supplies three
-- exposed items. Both rows produce 65, but through distinct argument streams.
def variadicInlineTupleDotCallMatchesNamedReceiver : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Data", alg [] [] [] [.num 10, .num 20, .num 30]),
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (resolve "Data") "TotalWithFee" (some (alg [] [] [] [.num 5])),
    .dotCall (.block (alg [] [] [] [sequenceSpread1230]))
      "TotalWithFee" (some (alg [] [] [] [.num 5]))
  ])) with
  | Except.ok [65, 65] => true
  | _ => false

#guard variadicInlineTupleDotCallMatchesNamedReceiver

def variadicNestedInlineTupleDotCallPreservesSequenceValue : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("TotalWithFee", variadicTotalWithFeeAlg)
  ] [
    .dotCall (.block (alg [] [] [] [
      .block (alg [] [] [] [.num 10, .num 20, .num 30])
    ])) "TotalWithFee" (some (alg [] [] [] [.num 5]))
  ])) with
  | Except.ok (.atom 65) => true
  | _ => false

#guard variadicNestedInlineTupleDotCallPreservesSequenceValue

def ordinaryInlineTupleDotCallStillPreservesReceiverBoundary : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Collect", ordinaryCountAlg)
  ] [
    .dotCall (.block (alg [] [] [] [.num 10, .num 20, .num 30])) "Collect" none
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard ordinaryInlineTupleDotCallStillPreservesReceiverBoundary

def sequenceBuiltinInlineTupleDotCallBehaviorUnchanged : Bool :=
  let inlineSum :=
    .dotCall (.block (alg [] [] [] [.num 10, .num 20, .num 30])) "sum" none
  let nestedSum :=
    .dotCall (.block (alg [] [] [] [
      .block (alg [] [] [] [.num 10, .num 20, .num 30])
    ])) "sum" none
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

-- Internal sequence `(Arg....Scale(10), Arg.map{n * 10})...`: a postfix spread
-- over the constructed result of the variadic-scale dot-call and the builtin map,
-- spreading the concatenated results.
def variadicScaleMatchesBuiltinMap : Bool :=
  let builtinMap := .dotCall (resolve "Arg") "map" (some (alg [] [] [] [
    .block (alg ["n"] [] [] [.binary .mul (.param "n") (.num 10)])
  ]))
  match runFlat (.block (algPrivate [] [] [
    ("Arg", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("Scale", variadicScaleAlg)
  ] [
    sequenceSpread
      (.sequenceConstruct
        (.dotCall (resolve "Arg") "Scale" (some (alg [] [] [] [.num 10])))
        builtinMap)
  ])) with
  | Except.ok [10, 20, 30, 10, 20, 30] => true
  | _ => false

#guard variadicScaleMatchesBuiltinMap

def variadicBindingErrorRoot : Algorithm :=
  algPrivate [] [] [
    ("F", algWithParameters [{ name := "first" }, { name := "rest", kind := .variadic }, { name := "last" }] [] [] [
      .param "first", .param "rest", .param "last"
    ])
  ] [
    .call (resolve "F") (alg [] [] [] [.num 1])
  ]

def variadicBindingErrorWhenNormalParamsCannotBind : Bool :=
  -- F(first, rest..., last) is a deconstruction parameter list. F(1) supplies one
  -- scalar item, which is not opened (rule 5); the matcher needs at least the two
  -- fixed bindings (first, last), so it reports arityMismatch 2 1.
  match runResult (.block variadicBindingErrorRoot) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | Except.ok _ => false

#guard variadicBindingErrorWhenNormalParamsCannotBind

def sequenceValueVariadicCountAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [.capture { name := "xs", kind := .variadic }]] [] [] [
    .dotCall (.param "xs") "count" none
  ]

def sequenceValueVariadicFirstAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [.capture { name := "xs", kind := .variadic }]] [] [] [
    .index (.param "xs") (.num 0)
  ]

def sequenceValueVariadicMixedAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "xs", kind := .variadic }],
    .capture { name := "a" },
    .capture { name := "b" }
  ] [] [] [
    .dotCall (.param "xs") "count" none,
    .param "a",
    .param "b"
  ]

def sequenceValueVariadicCapturesImmediateSequenceValueItems : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", sequenceValueVariadicCountAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3])
    ])
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard sequenceValueVariadicCapturesImmediateSequenceValueItems

def sequenceValueVariadicRemovesOnlyOneSequenceValueBoundary : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", sequenceValueVariadicCountAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2]),
        .num 3
      ])
    ])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceValueVariadicRemovesOnlyOneSequenceValueBoundary

def sequenceValueVariadicPreservesNestedSequenceValueItem : Bool :=
  match runResult (.block (algPrivate [] [] [("F", sequenceValueVariadicFirstAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2]),
        .num 3
      ])
    ])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValueVariadicPreservesNestedSequenceValueItem

def sequenceValueVariadicRequiresSequenceValueSlot : Bool :=
  match runResult (.block (algPrivate [] [] [("F", sequenceValueVariadicCountAlg)] [
    .call (resolve "F") (alg [] [] [] [.num 1, .num 2, .num 3])
  ])) with
  | Except.error err => innermostIsArityMismatch 1 3 err
  | Except.ok _ => false

#guard sequenceValueVariadicRequiresSequenceValueSlot

def sequenceValueVariadicWithMixedTopLevelParameters : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", sequenceValueVariadicMixedAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3]),
      .num 4,
      .num 5
    ])
  ])) with
  | Except.ok [3, 4, 5] => true
  | _ => false

#guard sequenceValueVariadicWithMixedTopLevelParameters

def sequenceValueSeparateVariadicsDifferentLevelsAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "inner", kind := .variadic }],
    .capture { name := "outer", kind := .variadic }
  ] [] [] [
    .dotCall (.param "inner") "count" none,
    .dotCall (.param "outer") "count" none
  ]

def sequenceValueSeparateVariadicsDifferentLevelsBindIndependently : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", sequenceValueSeparateVariadicsDifferentLevelsAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .num 3,
      .num 4
    ])
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard sequenceValueSeparateVariadicsDifferentLevelsBindIndependently

def sequenceValueHeadTailAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "head" },
      .capture { name := "tail", kind := .variadic }
    ]
  ] [] [] [
    .param "head",
    .dotCall (.param "tail") "count" none
  ]

def sequenceValueHeadTailPatternBindsWithinOneSlot : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", sequenceValueHeadTailAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4])
    ])
  ])) with
  | Except.ok [1, 3] => true
  | _ => false

#guard sequenceValueHeadTailPatternBindsWithinOneSlot

def sequenceValueFirstMiddleLastAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "first" },
      .capture { name := "middle", kind := .variadic },
      .capture { name := "last" }
    ]
  ] [] [] [
    .param "first",
    .dotCall (.param "middle") "count" none,
    .param "last"
  ]

def sequenceValueFirstMiddleLastPatternBindsWithinOneSlot : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", sequenceValueFirstMiddleLastAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])
    ])
  ])) with
  | Except.ok [1, 3, 5] => true
  | _ => false

#guard sequenceValueFirstMiddleLastPatternBindsWithinOneSlot

def sequenceValueVariadicWithSuffixInsideSequenceValueAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "history", kind := .variadic },
      .capture { name := "pre2" }
    ],
    .capture { name := "pre1" }
  ] [] [] [
    .dotCall (.param "history") "count" none,
    .param "pre2",
    .param "pre1"
  ]

def sequenceValueVariadicWithSuffixInsideSequenceValueBindsWithinOneSlot : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", sequenceValueVariadicWithSuffixInsideSequenceValueAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3]),
      .num 4
    ])
  ])) with
  | Except.ok [2, 3, 4] => true
  | _ => false

#guard sequenceValueVariadicWithSuffixInsideSequenceValueBindsWithinOneSlot

def sequenceValueVariadicWithSuffixInsideSequenceValueRequiresSuffixValue : Bool :=
  match runResult (.block (algPrivate [] [] [("F", sequenceValueVariadicWithSuffixInsideSequenceValueAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] []),
      .num 4
    ])
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard sequenceValueVariadicWithSuffixInsideSequenceValueRequiresSuffixValue

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
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [.num 5]),
    ("F", sequenceValuePairFirstAlg)
  ] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.resolve "A"]),
        .num 6
      ])
    ])
  ])) with
  | Except.ok (.atom 5) => true
  | _ => false

#guard sequenceValuePatternParenScalarPropertyItemIsNotOrphan

/-- Regression: `F(((A), 6))` with `A = (1, 2)`. The grouped property reference
    supplies the canonical `(1, 2)` as one item -- not an orphan `((1, 2))`. -/
def sequenceValuePatternParenSequencePropertyItemStaysCanonical : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("F", sequenceValuePairFirstAlg)
  ] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.resolve "A"]),
        .num 6
      ])
    ])
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard sequenceValuePatternParenSequencePropertyItemStaysCanonical

/-- Regression: `F(((), 6))`. A non-spread `()` item is one visible item,
    exactly as in ordinary sequence-value construction, so the pattern sees
    `((), 6)` and binds `x` to the empty sequence value. -/
def sequenceValuePatternEmptySequenceSiblingItemIsPreserved : Bool :=
  match runResult (.block (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [
        .emptySequence 0,
        .num 6
      ])
    ])
  ])) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard sequenceValuePatternEmptySequenceSiblingItemIsPreserved

/-- Regression: only an explicit spread contributes zero items. `F((E..., 6))`
    with `E = ()` spreads away the empty value, so the pattern sees the single
    item `6`. -/
def sequenceValuePatternSpreadOfEmptyStillContributesNoItems : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("E", alg [] [] [] [.emptySequence 0]),
    ("F", sequenceValueVariadicCountAlg)
  ] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [
        .sequenceSpread (.resolve "E"),
        .num 6
      ])
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard sequenceValuePatternSpreadOfEmptyStillContributesNoItems

/-- Regression: `F(((1, 2)))` with `F((x, y)) = x`. The inline-written argument
    `((1, 2))` is one written grouping level around the canonical item
    `(1, 2)`, so the pattern receives exactly ONE written slot and reports
    `arityMismatch 2 1`. Written slots stay authoritative for inline-written
    pattern arguments: binding neither mints an orphan `((1, 2))` nor silently
    opens the single written item. -/
def sequenceValuePatternLiteralWrappedPairReportsWrittenSlotArity : Bool :=
  match runResult (.block (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2])
      ])
    ])
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | Except.ok _ => false

#guard sequenceValuePatternLiteralWrappedPairReportsWrittenSlotArity

/-- Regression: redundant grouping depth canonicalizes away shallowly at each
    level, so `F((((1, 2))))` still writes exactly one slot -- the canonical
    `(1, 2)` -- and reports the same `arityMismatch 2 1`. -/
def sequenceValuePatternDeeplyWrappedPairReportsWrittenSlotArity : Bool :=
  match runResult (.block (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [
          .block (alg [] [] [] [.num 1, .num 2])
        ])
      ])
    ])
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | Except.ok _ => false

#guard sequenceValuePatternDeeplyWrappedPairReportsWrittenSlotArity

/-- Regression: `A = ((1, 2))` canonicalizes at property construction to
    `(1, 2)`; `F(A)` then opens the stored canonical sequence value for the
    pattern, so `F((x, y)) = x` binds `x = 1`. No hidden orphan `((1, 2))`
    distinguishes the stored value from the writable literal `(1, 2)`. -/
def sequenceValuePatternPropertyStoredWrappedPairOpensCanonically : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2])]),
    ("F", sequenceValuePairFirstAlg)
  ] [
    .call (resolve "F") (alg [] [] [] [.resolve "A"])
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
  match runResult (.block (algPrivate [] [] [("F", sequenceValuePairFirstWithFixedSuffixAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2])
      ]),
      .num 3
    ])
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
  match runResult (.block (algPrivate [] [] [("F", sequenceValueSingleCaptureAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2])
      ])
    ])
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
  match runFlat (.block (algPrivate [] [] [("F", sequenceValueSingleCaptureCountAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2])
      ])
    ])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceValuePatternSingleCaptureWrappedPairCountsItems

/-- Guard: the shallow combiner never drops empty-sequence siblings.
    `F(((), ()))` writes two items, so the pair pattern binds both empties
    positionally and `x` is the real empty sequence value. -/
def sequenceValuePatternTwoEmptySiblingItemsBindPositionally : Bool :=
  match runResult (.block (algPrivate [] [] [("F", sequenceValuePairFirstAlg)] [
    .call (resolve "F") (alg [] [] [] [
      .block (alg [] [] [] [.emptySequence 0, .emptySequence 0])
    ])
  ])) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard sequenceValuePatternTwoEmptySiblingItemsBindPositionally

def sequenceValueVariadicIsNotTopLevelVariadic : Bool :=
  let sequenceValueCall :=
    runFlat (.block (algPrivate [] [] [("F", algWithParameterPatterns [
      .sequenceValue [.capture { name := "xs", kind := .variadic }], .capture { name := "y" }
    ] [] [] [
      .dotCall (.param "xs") "count" none,
      .param "y"
    ])] [
      .call (resolve "F") (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2]),
        .num 3
      ])
    ]))
  let flatCall :=
    runResult (.block (algPrivate [] [] [("F", algWithParameterPatterns [
      .sequenceValue [.capture { name := "xs", kind := .variadic }], .capture { name := "y" }
    ] [] [] [
      .dotCall (.param "xs") "count" none,
      .param "y"
    ])] [
      .call (resolve "F") (alg [] [] [] [.num 1, .num 2, .num 3])
    ]))
  match sequenceValueCall, flatCall with
  | Except.ok [2, 3], Except.error err => innermostIsArityMismatch 2 3 err
  | _, _ => false

#guard sequenceValueVariadicIsNotTopLevelVariadic

-- Source `Step((history...), previous) = (history..., previous + 1), previous + 1`,
-- matching the C# regression `Eval_LoopStep_SequenceValueCommaHistorySlotUsesExplicitSpreadAcrossRepeat`.
-- The first output slot is the written sequence value `(history..., previous + 1)`:
-- a block whose comma outputs are `history...` (an explicit spread opening the
-- captured history one level) and `previous + 1`. The written spread splices its
-- items before the sibling slot — the same `(A..., 99)` = `(1, 2, 99)` rule as
-- every written sequence value — so the history slot GROWS FLAT by one item per
-- step. Starting from `(1, 2)` and stepping twice, `:0` selects the flat
-- `(1, 2, 3, 4)`. To deepen instead of flattening, write the history as a
-- non-spread item: `(history, previous + 1)`.
-- (Before the July 2026 alignment fix, `evalAlgOutputCore` kept a non-empty
-- spread output slot grouped as one un-expanded slot, so this program nested to
-- `(((1, 2), 3), 4)` — diverging from `evalAlgOutputCountedCore`, from the C#
-- evaluator, and from written-sequence spread semantics. This guard pins the
-- aligned flat behavior at the exact structural level.)
def sequenceValueVariadicLoopStepSpreadGrowsHistoryFlat : Bool :=
  let step := algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .variadic }],
    .capture { name := "previous" }
  ] [] [] [
    .block (alg [] [] [] [sequenceSpread (.param "history"), .binary .add (.param "previous") (.num 1)]),
    .binary .add (.param "previous") (.num 1)
  ]
  match runResult (.block (algPrivate [] [] [("Step", step)] [
    .index
      (.dotCall (resolve "Step") "repeat" (some (alg [] [] [] [
        .num 2,
        .block (alg [] [] [] [.num 1, .num 2]),
        .num 2
      ])))
      (.num 0)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3, .atom 4]) => true
  | _ => false

#guard sequenceValueVariadicLoopStepSpreadGrowsHistoryFlat

-- Source `Step((history..., previous), current) = (history..., current), current`.
-- Same shape as `sequenceValueVariadicLoopStepSpreadGrowsHistoryFlat`: the first output
-- slot is the sequence-value pair `(history..., current)` — a block whose comma outputs are
-- `history...` (sequence-spread) and `current` — so it is one next-state slot.
-- (Contrast a spread over `sequenceConstruct history current`, which is a different shape.)
def sequenceValueVariadicLoopStepWithSuffixInsideSequenceValuePreservesStateShape : Bool :=
  let step := algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "history", kind := .variadic },
      .capture { name := "previous" }
    ],
    .capture { name := "current" }
  ] [] [] [
    .block (alg [] [] [] [sequenceSpread (.param "history"), .param "current"]),
    .param "current"
  ]
  -- Exact structural check. Here the sequence-value pattern `(history..., previous)`
  -- DESTRUCTURES the slot `(1, 2)` into atoms — history captures the leading atom
  -- `1` and `previous` the trailing `2` — so `history...` spreads a bare atom, not
  -- a nested sequence value. The next slot is therefore the FLAT pair `(1, 3)`, and it stays
  -- flat across iterations (dropping the previous `previous`, unlike the
  -- variadic-only `(history...)` capture in
  -- `sequenceValueVariadicLoopStepSpreadGrowsHistoryFlat`, which accumulates).
  -- Asserting the exact `Result` pins this flat shape.
  match runResult (.block (algPrivate [] [] [("Step", step)] [
    .index
      (.dotCall (resolve "Step") "repeat" (some (alg [] [] [] [
        .num 2,
        .block (alg [] [] [] [.num 1, .num 2]),
        .num 3
      ])))
      (.num 0)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 3]) => true
  | _ => false

#guard sequenceValueVariadicLoopStepWithSuffixInsideSequenceValuePreservesStateShape

def loopVariadicHistoryLastExpr : KatLang.Expr :=
  .dotCall (.call (resolve "atoms") (alg [] [] [] [.param "history"])) "last" none

def loopVariadicNextExpr : KatLang.Expr :=
  .binary .add loopVariadicHistoryLastExpr (.num 1)

def loopVariadicAppendNextAlg : Algorithm :=
  algWithParameters [{ name := "history", kind := .variadic }] [] [] [
    .sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr
  ]

def loopVariadicContinueFlagExpr : KatLang.Expr :=
  .call (resolve "if") (alg [] [] [] [
    .binary .lt loopVariadicNextExpr (.num 6),
    .num 1,
    .num 0
  ])

def loopVariadicWhileAppendNextAlg : Algorithm :=
  algWithParameters [{ name := "history", kind := .variadic }] [] [] [
    .sequenceConstruct
      (.sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr)
      loopVariadicContinueFlagExpr
  ]

def loopVariadicInitialState : Algorithm :=
  alg [] [] [] [.num 1, .num 2, .num 4]

def variadicLoopStepRepeatOneIterationCapturesStateItems : Bool :=
  match runResult (.block (algPrivate [] [] [("Step", loopVariadicAppendNextAlg)] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [
      .num 1,
      sequenceItems [.num 1, .num 2, .num 4]
    ]))
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5]) => true
  | _ => false

#guard variadicLoopStepRepeatOneIterationCapturesStateItems

def variadicLoopStepRepeatTwoIterationsKeepsExpandedState : Bool :=
  match runResult (.block (algPrivate [] [] [("Step", loopVariadicAppendNextAlg)] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [
      .num 2,
      sequenceItems [.num 1, .num 2, .num 4]
    ]))
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5, .atom 6]) => true
  | _ => false

#guard variadicLoopStepRepeatTwoIterationsKeepsExpandedState

def variadicLoopStepWhileUsesExpandedState : Bool :=
  match runResult (.block (algPrivate [] [] [("Step", loopVariadicWhileAppendNextAlg)] [
    .dotCall (resolve "Step") "while" (some (alg [] [] [] [
      sequenceItems [.num 1, .num 2, .num 4]
    ]))
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard variadicLoopStepWhileUsesExpandedState

def sequenceBuiltinDotCallVariadicRepeatReceiverTakeUsesFinalStateSlots : Bool :=
  match runFlat (.block (algPrivate [] [] [("Step", loopVariadicAppendNextAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some (alg [] [] [] [
        .num 3,
        sequenceItems [.num 1, .num 2, .num 4]
      ])))
      "take"
      (some (alg [] [] [] [.num 5]))
  ])) with
  | Except.ok [1, 2, 4, 5, 6] => true
  | _ => false

#guard sequenceBuiltinDotCallVariadicRepeatReceiverTakeUsesFinalStateSlots

-- Aspect 2 loop-state variadic binding (mirrors C# EvaluatorTests.Eval_VariadicLoopStep_*).
-- A top-level variadic loop interface binds state as an item supply: the fixed prefix
-- and suffix bind from the ends, and the rest captures the remaining middle state slots
-- as one grouped value. The structural minimum is the parameter count (so 2 slots fail
-- for first/middle.../last) and the max is unbounded (extra middle slots are accepted).
-- This is the loop counterpart to the normal user-call path, where the rest may be empty.
def loopVariadicPrefixMiddleSuffixAlg : Algorithm :=
  algWithParameters [
    { name := "first" },
    { name := "middle", kind := .variadic },
    { name := "last" }
  ] [] [] [
    .param "first",
    .dotCall (.param "middle") "count" none,
    .param "last"
  ]

def loopVariadicPrefixMiddleSuffixIncrementAlg : Algorithm :=
  algWithParameters [
    { name := "first" },
    { name := "middle", kind := .variadic },
    { name := "last" }
  ] [] [] [
    .binary .add (.param "first") (.num 1),
    sequenceSpread (.param "middle"),
    .binary .add (.param "last") (.num 1)
  ]

-- Extra middle: 4 state slots bind first=10/last=40 from the ends, middle = (20, 30)
-- (count 2). Mirrors C# Eval_VariadicLoopStep_WithPrefixMiddleSuffix_PreservesDeclarationOrderBindings.
def variadicLoopStepCapturesExtraMiddleStateSlots : Bool :=
  match runFlat (.block (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixAlg)] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [.num 1, .num 10, .num 20, .num 30, .num 40]))
  ])) with
  | Except.ok [10, 2, 40] => true
  | _ => false

#guard variadicLoopStepCapturesExtraMiddleStateSlots

-- Exact structural count: 3 state slots bind first=10/last=30 and middle = (20) (count 1).
def variadicLoopStepExactStructuralCountBinds : Bool :=
  match runFlat (.block (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixAlg)] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [.num 1, .num 10, .num 20, .num 30]))
  ])) with
  | Except.ok [10, 1, 30] => true
  | _ => false

#guard variadicLoopStepExactStructuralCountBinds

-- Structural-minimum failure: only 2 state slots cannot satisfy first + middle + last;
-- the loop requires at least the structural parameter count (3), so this is arityMismatch 3 2.
def variadicLoopStepBelowStructuralMinimumFails : Bool :=
  match runResult (.block (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixAlg)] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [.num 1, .num 10, .num 20]))
  ])) with
  | Except.error err => innermostIsArityMismatch 3 2 err
  | _ => false

#guard variadicLoopStepBelowStructuralMinimumFails

-- The exact reviewed case: Step(first, middle..., last) = first + 1, middle..., last + 1
-- with Step.repeat(2, 0, 5, 5, 10) binds first=0, middle=(5, 5), last=10 and, after two
-- iterations, yields 2, 5, 5, 12 (previously rejected by Lean as arityMismatch 3 4).
def variadicLoopStepExtraMiddleRepeatsTwice : Bool :=
  match runFlat (.block (algPrivate [] [] [("Step", loopVariadicPrefixMiddleSuffixIncrementAlg)] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [.num 2, .num 0, .num 5, .num 5, .num 10]))
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
    .block (alg [] [] [] [.param "x", .binary .add (.param "x") (.num 1)])
  ]

def loopBoundarySequenceValueWhileStepAlg : Algorithm :=
  alg ["x"] [] [] [
    .block (alg [] [] [] [.param "x", .binary .add (.param "x") (.num 1)]),
    .num 0
  ]

def sequenceBuiltinDotCallRepeatReceiverTakeUsesFinalStateSlots : Bool :=
  match runFlat (.block (algPrivate [] [] [("Step", loopBoundaryPairStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some (alg [] [] [] [
        .num 1,
        .num 1,
        .num 2
      ])))
      "take"
      (some (alg [] [] [] [.num 1]))
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallRepeatReceiverTakeUsesFinalStateSlots

def sequenceBuiltinDotCallRepeatReceiverCountUsesFinalStateSlots : Bool :=
  match runFlat (.block (algPrivate [] [] [("Step", loopBoundaryPairStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some (alg [] [] [] [
        .num 1,
        .num 1,
        .num 2
      ])))
      "count"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallRepeatReceiverCountUsesFinalStateSlots

def sequenceBuiltinDotCallRepeatSequenceValueStateCountsOneItem : Bool :=
  match runFlat (.block (algPrivate [] [] [("Step", loopBoundarySequenceValueRepeatStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "repeat" (some (alg [] [] [] [
        .num 1,
        .num 1
      ])))
      "count"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallRepeatSequenceValueStateCountsOneItem

def sequenceBuiltinDotCallWhileReceiverTakeUsesFinalStateSlots : Bool :=
  match runFlat (.block (algPrivate [] [] [("Step", loopBoundaryPairWhileStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "while" (some (alg [] [] [] [
        .num 0,
        .num 0
      ])))
      "take"
      (some (alg [] [] [] [.num 1]))
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallWhileReceiverTakeUsesFinalStateSlots

def sequenceBuiltinDotCallWhileReceiverCountUsesFinalStateSlots : Bool :=
  match runFlat (.block (algPrivate [] [] [("Step", loopBoundaryPairWhileStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "while" (some (alg [] [] [] [
        .num 0,
        .num 0
      ])))
      "count"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceBuiltinDotCallWhileReceiverCountUsesFinalStateSlots

def sequenceBuiltinDotCallWhileSequenceValueStateCountsOneItem : Bool :=
  match runFlat (.block (algPrivate [] [] [("Step", loopBoundarySequenceValueWhileStepAlg)] [
    .dotCall
      (.dotCall (resolve "Step") "while" (some (alg [] [] [] [
        .num 1
      ])))
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
  algWithParameters [{ name := "values", kind := .variadic }] [] [] [.param "values"]

def loopBoundarySequenceValueHistoryStepAlg : Algorithm :=
  alg ["history"] [] [] [
    .block (alg [] [] [] [
      .sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr
    ])
  ]

def loopBoundarySpreadHistoryStepAlg : Algorithm :=
  alg ["history"] [] [] [
    .sequenceConstruct (sequenceSpread (.param "history")) loopVariadicNextExpr
  ]

def loopInitialManyExplicitArgsCreateManySlots : Bool :=
  match runResult (.block (algPrivate [] [] [("Step", loopBoundaryPairStepAlg)] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [.num 1, .num 1, .num 2]))
  ])) with
  | Except.ok (.sequenceValue [.atom 2, .atom 3]) => true
  | _ => false

#guard loopInitialManyExplicitArgsCreateManySlots

-- A rest-only variadic loop step binds many separate init slots as its item supply
-- (Aspect 2: matches C#). Step(values...) = values with repeat(1, 1, 2, 3) captures
-- values = (1, 2, 3) rather than rejecting the extra slots as the old strict path did.
def loopInitialExplicitVariadicStepCapturesManySlots : Bool :=
  match runResult (.block (algPrivate [] [] [("Step", loopBoundaryVariadicIdentityAlg)] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [.num 1, .num 1, .num 2, .num 3]))
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]) => true
  | _ => false

#guard loopInitialExplicitVariadicStepCapturesManySlots

def loopInitialSequenceValuePropertyArgIsOneSlot : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Step", loopBoundaryIdentityAlg),
    ("List", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [.num 1, resolve "List"]))
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4]) => true
  | _ => false

#guard loopInitialSequenceValuePropertyArgIsOneSlot

def loopInitialSequenceValueArgDoesNotSatisfyTwoOrdinaryParams : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Step", loopBoundarySumPairStepAlg),
    ("Pair", alg [] [] [] [.num 1, .num 2])
  ] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [.num 1, resolve "Pair"]))
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | _ => false

#guard loopInitialSequenceValueArgDoesNotSatisfyTwoOrdinaryParams

def loopInitialExplicitSelectionsSplitSequenceValueArg : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Step", loopBoundarySumPairStepAlg),
    ("Pair", alg [] [] [] [.num 1, .num 2])
  ] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [
      .num 1,
      .index (resolve "Pair") (.num 0),
      .index (resolve "Pair") (.num 1)
    ]))
  ])) with
  | Except.ok (.atom 3) => true
  | _ => false

#guard loopInitialExplicitSelectionsSplitSequenceValueArg

def loopInitialSequenceValueHistorySlotCanBePreservedAcrossRepeat : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Step", loopBoundarySequenceValueHistoryStepAlg),
    ("List", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [.num 2, resolve "List"]))
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5, .atom 6]) => true
  | _ => false

#guard loopInitialSequenceValueHistorySlotCanBePreservedAcrossRepeat

def loopInitialSpreadStepOutputStillBecomesNextStateSlots : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Step", loopBoundarySpreadHistoryStepAlg),
    ("List", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [.num 2, resolve "List"]))
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4, .atom 5, .atom 6]) => true
  | _ => false

#guard loopInitialSpreadStepOutputStillBecomesNextStateSlots

def loopInitialMultiOutputPropertyArgIsOneSlot : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Step", loopBoundaryIdentityAlg),
    ("Values", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [.num 1, resolve "Values"]))
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4]) => true
  | _ => false

#guard loopInitialMultiOutputPropertyArgIsOneSlot

-- Explicit selections that split a multi-output property into separate init slots are
-- bound by the rest-only variadic step as its item supply (Aspect 2: matches C#), so the
-- three split slots are captured as values = (1, 2, 4) instead of being rejected.
def loopInitialExplicitSelectionsSplitMultiOutputProperty : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Step", loopBoundaryVariadicIdentityAlg),
    ("Values", alg [] [] [] [.num 1, .num 2, .num 4])
  ] [
    .dotCall (resolve "Step") "repeat" (some (alg [] [] [] [
      .num 1,
      .index (resolve "Values") (.num 0),
      .index (resolve "Values") (.num 1),
      .index (resolve "Values") (.num 2)
    ]))
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 4]) => true
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
  match runFlat (.block (algPrivate [] [] [("F", valueAccessConditionalAlg)] [
    .call (resolve "F") (alg [] [] [] [.num 0]),
    .call (resolve "F") (alg [] [] [] [.num 7])
  ])) with
  | Except.ok [0, 1] => true
  | _ => false

#guard conditionalDirectCallStillSelectsBranch

-- Bare property-style reference must raise noMatchingBranch, not return a
-- silently cached empty sequence value.
def bareConditionalPropertyReferenceFails : Bool :=
  match runResult (.block (algPrivate [] [] [("F", valueAccessConditionalAlg)] [
    resolve "F"
  ])) with
  | Except.error err => innermostIsNoMatchingBranch "F" err
  | _ => false

#guard bareConditionalPropertyReferenceFails

-- Dot-call access without arguments agrees with the bare reference.
def dotCallConditionalWithoutArgsFails : Bool :=
  match runResult (.dotCall (.block (algPrivate [] [] [
    ("F", valueAccessConditionalAlg)
  ] [.num 0])) "F" none) with
  | Except.error err => innermostIsNoMatchingBranch "F" err
  | _ => false

#guard dotCallConditionalWithoutArgsFails

-- Forcing a conditional through a sequence-builtin collection argument also
-- fails instead of silently contributing nothing.
def conditionalCollectionArgumentFails : Bool :=
  match runResult (.block (algPrivate [] [] [("F", valueAccessConditionalAlg)] [
    .call (resolve "sum") (alg [] [] [] [resolve "F"])
  ])) with
  | Except.error err => innermostIsNoMatchingBranch "conditional" err
  | _ => false

#guard conditionalCollectionArgumentFails

-- A conditional bound as a higher-order argument fails when referenced as a
-- bare zero-argument thunk inside the callee body.
def conditionalHigherOrderThunkReferenceFails : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("F", valueAccessConditionalAlg),
    ("Apply", alg ["f"] [] [] [.param "f"])
  ] [
    .call (resolve "Apply") (alg [] [] [] [resolve "F"])
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
  match runFlat (.block (algPrivate [] [] [("G", singletonSequenceValueConditionalAlg)] [
    .call (resolve "G") (alg [] [] [] [.num 0]),
    .call (resolve "G") (alg [] [] [] [.num 5])
  ])) with
  | Except.ok [100, 5] => true
  | _ => false

#guard singletonSequenceValuePatternMatchesDirectCall

-- The same conditional must accept the same shapes through map callbacks.
def singletonSequenceValuePatternMatchesMapCallback : Bool :=
  match runFlat (.block (algPrivate [] [] [("G", singletonSequenceValueConditionalAlg)] [
    .call (resolve "map") (alg [] [] [] [sequenceItems [.num 0, .num 5], resolve "G"])
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
  match runFlat (.block (algPrivate [] [] [("H", pairFirst)] [
    .call (resolve "H") (alg [] [] [] [.num 9])
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard multiMemberSequenceValuePatternStillRejectsScalars

--------------------------------------------------------------------------------
-- Dot-call receiver symmetry for user-defined leading flat variadic callees
--------------------------------------------------------------------------------
-- The ordinary dot-call receiver is ONE leading argument slot, and dot-call
-- matches the equivalent canonical call:
--   receiver.F(args...)      == F(receiver, args...)
--   (receiver...).F(args...) == F(receiver..., args...)
-- Explicit receiver spread spreads the receiver's emitted top-level values.
-- A sequence-valued property such as `Pair = (10, 20)` emits ONE sequence value, so
-- even its spread spreads one sequence value (spread preserves named
-- sequence-value operand boundaries); a multi-output property such as
-- `Values = 10, 20` emits two values, which is where ordinary-receiver slot
-- allocation and explicit spread become observably different.

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

-- NItems(values...) = values.count
def receiverSymmetryNItemsAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }] [] []
    [.dotCall (.param "values") "count" none]

-- BeforeLastCount(values..., last) = values.count
def receiverSymmetryBeforeLastCountAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }, { name := "last" }] [] []
    [.dotCall (.param "values") "count" none]

-- SumPlusLast(values..., last) = values.sum + last
def receiverSymmetrySumAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }, { name := "last" }] [] []
    [.binary .add (.dotCall (.param "values") "sum" none) (.param "last")]

-- Pair = (10, 20): one sequence value.
def sequenceValuePairReceiverProp : Prod String Algorithm :=
  ("Pair", alg [] [] [] [.block (alg [] [] [] [.num 10, .num 20])])

-- Values = 10, 20: two emitted top-level values.
def multiOutputValuesReceiverProp : Prod String Algorithm :=
  ("Values", alg [] [] [] [.num 10, .num 20])

def runReceiverSymmetryCase (receiverProp calleeProp : Prod String Algorithm)
    (out : KatLang.Expr) : Except Error (List Int) :=
  runFlat (.block (algPrivate [] [] [receiverProp, calleeProp] [out]))

-- Pair normalizes to the two-item sequence it contains; ordinary receiver and
-- canonical call agree on that one sequence-valued slot.
def sequenceValueReceiverLeadingVariadicIsOneSlot : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (resolve "Pair") "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") (alg [] [] [] [resolve "Pair"]))) [2]

#guard sequenceValueReceiverLeadingVariadicIsOneSlot

-- Pair... spreads two slots; rest-only `NItems(values...)` consumes an item
-- supply, so it binds those two slots into one sequence value of count 2.
def sequenceValueReceiverSpreadFeedsItemSupply : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Pair")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") (alg [] [] [] [sequenceSpread (resolve "Pair")]))) [2]

#guard sequenceValueReceiverSpreadFeedsItemSupply

-- BeforeLastCount(values..., last) binds the supplied item supply:
-- Pair.BeforeLastCount(99) and the canonical call pass one sequence-valued slot
-- plus the suffix; the spread forms open Pair before suffix allocation. All four
-- forms agree on a variadic capture whose collection count is 2.
def sequenceValueReceiverWithSuffixMatchesCanonicalCalls : Bool :=
  let callee := ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg)
  let suffixArgs := alg [] [] [] [.num 99]
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (resolve "Pair") "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") (alg [] [] [] [resolve "Pair", .num 99]))) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Pair")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") (alg [] [] [] [sequenceSpread (resolve "Pair"), .num 99]))) [2]

#guard sequenceValueReceiverWithSuffixMatchesCanonicalCalls

-- Values emits two top-level values. Rest-only `NItems(values...)` consumes an
-- item supply, so the ordinary forms (one sequence-valued slot) and the explicit
-- spread forms (two slots) all bind to a sequence value of count 2.
def multiOutputReceiverCountsMatchCanonicalCalls : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") (alg [] [] [] [resolve "Values"]))) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") (alg [] [] [] [sequenceSpread (resolve "Values")]))) [2]

#guard multiOutputReceiverCountsMatchCanonicalCalls

-- BeforeLastCount(values..., last) binds the supplied item supply. The ordinary
-- and canonical forms pass one sequence-valued slot plus the suffix; the spread
-- forms open Values before suffix allocation. All four agree on 2.
def multiOutputReceiverWithSuffixMatchesCanonicalCalls : Bool :=
  let callee := ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg)
  let suffixArgs := alg [] [] [] [.num 99]
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") (alg [] [] [] [resolve "Values", .num 99]))) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") (alg [] [] [] [sequenceSpread (resolve "Values"), .num 99]))) [2]

#guard multiOutputReceiverWithSuffixMatchesCanonicalCalls

-- SumPlusLast(values..., last) with no extra argument receives exactly one
-- grouped sequence value, so `last` gets that value and the numeric body fails.
-- Explicit spread below is the successful path.
def ordinaryMultiOutputReceiverStaysOneSlotAtSuffixAllocation : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "SumPlusLast" none)) &&
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") (alg [] [] [] [resolve "Values"])))

#guard ordinaryMultiOutputReceiverStaysOneSlotAtSuffixAllocation

-- Explicit spread pre-expands before slot allocation: (Values...).SumPlusLast
-- spreads 10 and 20 as separate items, so `last` binds 20 and the variadic
-- captures [10]. The canonical call agrees.
def spreadMultiOutputReceiverPreExpandsBeforeSuffixAllocation : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "SumPlusLast" none)) [30] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") (alg [] [] [] [sequenceSpread (resolve "Values")]))) [30]

#guard spreadMultiOutputReceiverPreExpandsBeforeSuffixAllocation

-- A direct inline block receiver exposes its top-level output items.
def inlineBlockReceiverExposesTopLevelItemsToLeadingVariadic : Bool :=
  expectFlat (runFlat (.block (algPrivate [] [] [
    ("NItems", receiverSymmetryNItemsAlg)
  ] [
    .dotCall (.block (alg [] [] [] [.num 10, .num 20])) "NItems" none
  ]))) [2]

#guard inlineBlockReceiverExposesTopLevelItemsToLeadingVariadic

--------------------------------------------------------------------------------
-- Deconstruction parameter binding (movable rest, single grouped opening)
--------------------------------------------------------------------------------
-- F(x, y..., z) is a comma deconstruction parameter list (two or more captures
-- containing one rest), so the supplied item supply is matched prefix/rest/suffix
-- and a single grouped argument is opened element-by-element by rule 4.

def deconstructSumAlg : Algorithm :=
  algWithParameters [
    { name := "x" }, { name := "y", kind := .variadic }, { name := "z" }
  ] [] [] [
    .binary .add (.binary .add (.param "x") (.dotCall (.param "y") "sum" none)) (.param "z")
  ]

def deconstructFiveArg : Algorithm :=
  alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5]

-- F(1, 2, 3, 4, 5): five direct item slots.
def deconstructionDirectItemSupply : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", deconstructSumAlg)] [
    .call (resolve "F") deconstructFiveArg
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard deconstructionDirectItemSupply

-- F(A) where A = 1, 2, 3, 4, 5: one sequence-valued argument is supplied.
-- Function-call binding does not implicitly open it, so the mixed fixed/rest
-- shape is under-supplied.
def deconstructionSingleGroupedArgumentRequiresSpread : Bool :=
  match runFlat (.block (algPrivate [] [] [("A", deconstructFiveArg), ("F", deconstructSumAlg)] [
    .call (resolve "F") (alg [] [] [] [resolve "A"])
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | _ => false

#guard deconstructionSingleGroupedArgumentRequiresSpread

-- F(A...): explicit spread supplies five slots.
def deconstructionSpreadArgument : Bool :=
  match runFlat (.block (algPrivate [] [] [("A", deconstructFiveArg), ("F", deconstructSumAlg)] [
    .call (resolve "F") (alg [] [] [] [sequenceSpread (resolve "A")])
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard deconstructionSpreadArgument

-- F(1, 2): the rest captures zero items, so x = 1, y = (), z = 2 and y.sum = 0.
def deconstructionEmptyRest : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", deconstructSumAlg)] [
    .call (resolve "F") (alg [] [] [] [.num 1, .num 2])
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard deconstructionEmptyRest

-- p1, p2, rest..., q1, q2 against seven items binds the middle three to rest.
def deconstructionMatchAlg : Algorithm :=
  algWithParameters [
    { name := "p1" }, { name := "p2" }, { name := "rest", kind := .variadic },
    { name := "q1" }, { name := "q2" }
  ] [] [] [
    .param "p1", .param "p2", .dotCall (.param "rest") "count" none, .param "q1", .param "q2"
  ]

def deconstructionMatchingAlgorithm : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", deconstructionMatchAlg)] [
    .call (resolve "F") (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5, .num 6, .num 7])
  ])) with
  | Except.ok [1, 2, 3, 6, 7] => true
  | _ => false

#guard deconstructionMatchingAlgorithm

-- A single scalar argument is a one-item supply: F(first, tail...) with 1 binds
-- first = 1 and the rest captures zero items (tail.count = 0).
def deconstructFirstTailAlg : Algorithm :=
  algWithParameters [{ name := "first" }, { name := "tail", kind := .variadic }] [] [] [
    .param "first", .dotCall (.param "tail") "count" none
  ]

def deconstructionScalarArgument : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", deconstructFirstTailAlg)] [
    .call (resolve "F") (alg [] [] [] [.num 1])
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard deconstructionScalarArgument

-- A sequence-value parameter pattern also normalizes a scalar to a one-item
-- supply: F((first, tail...)) with the scalar 1 binds first = 1, tail = ().
def deconstructSequenceValueFirstTailAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "first" }, .capture { name := "tail", kind := .variadic }]
  ] [] [] [
    .param "first", .dotCall (.param "tail") "count" none
  ]

def sequenceValuePatternScalarArgument : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", deconstructSequenceValueFirstTailAlg)] [
    .call (resolve "F") (alg [] [] [] [.num 1])
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
  match runResult (.block (algPrivate [] [] [("F", deconstructSequenceValueFirstTailAlg)] [
    .call (resolve "map") (alg [] [] [] [
      sequenceItems [.num 1, .num 2, .num 3],
      .resolve "F"
    ])
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard sequenceValueDeconstructionCallbackOnScalarFails

-- Aspect 2 callback boundary (positive parity, mirrors C#
-- DeconstructionBindingTests.CallbackDeconstruction_OnSequenceValueRows_BindsPerRow):
-- a deconstruction-shaped callback applied per sequence-value row binds x/y.../z
-- within each row. With Rows = (1, 2, 3), (4, 5, 6) and F(x, y..., z) = x + y.sum + z,
-- Rows.map(F) is 6 and 15. Row callbacks work while scalar-element deconstruction
-- stays strict (see sequenceValueDeconstructionCallbackOnScalarFails above).
def deconstructionRowsAlg : Algorithm :=
  alg [] [] [] [
    sequenceItems [.num 1, .num 2, .num 3],
    sequenceItems [.num 4, .num 5, .num 6]
  ]

def deconstructionCallbackOnSequenceValueRows : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Rows", deconstructionRowsAlg),
    ("F", deconstructSumAlg)
  ] [
    .dotCall (resolve "Rows") "map" (some (alg [] [] [] [resolve "F"]))
  ])) with
  | Except.ok [6, 15] => true
  | _ => false

#guard deconstructionCallbackOnSequenceValueRows

-- A lone rest-only parameter captures the supplied call arguments. Its captured
-- value may display/count like the grouped value it captured, but the supplied
-- argument boundary still differs from explicit spread in mixed shapes below.
def restOnlyCollectAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .variadic }] [] [] [
    .dotCall (.param "values") "sum" none
  ]

def restOnlyConsumesItemSupply : Bool :=
  let singleGroupedArg :=
    match runFlat (.block (algPrivate [] [] [("A", deconstructFiveArg), ("Sum", restOnlyCollectAlg)] [
      .call (resolve "Sum") (alg [] [] [] [resolve "A"])
    ])) with
    | Except.ok [15] => true
    | _ => false
  let multipleSlots :=
    match runFlat (.block (algPrivate [] [] [("Sum", restOnlyCollectAlg)] [
      .call (resolve "Sum") (alg [] [] [] [.num 1, .num 2, .num 3])
    ])) with
    | Except.ok [6] => true
    | _ => false
  singleGroupedArg && multipleSlots

#guard restOnlyConsumesItemSupply

def mixedVariadicBoundaryAlg : Algorithm :=
  algWithParameters [{ name := "first" }, { name := "rest", kind := .variadic }] [] [] [
    .dotCall (.param "first") "count" none,
    .dotCall (.param "rest") "count" none
  ]

def mixedVariadicPlainSequenceArgumentPreservesBoundary : Bool :=
  match runFlat (.block (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2]), ("G", mixedVariadicBoundaryAlg)] [
    .call (resolve "G") (alg [] [] [] [resolve "A"])
  ])) with
  | Except.ok [2, 0] => true
  | _ => false

#guard mixedVariadicPlainSequenceArgumentPreservesBoundary

def mixedVariadicExplicitSpreadOpensSequenceArgument : Bool :=
  match runFlat (.block (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2]), ("G", mixedVariadicBoundaryAlg)] [
    .call (resolve "G") (alg [] [] [] [sequenceSpread (resolve "A")])
  ])) with
  | Except.ok [1, 1] => true
  | _ => false

#guard mixedVariadicExplicitSpreadOpensSequenceArgument

def itemSupplySumAlg : Algorithm :=
  algWithParameters [{ name := "x", kind := .variadic }] [] [] [
    .dotCall (.param "x") "sum" none
  ]

-- Rest-only `G(x...)` may display the same captured value for `G(A)` and
-- `G(A...)`, but those are different supplied argument streams. Mixed-shape
-- guards above make the boundary visible.
def restOnlyItemSupplyAllFormsSumTo15 : Bool :=
  let withArgs (args : Algorithm) : Bool :=
    match runFlat (.block (algPrivate [] [] [("A", deconstructFiveArg), ("G", itemSupplySumAlg)] [
      .call (resolve "G") args
    ])) with
    | Except.ok [15] => true
    | _ => false
  withArgs (alg [] [] [] [resolve "A"])
    && withArgs (alg [] [] [] [sequenceSpread (resolve "A")])
    && withArgs deconstructFiveArg
    && withArgs (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])])

#guard restOnlyItemSupplyAllFormsSumTo15

-- An empty call binds an empty item supply (min arity 0): `G()` sums to 0.
def restOnlyEmptyCallSumsToZero : Bool :=
  match runFlat (.block (algPrivate [] [] [("G", itemSupplySumAlg)] [
    .call (resolve "G") (alg [] [] [] [])
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard restOnlyEmptyCallSumsToZero

def itemSupplyCountAlg : Algorithm :=
  algWithParameters [{ name := "x", kind := .variadic }] [] [] [
    .dotCall (.param "x") "count" none
  ]

-- Multiple sibling grouped values are preserved (G(A, B) binds x = ((1, 2), (3, 4)),
-- count 2), not auto-flattened; only explicit `...` opens them into one item supply
-- (G(A..., B...) binds x = (1, 2, 3, 4), count 4).
def restOnlyPreservesSiblingGroupedValues : Bool :=
  let twoItemRoot (argExprs : List KatLang.Expr) : Algorithm :=
    algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4]),
      ("G", itemSupplyCountAlg)
    ] [ .call (resolve "G") (alg [] [] [] argExprs) ]
  let preserved :=
    match runFlat (.block (twoItemRoot [resolve "A", resolve "B"])) with
    | Except.ok [2] => true
    | _ => false
  let opened :=
    match runFlat (.block (twoItemRoot [sequenceSpread (resolve "A"), sequenceSpread (resolve "B")])) with
    | Except.ok [4] => true
    | _ => false
  preserved && opened

#guard restOnlyPreservesSiblingGroupedValues

def restPrefixSumAlg : Algorithm :=
  algWithParameters [{ name := "x", kind := .variadic }, { name := "y" }] [] [] [
    .binary .add (.dotCall (.param "x") "sum" none) (.param "y")
  ]

-- `(((1, 2, 3, 4, 5)))` is a doubly-nested singleton sequence value: a block whose
-- single output is a block whose output is the five items.
def nestedSingletonFive : KatLang.Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])])

-- Repeated singleton grouping is useful-structure canonicalized as a value, but
-- a function call still receives one argument unless `...` is written.
def repeatedSingletonBoundaryDoesNotImplicitlyOpenCallArgument : Bool :=
  let plainMixed :=
    match runFlat (.block (algPrivate [] [] [("F", deconstructSumAlg)] [
      .call (resolve "F") (alg [] [] [] [nestedSingletonFive])
    ])) with
    | Except.error err => innermostIsArityMismatch 2 1 err
    | _ => false
  let spreadMixed :=
    match runFlat (.block (algPrivate [] [] [("F", deconstructSumAlg)] [
      .call (resolve "F") (alg [] [] [] [sequenceSpread nestedSingletonFive])
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
  match runResult (.block (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") (alg [] [] [] [.num 0])
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
  match runResult (.block (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") (alg [] [] [] [.num 0])
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
  match runFlat (.block (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") (alg [] [] [] [.block (alg [] [] [] [.num 0, .num 5])]),
    .call (resolve "F") (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2])])
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
  match runFlat (.block (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") (alg [] [] [] [.num 0]),
    .call (resolve "F") (alg [] [] [] [.num 7])
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
  match runResult (.block (algPrivate [] [] [("Outer", outer)] [.num 42])) with
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
  alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2])]

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
  alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2, .num 3])]

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
-- An explicit spread argument (`if(X...)`) has a runtime-only count. The C#
-- parser is the only layer that gated `if` arity statically; the shared
-- evaluator already expands spread before applying counted `if`, via
-- `applyBuiltinCountedResolved -> expandSequenceSpreadBuiltinArguments`. So a
-- spread of `1, 2, 3` opens into the three argument slots and selects `whenTrue`
-- (2) as one value, matching the user wrapper `MyIF(a, b, c) = if(a, b, c)`.
-- This guard witnesses that no Lean evaluator change was needed for #131.

/-- One spread argument whose value opens to three top-level items (`X...`). -/
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
-- `(1, 2, 3)...`: the spread opens its items, so the argument still expands to
-- three slots. This mirrors the C# engine test for `TrueResult = (1, 2, 3)`.
def ifSpreadGroupedOperandArg : KatLang.ResolvedArgumentAlgorithm :=
  { algorithm := alg [] [] [] [.sequenceSpread (.block ifBranchThreeOutputs)],
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
-- as one sequence value (emitted count 1). Only explicit caller-site postfix
-- `...` re-opens it. Root output is NOT a call boundary and keeps its slot count;
-- `while`/`repeat` loop state and the strict map/reduce callback paths are also
-- unchanged. These guards pin the emitted count exactly. Lean: reCountValueBoundary.

/-- Evaluate a whole program counted, mirroring `runResultM` but preserving the
    root emitted count, so a boundary returning one value shows count 1 while the
    root output list still shows its slot count. -/
def runCountedProgram (e : KatLang.Expr) : Except KatLang.Error KatLang.CountedResult :=
  let ctx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg], algEnv := [] }
  KatLang.runEvalM
    (match e with
     | .block a =>
         let wired := KatLang.wireToCaller ctx a
         if (KatLang.Algorithm.params wired).length = 0 then
           KatLang.evalAlgOutputCounted wired ctx []
         else
           .error (KatLang.Error.unresolvedImplicitParams (KatLang.Algorithm.params wired))
     | _ => KatLang.evalCounted e ctx [])

/-- `F(a...) = a` then `F(5, 9)`. -/
def boundaryVariadicReturnAlg : Algorithm :=
  algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]

def boundaryVariadicReturnRoot (body : List KatLang.Expr) : Algorithm :=
  algPrivate [] [] [("F", algWithParameters [{ name := "a", kind := .variadic }] [] [] body)]
    [.call (.resolve "F") (alg [] [] [] [.num 5, .num 9])]

def boundaryVariadicReturnIsOneValue : Bool :=
  match runCountedProgram (.block (boundaryVariadicReturnRoot [.param "a"])) with
  | .ok (Result.sequenceValue [Result.atom 5, Result.atom 9], 1) => true
  | _ => false

#guard boundaryVariadicReturnIsOneValue

/-- `F(a...) = a...` then `F(5, 9)` -- the body spread opens the capture, but the
    call boundary still returns one value. -/
def boundaryVariadicBodySpreadIsOneValue : Bool :=
  match runCountedProgram (.block (boundaryVariadicReturnRoot [sequenceSpread (.param "a")])) with
  | .ok (Result.sequenceValue [Result.atom 5, Result.atom 9], 1) => true
  | _ => false

#guard boundaryVariadicBodySpreadIsOneValue

/-- `F(a...) = a, 0` then `F(5, 9)` -- the capture stays grouped as a nested value. -/
def boundaryVariadicCommaSlotGroupsCapture : Bool :=
  match runCountedProgram (.block (boundaryVariadicReturnRoot [.param "a", .num 0])) with
  | .ok (Result.sequenceValue [Result.sequenceValue [Result.atom 5, Result.atom 9], Result.atom 0], 1) => true
  | _ => false

#guard boundaryVariadicCommaSlotGroupsCapture

/-- `F(a...) = a..., 0` then `F(5, 9)` -- body spread flattens, boundary still one value. -/
def boundaryVariadicBodySpreadThenSlotIsOneFlatValue : Bool :=
  match runCountedProgram (.block (boundaryVariadicReturnRoot [sequenceSpread (.param "a"), .num 0])) with
  | .ok (Result.sequenceValue [Result.atom 5, Result.atom 9, Result.atom 0], 1) => true
  | _ => false

#guard boundaryVariadicBodySpreadThenSlotIsOneFlatValue

/-- `F(a...) = a` then `F(5, 9)...` -- caller-site spread re-opens the returned value. -/
def boundaryCallerSpreadOpensReturnedValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("F", boundaryVariadicReturnAlg)]
      [sequenceSpread (.call (.resolve "F") (alg [] [] [] [.num 5, .num 9]))])) with
  | .ok (Result.sequenceValue [Result.atom 5, Result.atom 9], 2) => true
  | _ => false

#guard boundaryCallerSpreadOpensReturnedValue

/-- `X = 1, 2, 3` accessed three ways: lexical `X`, explicit call `X()`, and the
    multi-output property body. -/
def boundaryMultiOutputProp : Algorithm := alg [] [] [] [.num 1, .num 2, .num 3]

def boundaryLexicalAccessIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("X", boundaryMultiOutputProp)] [.resolve "X"])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryLexicalAccessIsOneValue

def boundaryExplicitZeroArgCallIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("X", boundaryMultiOutputProp)]
      [.call (.resolve "X") (alg [] [] [] [])])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryExplicitZeroArgCallIsOneValue

/-- Structural dot zero-arg access `M.P` now matches lexical access (count 1). -/
def boundaryStructuralHolder : Algorithm :=
  alg [] [] [publicProp "P" boundaryMultiOutputProp] [.num 0]

def boundaryStructuralDotAccessIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("M", boundaryStructuralHolder)]
      [.dotCall (.resolve "M") "P" none])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryStructuralDotAccessIsOneValue

/-- Collection-producing builtin `order` returns one exact list value; spread
    opens it. -/
def boundaryOrderIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("X", alg [] [] [] [.num 3, .num 1, .num 2])]
      [.dotCall (.resolve "X") "order" none])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryOrderIsOneValue

def boundaryOrderSpreadOpensItems : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("X", alg [] [] [] [.num 3, .num 1, .num 2])]
      [sequenceSpread (.dotCall (.resolve "X") "order" none)])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryOrderSpreadOpensItems

/-- `range(1, 3)` is a collection-producing builtin: one exact list value,
    opened by spread. -/
def boundaryRangeIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] []
      [.call (.resolve "range") (alg [] [] [] [.num 1, .num 3])])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryRangeIsOneValue

/-- Internal variadic forwarding is unaffected: `F(a...) = a.sum` still sums the
    raw captured item supply. -/
def boundaryVariadicForwardingPreservesRawSupply : Bool :=
  match runCountedProgram (.block (algPrivate [] []
      [("F", algWithParameters [{ name := "a", kind := .variadic }] [] []
        [.dotCall (.param "a") "sum" none])]
      [.call (.resolve "F") (alg [] [] [] [.num 5, .num 9])])) with
  | .ok (Result.atom 14, 1) => true
  | _ => false

#guard boundaryVariadicForwardingPreservesRawSupply

/-- Regression: root output is NOT a call boundary and stays multi-output. -/
def boundaryRootOutputStaysMultiOutput : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [] [.num 1, .num 2, .num 3])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryRootOutputStaysMultiOutput

/-- Regression: redundant empty sequence nesting canonicalizes before the
    boundary re-count observes it. -/
def boundaryCanonicalizesNestedEmptySequence : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("F", alg [] [] [] [.emptySequence 1])] [.resolve "F"])) with
  | .ok (Result.sequenceValue [], 1) => true
  | _ => false

#guard boundaryCanonicalizesNestedEmptySequence

-- Collection-producing builtin parity: each returns one exact list value (count 1)
-- at the call/property boundary; caller-site `...` opens it into an item supply.
-- (`order` and `range` are covered by the guards above.)

def boundaryDesc312 : Algorithm := alg [] [] [] [.num 3, .num 1, .num 2]
def boundary123 : Algorithm := alg [] [] [] [.num 1, .num 2, .num 3]

/-- `X.orderDesc` is one value; `X.orderDesc...` opens it. -/
def boundaryOrderDescIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("X", boundaryDesc312)]
      [.dotCall (.resolve "X") "orderDesc" none])) with
  | .ok (Result.listValue [Result.atom 3, Result.atom 2, Result.atom 1], 1) => true
  | _ => false

#guard boundaryOrderDescIsOneValue

def boundaryOrderDescSpreadOpensItems : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("X", boundaryDesc312)]
      [sequenceSpread (.dotCall (.resolve "X") "orderDesc" none)])) with
  | .ok (Result.sequenceValue [Result.atom 3, Result.atom 2, Result.atom 1], 3) => true
  | _ => false

#guard boundaryOrderDescSpreadOpensItems

/-- `X.distinct` is one value; `X.distinct...` opens it. -/
def boundaryDistinctIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("X", alg [] [] [] [.num 1, .num 1, .num 2, .num 3])]
      [.dotCall (.resolve "X") "distinct" none])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryDistinctIsOneValue

def boundaryDistinctSpreadOpensItems : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("X", alg [] [] [] [.num 1, .num 1, .num 2, .num 3])]
      [sequenceSpread (.dotCall (.resolve "X") "distinct" none)])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryDistinctSpreadOpensItems

/-- `X.take(2)` is one value. -/
def boundaryTakeIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("X", boundary123)]
      [.dotCall (.resolve "X") "take" (some (alg [] [] [] [.num 2]))])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2], 1) => true
  | _ => false

#guard boundaryTakeIsOneValue

/-- `X.skip(1)` is one value; `X.skip(1)...` opens it. -/
def boundarySkipIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("X", boundary123)]
      [.dotCall (.resolve "X") "skip" (some (alg [] [] [] [.num 1]))])) with
  | .ok (Result.listValue [Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundarySkipIsOneValue

def boundarySkipSpreadOpensItems : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("X", boundary123)]
      [sequenceSpread (.dotCall (.resolve "X") "skip" (some (alg [] [] [] [.num 1])))])) with
  | .ok (Result.sequenceValue [Result.atom 2, Result.atom 3], 2) => true
  | _ => false

#guard boundarySkipSpreadOpensItems

/-- `X.filter(IsBig)` (with `IsBig(x) = x > 1`) is one value; `...` opens it. -/
def boundaryFilterPredicate : Algorithm := alg ["x"] [] [] [.binary .gt (.param "x") (.num 1)]

def boundaryFilterIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("IsBig", boundaryFilterPredicate), ("X", boundary123)]
      [.dotCall (.resolve "X") "filter" (some (alg [] [] [] [.resolve "IsBig"]))])) with
  | .ok (Result.listValue [Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryFilterIsOneValue

def boundaryFilterSpreadOpensItems : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("IsBig", boundaryFilterPredicate), ("X", boundary123)]
      [sequenceSpread (.dotCall (.resolve "X") "filter" (some (alg [] [] [] [.resolve "IsBig"])))])) with
  | .ok (Result.sequenceValue [Result.atom 2, Result.atom 3], 2) => true
  | _ => false

#guard boundaryFilterSpreadOpensItems

/-- `X.map(Double)` (with `Double(x) = x * 2`) is one value; `...` opens it. -/
def boundaryMapTransform : Algorithm := alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]

def boundaryMapIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("Double", boundaryMapTransform), ("X", boundary123)]
      [.dotCall (.resolve "X") "map" (some (alg [] [] [] [.resolve "Double"]))])) with
  | .ok (Result.listValue [Result.atom 2, Result.atom 4, Result.atom 6], 1) => true
  | _ => false

#guard boundaryMapIsOneValue

def boundaryMapSpreadOpensItems : Bool :=
  match runCountedProgram (.block (algPrivate [] [] [("Double", boundaryMapTransform), ("X", boundary123)]
      [sequenceSpread (.dotCall (.resolve "X") "map" (some (alg [] [] [] [.resolve "Double"])))])) with
  | .ok (Result.sequenceValue [Result.atom 2, Result.atom 4, Result.atom 6], 3) => true
  | _ => false

#guard boundaryMapSpreadOpensItems

/-- `atoms((1, (2, 3)))` is one value; `atoms(...)...` opens it. -/
def boundaryAtomsArg : Algorithm := alg [] [] [] [sequenceItems [.num 1, sequenceItems [.num 2, .num 3]]]

def boundaryAtomsIsOneValue : Bool :=
  match runCountedProgram (.block (algPrivate [] [] []
      [.call (.resolve "atoms") boundaryAtomsArg])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryAtomsIsOneValue

def boundaryAtomsSpreadOpensItems : Bool :=
  match runCountedProgram (.block (algPrivate [] [] []
      [sequenceSpread (.call (.resolve "atoms") boundaryAtomsArg)])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryAtomsSpreadOpensItems

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
    ("Pair", alg [] [] [] [.block (alg [] [] [] [.num 10, .num 20])]),
    ("Values", alg [] [] [] [.num 10, .num 20]),
    ("Value", alg [] [] [] [.num 42]),
    ("Receiver", alg [] [] [] [.num 1]),
    ("Bad", alg [] [] [] [.binary .div (.num 1) (.num 0)]),
    ("Holder", alg [] [] [publicProp "Inner" (alg [] [] [] [.num 42])] [.num 1]),
    ("Choose", dotCallParityChooseAlg),
    ("G", dotCallParitySingletonSequenceValueAlg)
  ] [.num 0]

-- Inline `(…)` receivers expose their top-level output items.
def dotCallParityData123 : KatLang.Expr := .block (alg [] [] [] [.num 1, .num 2, .num 3])
def dotCallParityData312 : KatLang.Expr := .block (alg [] [] [] [.num 3, .num 1, .num 2])
def dotCallParityDataMixedSigns : KatLang.Expr :=
  .block (alg [] [] [] [.num (-1), .num 2, .num (-3)])

def dotCallArgs (items : List KatLang.Expr) : Option Algorithm :=
  some (alg [] [] [] items)

structure DotCallParityCase where
  label : String
  target : KatLang.Expr
  name : String
  argsOpt : Option Algorithm := none
  expected : BuiltinApplyOutcome := .succeeded
  expectedAtoms : Option (List Int) := none

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
  let plain := (KatLang.evalDotCall c.target c.name c.argsOpt ctx []).run KatLang.EvalState.empty
  let counted := (KatLang.evalDotCallCounted c.target c.name c.argsOpt ctx []).run KatLang.EvalState.empty
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
    -- spread: Pair.NItems == NItems(Pair) == 1.
    { label := "B/sequenceValue-receiver-one-slot", target := resolve "Pair", name := "NItems",
      expectedAtoms := some [2] },
    -- C: explicit spread of a multi-output property spreads its emitted top-level
    -- values into the rest-only `NItems(values...)` item supply: (Values...).NItems
    -- binds the two values, count 2.
    { label := "C/spread-multi-output-receiver",
      target := sequenceSpreadReceiver (resolve "Values"), name := "NItems",
      expectedAtoms := some [2] },
    -- D: explicit spread of a sequence-valued property opens it into the item
    -- supply the same way: (Pair...).NItems binds the two elements, count 2.
    { label := "D/spread-sequenceValue-receiver-stays-sequenceValue",
      target := sequenceSpreadReceiver (resolve "Pair"), name := "NItems",
      expectedAtoms := some [2] },
    -- E: leading variadic with suffix: Pair.BeforeLastCount(99) captures the
    -- sequence-value receiver as one variadic item.
    { label := "E/leading-variadic-with-suffix", target := resolve "Pair",
      name := "BeforeLastCount", argsOpt := dotCallArgs [.num 99],
      expectedAtoms := some [2] },
    -- F/G: spread receivers pre-expand only for leading-flat-variadic callees
    -- (`hasLeadingFlatVariadicParameter`; the C# evaluator gates identically),
    -- so a fixed-arity callee receives the spread receiver as ONE slot and
    -- under-binds — for the multi-output and the sequence-valued property alike.
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
      expectedAtoms := some [42] } ]

def dotCallParityCaseFailures : List String :=
  (dotCallParityCases.filter (fun c => !(dotCallParityCaseHolds c))).map
    (fun c => c.label)

#guard dotCallParityCaseFailures == []

-- The cache-sensitive cases must actually write the cache, so the final-state
-- comparison inside the parity helper is not vacuously `empty == empty`.
def dotCallParityCacheCasesWriteCache : Bool :=
  [ (resolve "Holder", "Inner") ].all
    fun (target, name) =>
      match (KatLang.evalDotCall target name none (dotCallParityCtx dotCallParityProg) []).run
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
  match runResult (.block (alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
  | _ => false

#guard listLiteralConstructsExactValue

-- `[]`, `[7]`, and `[[7]]` keep exact cardinality and nesting: no singleton
-- erasure and no empty canonicalization applies to list structure.
def listExactnessPreserved : Bool :=
  (match runResult (.block (alg [] [] [] [.listLiteral []])) with
   | Except.ok (Result.listValue []) => true | _ => false) &&
  (match runResult (.block (alg [] [] [] [.listLiteral [.num 7]])) with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false) &&
  (match runResult (.block (alg [] [] [] [.listLiteral [.listLiteral [.num 7]]])) with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 7]]) => true | _ => false)

#guard listExactnessPreserved

-- Equality is structural, recursive, and kind-exact: a list never equals a
-- sequence value or the lone item it contains.
def listEqualityIsKindExact : Bool :=
  expectFlat (runFlat (.block (alg [] [] [] [
    .binary .eq (.listLiteral [.num 1, .num 2]) (.listLiteral [.num 1, .num 2]),
    .binary .eq (.listLiteral []) (.emptySequence 0),
    .binary .eq (.listLiteral [.num 7]) (.num 7),
    .binary .eq (.listLiteral [.num 1, .num 2]) (.block (alg [] [] [] [.num 1, .num 2]))])))
    [1, 0, 0, 0]

#guard listEqualityIsKindExact

-- Ordinary parentheses stay a redundant SEQUENCE grouping around lists:
-- `([1, 2])` canonicalizes to the exact list itself.
def redundantParensAroundListCanonicalize : Bool :=
  match runResult (.block (alg [] [] [] [.block (alg [] [] [] [.listLiteral [.num 1, .num 2]])])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard redundantParensAroundListCanonicalize

-- A non-spread `()` element stays one visible list element.
def listKeepsVisibleEmptyElement : Bool :=
  match runResult (.block (alg [] [] [] [.listLiteral [.num 1, .emptySequence 0, .num 2]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.sequenceValue [], Result.atom 2]) => true
  | _ => false

#guard listKeepsVisibleEmptyElement

-- Postfix spread opens exactly ONE list boundary; capturing the spread yields
-- the canonical sequence of the elements.
def spreadCaptureConvertsListToSequence : Bool :=
  match runResult (.block (algPrivate [] []
    [("A", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]]),
     ("B", alg [] [] [] [sequenceSpread (.resolve "A")])]
    [.resolve "B"])) with
  | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
  | _ => false

#guard spreadCaptureConvertsListToSequence

-- Spread edge cases: `[]...` supplies zero items (captures as `()`),
-- `[7]...` supplies the item, `[[7]]...` supplies the inner list intact.
def listSpreadEdgeCasesOpenOneBoundary : Bool :=
  (match runResult (.block (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral []])] [sequenceSpread (.resolve "A")])) with
   | Except.ok (Result.sequenceValue []) => true | _ => false) &&
  (match runResult (.block (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.num 7]])] [sequenceSpread (.resolve "A")])) with
   | Except.ok (Result.atom 7) => true | _ => false) &&
  (match runResult (.block (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.listLiteral [.num 7]]])] [sequenceSpread (.resolve "A")])) with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false)

#guard listSpreadEdgeCasesOpenOneBoundary

-- List-literal elements use the ordinary expression-list model: spread
-- elements insert their item supply into the constructed list.
def listLiteralSpreadElements : Bool :=
  match runResult (.block (algPrivate [] []
    [("A", alg [] [] [] [.num 1, .num 2, .num 3])]
    [.listLiteral [.num 0, sequenceSpread (.resolve "A"), .num 4]])) with
  | Except.ok (Result.listValue
      [Result.atom 0, Result.atom 1, Result.atom 2, Result.atom 3, Result.atom 4]) => true
  | _ => false

#guard listLiteralSpreadElements

-- Empty spreads contribute no elements; a NON-spread `[]` stays one element.
def emptyListSpreadIsNeutralInListLiteral : Bool :=
  (match runResult (.block (alg [] [] []
      [.listLiteral [.num 1, sequenceSpread (.listLiteral []), .num 2]])) with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.listLiteral [.num 1, .listLiteral [], .num 2]])) with
   | Except.ok (Result.listValue [Result.atom 1, Result.listValue [], Result.atom 2]) => true
   | _ => false)

#guard emptyListSpreadIsNeutralInListLiteral

-- Calls preserve list boundaries: a list without spread is ONE argument.
def callPreservesListBoundary : Bool :=
  match runResult (.block (algPrivate [] []
    [("F", alg ["a"] [] [] [.param "a"]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2]])]
    [.call (.resolve "F") (alg [] [] [] [.resolve "A"])])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard callPreservesListBoundary

-- Explicit spread supplies the elements as separate arguments.
def spreadOpensListIntoCallArguments : Bool :=
  expectFlat (runFlat (.block (algPrivate [] []
    [("F", alg ["a", "b", "c"] [] []
        [.binary .add (.binary .add (.param "a") (.param "b")) (.param "c")]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call (.resolve "F") (alg [] [] [] [sequenceSpread (.resolve "A")])]))) [6]

#guard spreadOpensListIntoCallArguments

-- A fixed-arity callee rejects an unspread list (calls never open lists).
-- The list behaves exactly like any other single non-openable argument
-- (scalar, string): the Lean final-arg binding path reports the remaining
-- parameter/argument counts after the first binding step (`2 0`), a
-- pre-existing payload shape shared by `F(5)` and `F('xy')`; the C# runtime
-- reports the full signature counts (`3 1`). Both are category `arity`.
def callDoesNotImplicitlyOpenList : Bool :=
  expectInnermostArityMismatch 2 0 (runFlat (.block (algPrivate [] []
    [("F", alg ["a", "b", "c"] [] []
        [.binary .add (.binary .add (.param "a") (.param "b")) (.param "c")]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call (.resolve "F") (alg [] [] [] [.resolve "A"])])))

#guard callDoesNotImplicitlyOpenList

-- Mixed fixed/rest call: a lone list argument stays whole — `first` receives
-- the entire list, `rest` captures nothing.
def mixedRestCallKeepsLoneListWhole : Bool :=
  match runResult (.block (algPrivate [] []
    [("F", algWithParameters [{ name := "first" }, { name := "rest", kind := .variadic }] [] []
        [.param "first"]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2]])]
    [.call (.resolve "F") (alg [] [] [] [.resolve "A"])])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard mixedRestCallKeepsLoneListWhole

-- Deconstruction (the sequence-value parameter pattern) opens a lone LIST
-- exactly like a lone sequence value: `x, y, z = [1, 2, 3]` binds elementwise.
def deconstructionOpensLoneList : Bool :=
  let helper := KatLang.Expr.block (algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]]
    [] [] [.param "y"])
  expectFlat (runFlat (.block (algPrivate [] []
    [("d", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call helper (alg [] [] [] [.resolve "d"])]))) [2]

#guard deconstructionOpensLoneList

-- Rest capture in deconstruction stays SEQUENCE-shaped: it never
-- reconstructs the source list.
def listRestCaptureIsSequenceShaped : Bool :=
  let helper := KatLang.Expr.block (algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .variadic }]]
    [] [] [.param "rest"])
  match runResult (.block (algPrivate [] []
    [("d", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call helper (alg [] [] [] [.resolve "d"])])) with
  | Except.ok (Result.sequenceValue [Result.atom 2, Result.atom 3]) => true
  | _ => false

#guard listRestCaptureIsSequenceShaped

-- Deconstruction opens only the OUTER lone structure: nested lists stay whole.
def deconstructionDoesNotOpenListRecursively : Bool :=
  let helper := KatLang.Expr.block (algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]]
    [] [] [.param "x"])
  match runResult (.block (algPrivate [] []
    [("d", alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2], .num 3]])]
    [.call helper (alg [] [] [] [.resolve "d"])])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard deconstructionDoesNotOpenListRecursively

-- Builtin collection binding opens a lone list like a lone sequence value:
-- the shared collection-item view opens ONE outer sequence or list boundary,
-- so `count([1, 2, 3])` counts three items.
def builtinLoneListCollectionOpens : Bool :=
  expectFlat (runFlat (.block (alg [] [] []
    [.call (.resolve "count") (alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])])))
    [3]

#guard builtinLoneListCollectionOpens

-- Opening is never recursive: two sibling lists grouped into ONE collection
-- argument are two items (`count(([], []))` is 2), the ungrouped `count([], [])`
-- is a two-argument arity error, and a nested list inside an opened lone list
-- stays one opaque item (`count([1, [2], 3])` is 3).
def builtinSiblingListsCountAsItems : Bool :=
  expectFlat (runFlat (.block (alg [] [] []
    [.call (.resolve "count") (alg [] [] []
      [.block (alg [] [] [] [.listLiteral [], .listLiteral []])])])))
    [2] &&
  (match runResult (.block (alg [] [] []
    [.call (.resolve "count") (alg [] [] []
      [.listLiteral [], .listLiteral []])])) with
   | Except.error err => innermostIsArityMismatch 1 2 err
   | _ => false)

#guard builtinSiblingListsCountAsItems

def builtinNestedListStaysOneItem : Bool :=
  expectFlat (runFlat (.block (alg [] [] []
    [.call (.resolve "count") (alg [] [] []
      [.listLiteral [.num 1, .listLiteral [.num 2], .num 3]])])))
    [3]

#guard builtinNestedListStaysOneItem

-- Spread keeps only its ordinary meaning at builtin calls: `count([1, 2, 3]...)`
-- opens the list into THREE ordinary argument slots, an arity error under
-- `count(collection)` (same for sum). Grouping the spread back into one
-- argument is the rewrite idiom: `count(([1, 2, 3]...))` is 3, and the
-- unspread `count([1, 2, 3])` stays the direct form (see
-- builtinLoneListCollectionOpens above).
def builtinSpreadListFollowsFixedArity : Bool :=
  (match runResult (.block (alg [] [] []
    [.call (.resolve "count") (alg [] [] [] [sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])])])) with
   | Except.error err => innermostIsArityMismatch 1 3 err
   | _ => false) &&
  (match runResult (.block (alg [] [] []
    [.call (.resolve "sum") (alg [] [] [] [sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])])])) with
   | Except.error err => innermostIsArityMismatch 1 3 err
   | _ => false) &&
  expectFlat (runFlat (.block (alg [] [] []
    [.call (.resolve "count") (alg [] [] []
      [.block (alg [] [] [] [sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])])])]))) [3]

#guard builtinSpreadListFollowsFixedArity

-- Indexing returns the selected element exactly as stored: selecting a list
-- ITEM from a sequence preserves the list (projection does not erase
-- listness).
def indexingPreservesSelectedList : Bool :=
  match runResult (.block (algPrivate [] []
    [("A", alg [] [] [] [.block (alg [] [] [] [.num 0, .listLiteral [.num 1, .num 2]])])]
    [.index (.resolve "A") (.num 1)])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard indexingPreservesSelectedList

-- Indexing `:` opens a LIST TARGET to its immediate elements exactly like a
-- sequence target (`Result.projectionItems`): `[1, 2, 3]:0` is `1`, `[7]:0`
-- is `7`, and the selected element keeps its exact kind.
def listIndexingSelectsElement : Bool :=
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 0)])) with
   | Except.ok (Result.atom 1) => true | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 1)])) with
   | Except.ok (Result.atom 2) => true | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 2)])) with
   | Except.ok (Result.atom 3) => true | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral [.num 7]) (.num 0)])) with
   | Except.ok (Result.atom 7) => true | _ => false)

#guard listIndexingSelectsElement

-- A selected LIST element stays one exact opaque list (no flattening, no
-- sequence conversion): `[[1, 2], [3, 4]]:0` is `[1, 2]` and `[[]]:0` is `[]`.
def listIndexingNestedElementStaysList : Bool :=
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral
        [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]) (.num 0)])) with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral [.listLiteral []]) (.num 0)])) with
   | Except.ok (Result.listValue []) => true | _ => false)

#guard listIndexingNestedElementStaysList

-- Chained projection peels one boundary per `:`: `[[1, 2], [3, 4]]:1:0` is `3`.
def listIndexingChainedSelectsOneLevelAtATime : Bool :=
  match runResult (.block (alg [] [] []
    [.index (.index (.listLiteral
      [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]) (.num 1)) (.num 0)])) with
  | Except.ok (Result.atom 3) => true
  | _ => false

#guard listIndexingChainedSelectsOneLevelAtATime

-- A selected SEQUENCE element inside a list projects one level with its item
-- count, exactly like the sequence-target twin; a selected `()` element stays
-- one visible empty row at root.
def listIndexingSequenceElementProjectsCounted : Bool :=
  (match runCountedProgram (.block (alg [] [] []
      [.index (.listLiteral
        [.block (alg [] [] [] [.num 1, .num 2]),
         .block (alg [] [] [] [.num 3, .num 4])]) (.num 0)])) with
   | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2], 2) => true | _ => false) &&
  (match runCountedProgram (.block (alg [] [] []
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
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral []) (.num 0)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.num 2)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.num 100)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.num (-1))])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 3000000000)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.index (.block (alg [] [] [] [.num 1, .num 2, .num 3])) (.num 3000000000)])) with
   | Except.error err => innermostIsBadIndex err | _ => false)

#guard listIndexingOutOfRangeIsBadIndex

-- Selector validation is unchanged by list targets: a list-valued selector
-- never coerces to a number (badArity), and a string selector stays the
-- string type mismatch — identical to sequence targets.
def listIndexingSelectorValidationUnchanged : Bool :=
  (match runResult (.block (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.listLiteral [.num 0])])) with
   | Except.error err => innermostIsBadArity err | _ => false) &&
  (match runResult (.block (alg [] [] []
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
  (KatLang.exprDiagnosticName (.index (.resolve "A") (.call (.resolve "f") (alg [] [] [] [.num 0])))
    == "A:(f(...))") &&
  -- A bare negative literal is not selector syntax at all (`A:-1` is a parse
  -- error), so it keeps parentheses.
  (KatLang.exprDiagnosticName (.index (.resolve "A") (.num (-1))) == "A:(-1)")

#guard indexDiagnosticNameParenthesizesRebindingOperands

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
  (match runResult (.block (alg [] [] []
      [.index (.call (.resolve "range") (alg [] [] [] [.num 1, .num 3])) (.num 2)])) with
   | Except.ok (Result.atom 3) => true | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.index (.dotCall (.listLiteral [.num 3, .num 1, .num 2]) "order" none) (.num 0)])) with
   | Except.ok (Result.atom 1) => true | _ => false) &&
  (match runResult (.block (alg [] [] []
      [.index (.call (.resolve "take")
        (alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3], .num 2])) (.num 1)])) with
   | Except.ok (Result.atom 2) => true | _ => false)

#guard listIndexingBuiltinResultsDirectlyIndexable

-- Each written spread layer opens exactly one boundary: stacked spread on a
-- nested list agrees with the value-boundary-separated form (`A......` is
-- `(A...)...`), and extra layers on sequence values stay fixed points.
def stackedSpreadOpensOneListBoundaryPerLayer : Bool :=
  (match runResult (.block (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.listLiteral [.num 7]]])]
      [.sequenceSpread (.sequenceSpread (.resolve "A"))])) with
   | Except.ok (Result.atom 7) => true | _ => false) &&
  (match runResult (.block (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2]]])]
      [.sequenceSpread (.sequenceSpread (.resolve "A"))])) with
   | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runResult (.block (algPrivate [] []
      [("A", alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2])])]
      [.sequenceSpread (.sequenceSpread (.resolve "A"))])) with
   | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2]) => true | _ => false)

#guard stackedSpreadOpensOneListBoundaryPerLayer

end KatLangTests
