import KatLang

--------------------------------------------------------------------------------
-- dotCall semantics tests
--------------------------------------------------------------------------------

namespace KatLangTests
open KatLang (alg algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)

def hasContext (target : String) : Error -> Bool
  | .withContext msg inner => msg = target || hasContext target inner
  | _ => false

def innermostIsBadArity : Error -> Bool
  | .withContext _ inner => innermostIsBadArity inner
  | .badArity => true
  | _ => false

def innermostIsArityMismatch (expected actual : Nat) : Error -> Bool
  | .withContext _ inner => innermostIsArityMismatch expected actual inner
  | .arityMismatch e a => e = expected && a = actual
  | _ => false

def innermostIsMissingOutput : Error -> Bool
  | .withContext _ inner => innermostIsMissingOutput inner
  | .missingOutput => true
  | _ => false

def innermostIsResultJoinMissingOutput (side : String) : Error -> Bool
  | .withContext _ inner => innermostIsResultJoinMissingOutput side inner
  | .resultJoinMissingOutput actual => actual = side
  | _ => false

def innermostIsExplicitParamsRequireOutput : Error -> Bool
  | .withContext _ inner => innermostIsExplicitParamsRequireOutput inner
  | .explicitParamsRequireOutput => true
  | _ => false

def innermostIsSpecialOutputAccess : Error -> Bool
  | .withContext _ inner => innermostIsSpecialOutputAccess inner
  | .specialOutputAccess => true
  | _ => false

def innermostIsUnknownName (target : String) : Error -> Bool
  | .withContext _ inner => innermostIsUnknownName target inner
  | .unknownName name => name = target
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

#eval test1  -- should be true
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

#eval test2a  -- should be true
-- EXPECTED: Except.error (arityMismatch 1 0)
#eval runResult (.dotCall (.block receiver2) "F" none)

-- Test 2b: Structural property with explicit args → direct binding (navigation-only)
-- a.F(10) where F(x) = x + 1 → 11
def test2b : Bool :=
  match runFlat (.dotCall (.block receiver2) "F" (some (alg [] [] [] [.num 10]))) with
  | Except.ok [11] => true
  | _ => false

#eval test2b  -- should be true
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

#eval test2c  -- should be true
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

#eval directCallWorks  -- should be true

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

#eval directCallUsesOwnArity  -- should be true

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

#eval zeroArgOutputCallWorks  -- should be true

def zeroArgOutputRejectsExtraArgsRoot : Algorithm :=
  algPrivate [] [] [("Algo", zeroArgOutputAlg)] [
    .call (.resolve "Algo") (alg [] [] [] [.num 6])
  ]

def zeroArgOutputRejectsExtraArgs : Bool :=
  match runResult (.block zeroArgOutputRejectsExtraArgsRoot) with
  | Except.error err => innermostIsArityMismatch 0 1 err
  | Except.ok _ => false

#eval zeroArgOutputRejectsExtraArgs  -- should be true

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

#eval helperDotCallStillWorks  -- should be true

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

#eval capturedLocalHelperStillWorks  -- should be true

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

#eval capturedLocalOnlyDotRejected  -- should be true

def capturedLocalOnlyDotCallRoot : Algorithm :=
  algPrivate [] [] [("Algo", capturedLocalOnlyAlg)] [
    .dotCall (.resolve "Algo") "Prop" (some (alg [] [] [] [.num 6]))
  ]

def capturedLocalOnlyDotCallRejected : Bool :=
  match runResult (.block capturedLocalOnlyDotCallRoot) with
  | Except.error err => innermostIsLocalOnlyProperty "Algo" "Prop" .localCapturedAncestorParams err
  | Except.ok _ => false

#eval capturedLocalOnlyDotCallRejected  -- should be true

def helperDirectCallStillFailsRoot : Algorithm :=
  algPrivate [] [] [("Algo", helperOutputAlg)] [
    .call (.resolve "Algo") (alg [] [] [] [.num 6])
  ]

def helperDirectCallStillFails : Bool :=
  match runResult (.block helperDirectCallStillFailsRoot) with
  | Except.error err => innermostIsArityMismatch 0 1 err
  | Except.ok _ => false

#eval helperDirectCallStillFails  -- should be true

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

#eval parametrizedValuePositionRejectsBareUse  -- should be true

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

#eval nestedDirectCallWorks  -- should be true

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

#eval conditionalLocalInnerRejected  -- should be true

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

#eval conditionalSplitHelpersRejected  -- should be true

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

#eval outputDotCallRejected  -- should be true

def nestedOutputDotCallRejectedRoot : Algorithm :=
  algPrivate [] [] [("Outer", outerDirectCallAlg)] [
    .dotCall (.dotCall (.resolve "Outer") "Inner" none) "Output" (some (alg [] [] [] [.num 6]))
  ]

def nestedOutputDotCallRejected : Bool :=
  match runResult (.block nestedOutputDotCallRejectedRoot) with
  | Except.error err => innermostIsSpecialOutputAccess err
  | Except.ok _ => false

#eval nestedOutputDotCallRejected  -- should be true

def bareOutputAccessRejectedRoot : Algorithm :=
  algPrivate [] [] [("Algo", zeroArgOutputAlg)] [
    .dotCall (.resolve "Algo") "Output" none
  ]

def bareOutputAccessRejected : Bool :=
  match runResult (.block bareOutputAccessRejectedRoot) with
  | Except.error err => innermostIsSpecialOutputAccess err
  | Except.ok _ => false

#eval bareOutputAccessRejected  -- should be true

def stringLiteralSatisfiesInvariant : Bool :=
  KatLang.postElabInvariant (.stringLiteral "abc")

#eval stringLiteralSatisfiesInvariant  -- should be true

def stringOutputAlgSatisfiesInvariant : Bool :=
  KatLang.postElabInvariantAlg (alg [] [] [] [.stringLiteral "abc"])

#eval stringOutputAlgSatisfiesInvariant  -- should be true

def unresolvedLoadViolatesInvariant : Bool :=
  !KatLang.postElabInvariant
    (.call (.resolve "load") (alg [] [] [] [.stringLiteral "https://katlang.org/lib.kat"]))

#eval unresolvedLoadViolatesInvariant  -- should be true

def outputDotCallViolatesInvariant : Bool :=
  !KatLang.postElabInvariant (.dotCall (.resolve "Algo") "Output" none)

#eval outputDotCallViolatesInvariant  -- should be true

def structuralOutputPropertyViolatesInvariant : Bool :=
  !KatLang.postElabInvariantAlg
    (alg [] [] [privateProp "Output" (alg [] [] [] [.num 1])] [.num 2])

#eval structuralOutputPropertyViolatesInvariant  -- should be true

def helperPropertySatisfiesInvariant : Bool :=
  KatLang.postElabInvariantAlg
    (alg [] [] [privateProp "Helper" (alg [] [] [] [.num 1])] [.stringLiteral "abc"])

#eval helperPropertySatisfiesInvariant  -- should be true

--------------------------------------------------------------------------------
-- missingOutput semantics tests
--------------------------------------------------------------------------------

def noOutputGroupAlg : Algorithm :=
  algPrivate [] [] [("X", alg [] [] [] [.num 1])] []

def missingOutputValid1Root : Algorithm :=
  algPrivate [] [] [("A", noOutputGroupAlg)] []

def missingOutputValid1 : Bool :=
  match runFlat (.block missingOutputValid1Root) with
  | Except.ok [] => true
  | _ => false

#eval missingOutputValid1  -- should be true

def missingOutputValid2Root : Algorithm :=
  algPrivate [] [] [("A", noOutputGroupAlg)] [
    .dotCall (.resolve "A") "X" none
  ]

def missingOutputValid2 : Bool :=
  match runFlat (.block missingOutputValid2Root) with
  | Except.ok [1] => true
  | _ => false

#eval missingOutputValid2  -- should be true

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

#eval missingOutputValid3  -- should be true

def holderMissingOutputAlg : Algorithm :=
  algPrivate [] [] [("F", noOutputGroupAlg)] [.num 0]

def missingOutputValid4Root : Algorithm :=
  algPrivate [] [] [("Holder", holderMissingOutputAlg)] [.resolve "Holder"]

def missingOutputValid4 : Bool :=
  match runFlat (.block missingOutputValid4Root) with
  | Except.ok [0] => true
  | _ => false

#eval missingOutputValid4  -- should be true

def missingOutputError5Root : Algorithm :=
  algPrivate [] [] [("A", noOutputGroupAlg)] [.resolve "A"]

def missingOutputError5 : Bool :=
  match runResult (.block missingOutputError5Root) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#eval missingOutputError5  -- should be true

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

#eval missingOutputError6  -- should be true

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

#eval missingOutputError6b  -- should be true

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

#eval missingOutputError7  -- should be true

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

#eval missingOutputError8  -- should be true

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

#eval missingOutputError9  -- should be true

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

#eval missingOutputValid10  -- should be true

--------------------------------------------------------------------------------
-- explicit algorithm params require output
--------------------------------------------------------------------------------

def noOutputHelperContainer : Algorithm :=
  algPrivate [] [] [("Prop", alg [] [] [] [.num 7])] []

def invalidExplicitParamClauseAlg : Algorithm :=
  Algorithm.elaborateClauseDefinition (KatLang.Pattern.bind "x") noOutputHelperContainer

def explicitParamsWithoutOutputRejected : Bool :=
  match KatLang.validateExplicitParamOutputInvariant invalidExplicitParamClauseAlg with
  | Except.error Error.explicitParamsRequireOutput => true
  | _ => false

#eval explicitParamsWithoutOutputRejected  -- should be true

def explicitParamsWithoutOutputRejectedAtRun : Bool :=
  match runResult (.block (algPrivate [] [] [("Algo", invalidExplicitParamClauseAlg)] [.num 0])) with
  | Except.error err => innermostIsExplicitParamsRequireOutput err
  | Except.ok _ => false

#eval explicitParamsWithoutOutputRejectedAtRun  -- should be true

def parameterizedChildPropertyContainer : Algorithm :=
  algPrivate [] [] [("Prop", alg ["x", "y"] [] [] [.num 7])] []

def parameterizedChildPropertyWithoutOuterParamsStillValid : Bool :=
  match runFlat (.block (algPrivate [] [] [("Algo", parameterizedChildPropertyContainer)] [
    .dotCall (.resolve "Algo") "Prop" (some (alg [] [] [] [.num 1, .num 2]))
  ])) with
  | Except.ok [7] => true
  | _ => false

#eval parameterizedChildPropertyWithoutOuterParamsStillValid  -- should be true

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

#eval test3  -- should be true
-- EXPECTED: Except.ok [10]
#eval runFlat (.block outer3)

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

#eval test4  -- should be true
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

#eval openPrivateHeadLaterWorks  -- should be true

def openDoesNotExposePrivateMemberRoot : Algorithm :=
  algPrivate [] [.resolve "Lib"] [("Lib", openPrivateHeadLib)] [.resolve "Hidden"]

def openDoesNotExposePrivateMember : Bool :=
  match runResult (.block openDoesNotExposePrivateMemberRoot) with
  | Except.error err => innermostIsUnknownName "Hidden" err
  | Except.ok _ => false

#eval openDoesNotExposePrivateMember  -- should be true

def openMissingHeadRoot : Algorithm :=
  alg [] [.resolve "Missing"] [] [.resolve "X"]

def openMissingHeadStillErrors : Bool :=
  match runResult (.block openMissingHeadRoot) with
  | Except.error err =>
      hasContext "while resolving open: Missing" err
      && innermostIsUnknownName "Missing" err
  | Except.ok _ => false

#eval openMissingHeadStillErrors  -- should be true

def openBuiltinTargetRoot : Algorithm :=
  alg [] [.resolve "if"] [] [.resolve "X"]

def openBuiltinTargetStillIllegal : Bool :=
  match runResult (.block openBuiltinTargetRoot) with
  | Except.error err =>
      hasContext "while resolving open: if" err
      && innermostIsIllegalInOpen "builtin 'if'" err
  | Except.ok _ => false

#eval openBuiltinTargetStillIllegal  -- should be true

def openQualifiedPrivatePathRoot : Algorithm :=
  algPrivate [] [.dotCall (.resolve "Lib") "PrivateSub" none] [("Lib", openPrivateHeadLib)] [.resolve "Y"]

def openQualifiedPrivatePathStillRestricted : Bool :=
  match runResult (.block openQualifiedPrivatePathRoot) with
  | Except.error err =>
      hasContext "while resolving open: Lib.PrivateSub" err
      && innermostIsNotPublicProperty "Lib" "PrivateSub" err
  | Except.ok _ => false

#eval openQualifiedPrivatePathStillRestricted  -- should be true

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

#eval test5a  -- should be true
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

#eval test5b  -- should be true
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

#eval test6  -- should be true
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

#eval test7  -- should be true
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

#eval test8  -- should be true
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

#eval test9a  -- should be true
#eval runResult (.dotCall (.block receiver9) "Inc" none)

-- Test 9b: Structural property with explicit args → direct binding
-- a.Inc(5) where Inc(x) = x + 1 → 6
def test9b : Bool :=
  match runFlat (.dotCall (.block receiver9) "Inc" (some (alg [] [] [] [.num 5]))) with
  | Except.ok [6] => true
  | _ => false

#eval test9b  -- should be true
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

#eval test10  -- should be true
#eval runFlat (.block (algPrivate [] [] [("R", receiver10)] [
  .call (resolve "repeat")
    (alg [] [] [] [
      .block (alg ["x"] [] [] [.binary .add (.param "x") (.num 10)]),
      .dotCall (resolve "R") "Count" (some (alg [] [] [] [.num 1])),
      .block (alg [] [] [] [.num 0])
    ])
]))

-- Test 11: dotCall none syntax for count in Repeat argument position
-- Repeat(Add, Numbers.count, (0,0)) where Numbers.count is encoded as .dotCall
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
          .block (alg [] [] [] [.num 0, .num 0])
        ]))
      (.num 1)
  ]

def test11 : Bool :=
  match runFlat (.block testAlg11) with
  | Except.ok [24] => true
  | _ => false

#eval test11  -- should be true
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

#eval test12  -- should be true
-- EXPECTED: Except.ok [3]
#eval runFlat (.block testAlg12)

-- Test 13: named multi-output receiver no longer exposes arity
def arityRemovedRoot13 : Algorithm :=
  algPrivate [] [] [("Data", alg [] [] [] [.num 1, .num 7])] [
    .dotCall (resolve "Data") "arity" none
  ]

def test13 : Bool :=
  match runResult (.block arityRemovedRoot13) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#eval test13  -- should be true
#eval runResult (.block arityRemovedRoot13)

-- Test 14: inline grouped receiver no longer exposes arity
def test14 : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.num 1, .num 7])) "arity" none) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#eval test14  -- should be true
#eval runResult (.dotCall (.block (alg [] [] [] [.num 1, .num 7])) "arity" none)

-- Test 14a: extra grouped receiver layer no longer exposes arity
def test14a : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 7])])) "arity" none) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#eval test14a  -- should be true
#eval runResult (.dotCall (.block (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 7])])) "arity" none)

-- Test 14b: count still works for named, inline, and nested grouped receivers
def countReceiverRoot14b : Algorithm :=
  algPrivate [] [] [("Data", alg [] [] [] [.num 1, .num 7])] [
    .dotCall (resolve "Data") "count" none,
    .dotCall (.block (alg [] [] [] [.num 1, .num 7])) "count" none,
    .dotCall (.block (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 7])])) "count" none
  ]

def test14b : Bool :=
  match runFlat (.block countReceiverRoot14b) with
  | Except.ok [2, 2, 1] => true
  | _ => false

#eval test14b  -- should be true
#eval runFlat (.block countReceiverRoot14b)

-- Test 14d: old length intrinsic name is no longer recognized
def test14d : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "length" none) with
  | Except.error _ => true
  | Except.ok _ => false

#eval test14d  -- should be true
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

#eval test15  -- should be true
#eval runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("ApplyTwice", applyTwiceAlg15)] [
  .call (resolve "ApplyTwice") (alg [] [] [] [resolve "Inc", .num 10])
]))

-- Test 16: higher-order args do not force argExpr-count = param-count
-- UsePair(f, x, y) = f(x) + y; second argument unpacks to two values.
def usePairAlg16 : Algorithm :=
  alg ["f", "x", "y"] [] [] [
    .binary .add
      (.call (.param "f") (alg [] [] [] [.param "x"]))
      (.param "y")
  ]

def pairArg16 : Algorithm :=
  alg [] [] [] [.num 10, .num 20]

def test16 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("UsePair", usePairAlg16)] [
    .call (resolve "UsePair") (alg [] [] [] [resolve "Inc", .block pairArg16])
  ])) with
  | Except.ok [31] => true
  | _ => false

#eval test16  -- should be true
#eval runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("UsePair", usePairAlg16)] [
  .call (resolve "UsePair") (alg [] [] [] [resolve "Inc", .block pairArg16])
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
    .call (resolve "F") (alg [] [] [] [.num 3, .num 7]),
    .call (resolve "F") (alg [] [] [] [.block dotCallBoundaryPairReceiverAlg16a])
  ])) with
  | Except.ok [10, 10] => true
  | _ => false

#eval dotCallBoundaryNormalCallsStillWork16a  -- should be true

def dotCallBoundaryScalarReceiverStillWorks16a : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.num 3) "F" (some (alg [] [] [] [.num 7]))
  ])) with
  | Except.ok [10] => true
  | _ => false

#eval dotCallBoundaryScalarReceiverStillWorks16a  -- should be true

def dotCallBoundaryMultiOutputReceiverNoArgsFails16a : Bool :=
  match runResult (.block (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "F" none
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#eval dotCallBoundaryMultiOutputReceiverNoArgsFails16a  -- should be true

def dotCallBoundaryMultiOutputReceiverEmptyArgsFails16a : Bool :=
  match runResult (.block (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "F" (some (alg [] [] [] []))
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#eval dotCallBoundaryMultiOutputReceiverEmptyArgsFails16a  -- should be true

def dotCallBoundaryCountedPathDoesNotSpread16a : Bool :=
  match runResult (.block (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall
      (.dotCall (.block dotCallBoundaryPairReceiverAlg16a) "F" none)
      "count"
      none
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#eval dotCallBoundaryCountedPathDoesNotSpread16a  -- should be true

def dotCallBoundaryGroupReceiverAlg16a : Algorithm :=
  alg ["x"] [] [] [.param "x"]

def dotCallBoundaryOneParamGetsGroupedReceiver16a : Bool :=
  match runResult (.block (algPrivate [] [] [("G", dotCallBoundaryGroupReceiverAlg16a)] [
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "G" none
  ])) with
  | Except.ok (.group [.atom 3, .atom 7]) => true
  | _ => false

#eval dotCallBoundaryOneParamGetsGroupedReceiver16a  -- should be true

def dotCallBoundaryFinalExplicitArgStillUnpacks16a : Bool :=
  let hAlg := alg ["a", "b", "c"] [] [] [
    .binary .add
      (.binary .add (.param "a") (.param "b"))
      (.param "c")
  ]
  match runFlat (.block (algPrivate [] [] [("H", hAlg)] [
    .dotCall (.num 3) "H" (some (alg [] [] [] [
      .block (alg [] [] [] [.num 4, .num 5])
    ]))
  ])) with
  | Except.ok [12] => true
  | _ => false

#eval dotCallBoundaryFinalExplicitArgStillUnpacks16a  -- should be true

def dotCallBoundarySequenceBuiltinsStillExpand16a : Bool :=
  match runFlat (.block (alg [] [] [] [
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "sum" none,
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "count" none,
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "first" none,
    .dotCall (.block dotCallBoundaryPairReceiverAlg16a) "last" none
  ])) with
  | Except.ok [10, 2, 3, 7] => true
  | _ => false

#eval dotCallBoundarySequenceBuiltinsStillExpand16a  -- should be true

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

#eval test17  -- should be true
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

#eval test18  -- should be true
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

#eval test19  -- should be true
#eval runFlat (.block (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
  .call (resolve "Apply") (alg [] [] [] [.block constSevenAlg19])
]))

def test19SingleOutputCallRejected : Bool :=
  match runFlat (.block (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
    .call (resolve "Apply") (alg [] [] [] [.block constSevenAlg19])
  ])) with
  | Except.error _ => true
  | _ => false

#eval test19SingleOutputCallRejected  -- should be true
#eval runFlat (.block (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
  .call (resolve "Apply") (alg [] [] [] [.block constSevenAlg19])
]))

def test19MultiOutput : Bool :=
  match runFlat (.block (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
    .call (resolve "Apply") (alg [] [] [] [.block twoValueAlg19])
  ])) with
  | Except.ok [1, 2] => true
  | _ => false

#eval test19MultiOutput  -- should be true
#eval runFlat (.block (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
  .call (resolve "Apply") (alg [] [] [] [.block twoValueAlg19])
]))

def test19MultiOutputCallRejected : Bool :=
  match runFlat (.block (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
    .call (resolve "Apply") (alg [] [] [] [.block twoValueAlg19])
  ])) with
  | Except.error _ => true
  | _ => false

#eval test19MultiOutputCallRejected  -- should be true
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
    pattern := KatLang.Pattern.group [KatLang.Pattern.bind "x", KatLang.Pattern.bind "f"]
    body := applyClauseBody19a
  }]

def test19aShape : Bool :=
  match applyClauseAlg19a with
  | .mk _ ["x", "f"] _ _ _ => true
  | _ => false

#eval test19aShape  -- should be true

def test19aRun : Bool :=
  match runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("Apply", applyClauseAlg19a)] [
    .call (resolve "Apply") (alg [] [] [] [.num 9, resolve "Inc"])
  ])) with
  | Except.ok [10] => true
  | _ => false

#eval test19aRun  -- should be true

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
  | .mk _ ["x"] _ _ _ => true
  | _ => false

#eval test19aSingleBinderShape  -- should be true

def test19aSingleBinderRun : Bool :=
  match runFlat (.block (algPrivate [] [] [("Id", idClauseAlg19a)] [
    .call (resolve "Id") (alg [] [] [] [.num 7])
  ])) with
  | Except.ok [7] => true
  | _ => false

#eval test19aSingleBinderRun  -- should be true

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

#eval test19aMultiClauseShape  -- should be true

def test19aMultiClauseRun : Bool :=
  match runFlat (.block (algPrivate [] [] [("F", fallbackClauseAlg19a)] [
    .call (resolve "F") (alg [] [] [] [.num 2])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test19aMultiClauseRun  -- should be true

def test19aLiteralPatternIsConditional : Bool :=
  match Algorithm.elaborateClauseGroup [{
      pattern := KatLang.Pattern.litInt 1
      body := alg [] [] [] [.num 42]
    }] with
  | .conditional _ _ [_] => true
  | _ => false

#eval test19aLiteralPatternIsConditional  -- should be true

def test19aGroupedPatternIsConditional : Bool :=
  match Algorithm.elaborateClauseGroup [{
      pattern := KatLang.Pattern.group [
        KatLang.Pattern.bind "x",
        KatLang.Pattern.group [KatLang.Pattern.bind "acc", KatLang.Pattern.bind "counter"]
      ]
      body := alg [] [] [] [.param "x"]
    }] with
  | .conditional _ _ [_] => true
  | _ => false

#eval test19aGroupedPatternIsConditional  -- should be true

-- Test 19b: compatibility fallback for a manually constructed single-branch
-- flat-binder conditional still preserves higher-order args in the core AST.
def applyCondAlg19b : Algorithm :=
  .conditional none [] [
    ⟨ KatLang.Pattern.group [KatLang.Pattern.bind "x", KatLang.Pattern.bind "f"],
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

#eval test19b  -- should be true
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

#eval test19c  -- should be true
#eval runFlat (.block (algPrivate [] [] [("Inc", incAlg15), ("Receiver", receiver19c)] [
  .dotCall (resolve "Receiver") "Apply" (some (alg [] [] [] [.num 9, resolve "Inc"]))
]))

-- Test 19d: grouped eager values stay whole when a sibling argument binds only
-- through AlgEnv.
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
      .block (alg [] [] [] [.num 1, .num 2]),
      .block evenPredicateAlg19d
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test19d  -- should be true
#eval runFlat (.block (algPrivate [] [] [
  ("OccurrenceCount", occurrenceCountAlg19d)
] [
  .call (.resolve "OccurrenceCount") (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block evenPredicateAlg19d
  ])
]))

-- Test 19e: inline predicate captures an outer value parameter rather than
-- re-declaring it as a local parameter.
--
-- Plain-call sequence builtins now expand emitted top-level items from
-- ordinary arguments. This test still uses explicit top-level pair arguments
-- to keep the capture shape obvious.
def occurrenceCountAlg19e : Algorithm :=
  alg ["target"] [] [] [
    .dotCall
      (.call (.resolve "filter") (alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 10]),
        .block (alg [] [] [] [.num 2, .num 20]),
        .block (alg [] [] [] [.num 2, .num 30]),
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

#eval test19e  -- should be true
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

#eval test20  -- should be true
#eval runFlat (.call (resolve "if") (alg [] [] [] [.num 1, .num 5, .num 6]))

-- Test 21: 3-arg if false → produce else-branch value
-- if(0, 5, 6) → [6]
def test21 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 0, .num 5, .num 6])) with
  | Except.ok [6] => true
  | _ => false

#eval test21  -- should be true
#eval runFlat (.call (resolve "if") (alg [] [] [] [.num 0, .num 5, .num 6]))

--------------------------------------------------------------------------------
-- Conditional algorithm tests
--------------------------------------------------------------------------------

open KatLang (Pattern CondBranch)

-- Test 22: K combinator via conditional algorithm
-- K(a, b) = a  →  K(10, 20) => 10
def kAlg : Algorithm :=
  .conditional none [] [
    ⟨ .group [.bind "a", .bind "b"],
      alg [] [] [] [.param "a"] ⟩
  ]

def test34 : Bool :=
  match runFlat (.block (algPrivate [] [] [("K", kAlg)] [
    .call (resolve "K") (alg [] [] [] [.num 10, .num 20])
  ])) with
  | Except.ok [10] => true
  | _ => false

#eval test34  -- should be true
#eval runFlat (.block (algPrivate [] [] [("K", kAlg)] [
  .call (resolve "K") (alg [] [] [] [.num 10, .num 20])
]))

-- Test 35: Multiple branches with literal match
-- Else(1, (a, b)) = a
-- Else(c, (a, b)) = b
def elseAlg : Algorithm :=
  .conditional none [] [
    ⟨ .group [.litInt 1, .group [.bind "a", .bind "b"]],
      alg [] [] [] [.param "a"] ⟩,
    ⟨ .group [.bind "c", .group [.bind "a", .bind "b"]],
      alg [] [] [] [.param "b"] ⟩
  ]

-- Else(1, (2, 3)) → first branch matches → a = 2
def test35a : Bool :=
  match runFlat (.block (algPrivate [] [] [("Else", elseAlg)] [
    .call (resolve "Else") (alg [] [] [] [.num 1, .block (alg [] [] [] [.num 2, .num 3])])
  ])) with
  | Except.ok [2] => true
  | _ => false

#eval test35a  -- should be true

-- Else(0, (2, 3)) → second branch matches → b = 3
def test35b : Bool :=
  match runFlat (.block (algPrivate [] [] [("Else", elseAlg)] [
    .call (resolve "Else") (alg [] [] [] [.num 0, .block (alg [] [] [] [.num 2, .num 3])])
  ])) with
  | Except.ok [3] => true
  | _ => false

#eval test35b  -- should be true

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

#eval test36  -- should be true

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

#eval test37  -- should be true

-- Test 22: 2-arg if is rejected
def test22 : Bool :=
  match runResult (.call (resolve "if") (alg [] [] [] [.num 1, .num 5])) with
  | Except.error _ => true
  | Except.ok _ => false

#eval test22  -- should be true
#eval runResult (.call (resolve "if") (alg [] [] [] [.num 1, .num 5]))

-- Test 23: 2-arg if in addition is rejected
def test23 : Bool :=
  match runResult (.binary .add (.num 10) (.call (resolve "if") (alg [] [] [] [.num 1, .num 5]))) with
  | Except.error _ => true
  | Except.ok _ => false

#eval test23  -- should be true
#eval runResult (.binary .add (.num 10) (.call (resolve "if") (alg [] [] [] [.num 1, .num 5])))

-- Test 24: 2-arg if in multiplication is rejected
def test24 : Bool :=
  match runResult (.binary .mul (.num 10) (.call (resolve "if") (alg [] [] [] [
    .binary .lt (.num 7) (.num 6),
    .num 1
  ]))) with
  | Except.error _ => true
  | Except.ok _ => false

#eval test24  -- should be true
#eval runResult (.binary .mul (.num 10) (.call (resolve "if") (alg [] [] [] [
  .binary .lt (.num 7) (.num 6),
  .num 1
])))

-- Test 25: Result join with 3-arg if selects the else branch
-- 1, if(0, 2, 9), 3 → [1, 9, 3]
def test25 : Bool :=
  match runFlat (.resultJoin (.num 1) (.resultJoin (.call (resolve "if") (alg [] [] [] [.num 0, .num 2, .num 9])) (.num 3))) with
  | Except.ok [1, 9, 3] => true
  | _ => false

#eval test25  -- should be true
#eval runFlat (.resultJoin (.num 1) (.resultJoin (.call (resolve "if") (alg [] [] [] [.num 0, .num 2, .num 9])) (.num 3)))

def resultJoin1234 : KatLang.Expr :=
  .resultJoin (.resultJoin (.resultJoin (.num 1) (.num 2)) (.num 3)) (.num 4)

def test25a : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [resultJoin1234]),
    .call (resolve "count") (alg [] [] [] [resultJoin1234]),
    .call (resolve "first") (alg [] [] [] [resultJoin1234]),
    .call (resolve "last") (alg [] [] [] [resultJoin1234])
  ])) with
  | Except.ok [10, 4, 1, 4] => true
  | _ => false

#eval test25a  -- should be true

def test25b : Bool :=
  let groupedLeft := .resultJoin (.block (alg [] [] [] [.num 1, .num 2])) (.num 3)
  let groupedRight := .resultJoin (.num 1) (.block (alg [] [] [] [.num 2, .num 3]))
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [groupedLeft]),
    .call (resolve "count") (alg [] [] [] [groupedRight])
  ])) with
  | Except.ok [3, 3] => true
  | _ => false

#eval test25b  -- should be true

def test25bNestedGroups : Bool :=
  let nestedLeft := .resultJoin (.block (alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2])])) (.num 3)
  let nestedMiddle := .resultJoin (.block (alg [] [] [] [.num 1, .block (alg [] [] [] [.num 2, .num 3])])) (.num 4)
  match runResult (.block (alg [] [] [] [nestedLeft, nestedMiddle])) with
  | Except.ok value =>
      value == Result.group [
        Result.group [Result.group [Result.atom 1, Result.atom 2], Result.atom 3],
        Result.group [Result.atom 1, Result.group [Result.atom 2, Result.atom 3], Result.atom 4]
      ]
  | _ => false

#eval test25bNestedGroups  -- should be true

def test25bCommaSimilarity : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("B", alg [] [] [] [.resultJoin (.num 1) (.num 2)])
  ] [
    .dotCall (resolve "A") "count" none,
    .dotCall (resolve "B") "count" none
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#eval test25bCommaSimilarity  -- should be true

def test25c : Bool :=
  let pThenMore := .resultJoin (.resultJoin (.resultJoin (resolve "P") (.num 3)) (.num 4)) (.num 5)
  match runFlat (.block (algPrivate [] [] [
    ("P", alg [] [] [] [.num 1, .num 2]),
    ("X", alg [] [] [] [.call (resolve "sum") (alg [] [] [] [pThenMore])])
  ] [
    resolve "X"
  ])) with
  | Except.ok [15] => true
  | _ => false

#eval test25c  -- should be true

def test25dResultShape : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("F", alg ["a"] [] [] [.param "a", .num 3])
  ] [
    .dotCall (resolve "A") "F" none
  ])) with
  | Except.ok value =>
      value == Result.group [Result.group [Result.atom 1, Result.atom 2], Result.atom 3]
  | _ => false

#eval test25dResultShape  -- should be true

def test25e : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("F", alg ["a"] [] [] [.resultJoin (.param "a") (.num 3)])
  ] [
    .dotCall (resolve "A") "F" none
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#eval test25e  -- should be true

def test25f : Bool :=
  let a := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] [.num 10]
  let b := alg [] [] [publicProp "Y" (alg [] [] [] [.num 2])] [.num 20]
  match runFlat (.block (algPrivate [] [] [
    ("A", a),
    ("B", b),
    ("C", alg [] [] [] [.resultJoin (resolve "A") (resolve "B")])
  ] [
    resolve "C"
  ])) with
  | Except.ok [10, 20] => true
  | _ => false

#eval test25f  -- should be true

def test25g : Bool :=
  let a := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] [.num 10]
  let b := alg [] [] [publicProp "Y" (alg [] [] [] [.num 2])] [.num 20]
  match runFlat (.block (algPrivate [] [] [
    ("A", a),
    ("B", b),
    ("C", alg [] [] [] [.resultJoin (resolve "A") (resolve "B")])
  ] [
    .dotCall (resolve "C") "X" none
  ])) with
  | Except.error err => innermostIsUnknownName "X" err
  | _ => false

#eval test25g  -- should be true

def test25h : Bool :=
  let bad := .block (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])
  match runFlat (.resultJoin bad (.num 3)) with
  | Except.error err => innermostIsResultJoinMissingOutput "left" err
  | _ => false

#eval test25h  -- should be true

def test25i : Bool :=
  let bad := .block (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])
  match runFlat (.resultJoin (.num 3) bad) with
  | Except.error err => innermostIsResultJoinMissingOutput "right" err
  | _ => false

#eval test25i  -- should be true

def test25j : Bool :=
  let a := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] []
  let b := alg [] [] [publicProp "Y" (alg [] [] [] [.num 2])] []
  match runFlat (.block (algPrivate [] [.resultJoin (resolve "A") (resolve "B")] [
    ("A", a),
    ("B", b)
  ] [
    .binary .add (resolve "X") (resolve "Y")
  ])) with
  | Except.error err => innermostIsBadOpenForm "resultJoin: A; B" err
  | _ => false

#eval test25j  -- should be true

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

#eval test26  -- should be true

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

#eval test27  -- should be true

-- Test 28: 3-arg if still works — if(1, 10, 20) → [10]
def test28 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 1, .num 10, .num 20])) with
  | Except.ok [10] => true
  | _ => false

#eval test28  -- should be true

-- Test 29: 3-arg if false → if(0, 10, 20) → [20]
def test29 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 0, .num 10, .num 20])) with
  | Except.ok [20] => true
  | _ => false

#eval test29  -- should be true

-- Test 30: 3-arg if with non-zero condition → true
-- if(42, 7, 9) → [7]
def test30 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 42, .num 7, .num 9])) with
  | Except.ok [7] => true
  | _ => false

#eval test30  -- should be true

-- Test 31: 3-arg if with negative condition → true
-- if(-1, 7, 9) → [7]
def test31 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num (-1), .num 7, .num 9])) with
  | Except.ok [7] => true
  | _ => false

#eval test31  -- should be true

--------------------------------------------------------------------------------
-- string intrinsic tests
--------------------------------------------------------------------------------

-- Test 52: string intrinsic on positive integer via algorithm
-- (block [123]).string → Result.str "123"
def test52 : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.num 123])) "string" none) with
  | Except.ok (Result.str "123") => true
  | _ => false

#eval test52  -- should be true
#eval runResult (.dotCall (.block (alg [] [] [] [.num 123])) "string" none)

-- Test 53: string intrinsic on zero
-- (block [0]).string → Result.str "0"
def test53 : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.num 0])) "string" none) with
  | Except.ok (Result.str "0") => true
  | _ => false

#eval test53  -- should be true

-- Test 54: string intrinsic on negative integer
-- (block [-5]).string → Result.str "-5"
def test54 : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.num (-5)])) "string" none) with
  | Except.ok (Result.str "-5") => true
  | _ => false

#eval test54  -- should be true

-- Test 55: string intrinsic on a named property
-- A = 123; A.string → Result.str "123"
def test55 : Bool :=
  let innerAlg := algPrivate [] [] [("A", alg [] [] [] [.num 123])] [
    .dotCall (.resolve "A") "string" none
  ]
  match runResult (.block innerAlg) with
  | Except.ok (Result.str "123") => true
  | _ => false

#eval test55  -- should be true

-- Test 56: string intrinsic on numeric literal (notAnAlgorithm path)
-- (.num 42).string → Result.str "42"
def test56 : Bool :=
  match runResult (.dotCall (.num 42) "string" none) with
  | Except.ok (Result.str "42") => true
  | _ => false

#eval test56  -- should be true

-- Test 57: string intrinsic on string literal → typeMismatch error
-- ("hello").string → Error.typeMismatch
def test57 : Bool :=
  match runResult (.dotCall (.stringLiteral "hello") "string" none) with
  | Except.error _ => true
  | _ => false

#eval test57  -- should be true

-- Test 58: string intrinsic on multi-output → typeMismatch error
-- (1, 2).string → Error (group is not a numeric atom)
def test58 : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "string" none) with
  | Except.error _ => true
  | _ => false

#eval test58  -- should be true

--------------------------------------------------------------------------------
-- range builtin tests
--------------------------------------------------------------------------------

-- Test 59: ascending inclusive range
def test59 : Bool :=
  match runFlat (.call (resolve "range") (alg [] [] [] [.num 1, .num 10])) with
  | Except.ok [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] => true
  | _ => false

#eval test59  -- should be true

-- Test 60: descending inclusive range
def test60 : Bool :=
  match runFlat (.call (resolve "range") (alg [] [] [] [.num 10, .num 1])) with
  | Except.ok [10, 9, 8, 7, 6, 5, 4, 3, 2, 1] => true
  | _ => false

#eval test60  -- should be true

-- Test 61: equal bounds produce a singleton
def test61 : Bool :=
  match runFlat (.call (resolve "range") (alg [] [] [] [.num 5, .num 5])) with
  | Except.ok [5] => true
  | _ => false

#eval test61  -- should be true

-- Test 62: negative to positive bounds remain inclusive and ordered
def test62 : Bool :=
  match runFlat (.call (resolve "range") (alg [] [] [] [.num (-2), .num 2])) with
  | Except.ok [-2, -1, 0, 1, 2] => true
  | _ => false

#eval test62  -- should be true

-- Test 32: Unary / binary composition with 2-arg if is rejected
def test32 : Bool :=
  match runResult (.binary .add (.num 10) (.unary .minus (.call (resolve "if") (alg [] [] [] [.num 0, .num 5])))) with
  | Except.error _ => true
  | Except.ok _ => false

#eval test32  -- should be true

-- Test 33: if arity mismatch — 1 arg → error
def test33 : Bool :=
  match runResult (.call (resolve "if") (alg [] [] [] [.num 1])) with
  | Except.error _ => true
  | Except.ok _ => false

#eval test33  -- should be true

--------------------------------------------------------------------------------
-- String literal tests (first-class string values)
--------------------------------------------------------------------------------

-- Test 38: String literal evaluates to Result.str
def test38 : Bool :=
  match runResult (.stringLiteral "hello") with
  | Except.ok (.str "hello") => true
  | _ => false

#eval test38  -- should be true

-- Test 39: String equality — same values
def test39 : Bool :=
  match runFlat (.binary .eq (.stringLiteral "a") (.stringLiteral "a")) with
  | Except.ok [1] => true
  | _ => false

#eval test39  -- should be true

-- Test 40: String equality — different values
def test40 : Bool :=
  match runFlat (.binary .eq (.stringLiteral "a") (.stringLiteral "b")) with
  | Except.ok [0] => true
  | _ => false

#eval test40  -- should be true

-- Test 41: String inequality
def test41 : Bool :=
  match runFlat (.binary .ne (.stringLiteral "a") (.stringLiteral "b")) with
  | Except.ok [1] => true
  | _ => false

#eval test41  -- should be true

-- Test 42: String equality is case-sensitive
def test42 : Bool :=
  match runFlat (.binary .eq (.stringLiteral "Apples") (.stringLiteral "apples")) with
  | Except.ok [0] => true
  | _ => false

#eval test42  -- should be true

-- Test 43: Unsupported binary operation on strings → typeMismatch
def test43 : Bool :=
  match runResult (.binary .add (.stringLiteral "a") (.stringLiteral "b")) with
  | Except.error (Error.typeMismatch _) => true
  | _ => false

#eval test43  -- should be true

-- Test 44: Mixed string/number in binary → typeMismatch
def test44 : Bool :=
  match runResult (.binary .add (.num 1) (.stringLiteral "a")) with
  | Except.error (Error.typeMismatch _) => true
  | _ => false

#eval test44  -- should be true

-- Test 45: Unary minus on string → typeMismatch
def test45 : Bool :=
  match runResult (.unary .minus (.stringLiteral "hello")) with
  | Except.error (Error.typeMismatch _) => true
  | _ => false

#eval test45  -- should be true

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

#eval test46  -- should be true

-- Test 47: Conditional algorithm with string pattern — no match
def test47 : Bool :=
  match runResult (.block (algPrivate [] [] [("Price", priceAlg)] [
    .call (resolve "Price") (alg [] [] [] [.stringLiteral "bananas"])
  ])) with
  | Except.error _ => true   -- noMatchingBranch
  | Except.ok _    => false

#eval test47  -- should be true

-- Test 48: String passed as algorithm argument
-- Echo = x, Echo('hello') → 'hello'
def echoAlg : Algorithm := alg ["x"] [] [] [.param "x"]
def test48 : Bool :=
  match runResult (.block (algPrivate [] [] [("Echo", echoAlg)] [
    .call (resolve "Echo") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.ok (.str "hello") => true
  | _ => false

#eval test48  -- should be true

-- Test 49: String stored in property and returned
-- Name = 'KatLang', output = Name
def test49 : Bool :=
  let nameAlg := alg [] [] [] [.stringLiteral "KatLang"]
  match runResult (.block (algPrivate [] [] [("Name", nameAlg)] [resolve "Name"])) with
  | Except.ok (.str "KatLang") => true
  | _ => false

#eval test49  -- should be true

-- Test 50: Pattern matching — litString in isMatchEquivalent
def test50a : Bool := Pattern.isMatchEquivalent (.litString "a") (.litString "a")
def test50b : Bool := !Pattern.isMatchEquivalent (.litString "a") (.litString "b")
def test50c : Bool := !Pattern.isMatchEquivalent (.litString "a") (.litInt 1)
def test50d : Bool := !Pattern.isMatchEquivalent (.litString "a") (.bind "x")

#eval test50a  -- should be true
#eval test50b  -- should be true
#eval test50c  -- should be true
#eval test50d  -- should be true

-- Test 51: Block with unresolved implicit params → unresolvedImplicitParams error
-- A block whose algorithm has params (unresolved names become params) should
-- produce unresolvedImplicitParams, not arityMismatch.
def test51 : Bool :=
  -- param "x" makes the block have params=["x"]
  match runResult (.block (alg ["x"] [] [] [.param "x"])) with
  | Except.error (Error.unresolvedImplicitParams ["x"]) => true
  | _ => false

#eval test51  -- should be true

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

def keepTenGroupAlg66b : Algorithm :=
  .conditional none [] [
    ⟨ .group [
        .group [
          .bind "a", .bind "b", .bind "c", .bind "d", .bind "e",
          .bind "f", .bind "g", .bind "h", .bind "i", .bind "j"
        ]
      ],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def keepFourGroupAlg66c : Algorithm :=
  .conditional none [] [
    ⟨ .group [.group [.bind "a", .bind "b", .bind "c", .bind "d"]],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def rejectFourGroupAlg66d : Algorithm :=
  .conditional none [] [
    ⟨ .group [.group [.bind "a", .bind "b", .bind "c", .bind "d"]],
      alg [] [] [] [.num 0] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 1] ⟩
  ]

def markThreeGroupAlg66e : Algorithm :=
  .conditional none [] [
    ⟨ .group [.group [.bind "a", .bind "b", .bind "c"]],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def keepPairAlg67 : Algorithm :=
  .conditional none [] [
    ⟨ .group [.bind "tag", .bind "value"],
      alg [] [] [] [.binary .eq (.binary .mod (.param "tag") (.num 2)) (.num 0)] ⟩
  ]

def badMultiFalseAlg68 : Algorithm :=
  alg ["x"] [] [] [.num 0, .num 999]

def badMultiTrueAlg69 : Algorithm :=
  alg ["x"] [] [] [.num 5, .num 0]

def badGroupedAlg70 : Algorithm :=
  alg ["x"] [] [] [.block (alg [] [] [] [.num 1, .num 0])]

def emptyTruthAlg71 : Algorithm :=
  alg ["x"] [] [] [
    .call (resolve "take") (alg [] [] [] [
      .param "x",
      .num 0
    ])
  ]

-- Test 63: plain-call filter preserves a range argument as one outer item
def test63 : Bool :=
  match runFlat (.block (algPrivate [] [] [("KeepTenGroup", keepTenGroupAlg66b)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 10]),
      .resolve "KeepTenGroup"
    ])
  ])) with
  | Except.ok [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] => true
  | _ => false

#eval test63  -- should be true

-- Test 64: descending ranges stay grouped as one outer item in plain-call filter
def test64 : Bool :=
  match runFlat (.block (algPrivate [] [] [("KeepTenGroup", keepTenGroupAlg66b)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 10, .num 1]),
      .resolve "KeepTenGroup"
    ])
  ])) with
  | Except.ok [10, 9, 8, 7, 6, 5, 4, 3, 2, 1] => true
  | _ => false

#eval test64  -- should be true

-- Test 65: a grouped-only predicate now matches one grouped range item
def test65 : Bool :=
  match runFlat (.block (algPrivate [] [] [("KeepFourGroup", keepFourGroupAlg66c)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "KeepFourGroup"
    ])
  ])) with
  | Except.ok [1, 2, 3, 4] => true
  | _ => false

#eval test65  -- should be true

-- Test 66: a grouped-only rejection predicate now rejects one grouped range item
def test66 : Bool :=
  match runFlat (.block (algPrivate [] [] [("RejectFourGroup", rejectFourGroupAlg66d)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "RejectFourGroup"
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#eval test66  -- should be true

-- Test 66aa: comma-separated higher-order args preserve outer boundaries
def test66aa : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg63)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 3, .num 6]),
      .num 8,
      .resolve "IsEven"
    ])
  ])) with
  | Except.ok [8] => true
  | _ => false

#eval test66aa  -- should be true

-- Test 66ab: explicit result join projects range content for filter
def test66ab : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg63)] [
    .call (resolve "filter") (alg [] [] [] [
      .resultJoin
        (.call (resolve "range") (alg [] [] [] [.num 3, .num 6]))
        (.num 8),
      .resolve "IsEven"
    ])
  ])) with
  | Except.ok [4, 6, 8] => true
  | _ => false

#eval test66ab  -- should be true

-- Test 67: filtering an already-empty grouped boundary stays empty
def test67 : Bool :=
  match runFlat (.block (algPrivate [] [] [("KeepFourGroup", keepFourGroupAlg66c), ("RejectFourGroup", rejectFourGroupAlg66d)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "RejectFourGroup"
      ]),
      .resolve "KeepFourGroup"
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#eval test67  -- should be true

-- Test 68: grouped elements are preserved whole and in order
def test68 : Bool :=
  match runResult (.block (algPrivate [] [] [("KeepPair", keepPairAlg67)] [
    .call (resolve "filter") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 10]),
      .block (alg [] [] [] [.num 2, .num 20]),
      .block (alg [] [] [] [.num 3, .num 30]),
      .block (alg [] [] [] [.num 4, .num 40]),
      .resolve "KeepPair"
    ])
  ])) with
  | Except.ok (.group [
      .group [.atom 2, .atom 20],
      .group [.atom 4, .atom 40]
    ]) => true
  | _ => false

#eval test68  -- should be true

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

#eval test69  -- should be true

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

#eval test70  -- should be true

-- Test 71: grouped predicate result is rejected
def test71 : Bool :=
  match runResult (.block (algPrivate [] [] [("Bad", badGroupedAlg70)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "Bad"
    ])
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#eval test71  -- should be true

-- Test 72: empty predicate result is rejected
def test72 : Bool :=
  match runResult (.block (algPrivate [] [] [("Bad", emptyTruthAlg71)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "Bad"
    ])
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#eval test72  -- should be true

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

#eval test73  -- should be true

-- Test 74: builtin arity mismatch still follows normal conventions
def test74 : Bool :=
  match runResult (.call (resolve "filter") (alg [] [] [] [
    .call (resolve "range") (alg [] [] [] [.num 1, .num 3])
  ])) with
  | Except.error _ => true
  | _ => false

#eval test74  -- should be true

-- Test 75: filter predicate arity mismatch explains the implicit item argument
def test75 : Bool :=
  match runResult (.dotCall
    (.call (resolve "range") (alg [] [] [] [.num 1, .num 5]))
    "filter"
    (some (alg [] [] [] [.num 1]))) with
  | Except.error err =>
      hasContext "while evaluating filter predicate (filter passes each iterated collection item as collected; ordinary boundaries stay whole and explicit result join/: iterate content)" err &&
      innermostIsArityMismatch 0 1 err
  | _ => false

#eval test75  -- should be true

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
    ⟨ .group [
        .group [.bind "a", .bind "b", .bind "c", .bind "d"],
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
    ⟨ .group [.bind "x", .bind "acc"],
      alg [] [] [] [.num 0] ⟩
  ]

def reduceGroupedItemAlg79 : Algorithm :=
  .conditional none [] [
    ⟨ .group [.group [.bind "tag", .bind "value"], .bind "acc"],
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

def reduceEmptyBoundaryGroupedAccAlg80b : Algorithm :=
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

def reduceEmptyAlg81 : Algorithm :=
  alg ["x", "acc"] [] [] [
    .call (resolve "take") (alg [] [] [] [
      .param "x",
      .num 0
    ])
  ]

def reduceMultiAlg82 : Algorithm :=
  alg ["x", "acc"] [] [] [.param "acc", .param "x"]

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

#eval test76  -- should be true

-- Test 77: plain-call reduce preserves one grouped range item
def test77 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Mul", mulAlg77)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "Mul",
      .num 1
    ])
  ])) with
  | Except.ok [14] => true
  | _ => false

#eval test77  -- should be true

-- Test 77a: plain-call reduce can still observe grouped range content explicitly
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

#eval test77a  -- should be true

-- Test 78: grouped-only reduce branches now match one grouped range item
def test78 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Digits", digitsAlg78)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "Digits",
      .num 0
    ])
  ])) with
  | Except.ok [1234] => true
  | _ => false

#eval test78  -- should be true

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

#eval test79  -- should be true

-- Test 80: grouped accumulators also stay unchanged when reducing an empty collection
def test80 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a), ("MarkEmptyBoundary", reduceEmptyBoundaryGroupedAccAlg80b)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ]),
      .resolve "MarkEmptyBoundary",
      .block (alg [] [] [] [.num 7, .num 9])
    ])
  ])) with
  | Except.ok (.group [.atom 7, .atom 9]) => true
  | _ => false

#eval test80  -- should be true

-- Test 81: grouped collection elements are passed to the step as whole values
def test81 : Bool :=
  match runFlat (.block (algPrivate [] [] [("TakeValue", reduceGroupedItemAlg79)] [
    .call (resolve "reduce") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 10]),
      .block (alg [] [] [] [.num 2, .num 20]),
      .block (alg [] [] [] [.num 3, .num 30]),
      .resolve "TakeValue",
      .num 0
    ])
  ])) with
  | Except.ok [60] => true
  | _ => false

#eval test81  -- should be true

-- Test 82: grouped accumulators keep their shape while one grouped range item is reduced once
def test82 : Bool :=
  match runResult (.block (algPrivate [] [] [("Stats", reduceStatsAlg80)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "Stats",
      .block (alg [] [] [] [.num 0, .num 0])
    ])
  ])) with
  | Except.ok (.group [.atom 4, .atom 1]) => true
  | _ => false

#eval test82  -- should be true

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

#eval test83  -- should be true

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

#eval test84  -- should be true

-- Test 84a: reduce requires at least three total arguments
def test84a : Bool :=
  match runResult (.block (algPrivate [] [] [("Add", addAlg76)] [
    .call (resolve "reduce") (alg [] [] [] [
      .num 1,
      .resolve "Add"
    ])
  ])) with
  | Except.error err =>
      hasContext "expected at least 3 arguments (one or more sequence arguments plus step algorithm, initial accumulator algorithm) arguments" err
      && innermostIsArityMismatch 0 2 err
  | _ => false

#eval test84a  -- should be true

-- Test 84b: reduce reports a missing initial accumulator before evaluating the step as the accumulator
def test84b : Bool :=
  match runResult (.block (algPrivate [] [] [("Add", addAlg76)] [
    .call (resolve "reduce") (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3,
      .resolve "Add"
    ])
  ])) with
  | Except.error err =>
      hasContext "while preparing reduce initial accumulator" err
      && innermostIsBadArity err
  | _ => false

#eval test84b  -- should be true

--------------------------------------------------------------------------------
-- map builtin tests
--------------------------------------------------------------------------------

def doubleAlg85 : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]

def takeMiddleGroupAlg85a : Algorithm :=
  .conditional none [] [
    ⟨ .group [.group [.bind "a", .bind "b", .bind "c", .bind "d", .bind "e"]],
      alg [] [] [] [.param "c"] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def squareAlg86 : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.param "x")]

def tagAlg87 : Algorithm :=
  .conditional none [] [
    ⟨ .group [.group [.bind "first", .bind "b", .bind "c", .bind "d", .bind "last"]],
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
    ⟨ .group [.bind "tag", .bind "value"],
      alg [] [] [] [.param "value"] ⟩
  ]

def pairWithSquareAlg90 : Algorithm :=
  .conditional none [] [
    ⟨ .group [.group [.bind "first", .bind "middle", .bind "last"]],
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

def mapEmptyAlg91 : Algorithm :=
  alg ["x"] [] [] [
    .call (resolve "take") (alg [] [] [] [
      .param "x",
      .num 0
    ])
  ]

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

#eval test85  -- should be true

-- Test 86: plain-call map preserves one grouped range item
def test86 : Bool :=
  match runFlat (.block (algPrivate [] [] [("TakeMiddle", takeMiddleGroupAlg85a)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5]),
      .resolve "TakeMiddle"
    ])
  ])) with
  | Except.ok [3] => true
  | _ => false

#eval test86  -- should be true

-- Test 86a: plain-call map does not silently flatten grouped range input for scalar transforms
def test86a : Bool :=
  match runResult (.block (algPrivate [] [] [("Double", doubleAlg85)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5]),
      .resolve "Double"
    ])
  ])) with
  | Except.error err =>
      hasContext "while evaluating map transform (map passes each iterated collection item as collected; ordinary boundaries stay whole and explicit result join/: iterate content)" err
      && innermostIsBadArity err
  | _ => false

#eval test86a  -- should be true

-- Test 87: grouped-only map branches now see one grouped range item
def test87 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Tag", tagAlg87)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1]),
      .resolve "Tag"
    ])
  ])) with
  | Except.ok [51] => true
  | _ => false

#eval test87  -- should be true

-- Test 88: empty grouped callback items project to zero outputs inside map
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
  | Except.ok (.group []) => true
  | _ => false

#eval test88  -- should be true

-- Test 89: grouped collection elements are passed to the transform as whole values
def test89 : Bool :=
  match runFlat (.block (algPrivate [] [] [("TakeValue", takePairValueAlg89)] [
    .call (resolve "map") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 10]),
      .block (alg [] [] [] [.num 2, .num 20]),
      .block (alg [] [] [] [.num 3, .num 30]),
      .resolve "TakeValue"
    ])
  ])) with
  | Except.ok [10, 20, 30] => true
  | _ => false

#eval test89  -- should be true

-- Test 90: grouped mapped results are accepted for one grouped range item
def test90 : Bool :=
  match runResult (.block (algPrivate [] [] [("PairWithSquare", pairWithSquareAlg90)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "PairWithSquare"
    ])
  ])) with
  | Except.ok (.group [.atom 1, .atom 3]) => true
  | _ => false

#eval test90  -- should be true

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

#eval test91  -- should be true

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

#eval test92  -- should be true

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

#eval test93  -- should be true

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

#eval test94  -- should be true

-- Test 95: descending ranges also expand for plain-call sum
def test95 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1])
    ])
  ])) with
  | Except.ok [15] => true
  | _ => false

#eval test95  -- should be true

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

#eval test96  -- should be true

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

#eval test97  -- should be true

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

#eval test98  -- should be true

-- Test 99: a single atomic value is treated as a one-element collection
def test99 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [.num 5])
  ])) with
  | Except.ok [5] => true
  | _ => false

#eval test99  -- should be true

-- Test 100: grouped top-level elements are rejected rather than flattened
def test100 : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [groupedPairs])
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test100  -- should be true

-- Test 101: string elements are rejected by sum
def test101 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#eval test101  -- should be true

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

#eval test102  -- should be true

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

#eval test103  -- should be true

-- Test 103a: dot-call count matches the shared grouped receiver examples
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
  | Except.ok [2, 1, 2, 1] => true
  | _ => false

#eval test103a  -- should be true

-- Test 103b: nested grouped receiver boundaries are preserved after one strip
def test103b : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runFlat (.block (alg [] [] [] [
    .dotCall groupedPairs "count" none,
    .dotCall (.block (alg [] [] [] [groupedPairs])) "count" none
  ])) with
  | Except.ok [2, 1] => true
  | _ => false

#eval test103b  -- should be true

-- Test 104: descending ranges still count all expanded top-level items
def test104 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1])
    ])
  ])) with
  | Except.ok [5] => true
  | _ => false

#eval test104  -- should be true

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

#eval test105  -- should be true

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

#eval test106  -- should be true

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

#eval test107  -- should be true

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

#eval test107a  -- should be true

-- Test 107b: count with no collection argument is still invalid
def test107b : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [])
  ])) with
  | Except.error _ => true
  | _ => false

#eval test107b  -- should be true

-- Test 108: a single grouped sequence argument counts as one top-level item
def test108 : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [groupedPairs])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test108  -- should be true

-- Test 109: a single atomic value is treated as a one-element collection
def test109 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [.num 5])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test109  -- should be true

-- Test 110: string elements are valid top-level elements for count
def test110 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test110  -- should be true

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

#eval test110a  -- should be true

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

#eval test110b  -- should be true

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

#eval test110c  -- should be true

-- Test 110d: contains compares grouped top-level items structurally
def test110d : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "contains") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test110d  -- should be true

-- Test 110e: contains searches top-level items only, not nested grouped members
def test110e : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runFlat (.block (alg [] [] [] [
    .call (resolve "contains") (alg [] [] [] [
      groupedPairs,
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.ok [0] => true
  | _ => false

#eval test110e  -- should be true

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

#eval test110f  -- should be true

-- Test 110g: contains preserves a grouped searched item from multi-output trailing args
def test110g : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Item", alg [] [] [] [.num 1, .num 2])
  ] [
    .call (resolve "contains") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .resolve "Item"
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test110g  -- should be true

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

#eval test111  -- should be true

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

#eval test112  -- should be true

-- Test 113: descending ranges also expand for plain-call min
def test113 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1])
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test113  -- should be true

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

#eval test114  -- should be true

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

#eval test115  -- should be true

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

#eval test116  -- should be true

-- Test 117: a single atomic value is treated as a one-element collection
def test117 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [.num 5])
  ])) with
  | Except.ok [5] => true
  | _ => false

#eval test117  -- should be true

-- Test 118: grouped top-level elements are rejected rather than flattened
def test118 : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [groupedPairs])
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test118  -- should be true

-- Test 119: string elements are rejected by min
def test119 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#eval test119  -- should be true

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

#eval test120  -- should be true

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

#eval test121  -- should be true

-- Test 122: descending ranges also expand for plain-call max
def test122 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1])
    ])
  ])) with
  | Except.ok [5] => true
  | _ => false

#eval test122  -- should be true

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

#eval test123  -- should be true

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

#eval test124  -- should be true

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

#eval test125  -- should be true

-- Test 126: a single atomic value is treated as a one-element collection
def test126 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [.num 5])
  ])) with
  | Except.ok [5] => true
  | _ => false

#eval test126  -- should be true

-- Test 127: grouped top-level elements are rejected rather than flattened
def test127 : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [groupedPairs])
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test127  -- should be true

-- Test 128: string elements are rejected by max
def test128 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#eval test128  -- should be true

-- Test 129: plain-call avg averages expanded range items
def test129 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5])
    ])
  ])) with
  | Except.ok [3] => true
  | _ => false

#eval test129  -- should be true

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

#eval test130  -- should be true

-- Test 131: descending ranges also expand for plain-call avg
def test131 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1])
    ])
  ])) with
  | Except.ok [3] => true
  | _ => false

#eval test131  -- should be true

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

#eval test132  -- should be true

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

#eval test133  -- should be true

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

#eval test134  -- should be true

-- Test 135: a single atomic value is treated as a one-element collection
def test135 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [.num 5])
  ])) with
  | Except.ok [5] => true
  | _ => false

#eval test135  -- should be true

-- Test 136: grouped top-level elements are rejected rather than flattened
def test136 : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [groupedPairs])
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test136  -- should be true

-- Test 137: string elements are rejected by avg
def test137 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#eval test137  -- should be true

--------------------------------------------------------------------------------
-- order builtins tests
--------------------------------------------------------------------------------

-- Test 138: ordinary builtin-call order sorts direct multi-argument inputs ascending and preserves duplicates
def test138 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [
      .num 3,
      .num 4,
      .num 2,
      .num 1,
      .num 3,
      .num 3
    ])
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#eval test138  -- should be true

-- Test 139: dot-call order sorts property output ascending
def test139 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .dotCall (.resolve "Values") "order" none
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#eval test139  -- should be true

-- Test 140: dot-call orderDesc sorts descending and preserves duplicates
def test140 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .dotCall (.resolve "Values") "orderDesc" none
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#eval test140  -- should be true

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

#eval test141  -- should be true

-- Test 142: dot-call order rejects empty receiver outputs with ordinary arity rules
def test142 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .dotCall
      (.call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ]))
      "order"
      none
  ])) with
  | Except.error err =>
      hasContext "while evaluating dotCall .order of (call)" err
        && innermostIsArityMismatch 0 0 err
  | _ => false

#eval test142  -- should be true

-- Test 143: unsupported sortable elements are rejected by order
def test143 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .stringLiteral "hello"])
    ])
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test143  -- should be true

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

#eval test144  -- should be true

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

#eval test145  -- should be true

-- Test 146: plain-call last returns the last expanded range item
def test146 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "last") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5])
    ])
  ])) with
  | Except.ok [5] => true
  | _ => false

#eval test146  -- should be true

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

#eval test147  -- should be true

-- Test 148: first preserves a single grouped sequence argument unchanged
def test148 : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "first") (alg [] [] [] [groupedPairs])
  ])) with
  | Except.ok (.group [
      .group [.atom 1, .atom 2],
      .group [.atom 3, .atom 4]
    ]) => true
  | _ => false

#eval test148  -- should be true

-- Test 149: last preserves a single grouped sequence argument unchanged
def test149 : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "last") (alg [] [] [] [groupedPairs])
  ])) with
  | Except.ok (.group [
      .group [.atom 1, .atom 2],
      .group [.atom 3, .atom 4]
    ]) => true
  | _ => false

#eval test149  -- should be true

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

#eval test150  -- should be true

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

#eval test151  -- should be true

-- Additional sequence-input builtin regression tests

def test151a : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#eval test151a  -- should be true

def test151b : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "orderDesc") (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#eval test151b  -- should be true

def test151c : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2])] [
    .call (resolve "order") (alg [] [] [] [.resolve "Values", .num 1, .num 3])
  ])) with
  | Except.ok [1, 2, 3, 3, 4] => true
  | _ => false

#eval test151c  -- should be true

def test151d : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test151d  -- should be true

def test151e : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "orderDesc") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test151e  -- should be true

def test151f : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "first") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ])) with
  | Except.ok (.group [.atom 1, .atom 2]) => true
  | _ => false

#eval test151f  -- should be true

def test151g : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "last") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ])) with
  | Except.ok (.group [.atom 3, .atom 4]) => true
  | _ => false

#eval test151g  -- should be true

def test151h : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [.num 10, .num 20, .num 30])
  ])) with
  | Except.ok [3] => true
  | _ => false

#eval test151h  -- should be true

def test151i : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ])) with
  | Except.ok [2] => true
  | _ => false

#eval test151i  -- should be true

def test151j : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [.num 10, .num 20, .num 30])
  ])) with
  | Except.ok [60] => true
  | _ => false

#eval test151j  -- should be true

def test151k : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [.num 10, .num 4, .num 7])
  ])) with
  | Except.ok [4] => true
  | _ => false

#eval test151k  -- should be true

def test151l : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [.num 10, .num 4, .num 7])
  ])) with
  | Except.ok [10] => true
  | _ => false

#eval test151l  -- should be true

def test151m : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [.num 10, .num 20, .num 30])
  ])) with
  | Except.ok [20] => true
  | _ => false

#eval test151m  -- should be true

def test151n : Bool :=
  match runFlat (.block (algPrivate [] [] [("KeepFourGroup", keepFourGroupAlg66c)] [
    .call (resolve "filter") (alg [] [] [] [
      .num 1,
      .num 2,
      .call (resolve "range") (alg [] [] [] [.num 3, .num 6]),
      .resolve "KeepFourGroup"
    ])
  ])) with
  | Except.ok [3, 4, 5, 6] => true
  | _ => false

#eval test151n  -- should be true

def test151o : Bool :=
  match runFlat (.block (algPrivate [] [] [("MarkThreeGroup", markThreeGroupAlg66e)] [
    .call (resolve "map") (alg [] [] [] [
      .num 1,
      .call (resolve "range") (alg [] [] [] [.num 2, .num 4]),
      .resolve "MarkThreeGroup"
    ])
  ])) with
  | Except.ok [0, 1] => true
  | _ => false

#eval test151o  -- should be true

def test151ob : Bool :=
  match runFlat (.block (algPrivate [] [] [("MarkThreeGroup", markThreeGroupAlg66e)] [
    .call (resolve "map") (alg [] [] [] [
      .resultJoin
        (.num 1)
        (.call (resolve "range") (alg [] [] [] [.num 2, .num 4])),
      .resolve "MarkThreeGroup"
    ])
  ])) with
  | Except.ok [0, 0, 0, 0] => true
  | _ => false

#eval test151ob  -- should be true

def test151oc : Bool :=
  match runFlat (.block (algPrivate [] [] [("MarkThreeGroup", markThreeGroupAlg66e)] [
    .call (resolve "filter") (alg [] [] [] [
      .resultJoin
        (.num 1)
        (.call (resolve "range") (alg [] [] [] [.num 2, .num 4])),
      .resolve "MarkThreeGroup"
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#eval test151oc  -- should be true

def markGroupedRangeDirectCallAlg151oa : Algorithm :=
  .conditional none [] [
    ⟨ .group [.group [.bind "a", .bind "b", .bind "c"]],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def test151oa : Bool :=
  match runFlat (.block (algPrivate [] [] [("MarkGroupedRange", markGroupedRangeDirectCallAlg151oa)] [
    .call (resolve "MarkGroupedRange") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3])
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test151oa  -- should be true

def test151p : Bool :=
  match runFlat (.block (algPrivate [] [] [("AddItemCount", addItemCountAlg80c)] [
    .call (resolve "reduce") (alg [] [] [] [
      .num 1,
      .num 2,
      .call (resolve "range") (alg [] [] [] [.num 3, .num 4]),
      .resolve "AddItemCount",
      .num 0
    ])
  ])) with
  | Except.ok [4] => true
  | _ => false

#eval test151p  -- should be true

def addGroupedRangeAlg151pb : Algorithm :=
  .conditional none [] [
    ⟨ .group [.group [.bind "a", .bind "b", .bind "c"], .bind "acc"],
      alg [] [] [] [.binary .add (.param "acc") (.num 100)] ⟩,
    ⟨ .group [.bind "x", .bind "acc"],
      alg [] [] [] [.binary .add (.param "acc") (.param "x")] ⟩
  ]

def test151pb : Bool :=
  match runFlat (.block (algPrivate [] [] [("AddGroupedRange", addGroupedRangeAlg151pb)] [
    .call (resolve "reduce") (alg [] [] [] [
      .num 1,
      .call (resolve "range") (alg [] [] [] [.num 2, .num 4]),
      .resolve "AddGroupedRange",
      .num 0
    ])
  ])) with
  | Except.ok [101] => true
  | _ => false

#eval test151pb  -- should be true

def test151pc : Bool :=
  match runFlat (.block (algPrivate [] [] [("AddGroupedRange", addGroupedRangeAlg151pb)] [
    .call (resolve "reduce") (alg [] [] [] [
      .resultJoin
        (.num 1)
        (.call (resolve "range") (alg [] [] [] [.num 2, .num 4])),
      .resolve "AddGroupedRange",
      .num 0
    ])
  ])) with
  | Except.ok [10] => true
  | _ => false

#eval test151pc  -- should be true

def test151q : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [
      .block (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])
    ])
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test151q  -- should be true

def test151r : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .call (resolve "order") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#eval test151r  -- should be true

def test151s : Bool :=
  match runResult (.block (algPrivate [] [] [("Values", alg [] [] [] [.block (alg [] [] [] [.num 3, .num 4, .num 2])])] [
    .call (resolve "order") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test151s  -- should be true

def test151t : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "orderDesc") (alg [] [] [] [
      .block (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])
    ])
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test151t  -- should be true

def test151u : Bool :=
  match runFlat (.block (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .call (resolve "orderDesc") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#eval test151u  -- should be true

def test151v : Bool :=
  match runResult (.block (algPrivate [] [] [("Values", alg [] [] [] [.block (alg [] [] [] [.num 3, .num 4, .num 2])])] [
    .call (resolve "orderDesc") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test151v  -- should be true

def test151w : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test151w  -- should be true

def test151x : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "first") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.ok (.group [.atom 1, .atom 2]) => true
  | _ => false

#eval test151x  -- should be true

def test151y : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "last") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.ok (.group [.atom 1, .atom 2]) => true
  | _ => false

#eval test151y  -- should be true

-- Additional uniform sequence-extraction wrapper regressions

def test152 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("KeepSecondEven", evenPredicateAlg19d),
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ] [
    .call (resolve "filter") (alg [] [] [] [
      .resolve "Values",
      .resolve "KeepSecondEven"
    ])
  ])) with
  | Except.ok (.group [.atom 1, .atom 2]) => true
  | _ => false

#eval test152  -- should be true

def test153 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("TakeValue", takePairValueAlg89),
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ] [
    .call (resolve "map") (alg [] [] [] [
      .resolve "Values",
      .resolve "TakeValue"
    ])
  ])) with
  | Except.ok [2] => true
  | _ => false

#eval test153  -- should be true

def test154 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("AddValue", reduceGroupedItemAlg79),
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ] [
    .call (resolve "reduce") (alg [] [] [] [
      .resolve "Values",
      .resolve "AddValue",
      .num 0
    ])
  ])) with
  | Except.ok [2] => true
  | _ => false

#eval test154  -- should be true

def test155 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2, .num 3])
    ])
  ] [
    .call (resolve "count") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test155  -- should be true

def test156 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .call (resolve "count") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [3] => true
  | _ => false

#eval test156  -- should be true

def test157 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ] [
    .call (resolve "first") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok (.group [.atom 1, .atom 2]) => true
  | _ => false

#eval test157  -- should be true

def test158 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ] [
    .call (resolve "last") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok (.group [.atom 1, .atom 2]) => true
  | _ => false

#eval test158  -- should be true

def test159 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 10, .num 20, .num 30])
    ])
  ] [
    .call (resolve "sum") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test159  -- should be true

def test160 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 10, .num 20, .num 30])
    ])
  ] [
    .call (resolve "min") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test160  -- should be true

def test161 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 10, .num 20, .num 30])
    ])
  ] [
    .call (resolve "max") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test161  -- should be true

def test162 : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .block (alg [] [] [] [.num 10, .num 20, .num 30])
    ])
  ] [
    .call (resolve "avg") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 0 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test162  -- should be true

def test163 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 20, .num 30])
  ] [
    .call (resolve "sum") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [60] => true
  | _ => false

#eval test163  -- should be true

def test164 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 4, .num 7])
  ] [
    .call (resolve "min") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [4] => true
  | _ => false

#eval test164  -- should be true

def test165 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 4, .num 7])
  ] [
    .call (resolve "max") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [10] => true
  | _ => false

#eval test165  -- should be true

def test166 : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 20, .num 30])
  ] [
    .call (resolve "avg") (alg [] [] [] [.resolve "Values"])
  ])) with
  | Except.ok [20] => true
  | _ => false

#eval test166  -- should be true

def test167 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .dotCall
      (.call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ]))
      "orderDesc"
      none
  ])) with
  | Except.error err =>
      hasContext "while evaluating dotCall .orderDesc of (call)" err
        && innermostIsArityMismatch 0 0 err
  | _ => false

#eval test167  -- should be true

def test168 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [.num 1, .num 2])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test168  -- should be true

def test169 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [.num (-1), .num (-2)])
  ])) with
  | Except.ok [-2] => true
  | _ => false

#eval test169  -- should be true

def test170 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ])
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 1 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test170  -- should be true

def test171 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "orderDesc") (alg [] [] [] [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ])
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 1 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test171  -- should be true

def test172 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ])
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 1 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test172  -- should be true

def test173 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ])
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 1 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test173  -- should be true

def test174 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ])
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 1 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test174  -- should be true

def test175 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [
      .num 1,
      .block (alg [] [] [] [.num 2, .num 3])
    ])
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 1 was grouped value" err && innermostIsBadArity err
  | _ => false

#eval test175  -- should be true

def test176 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3,
      .num 4,
      .num 5,
      .num 3
    ])
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#eval test176  -- should be true

def test177 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3,
      .num 4,
      .num 5,
      .num 3
    ])
  ])) with
  | Except.ok [4, 5] => true
  | _ => false

#eval test177  -- should be true

def test178 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3,
      .num 0
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#eval test178  -- should be true

def test179 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3,
      .num 0
    ])
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#eval test179  -- should be true

def test180 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3,
      .num (-2)
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#eval test180  -- should be true

def test181 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3,
      .num (-2)
    ])
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#eval test181  -- should be true

def test182 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3,
      .num 10
    ])
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#eval test182  -- should be true

def test183 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3,
      .num 10
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#eval test183  -- should be true

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

#eval test184  -- should be true

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

#eval test185  -- should be true

def test186 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4]),
      .num 1
    ])
  ])) with
  | Except.ok (.group [.atom 1, .atom 2]) => true
  | _ => false

#eval test186  -- should be true

def test187 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4]),
      .num 1
    ])
  ])) with
  | Except.ok (.group [.atom 3, .atom 4]) => true
  | _ => false

#eval test187  -- should be true

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
  | Except.ok (.group [.atom 1, .atom 2, .atom 3]) => true
  | _ => false

#eval test188  -- should be true

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

#eval test189  -- should be true

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
  | Except.ok [] => true
  | _ => false

#eval test190  -- should be true

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

#eval test191  -- should be true

def test192 : Bool :=
  match runResult (.block (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "take") (alg [] [] [] [
      .num 1,
      .num 2,
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "AlwaysFalse"
      ])
    ])
  ])) with
  | Except.error err => hasContext "take count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#eval test192  -- should be true

def test193 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "take") (alg [] [] [] [
      .num 3,
      .num 4,
      .block (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.error err => hasContext "take count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#eval test193  -- should be true

def test194 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      .num 1,
      .num 2,
      .stringLiteral "hello"
    ])
  ])) with
  | Except.error err => hasContext "skip count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#eval test194  -- should be true

def test195 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "skip") (alg [] [] [] [
      .num 3,
      .num 4,
      .call (resolve "range") (alg [] [] [] [.num 1, .num 2])
    ])
  ])) with
  | Except.error err => hasContext "skip count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#eval test195  -- should be true

def test196 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "distinct") (alg [] [] [] [
      .num 3,
      .num 1,
      .num 3,
      .num 2,
      .num 1,
      .num 2
    ])
  ])) with
  | Except.ok [3, 1, 2] => true
  | _ => false

#eval test196  -- should be true

def test197 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "distinct") (alg [] [] [] [
      .num 4,
      .num 4,
      .num 4,
      .num 4
    ])
  ])) with
  | Except.ok [4] => true
  | _ => false

#eval test197  -- should be true

def test198 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "distinct") (alg [] [] [] [
      .num 1,
      .num 2,
      .num 3
    ])
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#eval test198  -- should be true

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

#eval test199  -- should be true

def test200 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "distinct") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ])) with
  | Except.ok (.group [
      .group [.atom 1, .atom 2],
      .group [.atom 3, .atom 4]
    ]) => true
  | _ => false

#eval test200  -- should be true

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
  | Except.ok (.group [
      .group [.atom 1, .atom 2],
      .group [.atom 1, .atom 2],
      .group [.atom 3, .atom 4]
    ]) => true
  | _ => false

#eval test201  -- should be true

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
  | Except.ok (.group [
      .group [.atom 1, .atom 2],
      .group [.atom 3, .atom 4]
    ]) => true
  | _ => false

#eval test202  -- should be true

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

#eval test203  -- should be true

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

#eval test204  -- should be true

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

#eval test205  -- should be true

def test206 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [
    .num 3,
    .num 5,
    .num 3
  ])) "sum" none) with
  | Except.ok [11] => true
  | _ => false

#eval test206  -- should be true

def test207 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [
    .num 1,
    .num 2,
    .num 1,
    .num 3
  ])) "distinct" none) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#eval test207  -- should be true

def test208 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [
    .num 1,
    .num 2,
    .num 3
  ])) "take" (some (alg [] [] [] [.num 2]))) with
  | Except.ok [1, 2] => true
  | _ => false

#eval test208  -- should be true

def test209 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [
    .num 1,
    .num 2,
    .num 3
  ])) "skip" (some (alg [] [] [] [.num 1]))) with
  | Except.ok [2, 3] => true
  | _ => false

#eval test209  -- should be true

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

#eval test210  -- should be true

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

#eval test211  -- should be true

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

#eval test212  -- should be true

def test213 : Bool :=
  match runFlat (.dotCall (.block (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 3, .num 1, .num 2])
  ] [
    .resolve "Values"
  ])) "order" none) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#eval test213  -- should be true

def test214 : Bool :=
  let inlineReceiver := .block (alg [] [] [] [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ])
  let groupedReceiver := .block (alg [] [] [] [inlineReceiver])
  let namedGroupedFails :=
    match runResult (.block (algPrivate [] [] [
      ("Data", alg [] [] [] [inlineReceiver])
    ] [
      .dotCall (.resolve "Data") "order" none
    ])) with
    | Except.error err =>
        hasContext "order expects each collection element to be a single numeric value; item 0 was grouped value" err
          && innermostIsBadArity err
    | _ => false
  let inlineReceiverWorks :=
    match runFlat (.dotCall inlineReceiver "order" none) with
    | Except.ok [3, 3, 3, 5, 6] => true
    | _ => false
  let doubleParenReceiverFails :=
    match runResult (.dotCall groupedReceiver "order" none) with
    | Except.error err =>
        hasContext "order expects each collection element to be a single numeric value; item 0 was grouped value" err
          && innermostIsBadArity err
    | _ => false
  namedGroupedFails && inlineReceiverWorks && doubleParenReceiverFails

#eval test214  -- should be true

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

#eval test215  -- should be true

def test215a : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [.num 7, .num 8])
  ] [
    .index (.resolve "A") (.num 0)
  ])) with
  | Except.ok (.atom 7) => true
  | _ => false

#eval test215a  -- should be true

def test215b : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("A", alg [] [] [] [
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4])
    ])
  ] [
    .index (.resolve "A") (.num 0)
  ])) with
  | Except.ok (.group [.atom 1, .atom 2]) => true
  | _ => false

#eval test215b  -- should be true

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

#eval test215c  -- should be true

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

#eval test215cWrappedProjectionBoundary  -- should be true

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
  | Except.ok (.group [
      .group [.atom 1, .atom 2],
      .group [.atom 3, .atom 4]
    ]) => true
  | _ => false

#eval test215d  -- should be true

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
  | Except.ok (.group [.atom 3, .atom 4]) => true
  | _ => false

#eval test215e  -- should be true

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

#eval test215f  -- should be true

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
      hasContext "sum expects each collection element to be a single numeric value; item 0 was grouped value" err
        && innermostIsBadArity err
  | _ => false

#eval test215g  -- should be true

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
  | Except.ok (.group [
      .group [.atom 4, .atom 5, .atom 4, .atom 6],
      .group [.atom 4, .atom 5, .atom 4, .atom 6],
      .group [.atom 4, .atom 5, .atom 4, .atom 6],
      .group [.atom 4, .atom 5, .atom 4, .atom 6],
      .group []
    ]) => true
  | _ => false

#eval test216  -- should be true

def test217 : Bool :=
  let runBuiltin := fun (name : String) =>
    runResult (.block (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .block (alg [] [] [] [.num 10, .num 20, .num 30])
      ])
    ] [
      .dotCall (.resolve "Values") name none
    ]))
  let minFails :=
    match runBuiltin "min" with
    | Except.error err =>
        hasContext "min expects each collection element to be a single numeric value; item 0 was grouped value" err
          && innermostIsBadArity err
    | _ => false
  let maxFails :=
    match runBuiltin "max" with
    | Except.error err =>
        hasContext "max expects each collection element to be a single numeric value; item 0 was grouped value" err
          && innermostIsBadArity err
    | _ => false
  let sumFails :=
    match runBuiltin "sum" with
    | Except.error err =>
        hasContext "sum expects each collection element to be a single numeric value; item 0 was grouped value" err
          && innermostIsBadArity err
    | _ => false
  let avgFails :=
    match runBuiltin "avg" with
    | Except.error err =>
        hasContext "avg expects each collection element to be a single numeric value; item 0 was grouped value" err
          && innermostIsBadArity err
    | _ => false
  let orderFails :=
    match runBuiltin "order" with
    | Except.error err =>
        hasContext "order expects each collection element to be a single numeric value; item 0 was grouped value" err
          && innermostIsBadArity err
    | _ => false
  let orderDescFails :=
    match runBuiltin "orderDesc" with
    | Except.error err =>
        hasContext "orderDesc expects each collection element to be a single numeric value; item 0 was grouped value" err
          && innermostIsBadArity err
    | _ => false
  minFails && maxFails && sumFails && avgFails && orderFails && orderDescFails

#eval test217  -- should be true

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
        (.call (.resolve "count") (alg [] [] [] [.param "item"]))
        (.param "acc")
    ]
  let filterResult :=
    runResult (.block (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2])
      ]),
      ("KeepSecondEven", keepSecondEven)
    ] [
      .dotCall (.resolve "Values") "filter" (some (alg [] [] [] [.resolve "KeepSecondEven"]))
    ]))
  let mapResult :=
    runResult (.block (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2, .num 3])
      ]),
      ("TakeFirst", takeFirstAlg)
    ] [
      .dotCall (.resolve "Values") "map" (some (alg [] [] [] [.resolve "TakeFirst"]))
    ]))
  let reduceResult :=
    runFlat (.block (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .block (alg [] [] [] [.num 1, .num 2, .num 3])
      ]),
      ("AddItemCount", addItemCount)
    ] [
      .dotCall (.resolve "Values") "reduce" (some (alg [] [] [] [.resolve "AddItemCount", .num 0]))
    ]))
  let filterOk :=
    match filterResult with
    | Except.ok (.group [.atom 1, .atom 2]) => true
    | _ => false
  let mapOk :=
    match mapResult with
    | Except.ok (.atom 1) => true
    | _ => false
  let reduceOk :=
    match reduceResult with
    | Except.ok [3] => true
    | _ => false
  filterOk && mapOk && reduceOk

#eval test218  -- should be true

def test219 : Bool :=
  match runResult (.dotCall (.block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])) "sum" none) with
  | Except.error err =>
      hasContext "sum expects each collection element to be a single numeric value; item 0 was grouped value" err
        && innermostIsBadArity err
  | _ => false

#eval test219  -- should be true

--------------------------------------------------------------------------------
-- Sequence-boundary cleanup regressions
--------------------------------------------------------------------------------

def test228 : Bool :=
  match runFlat (.call (resolve "count") (alg [] [] [] [
    .num 3,
    .num 4,
    .call (resolve "range") (alg [] [] [] [.num 1, .num 5]),
    .num 7
  ])) with
  | Except.ok [8] => true
  | _ => false

#eval test228  -- should be true

def test229 : Bool :=
  let groupedRange := .block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4, .num 5])
  match runFlat (.block (alg [] [] [] [
    .call (resolve "contains") (alg [] [] [] [
      .num 3,
      .num 4,
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5]),
      .num 7,
      .num 5
    ]),
    .call (resolve "contains") (alg [] [] [] [
      .num 3,
      .num 4,
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5]),
      .num 7,
      groupedRange
    ])
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#eval test229  -- should be true

def test230 : Bool :=
  match runFlat (.call (resolve "order") (alg [] [] [] [
    .num 3,
    .num 4,
    .call (resolve "range") (alg [] [] [] [.num 1, .num 5]),
    .num 7
  ])) with
  | Except.ok [1, 2, 3, 3, 4, 4, 5, 7] => true
  | _ => false

#eval test230  -- should be true

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

#eval test231  -- should be true

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
      firstReport,
      secondReport,
      .resolve "IsSafe"
    ])
  ])) with
  | Except.ok (.group [.atom 7, .atom 6, .atom 4, .atom 2, .atom 1]) => true
  | _ => false

#eval test232  -- should be true

def test233 : Bool :=
  let takeFirstProjected : Algorithm :=
    alg ["report"] [] [] [
      .index (.param "report") (.num 0)
    ]
  match runFlat (.block (algPrivate [] [] [
    ("TakeFirst", takeFirstProjected)
  ] [
    .call (resolve "map") (alg [] [] [] [
      .block (alg [] [] [] [.num 7, .num 6, .num 4, .num 2, .num 1]),
      .block (alg [] [] [] [.num 1, .num 2, .num 7, .num 8, .num 9]),
      .resolve "TakeFirst"
    ])
  ])) with
  | Except.ok [7, 1] => true
  | _ => false

#eval test233  -- should be true

def test234 : Bool :=
  let countItem : Algorithm :=
    alg ["x"] [] [] [
      .dotCall (.param "x") "count" none
    ]
  match runFlat (.block (algPrivate [] [] [
    ("Items", alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .num 7
    ]),
    ("CountItem", countItem)
  ] [
    .dotCall (.resolve "Items") "count" none,
    .dotCall (.index (.resolve "Items") (.num 0)) "count" none,
    .dotCall (.index (.resolve "Items") (.num 1)) "count" none,
    .dotCall (.resolve "Items") "map" (some (alg [] [] [] [.resolve "CountItem"]))
  ])) with
  | Except.ok [2, 3, 1, 3, 1] => true
  | _ => false

#eval test234  -- should be true

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
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .num 7
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
  | Except.ok [1, 7, 1] => true
  | _ => false

#eval test235  -- should be true

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
      .block (alg [] [] [] [.num 1, .num 2]),
      .block (alg [] [] [] [.num 3, .num 4]),
      .resolve "Signature",
      .num 0
    ])
  ])) with
  | Except.ok [2, 3, 2, 7, 2327, 2327] => true
  | _ => false

#eval test236  -- should be true

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
  | Except.ok [2, 22, 22] => true
  | _ => false

#eval test237  -- should be true

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
  | Except.ok (.group [.atom 2121, .atom 1]) => true
  | _ => false

#eval test238  -- should be true

--------------------------------------------------------------------------------
-- Sequence builtin dot-call regression sweep
--------------------------------------------------------------------------------

private def dotSweepAtomsAlg (xs : List Int) : Algorithm :=
  alg [] [] [] (xs.map (fun value => .num value))

private def dotSweepGroupedExpr (xs : List Int) : KatLang.Expr :=
  KatLang.block (dotSweepAtomsAlg xs)

private def dotSweepGroupedAlg (xs : List Int) : Algorithm :=
  alg [] [] [] [dotSweepGroupedExpr xs]

private def dotSweepPairAlg (first second : List Int) : Algorithm :=
  alg [] [] [] [dotSweepGroupedExpr first, dotSweepGroupedExpr second]

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
    ("Grouped", dotSweepGroupedAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [3, 1, 2] [9, 8, 7])
  ] [
    .dotCall (resolve "Values") "count" none,
    .call (resolve "count") (alg [] [] [] [resolve "Values"]),
    .dotCall (resolve "Grouped") "count" none,
    .call (resolve "count") (alg [] [] [] [resolve "Grouped"]),
    .dotCall data0 "count" none,
    .call (resolve "count") (alg [] [] [] [data0])
  ])) with
  | Except.ok [3, 3, 1, 1, 3, 3] => true
  | _ => false

#eval sequenceBuiltinDotCallCountSweep  -- should be true

def sequenceBuiltinDotCallContainsSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.block (algPrivate [] [] [
    ("Values", dotSweepAtomsAlg [1, 2, 3]),
    ("Grouped", dotSweepGroupedAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [3, 1, 2] [9, 8, 7])
  ] [
    .dotCall (resolve "Values") "contains" (some (alg [] [] [] [.num 2])),
    .call (resolve "contains") (alg [] [] [] [resolve "Values", .num 2]),
    .dotCall (resolve "Grouped") "contains" (some (alg [] [] [] [.num 2])),
    .dotCall (resolve "Grouped") "contains" (some (alg [] [] [] [dotSweepGroupedExpr [1, 2, 3]])),
    .dotCall data0 "contains" (some (alg [] [] [] [.num 2])),
    .call (resolve "contains") (alg [] [] [] [data0, .num 2])
  ])) with
  | Except.ok [1, 1, 0, 1, 1, 1] => true
  | _ => false

#eval sequenceBuiltinDotCallContainsSweep  -- should be true

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

#eval sequenceBuiltinDotCallOrderSweep  -- should be true

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
  let groupedOrder :=
    match runResult (.block (algPrivate [] [] [
      ("Grouped", dotSweepGroupedAlg [3, 1, 2])
    ] [
      .dotCall (resolve "Grouped") "order" none
    ])) with
    | Except.error err =>
        hasContext "order expects each collection element to be a single numeric value; item 0 was grouped value" err &&
        innermostIsBadArity err
    | _ => false
  let groupedOrderDesc :=
    match runResult (.block (algPrivate [] [] [
      ("Grouped", dotSweepGroupedAlg [3, 1, 2])
    ] [
      .dotCall (resolve "Grouped") "orderDesc" none
    ])) with
    | Except.error err =>
        hasContext "orderDesc expects each collection element to be a single numeric value; item 0 was grouped value" err &&
        innermostIsBadArity err
    | _ => false
  orderValues && orderDescValues && groupedOrder && groupedOrderDesc

#eval sequenceBuiltinDotCallOrderBoundarySweep  -- should be true

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

#eval sequenceBuiltinDotCallFirstLastSweep  -- should be true

def sequenceBuiltinDotCallFirstLastGroupedSweep : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Grouped", dotSweepGroupedAlg [5, 6, 7])
  ] [
    .dotCall (resolve "Grouped") "first" none,
    .call (resolve "first") (alg [] [] [] [resolve "Grouped"]),
    .dotCall (resolve "Grouped") "last" none,
    .call (resolve "last") (alg [] [] [] [resolve "Grouped"])
  ])) with
  | Except.ok (.group [
      .group [.atom 5, .atom 6, .atom 7],
      .group [.atom 5, .atom 6, .atom 7],
      .group [.atom 5, .atom 6, .atom 7],
      .group [.atom 5, .atom 6, .atom 7]
    ]) => true
  | _ => false

#eval sequenceBuiltinDotCallFirstLastGroupedSweep  -- should be true

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

#eval sequenceBuiltinDotCallDistinctSweep  -- should be true

def sequenceBuiltinDotCallDistinctGroupedSweep : Bool :=
  match runResult (.block (algPrivate [] [] [
    ("Grouped", dotSweepGroupedAlg [1, 2, 1, 3])
  ] [
    .dotCall (resolve "Grouped") "distinct" none,
    .call (resolve "distinct") (alg [] [] [] [resolve "Grouped"])
  ])) with
  | Except.ok (.group [
      .group [.atom 1, .atom 2, .atom 1, .atom 3],
      .group [.atom 1, .atom 2, .atom 1, .atom 3]
    ]) => true
  | _ => false

#eval sequenceBuiltinDotCallDistinctGroupedSweep  -- should be true

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

#eval sequenceBuiltinDotCallTakeSkipSweep  -- should be true

def sequenceBuiltinDotCallTakeSkipGroupedSweep : Bool :=
  let takeOk :=
    match runResult (.block (algPrivate [] [] [
      ("Grouped", dotSweepGroupedAlg [1, 2, 3])
    ] [
      .dotCall (resolve "Grouped") "take" (some (alg [] [] [] [.num 2])),
      .call (resolve "take") (alg [] [] [] [resolve "Grouped", .num 2])
    ])) with
    | Except.ok (.group [
        .group [.atom 1, .atom 2, .atom 3],
        .group [.atom 1, .atom 2, .atom 3]
      ]) => true
    | _ => false
  let skipDotOk :=
    match runFlat (.block (algPrivate [] [] [
      ("Grouped", dotSweepGroupedAlg [1, 2, 3])
    ] [
      .dotCall (resolve "Grouped") "skip" (some (alg [] [] [] [.num 1]))
    ])) with
    | Except.ok [] => true
    | _ => false
  let skipPlainOk :=
    match runFlat (.block (algPrivate [] [] [
      ("Grouped", dotSweepGroupedAlg [1, 2, 3])
    ] [
      .call (resolve "skip") (alg [] [] [] [resolve "Grouped", .num 1])
    ])) with
    | Except.ok [] => true
    | _ => false
  takeOk && skipDotOk && skipPlainOk

#eval sequenceBuiltinDotCallTakeSkipGroupedSweep  -- should be true

def sequenceBuiltinDotCallInlineReceiverSweep : Bool :=
  match runFlat (.block (algPrivate [] [] [
    ("AddOne", dotSweepAddOneAlg),
    ("IsLarge", dotSweepIsGreaterThanOneAlg),
    ("Add", dotSweepAddAlg)
  ] [
    .dotCall (dotSweepGroupedExpr [1, 2, 3]) "count" none,
    .dotCall (dotSweepGroupedExpr [1, 2, 3]) "contains" (some (alg [] [] [] [.num 2])),
    .dotCall (dotSweepGroupedExpr [3, 1, 2]) "order" none,
    .dotCall (dotSweepGroupedExpr [5, 6, 7]) "first" none,
    .dotCall (dotSweepGroupedExpr [5, 6, 7]) "last" none,
    .dotCall (dotSweepGroupedExpr [1, 2, 1, 3]) "distinct" none,
    .dotCall (dotSweepGroupedExpr [1, 2, 3]) "take" (some (alg [] [] [] [.num 2])),
    .dotCall (dotSweepGroupedExpr [1, 2, 3]) "skip" (some (alg [] [] [] [.num 1])),
    .dotCall (dotSweepGroupedExpr [10, 4, 7]) "min" none,
    .dotCall (dotSweepGroupedExpr [10, 4, 7]) "max" none,
    .dotCall (dotSweepGroupedExpr [3, 5, 3]) "sum" none,
    .dotCall (dotSweepGroupedExpr [10, 4, 7]) "avg" none,
    .dotCall (dotSweepGroupedExpr [1, 2, 3]) "map" (some (alg [] [] [] [resolve "AddOne"])),
    .dotCall (dotSweepGroupedExpr [1, 2, 3, 4]) "filter" (some (alg [] [] [] [resolve "IsLarge"])),
    .dotCall (dotSweepGroupedExpr [1, 2, 3]) "reduce" (some (alg [] [] [] [resolve "Add", .num 0]))
  ])) with
  | Except.ok [3, 1, 1, 2, 3, 5, 7, 1, 2, 3, 1, 2, 2, 3, 4, 10, 11, 7, 2, 3, 4, 2, 3, 4, 6] => true
  | _ => false

#eval sequenceBuiltinDotCallInlineReceiverSweep  -- should be true

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

#eval sequenceBuiltinDotCallNumericAggregationSweep  -- should be true

def sequenceBuiltinDotCallNumericAggregationBoundarySweep : Bool :=
  let sumValues :=
    match runFlat (.block (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "sum") (alg [] [] [] [resolve "Values"])
    ])) with
    | Except.ok [6] => true
    | _ => false
  let sumGrouped :=
    match runResult (.block (algPrivate [] [] [
      ("Grouped", dotSweepGroupedAlg [1, 2, 3])
    ] [
      .dotCall (resolve "Grouped") "sum" none
    ])) with
    | Except.error err =>
        hasContext "sum expects each collection element to be a single numeric value; item 0 was grouped value" err &&
        innermostIsBadArity err
    | _ => false
  let avgValues :=
    match runFlat (.block (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "avg") (alg [] [] [] [resolve "Values"])
    ])) with
    | Except.ok [2] => true
    | _ => false
  let avgGrouped :=
    match runResult (.block (algPrivate [] [] [
      ("Grouped", dotSweepGroupedAlg [1, 2, 3])
    ] [
      .dotCall (resolve "Grouped") "avg" none
    ])) with
    | Except.error err =>
        hasContext "avg expects each collection element to be a single numeric value; item 0 was grouped value" err &&
        innermostIsBadArity err
    | _ => false
  let minValues :=
    match runFlat (.block (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "min") (alg [] [] [] [resolve "Values"])
    ])) with
    | Except.ok [1] => true
    | _ => false
  let minGrouped :=
    match runResult (.block (algPrivate [] [] [
      ("Grouped", dotSweepGroupedAlg [1, 2, 3])
    ] [
      .dotCall (resolve "Grouped") "min" none
    ])) with
    | Except.error err =>
        hasContext "min expects each collection element to be a single numeric value; item 0 was grouped value" err &&
        innermostIsBadArity err
    | _ => false
  let maxValues :=
    match runFlat (.block (algPrivate [] [] [
      ("Values", dotSweepAtomsAlg [1, 2, 3])
    ] [
      .call (resolve "max") (alg [] [] [] [resolve "Values"])
    ])) with
    | Except.ok [3] => true
    | _ => false
  let maxGrouped :=
    match runResult (.block (algPrivate [] [] [
      ("Grouped", dotSweepGroupedAlg [1, 2, 3])
    ] [
      .dotCall (resolve "Grouped") "max" none
    ])) with
    | Except.error err =>
        hasContext "max expects each collection element to be a single numeric value; item 0 was grouped value" err &&
        innermostIsBadArity err
    | _ => false
  sumValues && sumGrouped && avgValues && avgGrouped && minValues && minGrouped && maxValues && maxGrouped

#eval sequenceBuiltinDotCallNumericAggregationBoundarySweep  -- should be true

def sequenceBuiltinDotCallMapSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.block (algPrivate [] [] [
    ("ItemCount", dotSweepTopLevelItemCountAlg),
    ("AddOne", dotSweepAddOneAlg),
    ("Items", alg [] [] [] [dotSweepGroupedExpr [1, 2, 3], .num 7]),
    ("Grouped", dotSweepGroupedAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [1, 2, 3] [4, 5, 6])
  ] [
    .dotCall (resolve "Items") "map" (some (alg [] [] [] [resolve "ItemCount"])),
    .call (resolve "map") (alg [] [] [] [resolve "Items", resolve "ItemCount"]),
    .dotCall (resolve "Grouped") "map" (some (alg [] [] [] [resolve "ItemCount"])),
    .call (resolve "map") (alg [] [] [] [resolve "Grouped", resolve "ItemCount"]),
    .dotCall data0 "map" (some (alg [] [] [] [resolve "AddOne"])),
    .call (resolve "map") (alg [] [] [] [data0, resolve "AddOne"])
  ])) with
  | Except.ok [3, 1, 2, 3, 3, 2, 3, 4, 2, 3, 4] => true
  | _ => false

#eval sequenceBuiltinDotCallMapSweep  -- should be true

def sequenceBuiltinDotCallFilterSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.block (algPrivate [] [] [
    ("KeepCountThree", dotSweepKeepCountThreeAlg),
    ("IsLarge", dotSweepIsGreaterThanOneAlg),
    ("Items", alg [] [] [] [dotSweepGroupedExpr [1, 2, 3], dotSweepGroupedExpr [4, 5, 6], .num 7]),
    ("Grouped", dotSweepGroupedAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [1, 2, 3] [4, 5, 6])
  ] [
    .dotCall (.dotCall (resolve "Items") "filter" (some (alg [] [] [] [resolve "KeepCountThree"]))) "count" none,
    .dotCall (.call (resolve "filter") (alg [] [] [] [resolve "Items", resolve "KeepCountThree"])) "count" none,
    .dotCall (.dotCall (resolve "Grouped") "filter" (some (alg [] [] [] [resolve "KeepCountThree"]))) "count" none,
    .dotCall (.call (resolve "filter") (alg [] [] [] [resolve "Grouped", resolve "KeepCountThree"])) "count" none,
    .dotCall (.dotCall data0 "filter" (some (alg [] [] [] [resolve "IsLarge"]))) "count" none,
    .dotCall (.call (resolve "filter") (alg [] [] [] [data0, resolve "IsLarge"])) "count" none
  ])) with
  | Except.ok [2, 1, 1, 1, 2, 2] => true
  | _ => false

#eval sequenceBuiltinDotCallFilterSweep  -- should be true

def sequenceBuiltinDotCallReduceSweep : Bool :=
  let data0 := .index (resolve "Data") (.num 0)
  match runFlat (.block (algPrivate [] [] [
    ("AddItemCount", dotSweepAddTopLevelItemCountAlg),
    ("Add", dotSweepAddAlg),
    ("Items", alg [] [] [] [dotSweepGroupedExpr [1, 2, 3], .num 7]),
    ("Grouped", dotSweepGroupedAlg [1, 2, 3]),
    ("Data", dotSweepPairAlg [1, 2, 3] [4, 5, 6])
  ] [
    .dotCall (resolve "Items") "reduce" (some (alg [] [] [] [resolve "AddItemCount", .num 0])),
    .call (resolve "reduce") (alg [] [] [] [resolve "Items", resolve "AddItemCount", .num 0]),
    .dotCall (resolve "Grouped") "reduce" (some (alg [] [] [] [resolve "AddItemCount", .num 0])),
    .call (resolve "reduce") (alg [] [] [] [resolve "Grouped", resolve "AddItemCount", .num 0]),
    .dotCall data0 "reduce" (some (alg [] [] [] [resolve "Add", .num 0])),
    .call (resolve "reduce") (alg [] [] [] [data0, resolve "Add", .num 0])
  ])) with
  | Except.ok [4, 2, 3, 3, 6, 6] => true
  | _ => false

#eval sequenceBuiltinDotCallReduceSweep  -- should be true

end KatLangTests
