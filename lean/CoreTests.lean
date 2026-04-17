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

-- Test 6: Numbers.arity as algorithm argument to Repeat
-- Repeat(step, Numbers.arity, init) where Numbers = [10,20,30]
-- step(x) = x + 1, init = 0, count = Numbers.arity = 3
-- Result: 0 → 1 → 2 → 3
open KatLang (resolve param num)

def numbersAlg : Algorithm :=
  alg [] [] [] [.num 10, .num 20, .num 30]

-- step: single-param algorithm that adds 1
def stepAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

-- Root algorithm that calls Repeat(step, Numbers.arity, init)
def repeatArityRoot : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg), ("Step", stepAlg)] [
    .call (resolve "repeat")
      (alg [] [] [] [
        resolve "Step",
        .dotCall (resolve "Numbers") "arity" none,
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

-- Test 7: Numbers.arity as Repeat count (comprehensive)
-- Uses 6 output expressions to verify correct count
def numbersAlg7 : Algorithm :=
  alg [] [] [] [.num 3, .num 5, .num 9, .num 1, .num 0, .num 6]

def testAlg7 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg7)] [
    .call (resolve "repeat")
      (alg [] [] [] [
        .block (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),  -- step: increment
        .dotCall (resolve "Numbers") "arity" none,                      -- count: 6
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

-- Test 11: dotCall none syntax for arity in Repeat argument position
-- Repeat(Add, Numbers.arity, (0,0)) where Numbers.arity is encoded as .dotCall
-- Numbers = [3,5,9,1,0,6] → arity = 6
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
          .dotCall (resolve "Numbers") "arity" none,     -- ← no-arg dotCall
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

-- Test 12: dotCall arity as Repeat count (simple increment)
-- Same as Test 7 but with dotCall none syntax
-- Numbers has 3 outputs → arity = 3, step(x) = x + 1, init = 0 → 3
def numbersAlg12 : Algorithm :=
  alg [] [] [] [.num 10, .num 20, .num 30]

def testAlg12 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg12)] [
    .call (resolve "repeat")
      (alg [] [] [] [
        .block (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),  -- step
        .dotCall (resolve "Numbers") "arity" none,                       -- ← no-arg dotCall
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

-- Test 13: dotCall none arity in value position (evalDotCall path)
def test13 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "arity" none) with
  | Except.ok [2] => true
  | _ => false

#eval test13  -- should be true
#eval runFlat (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "arity" none)

-- Test 14: .dotCall arity in value position (evalDotCall path)
def test14 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "arity" none) with
  | Except.ok [2] => true
  | _ => false

#eval test14  -- should be true
#eval runFlat (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "arity" none)

-- Test 14a: grouped output keeps structural arity distinct from count
def groupedOutputRoot14a : Algorithm :=
  algPrivate [] [] [("T", alg [] [] [] [.block (alg [] [] [] [.num 1, .num 2, .num 3])])] [
    .dotCall (resolve "T") "arity" none,
    .dotCall (resolve "T") "count" none
  ]

def test14a : Bool :=
  match runFlat (.block groupedOutputRoot14a) with
  | Except.ok [1, 3] => true
  | _ => false

#eval test14a  -- should be true
#eval runFlat (.block groupedOutputRoot14a)

-- Test 14b: plain multi-output keeps arity and count aligned
def multiOutputRoot14b : Algorithm :=
  algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2, .num 3])] [
    .dotCall (resolve "A") "arity" none,
    .dotCall (resolve "A") "count" none
  ]

def test14b : Bool :=
  match runFlat (.block multiOutputRoot14b) with
  | Except.ok [3, 3] => true
  | _ => false

#eval test14b  -- should be true
#eval runFlat (.block multiOutputRoot14b)

-- Test 14c: sorted output preserves structural arity while count reflects evaluated values
def sortedOutputRoot14c : Algorithm :=
  algPrivate [] [] [
    ("List", alg [] [] [] [.num 3, .num 1, .num 2]),
    ("Sorted", alg [] [] [] [.dotCall (resolve "List") "order" none])
  ] [
    .dotCall (resolve "Sorted") "arity" none,
    .dotCall (resolve "Sorted") "count" none
  ]

def test14c : Bool :=
  match runFlat (.block sortedOutputRoot14c) with
  | Except.ok [1, 3] => true
  | _ => false

#eval test14c  -- should be true
#eval runFlat (.block sortedOutputRoot14c)

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

-- Test 19: dual-view semantics for higher-order parameters
-- The same parameter should remain callable through AlgEnv and readable through ValEnv
-- when the original argument expression supports both meanings.
-- A 0-param block supports both: it evaluates to a value (ValEnv) and resolves
-- as an algorithm (AlgEnv).  The body calls f() via AlgEnv and reads f via ValEnv.
def constSevenAlg19 : Algorithm :=
  alg [] [] [] [.num 7]

def dualUseAlg19 : Algorithm :=
  alg ["f"] [] [] [
    .binary .add
      (.call (.param "f") (alg [] [] [] []))
      (.param "f")
  ]

def test19 : Bool :=
  match runFlat (.block (algPrivate [] [] [("DualUse", dualUseAlg19)] [
    .call (resolve "DualUse") (alg [] [] [] [.block constSevenAlg19])
  ])) with
  | Except.ok [14] => true
  | _ => false

#eval test19  -- should be true
#eval runFlat (.block (algPrivate [] [] [("DualUse", dualUseAlg19)] [
  .call (resolve "DualUse") (alg [] [] [] [.block constSevenAlg19])
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
      (.binary .mod (.param "n") (.num 2))
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
def occurrenceCountAlg19e : Algorithm :=
  alg ["values", "target"] [] [] [
    .dotCall
      (.call (.resolve "filter") (alg [] [] [] [
        .param "values",
        .block (alg ["item"] [] [] [
          .binary .eq
            (.param "item")
            (.param "target")
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
      .block (alg [] [] [] [.num 1, .num 2]),
      .num 2
    ])
  ])) with
  | Except.ok [1] => true
  | _ => false

#eval test19e  -- should be true
#eval runFlat (.block (algPrivate [] [] [
  ("OccurrenceCount", occurrenceCountAlg19e)
] [
  .call (.resolve "OccurrenceCount") (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .num 2
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

-- Test 25: Combine with 3-arg if selects the else branch
-- 1, if(0, 2, 9), 3 → [1, 9, 3]
def test25 : Bool :=
  match runFlat (.combine (.num 1) (.combine (.call (resolve "if") (alg [] [] [] [.num 0, .num 2, .num 9])) (.num 3))) with
  | Except.ok [1, 9, 3] => true
  | _ => false

#eval test25  -- should be true
#eval runFlat (.combine (.num 1) (.combine (.call (resolve "if") (alg [] [] [] [.num 0, .num 2, .num 9])) (.num 3)))

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
  alg ["x"] [] [] [.dotCall (.param "x") "string" none]

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
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "IsNegative"
    ])
  ]

-- Test 63: filter(range(1, 10), IsEven) keeps even items in ascending order
def test63 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg63)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 10]),
      .resolve "IsEven"
    ])
  ])) with
  | Except.ok [2, 4, 6, 8, 10] => true
  | _ => false

#eval test63  -- should be true

-- Test 64: descending range preserves original order of kept items
def test64 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg63)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 10, .num 1]),
      .resolve "IsEven"
    ])
  ])) with
  | Except.ok [10, 8, 6, 4, 2] => true
  | _ => false

#eval test64  -- should be true

-- Test 65: all-true predicate returns the same collection in the same order
def test65 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsPositive", isPositiveAlg64)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "IsPositive"
    ])
  ])) with
  | Except.ok [1, 2, 3, 4] => true
  | _ => false

#eval test65  -- should be true

-- Test 66: all-false predicate produces an empty result
def test66 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "IsNegative"
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#eval test66  -- should be true

-- Test 67: empty input collection stays empty
def test67 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg63), ("IsNegative", isNegativeAlg65)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
      ]),
      .resolve "IsEven"
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#eval test67  -- should be true

-- Test 68: grouped elements are preserved whole and in order
def test68 : Bool :=
  let groupedItems := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 10]),
    .block (alg [] [] [] [.num 2, .num 20]),
    .block (alg [] [] [] [.num 3, .num 30]),
    .block (alg [] [] [] [.num 4, .num 40])
  ])
  match runResult (.block (algPrivate [] [] [("KeepPair", keepPairAlg67)] [
    .call (resolve "filter") (alg [] [] [] [groupedItems, .resolve "KeepPair"])
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
  match runResult (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65), ("Bad", emptyTruthAlg71)] [
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
      hasContext "while evaluating filter predicate (filter passes each collection item as one argument to the predicate)" err &&
      innermostIsArityMismatch 0 1 err
  | _ => false

#eval test75  -- should be true

--------------------------------------------------------------------------------
-- reduce builtin tests
--------------------------------------------------------------------------------

def addAlg76 : Algorithm :=
  alg ["x", "total"] [] [] [.binary .add (.param "x") (.param "total")]

def mulAlg77 : Algorithm :=
  alg ["x", "total"] [] [] [.binary .mul (.param "x") (.param "total")]

def digitsAlg78 : Algorithm :=
  alg ["x", "acc"] [] [] [
    .binary .add (.binary .mul (.param "acc") (.num 10)) (.param "x")
  ]

def reduceGroupedItemAlg79 : Algorithm :=
  .conditional none [] [
    ⟨ .group [.group [.bind "tag", .bind "value"], .bind "acc"],
      alg [] [] [] [.binary .add (.param "acc") (.param "value")] ⟩
  ]

def reduceStatsAlg80 : Algorithm :=
  alg ["x", "acc"] [] [] [
    .block (alg [] [] [] [
      .binary .add (.param "x") (.index (.param "acc") (.num 0)),
      .binary .add (.index (.param "acc") (.num 1)) (.num 1)
    ])
  ]

def reduceEmptyAlg81 : Algorithm :=
  alg ["x", "acc"] [] [] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "IsNegative"
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

-- Test 77: ordinary builtin-call reduce with multiplicative step
def test77 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Mul", mulAlg77)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "Mul",
      .num 1
    ])
  ])) with
  | Except.ok [24] => true
  | _ => false

#eval test77  -- should be true

-- Test 78: reduce folds left to right
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

-- Test 79: empty collection returns the numeric initial accumulator unchanged
def test79 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Add", addAlg76), ("IsNegative", isNegativeAlg65)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
      ]),
      .resolve "Add",
      .num 0
    ])
  ])) with
  | Except.ok [0] => true
  | _ => false

#eval test79  -- should be true

-- Test 80: empty collection returns a grouped initial accumulator unchanged
def test80 : Bool :=
  match runResult (.block (algPrivate [] [] [("Add", addAlg76), ("IsNegative", isNegativeAlg65)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
      ]),
      .resolve "Add",
      .block (alg [] [] [] [.num 7, .num 9])
    ])
  ])) with
  | Except.ok (.group [.atom 7, .atom 9]) => true
  | _ => false

#eval test80  -- should be true

-- Test 81: grouped collection elements are passed to the step as whole values
def test81 : Bool :=
  let groupedItems := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 10]),
    .block (alg [] [] [] [.num 2, .num 20]),
    .block (alg [] [] [] [.num 3, .num 30])
  ])
  match runFlat (.block (algPrivate [] [] [("TakeValue", reduceGroupedItemAlg79)] [
    .call (resolve "reduce") (alg [] [] [] [
      groupedItems,
      .resolve "TakeValue",
      .num 0
    ])
  ])) with
  | Except.ok [60] => true
  | _ => false

#eval test81  -- should be true

-- Test 82: grouped accumulator values are accepted and returned unchanged in shape
def test82 : Bool :=
  match runResult (.block (algPrivate [] [] [("Stats", reduceStatsAlg80)] [
    .call (resolve "reduce") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
      .resolve "Stats",
      .block (alg [] [] [] [.num 0, .num 0])
    ])
  ])) with
  | Except.ok (.group [.atom 10, .atom 4]) => true
  | _ => false

#eval test82  -- should be true

-- Test 83: reduce step must not return an empty result
def test83 : Bool :=
  match runResult (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65), ("Bad", reduceEmptyAlg81)] [
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

--------------------------------------------------------------------------------
-- map builtin tests
--------------------------------------------------------------------------------

def doubleAlg85 : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]

def squareAlg86 : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.param "x")]

def tagAlg87 : Algorithm :=
  alg ["x"] [] [] [
    .binary .add (.binary .mul (.param "x") (.num 10)) (.num 1)
  ]

def takePairValueAlg89 : Algorithm :=
  .conditional none [] [
    ⟨ .group [.bind "tag", .bind "value"],
      alg [] [] [] [.param "value"] ⟩
  ]

def pairWithSquareAlg90 : Algorithm :=
  alg ["x"] [] [] [
    .block (alg [] [] [] [
      .param "x",
      .binary .mul (.param "x") (.param "x")
    ])
  ]

def mapEmptyAlg91 : Algorithm :=
  alg ["x"] [] [] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "IsNegative"
    ])
  ]

def mapMultiAlg92 : Algorithm :=
  alg ["x"] [] [] [
    .param "x",
    .binary .mul (.param "x") (.param "x")
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

-- Test 86: ordinary builtin-call map squares each range element
def test86 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Square", squareAlg86)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 5]),
      .resolve "Square"
    ])
  ])) with
  | Except.ok [1, 4, 9, 16, 25] => true
  | _ => false

#eval test86  -- should be true

-- Test 87: map preserves the original left-to-right element order
def test87 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Tag", tagAlg87)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 5, .num 1]),
      .resolve "Tag"
    ])
  ])) with
  | Except.ok [51, 41, 31, 21, 11] => true
  | _ => false

#eval test87  -- should be true

-- Test 88: empty input collection stays empty
def test88 : Bool :=
  match runFlat (.block (algPrivate [] [] [("Double", doubleAlg85), ("IsNegative", isNegativeAlg65)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
      ]),
      .resolve "Double"
    ])
  ])) with
  | Except.ok [] => true
  | _ => false

#eval test88  -- should be true

-- Test 89: grouped collection elements are passed to the transform as whole values
def test89 : Bool :=
  let groupedItems := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 10]),
    .block (alg [] [] [] [.num 2, .num 20]),
    .block (alg [] [] [] [.num 3, .num 30])
  ])
  match runFlat (.block (algPrivate [] [] [("TakeValue", takePairValueAlg89)] [
    .call (resolve "map") (alg [] [] [] [groupedItems, .resolve "TakeValue"])
  ])) with
  | Except.ok [10, 20, 30] => true
  | _ => false

#eval test89  -- should be true

-- Test 90: grouped mapped results are accepted as one mapped element each
def test90 : Bool :=
  match runResult (.block (algPrivate [] [] [("PairWithSquare", pairWithSquareAlg90)] [
    .call (resolve "map") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "PairWithSquare"
    ])
  ])) with
  | Except.ok (.group [
      .group [.atom 1, .atom 1],
      .group [.atom 2, .atom 4],
      .group [.atom 3, .atom 9]
    ]) => true
  | _ => false

#eval test90  -- should be true

-- Test 91: map transform must not return an empty result
def test91 : Bool :=
  match runResult (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65), ("Bad", mapEmptyAlg91)] [
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

-- Test 93: ordinary builtin-call sum adds an ascending range
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

-- Test 95: descending ranges are summed in their original top-level order
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

-- Test 98: empty collections sum to zero
def test98 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65)] [
    .call (resolve "sum") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
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
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value" err && innermostIsBadArity err
  | _ => false

#eval test100  -- should be true

-- Test 101: string elements are rejected by sum
def test101 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "sum") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value" err && innermostIsBadArity err
  | _ => false

#eval test101  -- should be true

--------------------------------------------------------------------------------
-- count builtin tests
--------------------------------------------------------------------------------

-- Test 102: ordinary builtin-call count counts an ascending range
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

-- Test 104: descending ranges keep their top-level element count
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

-- Test 107: empty collections count as zero
def test107 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65)] [
    .call (resolve "count") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
      ])
    ])
  ])) with
  | Except.ok [0] => true
  | _ => false

#eval test107  -- should be true

-- Test 108: grouped top-level elements count as one each and are not flattened
def test108 : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runFlat (.block (alg [] [] [] [
    .call (resolve "count") (alg [] [] [] [groupedPairs])
  ])) with
  | Except.ok [2] => true
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

--------------------------------------------------------------------------------
-- min builtin tests
--------------------------------------------------------------------------------

def negateAlg111 : Algorithm :=
  alg ["x"] [] [] [
    .unary .minus (.param "x")
  ]

-- Test 111: ordinary builtin-call min finds the minimum in an ascending range
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

-- Test 113: descending ranges still compare top-level elements correctly
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

-- Test 116: empty collections are rejected by min
def test116 : Bool :=
  match runResult (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65)] [
    .call (resolve "min") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
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
  | Except.error err => hasContext "min expects each collection element to be a single numeric value" err && innermostIsBadArity err
  | _ => false

#eval test118  -- should be true

-- Test 119: string elements are rejected by min
def test119 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "min") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value" err && innermostIsBadArity err
  | _ => false

#eval test119  -- should be true

--------------------------------------------------------------------------------
-- max builtin tests
--------------------------------------------------------------------------------

-- Test 120: ordinary builtin-call max finds the maximum in an ascending range
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

-- Test 122: descending ranges still compare top-level elements correctly
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

-- Test 125: empty collections are rejected by max
def test125 : Bool :=
  match runResult (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65)] [
    .call (resolve "max") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
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
  | Except.error err => hasContext "max expects each collection element to be a single numeric value" err && innermostIsBadArity err
  | _ => false

#eval test127  -- should be true

-- Test 128: string elements are rejected by max
def test128 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "max") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value" err && innermostIsBadArity err
  | _ => false

#eval test128  -- should be true

-- Test 129: ordinary builtin-call avg finds the mean in an ascending range
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

-- Test 131: descending ranges still average top-level elements correctly
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

-- Test 134: empty collections are rejected by avg
def test134 : Bool :=
  match runResult (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65)] [
    .call (resolve "avg") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
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
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value" err && innermostIsBadArity err
  | _ => false

#eval test136  -- should be true

-- Test 137: string elements are rejected by avg
def test137 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "avg") (alg [] [] [] [.stringLiteral "hello"])
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value" err && innermostIsBadArity err
  | _ => false

#eval test137  -- should be true

--------------------------------------------------------------------------------
-- order builtins tests
--------------------------------------------------------------------------------

-- Test 138: ordinary builtin-call order sorts ascending and preserves duplicates
def test138 : Bool :=
  match runFlat (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [
      .block (alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])
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

-- Test 142: empty collections stay empty when sorted
def test142 : Bool :=
  match runFlat (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65)] [
    .dotCall
      (.call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
      ]))
      "order"
      none
  ])) with
  | Except.ok [] => true
  | _ => false

#eval test142  -- should be true

-- Test 143: unsupported sortable elements are rejected by order
def test143 : Bool :=
  match runResult (.block (alg [] [] [] [
    .call (resolve "order") (alg [] [] [] [
      .block (alg [] [] [] [.num 1, .stringLiteral "hello"])
    ])
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value" err && innermostIsBadArity err
  | _ => false

#eval test143  -- should be true

--------------------------------------------------------------------------------
-- first/last builtin tests
--------------------------------------------------------------------------------

-- Test 144: ordinary builtin-call first picks the first ascending range element
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

-- Test 146: ordinary builtin-call last picks the last ascending range element
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

-- Test 148: first preserves a grouped top-level element unchanged
def test148 : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "first") (alg [] [] [] [groupedPairs])
  ])) with
  | Except.ok (.group [.atom 1, .atom 2]) => true
  | _ => false

#eval test148  -- should be true

-- Test 149: last preserves a grouped top-level element unchanged
def test149 : Bool :=
  let groupedPairs := .block (alg [] [] [] [
    .block (alg [] [] [] [.num 1, .num 2]),
    .block (alg [] [] [] [.num 3, .num 4])
  ])
  match runResult (.block (alg [] [] [] [
    .call (resolve "last") (alg [] [] [] [groupedPairs])
  ])) with
  | Except.ok (.group [.atom 3, .atom 4]) => true
  | _ => false

#eval test149  -- should be true

-- Test 150: first rejects empty collections
def test150 : Bool :=
  match runResult (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65)] [
    .call (resolve "first") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
      ])
    ])
  ])) with
  | Except.error err => hasContext "first requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#eval test150  -- should be true

-- Test 151: last rejects empty collections
def test151 : Bool :=
  match runResult (.block (algPrivate [] [] [("IsNegative", isNegativeAlg65)] [
    .call (resolve "last") (alg [] [] [] [
      .call (resolve "filter") (alg [] [] [] [
        .call (resolve "range") (alg [] [] [] [.num 1, .num 4]),
        .resolve "IsNegative"
      ])
    ])
  ])) with
  | Except.error err => hasContext "last requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#eval test151  -- should be true

end KatLangTests
