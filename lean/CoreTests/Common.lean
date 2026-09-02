import KatLang

--------------------------------------------------------------------------------
-- CoreTests.Common: matcher, constructor, and run helpers shared by the CoreTests domain modules
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

-- Shared fixtures and helpers used by more than one domain module (moved here from their original sections).

def incAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

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

def evenPredicateAlg19d : Algorithm :=
  alg ["n"] [] [] [
    .binary .eq
      (.binary .mod (.index (.param "n") (.num 1)) (.num 2))
      (.num 0)
  ]

def expectFlat (result : Except Error (List Int)) (expected : List Int) : Bool :=
  match result with
  | Except.ok values => values == expected
  | _ => false

def expectInnermostArityMismatch (expected actual : Nat) (result : Except Error (List Int)) : Bool :=
  match result with
  | Except.error err => innermostIsArityMismatch expected actual err
  | _ => false

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

end KatLangTests
