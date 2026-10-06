import KatLang
import CoreTests.Common

namespace KatLangTests.ModuleUnits
open KatLang (alg publicProp privateProp runResult Algorithm Error Result PropertyIdentity)

--------------------------------------------------------------------------------
-- Loaded modules — Q-31 H-P + Q-32 I-U (decided 2026-10-06)
--
-- A loaded module is a hygienic source unit rooted at the prelude: wherever it is reached,
-- `Algorithm.withParent` wires it under the chain's root level, so its free names never see
-- its holder's (H-P), and one canonical URL is ONE declaration — `PropertyIdentity.module` —
-- so every holder reaches the one declaration in the one declaring scope: one callable
-- identity (NEED-04) and one open provider (Q-19 D-I) (I-U). Lean has no loader; these
-- guards build the elaborated trees the C# loader produces, and the encoder emits the same
-- mark for every C# loaded-module root (`LeanAstEncoder`, `IsModuleElaborated`).
-- C#: `Evaluator.WithParent`, `ModuleHygieneTests`, `ModuleIdentityTests`.
--------------------------------------------------------------------------------

/-- The loaded module `public V = sum((1, 2))`, marked as module declaration `n`. -/
def sumModule (n : Nat) : Algorithm :=
  (alg [] [] [publicProp "V" (alg [] [] [] [.call (.resolve "sum") [.capture [.num 1, .num 2]]])] [])
    |>.withDeclarationId (some (.module n))

/-- The same text written inline (an ordinary declaration): it sees its definition site. -/
def sumInline : Algorithm :=
  alg [] [] [publicProp "V" (alg [] [] [] [.call (.resolve "sum") [.capture [.num 1, .num 2]]])] []

/-- A site whose own `sum` shadows the prelude's, holding `module` as `M` and reading `M.V`. -/
def shadowingSite (module : Algorithm) : KatLang.Expr :=
  .algorithmExpr (alg [] []
    [privateProp "sum" (alg ["xs"] [] [] [.num 999]), privateProp "M" module]
    [.dotCall (.resolve "M") "V" none])

def evaluatesTo (e : KatLang.Expr) (expected : Result) : Bool :=
  match runResult e with
  | .ok value => value == expected
  | .error _ => false

-- H-P: the module reads the prelude's `sum`, whatever the site shadows; the inline text reads
-- the site's (its definition site) — the one difference the mark makes.
#guard evaluatesTo (shadowingSite (sumModule 0)) (.atom 3)
#guard evaluatesTo (shadowingSite sumInline) (.atom 999)

-- … inside a parameterized owner too: the module is never wired under the owner's activation.
def ownerSite (module : Algorithm) : KatLang.Expr :=
  .algorithmExpr (alg [] []
    [privateProp "sum" (alg ["xs"] [] [] [.num 999]),
     privateProp "G" (alg ["k"] [] [privateProp "M" module]
       [.binary .add (.dotCall (.resolve "M") "V" none) (.binary .mul (.param "k") (.num 0))])]
    [.call (.resolve "G") [.num 1]])

#guard evaluatesTo (ownerSite (sumModule 0)) (.atom 3)
#guard evaluatesTo (ownerSite sumInline) (.atom 999)

/-- The site's properties are never seen either: a module reading an undeclared `Base` (in C# the
    front end makes it the member's own parameter) finds nothing at the prelude. -/
def baseModule : Algorithm :=
  (alg [] [] [publicProp "V" (alg [] [] [] [.binary .add (.resolve "Base") (.num 1)])] [])
    |>.withDeclarationId (some (.module 0))

def baseSite : KatLang.Expr :=
  .algorithmExpr (alg [] [] [privateProp "Base" (alg [] [] [] [.num 10]), privateProp "M" baseModule]
    [.dotCall (.resolve "M") "V" none])

def failsUnknown (e : KatLang.Expr) (name : String) : Bool :=
  match runResult e with
  | .error err => innermostIsUnknownName name err
  | .ok _ => false

#guard failsUnknown baseSite "Base"

/-- The module `public X = 5`, marked as module declaration `n`. Its member is the module's one
    member declaration wherever the module is held, so it carries a shared identity — exactly as
    the encoder carries the members of a C# module root reached twice (`.shared`). -/
def fiveModule (n : Nat) : Algorithm :=
  (alg [] []
    [{ (publicProp "X" ((alg [] [] [] [.num 5]).withDeclarationId (some (.shared (100 + n)))))
        with identity := some (.shared (100 + n)) }] [])
    |>.withDeclarationId (some (.module n))

-- I-U: two holders of ONE module declaration reach one callable (NEED-04) …
def repeatedCallable (a b : Algorithm) : KatLang.Expr :=
  .algorithmExpr (alg [] []
    [privateProp "P" (alg ["f", "f"] [] [] [.param "f"]),
     privateProp "A" a,
     privateProp "C" (alg [] [] [privateProp "B" b] [.dotCall (.resolve "B") "X" none])]
    [.call (.resolve "P") [.dotCall (.resolve "A") "X" none, .dotCall (.dotCall (.resolve "C") "B" none) "X" none]])

#guard evaluatesTo (repeatedCallable (fiveModule 0) (fiveModule 0)) (.atom 5)

-- … while two declarations (two canonical URLs, however equal their bytes) are two callables.
#guard !evaluatesTo (repeatedCallable (fiveModule 0) (fiveModule 1)) (.atom 5)

-- … and one open provider (Q-19 D-I), while two declarations are two.
def openTwoHolders (a b : Algorithm) : KatLang.Expr :=
  .algorithmExpr (alg [] [.resolve "A", .resolve "B"] [privateProp "A" a, privateProp "B" b] [.resolve "X"])

#guard evaluatesTo (openTwoHolders (fiveModule 0) (fiveModule 0)) (.atom 5)

def ambiguousX (e : KatLang.Expr) : Bool :=
  match runResult e with
  | .error err => innermostAmbiguity err
  | .ok _ => false
where
  innermostAmbiguity : Error -> Bool
    | .withContext _ inner => innermostAmbiguity inner
    | .ambiguousOpen name _ => name = "X"
    | _ => false

#guard ambiguousX (openTwoHolders (fiveModule 0) (fiveModule 1))

-- The pre-evaluation alias chase restarts at a module: an alias inside it never resolves through
-- its holder. A host-built holder alias `Helper = M.F` over a module alias `F = Helper` is no static
-- cycle (the module's `Helper` is not the holder's), while the same text written inline is one.
def helperAlias : KatLang.PropDef :=
  privateProp "Helper" (.alias none [] [] (.dotCall (.resolve "M") "F" none) none)

def aliasBody : Algorithm :=
  alg [] [] [publicProp "F" (.alias none [] [] (.resolve "Helper") none)] []

def validates (a : Algorithm) : Bool :=
  match KatLang.runEvalM (KatLang.validateExplicitParamOutputInvariant a) with
  | .ok _ => true
  | .error _ => false

#guard validates (alg [] [] [helperAlias, privateProp "M" (aliasBody.withDeclarationId (some (.module 0)))] [.num 1])
#guard !validates (alg [] [] [helperAlias, privateProp "M" aliasBody] [.num 1])

end KatLangTests.ModuleUnits
