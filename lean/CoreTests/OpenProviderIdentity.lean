import KatLang
import CoreTests.Common

namespace KatLangTests.ProviderIdentity
open KatLang (alg algPrivate publicProp privateProp runResult Algorithm Error Result PropertyIdentity)

--------------------------------------------------------------------------------
-- Open provider identity — Q-19 D-I (decided 2026-10-06)
--
-- An `open` list counts the PROVIDERS its targets resolve to, by the language's one
-- callable identity (`sameRepeatedCallableIdentity`: declaration, declaring scope,
-- compatible activations), never by spelling or position (`resolveAllOpens`). One
-- declaration reached through two spellings, one path written twice, and one shared
-- declaration held by two properties of one scope are ONE provider; two written blocks
-- and two declarations stay two however equal their bodies, and a member alias never
-- merges its owner with another provider. C#: `Evaluator.ResolveAllOpens`,
-- `ElaboratedScopeLookup.ResolveOpenProvider`, `OpenProviderIdentityTests`.
--------------------------------------------------------------------------------

/-- `Lib = { public Sub = { public X = 1 }, public R = { open TARGETS ⏎ X } }` / `Lib.R`. -/
def subInsideLib (targets : List KatLang.Expr) : KatLang.Expr :=
  let sub := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] []
  let r := alg [] targets [] [.resolve "X"]
  let lib := alg [] [] [publicProp "Sub" sub, publicProp "R" r] []
  .algorithmExpr (alg [] [] [privateProp "Lib" lib] [.dotCall (.resolve "Lib") "R" none])

/-- One evaluation that must succeed with `expected`. -/
def evaluatesTo (e : KatLang.Expr) (expected : Result) : Bool :=
  match runResult e with
  | .ok value => value == expected
  | .error _ => false

/-- The innermost error is the open ambiguity of `name`. -/
def innermostAmbiguity (name : String) : Error -> Bool
  | .withContext _ inner => innermostAmbiguity name inner
  | .ambiguousOpen actual _ => actual = name
  | _ => false

/-- One evaluation that must be the ambiguity of `X`. -/
def ambiguousX (e : KatLang.Expr) : Bool :=
  match runResult e with
  | .error err => innermostAmbiguity "X" err
  | .ok _ => false

-- One declaration through two spellings is one provider, in either order.
def libSub : KatLang.Expr := .dotCall (.resolve "Lib") "Sub" none

#guard evaluatesTo (subInsideLib [.resolve "Sub", libSub]) (.atom 1)
#guard evaluatesTo (subInsideLib [libSub, .resolve "Sub"]) (.atom 1)
#guard evaluatesTo (subInsideLib [.resolve "Sub"]) (.atom 1)

/-- A program whose root body opens `targets` over the root properties `props` and reads `X`. -/
def openAtRoot (targets : List KatLang.Expr) (props : List KatLang.PropDef) : KatLang.Expr :=
  .algorithmExpr (alg [] targets props [.resolve "X"])

def libWithSub : KatLang.PropDef :=
  privateProp "Lib" (alg [] [] [publicProp "Sub" (alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] [])] [])

-- One path written twice is one provider.
#guard evaluatesTo (openAtRoot [libSub, libSub] [libWithSub]) (.atom 1)

-- Two written blocks are two providers however equal their bodies.
def xBlock (value : Int) : KatLang.Expr :=
  .algorithmExpr (alg [] [] [publicProp "X" (alg [] [] [] [.num value])] [])

#guard ambiguousX (openAtRoot [xBlock 1, xBlock 1] [])
#guard ambiguousX (openAtRoot [xBlock 1, xBlock 2] [])

-- Two declarations are two providers, in either order, even with identical bodies.
def declared (name : String) (value : Int) : KatLang.PropDef :=
  privateProp name (alg [] [] [publicProp "X" (alg [] [] [] [.num value])] [])

#guard ambiguousX (openAtRoot [.resolve "A", .resolve "B"] [declared "A" 1, declared "B" 2])
#guard ambiguousX (openAtRoot [.resolve "B", .resolve "A"] [declared "A" 1, declared "B" 2])
#guard ambiguousX (openAtRoot [.resolve "A", .resolve "B"] [declared "A" 1, declared "B" 1])

-- ONE shared declaration (one written declaration reached at two syntax sites, as the C#
-- encoder carries it: one `.shared` id) held by two properties of one scope is one provider —
-- NEED-04 already calls the two holders one callable.
def sharedProvider : Algorithm :=
  (alg [] [] [publicProp "X" (alg [] [] [] [.num 7])] []).withDeclarationId (some (.shared 0))

#guard evaluatesTo (openAtRoot [.resolve "A", .resolve "B"]
  [privateProp "A" sharedProvider, privateProp "B" sharedProvider]) (.atom 7)

-- A member alias never merges two providers: `B.X` is an alias of `A.X`, yet `A` and `B`
-- are two declarations, so `X` is ambiguous (the alias is its own binding).
def aliasReexport : KatLang.Expr :=
  let a := alg [] [] [publicProp "X" (alg ["v"] [] [] [.binary .add (.param "v") (.num 1)])] []
  let b := alg [] [] [publicProp "X" (.alias none [] [] (.dotCall (.resolve "A") "X" none))] []
  .algorithmExpr (alg [] [.resolve "A", .resolve "B"] [privateProp "A" a, privateProp "B" b]
    [.call (.resolve "X") [.num 5]])

#guard ambiguousX aliasReexport

end KatLangTests.ProviderIdentity
