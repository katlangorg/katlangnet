import KatLang

--------------------------------------------------------------------------------
-- Example (explicit imports)
--------------------------------------------------------------------------------

open KatLang
open KatLang.Expr

def NumbersLib : Algorithm :=
  KatLang.alg
    []
    []
    [ KatLang.publicProp "Numbers"
        (KatLang.alg [] [] [] [ KatLang.num 3, KatLang.num 5, KatLang.num 9
                              , KatLang.num 1, KatLang.num 0, KatLang.num 6 ])
    ]
    []

def AddAlg : Algorithm :=
  KatLang.alg
    ["a", "sum"]
    []
    []
    [ KatLang.param "a" + KatLang.num 1
    , KatLang.param "sum" + KatLang.index (KatLang.resolve "Numbers") (KatLang.param "a")
    ]

def SumAlg : Algorithm :=
  KatLang.alg
    []
    []
    []
    [ KatLang.index
        (KatLang.call
          (KatLang.resolve "repeat")
          [ KatLang.resolve "Add"
          , KatLang.algorithmExpr (KatLang.alg [] [] [] [ KatLang.dotCall (KatLang.resolve "Numbers") "count" ])
          , KatLang.num 0
          , KatLang.num 0
          ])
        (KatLang.num 1)
    ]

def RootAlg : Algorithm :=
  KatLang.algPrivate
    []
    [ KatLang.algorithmExpr NumbersLib ]  -- ★ opened import
    [ ("Add", AddAlg)
    , ("Sum", SumAlg)
    ]
    [ KatLang.resolve "Sum" ]

-- Expected: ok [24]
#eval! KatLang.runFlat (KatLang.algorithmExpr RootAlg)
#eval! KatLang.runResult (KatLang.algorithmExpr RootAlg)

--------------------------------------------------------------------------------
-- Zero-parameter property cache demo
--------------------------------------------------------------------------------

structure ZeroArgCacheEntryDemo where
  propertyName : Ident
  accessKind : ZeroArgPropertyAccessKind
  countedResult : CountedResult
  deriving Repr

def zeroArgPropertyCacheView (state : EvalState) : List ZeroArgCacheEntryDemo :=
  state.zeroArgPropertyCache.map fun entry =>
    { propertyName := entry.fst.propertyName
      accessKind := entry.fst.accessKind
      countedResult := entry.snd }

def runResultAndCacheView (e : Expr) : Except Error (Result × List ZeroArgCacheEntryDemo) :=
  match KatLang.runResultWithState e with
  | Except.ok (result, state) => Except.ok (result, zeroArgPropertyCacheView state)
  | Except.error err => Except.error err

def CachedPropertyStyleRoot : Algorithm :=
  KatLang.algPrivate
    []
    []
    [ ("A", KatLang.alg [] [] [] [KatLang.num 1 + KatLang.num 2]) ]
    [ KatLang.resolve "A"
    , KatLang.resolve "A"
    ]

def ExplicitZeroArgCallRoot : Algorithm :=
  KatLang.algPrivate
    []
    []
    [ ("A", KatLang.alg [] [] [] [KatLang.num 1 + KatLang.num 2]) ]
    [ KatLang.call (KatLang.resolve "A") []
    , KatLang.call (KatLang.resolve "A") []
    ]

-- Property-style access (`A, A`) leaves one zero-argument cache entry for A.
#eval! runResultAndCacheView (KatLang.algorithmExpr CachedPropertyStyleRoot)

-- Explicit calls (`A(), A()`) bypass A's zero-argument cache entry.
#eval! runResultAndCacheView (KatLang.algorithmExpr ExplicitZeroArgCallRoot)
