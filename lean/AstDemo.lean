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
          (KatLang.Algorithm.mk
            none
            []
            []
            []
            [ KatLang.resolve "Add"
            , KatLang.block (KatLang.alg [] [] [] [ KatLang.dotCall (KatLang.resolve "Numbers") "count" ])
            , KatLang.block (KatLang.alg [] [] [] [ KatLang.num 0, KatLang.num 0 ])
            ]))
        (KatLang.num 1)
    ]

def RootAlg : Algorithm :=
  KatLang.algPrivate
    []
    [ KatLang.block NumbersLib ]  -- ★ opened import
    [ ("Add", AddAlg)
    , ("Sum", SumAlg)
    ]
    [ KatLang.resolve "Sum" ]

-- Expected: ok [24]
#eval! KatLang.runFlat (KatLang.block RootAlg)
#eval! KatLang.runResult (KatLang.block RootAlg)
