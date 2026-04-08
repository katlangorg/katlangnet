import KatLang

--------------------------------------------------------------------------------
-- dotCall semantics tests
--------------------------------------------------------------------------------

namespace KatLangTests
open KatLang (alg algPrivate privateProp publicProp runFlat runResult Algorithm Error Result)

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

-- Test 6: Numbers.length as algorithm argument to Repeat
-- Repeat(step, Numbers.length, init) where Numbers = [10,20,30]
-- step(x) = x + 1, init = 0, count = Numbers.length = 3
-- Result: 0 → 1 → 2 → 3
open KatLang (resolve param num)

def numbersAlg : Algorithm :=
  alg [] [] [] [.num 10, .num 20, .num 30]

-- step: single-param algorithm that adds 1
def stepAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

-- Root algorithm that calls Repeat(step, Numbers.length, init)
def repeatLenRoot : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg), ("Step", stepAlg)] [
    .call (resolve "repeat")
      (alg [] [] [] [
        resolve "Step",
        .dotCall (resolve "Numbers") "length" none,
        .block (alg [] [] [] [.num 0])
      ])
  ]

def test6 : Bool :=
  match runFlat (.block repeatLenRoot) with
  | Except.ok [3] => true
  | _ => false

#eval test6  -- should be true
-- EXPECTED: Except.ok [3] (step applied 3 times: 0→1→2→3)
#eval runFlat (.block repeatLenRoot)

-- Test 7: Numbers.length as Repeat count (comprehensive)
-- Uses 6 output expressions to verify correct count
def numbersAlg7 : Algorithm :=
  alg [] [] [] [.num 3, .num 5, .num 9, .num 1, .num 0, .num 6]

def testAlg7 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg7)] [
    .call (resolve "repeat")
      (alg [] [] [] [
        .block (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),  -- step: increment
        .dotCall (resolve "Numbers") "length" none,                     -- count: 6
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

-- Test 11: dotCall none syntax for length in Repeat argument position
-- Repeat(Add, Numbers.length, (0,0)) where Numbers.length is encoded as .dotCall
-- Numbers = [3,5,9,1,0,6] → length = 6
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
          .dotCall (resolve "Numbers") "length" none,    -- ← no-arg dotCall
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

-- Test 12: dotCall length as Repeat count (simple increment)
-- Same as Test 7 but with dotCall none syntax
-- Numbers has 3 outputs → length = 3, step(x) = x + 1, init = 0 → 3
def numbersAlg12 : Algorithm :=
  alg [] [] [] [.num 10, .num 20, .num 30]

def testAlg12 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg12)] [
    .call (resolve "repeat")
      (alg [] [] [] [
        .block (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),  -- step
        .dotCall (resolve "Numbers") "length" none,                              -- ← no-arg dotCall
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

-- Test 13: dotCall none length in value position (evalDotCall path)
def test13 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "length" none) with
  | Except.ok [2] => true
  | _ => false

#eval test13  -- should be true
#eval runFlat (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "length" none)

-- Test 14: .dotCall length in value position (evalDotCall path)
def test14 : Bool :=
  match runFlat (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "length" none) with
  | Except.ok [2] => true
  | _ => false

#eval test14  -- should be true
#eval runFlat (.dotCall (.block (alg [] [] [] [.num 1, .num 2])) "length" none)

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

--------------------------------------------------------------------------------
-- 2-arg if builtin tests (conditional output / emit-on-true)
-- if(cond, value): true → value, false → group [] (no output).
--------------------------------------------------------------------------------

-- Test 20: 2-arg if true → produce value
-- if(1, 5) → [5]
def test20 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 1, .num 5])) with
  | Except.ok [5] => true
  | _ => false

#eval test20  -- should be true
#eval runFlat (.call (resolve "if") (alg [] [] [] [.num 1, .num 5]))

-- Test 21: 2-arg if false → empty output
-- if(0, 5) → []
def test21 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 0, .num 5])) with
  | Except.ok [] => true
  | _ => false

#eval test21  -- should be true
#eval runFlat (.call (resolve "if") (alg [] [] [] [.num 0, .num 5]))

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

-- Test 22: 2-arg if false in addition → empty transparent, 10 + if(0, 5) → [10]
def test22 : Bool :=
  match runFlat (.binary .add (.num 10) (.call (resolve "if") (alg [] [] [] [.num 0, .num 5]))) with
  | Except.ok [10] => true
  | _ => false

#eval test22  -- should be true
#eval runFlat (.binary .add (.num 10) (.call (resolve "if") (alg [] [] [] [.num 0, .num 5])))

-- Test 23: 2-arg if true in addition → 10 + if(1, 5) → [15]
def test23 : Bool :=
  match runFlat (.binary .add (.num 10) (.call (resolve "if") (alg [] [] [] [.num 1, .num 5]))) with
  | Except.ok [15] => true
  | _ => false

#eval test23  -- should be true
#eval runFlat (.binary .add (.num 10) (.call (resolve "if") (alg [] [] [] [.num 1, .num 5])))

-- Test 24: Combine with 2-arg if false → omitted from output
-- 1, if(0, 2), 3 → [1, 3]
def test24 : Bool :=
  match runFlat (.combine (.num 1) (.combine (.call (resolve "if") (alg [] [] [] [.num 0, .num 2])) (.num 3))) with
  | Except.ok [1, 3] => true
  | _ => false

#eval test24  -- should be true
#eval runFlat (.combine (.num 1) (.combine (.call (resolve "if") (alg [] [] [] [.num 0, .num 2])) (.num 3)))

-- Test 25: Combine with 2-arg if true → included in output
-- 1, if(1, 2), 3 → [1, 2, 3]
def test25 : Bool :=
  match runFlat (.combine (.num 1) (.combine (.call (resolve "if") (alg [] [] [] [.num 1, .num 2])) (.num 3))) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#eval test25  -- should be true
#eval runFlat (.combine (.num 1) (.combine (.call (resolve "if") (alg [] [] [] [.num 1, .num 2])) (.num 3)))

-- Test 26: Nested 2-arg if — if(1, if(1, 5)) → [5]
def test26 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [
    .num 1,
    .call (resolve "if") (alg [] [] [] [.num 1, .num 5])
  ])) with
  | Except.ok [5] => true
  | _ => false

#eval test26  -- should be true

-- Test 27: Nested 2-arg if — outer false → empty
-- if(0, if(1, 5)) → []
def test27 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [
    .num 0,
    .call (resolve "if") (alg [] [] [] [.num 1, .num 5])
  ])) with
  | Except.ok [] => true
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

-- Test 30: 2-arg if with non-zero condition → true
-- if(42, 7) → [7]
def test30 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num 42, .num 7])) with
  | Except.ok [7] => true
  | _ => false

#eval test30  -- should be true

-- Test 31: 2-arg if with negative condition → true
-- if(-1, 7) → [7]
def test31 : Bool :=
  match runFlat (.call (resolve "if") (alg [] [] [] [.num (-1), .num 7])) with
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

-- Test 32: Unary on empty 2-arg if → transparent
-- -(if(0, 5)) → empty, 10 + -(if(0, 5)) → [10]
def test32 : Bool :=
  match runFlat (.binary .add (.num 10) (.unary .minus (.call (resolve "if") (alg [] [] [] [.num 0, .num 5])))) with
  | Except.ok [10] => true
  | _ => false

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
  match runFlat (.block (algPrivate [] [] [("IsEven", isEvenAlg63)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "if") (alg [] [] [] [.num 0, .num 1]),
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

-- Test 69: predicate result invalid for truth testing → error
def test69 : Bool :=
  match runResult (.block (algPrivate [] [] [("BadTruth", badTruthAlg66)] [
    .call (resolve "filter") (alg [] [] [] [
      .call (resolve "range") (alg [] [] [] [.num 1, .num 3]),
      .resolve "BadTruth"
    ])
  ])) with
  | Except.error _ => true
  | _ => false

#eval test69  -- should be true

-- Test 70: builtin arity mismatch still follows normal conventions
def test70 : Bool :=
  match runResult (.call (resolve "filter") (alg [] [] [] [
    .call (resolve "range") (alg [] [] [] [.num 1, .num 3])
  ])) with
  | Except.error _ => true
  | _ => false

#eval test70  -- should be true

end KatLangTests
