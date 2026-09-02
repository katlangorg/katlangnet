import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

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

end KatLangTests
