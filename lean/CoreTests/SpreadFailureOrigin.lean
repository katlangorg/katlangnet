import KatLang
import CoreTests.Common

/-!
# Spread failure origin (X-29 / Q-36, decided 2026-10-24)

Spread preserves failures originating within its operand's dependencies or arguments, including
their category, cause and blame; only the operand's OWN missing output becomes
`spreadMissingOutput`. The origin is part of the completed failure (`MissingOutputOrigin`): the
output check of the demanded computation raises it `own`, and a subordinate computation's failure
is `nested` in its consumer's outcome (`withNestedMissingOutput`). The spread reads it through
`spreadOperandFailure`, which evaluates nothing. C# twins: `SpreadFailureOriginTests`; the
differential corpora pin the same programs through both production evaluators.
-/

namespace KatLangTests
open KatLang (alg algPrivate algWithParameters runResult Algorithm Error Result MissingOutputOrigin)

/-- A brace body with a property and no written output: `{ X = 1 }`. -/
def originNoOutputAlg : Algorithm :=
  algPrivate [] [] [("X", alg [] [] [] [.num 1])] []

/-- `G = { X = 1 }` (no output), `H = G + 1`, `F(x) = x`, `P(x) = x*`. -/
def originRoot (row : KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("G", originNoOutputAlg),
    ("H", alg [] [] [] [.binary .add (.resolve "G") (.num 1)]),
    ("F", alg ["x"] [] [] [.param "x"]),
    ("P", alg ["x"] [] [] [sequenceSpread (.param "x")]),
    ("C", algWithParameters [{ name := "xs", kind := .collecting }] [] [] [sequenceSpread (.param "xs")])
  ] [row])

def originEmptyBlock : KatLang.Expr := .algorithmExpr originNoOutputAlg

/-- The context frames of a failure, outermost first. -/
def originContextFrames : Error → List String
  | .withContext c inner => c :: originContextFrames inner
  | _ => []

/-- The failure under its context frames. -/
def originInnermostError : Error → Error
  | .withContext _ inner => originInnermostError inner
  | err => err

/-- The run fails with exactly these frames around the spread operand's OWN missing output. -/
def originFailsSpreadOwn (frames : List String) (row : KatLang.Expr) : Bool :=
  match runResult (originRoot row) with
  | .error err => originContextFrames err == frames && (originInnermostError err matches .spreadMissingOutput)
  | .ok _ => false

/-- The run fails with exactly these frames around a NESTED missing output. -/
def originFailsNested (frames : List String) (row : KatLang.Expr) : Bool :=
  match runResult (originRoot row) with
  | .error err => originContextFrames err == frames && (originInnermostError err matches .missingOutput .nested)
  | .ok _ => false

def originSucceedsEmpty (row : KatLang.Expr) : Bool :=
  match runResult (originRoot row) with
  | .ok (.sequenceValue []) => true
  | _ => false

-- Direct missing output: the computation the operand denotes or invokes has none.
#guard originFailsSpreadOwn [] (sequenceSpread originEmptyBlock)                              -- {}*
#guard originFailsSpreadOwn ["while evaluating property G"] (sequenceSpread (.resolve "G")) -- G*
#guard originFailsSpreadOwn ["while evaluating call to G"] (sequenceSpread (.call (.resolve "G") [])) -- G()*

-- Nested missing output: category, cause (`G`) and blame kept, the spread operand added.
#guard originFailsNested ["while evaluating spread operand H", "while evaluating property G"]
  (sequenceSpread (.resolve "H"))                                                -- H*
#guard originFailsNested ["while evaluating spread operand (call)", "while evaluating call to H",
    "while evaluating property G"]
  (sequenceSpread (.call (.resolve "H") []))                                     -- H()*
-- `F({})*` keeps exactly the frames `F({})` reports, under the spread operand.
#guard originFailsNested ["while evaluating call to F"] (.call (.resolve "F") [originEmptyBlock])
#guard originFailsNested ["while evaluating spread operand (call)", "while evaluating call to F"]
  (sequenceSpread (.call (.resolve "F") [originEmptyBlock]))                           -- F({})*
#guard originFailsNested ["while evaluating spread operand (inline library)", "while evaluating property G"]
  (sequenceSpread (.algorithmExpr (alg [] [] [] [.resolve "G"])))               -- { G }*
#guard originFailsNested ["while evaluating spread operand (inline library)", "while evaluating property G"]
  (sequenceSpread (.capture [.resolve "G", .num 1]))                             -- (G, 1)*
#guard originFailsNested ["while evaluating spread operand (listLiteral)", "while evaluating property G"]
  (sequenceSpread (.listLiteral [.resolve "G"]))                                 -- [G]*
#guard originFailsNested ["while evaluating spread operand (call)", "while evaluating call to if",
    "while evaluating property G"]
  (sequenceSpread (.call (.resolve "if") [.boolLiteral true, .resolve "G", .num 1]))

-- Empty values and supplies are not missing output.
#guard originSucceedsEmpty (sequenceSpread (.emptySequence 0))                          -- ()*
#guard originSucceedsEmpty (sequenceSpread (.listLiteral []))                           -- []*

-- Ordinary failures are the operand's own, unchanged; an inner spread keeps its own report.
#guard match runResult (originRoot (sequenceSpread (.binary .div (.num 1) (.num 0)))) with
  | .error .divByZero => true
  | _ => false
#guard originFailsSpreadOwn [] (sequenceSpread (.capture [sequenceSpread originEmptyBlock])) -- ({}*)*

-- A failed spread slot supplies nothing: its failure precedes arity and callback roles.
#guard originFailsNested ["while evaluating call to count", "while evaluating spread operand H",
    "while evaluating property G"]
  (.call (.resolve "count") [.num 1, sequenceSpread (.resolve "H")])
#guard originFailsSpreadOwn ["while evaluating call to count"]
  (.call (.resolve "count") [.num 1, sequenceSpread originEmptyBlock])
#guard originFailsNested ["while evaluating call to map", "while evaluating spread operand H",
    "while evaluating property G"]
  (.call (.resolve "map") [.listLiteral [], sequenceSpread (.resolve "H")])

-- Parameter forwarding is transparent: `x` denotes the supplied computation, so a directly
-- output-less argument is the spread's own report and a dependency's failure stays nested —
-- also through the argument's completed need cell.
#guard originFailsSpreadOwn ["while evaluating call to P"] (.call (.resolve "P") [originEmptyBlock])
#guard originFailsSpreadOwn ["while evaluating call to P", "while evaluating property G"]
  (.call (.resolve "P") [.resolve "G"])
#guard originFailsNested ["while evaluating call to P", "while evaluating spread operand x",
    "while evaluating property G"]
  (.call (.resolve "P") [.resolve "H"])
#guard originFailsNested ["while evaluating call to P", "while evaluating spread operand x",
    "while evaluating property G"]
  (.call (.resolve "P") [.listLiteral [.resolve "G"]])

-- A collector constructs its exact list; failure of an element is nested in its completed cell.
#guard originFailsNested ["while evaluating call to C", "while evaluating spread operand xs",
    "while evaluating property G"]
  (.call (.resolve "C") [.resolve "G"])

-- The origin is a property of the completed failure, never of a consumer: the classifier and
-- the nesting are total functions of the error, and nesting is idempotent.
#guard KatLang.isOwnMissingOutputError (.withContext "c" (.missingOutput .own))
#guard !KatLang.isOwnMissingOutputError (.withContext "c" (.missingOutput .nested))
#guard KatLang.isMissingOutputError (.withContext "c" (.missingOutput .nested))
#guard (Error.nestMissingOutput (.withContext "c" (.missingOutput .own))) matches
  .withContext "c" (.missingOutput .nested)
#guard (Error.nestMissingOutput .divByZero) matches .divByZero
#guard (Error.nestMissingOutput .spreadMissingOutput) matches .spreadMissingOutput
#guard (KatLang.spreadOperandFailure (.resolve "H") .divByZero) matches .divByZero

end KatLangTests
