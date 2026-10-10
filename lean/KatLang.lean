-- KatLang authoritative language model (core AST + semantics + while/repeat init boundaries + higher-order alg params + conditional algorithms + first-class strings).
-- Release version: see KatLangVersion.props.
-- Core semantics are authoritative. Surface syntax handled externally except
-- where noted (implicit parameter detection, while/repeat init boundaries).
-- Load elaboration is handled entirely in the front-end / elaboration layer;
-- the core AST never contains load nodes (see load elaboration section below).
--
-- Numeric model:
--   The Lean core uses unbounded Int while the C# runtime uses IEEE 754
--   Decimal128 (34-significant-digit decimal floating point).
--   The integer-valued operations use truncation toward zero (Int.tdiv /
--   Int.tmod). On the common exact integer subdomain this agrees with the C#
--   reference, including negative operands (`-7 div 2 = -3`,
--   `-7 mod 2 = -1`). This is not a blanket "integer source = shared model"
--   rule: large integral arithmetic can round or overflow in the
--   finite-precision runtime. `div` itself truncates the EXACT quotient there
--   too (G-3, September 2026 — never a quotient first rounded to 34 digits)
--   and is exact wherever the truncated quotient is representable: every
--   |q| <= 10^34 (the exact consecutive-integer domain) and every representable
--   sparse integer beyond it; a truncated quotient with more than 34
--   significant digits is rounded toward zero to 34 digits in the runtime
--   while this core keeps the exact integer. Fractional
--   results the decimal runtime can represent are another documented Int-core
--   limitation: `/`-style quotients and the `avg` builtin truncate here
--   (`7 / 2 = 3` and `avg((1, 2)) = 1`) but yield decimals in the runtime
--   (`3.5` and `1.5`), and negative exponents with
--   |base| >= 2 raise an explicit error instead of silently truncating the
--   reciprocal to 0 (see `negativeIntPow`). Zero raised to a negative
--   exponent is a language error in BOTH models: the runtime rejects EVERY
--   exponent below zero (`0 ^ -1`, `0 ^ -0.5`, `Math.Pow(0, -2.5)` alike —
--   a negative power of zero is reciprocal-like, and a zero divisor is an
--   error, never IEEE `Infinity`), and the Int core states that same rule at
--   its only reachable instance, integer exponents. Fractional exponents
--   have no Int counterpart, so this is a documented model boundary, not a
--   narrower runtime rule.
--   IEEE special values and range behavior exist only in the runtime: NaN,
--   ±Infinity, signed zero, overflow to infinity, and gradual underflow
--   (subnormals and eventual zero) have no Int
--   counterpart, so the core neither models nor approximates them — they are
--   pinned as C#-only canonical cases in the executable language spec
--   (the LanguageSpecCorpus model-divergence family) and stay excluded from
--   the Lean-guarded corpora. The routing rule for numeric changes is the
--   "Core numeric semantics" row in src/KatLang/SEMANTIC-ALIGNMENT.md.
--
-- Open declarations:
--   `open` is a DECLARATION keyword, not a property assignment.
--   Exact syntax: `open target1, target2, ...` (no `=` sign).
--   Each algorithm may contain at most ONE `open` declaration with a comma-separated
--   list of targets. The opens list maps to `Algorithm.opens : List Expr`.
--
--   Valid open targets (post-elaboration / canonical forms):
--     - identifier:     `open Math`            → Resolve("Math")
--     - dotted path:    `open Lib.Sub`         → DotCall(Resolve("Lib"), "Sub", none)
--     - load:           `open load('url')`     → Call(Resolve("load"), ...) → elaborated to Block (surface-only, not in core Expr)
--     - inline block:   `open { public X = 1 }` → Block(...)
--
--   Exact-syntax sugar (parser-only, not in core model):
--     - `open 'url'` desugars to `open load('url')` before elaboration.
--     Raw string literals do NOT survive into the canonical open list.
--
-- Clause-definition syntax (parser-only, not in core model):
--   Clause-style definitions use syntax:
--     `Name(pattern) = body`
--   This form is recognized only in definition position.
--   In expression position, `Name(args)` remains an ordinary call.
--   On the left-hand side of `=` in definition context, `Name(...)` is not a
--   call expression — it is clause-pattern syntax.
--
--   Elaboration / classification rule:
--     - a same-name clause group elaborates to ordinary `Algorithm.mk` only
--       when the group contains exactly one clause and that sole head is a
--       recursive parameter pattern made only of captures and structural
--       (sequence or list) patterns (for example `Apply(f) = f(4)`,
--       `PairSum((x, y)) = x + y`, `Only([x]) = x`, or
--       `CountSequenceValue((*values)) = values.count`)
--     - multi-clause families and clause heads that require literal or
--       whole-argument conditional matching elaborate to `Algorithm.conditional`
--
--   This split is intentional: ordinary elaboration preserves dual-view call
--   binding for higher-order arguments, while true conditional algorithms keep
--   their full-input-specification and whole-argument matching semantics.
--
-- Structural patterns (September 2026): STRUCTURAL PATTERN DELIMITERS SELECT
--   THE VALUE KIND THEY DESTRUCTURE. In both pattern languages a
--   parenthesized structural pattern `(p1, …, pn)` (`sequenceValue`) matches
--   SEQUENCE values only and a bracketed structural pattern `[p1, …, pn]`
--   (`listValue`) matches LIST values only; neither destructures the other
--   kind, and neither treats a scalar as a one-item structure. A bare
--   binder is the only pattern that takes a value whole, whatever its kind.
--   Because there is no one-item sequence value (`Result.normalize`), a
--   sequence pattern with exactly one non-collecting item — `(x)`, `((x, y))`,
--   `([x])` — describes a boundary no value has and is INVALID
--   (`ParameterPattern.hasSingletonSequenceGroup`,
--   `Pattern.headHasSingletonSequenceGroup`, rejected before evaluation by
--   `validateExplicitParamOutputInvariant`; the C# parser reports
--   `SingletonSequencePattern`), while a collector-only `(*xs)` stays valid
--   because a collector is variadic. The one-element pattern is the list
--   pattern `[x]`. The call head's own parentheses are the call's argument
--   list, never a structural pattern.
--
-- Algorithm output (surface syntax):
--   Every non-definition expression row in an algorithm body contributes to
--   the Algorithm's `output` field. Output rows and property definitions may
--   be interleaved; there is no dedicated output keyword or output-definition
--   syntax, and `Output`/`output` are ordinary identifiers with no special
--   treatment (`Output = expr` is an ordinary property definition).
--
--   Semantic rules (enforced by evaluator, not parser):
--     - Opens provide PUBLIC properties only (lookupOpenProperties filters by isPublic).
--     - Strict isolation: opening a library does NOT import its transitive opens.
--     - Ambiguity: if multiple open targets provide the same public name, and no
--       owned/local/parent property shadows it, `ambiguousOpen` is raised.
--     - Owned/local/parent lookup takes precedence over opens (ownership-first).
--
-- Evaluator architecture (details: comment above the evaluator `mutual` block):
--   The single evaluator `mutual` block is intentionally evaluation-only: it
--   contains the runtime evaluation recursion plus thin wrappers over that
--   recursion, and nothing else. Name/open/lexical resolution, parameter-
--   pattern binding, pure sequence-builtin computations, and argument-shape
--   helpers are total definitions outside the evaluator cycle. Shrinking the
--   block further means touching genuine evaluation recursion, so treat any
--   future reduction as a semantic refactor (for example counted/non-counted
--   unification or a fuel-indexed total evaluator), not an extraction cleanup.

universe u v

namespace KatLang

--------------------------------------------------------------------------------
-- Typed identifiers (lightweight aliases for future-proofing)
--------------------------------------------------------------------------------

abbrev Ident := String    -- algorithm / property / parameter names
abbrev Assoc (K V : Type) := List (Prod K V)  -- association list

inductive ParameterKind where
  | normal
  | collecting
  deriving Repr, BEq, DecidableEq

structure CallableParameter where
  name : Ident
  kind : ParameterKind := .normal
  deriving Repr, BEq

/-- A parameter pattern of the ORDINARY pattern language: a capture, or a
    structural pattern whose delimiter selects the value kind it destructures —
    `sequenceValue` is the parenthesized sequence pattern `(p1, …, pn)`, which
    opens SEQUENCE values only, and `listValue` is the bracketed list pattern
    `[p1, …, pn]`, which opens LIST values only (see the file header, Structural
    patterns).

    `unpacking` is NOT written syntax: it is the UNPACKING RECEIVER of assignment
    deconstruction (`x, *rest, z = RHS`), which the front end elaborates into one
    per-target helper whose single parameter pattern is `unpacking [targets]`,
    applied to the hoisted right-hand side. It binds its target list against the
    ONE-LEVEL items of the supplied value — a sequence or a list opens one level,
    and any other value is one item (`Result.spreadItems`) — so a lone structure
    of either kind is split while a scalar is one target's value
    (`x, *rest = 1` binds `rest = []`). It has no delimiter that could select a
    value kind, so it opens both kinds alike; the kind-specific structural
    patterns never do. (The algebra's `CoreArityAlgebra.bindDeconstruct` /
    `openLoneStructure` is this receiver.) The right-hand side is demanded as an
    ORDINARY value, so a right-hand side without output is its own missing-output
    failure — never a spread failure.
    C#: `CaptureParameterPattern` / `SequenceValueParameterPattern` /
    `ListValueParameterPattern` / `UnpackingParameterPattern`. -/
inductive ParameterPattern where
  | capture : CallableParameter -> ParameterPattern
  | sequenceValue : List ParameterPattern -> ParameterPattern
  | listValue : List ParameterPattern -> ParameterPattern
  | unpacking : List ParameterPattern -> ParameterPattern
  deriving Repr, BEq

structure CallableSignature where
  name : Ident
  parameters : List CallableParameter
  deriving Repr, BEq

def CallableParameter.displayName (parameter : CallableParameter) : String :=
  match parameter.kind with
  | .normal => parameter.name
  | .collecting => "*" ++ parameter.name

namespace ParameterPattern
  partial def captures : ParameterPattern -> List CallableParameter
    | .capture parameter => [parameter]
    | .sequenceValue items => items.flatMap captures
    | .listValue items => items.flatMap captures
    | .unpacking items => items.flatMap captures

  def fromParameters (parameters : List CallableParameter) : List ParameterPattern :=
    parameters.map .capture

  def normalPatterns (ps : List Ident) : List ParameterPattern :=
    ps.map (fun p => .capture { name := p })

  /-- Whether a pattern is a structural pattern — a sequence pattern `(…)`, a
      list pattern `[…]`, or the deconstruction unpacking receiver — rather than
      a capture. -/
  def isStructural : ParameterPattern -> Bool
    | .capture _ => false
    | .sequenceValue _ => true
    | .listValue _ => true
    | .unpacking _ => true

  def hasStructured (patterns : List ParameterPattern) : Bool :=
    patterns.any isStructural

  /-- True when the pattern list itself contains a collecting binding (nested
      captures inside structural patterns do not count).
      C#: `ParameterPattern.HasCollectingCaptureAtCurrentLevel`. -/
  def hasCollectingCaptureAtCurrentLevel (patterns : List ParameterPattern) : Bool :=
    patterns.any (fun
      | .capture parameter => parameter.kind == ParameterKind.collecting
      | _ => false)

  /-- The MINIMUM number of supplied argument slots a parameter-pattern list
      accepts — the ONE rule the binder enforces, factored out so no other layer can
      re-derive it (the Model-C binder reads the same count over need patterns,
      `needMinimumSuppliedSlots` in `bindNeedLevel`, which agrees with this one on
      every valid signature; formerly `bindParameterPatternList`):

      * every pattern consumes exactly ONE supplied slot, whatever it contains —
        a structural pattern (sequence or list) is one slot that the binder
        opens afterwards, so nested structure never changes the count at this
        level;
      * a collecting capture at THIS level consumes NONE: it collects whatever
        slots are left over after the fixed prefix and suffix bind, and an empty
        leftover is the exact empty list (`collectSegment [] = []`).

      So `Only(*xs)` accepts zero supplied slots, while `Head(x, *rest)`,
      `Tail(*rest, z)`, `P((x, *rest))` and `Pair(x, y)` each require at least
      one. A list with two collecting captures is a rejected signature, never a
      lower minimum. C#: `ParameterPattern.MinimumSuppliedSlots`. -/
  def minimumSuppliedSlots (patterns : List ParameterPattern) : Nat :=
    if hasCollectingCaptureAtCurrentLevel patterns then patterns.length - 1 else patterns.length

  mutual
    /-- Whether a pattern binds `name` at any depth — the STATIC fact the
        historical Ready binders read to tell whether every contribution of a
        repeated name at one level is already known (`settlePatternRange`,
        `HistoricalReadyBinding.lean`). Total, so the binder bridge laws can
        unfold it. It has no C# twin (the pointer `ParameterPatternBindsName`
        named a function that never existed). -/
    def bindsName (name : Ident) : ParameterPattern -> Bool
      | .capture parameter => parameter.name == name
      | .sequenceValue items => anyBindsName name items
      | .listValue items => anyBindsName name items
      | .unpacking items => anyBindsName name items

    /-- Whether any pattern of a list binds `name` at any depth. -/
    def anyBindsName (name : Ident) : List ParameterPattern -> Bool
      | [] => false
      | pattern :: rest => bindsName name pattern || anyBindsName name rest
  end

  /-- REPEATED NAMES ARE CONSTRAINTS, NOT MERGES (September 2026, Q-05): whether
      TWO OR MORE patterns of one pattern level bind `name` (at any depth inside
      each) — a REPEATED name of that level. Every occurrence of such a name is an
      independent contribution to an equality constraint, so a top-level capture of
      it must supply its OWN value; another occurrence can never stand in for a
      value it lacks. Since Model C the binder computes repeated names itself and
      demands each occurrence's own cell when it visits it (`bindNeedPatterns`,
      `bindNeedName`); this predicate serves the historical Ready binder
      (`bindParameterPattern`, `HistoricalReadyBinding.lean`) and the laws. Its C#
      twin `Evaluator.RepeatsAtLevel` was deleted with Model C. -/
  def repeatsAtLevel (name : Ident) (level : List ParameterPattern) : Bool :=
    2 ≤ (level.filter (bindsName name)).length

  def topLevelCaptureKind? (name : Ident) : List ParameterPattern -> Option ParameterKind
    | [] => none
    | .capture parameter :: rest =>
        if parameter.name = name then some parameter.kind else topLevelCaptureKind? name rest
    | .sequenceValue _ :: rest => topLevelCaptureKind? name rest
    | .listValue _ :: rest => topLevelCaptureKind? name rest
    | .unpacking _ :: rest => topLevelCaptureKind? name rest

  /-- The written form of a pattern, for diagnostics: `x`, `*xs`, `(x, y)`,
      `[x, *rest]`, and a deconstruction's written target list `x, *rest`.
      C#: `ParameterPattern.DisplayName`. -/
  partial def displayName : ParameterPattern -> String
    | .capture parameter => parameter.displayName
    | .sequenceValue items => "(" ++ String.intercalate ", " (items.map displayName) ++ ")"
    | .listValue items => "[" ++ String.intercalate ", " (items.map displayName) ++ "]"
    | .unpacking items => String.intercalate ", " (items.map displayName)

  /-- THE SINGLETON RULE (September 2026): a sequence pattern whose items are
      exactly ONE non-collecting pattern describes a one-item sequence boundary,
      and KatLang has no one-item sequence value (`Result.normalize` collapses
      it), so no value could ever match it. `(x)`, `((x, y))` and `([x])` are
      therefore invalid, while the collector-only `(*xs)` is valid: a collector
      is variadic and stands for a sequence's elements, not for a sequence of
      one. A list pattern has no such rule — lists keep every cardinality, so
      `[x]` is the one-element structural pattern.
      C#: `ParameterPattern.IsSingletonSequenceItems`. -/
  def isSingletonSequenceItems : List ParameterPattern -> Bool
    | [.capture parameter] =>
        match parameter.kind with
        | .normal => true
        | .collecting => false
    | [.sequenceValue _] => true
    | [.listValue _] => true
    | [.unpacking _] => true
    | _ => false

  mutual
    /-- Whether a pattern contains an invalid singleton sequence pattern at any
        depth (the singleton rule above). -/
    def hasSingletonSequenceGroup : ParameterPattern -> Bool
      | .capture _ => false
      | .sequenceValue items => isSingletonSequenceItems items || anyHasSingletonSequenceGroup items
      | .listValue items => anyHasSingletonSequenceGroup items
      | .unpacking items => anyHasSingletonSequenceGroup items

    /-- Whether any pattern of a list contains an invalid singleton sequence
        pattern at any depth. -/
    def anyHasSingletonSequenceGroup : List ParameterPattern -> Bool
      | [] => false
      | pattern :: rest => hasSingletonSequenceGroup pattern || anyHasSingletonSequenceGroup rest
  end

  /-- The number of collecting captures at ONE pattern level; captures nested
      inside a structural pattern belong to that pattern's own level. -/
  def collectingCaptureCountAtCurrentLevel : List ParameterPattern -> Nat
    | [] => 0
    | .capture parameter :: rest =>
        (if parameter.kind == ParameterKind.collecting then 1 else 0)
          + collectingCaptureCountAtCurrentLevel rest
    | .sequenceValue _ :: rest => collectingCaptureCountAtCurrentLevel rest
    | .listValue _ :: rest => collectingCaptureCountAtCurrentLevel rest
    | .unpacking _ :: rest => collectingCaptureCountAtCurrentLevel rest

  mutual
    /-- Whether some pattern level NESTED in a pattern holds more than one
        collecting capture. -/
    def hasMultipleCollectingLevel : ParameterPattern -> Bool
      | .capture _ => false
      | .sequenceValue items =>
          1 < collectingCaptureCountAtCurrentLevel items || anyHasMultipleCollectingLevel items
      | .listValue items =>
          1 < collectingCaptureCountAtCurrentLevel items || anyHasMultipleCollectingLevel items
      | .unpacking items =>
          1 < collectingCaptureCountAtCurrentLevel items || anyHasMultipleCollectingLevel items

    /-- Whether some pattern level nested in any pattern of a list holds more
        than one collecting capture. -/
    def anyHasMultipleCollectingLevel : List ParameterPattern -> Bool
      | [] => false
      | pattern :: rest => hasMultipleCollectingLevel pattern || anyHasMultipleCollectingLevel rest
  end

  /-- AT MOST ONE COLLECTING CAPTURE PER PATTERN LEVEL: whether a pattern list,
      or some level nested in it, holds more than one. The binders allocate a
      level's supply around ONE movable collector (`findCollecting`), so a second
      collector at the same level leaves the allocation undefined: such a list is
      a rejected signature, never a lower minimum (`minimumSuppliedSlots`).
      C#: `ParameterPattern.HasMultipleCollectingCapturesAtAnyLevel`. -/
  def hasMultipleCollectingCapturesAtAnyLevel (patterns : List ParameterPattern) : Bool :=
    1 < collectingCaptureCountAtCurrentLevel patterns || anyHasMultipleCollectingLevel patterns

  mutual
    /-- The names of the COLLECTING captures of a pattern, at any depth, left to
        right. Total (unlike `captures`), so the validity laws evaluate. -/
    def collectingNames : ParameterPattern -> List Ident
      | .capture parameter => if parameter.kind == ParameterKind.collecting then [parameter.name] else []
      | .sequenceValue items => anyCollectingNames items
      | .listValue items => anyCollectingNames items
      | .unpacking items => anyCollectingNames items

    def anyCollectingNames : List ParameterPattern -> List Ident
      | [] => []
      | pattern :: rest => collectingNames pattern ++ anyCollectingNames rest
  end

  mutual
    /-- How many captures of a pattern bind `name`, at any depth. -/
    def nameOccurrences (name : Ident) : ParameterPattern -> Nat
      | .capture parameter => if parameter.name == name then 1 else 0
      | .sequenceValue items => anyNameOccurrences name items
      | .listValue items => anyNameOccurrences name items
      | .unpacking items => anyNameOccurrences name items

    def anyNameOccurrences (name : Ident) : List ParameterPattern -> Nat
      | [] => 0
      | pattern :: rest => nameOccurrences name pattern + anyNameOccurrences name rest
  end

  /-- Whether a repeated capture name includes a collecting binding: a written
      head may repeat a name only among fixed captures (Q-05's constraints), never
      with a collector. C#: `ParameterPattern.HasRepeatedCaptureNameIncludingCollecting`. -/
  def hasRepeatedCaptureNameIncludingCollecting (patterns : List ParameterPattern) : Bool :=
    (anyCollectingNames patterns).any (fun name => 2 ≤ anyNameOccurrences name patterns)

  /-- The rule a parameter-pattern list breaks as a callable SIGNATURE, in rule
      order. C#: `ParameterSignatureViolation`. -/
  inductive SignatureViolation where
    | singletonSequencePattern
    | multipleCollectingAtOneLevel
    | repeatedNameIncludesCollecting
    deriving Repr, DecidableEq, BEq

  /-- THE STRUCTURAL VALIDITY OF A SIGNATURE (X-02, September 30 2026): the first
      rule a parameter-pattern list breaks as a callable signature, or `none` for
      a valid one — no one-item sequence pattern at any depth (the singleton
      rule), at most one collecting capture per pattern level, and no repeated
      name that includes a collecting binding. These are exactly the rules a
      WRITTEN parameter list is held to, and the C# front end holds every
      INFERRED signature to them too: formula lifting that would compose an
      invalid contract (`C1(a, *p)`, `C2(b, *q)`, `K = C1 + C2` would give
      `K(a, *p, b, *q)`) is the definition's front-end error, never a signature
      that reaches a binder. A collecting name two callees share is ONE binding
      (`K(a, *rest, b)` is valid), and a collector nested in its own group is its
      group's level. C#: `ParameterPattern.FindSignatureViolation`. -/
  def signatureViolation? (patterns : List ParameterPattern) : Option SignatureViolation :=
    if anyHasSingletonSequenceGroup patterns then some .singletonSequencePattern
    else if hasMultipleCollectingCapturesAtAnyLevel patterns then some .multipleCollectingAtOneLevel
    else if hasRepeatedCaptureNameIncludingCollecting patterns then some .repeatedNameIncludesCollecting
    else none
end ParameterPattern

def callableParameterNameStartChar (c : Char) : Bool :=
  c == '_' || c.isAlpha

def callableParameterNameRestChar (c : Char) : Bool :=
  c == '_' || c.isAlphanum

def callableParameterNameIsIdentifierLike (name : Ident) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
      callableParameterNameStartChar first && rest.all callableParameterNameRestChar

def CallableSignature.collectingCount (signature : CallableSignature) : Nat :=
  (signature.parameters.filter (fun parameter => parameter.kind == ParameterKind.collecting)).length

def CallableSignature.hasAtMostOneCollecting (signature : CallableSignature) : Bool :=
  signature.collectingCount <= 1

def CallableSignature.emptyParameterName? (signature : CallableSignature) : Bool :=
  signature.parameters.any (fun parameter => parameter.name == "")

def CallableSignature.invalidParameterName? (signature : CallableSignature) : Option Ident :=
  (signature.parameters.find? fun parameter =>
    parameter.name != "" && !callableParameterNameIsIdentifierLike parameter.name).map (fun parameter => parameter.name)

def CallableSignature.duplicateParameterName? (signature : CallableSignature) : Option Ident :=
  let rec go : List Ident -> List CallableParameter -> Option Ident
    | _, [] => none
    | seen, parameter :: rest =>
        if seen.contains parameter.name then
          some parameter.name
        else
          go (parameter.name :: seen) rest
  go [] signature.parameters

def CallableSignature.validationError? (signature : CallableSignature) : Option String :=
  if !signature.hasAtMostOneCollecting then
    some s!"Callable signature `{signature.name}` cannot contain more than one collecting parameter."
  else if signature.emptyParameterName? then
    some s!"Callable signature `{signature.name}` contains an empty parameter name."
  else
    match signature.invalidParameterName? with
    | some parameterName =>
        some s!"Callable signature `{signature.name}` contains invalid parameter name `{parameterName}`."
    | none =>
        match signature.duplicateParameterName? with
        | some parameterName =>
            some s!"Callable signature `{signature.name}` contains duplicate parameter name `{parameterName}`."
        | none => none

def CallableSignature.collectingIndex? (signature : CallableSignature) : Option Nat :=
  let rec go : Nat -> List CallableParameter -> Option Nat
    | _, [] => none
    | index, parameter :: rest =>
        match parameter.kind with
        | .collecting => some index
        | .normal => go (index + 1) rest
  go 0 signature.parameters

def CallableSignature.requiredNormalParameterCount (signature : CallableSignature) : Nat :=
  (signature.parameters.filter (fun parameter => parameter.kind == ParameterKind.normal)).length

def CallableSignature.acceptsItemCount (signature : CallableSignature) (count : Nat) : Bool :=
  -- A collecting user signature consumes an item supply: it accepts at least
  -- the fixed (non-collecting) count. Fixed signatures, including collection
  -- builtins, stay exact.
  match signature.collectingIndex? with
  | some _ => count >= signature.requiredNormalParameterCount
  | none => count == signature.parameters.length

structure CallableArgumentBindings (α : Type) where
  normalBindings : List (Prod Ident α)
  collectingName? : Option Ident := none
  collectingItems : List α := []
  deriving Repr

/-- Exposure classification of a `PropDef`: an INPUT to lookup, computed by the C# front
    end and never derived here. SELECTION never depends on it: `open` selects public
    members and structural dot access selects declared members; whether the selected
    member may be USED at an access site is `memberAccessible?`, decided after selection.
    `.localCapturedAncestorParams required`: the value requires the inputs `required`,
    which only an enclosing owner's call binds (a parameter, or a conditional branch's
    pattern binder) — the member is LOCAL-CONTEXT-DEPENDENT, usable from every lexical
    context inside the owner of each required name and refused everywhere else, never
    universally hidden. `.localConditional` is the family-level reason a name access
    into a conditional's branch bodies is refused (`conditionalBranchesDefineProperty`);
    the front end never assigns it to a `PropDef` — a branch's own declarations classify
    exactly like declarations in any other body. -/
inductive PropExposure where
  | exported
  | localCapturedAncestorParams (required : List Ident)
  | localConditional
  deriving Repr, DecidableEq

namespace PropExposure
  def isExported : PropExposure -> Bool
    | .exported => true
    | _ => false
end PropExposure

--------------------------------------------------------------------------------
-- Errors / Monad
--------------------------------------------------------------------------------

inductive Error where
  | unknownName      : Ident -> Error
  | unknownProperty  : String -> Ident -> Error        -- object desc, property name
  | notPublicProperty : String -> Ident -> Error       -- object desc, property name (exists but private)
  | localOnlyProperty : String -> Ident -> PropExposure -> Error  -- object desc, property name, reason
  | notAnAlgorithm   : String -> Error          -- an invoking position received no callable identity (Q-06)
  | illegalInOpen    : String -> Error                -- semantic restriction (e.g., builtin not allowed)
  | badOpenForm      : String -> Error                -- syntactic form not allowed in open
  | illegalInEval    : String -> Error                -- a value outside the operation's domain (Q-27), or not evaluable
  | ambiguousOpen    : Ident -> List String -> Error   -- name, providers
  | arityMismatch    : Nat -> Nat -> Error     -- supply cardinality: expected, actual
  | badArity         : Error                   -- supply/output cardinality without a count (Q-27)
  | typeMismatch     : String -> Error          -- a present value of the wrong kind (Q-27)
  | badIndex         : Error                   -- a selection names no position (first/last included)
  | divByZero        : Error                   -- division or modulo by zero
  | demandCycle      : Error                   -- a VALUE demand re-enters its evaluating cell
  | noMatchingBranch : Ident -> Error          -- conditional algorithm: no branch matched
  | branchArityMismatch : Ident -> Nat -> Nat -> Error  -- conditional algorithm: branch top-level arity mismatch (name, expected, actual); raised by pre-evaluation validation (validateBranchArities)
  | branchOutputArityMismatch : Ident -> Nat -> Nat -> Error  -- conditional algorithm: branch top-level output arity mismatch (name, expected, actual); raised by pre-evaluation validation (validateBranchOutputArities)
  | duplicateProperty : Ident -> Error         -- algorithm defines the same property name more than once
  | duplicateBranchPattern : Error             -- conditional algorithm has match-equivalent branch patterns
  | explicitParamsRequireOutput : Error        -- explicit algorithm params require an algorithm output
  | missingOutput    : Error                   -- forced user-defined algorithm does not define output
  | spreadMissingOutput : Error          -- spread operand produced no output
  | unresolvedImplicitParams : List Ident -> Error  -- top-level block has unresolved implicit parameters
  | withContext      : String -> Error -> Error -- contextual wrapper
  deriving Repr

-- * IMPORTANT: Needed for compiling `partial` definitions.
-- Lean requires `Nonempty` for the function types of partial defs.
instance : Nonempty Error := Nonempty.intro Error.badArity

def CallableSignature.validate (signature : CallableSignature) : Except Error Unit :=
  match signature.validationError? with
  | some message => .error (Error.illegalInEval message)
  | none => .ok ()

/-- Variable-middle collecting-parameter binding over completed items, used by the arity laws (no production
    caller since Model C; its former C# mirror `BindCallableArguments` was deleted with it). The fixed
    prefix binds from the front, the fixed suffix from the back, and the collecting
    captures the remaining middle items (zero or more). The minimum is the FIXED
    (non-collecting) parameter count: like every other collecting binding, the collecting parameter may
    collect ZERO items (an empty collected segment is the exact list `[]`) — the same rule the
    shared pattern binder applies (`needMinimumSuppliedSlots`: required =
    patterns - 1; formerly `bindParameterPatternList`).
    (Collection builtins no longer bind here: they are ordinary fixed-arity
    callables bound in `bindSequenceBuiltinArguments`.) -/
def bindCallableArguments (signature : CallableSignature) (items : List α)
    (arityMismatch : Nat -> Nat -> Error)
    : Except Error (CallableArgumentBindings α) :=
  match signature.validate with
  | .error err => .error err
  | .ok () =>
      match signature.collectingIndex? with
      | none =>
          if items.length == signature.parameters.length then
            .ok {
              normalBindings := List.zip (signature.parameters.map (fun parameter => parameter.name)) items
            }
          else
            .error (arityMismatch signature.parameters.length items.length)
      | some collectingIndex =>
          -- Minimum = fixed (non-collecting) parameter count, so the collecting binding may
          -- collect zero items (empty collected segment = `[]`) at every receiver,
          -- including loop-state binding.
          let minimum := signature.parameters.length - 1
          if items.length < minimum then
            .error (arityMismatch minimum items.length)
          else
            let suffixParameters := signature.parameters.drop (collectingIndex + 1)
            let suffixCount := suffixParameters.length
            let suffixStart := items.length - suffixCount
            let prefixParameters := signature.parameters.take collectingIndex
            let prefixItems := items.take collectingIndex
            let suffixItems := items.drop suffixStart
            let middleItems := (items.drop collectingIndex).take (suffixStart - collectingIndex)
            .ok {
              normalBindings :=
                (List.zip (prefixParameters.map (fun parameter => parameter.name)) prefixItems) ++
                (List.zip (suffixParameters.map (fun parameter => parameter.name)) suffixItems)
              collectingName? := (signature.parameters.drop collectingIndex).head?.map (fun parameter => parameter.name)
              collectingItems := middleItems
            }

--------------------------------------------------------------------------------
-- Operators
--------------------------------------------------------------------------------

/-- The binary operators: arithmetic (numeric scalar operands, numeric result)
    and the logical operators (Boolean operands, Boolean result). The six
    comparison operators are NOT binary operators — they are the links of a
    comparison chain (`ComparisonOp`, `Expr.comparison`). C#: `BinaryOp`. -/
inductive BinaryOp where
  | add | sub | mul | div | idiv | mod | pow
  | and | or | xor
  deriving Repr, BEq, DecidableEq

def BinaryOp.symbol : BinaryOp -> String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .idiv => "div"
  | .mod => "mod"
  | .pow => "^"
  | .and => "and"
  | .or => "or"
  | .xor => "xor"

/-- The six comparison operators of the ONE comparison precedence tier. The
    ordering comparisons `lt`/`gt`/`le`/`ge` take numeric scalar operands;
    `eq`/`ne` are total structural equality over every value kind. Every
    comparison yields a Boolean value, and unparenthesized comparisons at one
    syntactic level form one `Expr.comparison` chain. C#: `ComparisonOp`. -/
inductive ComparisonOp where
  | lt | gt | le | ge | eq | ne
  deriving Repr, BEq, DecidableEq

def ComparisonOp.symbol : ComparisonOp -> String
  | .lt => "<"
  | .gt => ">"
  | .le => "<="
  | .ge => ">="
  | .eq => "=="
  | .ne => "!="

inductive UnaryOp where
  | minus | not
  deriving Repr

inductive Builtin where
  | ifBuiltin | whileBuiltin | repeatBuiltin | atomsBuiltin | rangeBuiltin | filterBuiltin | mapBuiltin | orderBuiltin | orderDescBuiltin | countBuiltin | containsBuiltin | firstBuiltin | lastBuiltin | distinctBuiltin | takeBuiltin | skipBuiltin | minBuiltin | maxBuiltin | sumBuiltin | avgBuiltin | reduceBuiltin
  deriving Repr, BEq, DecidableEq

inductive SequenceBuiltinSuffixArgKind where
  | algorithm
  | value
  | wholeNumber
  deriving Repr, BEq, DecidableEq

structure SequenceBuiltinSuffixArgDescriptor where
  name : Ident
  kind : SequenceBuiltinSuffixArgKind := .algorithm
  deriving Repr, BEq

/-- What a collection builtin does with an EMPTY one-level collection view
    (Q-27): an ordinary input (`allowEmpty`), outside an aggregate's domain
    (`requireAnyItem`, `illegalInEval` — `min`, `max`, `avg`), or a SELECTION
    that has no position to select (`requireSelectablePosition`, `badIndex` —
    `first`, `last`, exactly as `collection:0`, SEQ-04).
    C#: `SequenceBuiltinEmptyPolicy`. -/
inductive SequenceBuiltinEmptyPolicy where
  | allowEmpty
  | requireAnyItem
  | requireSelectablePosition
  deriving Repr, BEq, DecidableEq

inductive SequenceBuiltinItemShapeConstraint where
  | any
  | singleNumeric
  deriving Repr, BEq, DecidableEq

structure SequenceBuiltinMetadata where
  suffixArgs : List SequenceBuiltinSuffixArgDescriptor := []
  emptyPolicy : SequenceBuiltinEmptyPolicy := .allowEmpty
  itemShapeConstraint : SequenceBuiltinItemShapeConstraint := .any
  deriving Repr, BEq

def SequenceBuiltinMetadata.parameters (metadata : SequenceBuiltinMetadata) : List CallableParameter :=
  { name := "collection" } ::
    metadata.suffixArgs.map (fun descriptor => { name := descriptor.name })

def SequenceBuiltinMetadata.signature (builtinName : Ident) (metadata : SequenceBuiltinMetadata)
    : CallableSignature :=
  { name := builtinName, parameters := metadata.parameters }

/-- Metadata for collection builtins.
  A collection builtin is an ordinary fixed-arity native callable: exactly one
  fixed `collection` parameter followed by its fixed control parameters
  (`count(collection)`, `take(collection, count)`). The bound collection value
  is interpreted through the one-level builtin collection view only AFTER
  binding; argument boundaries are never altered before binding. `suffixArgs`
  describes the fixed control arguments that follow the collection. -/
def sequenceBuiltinMetadata? : Builtin -> Option SequenceBuiltinMetadata
  | .filterBuiltin => some {
      suffixArgs := [{ name := "predicate" }]
    }
  | .mapBuiltin => some {
      suffixArgs := [{ name := "mapper" }]
    }
  | .orderBuiltin => some {
      itemShapeConstraint := .singleNumeric
    }
  | .orderDescBuiltin => some {
      itemShapeConstraint := .singleNumeric
    }
  | .countBuiltin => some {
    }
  | .containsBuiltin => some {
      suffixArgs := [{ name := "item", kind := .value }]
    }
  | .firstBuiltin => some {
      emptyPolicy := .requireSelectablePosition
    }
  | .lastBuiltin => some {
      emptyPolicy := .requireSelectablePosition
    }
  | .distinctBuiltin => some {
    }
  | .takeBuiltin => some {
      suffixArgs := [{ name := "count", kind := .wholeNumber }]
    }
  | .skipBuiltin => some {
      suffixArgs := [{ name := "count", kind := .wholeNumber }]
    }
  | .minBuiltin => some {
      emptyPolicy := .requireAnyItem
      itemShapeConstraint := .singleNumeric
    }
  | .maxBuiltin => some {
      emptyPolicy := .requireAnyItem
      itemShapeConstraint := .singleNumeric
    }
  | .sumBuiltin => some {
      itemShapeConstraint := .singleNumeric
    }
  | .avgBuiltin => some {
      emptyPolicy := .requireAnyItem
      itemShapeConstraint := .singleNumeric
    }
  | .reduceBuiltin => some {
      -- The reducer is a callback the builtin INVOKES; the initial accumulator is
      -- an ordinary VALUE, demanded once (HO-04).
      suffixArgs := [
        { name := "reducer" },
        { name := "initial", kind := .value }
      ]
    }
  | _ => none

/-- What one supplied item position of a collection builtin IS to the builtin's
    argument adapter, decided by the metadata alone (CALL-03):
    - `value`: the `collection` (position 0) or a `.value` / `.wholeNumber`
      control. Demanded ONCE for its value; that outcome — one value or one
      failure — is final for the call.
    - `callback`: an `.algorithm` control (the `filter` predicate, the `map`
      mapper, the `reduce` reducer). It carries its algorithm, and the builtin
      INVOKES it per element; supplying it evaluates nothing.
    - `surplus`: a position beyond the fixed signature. Supplying it makes the
      call an arity error.
    A spread slot is not a position: it is supply assembly, and each of its items
    takes the role of the position it lands on. -/
inductive SequenceBuiltinSlotRole where
  | value
  | callback
  | surplus
  deriving Repr, BEq, DecidableEq

def SequenceBuiltinMetadata.slotRole (metadata : SequenceBuiltinMetadata) (slot : Nat)
    : SequenceBuiltinSlotRole :=
  if slot == 0 then .value
  else match metadata.suffixArgs[slot - 1]? with
    | some descriptor => if descriptor.kind == .algorithm then .callback else .value
    | none => .surplus

private def sequenceBuiltinTotalArgCountDesc
    (signature : CallableSignature) : String :=
  if signature.collectingIndex?.isSome then
    let minimum := signature.requiredNormalParameterCount
    if minimum = 0 then "any number of" else s!"at least {minimum}"
  else
    toString signature.parameters.length

def builtinDisplayName : Builtin -> String
  | .ifBuiltin => "if"
  | .whileBuiltin => "while"
  | .repeatBuiltin => "repeat"
  | .atomsBuiltin => "atoms"
  | .rangeBuiltin => "range"
  | .filterBuiltin => "filter"
  | .mapBuiltin => "map"
  | .orderBuiltin => "order"
  | .orderDescBuiltin => "orderDesc"
  | .countBuiltin => "count"
  | .containsBuiltin => "contains"
  | .firstBuiltin => "first"
  | .lastBuiltin => "last"
  | .distinctBuiltin => "distinct"
  | .takeBuiltin => "take"
  | .skipBuiltin => "skip"
  | .minBuiltin => "min"
  | .maxBuiltin => "max"
  | .sumBuiltin => "sum"
  | .avgBuiltin => "avg"
  | .reduceBuiltin => "reduce"

/-- Normative arity-acceptance specification for builtins, mirrored by the C#
    `BuiltinRegistry.AcceptsArity` (which the C# evaluator consults directly).
    The Lean `applyBuiltinCounted` dispatch enforces the same arities
    structurally via pattern-match fall-through to `builtinArityError`, and
    `applyBuiltin` inherits them as its Result projection; the two encodings
    must stay in agreement (pinned by the CoreTests arity parity guards). -/
def builtinAcceptsArity : Builtin -> Nat -> Bool
  | b, n =>
      match sequenceBuiltinMetadata? b with
      | some metadata =>
          -- Collection builtins are ordinary fixed-arity callables:
          -- `count(collection)` is exactly 1 argument and
          -- `take(collection, count)` is exactly 2, the same rule as every
          -- other fixed builtin.
          n = 1 + metadata.suffixArgs.length
      | none =>
          match b, n with
          | .ifBuiltin, 3 => true
          | .whileBuiltin, n => n >= 2
          | .repeatBuiltin, n => n >= 3
          | .atomsBuiltin, 1 => true
          | .rangeBuiltin, 2 => true
          | _, _ => false

/-- Human-readable expected arity string for error messages. -/
def builtinArityDesc : Builtin -> String
  | b =>
      match sequenceBuiltinMetadata? b with
      | some metadata =>
          let signature := metadata.signature (builtinDisplayName b)
          let totalArgCountDesc :=
            sequenceBuiltinTotalArgCountDesc signature
          if metadata.suffixArgs.isEmpty then
            totalArgCountDesc
          else
            let parameters := String.intercalate ", " (signature.parameters.map CallableParameter.displayName)
            s!"{totalArgCountDesc} arguments ({signature.name}({parameters}))"
      | none =>
          match b with
          | .ifBuiltin => "3"
          | .whileBuiltin => "at least 2"
          | .repeatBuiltin => "at least 3"
          | .atomsBuiltin => "1"
          | .rangeBuiltin => "2"
          | _ => "?"

/-- The fewest arguments a call of the builtin accepts — its fixed arity, or a
    variadic-state loop's minimum (its fixed parameters plus one initial state):
    exactly the arities `builtinAcceptsArity` admits. C#:
    `BuiltinDescriptor.ArityFacts.MinTopLevelArgumentCount`. -/
def builtinMinimumArity (b : Builtin) : Nat :=
  match sequenceBuiltinMetadata? b with
  | some metadata => 1 + metadata.suffixArgs.length
  | none =>
      match b with
      | .ifBuiltin => 3
      | .whileBuiltin => 2
      | .repeatBuiltin => 3
      | .atomsBuiltin => 1
      | .rangeBuiltin => 2
      | _ => 0

def builtinArityError (b : Builtin) (actual : Nat) : Error :=
  -- The numeric payload is the builtin's real arity contract (Q-27 payload
  -- hygiene, formerly a placeholder 0 for every builtin but `if`), beside the
  -- descriptive `builtinArityDesc` context. Mirrors the C# `WrongBuiltinArity`.
  Error.withContext s!"expected {builtinArityDesc b} arguments"
    (Error.arityMismatch (builtinMinimumArity b) actual)

--------------------------------------------------------------------------------
-- Patterns (for clause heads and conditional algorithms)
--------------------------------------------------------------------------------

/-- Pattern language for clause heads and conditional algorithm branch matching.
    Recursive capture/structural patterns can elaborate to ordinary explicit
    parameter patterns. Conditional patterns match against Result values at
    call time.
    - `bind x`: matches any Result and binds it to name `x`
    - `litInt n`: matches only `Result.atom n`
    - `litBool b`: matches only `Result.bool b` (the reserved literals `true` /
      `false` in a clause head; a Boolean is never a number, so `F(1)` and
      `F(true)` are different clauses)
    - `sequenceValue ps` (a nested `(p1, …, pn)`): matches ONLY a
      `Result.sequenceValue rs` of the same length, each sub-pattern matching
      its element; never a list and never a scalar. `()` matches only the empty
      sequence value. A one-item `(p)` is invalid (the singleton rule,
      `headHasSingletonSequenceGroup`): no one-item sequence value exists.
    - `listValue ps` (`[p1, …, pn]`): matches ONLY a `Result.listValue rs` of
      the same length, each sub-pattern matching its element; never a sequence
      and never a scalar. `[]` matches only the empty list, `[p]` a one-element
      list.
    At the TOP of a clause head a `sequenceValue` is the head's own argument
    list (`F(x, y)` is `sequenceValue [bind x, bind y]`, `F((x, y))` is
    `sequenceValue [sequenceValue [bind x, bind y]]`, `F([x])` is
    `sequenceValue [listValue [bind x]]`), never a structural pattern.

    Patterns are a separate semantic type, distinct from Expr.
    They do not appear in executable expression positions.

    **Full-input-specification rule**: In a conditional algorithm, the branch
    pattern in `Name(...)` is the COMPLETE INPUT SPECIFICATION of that branch.
    - All branch inputs must appear in the pattern.
    - The branch's OWN level does NOT infer additional implicit parameters
      from free identifiers.  Only names bound by the pattern (plus ordinary
      lexical / property / open / builtin resolution) are available in the
      rows the branch writes.
    - Unused pattern-bound names are allowed.
    - Grace `~` is NOT permitted in patterns or on the branch's own level.
      Patterns contain only matching constructs (binders, literals, nested
      sequence and list patterns), and the branch's own rows have no inferred
      parameter ordering to apply Grace to.  Algorithms NESTED inside a branch
      body (brace blocks, properties, nested families' owners) are ordinary
      independent owners: an inferring one infers its own signature, and may
      use Grace on its own inferred parameters, in the C# front end before
      Lean encoding (Q-16 G-O); its parameters are supplied by its caller and
      are never added to the branch.

    This keeps conditional algorithms self-contained: branch selection and
    branch binding are the same operation, with no hidden remaining parameters
    and no interaction with Grace-based parameter reordering at the branch's
    own level. -/
inductive Pattern where
  | bind      : Ident -> Pattern
  | litInt    : Int -> Pattern
  | litString : String -> Pattern    -- matches only Result.str s (exact string equality)
  | litBool   : Bool -> Pattern      -- matches only Result.bool b (C#: Pattern.LitBool)
  | sequenceValue     : List Pattern -> Pattern   -- `(p1, …, pn)`: sequence values only (C#: Pattern.SequenceValue)
  | listValue         : List Pattern -> Pattern   -- `[p1, …, pn]`: list values only (C#: Pattern.ListValue)
  deriving Repr, BEq

namespace Pattern
  /-- Collect all binder names in a pattern (left-to-right). -/
  def boundNames : Pattern -> List Ident
    | .bind x      => [x]
    | .litInt _    => []
    | .litString _ => []
    | .litBool _   => []
    | .sequenceValue ps    => ps.flatMap boundNames
    | .listValue ps        => ps.flatMap boundNames

  mutual
    /-- THE SINGLETON RULE for the family pattern language (see
        `ParameterPattern.isSingletonSequenceItems`): a NESTED sequence pattern
        with exactly one item describes a one-item sequence, which no value is,
        so it is invalid. A family pattern has no collecting binder, so every
        one-item sequence pattern is a singleton. A list pattern `[p]` is valid. -/
    def hasSingletonSequenceGroup : Pattern -> Bool
      | .sequenceValue ps => ps.length == 1 || anyHasSingletonSequenceGroup ps
      | .listValue ps => anyHasSingletonSequenceGroup ps
      | .bind _ => false
      | .litInt _ => false
      | .litString _ => false
      | .litBool _ => false

    def anyHasSingletonSequenceGroup : List Pattern -> Bool
      | [] => false
      | p :: ps => hasSingletonSequenceGroup p || anyHasSingletonSequenceGroup ps
  end

  /-- The singleton rule over a whole clause HEAD: a top-level `sequenceValue`
      is the head's own argument list (the call's parentheses), never a
      structural pattern, so only the patterns inside it are checked; any other
      head is one argument position checked as a pattern. -/
  def headHasSingletonSequenceGroup : Pattern -> Bool
    | .sequenceValue ps => anyHasSingletonSequenceGroup ps
    | p => hasSingletonSequenceGroup p

  /-- Compute the top-level arity of a pattern.
      - `sequenceValue [p1, ..., pn] ⟹ n` (the head's own argument list)
      - any other pattern, a list pattern included  ⟹ 1

      This defines the outer call interface of a conditional algorithm branch.
      Conditional algorithms require a uniform top-level interface across branches:
      all branches of the same conditional algorithm must have the same
      top-level pattern arity.  Nested substructure may vary, but the outer
      number of inputs must remain consistent. -/
  def topLevelArity : Pattern -> Nat
    | .sequenceValue ps => ps.length
    | _         => 1

  /-- Return positional parameter names only for the strict flat multi-binder
      core subset: a top-level flat sequence-value pattern of multiple plain binders.

      This helper is intentionally narrower than the surface clause
      elaboration rule. It is kept for compatibility with manually constructed
      core `.conditional` values handled by evaluator fallback.

      Rejected on purpose:
      - bare single binders (`.bind x`)
      - any sequence-value pattern containing non-binders
      - any top-level arity-1 sequence-value pattern, including singleton binder forms

      Surface clause elaboration uses `plainClauseParamNames?` below, which
      additionally accepts bare single binders like `F(x) = ...`. -/
  def flatBinderParamNames? : Pattern -> Option (List Ident)
    | .sequenceValue ps =>
        if ps.length <= 1 then
          none
        else
          ps.mapM (fun
            | .bind x => some x
            | _ => none)
    | _ => none

  /-- Return parameter names when a sole surface clause head consists only of
      recursive binder/structural (sequence or list) parameter patterns.

      This is only an eligibility helper for the whole same-name clause-group
      elaboration rule; it does not by itself decide ordinary-vs-conditional.

      Rejected on purpose:
      - literal or mixed non-binder pattern structure

      This is the ordinary clause-elaboration boundary: capture/structural-only
      recursive parameter patterns elaborate as ordinary algorithms, while
      literal or mixed patterns stay conditional. Each structural pattern keeps
      its kind: a sequence pattern stays a sequence pattern and a list pattern a
      list pattern. -/
  partial def parameterPattern? : Pattern -> Option ParameterPattern
    | .bind x => some (.capture { name := x })
    | .sequenceValue ps => do
        let patterns <- ps.mapM parameterPattern?
        some (.sequenceValue patterns)
    | .listValue ps => do
        let patterns <- ps.mapM parameterPattern?
        some (.listValue patterns)
    | _ => none

  partial def plainClauseParameterPatterns? : Pattern -> Option (List ParameterPattern)
    | .bind x => some [.capture { name := x }]
    | .sequenceValue ps => ps.mapM parameterPattern?
    | .listValue ps => (parameterPattern? (.listValue ps)).map (fun pattern => [pattern])
    | _ => none

  def plainClauseParamNames? : Pattern -> Option (List Ident)
    | p => (plainClauseParameterPatterns? p).map (fun patterns => (patterns.flatMap ParameterPattern.captures).map (fun parameter => parameter.name))

  /-- Check whether two patterns are match-equivalent. Binder spelling is
      irrelevant, but repeated-name equality positions must agree:
      - `bind _` ≡ `bind _` (any binder matches everything)
      - `litInt m` ≡ `litInt n` iff `m = n` (likewise `litString`, `litBool`)
      - `sequenceValue ps` ≡ `sequenceValue qs` iff same length and pairwise match-equivalent
      - `listValue ps` ≡ `listValue qs` iff same length and pairwise match-equivalent

      Used to detect duplicate branch patterns in conditional algorithms.

      Equivalence is structural, not extensional, and the structural KIND is part
      of the shape: a sequence pattern is never match-equivalent to a list
      pattern (`(x, y)` and `[a, b]`, `()` and `[]` match disjoint values), while
      renaming binders never makes two patterns of one shape distinct. -/
  def binderRenaming? (name : Ident) : List (Ident × Ident) -> Option Ident
    | [] => none
    | (left, right) :: rest =>
        if left = name then some right else binderRenaming? name rest

  def binderTargetUsed (name : Ident) : List (Ident × Ident) -> Bool
    | [] => false
    | (_, right) :: rest => right = name || binderTargetUsed name rest

  mutual
  partial def matchEquivalentWithRenaming : Pattern -> Pattern ->
      List (Ident × Ident) -> Option (List (Ident × Ident))
    | .bind left, .bind right, pairs =>
        match binderRenaming? left pairs with
        | some existing => if existing = right then some pairs else none
        | none =>
            if binderTargetUsed right pairs then none
            else some ((left, right) :: pairs)
    | .litInt m, .litInt n, pairs =>
        if m = n then some pairs else none
    | .litString s, .litString t, pairs =>
        if s = t then some pairs else none
    | .litBool b, .litBool c, pairs =>
        if b = c then some pairs else none
    | .sequenceValue ps, .sequenceValue qs, pairs =>
        matchEquivalentItemsWithRenaming ps qs pairs
    | .listValue ps, .listValue qs, pairs =>
        matchEquivalentItemsWithRenaming ps qs pairs
    | _, _, _ => none

  /-- Pairwise match-equivalence of two structural patterns' items of ONE kind. -/
  partial def matchEquivalentItemsWithRenaming (ps qs : List Pattern)
      (pairs : List (Ident × Ident)) : Option (List (Ident × Ident)) :=
    if ps.length != qs.length then
      none
    else
      let rec go : List (Pattern × Pattern) ->
          List (Ident × Ident) -> Option (List (Ident × Ident))
        | [], current => some current
        | (p, q) :: rest, current => do
            let next <- matchEquivalentWithRenaming p q current
            go rest next
      go (ps.zip qs) pairs
  end

  def isMatchEquivalent (left right : Pattern) : Bool :=
    (matchEquivalentWithRenaming left right []).isSome
end Pattern

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

/-- Declaration identity is independent of executable body equality. Ordinary
    tree declarations receive a fresh `syntax` identity once at run preparation.
    `shared` represents a host AST declaration reused at several syntax sites
    (C# binding plus declaring-scope identity); encoders preserve that sharing explicitly.
    `module` marks the ONE declaration of a loaded module (Q-31 H-P + Q-32 I-U, decided
    2026-10-06): a hygienic source unit rooted at the prelude, so wherever it is reached it is
    wired under the chain's root level (`Algorithm.withParent`), never under its holder, and
    every holder reaches the one declaration in the one declaring scope. Lean has no loader;
    the encoder emits the mark for the C# tree's loaded-module roots (C#:
    `Algorithm.User.IsModuleElaborated`). -/
inductive PropertyIdentity where
  | syntax : Nat -> PropertyIdentity
  | shared : Nat -> PropertyIdentity
  | runtime : Nat -> PropertyIdentity
  | module : Nat -> PropertyIdentity
  deriving Repr, BEq

mutual
  inductive Expr where
    | param   : Ident -> Expr
    | num     : Int -> Expr
    | stringLiteral : String -> Expr  -- * string literal: first-class value (evaluates to Result.str)
    -- * boolLiteral: the reserved Boolean literals `true` / `false`
    --   (evaluates to Result.bool). They are lexer keywords, never
    --   identifiers, so they can be neither declared nor shadowed and never
    --   become implicit parameters. C#: `Expr.BoolLiteral`.
    | boolLiteral : Bool -> Expr
    | unary   : UnaryOp -> Expr -> Expr
    -- * binary: an arithmetic or logical operator over two operands — never a
    --   comparison (see `comparison`).
    | binary  : BinaryOp -> Expr -> Expr -> Expr
    -- * comparison: a COMPARISON CHAIN `first op1 x1 op2 x2 …`, the ONE
    --   representation of every comparison, with one link (`a < b`) or many
    --   (`a < b <= c == d != e`). Unparenthesized comparison operators at one
    --   syntactic level form one chain; a parenthesized comparison is an
    --   ordinary operand (`(a < b) == c` is a one-link chain whose first
    --   operand is a chain). Each link compares the PREVIOUS operand with its
    --   own — adjacent-pair semantics, so `1 != 2 != 1` is `1 != 2` and
    --   `2 != 1` — and the chain is `true` iff every link holds. Evaluation
    --   (`evalComparisonCounted`) is incremental and left to right: every
    --   operand is evaluated EXACTLY ONCE (the previous operand's VALUE is
    --   reused, never its expression), each link is compared as soon as its
    --   operand is available, a `false` link never stops the chain (eager
    --   Boolean composition, so a later invalid comparison is still an error),
    --   and an error terminates it (later operands are not evaluated). A chain
    --   with no links evaluates its first operand and is `true`.
    --   C#: `Expr.Comparison`.
    | comparison : Expr -> List ComparisonLink -> Expr
    | index   : Expr -> Expr -> Expr
    -- * sequenceConstruct: INTERNAL sequence-join node retained for semantic
    --   AST compatibility (surface spreading is the attached postfix spread marker `expr*`,
    --   `sequenceSpread`, and never builds this node).
    --   It is NOT the representation of written sequence-value syntax: the
    --   C# surface parser and production transformations have zero origin
    --   sites for it — surviving parenthesized lists parse to `capture`
    --   nodes and `()` to emptySequence; visitors only rebuild an existing node.
    --   The exported `sequenceConstruct` helper (and the public C# AST API)
    --   is the intentional external origin mechanism. Its value evaluation
    --   DROPS `()` leaves (join semantics), which written parentheses never
    --   do, so routing surface syntax through it would silently violate the
    --   visible-empty rule. Guarded by SequenceConstructContainmentTests
    --   (C#) and the internal-node cases in SemanticExplorerCases.lean.
    | sequenceConstruct : Expr -> Expr -> Expr
    -- * emptySequence: the empty sequence value `()`. Repeated ordinary
    --   parentheses around the empty sequence are useful-structure normalized
    --   back to `()` rather than exposing higher-order empty sequence values.
    | emptySequence : Nat -> Expr
    -- * spread: UNARY representation over its single operand. The surface
    --   spelling is the attached postfix spread marker — `A*` lowers to this
    --   one node — so `sequenceSpread expr` spreads the top-level output
    --   items of `expr` and contributes them to the surrounding supply
    --   (conceptually `spread : Value -> Supply`; the receiver decides what
    --   the items become). A star with a same-line right operand is
    --   MULTIPLICATION in surface syntax, so spreading before another
    --   same-line supplied item requires a comma (`A*, B`; `A* B` is
    --   `A * B`); semicolon is not surface expression syntax. Nested
    --   spread such as `A**` is `sequenceSpread (sequenceSpread A)`;
    --   evaluation unwraps the chain iteratively
    --   (`peelSequenceSpreadLayers`, stack-safe) and applies each written
    --   layer compositionally — every layer opens one boundary of the value
    --   the previous layer's supply would re-capture — so `A**` agrees with
    --   `(A*)*` (a fixed point for sequence values; a singleton-list chain
    --   such as `[[7]]**` opens one list boundary per layer, while a
    --   multi-element list re-captures as a sequence after the first layer
    --   and then stays fixed).
    | sequenceSpread : Expr -> Expr
    -- * listLiteral: surface list literal `[e1, ..., en]`. Evaluates to exactly
    --   ONE list value (`Result.listValue`). Element slots follow
    --   the same expression-list rules as written parentheses (an explicit spread
    --   slot opens its operand's immediate items, a non-spread `()` slot stays one
    --   visible element), but the collected elements are stored EXACTLY: no
    --   singleton erasure and no empty-nesting collapse, so `[7]`, `[[7]]`, and
    --   `[]` are all distinct values. C#: `Expr.ListLiteral`.
    | listLiteral : List Expr -> Expr
    | resolve : Ident -> Expr
    -- * algorithmExpr: an algorithm used in expression position, exposing
    --   ALGORITHM IDENTITY: the contained algorithm owns its lexical scope
    --   (parameters, properties, `open`, declaration namespace) and the
    --   expression participates in value, algorithm/callable, and
    --   namespace/`open` interpretation. Surface form: `{ ... }` brace
    --   algorithm literals (also elaborated modules and recovery trees).
    --   C#: `Expr.AlgorithmExpr`.
    | algorithmExpr : Algorithm -> Expr
    -- * capture: a surviving parenthesized capture boundary over an
    --   OutputBundle (an ordered list of written expression rows with no
    --   lexical ownership — the `OutputBundle` abbreviation is declared after
    --   this mutual block). Written parentheses PERFORM capture
    --   (`capture : Supply -> Value`): evaluation supplies the rows through
    --   the shared output-row loop and canonically captures them as one
    --   value. CAPTURE IS NOT ALGORITHM IDENTITY: the algorithm channel sees
    --   only a zero-parameter output thunk over the bundle, never the
    --   algorithm identity of anything inside it. PARENTHESES GROUP SYNTAX;
    --   THEY DO NOT INTRODUCE A SEMANTIC BOUNDARY (September 2026): the C#
    --   parser erases every redundant group — a group of exactly ONE
    --   non-spread slot is that slot's expression whatever its kind, so
    --   `(x)`, `(x.M)`, `(F(1))`, `((1, 2))`, and `(())` never reach this
    --   node — and only a group whose parentheses DO something survives as
    --   it: several written slots (`(1, 2)`) or a lone spread slot (`(A*)`,
    --   the capture of an item supply into one value). A host AST may still
    --   build `capture [e]` directly; its semantics are the ordinary capture
    --   semantics (one row, captured to one value), never a written-slot
    --   boundary that a binder or receiver could observe. C#: `Expr.Capture`.
    | capture : List Expr -> Expr
    -- Call/dot-call arguments are an ordered OutputBundle of the ORIGINAL
    -- written argument expressions (spelled `List Expr` inside this mutual
    -- block), evaluated transparently in the caller's lexical context — never
    -- an Algorithm: an argument list owns no scope, and each slot participates
    -- independently in the value channel and (where permitted) the algorithm
    -- channel. `dotMember`'s `none` means NO argument-list syntax (`a.f`);
    -- `some []` is an explicit empty list (`a.f()`). C#: `Expr.Call`/`Expr.DotCall`.
    | call    : Expr -> List Expr -> Expr
    -- * dotMember: one dot edge `a.f` / `a.f(args)`, carrying the ELABORATED
    --   member facts beside the structural member name: `fallback` is the
    --   member's lexical-fallback callee identity as an ordinary name
    --   expression (`.resolve f`, or `.param f` once a front-end decides the
    --   member is a parameter reference). Resolution is structural-first with
    --   the fallback applying only on a structural miss — at EVERY level of
    --   a chain: a receiver that is itself an argumentless dot edge navigates
    --   its declared structural members (`resolveDotReceiver`), so
    --   `Lib.Sub.Q` reads `Sub`'s own `Q` before any lexical `Q`. Runtime
    --   consumers CONSUME these facts (`resolveAlg fallback`) instead of
    --   reconstructing the Param-vs-Resolve decision from environments. The C# front end
    --   consumes ordinary Grace composed with dot syntax (`a~.f` / `a.~f`),
    --   so Lean receives the SAME `dotMember` executable body as for `a.f`.
    --   Hand-built ordinary/lexical edges use the `Expr.dotCall` smart
    --   constructor declared after this mutual block.
    --   C#: `Expr.DotCall` (`LexicalFallback`).
    | dotMember : Expr -> Ident -> Expr -> Option (List Expr) -> Expr
    -- NOTE: load('url') is surface-only syntax, represented as Call(Resolve("load"), ...)
    -- in the parser and elaborated to algorithmExpr(...) by the load elaboration pass.
    -- It is NOT a core Expr constructor.  See load elaboration section below.
    deriving Repr

  /-- One link of a comparison chain: the operator that compares the PREVIOUS
      operand of the chain with `operand`. C#: `ComparisonLink`. -/
  structure ComparisonLink where
    op      : ComparisonOp
    operand : Expr
    deriving Repr

  /-- Property definition with visibility metadata. -/
  structure PropDef where
    name     : Ident
    alg      : Algorithm
    isPublic : Bool
    exposure : PropExposure := .exported
    identity : Option PropertyIdentity := none
    requiredOwnerDepths : Option (List (Ident × Option Nat)) := none
    deriving Repr

  /-- A branch of a conditional algorithm: a pattern and a body algorithm.
      The pattern is the complete input specification of the branch.
      Branch bodies receive bindings ONLY from the matched pattern (plus
      ordinary lexical resolution).  No extra implicit parameters are inferred
      at the branch's own level from free identifiers in the body, and Grace
      `~` is not allowed in patterns or on that level; an algorithm nested in
      the body is an ordinary independent owner (an inferring one may use
      Grace on its own inferred parameters in the C# front end, Q-16 G-O).
      Nested internal output structure may vary. -/
  structure CondBranch where
    pattern : Pattern
    body    : Algorithm
    deriving Repr

    /-- User-defined algorithm with properties, parameters, opens, and output.

      **Unique property name invariant**: the `properties` list must not
      contain two entries with the same `name`.  Properties are immutable
      bindings; redefining a property is a static error detected by the
      front-end / parser.  This invariant ensures that `lookupPropDefAny?`
      (which returns the first match) is unambiguous. -/
    inductive Algorithm where
    | mk :
        (parent     : Option ScopeCtx) ->
      (parameterPatterns : List ParameterPattern) ->
        (opens      : List Expr) ->
        (properties : List PropDef) ->
        (output     : List Expr) ->
        (declarationId : Option PropertyIdentity := none) ->
        Algorithm
    | builtin : Builtin -> Algorithm
    /-- Conditional algorithm: ordered pattern branches tried at call time.
        At call time the supply is formed (one suspended cell per argument; only
        explicit spreads are evaluated), a count that no branch head accepts is
        `arityMismatch` before any branch is tried (NEED-05), and the branches are
        then tried in source order over the SAME cells, each pattern demanding only
        the values it inspects (NEED-04; `selectNeedFamilyBranch`).  The first
        matching branch body is evaluated.  If no branch matches a supply of an
        accepted count, evaluation fails with noMatchingBranch.

        **Full-input-specification invariant**: each branch pattern `Name(...)`
        declares the complete input interface of that branch.  A branch's own
        level does NOT infer additional implicit parameters from free
        identifiers — only names bound by the pattern and names resolvable
        through ordinary lexical / property / open / builtin lookup are
        available.  Grace `~` is forbidden in patterns and on the branch's own
        level; algorithms nested in a branch body are ordinary independent
        owners (an inferring one may use Grace on its own inferred parameters in
        the C# front end before Lean encoding, Q-16 G-O), never adding a
        parameter to the branch.

        **Uniform top-level arity invariant**: all branches of the same
        conditional algorithm must have the same top-level pattern arity
        (as defined by `Pattern.topLevelArity`).  Nested internal pattern
        structure may vary, but the outer number of inputs must remain
        consistent.  This preserves a unified outer call interface and
        prevents conditional algorithms from acting as ad hoc overloading
        by varying top-level argument count.

        **Uniform top-level output arity invariant**: all branches of the same
        conditional algorithm must have the same top-level output arity
        (the number of top-level output expressions in the branch body).
        Nested internal output structure may vary, but the outer number of
        outputs must remain consistent.  This preserves a unified output
        interface across branches.

        **Unique branch pattern invariant**: the `branches` list must not
        contain two entries whose patterns are match-equivalent (as defined
        by `Pattern.isMatchEquivalent`).  Duplicate patterns are unreachable
        (first-match semantics) and indicate a static error detected by the
        front-end / parser.

        **Clause elaboration rule**: front-ends should use
        `Algorithm.elaborateClauseGroup` when lowering surface syntax
        `Name(pattern) = body`. The ordinary-vs-conditional split is decided
        for the whole same-name clause group, not per clause. A group
        elaborates to `Algorithm.mk` only when it contains exactly one clause
        and that sole head is a recursive capture/structural parameter pattern such
        as `Apply(f) = f(4)`, `PairSum((x, y)) = x + y`, `Only([x]) = x`, or
        `CountSequenceValue((*values)) = values.count`. Multi-clause families and
        literal/mixed heads such as

          F(0) = 0
          F(x) = 1

        still lower to `Algorithm.conditional`.

        The evaluator still recognizes the equivalent single-branch flat
        multi-binder core shape as a compatibility fallback for manually
        constructed `.conditional` ASTs, but clause elaboration must not rely
        on that fallback. -/
    | conditional :
        (parent   : Option ScopeCtx) ->
        (opens    : List Expr) ->
        (branches : List CondBranch) ->
        (declarationId : Option PropertyIdentity := none) ->
        Algorithm
    /-- A CALLABLE ALIAS (FWD-02, binding indirection; decided 2026-10-01): a BINDING of its own
        whose CALLABLE is the one its written `target` resolves to in the alias's OWN scope.

        A non-root open body — a named definition or an inline block with no written parameter
        list — whose one written row is a bare reference `F` is an alias when name resolution
        selects ONE callable identity that declares parameterized callable structure
        (`Algorithm.declaresParameterizedStructure`: a builtin, a clause family, nameable or not,
        or a user algorithm with at least one parameter pattern — or another alias, so a chain
        normalizes to one target). The surface pass produces this constructor; nothing is
        synthesized: an alias has no parameter list, no inherited signature and no wrapper call.

        **Two identities.** The BINDING is the alias's own: the property holding it keeps its
        declaration, exposure and zero-argument cache key (`zeroArgPropertyCacheKey` carries the
        property NAME), and the alias declares only what its own body declares (`properties`,
        normally none) — never its target's members, so written member access `A.K` takes the
        ordinary fallback and `open A` is refused (`requiresArguments`). The CALLABLE is the
        target's: every callable use — a call, a callback or loop step, the callable channel of an
        argument, a zero-argument value demand — uses the callable `target` resolves to in the
        alias's own scope (`resolveAliasTarget`), through that callable's own invocation. An alias
        is no invocation: resolving it charges nothing.

        `target` is a STATIC PATH (`Expr.isStaticAliasPath`): a name, or an argumentless dot path
        whose head is a name or a block. C#: `Algorithm.Alias`. -/
    | alias :
        (parent     : Option ScopeCtx) ->
        (opens      : List Expr) ->
        (properties : List PropDef) ->
        (target     : Expr) ->
        (declarationId : Option PropertyIdentity := none) ->
        Algorithm
    deriving Repr

  /-- A lexical scope level as the evaluator wires it. `params` are the parameter names
      the level's algorithm binds — its own parameters, or, on the family scope a
      conditional call wires the selected branch body under, the matched pattern
      binders. They take no part in property lookup; they let `memberAccessible?` find
      the owner of a local-only member's required input by the same nearest-owner walk
      the surface layer elaborated the reference with (C#: `ScopeCtx.Parameters`).
      `output` and `branches` retain the owning body for scope reconstruction.
      Declaration and activation IDs distinguish owners even when body components or
      binder names are shared. These IDs are separate from property-cache identity. -/
  inductive ScopeCtx where
    | mk :
        (parent  : Option ScopeCtx) ->
        (params  : List Ident) ->
        (opens   : List Expr) ->
        (props   : List PropDef) ->
        (output  : List Expr) ->
        (branches : List CondBranch) ->
        (activation : Option Nat) ->
        (declarationId : Option PropertyIdentity) ->
        ScopeCtx
    deriving Repr
end

/-- An ordered sequence of original written expression slots with no lexical
    ownership of its own: no parent scope, no parameters, no properties, no
    `open`. It is intensional syntax — how the slots contribute values or
    items is determined entirely by the RECEIVER that consumes the bundle:
    algorithm output evaluation preserves per-row emitted-count semantics,
    `Expr.capture` performs canonical sequence capture, and
    `Expr.listLiteral` collects the slots as one exact list value. It
    deliberately does NOT encode a fixed runtime consumption policy and is
    NOT a list of evaluated results. (`Algorithm.mk`'s `output` field, the
    `capture`/`listLiteral` constructor payloads, and the `call`/`dotCall`
    argument payloads are this type; the constructors inside the mutual block
    above spell it `List Expr` because the abbreviation cannot be declared
    before `Expr` exists.)
    C#: `OutputBundle`. -/
abbrev OutputBundle := List Expr

/-- Ordinary/lexical dot-call smart constructor: `a.f` / `a.f(args)` with the
    unelaborated fallback identity `.resolve f`. Hand-built ASTs keep plain
    lexical-fallback semantics through this form; elaborated trees carry the
    front-end's Param-vs-Resolve decision in the full `Expr.dotMember`
    constructor. C#: an `Expr.DotCall` with null `LexicalFallback`. -/
def Expr.dotCall (target : Expr) (name : Ident) (args : Option OutputBundle) : Expr :=
  .dotMember target name (.resolve name) args

/-- Smart constructor for a ONE-LINK comparison chain `left op right` — the
    hand-built spelling of an ordinary comparison (`a < b` is the chain with
    first operand `a` and the single link `< b`). C#: `new Expr.Comparison(a, [new ComparisonLink(op, b)])`. -/
def Expr.compare (op : ComparisonOp) (left right : Expr) : Expr :=
  .comparison left [{ op := op, operand := right }]

/-- Surface same-name clause-group classification.
  Front-ends must decide ordinary-vs-conditional elaboration only after
  collecting the entire same-name clause family, not while looking at the
  first clause in isolation.

  A same-name clause group elaborates as ordinary only when:
  - the group contains exactly one clause, and
  - that sole clause head is a recursive capture/structural (sequence or list)
    parameter pattern

  This is intentional. Later clauses may force the whole family to remain
  conditional, for example:

      F(0) = 0
      F(x) = 1

  Even though `F(x) = 1` alone would qualify for ordinary elaboration, the
  full family must stay conditional because branch selection is defined at the
  whole-group level. -/
inductive ClauseGroupDefinitionKind where
  | ordinary : List ParameterPattern -> ClauseGroupDefinitionKind
  | conditional : ClauseGroupDefinitionKind
  deriving Repr

--------------------------------------------------------------------------------
-- Result (structured evaluation artifact)
--------------------------------------------------------------------------------

inductive Result where
  | atom  : Int -> Result
  | str   : String -> Result     -- first-class string value (exact equality, no ordering/coercion)
  -- Boolean value `true` / `false`: a first-class scalar value kind that is
  -- NOT a number (no implicit conversion in either direction). Produced by
  -- the Boolean literals, every comparison operator, the logical operators,
  -- and `contains`; consumed wherever a condition or predicate is required
  -- (`if`, `filter`, the `while` continuation flag, `not`/`and`/`or`/`xor`).
  -- Equality is total across kinds (`bool true == atom 1` is false); there
  -- is no ordering on Booleans. C#: `Result.Bool`.
  | bool  : Bool -> Result
  | sequenceValue : List Result -> Result
  -- List value `[a, b, c]`. Unlike sequence values, list
  -- structure is never singleton-normalized: `listValue [r]` and `r` are
  -- distinct values, `listValue []` is distinct from the empty sequence
  -- value, and nesting is preserved exactly. C#: `Result.ListValue`.
  | listValue : List Result -> Result
  deriving Repr, BEq

namespace Result
  def normalize : Result -> Result
    | atom n => atom n
    | str s  => str s
    | bool b => bool b
    | sequenceValue rs =>
        let rs' := rs.map normalize
        match rs' with
        | [r] => r
        | _   => sequenceValue rs'
    -- Lists are exact: normalize their elements (redundant SEQUENCE structure
    -- inside a list still normalizes) but never collapse the list boundary
    -- itself — `[7]` stays `[7]`, never `7`.
    | listValue rs => listValue (rs.map normalize)

  /-- Language-level atom collection for the `atoms` builtin: recursively
      collect numeric atoms depth-first, left-to-right, through BOTH sequence
      and exact list boundaries. Strings and other non-numeric leaves
      contribute no atoms. The builtin materializes this collection as ONE
      list value (`makeCollectionListResult`).
      Deliberately separate from `Result.hostAtoms` (host projection), so the
      two contracts cannot drift through shared code. Boolean values are not
      numeric atoms and contribute nothing, like strings.
      C#: `Result.LanguageAtoms`. -/
  def languageAtoms : Result -> List Int
    | atom n    => [n]
    | str _     => []
    | bool _    => []
    | sequenceValue rs => rs.flatMap languageAtoms
    | listValue rs => rs.flatMap languageAtoms

  /-- Host-boundary numeric flattening used by `runFlat`: the numeric atoms
      reachable through sequence AND exact list boundaries, so collection-
      builtin results surface their numeric contents at the embedding
      boundary. This is a host projection, not language semantics: the
      `atoms` builtin collects through its own separate collector
      (`Result.languageAtoms`) and returns one exact list value rather than a
      host atom list, and no in-language conversion between lists and
      sequences is implied. Strings and Boolean values have no numeric
      projection and are omitted.
      C#: `Result.ToHostAtoms`. -/
  def hostAtoms : Result -> List Int
    | atom n    => [n]
    | str _     => []
    | bool _    => []
    | sequenceValue rs => rs.flatMap hostAtoms
    | listValue rs => rs.flatMap hostAtoms

  /-- Canonical text of a Boolean value: lowercase `true` / `false`, the same
      spelling as the literals. C#: `ValueTextRenderer.FormatBool`. -/
  def boolText : Bool -> String
    | true => "true"
    | false => "false"

  /-- Boolean view of a value, for every consumer that REQUIRES a condition or
      predicate (`if`, `filter`, the `while` continuation flag, `not`, `and`,
      `or`, `xor`). Only a Boolean value qualifies; a redundant singleton
      sequence boundary normalizes away exactly as `asInt?` does for numbers
      (`(true)` is `true`). Numbers have NO truth value — there is no
      `0`/nonzero convention — and neither do strings, multi-item sequence
      values, the empty sequence value, or lists.
      C#: `Result.AsBool`. -/
  def asBool? : Result -> Option Bool
    | bool b => some b
    | sequenceValue rs =>
        match normalize (sequenceValue rs) with
        | bool b => some b
        | _      => none
    | _ => none

    /-- Strict numeric extraction for numeric collection builtins such as `min`,
      `max`, `sum`, and `avg`.
      Accepts exactly one atomic numeric value.

      Sequence values are not flattened or recursively inspected, and strings
      are rejected. -/
  def singleAtomicNumber? : Result -> Option Int
    | atom n => some n
    | _      => none

  def asInt? : Result -> Option Int
    | atom n => some n
    | str _  => none
    | bool _ => none   -- Booleans are not numbers: no implicit conversion
    | sequenceValue rs =>
        match normalize (sequenceValue rs) with
        | atom n => some n
        | _      => none
    | listValue _ => none   -- lists never coerce to numbers, not even `[5]`

  /-- Top-level items of a MULTI-ITEM counted result: a sequence value's items;
      any other value is itself. This is not an opening operation — call
      binding never uses it (every non-spread argument is ONE item) — it only
      recovers the rows a multi-output body emitted (`countedTopLevelValues`)
      and serves as the non-list branch of the one-level views below. The
      explicit openers are the spread marker (`spreadItems`, which assignment
      deconstruction's elaboration also uses), the kind-specific structural
      patterns (`sequencePatternItems?` for `(…)`, `listPatternItems?` for
      `[…]`), the indexing `:` TARGET position view (`projectionItems` — the
      target's positions, never the selected element), and the post-binding
      builtin collection view (`builtinCollectionItems`, applied to the bound
      `collection` argument). Every opener except the structural patterns opens
      a sequence and a list alike; a structural pattern opens only its own
      kind. -/
  def toItems : Result -> List Result
    | atom n   => [atom n]
    | str s    => [str s]
    | bool b   => [bool b]
    | sequenceValue rs => rs
    | listValue rs => [listValue rs]

  /-- Item view used by the spread expression (`expr*`): spread opens exactly ONE
      structure boundary. Sequence values and exact list values open to their
      immediate items; atoms and strings supply themselves as one item.
      C#: `Result.SpreadItems`. -/
  def spreadItems : Result -> List Result
    | listValue rs => rs
    | r => r.toItems

  /-- The openable-structure view: a sequence value or exact list value opens
      to its immediate items; atoms, strings, and Booleans are not structures.
      Its total extension is the spread view (`(structureItems? v).getD [v] =
      spreadItems v`, `spreadItems_extends_structureItems`), which is what
      assignment deconstruction's unpacking receiver (`ParameterPattern.unpacking`)
      opens its lone right-hand side with; the structural patterns open only
      their own kind (`sequencePatternItems?`, `listPatternItems?`), and
      call-argument binding never opens an argument. It anchors the arity
      algebra's `structureItems?` (`CoreArityAlgebra.lean`); no evaluator path
      reads it, so it has no C# counterpart. -/
  def structureItems? : Result -> Option (List Result)
    | sequenceValue rs => some rs
    | listValue rs => some rs
    | _ => none

  /-- STRUCTURAL PATTERN DELIMITERS SELECT THE VALUE KIND THEY DESTRUCTURE
      (September 2026): the elements a SEQUENCE pattern `(p1, …, pn)` binds
      against, given the ONE value its slot supplies — a sequence value's
      elements, and nothing for any other value. A list value is NOT opened
      (`[x, y]` is the list pattern) and a scalar is NOT a one-item supply: the
      only pattern that takes a value whole is a bare binder. This is the ONE
      rule shared by the one Model-C binder (`bindNeedOne`, for direct calls,
      callbacks, loop steps and clause families alike) and the literal-pattern
      matchers (`matchPatternInto`, `matchCountedPatternInto`), so a callback that
      supplies one value `V` to a pattern `P` binds exactly as the ordinary call
      `P(V)` does (formerly also the Ready binders `bindParameterPattern` /
      `bindCountedParameterPattern`, now in `HistoricalReadyBinding.lean`). A
      sequence value has 0 or at least 2 elements (there is no one-item
      sequence), which is why a one-item sequence pattern is invalid.
      C#: `Result.SequencePatternItems`. -/
  def sequencePatternItems? : Result -> Option (List Result)
    | sequenceValue rs => some rs
    | _ => none

  /-- The elements a LIST pattern `[p1, …, pn]` binds against: a list value's
      elements, and nothing for any other value — never a sequence value and
      never a scalar. Lists keep every cardinality, so `[]`, `[x]` and
      `[x, *rest]` match lists of zero, one and at least one element.
      C#: `Result.ListPatternItems`. -/
  def listPatternItems? : Result -> Option (List Result)
    | listValue rs => some rs
    | _ => none

  /-- Count emitted top-level values when a result is already in hand.
      Empty results emit 0. Any non-empty atomic, string, or sequence value
      counts as one value. List values ALWAYS count as one visible value,
      including the empty list `[]` — only the empty SEQUENCE value `()` is
      the invisible-able empty result.

      It is the emitted count of every value boundary (VAL-06): property reads,
      call results — `map`/`reduce` callback results included (HO-03) —, builtin
      results, selection and callback items. -/
  def valueCount : Result -> Nat
    | sequenceValue [] => 0
    | _ => 1

  /-- Selectable-position view of an indexing `:` TARGET: a sequence value or
      exact list value offers its immediate elements as positions; every other
      value follows `toItems` (a scalar offers itself as the single position).
      This view decides WHICH positions exist and never opens the selected
      element, which `select?` returns exactly as stored (a nested list element
      stays one opaque list, a nested sequence element one sequence value).
      C#: `Result.ProjectionItems`. -/
  def projectionItems : Result -> List Result
    | listValue rs => rs
    | r => r.toItems

  /-- SELECTION IS A VALUE BOUNDARY (September 2026): `:` selects one
      top-level position of a sequence or exact list target and returns the
      stored element as ONE value — it never opens it. A selected sequence
      value stays one sequence value, a selected list stays one exact list, and
      the selected value's origin is forgotten: the `.index` arm of
      `evalCounted` re-counts it through the ordinary value boundary
      (`Result.valueCount`), so `()` selected through any route emits zero
      values and everything else emits one. Only the spread marker
      (`spreadItems`) opens a selected value. `first`/`last`
      (`evalFirstCounted`/`evalLastCounted`) and higher-order callback items
      (`countedSequenceCallbackItem`) select through the same rule. Laws:
      `select_is_a_value_boundary`, `first_is_select_zero`, `last_is_select_last`
      in `KatLangArityLaws.lean`. C#: `Result.Index`. -/
  def select? (r : Result) (i : Nat) : Option Result :=
    r.projectionItems[i]?
end Result

/-- Counted evaluation result: the normalized value paired with the number of
  top-level values emitted at the current algorithm boundary.

  Helpers whose names end in `Counted` preserve this pair instead of
  collapsing the result to just the normalized value. -/
abbrev CountedResult := Prod Result Nat

/-- One algorithm-output evaluation prepared for consumers that need both the
    ordinary counted value and the evaluated written output slots. `outputSlots`
    contains the same evaluated `Result` values used to construct `counted`; it
    is not a second semantic sequence and does not perform another evaluation.
    C#: `PreparedAlgorithmOutput`. -/
structure PreparedAlgorithmOutput where
  counted : CountedResult
  outputSlots : List Result
  deriving Repr

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

def lookupAssoc {A} (k : Ident) : Assoc Ident A -> Option A
  | [] => none
  | (k',v)::xs => if k = k' then some v else lookupAssoc k xs

abbrev ValEnv := Assoc Ident Result

/-- One parameter's ALGORITHM-channel binding, together with a VALUE outcome
    recorded beside it when that outcome is a FAILURE.

    AT-MOST-ONCE ARGUMENT VALUE EVALUATION (Q-01, September 2026): within one
    call, a written argument slot is evaluated at most once for its value.
    Under Model C (NEED-01/02, October 2026) that slot is the parameter's
    supplied need cell (`EvalState.needs`, `supplyNeed`, `demandNeed`): its
    first VALUE demand evaluates the computation once and stores the completed
    outcome, which every later demand reuses, and the `.param` arm of
    `evalCounted` demands the cell before any tier below it. No production
    binding path writes `valueFailure?` any more: its eager writer — the slot
    evaluated at assembly, its failure recorded here — survives only in the
    historical fixture `HistoricalReadyBinding.lean` (`slotAlgorithmBinding`).
    The field and its readers (the `.param` arm's algorithm-tier fallback,
    `parameterValueFailure?`, `evalDotCallCounted`'s `string` arm) remain for
    that legacy Ready tier, and none of them evaluates `algorithm`. The
    algorithm channel remains what it is for: invocation (`f(x)`, an invoking
    builtin slot), structural member access, and forwarding.
    `valueFailure?` is `none` exactly when the value tier holds the
    parameter's value or nothing was recorded. C#: the `ValueError` element
    of an `AlgEnv` entry. -/
structure AlgBinding where
  algorithm : Algorithm
  valueFailure? : Option Error := none
  deriving Repr

/-- Algorithm environment: maps parameter names to algorithm-channel bindings.
    Used for higher-order algorithm parameters — when a caller passes an
    algorithm as an argument, the callee can invoke it by name.
    Parallel to ValEnv (which maps names to Results). -/
abbrev AlgEnv := Assoc Ident AlgBinding

namespace AlgEnv
  /-- The algorithm a name is bound to on the algorithm channel: what an
      invocation, a structural member access, or a forwarded argument uses. -/
  def lookup (env : AlgEnv) (x : Ident) : Option Algorithm :=
    (lookupAssoc x env).map AlgBinding.algorithm

  /-- The complete algorithm-channel binding of a name, including any failure
      recorded beside it (`AlgBinding.valueFailure?`; no Model-C binding path
      records one). -/
  def lookupBinding (env : AlgEnv) (x : Ident) : Option AlgBinding :=
    lookupAssoc x env

  /-- Remove the named bindings from an INHERITED algorithm environment — the
      algorithm-tier counterpart of `CountedParamEnv.shadow` and `ValEnv.shadow`.

      A callee's algorithm environment is its own algorithm bindings prepended
      to the CALLER's, which is what lets a nested call still invoke an
      ancestor-owned callable parameter. A parameter the call bound only on the
      VALUE channel contributes no algorithm binding, so without this filter a
      same-named callable inherited from the caller answered every
      call-position read of that parameter (`resolveAlg (.param x)`):
      `Inner(f) = f(2)` called as `Inner(5)` inside `Apply(f)` invoked the
      caller's `f` instead of failing as not-callable, exactly as the standalone
      `Inner(5)` does. Shadowing is applied per binding site through
      `EvalCtx.bindParameters`. C#: `ShadowAlgEnv`. -/
  def shadow (env : AlgEnv) (names : List Ident) : AlgEnv :=
    env.filter (fun entry => !names.contains entry.fst)
end AlgEnv

/-- Counted parameter environment for callback-bound values: higher-order
    sequence items (selected values re-counted through `countedSequenceCallbackItem`,
    so a `()` item carries emitted count 0 and every other item count 1) and the
    reducer accumulator bound beside them. Collecting bindings also record
    their bound value here; since collecting binding collects ONE exact
    immutable list value, those entries always carry emitted count 1 and agree
    with ordinary value-environment lookup (there is no separate raw-supply
    forwarding environment). Since selection became a value boundary
    (September 2026) every entry's count is `Result.valueCount` of its value. -/
abbrev CountedParamEnv := Assoc Ident (Prod Result Nat)

namespace CountedParamEnv
  def lookup (env : CountedParamEnv) (x : Ident) : Option (Prod Result Nat) :=
    lookupAssoc x env

  def shadow (env : CountedParamEnv) (names : List Ident) : CountedParamEnv :=
    env.filter (fun entry => !names.contains entry.fst)
end CountedParamEnv

inductive ZeroArgPropertyAccessKind where
  | lexical
  | structural
  deriving Repr, BEq

/-- Key of the per-run zero-parameter property cache — and with it the cache's
    semantic LAW (C#: `ZeroArgPropertyCacheKey`).

    THE RULE: a zero-parameter property is evaluated once per run for each
    resolved property binding; repeated VALUE access to that same binding reuses
    the result, a shadowing property is a different binding with its own entry,
    and an explicit call `A()` evaluates afresh, neither reading nor replacing
    the entry. CACHE IDENTITY FOLLOWS SEMANTIC BINDING IDENTITY, never the
    spelling of the name: the key is the resolved binding (its declaring scope
    and declaration), so two properties that happen to share a name never share
    an entry. HOW A PROPERTY VALUE IS CONSUMED DOES NOT AFFECT CACHING: the
    decision to reuse or evaluate belongs to the property ACCESS, and every
    consumer — an operator, a comparison, a list element, a selection, a user
    call argument, a builtin VALUE slot (`sum(A)`, `A.sum`, `if(c, A, B)`, a
    loop's initial state, `reduce`'s initial accumulator), the `.string`
    intrinsic's receiver, a callback body — receives the value that access
    produced (`supplyNeed`, `evalDotStringReceiverValue`). The scope of a
    stored value follows the binding's exposure classification:

    * an EXPORTED binding is self-contained — its value depends on no input that
      an enclosing owner's call binds — so the binding context at the access is
      not a determinant of the value: ONE entry per run per declaring scope
      serves every property-style access, from any call, callback, loop
      iteration, or explicit outer call. Its environment components are `none`.
    * a LOCAL-ONLY binding reads an input an enclosing owner's call binds
      through the dynamically threaded environments, so its value is a
      function of its DECLARING owner's binding context, retained by the existing
      lexical activation. Nested consumers never split that entry, and distinct
      owner calls never share it even with equal values. Scopes without retained
      activations keep the host environment fallback.

    Lean keys use structural representations (`reprStr`) because the model has
    immutable AST values rather than C# object identities. Run preparation
    assigns declaration identities before wiring, so separate declarations with
    equal bodies never alias; explicit `shared` identities preserve host DAGs.
    The owner is its `asScopeCtx` (including parent chain), and exported
    lexical/structural spellings have one key. Explicit calls neither read
    nor replace their own cache entry. Only successful results are stored, and
    an enclosing failure never rolls back a successful nested store. Recursive
    reads entered before the first store still evaluate, but their later
    completions do not replace the first successful entry. -/
structure ZeroArgPropertyCacheKey where
  accessKind : ZeroArgPropertyAccessKind
  owner      : String
  propertyName : Ident
  propertyAlgorithm : String
  valEnv : Option String
  algEnv : Option String
  countedParamEnv : Option String
  bindingContext : Option Nat
  deriving Repr, BEq

abbrev ZeroArgPropertyCache := List (Prod ZeroArgPropertyCacheKey CountedResult)

namespace ZeroArgPropertyCache
  def lookup (cache : ZeroArgPropertyCache) (key : ZeroArgPropertyCacheKey)
      : Option CountedResult :=
    match cache with
    | [] => none
    | (existingKey, value) :: rest =>
        if existingKey == key then some value else lookup rest key

  def insert (cache : ZeroArgPropertyCache) (key : ZeroArgPropertyCacheKey)
      (value : CountedResult) : ZeroArgPropertyCache :=
    match cache with
    | [] => [(key, value)]
    | (existingKey, existingValue) :: rest =>
        if existingKey == key then
          (existingKey, existingValue) :: rest
        else
          (existingKey, existingValue) :: insert rest key value
end ZeroArgPropertyCache

/-- Invocation-local supply bindings refer to stable addresses in the run heap. -/
abbrev NeedEnv := Assoc Ident Nat

structure EvalCtx where
  callStack : List Algorithm
  algEnv    : AlgEnv := []
  countedParamEnv : CountedParamEnv := []
  needEnv : Assoc Ident Nat := []
  bindingContext : Nat := 0
  headScope : Option ScopeCtx := none
  deriving Repr


/-- VALUE state is separate from callable projection. Completed failures are sticky. -/
inductive NeedState where
  | suspended
  | evaluating
  | completed (outcome : Except Error CountedResult)
  deriving Repr

inductive NeedSuspension where
  | expression (source : Expr) (caller : EvalCtx) (values : ValEnv)
  | collector (slice : List Nat)
  -- Produced data is a calculation value and carries no callable identity.
  | ready (value : CountedResult)
  deriving Repr

structure NeedCell where
  suspension : NeedSuspension
  state : NeedState := .suspended
  callable : Option (Except Error (Option Algorithm)) := none
  deriving Repr

/-- The three binding channels saved by one lexical owner activation. -/
structure ParameterActivation where
  values : ValEnv
  needs : NeedEnv := []
  algorithms : AlgEnv
  counted : CountedParamEnv
  bindingContext : Nat := 0
  deriving Repr

/-- Per-run evaluator state. The zero-parameter property cache is part of the
    Lean semantics because property-style `A` and explicit `A()` now have
    distinct observable call shapes. The state is created fresh for each
    top-level `runResult`; it is not general memoization and does not cache
    arbitrary calls or expression results. -/
structure EvalState where
  needs : Array NeedCell := #[]
  zeroArgPropertyCache : ZeroArgPropertyCache := []
  nextBindingContext : Nat := 1
  lexicalActivations : Array ParameterActivation := #[]
  nextRuntimeDeclaration : Nat := 0
  deriving Repr

namespace EvalState
  def empty : EvalState := {}
end EvalState

/-- Errors retain completed evaluator state. A failed value probe may be
    accepted through its algorithm channel; successful nested properties keep
    their first run result even when that enclosing probe fails. The wrapper's
    `run` projection preserves the public Except-shaped result API. -/
structure EvalM (α : Type) where
  runState : ExceptT Error (StateM EvalState) α

instance : Monad EvalM where
  pure a := ⟨pure a⟩
  bind m f := ⟨m.runState >>= fun a => (f a).runState⟩

instance : MonadStateOf EvalState EvalM where
  get := ⟨get⟩
  set s := ⟨set s⟩
  modifyGet f := ⟨modifyGet f⟩

instance : MonadExceptOf Error EvalM where
  throw err := ⟨throw err⟩
  tryCatch m handler := ⟨tryCatch m.runState (fun err => (handler err).runState)⟩

instance : MonadLift (Except Error) EvalM where
  monadLift e := ⟨match e with | .ok a => pure a | .error err => throw err⟩

namespace EvalM
  def error {A : Type} (err : Error) : EvalM A := ⟨throw err⟩
  def ok {A : Type} (value : A) : EvalM A := pure value

  @[simp] theorem pure_bind {A B : Type} (value : A) (next : A -> EvalM B) :
      (pure value >>= next : EvalM B) = next value := rfl

  def run {A : Type} (m : EvalM A) (state : EvalState) : Except Error (A × EvalState) :=
    let (result, nextState) := m.runState state
    result.map (fun value => (value, nextState))
end EvalM

instance {A : Type} : Nonempty (EvalM A) := Nonempty.intro (.error Error.badArity)

/-- Capture a probe's error without rolling back successful nested cache
    stores or binding identities. The failed property itself is never stored. -/
def evalAttempt {A : Type} (m : EvalM A) : EvalM (Except Error A) :=
  ⟨fun state =>
    let (result, nextState) := m.runState state
    (.ok result, nextState)⟩

def runEvalM (m : EvalM A) : Except Error A :=
  match m.run EvalState.empty with
  | .ok (value, _) => .ok value
  | .error err => .error err

namespace EvalCtx
  def empty : EvalCtx := { callStack := [], algEnv := [], countedParamEnv := [] }
  def push (a : Algorithm) (ctx : EvalCtx) : EvalCtx :=
    { ctx with callStack := a :: ctx.callStack, headScope := none }
  def head? (ctx : EvalCtx) : Option Algorithm := ctx.callStack.head?
  def withAlgEnv (env : AlgEnv) (ctx : EvalCtx) : EvalCtx :=
    { ctx with algEnv := env }
  def withCountedParamEnv (env : CountedParamEnv) (ctx : EvalCtx) : EvalCtx :=
    { ctx with countedParamEnv := env }

  /-- The callee-side context of a parameter binding: the callee's own
      algorithm and counted bindings prepended to the CALLER's tiers with the
      bound parameter names removed from the inherited need-cell tier (`needEnv`) and from BOTH inherited binding tiers (`AlgEnv.shadow`,
      `CountedParamEnv.shadow`; the value tier is shadowed beside it with
      `ValEnv.shadow`).

      A bound parameter owns its name on every channel: a call-position read of
      a value-bound parameter never reaches a same-named caller callable,
      exactly as a value-position read of an algorithm-bound parameter never
      reaches a same-named caller value. Names the callee does not bind stay
      visible, which is what lets a nested call still reach an ancestor-owned
      callable. Every user-call, conditional-call, callback, and loop-step
      binding site builds its context through this one definition, so no path
      can shadow one tier and forget another.
      C#: `ShadowInheritedParameterEnvironments` plus the site's own prepend. -/
  def bindParameters (names : List Ident) (algBindings : AlgEnv)
      (countedBindings : CountedParamEnv) (ctx : EvalCtx) : EvalM EvalCtx := do
    -- Equal values in separate calls are still distinct bindings. Allocate at
    -- every binding boundary, including an explicit zero-argument call, just
    -- as C# creates fresh environment lists there. A property read only pushes
    -- its algorithm and preserves this identity.
    let state <- get
    set { state with nextBindingContext := state.nextBindingContext + 1 }
    pure { ctx with
      bindingContext := state.nextBindingContext,
      needEnv := ctx.needEnv.filter (fun entry => !names.contains entry.fst),
      algEnv := algBindings ++ AlgEnv.shadow ctx.algEnv names,
      countedParamEnv := countedBindings ++ CountedParamEnv.shadow ctx.countedParamEnv names }
end EvalCtx

/-- Allocate a fresh cell; transporting a parameter never calls this function. -/
def allocateNeed (suspension : NeedSuspension) : EvalM Nat := do
  let state <- get
  let address := state.needs.size
  set { state with needs := state.needs.push { suspension := suspension } }
  pure address

def readyNeed (value : CountedResult) : EvalM Nat :=
  allocateNeed (.ready value)


abbrev ValEnv.lookup (env : ValEnv) (x : Ident) : Option Result :=
  lookupAssoc x env

/-- Remove the named bindings from an INHERITED value environment.

    A callee's value environment is its own bindings prepended to the CALLER's
    (`argEnv ++ env`), which is what lets a nested property body still read an
    ancestor-owned parameter. A parameter the call bound only on the ALGORITHM
    channel — a higher-order argument, or any argument whose value evaluation
    failed — contributes no entry to `argEnv`, so without this filter a
    same-named binding inherited from the caller would answer every
    value-position read of that parameter: the callee would silently observe an
    unrelated caller value instead of the argument bound at THIS invocation, and
    which caller parameter names happen to collide with a callee's parameter
    names would become observable. Shadowing the callee's whole parameter list
    is exactly the rule `CountedParamEnv.shadow` and `AlgEnv.shadow` apply to
    the counted and algorithm tiers (`EvalCtx.bindParameters`); names that DO
    carry a value binding are shadowed by `argEnv` anyway, so filtering the
    tail changes nothing for them.
    C#: `ShadowValEnv`. -/
def ValEnv.shadow (env : ValEnv) (names : List Ident) : ValEnv :=
  env.filter (fun entry => !names.contains entry.fst)

def dedupList [BEq A] (xs : List A) : List A :=
  let rec go (seen : List A) : List A -> List A
    | []      => []
    | x :: rest => if seen.elem x then go seen rest else x :: go (x :: seen) rest
  go [] xs

--------------------------------------------------------------------------------
-- Algorithm helpers
--------------------------------------------------------------------------------

/-- Primary helper: Lookup PropDef by name (any visibility). -/
def lookupPropDefAny? (ps : List PropDef) (k : Ident) : Option PropDef :=
  ps.find? (fun p => p.name = k)

/-- Primary helper: Lookup PropDef by name when the property is exported. -/
def lookupPropDefExportedAny? (ps : List PropDef) (k : Ident) : Option PropDef :=
  ps.find? (fun p => p.name = k && p.exposure.isExported)

/-- Primary helper: Lookup PropDef by name (public only — the member an `open` provides,
    selected by visibility alone; accessibility is checked after selection). -/
def lookupPropDefPublic? (ps : List PropDef) (k : Ident) : Option PropDef :=
  ps.find? (fun p => p.name = k && p.isPublic)

/-- Lookup Algorithm from PropDef list (any visibility). -/
def lookupPropAny (ps : List PropDef) (k : Ident) : Option Algorithm :=
  (lookupPropDefAny? ps k).map (fun propDef => propDef.alg)

/-- Lookup Algorithm from PropDef list (public only). -/
def lookupPropPublic (ps : List PropDef) (k : Ident) : Option Algorithm :=
  (lookupPropDefPublic? ps k).map (fun propDef => propDef.alg)

/-- Check if PropDef list contains a property (any visibility). -/
def hasPropAny (ps : List PropDef) (k : Ident) : Bool :=
  (lookupPropDefAny? ps k).isSome

/-- The root level of a scope chain — the prelude level every evaluation chain is rooted at.
    A loaded module is wired there (`Algorithm.withParent`). C#: `Evaluator.ChainRoot`. -/
def ScopeCtx.chainRoot : ScopeCtx -> ScopeCtx
  | .mk none params opens props output branches activation id =>
      .mk none params opens props output branches activation id
  | .mk (some parent) _ _ _ _ _ _ _ => parent.chainRoot

namespace Algorithm
  def normalCallableParameters (ps : List Ident) : List CallableParameter :=
    ps.map (fun p => { name := p })

  def normalParameters (ps : List Ident) : List ParameterPattern :=
    ParameterPattern.normalPatterns ps

  def parent : Algorithm -> Option ScopeCtx
    | .mk p _ _ _ _ _ => p
    | .builtin _ => none
    | .conditional p _ _ _ => p
    | .alias p _ _ _ _ => p
  /-- An alias declares no parameter list of its own: its callable's is its target's. -/
  def parameterPatterns : Algorithm -> List ParameterPattern
    | .mk _ parameterPatterns _ _ _ _ => parameterPatterns
    | .builtin _ => []
    | .conditional _ _ _ _ => []
    | .alias _ _ _ _ _ => []

  def parameters : Algorithm -> List CallableParameter
    | a => (parameterPatterns a).flatMap ParameterPattern.captures

  def params : Algorithm -> List Ident
    | a => (parameters a).map (fun parameter => parameter.name)
  def paramKinds : Algorithm -> List ParameterKind
    | a => (parameters a).map (fun parameter => parameter.kind)
  def callableSignature (name : Ident) (a : Algorithm) : CallableSignature :=
    { name := name, parameters := parameters a }
  def opens : Algorithm -> List Expr
    | .mk _ _ op _ _ _ => op
    | .builtin _ => []
    | .conditional _ op _ _ => op
    | .alias _ op _ _ _ => op
  /-- An alias's are what its own body declares — never its target's members. -/
  def props : Algorithm -> List PropDef
    | .mk _ _ _ pr _ _ => pr
    | .builtin _ => []
    | .conditional _ _ _ _ => []
    | .alias _ _ pr _ _ => pr
  /-- The algorithm's output as an `OutputBundle` — ordered original written
      expression rows. The algorithm is the scope-owning DEFINITION of this
      bundle; the bundle itself owns no scope. An alias's is its ONE written row,
      the target reference (what the static walks see it read); the evaluator never
      evaluates an alias's output as rows — it normalizes the alias first. -/
  def output : Algorithm -> OutputBundle
    | .mk _ _ _ _ out _ => out
    | .builtin _ => []
    | .conditional _ _ _ _ => []
    | .alias _ _ _ target _ => [target]

  /-- Access branches for conditional algorithms. Returns [] for other forms. -/
  def branches : Algorithm -> List CondBranch
    | .conditional _ _ bs _ => bs
    | _ => []

  def declarationId : Algorithm -> Option PropertyIdentity
    | .mk _ _ _ _ _ id => id
    | .conditional _ _ _ id => id
    | .alias _ _ _ _ id => id
    | .builtin _ => none

  def withDeclarationId (id : Option PropertyIdentity) : Algorithm -> Algorithm
    | .mk p ps op pr out _ => .mk p ps op pr out id
    | .conditional p op bs _ => .conditional p op bs id
    | .alias p op pr target _ => .alias p op pr target id
    | .builtin b => .builtin b

  /-- Whether this is a loaded module's own declaration (`PropertyIdentity.module`). -/
  def isModuleRoot (a : Algorithm) : Bool :=
    match a.declarationId with
    | some (.module _) => true
    | _ => false

  /-- Wire under the scope `p`. A loaded module (Q-31 H-P) is wired under the chain's root
      level instead, wherever it is reached: its names never see its holder's, and every reach
      is the one declaration in the one declaring scope (Q-32 I-U). C#: `Evaluator.WithParent`. -/
  def withParent (p : Option ScopeCtx) : Algorithm -> Algorithm
    | .mk _ parameterPatterns op pr out (some (.module n)) =>
        .mk (p.map ScopeCtx.chainRoot) parameterPatterns op pr out (some (.module n))
    | .mk _ parameterPatterns op pr out id => .mk p parameterPatterns op pr out id
    | .builtin b => .builtin b
    | .conditional _ op bs id => .conditional p op bs id
    | .alias _ op pr target (some (.module n)) => .alias (p.map ScopeCtx.chainRoot) op pr target (some (.module n))
    | .alias _ op pr target id => .alias p op pr target id

  def parameterForName? (x : Ident) : List CallableParameter -> Option CallableParameter
    | [] => none
    | parameter :: parameters =>
        if x = parameter.name then some parameter else parameterForName? x parameters

  def mergeParameters (oldParameters : List CallableParameter) (newParams : List Ident)
      : List CallableParameter :=
    newParams.map (fun p => (parameterForName? p oldParameters).getD { name := p })

  def mergeParameterPatterns (oldPatterns : List ParameterPattern) (newParams : List Ident)
      : List ParameterPattern :=
    let oldCaptures := oldPatterns.flatMap ParameterPattern.captures
    if newParams.take oldCaptures.length == oldCaptures.map (fun parameter => parameter.name) then
      oldPatterns ++ (newParams.drop oldCaptures.length).map (fun p => ParameterPattern.capture { name := p })
    else
      (mergeParameters oldCaptures newParams).map ParameterPattern.capture

  /-- Replace the explicit parameter list of a user-defined algorithm.
      This is used by clause elaboration to preserve ignored binders such as
      `K(a, b) = a`, where `b` must remain part of the ordinary call interface
      even though it is not referenced in the body. -/
  def withParams (ps : List Ident) : Algorithm -> Algorithm
    | .mk p oldPatterns op pr out id => .mk p (mergeParameterPatterns oldPatterns ps) op pr out id
    | .builtin b => .builtin b
    | .conditional p op bs id => .conditional p op bs id
    | .alias p op pr target id => .alias p op pr target id

  def withParameterPatterns (patterns : List ParameterPattern) : Algorithm -> Algorithm
    | .mk p _ op pr out id => .mk p patterns op pr out id
    | .builtin b => .builtin b
    | .conditional p op bs id => .conditional p op bs id
    | .alias p op pr target id => .alias p op pr target id

  def hasStructuredParameterPattern (a : Algorithm) : Bool :=
    ParameterPattern.hasStructured (parameterPatterns a)

  def topLevelParameterKind? (a : Algorithm) (name : Ident) : Option ParameterKind :=
    ParameterPattern.topLevelCaptureKind? name (parameterPatterns a)

  def collectingParam? (a : Algorithm) : Option (Nat × Ident) :=
    if hasStructuredParameterPattern a then
      none
    else
      let rec go : Nat -> List CallableParameter -> Option (Nat × Ident)
        | _, [] => none
        | index, parameter :: parameters =>
            match parameter.kind with
            | .collecting => some (index, parameter.name)
            | .normal => go (index + 1) parameters
      go 0 (parameters a)

  /-- A callable whose top-level parameter list consumes the supplied call
      argument supply: any top-level collecting capture, whether a lone collecting binding
      `*name` or a comma shape such as `x, *y, z`. A plain sequence-valued
      argument stays one supplied argument; only explicit spread opens it first. -/
  def usesItemSupplyBinding (a : Algorithm) : Bool :=
    (collectingParam? a).isSome

  /-- Classify a same-name clause family after all of its clauses are known.
      This is the real ordinary-vs-conditional decision boundary.

      A same-name clause group is ordinary only when it contains exactly one
      clause and that sole head is a recursive capture/structural parameter pattern.
      Otherwise the whole group remains conditional. This prevents regressions
      where an early ordinary-looking clause is committed as ordinary before
      later clauses reveal true pattern semantics, such as:

          F(0) = 0
          F(x) = 1 -/
  def clauseGroupDefinitionKind : List CondBranch -> ClauseGroupDefinitionKind
    | [branch] =>
        match Pattern.plainClauseParameterPatterns? branch.pattern with
        | some patterns => .ordinary patterns
        | none => .conditional
    | _ => .conditional

  /-- Elaborate a whole same-name clause family.
      Front-ends should collect all clauses of a same-name family first, then
      call this helper exactly once. A family elaborates as ordinary only when
      it has exactly one clause and that sole head is a recursive capture/structural
      parameter pattern; otherwise the whole family elaborates as
      `Algorithm.conditional`.

      This preserves higher-order ordinary call semantics for single-clause
      families such as `Apply(f) = f(4)` and
      `Choose(x, predicate) = if(predicate(x), x, 0)`, and preserves structural
      ordinary parameter shapes such as `PairSum((x, y)) = x + y` and
      `Only([x]) = x`, while keeping
      multi-clause and literal/mixed families conditional.

      Opens are BRANCH-OWNED: every branch body keeps its own opens, and the
      family itself owns none (`opens := []` in both conditional arms). An
      `open` written in one clause provides its names to that branch body and
      its nested scopes only (MOD-05): the family scope is the parent level of
      EVERY selected branch (`wireSelectedBranchBody` installs `callee.opens`
      there), so copying one branch's opens onto the family would leak them
      into every sibling branch — and re-resolve a copied named target such as
      a branch-local `open L` from the family's scope, where `L` is not
      visible. Clause bodies are brace blocks and may each declare their own
      opens, so branch opens routinely differ. C#: `Algorithm.ElaborateClauseGroup`
      (`Opens: []`). -/
  def elaborateClauseGroup : List CondBranch -> Algorithm
    | [branch] =>
        match clauseGroupDefinitionKind [branch] with
        | .ordinary patterns => branch.body.withParameterPatterns patterns
        | .conditional =>
            .conditional (parent branch.body) [] [{
              pattern := branch.pattern
              body := branch.body.withParams []
            }]
    | branches =>
        .conditional
          (branches.head?.map (fun branch => parent branch.body) |>.join)
          []
          (branches.map (fun branch => {
            pattern := branch.pattern
            body := branch.body.withParams []
          }))

  /-- Convenience wrapper for an already-known single-clause group.
      Front-ends must not use this while parsing a clause family incrementally;
      they should first collect the full same-name group and then call
      `elaborateClauseGroup`. -/
  def elaborateClauseDefinition (pattern : Pattern) (body : Algorithm) : Algorithm :=
    elaborateClauseGroup [{ pattern := pattern, body := body }]

  def asScopeCtx (a : Algorithm) : ScopeCtx :=
    ScopeCtx.mk (parent a) (params a) (opens a) (props a) (output a) (branches a) none (declarationId a)

  def isBuiltin : Algorithm -> Bool
    | .builtin _ => true
    | _          => false

  /-- Algorithm-level explicit parameters define a closed direct-call interface
      and therefore require the algorithm to define output.  Surface front-ends
      must not append inferred implicit parameters to this interface; free names
      in explicitly parameterized bodies must resolve lexically or be reported as
      undeclared. -/
  def declaresExplicitParamsWithoutOutput : Algorithm -> Bool
    | .mk _ parameterPatterns _ _ out _ => !parameterPatterns.isEmpty && out.isEmpty
    | .builtin _ => false
    | .conditional _ _ _ _ => false
    | .alias _ _ _ _ _ => false

  /-- Unfiltered property lookup (sees private properties). -/
  def lookupProp (a : Algorithm) (k : Ident) : Option Algorithm :=
    lookupPropAny (props a) k

  /-- Public-only property lookup (for open resolution). -/
  def lookupPublicProp (a : Algorithm) (k : Ident) : Option Algorithm :=
    lookupPropPublic (props a) k

  /-- Lookup PropDef by name (any visibility). -/
  def lookupPropDefAny? (a : Algorithm) (k : Ident) : Option PropDef :=
    KatLang.lookupPropDefAny? (props a) k

  /-- Lookup PropDef by name when the property is exported. -/
  def lookupPropDefExportedAny? (a : Algorithm) (k : Ident) : Option PropDef :=
    KatLang.lookupPropDefExportedAny? (props a) k

  /-- Lookup PropDef by name (public only). -/
  def lookupPropDefPublic? (a : Algorithm) (k : Ident) : Option PropDef :=
    KatLang.lookupPropDefPublic? (props a) k

  /-- True when a conditional algorithm has a branch body defining the given property. -/
  def conditionalBranchesDefineProperty : Algorithm -> Ident -> Bool
    | .conditional _ _ bs _, k => bs.any (fun br => hasPropAny (props br.body) k)
    | _, _ => false

  /-- Wire a child algorithm to its parent's scope context. -/
  def childOf (a : Algorithm) (child : Algorithm) : Algorithm :=
    child.withParent (some (a.asScopeCtx))

  /-- Validate that all branches of a conditional algorithm have the same
      top-level pattern arity.  Returns `none` if valid (or non-conditional),
      `some (expected, actual)` for the first mismatching branch.
      This enforces the uniform top-level arity invariant:
      conditional algorithms are "one algorithm, one outer interface, many branches".

      Enforced in two places: front-ends report it during clause elaboration,
      and the core pre-evaluation validation pass (`runResultM` via
      `validateConditionalBranchArities`) rejects violating ASTs with
      `Error.branchArityMismatch` before any evaluation. -/
  def validateBranchArities : Algorithm -> Option (Nat × Nat)
    | .conditional _ _ bs _ =>
        match bs with
        | [] => none
        | b :: rest =>
            let expected := b.pattern.topLevelArity
            if rest.any (fun br => br.pattern.topLevelArity != expected)
            then
              match rest.find? (fun br => br.pattern.topLevelArity != expected) with
              | some bad => some (expected, bad.pattern.topLevelArity)
              | none     => none  -- unreachable
            else none
    | _ => none

  /-- Compute the top-level output arity of an algorithm.
      For user-defined algorithms (Algorithm.mk), this is the number of
      top-level output expressions.  For other forms, returns 0. -/
  def topLevelOutputArity (a : Algorithm) : Nat := a.output.length

  /-- Validate that all branches of a conditional algorithm have the same
      top-level output arity.  Returns `none` if valid (or non-conditional),
      `some (expected, actual)` for the first mismatching branch.
      This enforces the uniform top-level output arity invariant:
      all branches of a conditional algorithm share one output interface.
      Nested internal output structure may vary, but the outer number of
      outputs must remain consistent.

      Enforced in two places: front-ends report it during clause elaboration,
      and the core pre-evaluation validation pass (`runResultM` via
      `validateConditionalBranchArities`) rejects violating ASTs with
      `Error.branchOutputArityMismatch` before any evaluation. -/
  def validateBranchOutputArities : Algorithm -> Option (Nat × Nat)
    | .conditional _ _ bs _ =>
        match bs with
        | [] => none
        | b :: rest =>
            let expected := topLevelOutputArity b.body
            if rest.any (fun br => topLevelOutputArity br.body != expected)
            then
              match rest.find? (fun br => topLevelOutputArity br.body != expected) with
              | some bad => some (expected, topLevelOutputArity bad.body)
              | none     => none  -- unreachable
            else none
    | _ => none

  /-- Check whether the property list of an Algorithm.mk contains duplicate
      property names.  Returns the first duplicate name found, or `none`
      if all names are unique.  This enforces the unique property name invariant. -/
  def findDuplicatePropName : Algorithm -> Option Ident
    | .mk _ _ _ ps _ _ => firstDuplicateName (ps.map (·.name))
    | .alias _ _ ps _ _ => firstDuplicateName (ps.map (·.name))
    | _ => none
  where
    firstDuplicateName (names : List Ident) : Option Ident :=
      let rec go : List Ident -> List Ident -> Option Ident
        | [],        _    => none
        | n :: rest, seen =>
            if seen.elem n then some n
            else go rest (n :: seen)
      go names []

  /-- Check whether the branch list of an Algorithm.conditional contains
      match-equivalent patterns.  Returns `true` if a duplicate is found.
      This enforces the unique branch pattern invariant. -/
  def hasDuplicateBranchPatterns : Algorithm -> Bool
    | .conditional _ _ bs _ =>
        let rec go : List CondBranch -> Bool
          | [] => false
          | b :: rest =>
              if rest.any (fun br => b.pattern.isMatchEquivalent br.pattern)
              then true
              else go rest
        go bs
    | _ => false
end Algorithm

/-- Enforce the uniform branch arity invariants of one conditional algorithm:
    all branches must share the same top-level pattern arity and the same
    top-level output arity. Mirrors the C# parser's clause-elaboration checks;
    in the Lean model the check runs in the pre-evaluation validation pass. -/
def validateConditionalBranchArities (name : Ident) (a : Algorithm) : EvalM Unit :=
  match Algorithm.validateBranchArities a with
  | some (expected, actual) => .error (Error.branchArityMismatch name expected actual)
  | none =>
      match Algorithm.validateBranchOutputArities a with
      | some (expected, actual) => .error (Error.branchOutputArityMismatch name expected actual)
      | none => pure ()

/-- The one message of an invalid singleton sequence pattern (the singleton rule,
    `ParameterPattern.isSingletonSequenceItems`). C#: the parser's
    `SingletonSequencePattern` diagnostic and the pre-evaluation violation
    `PreEvaluationAstViolation.SingletonSequencePattern` share its wording. -/
def singletonSequencePatternMessage : String :=
  "A sequence pattern with exactly one non-collecting item is invalid: KatLang has no one-item sequence value. Bind the whole value with a plain name, or use the list pattern `[x]` for a one-element list."

/-- The singleton rule over an algorithm's OWN patterns: its explicit parameter
    patterns, or every branch head of a clause family. -/
def Algorithm.hasSingletonSequencePattern : Algorithm -> Bool
  | .mk _ parameters _ _ _ _ => ParameterPattern.anyHasSingletonSequenceGroup parameters
  | .builtin _ => false
  | .conditional _ _ branches _ => branches.any (fun branch => branch.pattern.headHasSingletonSequenceGroup)
  | .alias _ _ _ _ _ => false

/-- The one message of a parameter-pattern level with more than one collecting
    capture — the parser's wording for a written head. C#:
    `Parser.MultipleCollectingBindingsPerLevelDiagnostic`, shared by the
    pre-evaluation violation `PreEvaluationAstViolation.MultipleCollectingCaptures`. -/
def multipleCollectingBindingsPerLevelMessage : String :=
  "Only one collecting binding is allowed per pattern level."

/-- The collector rule over an algorithm's OWN parameter patterns (X-02): some
    pattern level holds more than one collecting capture. -/
def Algorithm.hasMultipleCollectingCaptures : Algorithm -> Bool
  | .mk _ parameters _ _ _ _ => ParameterPattern.hasMultipleCollectingCapturesAtAnyLevel parameters
  | .builtin _ => false
  | .conditional _ _ _ _ => false
  | .alias _ _ _ _ _ => false

/-- Human-readable constructor kind for diagnostics. -/
def Expr.kind : Expr -> String
  | .param _      => "param"
  | .num _        => "num"
  | .stringLiteral _ => "stringLiteral"
  | .boolLiteral _ => "boolLiteral"
  | .unary _ _    => "unary"
  | .binary _ _ _ => "binary"
  | .comparison _ _ => "comparison"
  | .index _ _    => "index"
  | .sequenceConstruct _ _ => "sequenceConstruct"
  | .emptySequence _ => "emptySequence"
  | .sequenceSpread _    => "spread"
  | .listLiteral _ => "listLiteral"
  | .resolve _    => "resolve"
  | .algorithmExpr _ => "algorithmExpr"
  | .capture _    => "capture"
  | .call _ _     => "call"
  | .dotMember _ _ _ _ => "dotCall"

/-- Render an empty-sequence core node by depth for diagnostics. Evaluation
  normalizes repeated ordinary parentheses back to `()`. -/
def emptySequenceText (depth : Nat) : String :=
  String.ofList (List.replicate (depth + 1) '(' ++ List.replicate (depth + 1) ')')

/-- This MINIMAL renderer models only structural reference forms; every other
  kind (`.num`, `.param`, `.binary`, ...) renders as the `(kind)` fallback, so
  C#'s merged `OpenExprName` prints more detail for them. That gap is
  pre-existing and uniform across `.dotCall`, `.sequenceConstruct`,
  `.sequenceSpread`, and `.index` alike — it is a property of this renderer's
  coverage, not of indexing. -/
def openExprNameIndexSelectorNeedsParens : Expr -> Bool
  | .dotMember _ _ _ _ => true
  | .index _ _        => true
  | .sequenceSpread _ => true
  | _                 => false

/-- Extract a descriptive name from an open expression for error messages.
  See `openExprNameIndexSelectorNeedsParens` for this renderer's coverage gap. -/
def openExprName (e : Expr) : String :=
  match e with
  | .resolve n => n
  | .dotMember o n _ _ =>
      openExprName o ++ "." ++ n
  -- Indexing is source-faithful postfix `target:selector`, never the `(index)`
  -- kind fallback. Only the forms this renderer prints BARE can continue the
  -- postfix chain and rebind; every unmodelled kind is already self-delimiting
  -- as `(kind)`, so parenthesizing it again would only double the parentheses.
  | .index target selector =>
      let selectorName := openExprName selector
      openExprName target ++ ":" ++
        (if openExprNameIndexSelectorNeedsParens selector then "(" ++ selectorName ++ ")"
         else selectorName)
  | .algorithmExpr _ => "(inline library)"
  | .capture _ => "(inline library)"
  -- SequenceConstruct is an internal value node; ';' is not surface syntax,
  -- so render it as one sequence value, never with ';'.
  | .sequenceConstruct a b => "(" ++ openExprName a ++ ", " ++ openExprName b ++ ")"
  -- A spread expression renders in the canonical postfix-marker form.
  | .sequenceSpread a => openExprName a ++ "*"
  -- Empty sequence core nodes render by depth for diagnostics.
  | .emptySequence depth => emptySequenceText depth
  | _ => s!"({Expr.kind e})"            -- * informative fallback using constructor kind

/-- A STATIC PATH (FWD-02): a name, or an argumentless dot edge whose receiver is itself
    a static path or a block — an edge spelled `string` included, since a declared member
    named `string` is selected like any member (Q-17 S-C). Every callable alias target is
    one; the surface pass forms an alias over nothing else. Returns the path's head (a name
    or a block) and its member steps, outermost receiver first.
    C#: `StaticAliasTargets.IsStaticPath`. -/
def Expr.staticAliasPath? : Expr -> Option (Expr × List Ident)
  | .resolve name => some (.resolve name, [])
  | .dotMember receiver member _ none =>
      match receiver with
      | .algorithmExpr block => some (.algorithmExpr block, [member])
      | other => (Expr.staticAliasPath? other).map (fun (head, steps) => (head, steps ++ [member]))
  | _ => none

def Expr.isStaticAliasPath (e : Expr) : Bool := (Expr.staticAliasPath? e).isSome

/-- The message of a callable alias whose target is not a static path (only a host-built
    tree has one). C#: `Evaluator.AliasTargetNotStaticPathMessage`. -/
def aliasTargetNotStaticPathMessage (target : String) : String :=
  s!"callable alias target {target} is not a name or a declared member path"

/-- The message of a callable alias cycle (only a host-built tree has one).
    C#: `Evaluator.AliasCycleMessage`. -/
def aliasCycleMessage : String :=
  "callable alias cycle: an alias target leads back to an alias already on its chain"

/-- The property `name` STATIC lexical lookup selects in `scope` (outermost scope first):
    the innermost scope that declares it, with the scope chain of the selected property's
    value (the scopes up to and including its owner). -/
def staticLexicalLookup? (scope : List Algorithm) (name : Ident) : Option (Algorithm × List Algorithm) :=
  let rec go : List Algorithm -> Option (Algorithm × List Algorithm)
    | [] => none
    | owner :: outerReversed =>
        match Algorithm.lookupPropDefAny? owner name with
        | some prop => some (prop.alg, (owner :: outerReversed).reverse)
        | none => go outerReversed
  go scope.reverse

/-- One STATIC step of a callable alias declared inside `chain` (outermost scope first): the
    callable its target selects by the ownership-first PROPERTY lookup over the alias's own
    declarations and its enclosing scopes, then structural navigation of declared members, with
    that callable's own scope chain. No `open` and no prelude is consulted: a target leaving the
    static chain has no static step. C#: `StaticAliasTargets.TryResolve`. -/
def staticAliasStep? (chain : List Algorithm) (alias : Algorithm) (target : Expr)
    : Option (Algorithm × List Algorithm) :=
  match Expr.staticAliasPath? target with
  | none => none
  | some (head, steps) =>
      let scope := chain ++ [alias]
      let start : Option (Algorithm × List Algorithm) :=
        match head with
        | .resolve name => staticLexicalLookup? scope name
        | .algorithmExpr block => some (block, scope)
        | _ => none
      -- A loaded module is rooted at the prelude (Q-31 H-P): what it declares resolves in a
      -- chain that starts at the module, and the module itself has no enclosing chain.
      (steps.foldl
        (fun acc step => acc.bind fun (value, valueChain) =>
          (Algorithm.lookupPropDefAny? value step).map fun prop =>
            (prop.alg, (if value.isModuleRoot then [] else valueChain) ++ [value]))
        start).map fun (value, valueChain) => (value, if value.isModuleRoot then [] else valueChain)

/-- The STATIC alias chase from the alias `start` declared inside `chain`: whether it leads back
    to an alias already on it (a cycle, only possible in a host-built tree). The chase runs at most
    `fuel` hops — `Algorithm.aliasCount` of the tree, the number of distinct aliases the static
    chase can land on — so a chase still landing on an alias after that many hops has revisited
    one: it is a cycle. C#: `StaticAliasTargets.FindCycle`. -/
def staticAliasCycle (fuel : Nat) (chain : List Algorithm) (start : Algorithm) : Bool :=
  match fuel, start with
  | 0, .alias _ _ _ _ _ => true
  | fuel + 1, .alias _ _ _ target _ =>
      match staticAliasStep? chain start target with
      | some (next@(.alias _ _ _ _ _), nextChain) => staticAliasCycle fuel nextChain next
      | _ => false
  | _, _ => false

/-- The STATIC normalization of the callable `a` declared inside `chain` (outermost scope first):
    `a` itself when it is not an alias, else the callable its chain of static steps
    (`staticAliasStep?`) ends at within `fuel` hops — none when a step leaves the static chain
    (an `open`, the prelude) or the fuel runs out. The surface pass's identity resolution through
    aliases (C#: the recorded `Algorithm.Alias.ResolvedTarget`), here over the static chain only;
    the evaluator's is `resolveAliasTarget`. -/
def staticAliasTarget? : Nat -> List Algorithm -> Algorithm -> Option Algorithm
  | _, _, .mk p ps op pr out id => some (.mk p ps op pr out id)
  | _, _, .builtin b => some (.builtin b)
  | _, _, .conditional p op bs id => some (.conditional p op bs id)
  | 0, _, .alias _ _ _ _ _ => none
  | fuel + 1, chain, .alias p op pr target id =>
      match staticAliasStep? chain (.alias p op pr target id) target with
      | some (next, nextChain) => staticAliasTarget? fuel nextChain next
      | none => none

mutual
  /-- The number of callable aliases in an algorithm tree — the fuel of the static alias chase
      (`staticAliasCycle`): a chase landing on more aliases than the tree holds has revisited one. -/
  partial def Algorithm.aliasCount : Algorithm -> Nat
    | .mk _ _ op pr out _ =>
        (op.map Expr.aliasCount).sum + (pr.map (fun prop => prop.alg.aliasCount)).sum + (out.map Expr.aliasCount).sum
    | .builtin _ => 0
    | .conditional _ op branches _ =>
        (op.map Expr.aliasCount).sum + (branches.map (fun branch => branch.body.aliasCount)).sum
    | .alias _ op pr target _ =>
        1 + (op.map Expr.aliasCount).sum + (pr.map (fun prop => prop.alg.aliasCount)).sum + target.aliasCount

  /-- The callable aliases inside an expression (in its blocks). -/
  partial def Expr.aliasCount : Expr -> Nat
    | .algorithmExpr alg => alg.aliasCount
    | .unary _ operand => operand.aliasCount
    | .binary _ left right => left.aliasCount + right.aliasCount
    | .comparison first links => first.aliasCount + (links.map (fun link => link.operand.aliasCount)).sum
    | .index target selector => target.aliasCount + selector.aliasCount
    | .sequenceConstruct left right => left.aliasCount + right.aliasCount
    | .sequenceSpread operand => operand.aliasCount
    | .listLiteral items => (items.map Expr.aliasCount).sum
    | .capture rows => (rows.map Expr.aliasCount).sum
    | .call fn args => fn.aliasCount + (args.map Expr.aliasCount).sum
    | .dotMember target _ fallback args? =>
        target.aliasCount + fallback.aliasCount + ((args?.getD []).map Expr.aliasCount).sum
    | _ => 0
end

mutual
  /-- Pre-evaluation structural validation over a whole algorithm tree:
      - explicit algorithm parameters only appear on algorithms that define
        output (`explicitParamsRequireOutput`)
      - no parameter pattern or branch pattern contains a one-item sequence
        pattern (the singleton rule; `illegalInEval`
        `singletonSequencePatternMessage`) — a host-built tree cannot give such
        a pattern a meaning the surface language refuses it
      - no parameter-pattern level holds more than one collecting capture (X-02;
        `illegalInEval` `multipleCollectingBindingsPerLevelMessage`): the
        binders allocate a level around ONE movable collector, so a host-built
        tree cannot reach them with a second one
      - conditional algorithms have uniform top-level branch pattern arity and
        uniform top-level branch output arity (`branchArityMismatch`,
        `branchOutputArityMismatch`)
      - every callable alias has a STATIC-PATH target (`Expr.isStaticAliasPath`;
        `illegalInEval` `aliasTargetNotStaticPathMessage`), and the static chase of
        its target never leads back to an alias already on its chain
        (`staticAliasCycle`; `illegalInEval` `aliasCycleMessage`) — only a host-built
        tree can violate either, the surface pass never forms one

      `name` labels conditional arity diagnostics with the nearest enclosing
      property name; anonymous algorithms report the placeholder
      `conditional`. `chain` is the static scope chain around `a` (outermost
      first) and `aliases` the whole tree's alias count, which the alias check
      reads. C#: `AlgorithmValidation.PreEvaluationValidationWalker`. -/
  partial def validateAlgorithmTree (a : Algorithm) (name : Ident)
      (chain : List Algorithm) (aliases : Nat) : EvalM Unit := do
    -- A loaded module is rooted at the prelude (Q-31 H-P): the static chain its aliases
    -- resolve in restarts at the module, whatever holds it.
    let chain := if a.isModuleRoot then [] else chain
    if a.hasSingletonSequencePattern then
      .error (Error.illegalInEval singletonSequencePatternMessage)
    if a.hasMultipleCollectingCaptures then
      .error (Error.illegalInEval multipleCollectingBindingsPerLevelMessage)
    let inner := chain ++ [a]
    match a with
    | .mk _ parameters op pr out _ =>
        if !parameters.isEmpty && out.isEmpty then
          .error Error.explicitParamsRequireOutput
        for openExpr in op do
          validateExprTree openExpr inner aliases
        for prop in pr do
          validateAlgorithmTree prop.alg prop.name inner aliases
        for expr in out do
          validateExprTree expr inner aliases
    | .builtin _ => pure ()
    | .conditional _ op branches _ =>
        validateConditionalBranchArities name a
        for openExpr in op do
          validateExprTree openExpr inner aliases
        for branch in branches do
          validateAlgorithmTree branch.body name inner aliases
    | .alias _ op pr target _ =>
        if !target.isStaticAliasPath then
          .error (Error.illegalInEval (aliasTargetNotStaticPathMessage (openExprName target)))
        if staticAliasCycle aliases chain a then
          .error (Error.illegalInEval aliasCycleMessage)
        for openExpr in op do
          validateExprTree openExpr inner aliases
        for prop in pr do
          validateAlgorithmTree prop.alg prop.name inner aliases
        validateExprTree target inner aliases

  /-- Traverse expressions so nested block literals and call-argument
      algorithms also satisfy the same pre-evaluation invariants. -/
  partial def validateExprTree (e : Expr) (chain : List Algorithm) (aliases : Nat) : EvalM Unit :=
    match e with
    | .param _ => pure ()
    | .num _ => pure ()
    | .stringLiteral _ => pure ()
    | .boolLiteral _ => pure ()
    | .resolve _ => pure ()
    | .unary _ operand =>
        validateExprTree operand chain aliases
    | .binary _ left right => do
        validateExprTree left chain aliases
        validateExprTree right chain aliases
    | .comparison first links => do
        validateExprTree first chain aliases
        links.forM (fun link => validateExprTree link.operand chain aliases)
    | .index target selector => do
        validateExprTree target chain aliases
        validateExprTree selector chain aliases
    | .sequenceConstruct left right => do
      validateExprTree left chain aliases
      validateExprTree right chain aliases
    | .emptySequence _ => pure ()
    | .sequenceSpread operand => do
        validateExprTree operand chain aliases
    | .listLiteral items =>
        items.forM (fun item => validateExprTree item chain aliases)
    | .algorithmExpr alg =>
        validateAlgorithmTree alg "conditional" chain aliases
    | .capture rows =>
        rows.forM (fun row => validateExprTree row chain aliases)
    | .call fn args => do
        validateExprTree fn chain aliases
        args.forM (fun arg => validateExprTree arg chain aliases)
    | .dotMember target _ fallback args? => do
        validateExprTree target chain aliases
        -- The stored lexical fallback is a real child (Resolve/Param for
        -- front-end trees, but hand-built trees could hide algorithms in it),
        -- so the validation walk covers it like every other reference.
        validateExprTree fallback chain aliases
        match args? with
        | some args => args.forM (fun arg => validateExprTree arg chain aliases)
        | none => pure ()
end

/-- The pre-evaluation validation of one algorithm tree (`validateAlgorithmTree` over the
    whole tree, its alias count read once). -/
def validateExplicitParamOutputInvariant (a : Algorithm) (name : Ident := "conditional") : EvalM Unit :=
  validateAlgorithmTree a name [] a.aliasCount

/-- The pre-evaluation validation of a program expression (`validateExprTree`). -/
def validateExplicitParamOutputInvariantExpr (e : Expr) : EvalM Unit :=
  validateExprTree e [] e.aliasCount

namespace ScopeCtx
  def parent : ScopeCtx -> Option ScopeCtx
    | .mk p _ _ _ _ _ _ _ => p
  def params : ScopeCtx -> List Ident
    | .mk _ ps _ _ _ _ _ _ => ps
  def opens : ScopeCtx -> List Expr
    | .mk _ _ op _ _ _ _ _ => op
  def props : ScopeCtx -> List PropDef
    | .mk _ _ _ ps _ _ _ _ => ps
  /-- The owning output rows, retained for scope reconstruction. Runtime declaration IDs
      distinguish owners even when these rows (or clause binders) have the same shape. -/
  def output : ScopeCtx -> List Expr
    | .mk _ _ _ _ out _ _ _ => out
  def activation : ScopeCtx -> Option Nat
    | .mk _ _ _ _ _ _ value _ => value
  def withActivation (value : Nat) : ScopeCtx -> ScopeCtx
    | .mk p ps op props out branches _ id => .mk p ps op props out branches (some value) id
  partial def declaration : ScopeCtx -> ScopeCtx
    | .mk p ps op props out branches _ id =>
        .mk (p.map declaration) ps op props out branches none id
  def ancestor? (scope : ScopeCtx) : Nat -> Option ScopeCtx
    | 0 => some scope
    | n + 1 => scope.parent >>= fun p => ancestor? p n
  def declarationId : ScopeCtx -> Option PropertyIdentity
    | .mk _ _ _ _ _ _ _ id => id
end ScopeCtx

namespace Algorithm
  /-- Create a temporary algorithm from a ScopeCtx for open resolution. -/
  def forOpens (sc : ScopeCtx) : Algorithm :=
    .mk (some sc) [] (ScopeCtx.opens sc) [] []

  /-- Whether an algorithm needs a call to have members: a parameterized algorithm
      (explicit or inferred parameters), a clause family (whose branches always take
      arguments), or a callable alias (it denotes its target's CALLABLE, never a
      namespace: an alias declares none of its target's members). Such an algorithm is
      not an `open` provider — `open` imports a namespace and never creates an
      activation, so there is no value its members could read their inputs from
      (C#: `Evaluator.RequiresArguments`). -/
  def requiresArguments : Algorithm -> Bool
    | .conditional _ _ _ _ => true
    | .alias _ _ _ _ _ => true
    | a => !(params a).isEmpty

  /-- Lift a single expression into an algorithm whose output is that expression. -/
  def ofExpr (e : Expr) : Algorithm :=
    Algorithm.mk none [] [] [] [e]  -- no params, no opens, no properties
end Algorithm

--------------------------------------------------------------------------------
-- Lexical lookup (direct parents only)
--------------------------------------------------------------------------------

partial def lookupInParentsDirect (sc : ScopeCtx) (name : Ident) : Option Algorithm :=
  match lookupPropAny (ScopeCtx.props sc) name with
  | some child => some (Algorithm.withParent (some sc) child)
  | none =>
      match ScopeCtx.parent sc with
      | some sc' => lookupInParentsDirect sc' name
      | none     => none

/-- Direct lexical lookup: local + parent chain only (no opens).
    Used to resolve open expressions safely (avoids cycles). -/
partial def lookupLexicalDirect (a : Algorithm) (name : Ident) : Option Algorithm :=
  match Algorithm.lookupProp a name with
  | some child => some (Algorithm.childOf a child)
  | none =>
    match Algorithm.parent a with
    | some sc => lookupInParentsDirect sc name
    | none    => none

--------------------------------------------------------------------------------
-- Member accessibility (the local-only law)
--------------------------------------------------------------------------------

/-- The scope owning parameter `name` as seen from `scope`: the nearest level, that scope
    itself first, whose parameters bind the name — the same nearest-owner walk that
    elaborated the captured reference (C#: `Evaluator.RequiredParameterOwner`). -/
partial def requiredParameterOwner? (scope : ScopeCtx) (name : Ident) : Option ScopeCtx :=
  if (ScopeCtx.params scope).contains name then some scope
  else
    match ScopeCtx.parent scope with
    | some parent => requiredParameterOwner? parent name
    | none => none

/- Runtime declaration/activation identity is not an exported-property cache determinant.
    Preserve the established structural cache law (C#: StructuralOwnerIdentity). -/
mutual
  partial def cacheExprShape : Expr -> Expr
    | .param n => .param n
    | .resolve n => .resolve n
    | .num n => .num n
    | .stringLiteral text => .stringLiteral text
    | .boolLiteral b => .boolLiteral b
    | .emptySequence depth => .emptySequence depth
    | .unary op e => .unary op (cacheExprShape e)
    | .binary op a b => .binary op (cacheExprShape a) (cacheExprShape b)
    | .comparison first links =>
        .comparison (cacheExprShape first)
          (links.map (fun link => { link with operand := cacheExprShape link.operand }))
    | .index a b => .index (cacheExprShape a) (cacheExprShape b)
    | .sequenceConstruct a b => .sequenceConstruct (cacheExprShape a) (cacheExprShape b)
    | .sequenceSpread e => .sequenceSpread (cacheExprShape e)
    | .listLiteral es => .listLiteral (es.map cacheExprShape)
    | .capture es => .capture (es.map cacheExprShape)
    | .algorithmExpr a => .algorithmExpr (cacheAlgorithmShape a)
    | .call f args => .call (cacheExprShape f) (args.map cacheExprShape)
    | .dotMember target name fallback args => .dotMember (cacheExprShape target) name
        (cacheExprShape fallback) (args.map (List.map cacheExprShape))

  partial def cacheAlgorithmShape : Algorithm -> Algorithm
    | .builtin b => .builtin b
    | .mk parent parameters opens props output _ =>
        .mk (parent.map cacheScopeShape) parameters (opens.map cacheExprShape)
          (props.map cachePropertyShape) (output.map cacheExprShape)
    | .conditional parent opens branches _ =>
        .conditional (parent.map cacheScopeShape) (opens.map cacheExprShape)
          (branches.map fun b => { b with body := cacheAlgorithmShape b.body })
    | .alias parent opens props target _ =>
        .alias (parent.map cacheScopeShape) (opens.map cacheExprShape)
          (props.map cachePropertyShape) (cacheExprShape target)

  partial def cacheScopeShape : ScopeCtx -> ScopeCtx
    | .mk parent _ opens props _ _ _ _ =>
        .mk (parent.map cacheScopeShape) [] (opens.map cacheExprShape)
          (props.map cachePropertyShape) [] [] none none

  partial def cachePropertyShape (p : PropDef) : PropDef :=
    { p with alg := cacheAlgorithmShape p.alg }
end

/-- Known declaration identities compare only the binder view and parent chain. Walking
    or printing their complete property/output graphs at every lookup is unnecessary. -/
partial def sameDeclaringScope (left right : ScopeCtx) : Bool :=
  match left.declarationId, right.declarationId with
  | some a, some b => a == b && left.params == right.params &&
      match left.parent, right.parent with
      | none, none => true
      | some p, some q => sameDeclaringScope p q
      | _, _ => false
  | _, _ => reprStr left.declaration == reprStr right.declaration

partial def compatibleActivations (required actual : Option ScopeCtx) : Bool :=
  match required, actual with
  | none, none => true
  | some r, some a =>
      (r.activation.isNone || r.activation == a.activation) && compatibleActivations r.parent a.parent
  | _, _ => false

def siteScope? (ctx : EvalCtx) : Option ScopeCtx :=
  ctx.headScope.orElse (fun _ => ctx.head?.map Algorithm.asScopeCtx)

partial def activeDeclaration? (required : ScopeCtx) (level : Option ScopeCtx) : Option ScopeCtx :=
  match level with
  | none => none
  | some scope =>
      if sameDeclaringScope required scope && compatibleActivations (some required) (some scope)
      then some scope else activeDeclaration? required scope.parent

def scopeInContext (a : Algorithm) (ctx : EvalCtx) : ScopeCtx :=
  let scope := a.asScopeCtx
  if scope.activation.isSome then scope
  else (activeDeclaration? scope (siteScope? ctx)).getD scope

def childOfInContext (parent child : Algorithm) (ctx : EvalCtx) : Algorithm :=
  child.withParent (some (scopeInContext parent ctx))

partial def scopeChainContains (level : Option ScopeCtx) (owner : ScopeCtx) : Bool :=
  match level with
  | none => false
  | some scope =>
      (sameDeclaringScope scope owner && scope.activation.isSome &&
        compatibleActivations (some owner) (some scope)) ||
      scopeChainContains scope.parent owner

def lexicalChainContains (ctx : EvalCtx) (owner : ScopeCtx) : Bool :=
  scopeChainContains (siteScope? ctx) owner

def recordParameterActivation (names : List Ident) (ctx : EvalCtx) (env : ValEnv) : EvalM Nat := do
  let state <- get
  let id := state.lexicalActivations.size
  let activation : ParameterActivation := {
    values := env.filter (fun b => names.contains b.fst)
    needs := ctx.needEnv.filter (fun b => names.contains b.fst)
    algorithms := ctx.algEnv.filter (fun b => names.contains b.fst)
    counted := ctx.countedParamEnv.filter (fun b => names.contains b.fst)
    bindingContext := ctx.bindingContext }
  set { state with
    lexicalActivations := state.lexicalActivations.push activation }
  pure id

def enterAlgorithmBody (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM EvalCtx := do
  if a.params.isEmpty && a.props.all (fun p => p.exposure.isExported) then pure (ctx.push a)
  else
    let id <- recordParameterActivation a.params ctx env
    pure { ctx.push a with headScope := some (a.asScopeCtx.withActivation id) }

def capturedParameterActivation? (name : Ident) (ctx : EvalCtx) : EvalM (Option ParameterActivation) := do
  match ctx.head?, siteScope? ctx with
  | some site, some scope =>
      if site.params.contains name then pure none
      else
        let id := scope.parent >>= fun parent =>
          (requiredParameterOwner? parent name).bind ScopeCtx.activation
        match id with
        | none => pure none
        | some id => pure ((<- get).lexicalActivations[id]?)
  | _, _ => pure none

def parameterContext (name : Ident) (ctx : EvalCtx) (env : ValEnv) : EvalM (EvalCtx × ValEnv) := do
  match <- capturedParameterActivation? name ctx with
  | none => pure (ctx, env)
  | some activation =>
      let parameterCtx := { ctx with needEnv := activation.needs, algEnv := activation.algorithms, countedParamEnv := activation.counted }
      pure (parameterCtx, activation.values)

def supplyNeed (source : Expr) (caller : EvalCtx) (values : ValEnv) : EvalM Nat := do
  if let .param name := source then
    let activation <- capturedParameterActivation? name caller
    if let some address := lookupAssoc name (activation.map ParameterActivation.needs |>.getD caller.needEnv) then
      return address
  allocateNeed (.expression source caller values)

/-- The failure recorded on a parameter's algorithm binding as its VALUE
    outcome (`AlgBinding.valueFailure?`), read in the parameter's own binding
    context exactly as the `.param` arm of `evalCounted` reads that tier:
    `none` when the parameter has a value (a value binding always wins, as in
    that read) or no failed algorithm-channel binding. Under Model C no
    production path records such a failure — a parameter's outcome is its
    need cell's (`demandNeed`), and the eager writer survives only in
    `HistoricalReadyBinding.lean` — so for every source program this is
    `none`. C#: `Evaluator.ParameterValueFailure`. -/
def parameterValueFailure? (name : Ident) (ctx : EvalCtx) (env : ValEnv) : EvalM (Option Error) := do
  let (parameterCtx, values) <- parameterContext name ctx env
  if (parameterCtx.countedParamEnv.lookup name).isSome || (values.lookup name).isSome then
    pure none
  else
    pure ((parameterCtx.algEnv.lookupBinding name).bind AlgBinding.valueFailure?)

/-- A builtin value boundary reads a parameter's established failure before
    classifying its independent callable channel. This never evaluates a body.
    C#: the expression overload of `ParameterValueFailure`. -/
def argumentParameterValueFailure? (source? : Option Expr) (ctx : EvalCtx)
    (env : ValEnv) : EvalM (Option Error) :=
  match source? with
  | some (.param name) => parameterValueFailure? name ctx env
  | _ => pure none

/-- THE member-accessibility law, applied AFTER a member has been selected — by structural
    dot access (`evalDotCallCounted`, `resolveDotReceiver`), by a dotted `open` path step
    (`resolveAlgForOpen`), and by an `open`-provided name (`lookupOpenProperties`); direct
    lexical hits never consult it, because a name found on the site's own chain is by
    construction inside every owner of what it captures.

    An exported member is accessible everywhere. Captured requirements retain exact owner
    positions across shadowing; names alone use the legacy nearest-owner host convention.
    Each owner must be the same declaration and activation in the site's lexical chain,
    including captured ancestors of a static provider. Reads use that owner's snapshot
    rather than a shadowing dynamic binding. An absent owner refuses the access.
    `.localConditional` is never assigned to a `PropDef`; declared by a host, it is
    inaccessible. C#: `Evaluator.IsAccessibleFrom`. -/
def memberAccessible? (ctx : EvalCtx) (container : Algorithm) (p : PropDef) : Bool :=
  match p.exposure with
  | .exported => true
  | .localConditional => false
  | .localCapturedAncestorParams required =>
      match siteScope? ctx with
      | none => false
      | some _ =>
          let declaringScope := scopeInContext container ctx
          match p.requiredOwnerDepths with
          | some requirements => requirements.all fun (name, depth) =>
              match depth >>= declaringScope.ancestor? with
              | some owner => owner.params.contains name && lexicalChainContains ctx owner
              | none => false
          | none => required.all fun name =>
              match requiredParameterOwner? declaringScope name with
              | some owner => lexicalChainContains ctx owner
              | none => false


def wireToCaller (ctx : EvalCtx) (a : Algorithm) : Algorithm :=
  match ctx.callStack.head? with
  | some caller => childOfInContext caller a ctx
  | none        => a

/-- Wires a selected branch body under its clause family for one call, publishing the
    matched pattern binders as the family scope's `params`: the body itself declares no
    parameters (binders bind by pattern matching), so this is the level at which
    `memberAccessible?` finds the owner of a binder-capturing member.
    C#: `Evaluator.ChildOfConditionalCall`. -/
def wireSelectedBranchBody (callee : Algorithm) (body : Algorithm) (binderNames : List Ident)
    (ctx : EvalCtx) (env : ValEnv) : EvalM Algorithm := do
  let id <- recordParameterActivation binderNames ctx env
  pure (body.withParent (some (.mk callee.parent binderNames callee.opens callee.props
    callee.output callee.branches (some id) callee.declarationId)))

def wireOpenBlockToGlobalScope (ctx : EvalCtx) (a : Algorithm) : Algorithm :=
  match Algorithm.parent a, ctx.callStack.reverse.head? with
  | none, some globalScope => Algorithm.childOf globalScope a
  | _, _ => a

-- Dot-call helpers
--------------------------------------------------------------------------------

/-- Convert a numeric Result to its canonical string representation.
    Only atomic numeric values are supported; other forms raise typeMismatch.
    Canonical representation: Int.repr (e.g., 123 → "123", -5 → "-5", 0 → "0"). -/
def resultToString (r : Result) : EvalM Result :=
  match r with
  | .atom n => pure (Result.str (toString n))
  | _ => .error (Error.typeMismatch "builtin property `string` expects a numeric receiver")

--------------------------------------------------------------------------------
-- Semantics
--------------------------------------------------------------------------------

partial def resultDiagnosticString : Result -> String
  | .atom value => toString value
  | .str value => "'" ++ value ++ "'"
  | .bool value => Result.boolText value
  | .sequenceValue items => "(" ++ String.intercalate ", " (items.map resultDiagnosticString) ++ ")"
  | .listValue items => "[" ++ String.intercalate ", " (items.map resultDiagnosticString) ++ "]"

/-- How a diagnostic names one value that failed an operand, condition, or
    predicate requirement: the value KIND first, then the value itself.
    C#: `Evaluator.DescribeOperand`. -/
def operandDescription : Result -> String
  | .sequenceValue items => s!"a sequence value with {items.length} sequence element{if items.length = 1 then "" else "s"}: {resultDiagnosticString (.sequenceValue items)}"
  | .str value => "a string: '" ++ value ++ "'"
  | .bool value => s!"a Boolean value: {Result.boolText value}"
  | .atom value => s!"numeric value {value}"
  | .listValue items => s!"a list value with {items.length} element{if items.length = 1 then "" else "s"}: {resultDiagnosticString (.listValue items)}"

/-- Coerce a Result to Int. Every present value that is not a number — a
    string, a Boolean, a sequence (`()` included) or a list — is the value-KIND
    failure `typeMismatch` (Q-27): a selector, a `range` bound, a `repeat`
    count and a Math argument of the wrong kind are never an arity error.
    C#: `Evaluator.ExpectInt`. -/
def expectInt (r : Result) : EvalM Int :=
  match r with
  | .str _ => .error (Error.typeMismatch "Expected a number, got a string")
  | .bool _ => .error (Error.typeMismatch "Expected a number, got a Boolean value")
  | _ => match Result.asInt? r with
    | some n => pure n
    | none   => .error (Error.typeMismatch s!"Expected a number, got {operandDescription r}")

/-- An ordinary structural pattern that received a value of another kind —
    a sequence pattern given a list or a scalar, a list pattern given a
    sequence or a scalar — fails its binding with this `typeMismatch`, naming
    the written pattern and the value received (STRUCTURAL PATTERN DELIMITERS
    SELECT THE VALUE KIND THEY DESTRUCTURE). A right-kind value with the wrong
    number of elements is the group's ordinary `arityMismatch` instead. In a
    clause family neither is raised: a mismatch only rejects the clause.
    C#: `Evaluator.StructuralPatternKindMismatch`. -/
def structuralPatternKindMismatch (pattern : ParameterPattern) (value : Result) : Error :=
  match pattern with
  | .listValue _ =>
      Error.typeMismatch
        s!"list pattern `{pattern.displayName}` expects a list value, but received {operandDescription value}"
  | _ =>
      Error.typeMismatch
        s!"sequence pattern `{pattern.displayName}` expects a sequence value, but received {operandDescription value}"

/-- The numeric-scalar operand rule of the arithmetic operators and the ordering
    comparisons, keyed by the operator's spelling. C#: `Evaluator.RequireNumericScalarOperand`. -/
def requireNumericScalarOperandOf (operatorSymbol : String) (side : String) (value : Result) : EvalM Int :=
  match Result.asInt? value with
  | some number => pure number
  | none => .error (Error.typeMismatch
      s!"operator `{operatorSymbol}` expects numeric scalar operands, but the {side} operand was {operandDescription value}")

def requireNumericScalarOperand (op : BinaryOp) (side : String) (value : Result) : EvalM Int :=
  requireNumericScalarOperandOf op.symbol side value

/-- The ordering comparisons share the arithmetic operators' numeric-scalar operand rule. -/
def requireNumericComparisonOperand (op : ComparisonOp) (side : String) (value : Result) : EvalM Int :=
  requireNumericScalarOperandOf op.symbol side value

/-- The logical operators `and` / `or` / `xor` require a Boolean value on
    BOTH sides: there is no numeric truthiness, so a number, string, sequence
    value, or list operand is a value-kind error naming the operand.
    C#: `Evaluator.RequireBooleanOperand`. -/
def requireBooleanOperand (op : BinaryOp) (side : String) (value : Result) : EvalM Bool :=
  match Result.asBool? value with
  | some b => pure b
  | none => .error (Error.typeMismatch
      s!"operator `{op.symbol}` expects Boolean operands, but the {side} operand was {operandDescription value}")

/-- The ONE message for every position that REQUIRES a Boolean value — an
    `if` condition, a `filter` predicate result, a `while` continuation flag:
    it names the role and the value kind actually supplied, so a number in a
    predicate position is reported as the value-kind mismatch it is, never as
    an arity or numeric error. C#: `Evaluator.BooleanRequiredMessage`. -/
def booleanRequiredMessage (role : String) (value : Result) : String :=
  s!"{role} must be a Boolean value (true or false), but was {operandDescription value}"

/-- Structural KatLang value equality used by `==` and `!=`.
    Numbers compare by value, strings by exact value, and sequence values by
    length plus recursive pairwise equality — exactly the derived structural
    `BEq` on `Result`. Different value kinds compare unequal rather than raising
    a type mismatch, so equality is total over all values and never type-errors.
    Ordering operators and arithmetic keep their numeric-scalar-only path via
    `requireNumericScalarOperand`. -/
def resultValueEq (a b : Result) : Bool := a == b

/-- Enumerate the inclusive integer span for `range(start, stop)`.
    The direction is inferred automatically:
    - ascending when `start <= stop`
    - descending when `start > stop`

    Because KatLang's Lean core represents numeric values as `Int`, the
    `range` builtin is integer-only by construction at the specification level. -/
def inclusiveRange (start stop : Int) : List Int :=
  if start <= stop then
    (List.range (Int.toNat (stop - start + 1))).map (fun i => start + Int.ofNat i)
  else
    (List.range (Int.toNat (start - stop + 1))).map (fun i => start - Int.ofNat i)

/-- Insert an integer into an ascending sorted list, preserving duplicates. -/
def insertIntAsc (value : Int) : List Int -> List Int
  | [] => [value]
  | head :: tail =>
      if value <= head then
        value :: head :: tail
      else
        head :: insertIntAsc value tail

/-- Ascending numeric sort used by `order` and `orderDesc`. -/
def sortIntsAsc : List Int -> List Int
  | [] => []
  | head :: tail => insertIntAsc head (sortIntsAsc tail)

/-- Descending numeric sort used by `orderDesc`. -/
def sortIntsDesc (xs : List Int) : List Int :=
  (sortIntsAsc xs).reverse

structure CallableCallItem where
  need? : Option Nat := none
  value? : Option Result := none
  algorithm? : Option Algorithm := none
  error? : Option Error := none
  skipMissingValue : Bool := false
  source? : Option Expr := none
  /-- The named binding's ALGORITHM-channel identity (a parameter's or a
      property reference's), carried beside the value-side `algorithm?`
      (`ResolvedArgumentAlgorithm.callable?`). -/
  callable? : Option Algorithm := none
  deriving Repr

/-- The algorithm a call item NAMES (`ResolvedArgumentAlgorithm.invoked`): the
    identity the zero-argument value-demand law judges, while a VALUE demand
    evaluates the value-side `algorithm?`. -/
def CallableCallItem.named? (item : CallableCallItem) : Option Algorithm :=
  item.callable?.or item.algorithm?

/-- The context of NEED-04's value verdict: the occurrences of one repeated
    parameter name received unequal VALUE contributions (the binder's
    `badArity`, unchanged by Q-27). C#: `Evaluator.RepeatedParameterContext`. -/
def repeatedParameterContext (name : Ident) : String :=
  s!"repeated parameter '{name}' requires equal arguments"

/-- Callable identity includes its declaration and the captured lexical activation chain.
    Comparing identities does not evaluate either algorithm or consult its value cache. -/
def sameRepeatedCallableIdentity (left right : Algorithm) : Bool :=
  match left, right with
  | .builtin a, .builtin b => a == b
  | .builtin _, _ | _, .builtin _ => false
  | _, _ =>
      left.declarationId == right.declarationId &&
      (match left.parent, right.parent with
       | none, none => true
       | some a, some b => sameDeclaringScope a b
       | _, _ => false) &&
      compatibleActivations left.parent right.parent &&
      compatibleActivations right.parent left.parent

/-- Builtin collection-item view of the bound collection argument: opens
  exactly one outer sequence or exact-list boundary to its immediate items;
  any other value supplies itself as one item (a scalar is a one-element
  collection). Never recursive — nested sequence values and nested list
  values stay intact as single items.
  Applied strictly AFTER ordinary fixed parameter binding, to the already
  bound `collection` parameter only — argument boundaries are never altered
  before binding. Call parameter binding never uses this view, assignment
  deconstruction opens its received value through the spread view
  (`Result.spreadItems`), and a structural pattern opens only its own kind.
  C#: `BuiltinCollectionItems`. -/
def builtinCollectionItems : Result -> List Result
  | .sequenceValue elems => elems
  | .listValue elems => elems
  | value => [value]

/-- Compatibility fallback for manually constructed core conditionals.
  Surface clause elaboration should already route eligible single-branch
  ordinary clause groups through `Algorithm.elaborateClauseGroup`, producing
  `Algorithm.mk` directly. This helper intentionally keeps only the stricter
  flat multi-binder `.conditional` core shape call-compatible with ordinary
  user algorithms, so evaluator fallback semantics do not silently broaden to
  bare single-binder conditionals. -/
def flatBinderUserEquivalent? (callee : Algorithm) : Option Algorithm :=
  match callee with
  | .conditional _ _ [branch] _ =>
      match Pattern.flatBinderParamNames? branch.pattern with
      | some ps =>
          let wiredBody := Algorithm.childOf callee branch.body
          some (Algorithm.mk
            (Algorithm.parent wiredBody)
            (Algorithm.normalParameters ps)
            (Algorithm.opens wiredBody)
            (Algorithm.props wiredBody)
            (Algorithm.output wiredBody))
      | none => none
  | _ => none

/-- ONE zero-supply acceptability rule: whether an ORDINARY call that supplies
    ZERO argument slots can bind this callable. It is derived from the very
    binder/dispatch semantics such a call uses, never from parameter-list
    emptiness:

    * a user algorithm accepts iff its top-level pattern list's
      `ParameterPattern.minimumSuppliedSlots` is zero — so `Only(*xs)` accepts
      (`Only()` binds `xs = []`) while `Head(x, *rest)`, `Tail(*rest, z)`,
      `P((x, *rest))`, `P([x])` and `Pair(x, y)` do not. A COLLECTING parameter
      contributes ZERO required slots; a nested pattern still consumes one, and
      binds ONE supplied value of its own kind, never none;
    * a clause family accepts iff some branch's top-level pattern has arity
      zero — exactly the branch the family dispatcher (`selectNeedFamilyBranch`)
      selects for an empty supply. A flat multi-binder core equivalent
      (`flatBinderUserEquivalent?`) always has at least two parameters, so it
      never accepts;
    * a BUILTIN never accepts (`sum()` is an arity error). Its rejection stays
      owned by `evalBuiltinValueCounted` / `builtinArityError b 0`, which is the
      very report `sum()` produces, so `zeroArgumentDemandError?` deliberately
      does not intercept builtins.

    C#: `Evaluator.AcceptsZeroSuppliedArguments`. -/
def Algorithm.acceptsZeroSuppliedArguments : Algorithm -> Bool
  | .builtin _ => false
  | .conditional _ _ branches _ =>
      branches.any (fun branch => Pattern.topLevelArity branch.pattern == 0)
  | a => ParameterPattern.minimumSuppliedSlots (Algorithm.parameterPatterns a) == 0

/-- Value-position access to a conditional algorithm cannot select a branch,
    so it must fail instead of silently forcing the conditional's empty output
    list. Mirrors the no-argument dot-call dispatch: a flat multi-binder core
    equivalent reports its ordinary call arity, and any other conditional
    reports `noMatchingBranch`. Returns `none` for non-conditional algorithms. -/
def conditionalValueAccessError? (name : String) (a : Algorithm) : Option Error :=
  match a with
  | .conditional _ _ _ _ =>
      match flatBinderUserEquivalent? a with
      | some simple => some (Error.arityMismatch (Algorithm.params simple).length 0)
      | none => some (Error.noMatchingBranch name)
  | _ => none

/-- Attach context to any error raised by `m`. -/
def withCtx (ctx : String) (m : EvalM A) : EvalM A := do
    match <- evalAttempt m with
    | .ok result => pure result
    | .error err => .error (Error.withContext ctx err)

/-- Attach property context specifically to a missing-output failure.
    Other errors are preserved unchanged. -/
def withMissingOutputCtx (ctx : String) (m : EvalM A) : EvalM A := do
    match <- evalAttempt m with
    | .ok result => pure result
    | .error .missingOutput => .error (.withContext ctx .missingOutput)
    | .error err => .error err

def isMissingOutputError : Error -> Bool
  | .missingOutput => true
  | .withContext _ inner => isMissingOutputError inner
  | _ => false

/-- The empty sequence value expression `()`. -/
def emptyResultExpr : Expr :=
  .emptySequence 0

/-- True when a Result is the empty sequence value or a redundant chain of
    one-item sequences ending in it. -/
def isEmptySequenceChain : Result -> Bool
  | .sequenceValue [] => true
  | .sequenceValue [inner] => isEmptySequenceChain inner
  | _ => false

/-- Reify a normalized Result as an expression that evaluates back to the same
    value/shape. Redundant empty-sequence chains reify as canonical `()`; other
    sequence-value results become block expressions. -/
def resultToExpr : Result -> Expr
  | .atom n => .num n
  | .str s => .stringLiteral s
  | .bool b => .boolLiteral b
  | .sequenceValue rs =>
      if isEmptySequenceChain (.sequenceValue rs) then
        .emptySequence 0
      else
        -- A reified sequence value is a capture of its already-evaluated
        -- items — a value boundary, not an algorithm.
        .capture (rs.map resultToExpr)
  -- Exact list values reify as list literals so they round-trip losslessly
  -- (a reified `()` element stays one visible list element).
  | .listValue rs => .listLiteral (rs.map resultToExpr)

/-- Recover the top-level values emitted at one algorithm boundary from a
    counted result.

    A sequence value emitted as a single top-level result stays intact, while a
    multi-output result is expanded back to its top-level items. -/
def countedTopLevelValues : CountedResult -> List Result
  | (_, 0) => []
  | (value, 1) => [value]
  | (value, _) => value.toItems

/-- Combine collected top-level output slots into one value. A single slot is
  returned as-is so useful sequence structure is preserved; multiple slots form
  one sequence value. Unlike `Result.normalize`, this does NOT singleton-collapse
  or recursively renormalize slot values -- slots are already evaluated values. -/
def combineOutputSlots : List Result -> Result
  | [r] => r
  | rs => Result.sequenceValue rs

/-- Materialize a collection-producing builtin's kept/projected items as ONE
    list value. Unlike canonical arity capture (ordinary
    construction via `Result.normalize`, `combineOutputSlots`), the list
    boundary is exact: zero items form `[]`, a
    single kept item forms `[item]` (the one-item collection boundary is NEVER
    erased, so `take(((1, 2), (3, 4)), 1)` yields `[(1, 2)]`), and item
    internals are never renormalized, dropped, or flattened -- nested sequence
    values and nested list values stay exact elements. The emitted count is
    always 1: a list value is one visible value (`Result.valueCount`),
    including the empty list `[]`.
    C#: `MakeCollectionListResult`. -/
def makeCollectionListResult (items : List Result) : CountedResult :=
  (Result.listValue items, 1)

/-- True when an argument's resolved algorithm meaning is genuinely
    callable-shaped: an ordinary call supplying ZERO arguments cannot bind it
    (a builtin, a clause family without a zero-arity branch, or a signature that
    requires a supplied slot). Declaring a parameter does not by itself make a
    callable (Q-03): a zero-parameter property and any callable that accepts zero
    supplied arguments, a collecting-only one included, are VALUES that merely
    resolved through the dual algorithm channel, so the test is the zero-argument
    law's own `acceptsZeroSuppliedArguments` (the rule the surface pass's
    `liftsBareValueReference` also reads). HISTORICAL: only the eager, value-only
    collector of `HistoricalReadyBinding` consults it (its former targeted
    "collects values, but ... is a callable" diagnostic). The production Model-C
    binder never does: a collecting parameter binds a lazy slice of the supplied
    cells, `xs*` re-supplies those cells with their VALUE/CALLABLE channels, and
    reading the collected list demands each element, which reports its own
    zero-argument demand failure (NEED-07/08; VAR-03 as reconciled 2026-10-09).
    The former C# twin `IsFunctionShapedAlgorithm` is deleted. -/
def Algorithm.isFunctionShaped (a : Algorithm) : Bool :=
  !a.acceptsZeroSuppliedArguments

/-- Collect the item segment assigned to a collecting binding as ONE list value.

    KatLang distinguishes three item-supply operations by receiver purpose:

    - `capture : Supply -> Value` — ordinary value/output capture, the
      normalizing boundary `Result.normalize (Result.sequenceValue xs)`
      (singleton erasure applies: `x = 1, 2, 3` is `(1, 2, 3)`, one supplied
      item is itself);
    - `collect : Supply -> ListValue` — THIS operation: a collecting binding (collecting parameter)
      materializes exactly the assigned items as one list
      (`collectSegment [] = []`, `collectSegment [v] = [v]`, never erased);
    - `spread : Value -> Supply` — the spread marker (`Result.spreadItems`), which
      opens one sequence OR list boundary.

    THE EXACT COLLECTOR LAW (September 2026): every collecting binding —
    single collecting parameters, mixed prefix/collecting/suffix parameter
    lists, nested pattern collectors, and deconstruction collecting bindings —
    binds exactly the items allocated to it and never inspects their values —
    since Model C (2026-10-02) as a lazy collector cell over the allocated supply
    cells (`bindNeedLevel`), whose VALUE demand materializes exactly this list
    through `makeCollectionListResult` (`demandNeed`); this helper remains the
    value-level definition the laws state. A collector opens nothing: one written
    argument is one item whatever its value, so `Coll((1, 2))` is
    `[(1, 2)]`, `Coll([1, 2])` is `[[1, 2]]`, `Coll(())` is `[()]`, and
    `Coll([])` is `[[]]` — only the caller's explicit spread turns a value into
    several items (`Coll((1, 2)*)` and `Coll([1, 2]*)` are `[1, 2]`).
    Deconstruction (through the spread view) and nested structural patterns
    (a sequence pattern a sequence value, a list pattern a list value) open
    their one value BEFORE allocation, as explicit structural syntax, and the
    collector then collects the opened items exactly. The round trip
    `Result.spreadItems (collectSegment xs) = xs` is the value-level face of
    collecting-parameter forwarding: `Forward(*items) = Target(items*)`
    re-supplies exactly the collected items — since Model C by transferring the
    collector's own cells, unforced (FWD-01, NEED-07/08) — with no hidden
    raw-supply metadata. A collecting value is one visible value, so its emitted count is
    always 1 (including `[]`). C#: the collector cell `Evaluator.CollectorCell`,
    materializing through `MakeCollectionListResult` (`CollectSegment` and
    `CreateCollectingCapture` were deleted by Model C). -/
def collectSegment (items : List Result) : Result :=
  Result.listValue items

/-- Re-count a counted result at a public property/call/builtin RESULT boundary.

    A property/call boundary always returns ONE value: the body may internally
    produce an item supply of count 0, 1, or many, but the caller observes the
    same structural value with emitted count `Result.valueCount value` (0 for the
    empty sequence value, otherwise 1). A multi-output body therefore becomes one
    sequence value at the boundary; only an explicit caller-site spread `value*`
    re-spreads it (via `Result.spreadItems`, which reads the value, not this count).

    This re-counts without normalizing or rebuilding the value; ordinary value
    construction has already normalized redundant unary empty structure. It is
    applied only to public result boundaries — `map`/`reduce` callback results
    (HO-03, Q-25) and the completed `while`/`repeat` result
    (`loopResultCounted`, Q-26) included — never to internal
    body/root output accumulation (`evalAlgOutputCountedCore`) or a loop step's
    own row supply (`evalAlgOutputSlots`), which must keep their multi-item
    counts. (Collecting parameter storage needs no re-count:
    collecting binding collects one exact list value, so its stored count is already
    1.) Lexical zero-arg property access (`evalCounted .resolve`) and the `if`
    builtin already perform this same re-count inline; this helper generalizes
    it. -/
def reCountValueBoundary (r : CountedResult) : CountedResult :=
  (r.fst, Result.valueCount r.fst)

/-- Build the canonical empty sequence value for an `emptySequence` node.
    Repeated ordinary parentheses around `()` do not create higher-order empty
    sequence values. -/
def buildEmptySequenceValue (_ : Nat) : Result :=
  Result.sequenceValue []

-- No builtin is valid as a bare zero-argument value; every builtin requires a
-- call. (The empty sequence value is written `()`, not a builtin.)
def evalBuiltinValueCounted : Builtin -> EvalM CountedResult
  | b => .error (builtinArityError b 0)

/-- Flatten a `sequenceConstruct` subtree into its ordered leaves without changing
    sequence-value/block values inside those leaves. -/
partial def sequenceConstructLeavesLoop : List Expr -> List Expr -> List Expr
  | [], acc => acc.reverse
  | current :: rest, acc =>
      match current with
      | .sequenceConstruct left right => sequenceConstructLeavesLoop (left :: right :: rest) acc
      | leaf => sequenceConstructLeavesLoop rest (leaf :: acc)

def sequenceConstructLeaves (expr : Expr) : List Expr :=
  sequenceConstructLeavesLoop [expr] []

/-- Peel directly-nested unary sequence spreads down to the innermost operand.
    Used by evaluation together with `peelSequenceSpreadLayers`: stacked
    spread is COMPOSITIONAL (`A**` agrees with `(A*)*`) — each extra written
    layer re-captures the previous layer's item supply into one value
    (`Result.normalize ∘ Result.sequenceValue`, the ordinary expression
    capture) and spreads that captured value, applied iteratively
    (stack-safe for deep `A**` chains, matching the C# evaluator). A
    multi-item supply re-captures as a sequence whose spread restores the
    same items, so extra layers are fixed points there
    (`[[1, 2], [3, 4]]**` supplies the two inner lists unchanged); only a
    LONE structured item singleton-collapses at the capture and lets the
    next layer open one more boundary (`[[7]]**` is `7`, like
    `([[7]]*)*`). This is NOT binary spine flattening: there is no right
    operand, it only unwraps the single-operand chain. -/
partial def peelSequenceSpread : Expr -> Expr
  | .sequenceSpread operand => peelSequenceSpread operand
  | e => e

/-- Peel directly-nested spreads while counting the written layers.
    Returns the innermost non-spread operand and the number of `.sequenceSpread` layers
    (at least 1 when called on a spread node). -/
partial def peelSequenceSpreadLayers : Expr -> Nat -> Expr × Nat
  | .sequenceSpread operand, n => peelSequenceSpreadLayers operand (n + 1)
  | e, n => (e, n)

def describeSequenceItem : Result -> String
  | .atom n => s!"numeric value {n}"
  | .str s => s!"string value {repr s}"
  | .bool b => s!"Boolean value {Result.boolText b}"
  | .sequenceValue [] => "empty sequence value"
  | .sequenceValue _ => "sequence value"
  | .listValue [] => "empty list value"
  | .listValue _ => "list value"

def numericSequenceItemErrorContext (b : Builtin) (index : Nat) (item : Result) : String :=
  s!"{builtinDisplayName b} expects each collection element to be a single numeric value; item {index} was {describeSequenceItem item}"

/-- Shared collected view for current collection-builtin evaluation.
    This is the bound collection argument's post-binding one-level item view;
    nested sequence values stay intact and recursive flattening remains the
    job of `atoms`. -/
structure CollectedSequenceBuiltinInput where
  items : List Result
  deriving Repr

def CollectedSequenceBuiltinInput.totalItemCount
    (input : CollectedSequenceBuiltinInput) : Nat :=
  input.items.length

structure PreparedSequenceBuiltinInput where
  items : List Result
  numericItems? : Option (List Int) := none
  deriving Repr

/-- One bound control argument of a collection builtin. A CALLBACK control
    (`.algorithm`) carries the algorithm channel and the named callable it
    invokes (`callable?`, read through `ResolvedArgumentAlgorithm.invoked`) and
    no value: it was never value-evaluated. A VALUE control carries the value
    its one demand established. -/
inductive PreparedSequenceBuiltinSuffixArg where
  | algorithm (value : Algorithm) (callable? : Option Algorithm := none)
  | needAlgorithm (address : Nat)
  | value (value : Result)
  | wholeNumber (value : Int)
  deriving Repr

structure BoundSequenceBuiltinArguments where
  preparedInput : PreparedSequenceBuiltinInput
  iterationItems : List CountedResult
  suffixArgs : List PreparedSequenceBuiltinSuffixArg
  deriving Repr

structure ResolvedArgumentAlgorithm where
  need? : Option Nat := none
  algorithm : Algorithm
  spreadsSequence : Bool := false
  /-- The written argument expression this algorithm was resolved from: the
      demand-site identity `zeroArgumentDemandError?` reports through when a
      builtin VALUE slot demands the algorithm with zero arguments. `none` for
      value-reified arguments (prepared callback data, expanded spread items,
      dotted receivers), whose algorithms carry no parameters. -/
  source? : Option Expr := none
  /-- An argument that NAMES a binding resolves to its value side (`algorithm`,
      a wrapper that performs the ordinary value read of the written name) and
      keeps the named algorithm here: a parameter bound on BOTH channels (the
      wrapper reads the bound value, so a VALUE slot never re-runs the
      argument's body), a parameter whose argument slot FAILED its one value
      evaluation (the wrapper reports that failure — AT-MOST-ONCE ARGUMENT VALUE
      EVALUATION), and a lexical property reference `A` (the wrapper is the
      ordinary property read `A` — the zero-argument property access with its run
      cache — so a VALUE slot never re-runs the property's body: HOW A PROPERTY
      VALUE IS CONSUMED DOES NOT AFFECT CACHING, and `sum(A)` reads exactly the
      value `A` reads). A slot that INVOKES its argument — a sequence callback or
      a loop step — calls `invoked`, so `Apply(f, xs) = map(xs, f)` applies the
      callable `f` exactly as `map(xs, Cnt)` does even when `Cnt` also satisfies
      a zero-argument value demand; the zero-argument value-demand law and every
      signature classification read `invoked` too, because they judge the named
      callable, not its value wrapper. `none` for every other argument, whose
      `algorithm` already is its algorithm-channel identity. -/
  callable? : Option Algorithm := none
  deriving Repr

/-- The algorithm an argument NAMES: the callable an ALGORITHM slot (a sequence
    callback or a loop step) invokes and the identity the zero-argument
    value-demand law and signature classification judge — a named binding's
    algorithm-channel identity when it has one, otherwise the resolved
    algorithm. VALUE slots read `algorithm`. -/
def ResolvedArgumentAlgorithm.invoked (arg : ResolvedArgumentAlgorithm) : Algorithm :=
  arg.callable?.getD arg.algorithm

def intPow (b : Int) : Nat -> Int
  | 0 => 1
  | n + 1 => b * intPow b n

/-- Negative integer exponents follow the C# reference semantics:
    - `0 ^ negative` is a domain error — the runtime's rule is "a zero base
      rejects ANY exponent below zero, integral or not" (`0 ^ -0.5` and
      `Math.Pow(0, -2.5)` fail exactly like `0 ^ -1`); the Int core can only
      reach the integer instance of that rule and shares its message,
    - bases `1` and `-1` have exact integer reciprocals,
    - any other base yields a fractional reciprocal (for example `2 ^ -1 = 0.5`
      in the decimal runtime), which the Int-valued Lean core cannot represent.

    Instead of silently truncating fractional reciprocals to `0`, the core
    raises an explicit error. This is a documented limitation of the integer
    numeric model, not a behavior the runtime should copy. -/
def negativeIntPow (base exponent : Int) : EvalM Result :=
  if base == 0 then
    .error (Error.illegalInEval "zero cannot be raised to a negative exponent")
  else if base == 1 then
    pure (Result.atom 1)
  else if base == -1 then
    pure (Result.atom (if exponent % 2 == 0 then 1 else -1))
  else
    .error (Error.illegalInEval
      s!"`{base} ^ {exponent}` produces a fractional result, which the integer-valued Lean core cannot represent")

/-- Predicate defining which expression forms are allowed in open position
    **after elaboration**.  Only structural references to libraries are permitted.

    OpenForm is the *post-elaboration* set of permitted open expressions.
    Surface-level `load('url')` calls (represented as `Call(Resolve("load"), ...)`)
    may appear in source open lists, but the load elaboration pass MUST rewrite
    every such call into `Expr.algorithmExpr` before open resolution or validation runs.

    Note: the C# parser produces DotCall for all dot syntax (e.g. `Lib.Sub`).
    `DotCall(obj, name, none)` is the canonical form for open dot paths.
    `DotCall(obj, name, some args)` is rejected as an invalid open form.
    After normalization and load elaboration, opens contain only the forms
    listed below.

    Additionally, the exact-syntax sugar `open 'url'` is desugared to
    `open load('url')` at parse time, so raw string literals never appear
    in the canonical open list.  The load elaboration pass then rewrites
    `Call(Resolve("load"), ...)` into `Block(parsed module)` as usual.

    Open target semantics here accept INDIVIDUAL targets only: block,
    resolve, and argumentless dot-call.  The C# parser parses the
    source-level open declaration as one comma-separated target list
    (`open A, B, C`) and validates each target as an individual
    Lean-compatible form before evaluation; `;`/adjacency are not open
    separators.  Spread is not a valid open target: a spread-marked
    target (`open A*`) parses to a spread expression and is rejected by
    open-form validation, so no accepted SequenceSpread ever reaches open
    resolution. -/
inductive OpenForm where
  | algorithmExpr : Algorithm -> OpenForm
  | resolve : Ident -> OpenForm
  | dotCall : Expr -> Ident -> OpenForm     -- a.f (no-arg dotCall)

def Expr.openForm? : Expr -> Option OpenForm
  | .algorithmExpr a => some (.algorithmExpr a)
  -- A capture is a value boundary, not algorithm/namespace identity, so a
  -- surviving capture (`open (M, N)`, `open (M*)`) is NOT an open form: it is
  -- rejected by open-form validation with badOpenForm, exactly like a
  -- spread-marked target. (A redundant group is no capture: the C# parser
  -- erases it, so `open (M)` IS `open M`.)
  | .resolve n       => some (.resolve n)
  -- Only argumentless dot paths are open forms. The C# front end rejects a
  -- Grace-marked open target such as `open A~.B` before Lean encoding; valid
  -- graced dot sources otherwise encode as the same dotMember as ordinary dot.
  -- This classifies the OUTER node; `resolveAlgForOpen` recurses through the
  -- receiver, so a path whose head is no open form (`open 5.N`) is rejected
  -- there. The C# front end refuses such a head statically (`BadOpenForm`).
  | .dotMember o n _ none => some (.dotCall o n)
  | _                => none          -- capture, argument-bearing dot forms, call, and all other forms are rejected

def Expr.isOpenForm (e : Expr) : Bool :=
  (Expr.openForm? e).isSome

/-- Diagnostic expression names use KatLang source syntax; `.index` renders as
  `target:selector`, never `target[selector]` (`[...]` is exact list literal
  syntax). Indexing is postfix and binds tighter than unary and every binary
  operator, so those operands need parentheses in target position: `-A:0` reads
  as `-(A:0)`, so the target of an index over a unary must render `(-A):0`.
  Postfix targets are left-associative and render faithfully bare (`A:0:1`).
  C#: `Evaluator.OpenExprIndexTargetName`. -/
def indexTargetNeedsParens : Expr -> Bool
  | .unary _ _    => true
  | .binary _ _ _ => true
  | .comparison _ _ => true
  | .num v       => decide (v < 0)
  | _             => false

/-- The index selector is a primary in source syntax, so any form that would
  continue the postfix chain rebinds to the target instead (`A:B.C` reads as
  `(A:B).C`, `A:B:C` as `(A:B):C`, while `A:f(0)` leaves an
  unseparated same-line group after `A:f` and is rejected), and a bare negative
  literal (`A:-1`) is not selector syntax at all.
  C#: `Evaluator.OpenExprIndexSelectorName`. -/
def indexSelectorNeedsParens : Expr -> Bool
  | .unary _ _      => true
  | .binary _ _ _   => true
  | .comparison _ _ => true
  | .call _ _       => true
  | .dotMember _ _ _ _ => true
  | .index _ _      => true
  | .sequenceSpread _ => true
  | .num v          => decide (v < 0)
  | _               => false

/-- Precedence tiers of the diagnostic-name renderer — the ONE parenthesization
  rule: a rendered name must read back as the AST it was rendered from, so an
  operand is parenthesized exactly when it binds LOOSER than the position it is
  written in. The tiers mirror the surface parser's ladder (loosest to
  tightest): `or` < `xor` < `and` < prefix `not` < the one comparison tier
  (`< > <= >= == !=`) < additive < multiplicative < prefix `-` < `^` < postfix.
  C#: `ExprNameRenderer.BindingTier` and the slot tiers below. -/
def orTier : Nat := 1
def xorTier : Nat := 2
def andTier : Nat := 3
def notTier : Nat := 4
def comparisonTier : Nat := 5
def additiveTier : Nat := 6
def multiplicativeTier : Nat := 7
def unaryMinusTier : Nat := 8
def powerTier : Nat := 9
def postfixTier : Nat := 10
def atomTier : Nat := 11

def binaryOperatorTier : BinaryOp -> Nat
  | .or => orTier
  | .xor => xorTier
  | .and => andTier
  | .add | .sub => additiveTier
  | .mul | .div | .idiv | .mod => multiplicativeTier
  | .pow => powerTier

/-- How tightly an expression binds when rendered bare. Prefix forms take their
  operator's tier (a negative literal renders with a leading minus, so it reads
  back as a prefix minus); postfix forms and the self-delimiting spellings
  (leaves, captures, lists, blocks, the parenthesized internal join) never
  rebind. C#: `ExprNameRenderer.BindingTier`. -/
def bindingTier : Expr -> Nat
  | .binary op _ _ => binaryOperatorTier op
  | .comparison _ [] => atomTier
  | .comparison _ _ => comparisonTier
  | .unary .not _ => notTier
  | .unary .minus _ => unaryMinusTier
  | .num v => if v < 0 then unaryMinusTier else atomTier
  | .index _ _ | .dotMember _ _ _ _ | .call _ _ | .sequenceSpread _ => postfixTier
  | _ => atomTier

/-- The tier a binary operator's LEFT operand is written at: the operator's own
  tier for the left-associative operators (an equal-tier left operand reads back
  unchanged), the postfix tier for `^`, whose base is postfix-level — a unary
  base or a negative literal must keep its parentheses, or `-a ^ b` would read
  back as `-(a ^ b)`, and `(a ^ b) ^ c` would read back right-associated.
  C#: `ExprNameRenderer.LeftOperandTier`. -/
def leftOperandTier (op : BinaryOp) : Nat :=
  match op with
  | .pow => postfixTier
  | _ => binaryOperatorTier op

/-- The tier a binary operator's RIGHT operand is written at: one above the
  operator for the left-associative operators (`a - (b - c)` keeps its
  parentheses), the unary tier for `^`, whose exponent re-enters the unary
  level (`a ^ -b` and `a ^ b ^ c` read back with the same AST).
  C#: `ExprNameRenderer.RightOperandTier`. -/
def rightOperandTier (op : BinaryOp) : Nat :=
  match op with
  | .pow => unaryMinusTier
  | _ => binaryOperatorTier op + 1

/-- A chain operand is written at the additive tier: a nested chain (`(a < b) == c`
  is not the chain `a < b == c`), a `not`, and the logical operators keep their
  parentheses; arithmetic, powers, prefix minus, and postfix forms read back bare.
  C#: `ExprNameRenderer.PushComparisonOperand`. -/
def comparisonOperandTier : Nat := additiveTier

/-- The tier a prefix operator's operand is written at: a `not` operand keeps its
  parentheses only when it binds looser than `not` (`not (a and b)`; a comparison
  chain reads back bare — `not a < b` IS `not (a < b)`), a minus operand when it
  binds no tighter than the prefix tier itself (`-(a + b)`, `-(a < b)`, `-(not a)`,
  `-(-a)`; a power reads back bare — `-a ^ b` IS `-(a ^ b)`).
  C#: `ExprNameRenderer.PushDiagnosticUnaryOperand`. -/
def unaryOperandTier : UnaryOp -> Nat
  | .not => notTier
  | .minus => unaryMinusTier + 1

def parenthesizeWhenLooser (slotTier : Nat) (operand : Expr) (name : String) : String :=
  if bindingTier operand < slotTier then "(" ++ name ++ ")" else name

/-- The diagnostic expression name (C#: `ExprNameMode.DiagnosticName`). Operators
  render bare, and every operand keeps parentheses exactly where the precedence
  ladder needs them (`bindingTier` against the slot tiers above), so the text
  reads back as the AST it was rendered from — nested binaries, comparison
  chains, and prefix operators included. -/
partial def exprDiagnosticName : Expr -> String
  | .param name => name
  | .num value => toString value
  | .stringLiteral value => "'" ++ value ++ "'"
  | .boolLiteral value => Result.boolText value
  -- A prefix operator's operand is parenthesized when it binds looser than the
  -- operator's slot (`unaryOperandTier`): `-(a + b)`, `-(not a)`, `-(-a)`,
  -- `not (a and b)`; `-a ^ b` and `not a < b` read back bare with the same AST.
  | .unary op operand =>
      let operandName := parenthesizeWhenLooser (unaryOperandTier op) operand (exprDiagnosticName operand)
      (match op with
       | .minus => "-"
       | .not => "not ") ++ operandName
  -- A binary node's operands are written at `leftOperandTier` / `rightOperandTier`:
  -- a rebinding power base (`(-a) ^ b`, `(a + b) ^ b`), a `not` under a tighter
  -- operator (`(not a) + b`, `a * (not b)`), a looser binary (`(a + b) * c`),
  -- a right operand of equal tier (`a - (b - c)`), and a comparison chain under
  -- an arithmetic operator (`(a < b) + c`) keep their parentheses; `a + b + c`,
  -- `-a + b`, `a ^ -b`, and `a ^ b ^ c` read back bare.
  -- C#: `PushBinaryLeftOperand` / `PushBinaryRightOperand`.
  | .binary op left right =>
      let leftName := parenthesizeWhenLooser (leftOperandTier op) left (exprDiagnosticName left)
      let rightName := parenthesizeWhenLooser (rightOperandTier op) right (exprDiagnosticName right)
      leftName ++ " " ++ op.symbol ++ " " ++ rightName
  -- A comparison chain renders as the flat chain it is — `a < b <= c == d` —
  -- never as nested binary comparisons. Each operand is written at
  -- `comparisonOperandTier`, so a nested (parenthesized) chain, a `not`, and a
  -- logical operator keep their parentheses: `(a < b) == c` is not `a < b == c`.
  -- C#: `PushComparisonChain`.
  | .comparison _ [] => "<comparison with no links>"
  | .comparison first links =>
      comparisonOperandName first
        ++ String.join (links.map (fun link => " " ++ link.op.symbol ++ " " ++ comparisonOperandName link.operand))
  -- Source-faithful postfix indexing `target:selector`; operands that would
  -- rebind under the real precedence are parenthesized. This renderer prints
  -- binary bare, so a binary index operand is parenthesized here; C# reaches
  -- the same text via `OpenExprName`, which self-parenthesizes binary. The two
  -- agree on a simple operand (`(A + B):0`) but not on a NESTED one, where C#
  -- also parenthesizes the inner binary (`((A + B) + C):0` vs `(A + B + C):0`).
  -- That difference is inherited from each renderer's own binary convention,
  -- is independent of indexing, and is unambiguous either way.
  | .index target selector =>
      let targetName := exprDiagnosticName target
      let selectorName := exprDiagnosticName selector
      (if indexTargetNeedsParens target then "(" ++ targetName ++ ")" else targetName)
        ++ ":" ++
        (if indexSelectorNeedsParens selector then "(" ++ selectorName ++ ")" else selectorName)
  -- Internal SequenceConstruct renders as one sequence value; ';' is not surface syntax.
  | .sequenceConstruct left right => "(" ++ exprDiagnosticName left ++ ", " ++ exprDiagnosticName right ++ ")"
  -- Empty sequence value `()` and its nested forms.
  | .emptySequence depth => emptySequenceText depth
  -- Postfix spread binds to the completed operand. Unary and binary operands
  -- need parentheses so the diagnostic text reads back with the same AST.
  | .sequenceSpread operand =>
      parenthesizeWhenLooser postfixTier operand (exprDiagnosticName operand) ++ "*"
  -- Exact list literal `[a, b, c]`.
  | .listLiteral items => "[" ++ String.intercalate ", " (items.map exprDiagnosticName) ++ "]"
  | .resolve name => name
  | .algorithmExpr algorithm => "(" ++ String.intercalate ", " ((Algorithm.output algorithm).map exprDiagnosticName) ++ ")"
  | .capture rows => "(" ++ String.intercalate ", " (rows.map exprDiagnosticName) ++ ")"
  -- Postfix targets keep every grouping boundary that would rebind: binary and
  -- comparison nodes, unary operators, and negative numeric literals alike.
  -- C#: PushOperand at PostfixTier (Open already groups binary/comparison nodes).
  | .call fn _ => postfixTargetName fn ++ "(...)"
  | .dotMember target name _ none =>
      postfixTargetName target ++ "." ++ name
  | .dotMember target name _ (some _) =>
      postfixTargetName target ++ "." ++ name ++ "(...)"
where
  /-- One operand of a comparison chain, parenthesized when it binds looser than
      `comparisonOperandTier`. -/
  comparisonOperandName (operand : Expr) : String :=
    parenthesizeWhenLooser comparisonOperandTier operand (exprDiagnosticName operand)
  /-- The target of a call or dot edge is written at the postfix tier. -/
  postfixTargetName (target : Expr) : String :=
    parenthesizeWhenLooser postfixTier target (exprDiagnosticName target)

/-- The binary operand-shape name `left op right` — delegates to the `.binary`
  arm of `exprDiagnosticName` so the two can never disagree (in particular on
  power-base parenthesization). C#: `ExprNameRenderer.RenderBinaryDiagnosticName`. -/
def binaryExprDiagnosticName (op : BinaryOp) (left right : Expr) : String :=
  exprDiagnosticName (.binary op left right)

/-- The operand-shape name of ONE link of a comparison chain — `left op right`,
  the two ADJACENT operands the link compares — so the failing link of
  `1 < 2 < true` reads `2 < true`, never a nested spelling of the whole chain.
  Delegates to the `.comparison` arm so the two can never disagree.
  C#: `ExprNameRenderer.RenderComparisonLinkDiagnosticName`. -/
def comparisonLinkDiagnosticName (op : ComparisonOp) (left right : Expr) : String :=
  exprDiagnosticName (.comparison left [{ op := op, operand := right }])

/-- Apply ONE LINK of a comparison chain — `leftValue op rightValue`, the two
    ADJACENT operands the link compares — the single comparison semantics shared
    by every chain evaluation. `eq`/`ne` compare KatLang values structurally
    across all value kinds (`resultValueEq`): different kinds compare unequal
    rather than raising a type mismatch (`true == 1` is `false`), so equality is
    total and never fails. The ordering comparisons reject strings and then
    require numeric scalar operands (a Boolean operand is rejected — Booleans
    are NOT ordered; the empty sequence value `()` is an ordinary non-scalar
    operand, SYN-01), each rejection carrying the operand-shape context of THIS
    link (`while evaluating `2 < true``), never a spelling of the whole chain.
    C#: `Evaluator.ApplyComparison`. -/
def applyComparison (op : ComparisonOp) (leftExpr rightExpr : Expr) (lr rr : Result) : EvalM Bool :=
  match op with
  | .eq => pure (resultValueEq lr rr)
  | .ne => pure (!(resultValueEq lr rr))
  | _ =>
    match lr, rr with
    -- Non-equality operators are not defined on strings (they fail here rather
    -- than via expectInt so the diagnostic names the string operands).
    | .str _, .str _ => .error (Error.typeMismatch "Strings only support == and != operators")
    -- Mixed string/number or string/sequence value: fail for any ordering operator.
    | .str _, _ => .error (Error.typeMismatch "Cannot apply operator to string and non-string operands")
    | _, .str _ => .error (Error.typeMismatch "Cannot apply operator to string and non-string operands")
    | _, _ => do
      let linkContext := s!"while evaluating `{comparisonLinkDiagnosticName op leftExpr rightExpr}`"
      let x <- withCtx linkContext (requireNumericComparisonOperand op "left" lr)
      let y <- withCtx linkContext (requireNumericComparisonOperand op "right" rr)
      pure (match op with
            | .lt => decide (x < y)
            | .gt => decide (x > y)
            | .le => decide (x <= y)
            | .ge => decide (x >= y)
            | .eq => decide (x = y)
            | .ne => x != y)

namespace CtxMsg
  def openMsg (k : String)              := s!"while resolving open: {k}"
  def call   (f : Expr)               := s!"while evaluating call to {openExprName f}"
  def property (n : Ident)            := s!"while evaluating property {n}"
  def dotCall (obj : Expr) (n : Ident) := s!"while evaluating dotCall .{n} of {openExprName obj}"
end CtxMsg

/-- The ONE zero-argument value-demand law (its rejection half), keyed by the
    written shape that names the demanded algorithm. It is consulted BEFORE an
    algorithm's body is entered wherever a resolved algorithm is demanded for its
    VALUE with zero explicit arguments: the value-position `resolve` /
    `algorithmExpr` arms of `evalCounted`, every lazy builtin VALUE slot (the `if`
    condition and branches, `while`/`repeat` initial state, the `repeat` count,
    `atoms`, `range` — `evalArgumentValueCounted`), and the ordinary-dot `string`
    intrinsic's receiver. The value-position `param` arm does NOT consult it: a
    parameter's value outcome was established when its argument slot was
    evaluated — through this law, at the written argument — and the read reuses
    that outcome (AT-MOST-ONCE ARGUMENT VALUE EVALUATION, `AlgBinding`).

    ELIGIBILITY IS ARITY, NOT PARAMETER-LIST EMPTINESS (September 2026): a
    callable may satisfy a zero-argument value demand exactly when an ordinary
    call supplying zero arguments can bind it
    (`Algorithm.acceptsZeroSuppliedArguments` — the binder's own
    `ParameterPattern.minimumSuppliedSlots` rule, the family's zero-arity branch
    rule). So `Only(*xs) = xs` is demandable (a collecting parameter requires no
    supplied slot: `Only` and `Only()` both accept zero) while `Head(x, *rest)`
    still requires one supplied value and is rejected. The REPORT names the true
    minimum supply — `minimumSuppliedSlots`, never the flattened declared capture
    count — so `Head` reports 1 and `P((x, y))` reports 1, exactly the counts
    `Head()` / `P()` report.

    Only the report's shape depends on the source:
    - a lexical property reference `X` (`.resolve`): a conditional cannot be
      accessed as a value (`conditionalValueAccessError?`), and a parameterized
      property is `withContext (property X) (arityMismatch k 0)`;
    - an algorithm-channel parameter `x` (`.param`) and a structurally navigated
      member `A.M` (an argumentless `.dotMember` receiver): the same conditional
      rule, then the bare `arityMismatch k 0`;
    - a written brace block (`.algorithmExpr`): `unresolvedImplicitParams` — the
      block's OWN inferred parameters;
    - an inline CALLABLE ALIAS block (`.algorithmExpr` of an `Algorithm.alias`,
      `{ F }`): binding indirection with no signature and no report of its own, so
      the demand is reported exactly as its written target reference `F` reports it
      — the target's own contract (`{ Inc }` with `Inc(x)` is Inc's property-context
      `arityMismatch 1 0`, a family `noMatchingBranch`), never the written block's
      `unresolvedImplicitParams` over the target's parameters (FA-OQ-1, owner
      decision Option B, 2026-10-10). A builtin target stays `none` here, as above;
    - an anonymous or value-reified argument (`none`): the bare `arityMismatch`.
    `none` means the demand may proceed to the algorithm's zero-argument value
    (`evalZeroArgumentDemandOutputCounted`, which binds the accepted EMPTY supply
    first). A builtin CALLBACK slot (`map`/`filter`/`reduce` steps, loop steps)
    supplies arguments and never consults this law. C#:
    `ZeroArgumentValueDemandError`. -/
def zeroArgumentDemandError? (source? : Option Expr) (a : Algorithm) : Option Error :=
  match a with
  | .builtin _ =>
      -- A builtin is deliberately NOT decided here: its zero-argument rejection
      -- is owned by `evalBuiltinValueCounted` (`builtinArityError b 0` — the very
      -- error `sum()` reports), and intercepting it would replace that report
      -- with a parameter-list one.
      none
  | _ =>
    if Algorithm.acceptsZeroSuppliedArguments a then none
    else
      let arity :=
        Error.arityMismatch
          (ParameterPattern.minimumSuppliedSlots (Algorithm.parameterPatterns a)) 0
      let named (name : Ident) (reject : Error) : Error :=
        (conditionalValueAccessError? name a).getD reject
      -- An inline callable alias is reported as its written target reference (FA-OQ-1).
      let source? := match source? with
        | some (.algorithmExpr (.alias _ _ _ target _)) => some target
        | other => other
      match source? with
      | some (.resolve n) => some (named n (Error.withContext (CtxMsg.property n) arity))
      | some (.param x) => some (named x arity)
      | some (.dotMember _ n _ _) => some (named n arity)
      | some (.algorithmExpr _) =>
          some (named "conditional" (Error.unresolvedImplicitParams (Algorithm.params a)))
      | _ => some (named "conditional" arity)

/-- The ACCEPTANCE half of the ONE zero-argument value-demand law, read off the
    law itself so the two halves can never disagree: `true` exactly when
    `zeroArgumentDemandError?` lets the demand proceed. It differs from
    `Algorithm.acceptsZeroSuppliedArguments` only for a BUILTIN, which the law
    deliberately passes through to its own arity rejection
    (`evalBuiltinValueCounted`) — the law
    `zero_argument_value_demand_accepts_exactly_zero_supply_callables` in
    `KatLangArityLaws.lean` proves the two agree everywhere else. Used by the
    demand sites that decide the same question without building a report: the
    structurally navigated member arm of `evalDotCallCounted` and the collection
    builtins' value slots. C#: `AcceptsZeroArgumentValueDemand`. -/
def acceptsZeroArgumentValueDemand (a : Algorithm) : Bool :=
  (zeroArgumentDemandError? none a).isNone

--------------------------------------------------------------------------------
-- Open resolution structures
--------------------------------------------------------------------------------

/-- A resolved open: its canonical dedup key, original expression, and resolved algorithm. -/
structure ResolvedOpen where
  key  : String
  expr : Expr
  lib  : Algorithm
  deriving Repr

/-- A resolved property-style access with the owner and binding retained for
    zero-argument property cache keys. -/
structure ResolvedProperty where
  owner   : Algorithm
  binding : PropDef
  alg     : Algorithm
  deriving Repr

structure OpenPropertyHit where
  provider : String
  property : ResolvedProperty
  deriving Repr

--------------------------------------------------------------------------------
-- Pattern matching (for conditional algorithms)
--------------------------------------------------------------------------------

/-- The elements a family structural pattern of `patternCount` items matches
    against: a value of the pattern's OWN kind (`Result.sequencePatternItems?`
    for `(…)`, `Result.listPatternItems?` for `[…]`) with exactly that many
    elements, and nothing otherwise — never a value of the other kind and never
    a scalar (STRUCTURAL PATTERN DELIMITERS SELECT THE VALUE KIND THEY
    DESTRUCTURE, September 2026; the former singleton fallback, under which a
    one-item `(b)` took any non-sequence value whole, is gone with the
    one-item sequence pattern itself). Shared by `matchPattern` and
    `matchCountedPattern`, so direct conditional calls and counted callback
    calls (map/filter/reduce) accept exactly the same input shapes. -/
def patternStructureMembers? (elements? : Option (List Result)) (patternCount : Nat)
    : Option (List Result) :=
  match elements? with
  | some rs => if rs.length == patternCount then some rs else none
  | none => none

mutual
/-- Match a pattern against a Result, returning accumulated bindings on success.
    - `bind x` matches any Result, binding x → r
    - `litInt n` matches only `Result.atom n`; `litBool b` only `Result.bool b`
    - `sequenceValue ps` matches only `Result.sequenceValue rs` with the same length,
      recursively; `listValue ps` matches only `Result.listValue rs` with the same
      length, recursively (`patternStructureMembers?`)

    Bindings accumulate left-to-right. Repeated names compare against the
    first bound value and do not add another environment entry. -/
partial def matchPatternInto (p : Pattern) (r : Result) (env : ValEnv)
    : Option ValEnv :=
  match p with
  | .bind x =>
      match env.lookup x with
      | some existing => if existing == r then some env else none
      | none => some (env ++ [(x, r)])
  | .litInt n  =>
      match r with
      | .atom v => if v = n then some env else none
      | _       => none
  | .litString s =>
      match r with
      | .str v => if v = s then some env else none
      | _      => none
  | .litBool b =>
      match r with
      | .bool v => if v = b then some env else none
      | _       => none
  | .sequenceValue ps  => matchStructureInto ps (patternStructureMembers? (Result.sequencePatternItems? r) ps.length) env
  | .listValue ps  => matchStructureInto ps (patternStructureMembers? (Result.listPatternItems? r) ps.length) env

/-- Match a structural pattern's items against the elements its value supplied
    (`none` when the value is not of the pattern's kind or length). -/
partial def matchStructureInto (ps : List Pattern) (members? : Option (List Result)) (env : ValEnv)
    : Option ValEnv :=
  match members? with
  | none => none
  | some rs =>
      let rec go : List Pattern -> List Result -> ValEnv -> Option ValEnv
        | [], [], current => some current
        | p::ps', r::rs', current => do
            let next <- matchPatternInto p r current
            go ps' rs' next
        | _, _, _ => none
      go ps rs env
end

def matchPattern (p : Pattern) (r : Result) : Option ValEnv :=
  matchPatternInto p r []

/-- Match a top-level conditional call head against the explicit argument list
    supplied at the call site.

    Ordinary direct conditional calls preserve explicit argument slots at the
    top level: a non-sequence-value head expects exactly one explicit argument, while a
    sequence-value head expects one explicit argument per sequence element. Nested sequence-value
    structure is still matched through `matchPattern`. -/
def matchCallPattern (p : Pattern) (args : List Result) : Option ValEnv :=
  match p with
  | .sequenceValue ps =>
      if ps.length != args.length then
        none
      else
        let rec go : List Pattern -> List Result -> ValEnv -> Option ValEnv
          | [], [], env => some env
          | p::ps', arg::args', env => do
              let next <- matchPatternInto p arg env
              go ps' args' next
          | _, _, _ => none
        go ps args []
  | _ =>
      match args with
      | [arg] => matchPattern p arg
      | _ => none

/-- Try to match branches in order against the explicit argument list of an
    ordinary direct conditional call. -/
def matchCallBranches (bs : List CondBranch) (args : List Result) : Option (CondBranch × ValEnv) :=
  match bs with
  | []     => none
  | b::bs' =>
      match matchCallPattern b.pattern args with
      | some env => some (b, env)
      | none     => matchCallBranches bs' args

mutual
partial def matchCountedPatternInto (p : Pattern) (arg : CountedResult)
    (env : CountedParamEnv) : Option CountedParamEnv :=
  match p with
  | .bind x =>
      match env.lookup x with
      | some existing => if existing.fst == arg.fst then some env else none
      | none => some (env ++ [(x, arg)])
  | .litInt n =>
      match arg.fst with
      | .atom v => if v = n then some env else none
      | _ => none
  | .litString s =>
      match arg.fst with
      | .str v => if v = s then some env else none
      | _ => none
  | .litBool b =>
      match arg.fst with
      | .bool v => if v = b then some env else none
      | _ => none
  | .sequenceValue ps =>
      matchCountedStructureInto ps (patternStructureMembers? (Result.sequencePatternItems? arg.fst) ps.length) env
  | .listValue ps =>
      matchCountedStructureInto ps (patternStructureMembers? (Result.listPatternItems? arg.fst) ps.length) env

/-- Counted twin of `matchStructureInto`: each element crosses the ordinary
    value boundary (`Result.valueCount`) before its sub-pattern matches. -/
partial def matchCountedStructureInto (ps : List Pattern) (members? : Option (List Result))
    (env : CountedParamEnv) : Option CountedParamEnv :=
  match members? with
  | none => none
  | some rs =>
      let rec go : List Pattern -> List Result ->
          CountedParamEnv -> Option CountedParamEnv
        | [], [], current => some current
        | p'::ps', r::rs', current => do
            let next <- matchCountedPatternInto p' (r, Result.valueCount r) current
            go ps' rs' next
        | _, _, _ => none
      go ps rs env
end

def matchCountedPattern (p : Pattern) (arg : CountedResult) : Option CountedParamEnv :=
  matchCountedPatternInto p arg []

def matchCountedCallPattern (p : Pattern) (args : List CountedResult) : Option CountedParamEnv :=
  match p with
  | .sequenceValue ps =>
      if ps.length != args.length then
        none
      else
        let rec go : List Pattern -> List CountedResult ->
            CountedParamEnv -> Option CountedParamEnv
          | [], [], env => some env
          | p'::ps', arg::args', env => do
              let next <- matchCountedPatternInto p' arg env
              go ps' args' next
          | _, _, _ => none
        go ps args []
  | _ =>
      match args with
      | [arg] => matchCountedPattern p arg
      | _ => none

def matchCountedCallBranches (bs : List CondBranch) (args : List CountedResult)
    : Option (CondBranch × CountedParamEnv) :=
  match bs with
  | [] => none
  | b::bs' =>
      match matchCountedCallPattern b.pattern args with
      | some env => some (b, env)
      | none => matchCountedCallBranches bs' args

--------------------------------------------------------------------------------
-- Pure evaluator helpers (no evaluator recursion)
--------------------------------------------------------------------------------
-- Helpers used by the evaluator that are not part of its recursion cycle:
-- they never call back into eval/evalCounted/applyBuiltin and friends, so
-- Lean checks them as ordinary total definitions.

/-- True when an argument expression supplies ONLY a value in argument
    position. A capture is a value boundary: it suppresses the algorithm
    identity of anything inside it, so higher-order probing never sees the
    enclosed content as callable.

    `algorithmExpr` is deliberately NOT value-only: an algorithm block
    explicitly exposes its contained Algorithm on the algorithm channel
    regardless of parameter/declaration/output count — `{42}` is as much an
    Algorithm as `{a + 1}` — while the value channel reifies the written slot
    independently. -/
def shouldWrapArgExprAsValue : Expr -> Bool
  | .capture _ => true
  | _ => false

def isLiftableArgResolutionError : Error → Bool
  | .notAnAlgorithm _ => true
  | .illegalInEval _  => true
  | .withContext _ e   => isLiftableArgResolutionError e
  | _                  => false

def loopStateResult (stateSlots : List Result) : Result :=
  Result.normalize (.sequenceValue stateSlots)

/-- The ROW SUPPLY a builtin loop step contributes (LOOP-03, LOOP-08, Q-23 decided
    October 2026): a builtin has no written rows, so the ONE result value of its
    ordinary invocation is ONE non-spread row — exactly the row its one-row user
    wrapper `W(p…) = builtin(p…)` writes. The emitted count is never consulted: a
    `()` result is one visible slot (never zero slots, as `countedTopLevelValues`
    would read it) and a collection result is one slot holding the collection.
    Laws: `loop_step_builtin_result_is_one_row`, `loop_step_builtin_rows_ignore_emitted_count`.
    C#: the builtin arm of `Evaluator.InvokeLoopStepSupply`. -/
def loopStepBuiltinRows (out : CountedResult) : List Result := [out.fst]

/-- The name a loop step's own call frame and a family step's `noMatchingBranch`
    report (LOOP-08, Q-23): the written expression its SUPPLY CELL retains — the
    step argument as written, or, for a cell transported through a parameter, the
    argument originally written for it (`supplyNeed`) — named exactly as the
    ordinary call names its callee (`openExprName`); a cell with no written source
    (a spread item) is the loop's step. C#: `Evaluator.StepDiagnosticName`. -/
def loopStepName (loopName : String) (step : ResolvedArgumentAlgorithm) : EvalM String := do
  let written? : Option Expr <- match step.need? with
    | some address => do
        match (<- get).needs[address]? with
        | some { suspension := .expression source _ _, .. } => pure (some source)
        | _ => pure none
    | none => pure step.source?
  pure (match written? with
    | some e => openExprName e
    | none => loopName ++ " step")

/-- The completed `while`/`repeat` result (LOOP-07, Q-26 decided October 2026):
    ONE value — the canonical capture of the final state's slots (`()` for zero
    slots, the slot itself for one, a sequence for several) — crossing the
    ordinary RESULT value boundary like every other builtin and call result:
    its emitted count is `Result.valueCount` of that value
    (`reCountValueBoundary`), never the slot count. The slot count is the
    loop's own protocol and is not observable outside the loop: a one-slot
    state holding `(20, 30)` and a two-slot state `20, 30` complete to the same
    counted result, and only an explicit spread `L*` opens it into items.
    Laws: `loop_result_is_a_value_boundary`, `loop_result_count_le_one`.
    C#: `Evaluator.MakeCheckedLoopStateResult`. -/
def loopResultCounted (finalSlots : List Result) : CountedResult :=
  reCountValueBoundary (loopStateResult finalSlots, finalSlots.length)

/-- The context of a `while` step that emitted no slot at all: its output has
    no continuation flag, an emitted-slot cardinality failure (`badArity`,
    Q-27). C#: `Evaluator.WhileStepWithoutFlagContext`. -/
def whileStepWithoutFlagContext : String :=
  "a while step must output at least its continuation flag"

/-- Split a loop step output into next state slots and the continuation flag.
    The step's LAST output is the flag and must be a Boolean value (`true`
    continues, `false` stops); a number, string, sequence, or list there is a
    value-kind error, never a truth test. A single-output step keeps the
    established shape — its one slot is both the next state and the flag — so
    it must be Boolean too. C#: `Evaluator.SplitContSlots`. -/
def splitContSlots (outputSlots : List Result) : EvalM (List Result × Bool) := do
  match outputSlots with
  | [] => .error (Error.withContext whileStepWithoutFlagContext Error.badArity)
  | [slot] =>
    match Result.asBool? slot with
    | some c => pure ([slot], c)
    | none => .error (Error.typeMismatch
        (booleanRequiredMessage "while continuation flag (the step's last output)" slot))
  | _ =>
    match outputSlots.getLast? with
    | some last =>
      match Result.asBool? last with
      | some c => pure (outputSlots.dropLast, c)
      | none => .error (Error.typeMismatch
          (booleanRequiredMessage "while continuation flag (the step's last output)" last))
    | none => .error Error.badArity

/-- The counted view of one iterated collection item as the callback receives
    it. A callback item is a SELECTED value, so it crosses the same ordinary
    value boundary as `S:i` / `first` / `last` (`reCountValueBoundary`): the
    item keeps its stored shape (a nested sequence or list stays one value for
    pattern matching and for every count-sensitive reader inside the body — a
    bare `x` output row, `x.Coll` on a collecting receiver), a `()` item emits
    zero values, and only an explicit
    spread `x*` opens it. Law: `callback_item_is_a_value_boundary`.
    C#: `CountedSequenceCallbackItem`. -/
def countedSequenceCallbackItem (item : CountedResult) : CountedResult :=
  reCountValueBoundary item

/-- A property-style access reuses the per-run cache exactly when the demanded
    callable is one the ONE zero-argument value-demand law ACCEPTS
    (`Algorithm.acceptsZeroSuppliedArguments`), so a newly eligible
    collecting-only property (`Only(*xs) = xs`) takes the very same demand/cache
    path an ordinary zero-parameter property takes — eligibility is what the
    September 2026 rule widened, cache POLICY is unchanged, and `Only()` remains
    an ordinary call that bypasses the entry. A builtin never accepts, so it
    keeps flowing to its own arity rejection uncached, exactly as before.
    Since Q-03 (2026-09-28) the surface pass reads the SAME rule when it decides
    whether to lift a bare reference (`liftsBareValueReference`): it never
    rewrites a reference to a callable this accepts into a fresh forwarding
    call, so such a reference reaches this cache in EVERY position — an
    operand, a list element, a selection target, a Math argument — and
    not only in the neutral ones.
    C#: the zero-argument property access path
    (`GetOrEvaluateZeroArgPropertyResult`), entered by callers only after the
    law accepted. -/
def isCacheableZeroArgPropertyAlgorithm (a : Algorithm) : Bool :=
  Algorithm.acceptsZeroSuppliedArguments a

/-- The cache key of one property-style access (see `ZeroArgPropertyCacheKey`
    for the law it encodes): an exported binding's key carries no environment
    components; a local-only binding uses its declaring owner's retained binding
    context, falling back to the access environments only for unactivated host scopes. -/
def zeroArgPropertyCacheKey (_accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (ctx : EvalCtx) (env : ValEnv)
    (ownerBindingContext : Option Nat := none)
    : ZeroArgPropertyCacheKey :=
  let bindingContextFree := binding.exposure.isExported
  {
    accessKind := .lexical,
    owner := reprStr owner.declarationId ++ reprStr (cacheScopeShape owner.asScopeCtx),
    propertyName := binding.name,
    propertyAlgorithm := reprStr (cacheAlgorithmShape binding.alg),
    valEnv := if bindingContextFree || ownerBindingContext.isSome then none else some (reprStr env),
    algEnv := if bindingContextFree || ownerBindingContext.isSome then none else some (reprStr ctx.algEnv),
    countedParamEnv := if bindingContextFree || ownerBindingContext.isSome then none else some (reprStr ctx.countedParamEnv),
    bindingContext := if bindingContextFree then none else some (ownerBindingContext.getD ctx.bindingContext)
  }

/-- The context at the declaring owner's entry, independent of the consumer. A
    parameterless property read preserves it; an explicit call binds a fresh one. -/
partial def propertyOwnerBindingContext (scope : Option ScopeCtx) (state : EvalState) : Option Nat :=
  match scope with
  | none => none
  | some level =>
      match level.activation.bind (fun id => state.lexicalActivations[id]?) with
      | some activation => some activation.bindingContext
      | none => propertyOwnerBindingContext level.parent state

def requireCallableValues (items : List CallableCallItem)
    : EvalM (List Result) := do
  match items with
  | [] => pure []
  | item :: rest =>
      let tail <- requireCallableValues rest
      match item.value? with
      | some value => pure (value :: tail)
      | none =>
          if item.skipMissingValue then
            pure tail
          else
            match item.error? with
            | some err => .error err
            | none => .error Error.badArity

def applySequenceBuiltinEmptyPolicy (b : Builtin) (metadata : SequenceBuiltinMetadata)
    (collected : CollectedSequenceBuiltinInput) : EvalM CollectedSequenceBuiltinInput :=
  match metadata.emptyPolicy with
  | .allowEmpty =>
      pure collected
  -- The empty collection is a DOMAIN failure of an aggregate and a missing
  -- POSITION of a selection (Q-27): never an arity error, because the argument
  -- count is correct.
  | .requireAnyItem =>
      if collected.totalItemCount = 0 then
        .error (Error.illegalInEval s!"{builtinDisplayName b} requires a non-empty collection")
      else
        pure collected
  | .requireSelectablePosition =>
      if collected.totalItemCount = 0 then
        .error (Error.withContext
          s!"{builtinDisplayName b} selects from an empty collection, which has no position to select"
          Error.badIndex)
      else
        pure collected

/-- Collect top-level collection elements as single atomic numeric values.
    Used by numeric ordering and aggregation builtins, which reject strings
    and sequence values instead of inventing mixed-type or structural
    interpretation.

    Diagnostics identify the 0-based collection item index so numeric shape
    failures remain debuggable after counted top-level extraction. An element
    that is not one number is a present value of the wrong KIND —
    `typeMismatch` (Q-27), never an arity error.
    C#: `Evaluator.CollectSingleAtomicNumbers`. -/
def collectSingleAtomicNumbers (b : Builtin)
    : Nat -> List Result -> EvalM (List Int)
  | _, [] => pure []
  | index, item :: rest =>
      match Result.singleAtomicNumber? item with
      | some n => do
          let tail <- collectSingleAtomicNumbers b (index + 1) rest
          pure (n :: tail)
      | none =>
          .error (Error.typeMismatch (numericSequenceItemErrorContext b index item))

def prepareSequenceBuiltinInput (b : Builtin) (metadata : SequenceBuiltinMetadata)
    (collected : CollectedSequenceBuiltinInput)
    : EvalM PreparedSequenceBuiltinInput := do
  let collected <- applySequenceBuiltinEmptyPolicy b metadata collected
  let numericItems <-
    match metadata.itemShapeConstraint with
    | .any =>
        pure none
    | .singleNumeric => do
      let numbers <- collectSingleAtomicNumbers b 0 collected.items
      pure (some numbers)
  pure { items := collected.items, numericItems? := numericItems }

def sequenceBuiltinSuffixArgRequirementDesc
    (kind : SequenceBuiltinSuffixArgKind) : String :=
  match kind with
  | .algorithm => "an algorithm"
  | .value => "exactly one value"
  | .wholeNumber => "exactly one whole-number value"

def sequenceBuiltinSuffixArgKindDesc
    (kind : SequenceBuiltinSuffixArgKind) : String :=
  match kind with
  | .algorithm => "algorithm"
  | .value => "value"
  | .wholeNumber => "whole-number value"

def sequenceBuiltinSuffixArgErrorContext
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor) : String :=
  s!"{builtinDisplayName b} {descriptor.name} must be {sequenceBuiltinSuffixArgRequirementDesc descriptor.kind}"

def internalSequenceBuiltinSuffixArgMetadataError
    (b : Builtin) (detail : String) : EvalM α :=
  .error (Error.withContext
    s!"internal sequence metadata for {builtinDisplayName b} {detail}"
    Error.badArity)

/-- After binding chooses a VALUE position, apply the shared demand rejection to
    an unevaluated callable using its written source — judging the callable the
    item NAMES (`CallableCallItem.named?`), never its value wrapper. Preserve a
    valid value's body error; callback positions never consult this helper. A
    parameter's established failure precedes callable classification. `refine`
    rewrites only the zero-argument law's REJECTION of the named callable (every
    value slot keeps it unchanged except `reduce`'s `initial`,
    `reduceInitialRejection`). -/
def sequenceBuiltinValueDemandErrorWith? (refine : Algorithm -> Error -> Error)
    (item : CallableCallItem) : Option Error :=
  match item.source?, item.error? with
  | some (.param _), some err => some err
  | _, _ => match item.named? with
    | some alg => ((zeroArgumentDemandError? item.source? alg).map (refine alg)).or item.error?
    | none => item.error?

def sequenceBuiltinValueDemandError? (item : CallableCallItem) : Option Error :=
  sequenceBuiltinValueDemandErrorWith? (fun _ err => err) item

def reduceInitialAccumulatorRequiresValueError : Error :=
  Error.withContext "while preparing reduce initial accumulator" Error.badArity

/-- `reduce`'s `initial` is an ordinary VALUE slot (HO-04), demanded once like
    every other value slot; only the REPORT of a zero-argument demand rejection is
    reduce's own. A rejected callable that declares parameters is the reducer
    written where the initial accumulator belongs (`reduce(xs, Add, Inc)`), so it
    gets reduce's dedicated accumulator report; any other rejection (a clause
    family's `noMatchingBranch`) keeps the law's report. -/
def reduceInitialRejection (alg : Algorithm) (err : Error) : Error :=
  if (Algorithm.params alg).isEmpty then err else reduceInitialAccumulatorRequiresValueError

def prepareSequenceBuiltinSuffixArgItem
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor)
    (item : CallableCallItem) : EvalM PreparedSequenceBuiltinSuffixArg := do
  match descriptor.kind with
  | .algorithm =>
    if let some address := item.need? then return .needAlgorithm address
    -- A CALLBACK slot: call-item assembly never evaluated the item (CALL-03), so
    -- it carries its algorithm channel only; the builtin invokes it later.
    match item.algorithm? with
    | some alg => pure (.algorithm alg item.callable?)
    | none =>
        match item.error? with
        | some err => .error err
        | none =>
        .error (Error.withContext
          (sequenceBuiltinSuffixArgErrorContext b descriptor)
          Error.badArity)
  | .value =>
    match item.value? with
    | some value => pure (.value value)
    | none =>
        let refine : Algorithm -> Error -> Error := match b with
          | .reduceBuiltin => reduceInitialRejection
          | _ => fun _ err => err
        match sequenceBuiltinValueDemandErrorWith? refine item with
        | some err => .error err
        | none =>
        .error (Error.withContext
          (sequenceBuiltinSuffixArgErrorContext b descriptor)
          Error.badArity)
  | .wholeNumber =>
    match item.value? with
    | some value =>
      -- The one numeric-control rule (Q-27): a present value of the wrong KIND
      -- is `typeMismatch`. (A non-whole number is the C# runtime's
      -- `illegalInEval`; the integer core has none.)
      match Result.singleAtomicNumber? value with
      | some number => pure (.wholeNumber number)
      | none =>
          .error (Error.typeMismatch
            s!"{sequenceBuiltinSuffixArgErrorContext b descriptor}, but was {operandDescription value}")
    | none =>
        match sequenceBuiltinValueDemandError? item with
        | some err => .error err
        | none =>
        .error (Error.withContext
          (sequenceBuiltinSuffixArgErrorContext b descriptor)
          Error.badArity)

def expectPreparedSequenceBuiltinSuffixArgAt
    (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor)
    (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat)
    (expectedKind : SequenceBuiltinSuffixArgKind)
    (projector : SequenceBuiltinSuffixArgDescriptor -> PreparedSequenceBuiltinSuffixArg -> EvalM α)
    : EvalM α := do
  if descriptors.length != args.length then
    internalSequenceBuiltinSuffixArgMetadataError b "mismatched suffix arguments"
  else
    match List.drop index descriptors, List.drop index args with
    | descriptor :: _, arg :: _ =>
        if descriptor.kind = expectedKind then
          projector descriptor arg
        else
          internalSequenceBuiltinSuffixArgMetadataError b
            s!"expected suffix argument {index + 1} ({descriptor.name}) to have metadata kind {sequenceBuiltinSuffixArgKindDesc expectedKind}, but found {sequenceBuiltinSuffixArgKindDesc descriptor.kind}"
    | _, _ =>
        internalSequenceBuiltinSuffixArgMetadataError b
          s!"expected suffix argument {index + 1} to have metadata kind {sequenceBuiltinSuffixArgKindDesc expectedKind}"

/-- The CALLBACK a sequence builtin invokes from an algorithm suffix slot (the
    `filter` predicate, the `map` mapper, the `reduce` reducer): the argument's
    algorithm-channel identity (`ResolvedArgumentAlgorithm.invoked`). -/

def expectPreparedSequenceBuiltinWholeNumberSuffixArg
    (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor)
    (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) : EvalM Int :=
  expectPreparedSequenceBuiltinSuffixArgAt b descriptors args index .wholeNumber fun descriptor arg =>
    match arg with
    | .wholeNumber number => pure number
    | _ =>
        internalSequenceBuiltinSuffixArgMetadataError b
          s!"prepared suffix argument {index + 1} ({descriptor.name}) did not match metadata kind {sequenceBuiltinSuffixArgKindDesc .wholeNumber}"

def expectPreparedSequenceBuiltinValueSuffixArg
    (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor)
    (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) : EvalM Result :=
  expectPreparedSequenceBuiltinSuffixArgAt b descriptors args index .value fun descriptor arg =>
    match arg with
    | .value value => pure value
    | _ =>
        internalSequenceBuiltinSuffixArgMetadataError b
          s!"prepared suffix argument {index + 1} ({descriptor.name}) did not match metadata kind {sequenceBuiltinSuffixArgKindDesc .value}"

def expectPreparedNumericItems (b : Builtin)
    (prepared : PreparedSequenceBuiltinInput) : EvalM (List Int) :=
  match prepared.numericItems? with
  | some numbers => pure numbers
  | none =>
      .error (Error.withContext
        s!"internal sequence metadata for {builtinDisplayName b} did not produce numeric items"
        Error.badArity)

/-- Evaluate `order(collection)`.
    `order` eagerly evaluates the full top-level collection, sorts its numeric
    items ascending, preserves duplicates, and materializes the sorted items
    as one list value.

    Each top-level collection element must be exactly one atomic numeric
    value. Sequence values are not flattened or recursively inspected, and
    strings are rejected. Empty collections yield the empty list `[]`. -/
def evalOrderCounted (numbers : List Int) : EvalM CountedResult := do
  let sorted := sortIntsAsc numbers
  pure (makeCollectionListResult (sorted.map Result.atom))

/-- Evaluate `orderDesc(collection)`.
    `orderDesc` eagerly evaluates the full top-level collection, sorts its
    numeric items descending, preserves duplicates, and materializes the
    sorted items as one list value.

    Each top-level collection element must be exactly one atomic numeric
    value. Sequence values are not flattened or recursively inspected, and
    strings are rejected. Empty collections yield the empty list `[]`. -/
def evalOrderDescCounted (numbers : List Int) : EvalM CountedResult := do
  let sorted := sortIntsDesc numbers
  pure (makeCollectionListResult (sorted.map Result.atom))

/-- Evaluate `count(collection)`.
    `count` processes top-level collection elements from left to right and
    increments once per element.

    Each atom, string, Boolean, sequence value, or list value counts as one
    top-level element. Sequence and list values are not flattened or recursively inspected, and empty
    collections return `0`. -/
def evalCountCounted (items : List Result) : EvalM CountedResult := do
  pure (Result.atom (Int.ofNat items.length), 1)

/-- Evaluate `contains(collection, item)`.
    `contains` checks whether any extracted top-level item equals the searched
    suffix item using ordinary KatLang value equality.

    Search is top-level only: sequence values compare as sequence values and are
    not recursively flattened or inspected. The result is a Boolean value:
    `true` when some item equals `item`, otherwise `false` (so an empty
    collection yields `false`). -/
def evalContainsCounted (items : List Result) (searched : Result) : EvalM CountedResult := do
  let found := items.any (fun item => item == searched)
  pure (Result.bool found, 1)

/-- Evaluate `distinct(collection)`.
    `distinct` removes later duplicate top-level items while preserving the
    first occurrence of each item and the original left-to-right order.

    Equality follows ordinary KatLang value semantics on extracted top-level
    items: atoms compare by numeric value, strings by exact string value, and
    sequence/list values structurally by their elements. Sequence and list
    values stay intact and are not flattened. The kept items are materialized
    as one list value: empty collections yield `[]`, and a
    single kept item forms `[item]` (so `distinct(((), ()))` yields `[()]`). -/
def evalDistinctCounted (items : List Result) : EvalM CountedResult := do
  let distinctItems := dedupList items
  pure (makeCollectionListResult distinctItems)

/-- Evaluate `first(collection)`: SELECT the first top-level collection
    element. The element is returned exactly as stored and re-counted through
    the ordinary value boundary (`Result.valueCount`), exactly like
    `collection:0` — a selected sequence or list stays one value, a selected
    `()` emits zero values, and only an explicit spread opens the selection.
    An empty collection has no position to select: `badIndex`, the outcome of
    `collection:0` (SEQ-04, Q-27; the empty policy reports it first).
    Laws: `first_is_select_zero`, `first_empty_is_badIndex`.
    C#: `EvalFirstCounted`. -/
def evalFirstCounted (items : List Result) : EvalM CountedResult := do
  match items with
  | first :: _ => pure (first, Result.valueCount first)
  | [] => .error Error.badIndex

/-- Evaluate `last(collection)`: SELECT the last top-level collection element
    through the same value boundary as `evalFirstCounted` and
    `collection:(count - 1)`. An empty collection has no position to select:
    `badIndex`. Laws: `last_is_select_last`, `last_empty_is_badIndex`.
    C#: `EvalLastCounted`. -/
def evalLastCounted (items : List Result) : EvalM CountedResult := do
  match items.getLast? with
  | some last => pure (last, Result.valueCount last)
  | none => .error Error.badIndex

/-- Evaluate `take(collection, count)`.
    `take` returns the first `count` extracted top-level items unchanged,
    materialized as one list value.
    `count` is a fixed control argument after the `collection` argument.

    Non-positive counts return the empty list `[]`. Counts larger than the
    item count return all items. Nested sequence and list values stay intact
    as exact elements (so `take(((1, 2), (3, 4)), 1)` yields `[(1, 2)]`), and
    the original top-level order is preserved. -/
def evalTakeCounted (items : List Result) (count : Int) : EvalM CountedResult := do
  let taken :=
    if count <= 0 then
      []
    else
      items.take (Int.toNat count)
  pure (makeCollectionListResult taken)

/-- Evaluate `skip(collection, count)`.
    `skip` returns the extracted top-level items after the first `count`
    items, preserving item identity and original order, materialized as one
    list value.
    `count` is a fixed control argument after the `collection` argument.

    Non-positive counts keep all items. Counts larger than the item count
    return the empty list `[]`. Nested sequence and list values stay intact
    as exact elements. -/
def evalSkipCounted (items : List Result) (count : Int) : EvalM CountedResult := do
  let remaining :=
    if count <= 0 then
      items
    else
      items.drop (Int.toNat count)
  pure (makeCollectionListResult remaining)

/-- Evaluate `min(collection)`.
    `min` compares top-level sequence items from left to right and
    returns the smallest numeric element.

    The collection must be non-empty. Each top-level collection element must
    be exactly one atomic numeric value. Sequence values are not flattened or
    recursively inspected, and strings are rejected. -/
def evalMinCounted (numbers : List Int) : EvalM CountedResult := do
  let rec minLoop : List Int -> Int -> EvalM Int
    | [], currentMin => pure currentMin
    | n :: rest, currentMin =>
        minLoop rest (if n < currentMin then n else currentMin)
  match numbers with
  | [] => .error (Error.illegalInEval "min requires a non-empty collection")
  | first :: rest => do
      let minimum <- minLoop rest first
      pure (Result.atom minimum, 1)

/-- Evaluate `max(collection)`.
    `max` compares top-level sequence items from left to right and
    returns the largest numeric element.

    The collection must be non-empty. Each top-level collection element must
    be exactly one atomic numeric value. Sequence values are not flattened or
    recursively inspected, and strings are rejected. -/
def evalMaxCounted (numbers : List Int) : EvalM CountedResult := do
  let rec maxLoop : List Int -> Int -> EvalM Int
    | [], currentMax => pure currentMax
    | n :: rest, currentMax =>
        maxLoop rest (if n > currentMax then n else currentMax)
  match numbers with
  | [] => .error (Error.illegalInEval "max requires a non-empty collection")
  | first :: rest => do
      let maximum <- maxLoop rest first
      pure (Result.atom maximum, 1)

/-- Evaluate `sum(collection)`.
    `sum` processes top-level sequence items from left to right and adds them
    into one numeric total.

    Each top-level collection element must be exactly one atomic numeric
    value. Sequence values are not flattened or recursively summed, strings
    are rejected, and empty collections return `0`. -/
def evalSumCounted (numbers : List Int) : EvalM CountedResult := do
  let total := numbers.foldl (fun acc n => acc + n) 0
  pure (Result.atom total, 1)

/-- Evaluate `avg(collection)`.
    `avg` processes top-level sequence items from left to right,
    accumulates their numeric total, and divides by the element count.
    The integer core truncates the quotient toward zero (Int.tdiv), matching
    the truncating division convention of `div`/`mod`; the decimal runtime
    rounds the exact fractional average once to Decimal128.

    The collection must be non-empty. Each top-level collection element must
    be exactly one atomic numeric value. Sequence values are not flattened or
    recursively inspected, and strings are rejected. -/
def evalAvgCounted (numbers : List Int) : EvalM CountedResult := do
  match numbers with
  | [] => .error (Error.illegalInEval "avg requires a non-empty collection")
  | values =>
      let total := values.foldl (fun acc n => acc + n) 0
      pure (Result.atom (total.tdiv (Int.ofNat values.length)), 1)

/-- Assemble the argument bundle for extension dot-call fallback: DOT-CALL
    PASSES A VALUE — `receiver.F(C, D)` is exactly the bundle of the written
    call `F(receiver, C, D)`, the ORIGINAL receiver expression as the ordinary
    first argument slot followed by the written extra arguments. Assembly is
    independent of the resolved callee: the receiver is never pre-expanded,
    never unwrapped, never given a supply of its own, and no parameter shape
    is inspected; a spread receiver is the ordinary spread slot `F(R*, …)`.
    Laws: `dot_receiver_is_ordinary_leading_argument`,
    `spread_dot_receiver_is_ordinary_spread_argument` (`KatLangArityLaws.lean`).
    C#: `BuildLexicalReceiverCallArgs`. -/
def prepareLexicalDotCallArgs (receiver : Expr) (extraArgs : Option OutputBundle)
    : OutputBundle :=
  [receiver] ++ extraArgs.getD []


--------------------------------------------------------------------------
-- Open resolution
--------------------------------------------------------------------------

/-- Algorithm resolution using only direct lexical lookup (no opens).
    Used for resolving open expressions to avoid circularity.

    Open resolution wires the resolved head to the scope where direct
    lexical lookup found it — its lexical definition site — and never to
    arbitrary caller context.  This enforces open isolation: a library's
    internal lexical structure is self-contained and never smuggles caller
    context.

    Open restrictions:
    - Only `Expr.openForm?` forms are permitted (structural references to libraries only).
    - Direct lexical heads (`open Name`) use ordinary direct lexical lookup
      (`lookupLexicalDirect`, local properties plus the parent chain, no opens).
      The head may be private if it is lexically visible. This includes the
      common surface form where `open Lib` appears before a later
      `Lib = { ... }` definition in the same algorithm body.
    - A head that a PARAMETER owns never arrives here as `.resolve`: the
      surface layer classifies every open head by the ordinary owner walk
      (`elaborateOpenHead`) and elaborates a parameter-owned head to `.param`,
      which `Expr.openForm?` rejects — so a static open can never bypass an
      established parameter and reach a farther same-named property, and
      nothing is opened dynamically.
    - Builtins are still rejected: even if lexical lookup finds one, it is
      not a valid open target.
    - **Public-path policy**: Qualified property access in open paths
      (e.g., `open Lib.Sub`) still requires each dotted member after the
      direct lexical head to be public. `Algorithm.lookupPublicProp`
      enforces this unchanged rule.
    - Inline/load-elaborated block opens keep isolation from the opener while
      retaining the global call-stack base, which is the builtin prelude in
      normal runs.
    - `open` exposes only public properties of the resolved algorithm.
      Opening an algorithm never makes its private properties visible.

    Examples:
    - `open Lib` where private `Lib` is defined later in the same algorithm body → OK
    - `open Lib.PrivateSub` where `PrivateSub` has `isPublic = false` → Error (notPublicProperty)
    - Structural access `Lib.PrivateSub.X` in code → OK (uses Algorithm.lookupProp, sees private)
    - `open Lib` does NOT expose private properties of Lib (filtered by lookupOpenProperties) -/
def resolveAlgForOpen (e : Expr) (ctx : EvalCtx) : EvalM Algorithm := do
  -- This match mirrors `Expr.openForm?` case-for-case (algorithmExpr /
  -- resolve / no-arg dotCall / reject-the-rest) but matches the
  -- expression directly so the dotted-path recursion is visibly structural.
  -- Keep the two in sync.
  match e with
  | .algorithmExpr a => pure (wireOpenBlockToGlobalScope ctx a)
  -- A capture is a value boundary, never algorithm/namespace identity:
  -- `open` consumes algorithm identity, so a captured target such as
  -- `open (M, N)` is not openable. Top-level capture targets are already
  -- rejected by resolveAllOpens' open-form validation; this arm is reached
  -- through dotted-path recursion (`open (X, Y).B`) and prebuilt ASTs — the
  -- C# front end refuses such a head statically (`BadOpenForm`).
  | .capture _ => throw (Error.badOpenForm "captured value groups cannot be opened")
  | .resolve n =>
    match ctx.callStack with
    | a::_ =>
      match lookupInParentsDirect (scopeInContext a ctx) n with
      | some r =>
          if r.isBuiltin then .error (Error.illegalInOpen s!"builtin '{n}'")
          else pure r
      | none => .error (Error.unknownName n)
    | [] => .error (Error.unknownName n)
  -- Only argumentless dot paths resolve as open targets. Grace-marked open
  -- targets are rejected by the C# front end before Lean encoding.
  | .dotMember o n _ none => do
    let a <- resolveAlgForOpen o ctx
    -- First check if property exists at all so ownership still wins over opens.
    match Algorithm.lookupPropDefAny? a n with
    | some p =>
        if p.alg.isBuiltin then
          .error (Error.illegalInOpen s!"builtin not allowed in open: {openExprName o}.{n}")
        else if !p.isPublic then
          .error (Error.notPublicProperty (openExprName o) n)
        -- Open paths select public members before checking contextual accessibility.
        else if !(memberAccessible? ctx a p) then
          .error (Error.localOnlyProperty (openExprName o) n p.exposure)
        else
          -- Property exists; check if it's public
          match Algorithm.lookupPublicProp a n with
          | some publicAlg => pure (childOfInContext a publicAlg ctx)
          | none   => .error (Error.notPublicProperty (openExprName o) n)
    | none =>
        if Algorithm.conditionalBranchesDefineProperty a n then
          .error (Error.localOnlyProperty (openExprName o) n .localConditional)
        else
          .error (Error.unknownProperty (openExprName o) n)
  -- load('url') is not a core Expr constructor; it is represented as
  -- Call(Resolve("load"), ...) at parse time and elaborated to Block before
  -- open resolution.  If it reaches here un-elaborated, it falls through to
  -- the call/default case below (exactly as `Expr.openForm?` maps it to none).
  | _ =>
      throw (Error.badOpenForm s!"{Expr.kind e}: {openExprName e}")

/-- Resolve an open expression to a library algorithm and apply the PROVIDER rule: the
    resolved provider — the whole target, never an intermediate of a dotted path — must
    need no call (`Algorithm.requiresArguments`). A parameterized algorithm or a clause
    family has no members outside an activation, and `open` never creates one (there is
    no `open Lib(5)`), so it is refused with `illegalInOpen`; a parameterized HEAD of a
    dotted target is navigated by identity like any structural receiver (`open Lib.Sub`
    with `Lib(p)` opens a self-contained `Sub`), and a member of it that captures `p` is
    refused at the access by `memberAccessible?`. C#: `Evaluator.ResolveOpen`. -/
def openTargetRequiresArgumentsMessage (target : String) : Algorithm -> String
  | .conditional _ _ _ _ =>
      s!"'{target}' cannot be opened because it is a clause family that requires arguments; " ++
        "open imports only an algorithm that needs no call."
  | .alias _ _ _ _ _ =>
      s!"'{target}' cannot be opened because it is a callable alias, not a namespace; " ++
        "open imports only an algorithm that needs no call."
  | a =>
      s!"'{target}' cannot be opened because it requires arguments " ++
        s!"({String.intercalate ", " (Algorithm.params a)}); " ++
        "open imports only an algorithm that needs no call."

def resolveOpen (e : Expr) (ctx : EvalCtx) : EvalM Algorithm := do
  let provider <- resolveAlgForOpen e ctx
  if provider.requiresArguments then
    .error (Error.illegalInOpen (openTargetRequiresArgumentsMessage (openExprName e) provider))
  else
    pure provider

/-- The head of an argumentless open path. An argument-bearing edge stops the walk,
    just as it stops open resolution. C#: `AstHelpers.OpenTargetHead`. -/
def Expr.openTargetHead : Expr → Expr
  | .dotMember receiver _ _ none => receiver.openTargetHead
  | e => e

/-- Resolve all opens of an algorithm upfront: the level's PROVIDERS, each counted once.
    Q-19 D-I (decided 2026-10-06): written targets that resolve to the same semantic
    provider count once, whatever their spelling or position — the provider identity is
    the language's one callable identity (`sameRepeatedCallableIdentity`, NEED-04's
    relation: declaration, declaring scope, compatible activations). So `open M, M`,
    `open Sub, Lib.Sub` for one declaration `Sub` of `Lib`, and two loads of one module
    are one provider, while two written blocks or two declarations stay two, however
    equal their members or values. The first occurrence names the provider; which
    providers the level has never depends on order. A repeated written-target key
    (`openExprName`; inline block heads, dotted paths from them included, are keyed by
    position) is skipped before resolution as a pure optimization — it resolves the same
    target. Validates all open expressions first for fail-fast diagnostics.
    C#: `Evaluator.ResolveAllOpens`. -/
def resolveAllOpens (a : Algorithm) (ctx : EvalCtx) : EvalM (List ResolvedOpen) := do
  let rawOpens := Algorithm.opens a
  -- Skip a repeated written-target key (it resolves the same target); inline blocks use
  -- positional keys, so this never merges two written blocks.
  let tagged := rawOpens.mapIdx (fun idx e =>
    let key := match e.openTargetHead with
      | .algorithmExpr _ => s!"(inline#{idx})"   -- * unique per original position
      | .capture _        => s!"(inline#{idx})"
      | _                 => openExprName e
    (key, e))
  let mut seen : List String := []
  let mut acc : List (Prod String Expr) := []
  for (k, e) in tagged do
    if !seen.elem k then
      seen := k :: seen
      acc := (k, e) :: acc
  acc := acc.reverse
  -- Validate all open expressions first (fail-fast with clear errors)
  acc.forM fun (k, e) =>
    if !Expr.isOpenForm e then
      throw (Error.badOpenForm s!"{Expr.kind e}: {k}")
    else
      pure ()
  -- Then resolve (each open wrapped with context using its key), counting each semantic
  -- provider once: a target resolving to the callable identity of an earlier one is that
  -- provider. A provider whose declaration is not identified (a hand-built tree that never
  -- passed the run's identification) is its own provider — C# compares declarations by
  -- reference, so an unidentified declaration is never another's.
  let resolved <- acc.mapM (fun (key, e) => do
    let lib <- withCtx (CtxMsg.openMsg key) (resolveOpen e ctx)
    pure { key := key, expr := e, lib := lib : ResolvedOpen })
  pure (resolved.foldl (fun (providers : List ResolvedOpen) r =>
    if r.lib.declarationId.isSome
        && providers.any (fun p => sameRepeatedCallableIdentity p.lib r.lib) then providers
    else providers ++ [r]) [])

/-- Lookup in opened namespaces with ambiguity error — the ONE open-lookup
    implementation in the ownership-first chain. It returns the full
    `ResolvedProperty` (owner + binding + wired algorithm) because the cached
    property-style path needs the binding; algorithm-only consumers project
    `ResolvedProperty.alg` instead of running a second lookup.
    Ordering rule: opens are searched in declaration order (first wins for
    single-provider lookups; multiple providers trigger ambiguousOpen).
    Only public properties are visible through opens.
    Returns:
      * ok none              if no open provides `name` publicly
      * ok (some prop)       if exactly one open provides it publicly (alg wired to library parent)
      * error ambiguousOpen if multiple opens provide it publicly -/
def lookupOpenProperties (a : Algorithm) (name : Ident) (ctx : EvalCtx)
    : EvalM (Option ResolvedProperty) := do
  let ctx' := { ctx.push a with headScope := some (scopeInContext a ctx) }
  let resolvedOpens <- resolveAllOpens a ctx'
  let mut hits : List OpenPropertyHit := []
  for ri in resolvedOpens do
    match Algorithm.lookupPropDefPublic? ri.lib name with
    | some prop =>
        hits := {
          provider := ri.key,
          property := {
            owner := ri.lib,
            binding := prop,
            alg := childOfInContext ri.lib prop.alg ctx
          }
        } :: hits
    | none => pure ()
  hits := hits.reverse

  -- SELECTION IS BY VISIBILITY ONLY: a public member is provided by its open whatever its
  -- exposure (it takes part in precedence and ambiguity like any provided name), and
  -- accessibility is checked on the selected member afterwards, from the site — the
  -- algorithm whose body reads the name (the original context's head), not the level
  -- whose opens are consulted. Which declaration a name selects therefore never depends
  -- on exposure, which is what lets the surface layer reproduce the selection before
  -- exposure is classified.
  match hits with
  | [] => pure none
  | [h] =>
      if memberAccessible? ctx h.property.owner h.property.binding then
        pure (some h.property)
      else
        .error (Error.localOnlyProperty h.provider name h.property.binding.exposure)
  | hs => .error (Error.ambiguousOpen name (hs.map (fun hit => hit.provider)))

--------------------------------------------------------------------------
-- Lexical resolution
--------------------------------------------------------------------------

/-- Structural-only lookup in parent chain (no opens anywhere).
    Ownership-first model: structural properties take precedence.
    Example: If parent defines Pi and opens Math also exports Pi,
    the parent's Pi wins. To get Math.Pi, use Math.Pi syntax.
    This is the ONE structural parent-chain lookup; algorithm-only consumers
    project `ResolvedProperty.alg`. -/
def lookupInParentsStructuralProperty (sc : ScopeCtx) (name : Ident)
    : Option ResolvedProperty :=
  match lookupPropDefAny? (ScopeCtx.props sc) name with
  | some prop =>
      -- The binding belongs to sc itself. `forOpens sc` is a lookup wrapper
      -- whose PARENT is sc; using it as owner adds a spurious scope level to
      -- the property key, splitting an ancestor read from a direct read.
      -- The owner rebuilt from the level carries the level's own parameters, so its
      -- `asScopeCtx` — the cache key's owner identity — equals the declaring
      -- algorithm's own.
      let owner := match sc with
        | .mk parent params opens props output _ _ id =>
            Algorithm.mk parent (Algorithm.normalParameters params) opens props output id
      some {
        owner := owner,
        binding := prop,
        alg := Algorithm.withParent (some sc) prop.alg
      }
  | none =>
      match sc with
      | .mk (some sc') _ _ _ _ _ _ _ => lookupInParentsStructuralProperty sc' name
      | .mk none _ _ _ _ _ _ _       => none

/-- Open-based lookup in parent chain (helper for lookupOpenPropertiesInChain). -/
def lookupOpenPropertiesInParentChain (sc : ScopeCtx) (name : Ident)
    (ctx : EvalCtx) : EvalM (Option ResolvedProperty) := do
  let tempAlg := Algorithm.forOpens sc
  match (<- lookupOpenProperties tempAlg name ctx) with
  | some r => pure (some r)
  | none =>
      match sc with
      | .mk (some sc') _ _ _ _ _ _ _ => lookupOpenPropertiesInParentChain sc' name ctx
      | .mk none _ _ _ _ _ _ _       => pure none

/-- Open-based lookup across the algorithm chain (current first, then parents).
    Checks opens at each level of the parent chain as fallback. -/
def lookupOpenPropertiesInChain (a : Algorithm) (name : Ident)
    (ctx : EvalCtx) : EvalM (Option ResolvedProperty) := do
  match (<- lookupOpenProperties a name ctx) with
  | some r => pure (some r)
  | none =>
      match Algorithm.parent a with
      | some sc => lookupOpenPropertiesInParentChain sc name ctx
      | none    => pure none

/-- Full lexical lookup with ownership-first model — the CANONICAL chain:
    1. Local properties (owned by this algorithm)
    2. Parent chain structural properties (owned by ancestors)
    3. Opens as fallback (foreign namespaces)

    This ensures structural ownership always takes precedence over opens.
    It keeps the resolved owner and binding for the zero-argument property
    cache; `lookupLexical` is its algorithm projection, so the
    ownership-first / dedup / ambiguity rules exist exactly once. The selected
    binding is returned RAW — an alias as the alias — for the consumers that
    navigate a binding's OWN declarations (a written dot receiver,
    `resolveDotReceiver`) and for alias resolution itself (`resolveAliasStep`);
    every other consumer reads it through `lookupLexicalProperty`, which makes
    it callable. C#: `Evaluator.LookupLexicalRaw`. -/
def lookupLexicalPropertyRaw (a : Algorithm) (name : Ident) (ctx : EvalCtx)
    : EvalM ResolvedProperty := do
  match Algorithm.lookupPropDefAny? a name with
  | some prop =>
      pure {
        owner := a,
        binding := prop,
        alg := childOfInContext a prop.alg ctx
      }
  | none =>
      match Algorithm.parent a with
      | some sc =>
          match lookupInParentsStructuralProperty sc name with
          | some r => pure r
          | none =>
              match (<- lookupOpenPropertiesInChain a name ctx) with
              | some r => pure r
              | none   => .error (Error.unknownName name)
      | none =>
          match (<- lookupOpenPropertiesInChain a name ctx) with
          | some r => pure r
          | none   => .error (Error.unknownName name)

/-- One STEP of `resolveAliasTarget`: the callable the alias `step`'s written `target` names
    in the alias's OWN scope — the alias pushed as the head, exactly where its body would be
    evaluated: a name by the ownership-first lexical lookup, RAW, so a target that is itself an
    alias continues the chase; a member path by structural navigation of DECLARED members, each
    member wired to its receiver and checked for accessibility from the alias's site exactly
    like `resolveDotReceiver` navigates (a member declared only in branches is the same
    `localOnlyProperty` error). A target that is not a static path, or a path step whose
    receiver declares no such member, has no callable: `illegalInEval` — only a host-built tree
    has either, since the surface pass forms an alias over a statically known member only.
    C#: `Evaluator.ResolveAliasStep`. -/
def resolveAliasStep (step : Algorithm) (target : Expr) (ctx : EvalCtx) : EvalM Algorithm := do
  let stepCtx := ctx.push step
  let notStatic : Error := Error.illegalInEval (aliasTargetNotStaticPathMessage (openExprName target))
  match Expr.staticAliasPath? target with
  | none => .error notStatic
  | some (head, steps) =>
      let start : Algorithm × String <- match head with
        | .resolve name => do
            let resolved <- lookupLexicalPropertyRaw step name stepCtx
            pure (resolved.alg, name)
        | .algorithmExpr block => pure (wireToCaller stepCtx block, openExprName head)
        | _ => .error notStatic
      let navigated <- steps.foldlM
        (fun (current : Algorithm × String) (member : Ident) =>
          let (receiver, receiverName) := current
          match Algorithm.lookupPropDefAny? receiver member with
          | some p =>
              if !(memberAccessible? stepCtx receiver p) then
                .error (Error.localOnlyProperty receiverName member p.exposure)
              else
                pure (childOfInContext receiver p.alg stepCtx, receiverName ++ "." ++ member)
          | none =>
              if Algorithm.conditionalBranchesDefineProperty receiver member then
                .error (Error.localOnlyProperty receiverName member .localConditional)
              else
                .error notStatic)
        start
      pure navigated.fst

/-- THE ONE NORMALIZATION (FWD-02, binding indirection; decided 2026-10-01):
    `ResolveCallable(A) = A is an alias ? ResolveCallable(target of A, resolved in A's own
    scope) : A`. Every place a binding becomes a CALLABLE goes through it — lexical lookup
    (`lookupLexicalProperty`), a structurally navigated member, an inline block — so calls,
    callbacks and loop steps, the callable channel of an argument, and value demands all
    receive the TARGET, while the BINDING — the property and its zero-argument cache key
    (`zeroArgPropertyCacheKey` reads the binding, never the resolved algorithm) — stays the
    alias's own. An alias is never an invocation: resolving it binds nothing, opens no
    binding context and charges nothing. A chase that reaches an alias of the same shape in
    the same scope again (`cacheAlgorithmShape`: the chase is deterministic in the shape) is a
    CYCLE, which only a host-built tree can form past the pre-evaluation check
    (`staticAliasCycle`): `illegalInEval aliasCycleMessage`, never a non-terminating chase.
    C#: `Evaluator.ResolveAliasTarget`. -/
partial def resolveAliasTarget (a : Algorithm) (ctx : EvalCtx) (visited : List String := []) : EvalM Algorithm :=
  match a with
  | .alias _ _ _ target _ => do
      let key := reprStr (cacheAlgorithmShape a)
      if visited.contains key then
        .error (Error.illegalInEval aliasCycleMessage)
      else
        let next <- resolveAliasStep a target ctx
        resolveAliasTarget next ctx (key :: visited)
  | other => pure other

/-- The canonical lexical lookup with the selected binding made CALLABLE: a binding that is a
    callable alias keeps its own property as the binding (its zero-argument cache key, its
    exposure and accessibility) while its resolved algorithm is the alias's normalized target
    (`resolveAliasTarget`). C#: `Evaluator.LookupLexical` (over `NormalizeAliasBinding`). -/
def lookupLexicalProperty (a : Algorithm) (name : Ident) (ctx : EvalCtx)
    : EvalM ResolvedProperty := do
  let resolved <- lookupLexicalPropertyRaw a name ctx
  match resolved.alg with
  | .alias _ _ _ _ _ => pure { resolved with alg := (<- resolveAliasTarget resolved.alg ctx) }
  | _ => pure resolved

/-- Algorithm-position lexical lookup (call callees, dot-call targets).
    This is the algorithm PROJECTION of `lookupLexicalProperty`: the canonical
    property-carrying chain owns ownership-first ordering, open dedup,
    ambiguity, and precedence, and this projection only discards the
    owner/binding metadata that algorithm-position consumers never read. -/
def lookupLexical (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM Algorithm := do
  let resolved <- lookupLexicalProperty a name ctx
  pure resolved.alg

/-- Runtime-created callable wrappers have identities too. C# mints a DeclarationIdentity
    on every new Algorithm.User; retaining this token through parameter forwarding makes
    one wrapper forwarded twice different from two separately resolved dot results. -/
def identifyRuntimeAlgorithm (algorithm : Algorithm) : EvalM Algorithm := do
  let state <- get
  set { state with nextRuntimeDeclaration := state.nextRuntimeDeclaration + 1 }
  pure (algorithm.withDeclarationId (some (.runtime state.nextRuntimeDeclaration)))

mutual
partial def resolveAlg (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  match e with
  | .sequenceConstruct _ _ =>
    .error (Error.notAnAlgorithm "sequence construct expression")
  | .sequenceSpread _ =>
    .error (Error.notAnAlgorithm "spread expression")
  -- An inline block whose one row names a parameterized callable is a callable alias
  -- (`{ F }`): its callable is its target's.
  | .algorithmExpr a => resolveAliasTarget (wireToCaller ctx a) ctx
  -- Capture is not algorithm identity: the algorithm channel sees only a
  -- zero-parameter value thunk over the bundle, exactly as the pre-split
  -- transparent wrapper behaved. `Apply((Inc, Dec))` therefore never receives
  -- either callable identity: a capture ARGUMENT has no CALLABLE channel at all
  -- (`projectNeedCallable` declines it through `shouldWrapArgExprAsValue`), so
  -- `f(9)` is `notAnAlgorithm` (Q-06, NEED-06), while
  -- the redundant group `Apply((Increment))` IS `Apply(Increment)` — the
  -- parser erases it before this node exists (parentheses group syntax).
  -- C#: `CaptureValueThunk`.
  | .capture rows => identifyRuntimeAlgorithm (wireToCaller ctx (Algorithm.mk none [] [] [] rows))
  | .resolve n =>
      match ctx.callStack with
      | a::_ => lookupLexical a n ctx
      | []   => .error (Error.unknownName n)
  | .dotMember o n fallback args =>
      -- The internal CARRIER of a dot RESULT used as a RECEIVER: a memberless
      -- wrapper whose evaluation (evalDotCall) owns every dot semantic
      -- (structural member, `.string` intrinsic, extension call). The whole
      -- node — including its elaborated fallback identity — rides along
      -- unchanged. Its only consumer is `resolveDotReceiver` below, where a
      -- structural miss or an argument-bearing edge is a VALUE (DOT-02); it is
      -- never a program-visible callable — every algorithm-capable position,
      -- the callee included, reads a dot expression's identity through
      -- `projectNeedStructuralMember` (DOT-09; `projectNeedCallable`,
      -- `resolveCalleeAlg`).
      identifyRuntimeAlgorithm (wireToCaller ctx (Algorithm.ofExpr (.dotMember o n fallback args)))
  -- Explicit errors for syntactic forms that cannot resolve to algorithms
  | .param x =>
      -- Higher-order parameter: if x is bound in AlgEnv, return the algorithm.
      -- The environment reaching here was shadowed by every enclosing
      -- binding's parameter names (`EvalCtx.bindParameters`), so a parameter
      -- bound only on the value channel finds NO entry and fails as
      -- not-callable instead of reaching a same-named caller callable.
      do
      let activation <- capturedParameterActivation? x ctx
      if let some address := lookupAssoc x (activation.map ParameterActivation.needs |>.getD ctx.needEnv) then
        match <- projectNeedCallable address with
        | some algorithm => return algorithm
        | none => return <- .error (Error.notAnAlgorithm s!"param({x})")
      match (activation.map ParameterActivation.algorithms |>.getD ctx.algEnv).lookup x with
      | some alg => pure alg
      | none     => .error (Error.notAnAlgorithm s!"param({x})")
  | .num n   => .error (Error.notAnAlgorithm s!"num({n})")
  | .emptySequence _ => .error (Error.notAnAlgorithm "empty sequence value")
  | .listLiteral _ => .error (Error.notAnAlgorithm "list literal")
  | .unary _ _ => .error (Error.notAnAlgorithm "unary expression")
  | .binary _ _ _ => .error (Error.notAnAlgorithm "binary expression")
  | .comparison _ _ => .error (Error.notAnAlgorithm "comparison expression")
  | .index _ _ => .error (Error.notAnAlgorithm "index expression")
  | .call _ _ => .error (Error.notAnAlgorithm "call expression")
  | .stringLiteral _ => .error (Error.notAnAlgorithm "string literal")
  | .boolLiteral _ => .error (Error.notAnAlgorithm "Boolean literal")

/-- Project identity without a VALUE demand or an invocation. -/
partial def projectNeedCallable (address : Nat) : EvalM (Option Algorithm) := do
  let state <- get
  let some cell := state.needs[address]? | throw (Error.illegalInEval "invalid need address")
  if let some outcome := cell.callable then
    return <- outcome
  let outcome <- evalAttempt <| match cell.suspension with
    | .ready _ => pure none
    | .collector _ => pure none
    | .expression source caller _ => do
      if shouldWrapArgExprAsValue source then return none
      if let .dotMember _ _ _ _ := source then
        let selected <- projectNeedStructuralMember source caller
        match selected with
        | some algorithm => pure (some (<- resolveAliasTarget algorithm caller))
        | none => pure none
      else
        match <- evalAttempt (resolveAlg source caller) with
        | .ok algorithm => pure (some algorithm)
        | .error err => if isLiftableArgResolutionError err then pure none else throw err
  modify fun current => { current with needs := (current.needs.modify address (fun currentCell => { currentCell with callable := some outcome })) }
  return <- outcome

/-- Identity-only structural navigation: THE ONE CALLABLE PROJECTION of a dot
    expression (DOT-09), shared by a supplied argument (`projectNeedCallable`, NEED-06)
    and a callee (`resolveCalleeAlg`, Q-18 C-B3). An argumentless path whose every edge
    selects a DECLARED member — a member named `string` included (Q-17 S-C) — is that
    member (accessibility checked after selection); a computed dot result (an
    argument-bearing edge, a structural miss) has no callable channel, and resolving a
    receiver must not mint a value-thunk identity. C#: `ProjectDotPathCallable`. -/
partial def projectNeedStructuralMember (source : Expr) (ctx : EvalCtx) : EvalM (Option Algorithm) := do
  match source with
  | .dotMember receiver name _ none =>
      let container <- projectNeedStructuralMember receiver ctx
      let some algorithm := container | return none
      match Algorithm.lookupPropDefAny? algorithm name with
      | some property =>
          if !(memberAccessible? ctx algorithm property) then
            throw (Error.localOnlyProperty (openExprName receiver) name property.exposure)
          pure (some (childOfInContext algorithm property.alg ctx))
      | none =>
          if Algorithm.conditionalBranchesDefineProperty algorithm name then
            throw (Error.localOnlyProperty (openExprName receiver) name .localConditional)
          return none
  | .resolve name =>
      match ctx.callStack with
      | owner :: _ => pure (some (<- lookupLexicalPropertyRaw owner name ctx).alg)
      | [] => throw (Error.unknownName name)
  | .algorithmExpr algorithm => pure (some (wireToCaller ctx algorithm))
  | .param _ =>
      match <- evalAttempt (resolveAlg source ctx) with
      | .ok algorithm => pure (some algorithm)
      | .error (.notAnAlgorithm _) => pure none
      | .error error => throw error
  | _ => pure none
end

/-- The structured `notAnAlgorithm` description of a dot expression in CALLEE position
    that carries no callable identity — a computed VALUE (an extension call's or the
    `.string` intrinsic's result, a call result). C#: `Evaluator.ComputedDotCalleeDescription`. -/
def computedDotCalleeDescription : String := "dot result"

/-- The CALLABLE a call's CALLEE carries (DOT-09; Q-18 C-B3). A dot expression carries ONE
    callable identity in every algorithm-capable position, so a dot callee is read through
    the SAME projection a supplied argument is (`projectNeedStructuralMember`, then alias
    normalization — exactly `projectNeedCallable`'s dot arm): an argumentless structural
    path is its member's own callable — `(Box.G)(2)` is the member call `Box.G(2)` and
    `(Box.V)()` the explicit fresh call `Box.V()`, grouping never changing identity — and
    every other dot expression is a computed value with no callable identity. Every other
    callee shape resolves through canonical `resolveAlg`. C#: `Evaluator.ResolveCallee`. -/
def resolveCalleeAlg (f : Expr) (ctx : EvalCtx) : EvalM Algorithm := do
  match f with
  | .dotMember _ _ _ _ =>
      match <- projectNeedStructuralMember f ctx with
      | some algorithm => resolveAliasTarget algorithm ctx
      | none => .error (Error.notAnAlgorithm computedDotCalleeDescription)
  | _ => resolveAlg f ctx

/-- The ROLE of a builtin's invoking (CALLABLE) slot — its callback, or a
    loop's step: the description of the slot's missing-callability verdict
    (Q-06), a structured semantic description and never a fake zero-parameter
    callable. The per-item invocation frames keep their own names ("filter
    predicate", "map transform", "reduce step").
    C#: `Evaluator.InvokingSlotRoles.Of`. -/
def invokingSlotRole : Builtin -> String
  | .mapBuiltin => "map transform"
  | .filterBuiltin => "filter predicate"
  | .reduceBuiltin => "reduce reducer"
  | .repeatBuiltin => "repeat step"
  | .whileBuiltin => "while step"
  | b => s!"{builtinDisplayName b} callback"

/-- CALLABLE projection of ONE invoking builtin slot — a collection builtin's
    callback (the `filter` predicate, the `map` transform, the `reduce`
    reducer) or a `while`/`repeat` step — made only when the builtin is about
    to invoke it, so an unused invoking slot is never projected or validated
    (CALL-03, LOOP-05). It reads the slot's callable identity alone and never
    demands its VALUE (NEED-06): a slot with no CALLABLE identity is
    `notAnAlgorithm` described by the slot's role (Q-06), the verdict a user
    higher-order parameter reports, raised before any invocation. A slot that
    HAS callable identity keeps every ordinary binder verdict when it is
    invoked. C#: `Evaluator.ProjectInvokingSlot`. -/
def projectInvokingSlot (role : String) : Option Algorithm -> EvalM Algorithm
  | some algorithm => pure algorithm
  | none => .error (Error.notAnAlgorithm role)

partial def expectPreparedSequenceBuiltinAlgorithmSuffixArg
    (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor)
    (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) : EvalM Algorithm :=
  expectPreparedSequenceBuiltinSuffixArgAt b descriptors args index .algorithm fun descriptor arg =>
    match arg with
    | .needAlgorithm address => do
        projectInvokingSlot (invokingSlotRole b) (<- projectNeedCallable address)
    | .algorithm algorithm callable? =>
        projectInvokingSlot (invokingSlotRole b)
          (some ({ algorithm := algorithm, callable? := callable? } : ResolvedArgumentAlgorithm).invoked)
    | _ =>
        internalSequenceBuiltinSuffixArgMetadataError b
          s!"prepared suffix argument {index + 1} ({descriptor.name}) did not match metadata kind {sequenceBuiltinSuffixArgKindDesc .algorithm}"

/-- Resolve a dot edge's RECEIVER in algorithm position — the structural half
    of the ordinary DotCall law applied at EVERY level of a chain.

    Every receiver shape resolves through canonical `resolveAlg` except an
    argumentless dot edge `X.M`, which NAVIGATES: when `X` (resolved the same
    way, recursively) is an algorithm that declares `M` (any visibility;
    selection never depends on exposure), the receiver IS that member algorithm
    wired to `X` (`childOfInContext`), so `Lib.Sub.Q` reads `Sub`'s own `Q`
    before any lexical `Q(x)` is considered, exactly as `Lib.Q` reads `Lib`'s.
    A member named `string` is navigated like any member (Q-17 S-C:
    `Obj.string.Q` reads the declared `string`'s own `Q`). A declared `M` that
    is inaccessible from the site (`memberAccessible?`), or one defined only
    inside conditional branches, is the same structural error that evaluating
    `X.M` itself reports — never a fallback. When `X` does not declare `M` (or
    is not an algorithm at all), the edge is an ordinary dot RESULT — its
    lexical fallback's value, or, for `string`, the intrinsic's text — and
    resolves to `resolveAlg`'s memberless wrapper, the internal carrier of that
    VALUE, so the chain continues by value (`3.A.B` stays `B(A(3))`). An
    argument-bearing edge is a call, hence a value, and never navigates; a
    capture receiver keeps suppressing structural identity (`(A, B).V` and
    `(A*).V` fall back — a redundant group never reaches this node, so the
    sources `(Obj).V` and `(Lib.Sub).Q` are simply `Obj.V` and `Lib.Sub.Q`:
    parentheses group syntax and never change which receiver is navigated).

    The resolution is identity navigation only: no intermediate edge is
    evaluated, so a parameterized or output-less container navigates exactly
    as it does at the first level (`F.Q` works while `F` alone is an arity or
    missing-output error). A dot expression's CALLABLE identity is read by
    `projectNeedStructuralMember` alone (DOT-09). C#: `ResolveDotReceiver`. -/
def resolveDotReceiver (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  match e with
  | .dotMember o n _ none =>
      do
        match <- evalAttempt (resolveDotReceiver o ctx) with
        | .ok a =>
            match Algorithm.lookupPropDefAny? a n with
            | some p =>
                if !(memberAccessible? ctx a p) then
                  .error (Error.localOnlyProperty (openExprName o) n p.exposure)
                else
                  pure (childOfInContext a p.alg ctx)
            | none =>
                if Algorithm.conditionalBranchesDefineProperty a n then
                  .error (Error.localOnlyProperty (openExprName o) n .localConditional)
                else
                  -- Structural miss: the edge is an ordinary dot result.
                  resolveAlg e ctx
        -- A value receiver makes the edge an ordinary dot result too.
        | .error (.notAnAlgorithm _) => resolveAlg e ctx
        | .error err => .error err
  -- A written receiver HEAD is navigated, so a name or a block is the binding's own
  -- algorithm, RAW: an alias declares only its own members, never its target's — written
  -- member access never follows an alias (FWD-02). C#: `Evaluator.ResolveReceiverHead`.
  | .resolve n =>
      match ctx.callStack with
      | a :: _ => do
          let resolved <- lookupLexicalPropertyRaw a n ctx
          pure resolved.alg
      | [] => .error (Error.unknownName n)
  | .algorithmExpr a => pure (wireToCaller ctx a)
  | _ => resolveAlg e ctx


/-- Transport builtin arguments as suspended cells, retaining written source and spread markers.
    Ordinary arguments do no value evaluation or callable probing during formation. -/
def resolveArgAlgsWithSequenceSpread (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    : EvalM (List ResolvedArgumentAlgorithm) :=
  args.mapM (fun e => do
    let address <- supplyNeed e ctx env
    pure { algorithm := Algorithm.ofExpr e, need? := some address,
           spreadsSequence := match e with | .sequenceSpread _ => true | _ => false,
           source? := some e })

/-
Evaluator recursion core.

Everything above this point is helper logic that never re-enters evaluation:
validation, name/open/lexical resolution, parameter-pattern binding,
argument-shape preparation, cache-key construction, and pure builtin
computations — checked as ordinary total definitions wherever Lean can see
termination.

This mutual block intentionally contains only functions that participate in
runtime evaluation recursion, plus thin wrappers used by those functions.
Its members are `partial` because KatLang programs may be recursively
defined, so evaluation is not structurally recursive over syntax alone; a
total version would require an explicit fuel/step-indexed evaluator.

Do not add non-evaluating helpers here — define them above this block so
Lean checks them as total definitions.

PLAIN/COUNTED OWNERSHIP: for every plain/counted evaluator pair the COUNTED
implementation is canonical and the plain implementation is its value
projection (`.fst` of the counted result) — `eval` projects `evalCounted`,
`evalUserCall`/`evalConditionalCall`/`evalResolvedCall`/`evalCallExpr`/
`evalDotCall`/`applyBuiltin`/`applyBuiltinResolved`/`evalAlgOutputCore`/
`evalCaptureValue`/`evalZeroArgPropertyAccess`/`evalResolvedCallbackCall`
project their counted twins. `evalCounted` therefore matches EVERY `Expr`
variant explicitly, with no default arm delegating back to `eval`: the
exhaustive match is the structural guard that a new variant cannot silently
reintroduce reverse (plain-owned) semantics. Plain projections may still be
CALLED from counted code wherever only the value of a subexpression or an
algorithm output is needed — that is a value-boundary read through the
projection, not an ownership reversal, and it recurses only into strictly
smaller work. The one intentionally non-projected sibling family is the
slot-view group (`evalAlgOutputSlots`, `evalExplicitSequenceValue*`), which
returns item lists rather than one counted value.
-/
/-- One inspecting-pattern language shared by ordinary calls, families and callbacks. -/
inductive NeedPattern where
  | bind (name : Ident) (collecting : Bool := false)
  | sequence (items : List NeedPattern)
  | list (items : List NeedPattern)
  | unpack (items : List NeedPattern)
  | literal (pattern : Pattern)
  deriving Repr

def NeedPattern.ofParameter : ParameterPattern -> NeedPattern
  | .capture p => .bind p.name (p.kind == .collecting)
  | .sequenceValue ps => .sequence (ps.map ofParameter)
  | .listValue ps => .list (ps.map ofParameter)
  | .unpacking ps => .unpack (ps.map ofParameter)

def NeedPattern.ofClause : Pattern -> NeedPattern
  | .bind name => .bind name
  | .sequenceValue ps => .sequence (ps.map ofClause)
  | .listValue ps => .list (ps.map ofClause)
  | pattern => .literal pattern

def NeedPattern.toParameter : NeedPattern -> ParameterPattern
  | .bind name collecting => .capture { name := name, kind := if collecting then .collecting else .normal }
  | .sequence ps => .sequenceValue (ps.map toParameter)
  | .list ps => .listValue (ps.map toParameter)
  | .unpack ps => .unpacking (ps.map toParameter)
  | .literal _ => .capture { name := "_" }

def NeedPattern.names : NeedPattern -> List Ident
  | .bind name _ => [name]
  | .sequence ps | .list ps | .unpack ps => ps.flatMap names
  | .literal _ => []

def NeedPattern.isCollecting : NeedPattern -> Bool
  | .bind _ collecting => collecting
  | _ => false

def needMinimumSuppliedSlots (patterns : List NeedPattern) : Nat :=
  patterns.length - (patterns.filter NeedPattern.isCollecting).length

def needAcceptsCardinality (patterns : List NeedPattern) (count : Nat) : Bool :=
  count >= needMinimumSuppliedSlots patterns &&
    (patterns.any NeedPattern.isCollecting || count == patterns.length)

def needClauseHead : Pattern -> List NeedPattern
  | .sequenceValue ps => ps.map NeedPattern.ofClause
  | pattern => [NeedPattern.ofClause pattern]

mutual

  /-- First VALUE demand evaluates once and stores success or ordinary failure.
      Re-entering an evaluating cell is a language error, independent of stack depth. -/
  partial def demandNeed (address : Nat) : EvalM CountedResult := do
    let some cell := (<- get).needs[address]? | throw (Error.illegalInEval "invalid need address")
    match cell.state with
    | .completed outcome => return <- outcome
    | .evaluating => throw Error.demandCycle
    | .suspended =>
      modify fun state => { state with needs := (state.needs.modify address (fun current => { current with state := .evaluating })) }
      let outcome <- evalAttempt <| match cell.suspension with
        | .ready value => pure value
        | .expression source caller values => reCountValueBoundary <$> evalCounted source caller values
        | .collector slice => do
          let values <- slice.mapM (fun element => Prod.fst <$> demandNeed element)
          pure (makeCollectionListResult values)
      modify fun state => { state with needs := (state.needs.modify address (fun current => { current with state := .completed outcome })) }
      return <- outcome

  /-- Supply formation only opens spreads. Known collecting slices transport addresses. -/
  partial def formNeedSupply (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM (List Nat) := do
    let rec go : List Expr -> EvalM (List Nat)
      | [] => pure []
      | source :: rest => do
        let head <- match source with
          | .sequenceSpread operand => do
            let address <- supplyNeed operand ctx env
            let some cell := (<- get).needs[address]? | throw Error.badArity
            match cell.suspension with
            | .collector slice => pure slice
            | _ => do
              let opened <- evalCounted source ctx env
              (countedTopLevelValues opened).mapM (fun value => readyNeed (value, Result.valueCount value))
          | _ => do pure [<- supplyNeed source ctx env]
        let tail <- go rest
        pure (head ++ tail)
    go args

  partial def bindNeedName (name : Ident) (address : Nat) (repeated : List Ident)
      (bound : NeedEnv) (family : Bool) : EvalM (Option NeedEnv) := do
    if repeated.contains name then
      let value <- demandNeed address
      if let some previous := lookupAssoc name bound then
        let before <- demandNeed previous
        if !(before == value) then
          if family then return none
          else throw (Error.withContext (repeatedParameterContext name) Error.badArity)
        let first <- projectNeedCallable previous
        let second <- projectNeedCallable address
        if let some a := first then
          if let some b := second then
            if !sameRepeatedCallableIdentity a b then
              if family then return none
              else throw (Error.typeMismatch "Repeated bind equality requires the same callable identity")
        if first.isSome || second.isNone then return some bound
    pure (some (bound.filter (fun entry => entry.fst != name) ++ [(name, address)]))

  partial def bindNeedOne (pattern : NeedPattern) (address : Nat) (repeated : List Ident)
      (bound : NeedEnv) (family : Bool) : EvalM (Option NeedEnv) := do
    if let .bind name _ := pattern then return <- bindNeedName name address repeated bound family
    let (value, _) <- demandNeed address
    match pattern with
    | .bind _ _ => throw Error.badArity
    | .literal literal => pure (if (matchPattern literal value).isSome then some bound else none)
    | .sequence ps | .list ps | .unpack ps =>
      let items? := match pattern with
        | .list _ => Result.listPatternItems? value
        | .sequence _ => Result.sequencePatternItems? value
        | _ => some (Result.spreadItems value)
      match items? with
      | none => if family then pure none else throw (structuralPatternKindMismatch pattern.toParameter value)
      | some items => do
        let cells <- items.mapM (fun item => readyNeed (item, Result.valueCount item))
        bindNeedLevel ps cells repeated bound family

  partial def bindNeedLevel (patterns : List NeedPattern) (cells : List Nat)
      (repeated : List Ident) (bound : NeedEnv) (family : Bool) : EvalM (Option NeedEnv) := do
    if !needAcceptsCardinality patterns cells.length then
      if family then return none
      else throw (Error.arityMismatch (needMinimumSuppliedSlots patterns) cells.length)
    let collector? := patterns.findIdx? NeedPattern.isCollecting
    let extra := cells.length + 1 - patterns.length
    let rec go : List NeedPattern -> Nat -> NeedEnv -> EvalM (Option NeedEnv)
      | [], _, current => pure (some current)
      | pattern :: rest, index, current => do
        let address <- if collector? == some index then
          allocateNeed (.collector ((cells.drop index).take extra))
        else
          match cells[if (collector?.map (fun i => decide (index > i))).getD false then index + extra - 1 else index]? with
          | some address => pure address
          | none => throw Error.badArity
        match <- bindNeedOne pattern address repeated current family with
        | none => pure none
        | some next => go rest (index + 1) next
    go patterns 0 bound

  partial def bindNeedPatterns (patterns : List NeedPattern) (cells : List Nat)
      (family : Bool := false) : EvalM (Option NeedEnv) := do
    let names := patterns.flatMap NeedPattern.names
    let repeated := names.eraseDups.filter (fun name => (names.filter (· == name)).length > 1)
    bindNeedLevel patterns cells repeated [] family

  partial def needBindingContext (ctx : EvalCtx) (bindings : NeedEnv) : EvalM EvalCtx := do
    let names := bindings.map Prod.fst
    let next <- ctx.bindParameters names [] []
    pure { next with needEnv := bindings ++ next.needEnv }

  /-- A user algorithm invoked over an already formed cell supply. Its result is the
      call's value boundary (VAL-06): ONE value, re-counted — for an ordinary call and a
      `map`/`filter`/`reduce` callback invocation alike (HO-03, Q-25 resolved October
      2026: a callback invocation IS the ordinary call). C#: `EvalNeedUserSupply`. -/
  partial def evalNeedUserSupply (callee : Algorithm) (cells : List Nat)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let patterns := (Algorithm.parameterPatterns callee).map NeedPattern.ofParameter
    let some bindings <- bindNeedPatterns patterns cells | throw Error.badArity
    if (Algorithm.output callee).isEmpty then throw Error.missingOutput
    let next <- needBindingContext ctx bindings
    let result <- evalAlgOutputCounted callee next (ValEnv.shadow env (Algorithm.params callee))
    pure (reCountValueBoundary result)

  /-- The ordinary clause-family dispatcher over an already formed cell supply: the
      duplicate-pattern check, the family's cardinality, then the clauses in WRITTEN
      order, each attempt inspecting the SAME cells through the one binder in family
      mode (a successful mismatch tries the next clause; a runtime failure during
      inspection aborts dispatch; no clause is `noMatchingBranch`), and finally the
      selected branch's activation. It returns the activated body, its context and
      its values WITHOUT evaluating it, so each receiver reads the body its own way:
      the ordinary call as one value (`evalNeedFamilySupply`), a loop step as its
      row supply (`runNeedStepSlots`, LOOP-08). C#: `BindNeedFamilySupply`. -/
  partial def selectNeedFamilyBranch (callee : Algorithm) (cells : List Nat)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String) : EvalM (Algorithm × EvalCtx × ValEnv) := do
    if callee.hasDuplicateBranchPatterns then throw Error.duplicateBranchPattern
    let branches := Algorithm.branches callee
    if !branches.any (fun branch => needAcceptsCardinality (needClauseHead branch.pattern) cells.length) then
      throw (Error.arityMismatch ((branches.head?.map (fun branch => needMinimumSuppliedSlots (needClauseHead branch.pattern))).getD 0) cells.length)
    let rec choose : List CondBranch -> EvalM (Algorithm × EvalCtx × ValEnv)
      | [] => throw (Error.noMatchingBranch calleeName)
      | branch :: rest => do
        match <- bindNeedPatterns (needClauseHead branch.pattern) cells true with
        | none => choose rest
        | some bindings => do
          let names := bindings.map Prod.fst
          let next <- needBindingContext (ctx.push callee) bindings
          let values := ValEnv.shadow env names
          let body <- wireSelectedBranchBody callee branch.body names next values
          pure (body, next, values)
    choose branches

  /-- A clause family invoked over an already formed cell supply: ordinary dispatch, then
      the selected body's output at the call's value boundary — for an ordinary call and a
      callback invocation alike (HO-03, PAT-11). C#: `EvalNeedFamilySupply`. -/
  partial def evalNeedFamilySupply (callee : Algorithm) (cells : List Nat)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String) : EvalM CountedResult := do
    let (body, next, values) <- selectNeedFamilyBranch callee cells ctx env calleeName
    let result <- evalAlgOutputCounted body next values
    pure (reCountValueBoundary result)

  partial def invokeNeed (arg : ResolvedArgumentAlgorithm) : EvalM (Option Algorithm) := do
    if let some address := arg.need? then return (<- projectNeedCallable address)
    pure (some arg.invoked)

  partial def argumentNeed (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Nat :=
    match arg.need? with
    | some address => pure address
    | none => do readyNeed (<- evalArgumentValueCounted arg ctx env)

  /-- One loop iteration's step invocation. A LOOP STEP IS AN ORDINARY CALLABLE
      INVOKED OVER THE CURRENT STATE SUPPLY (LOOP-08, Q-23 decided October 2026):
      the state cells are an already formed supply, and the step is invoked on them
      by its own ordinary machinery — a user algorithm through the one inspecting
      binder over its parameter patterns, a clause family through the ordinary
      family dispatcher (`selectNeedFamilyBranch`), a builtin through its ordinary
      argument roles (`applyBuiltinCountedResolved` over need-backed arguments, the
      callback route), an alias as its target. Only the RECEIVER is the loop's: the
      invocation's ROW SUPPLY is the next state (LOOP-03, Q-24) — a user body's or
      the selected clause's rows, and for a builtin, which has no written rows, its
      ONE result value as ONE non-spread row (`()` and collections included; never
      the result's emitted count). Patterns bind the incoming cells only: no
      pattern category is consulted when the rows form the next state
      (`Dup(x, x) = { x + 1, x + 1 }` and `Dup(x, x) = { (x + 1, x + 1)* }` both
      supply two slots). A family's or builtin's failure is its ordinary
      invocation failure under the step's own call frame (`stepName`, the written
      step as the ordinary call names its callee — `loopStepName`); a user step's
      supplied-cardinality failure keeps its loop-state report, while pattern
      inspection retains the ordinary binder's error. C#: `Evaluator.InvokeLoopStepSupply`. -/
  partial def runNeedStepSlots (step : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      (cells : List Nat) (stepName : String) : EvalM (List Result) := do
    match step with
    | .builtin b =>
        withCtx s!"while evaluating call to {stepName}" do
          let supplied := cells.map fun address =>
            ({ algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some address } : ResolvedArgumentAlgorithm)
          let out <- applyBuiltinCountedResolved b supplied ctx env
          pure (loopStepBuiltinRows out)
    | .conditional _ _ _ _ =>
        withCtx s!"while evaluating call to {stepName}" do
          let (body, next, values) <- selectNeedFamilyBranch step cells ctx env stepName
          evalAlgOutputSlots body next values
    | .alias _ _ _ _ _ => do
        let target <- resolveAliasTarget step ctx
        runNeedStepSlots target ctx env cells stepName
    | .mk _ _ _ _ _ _ => do
        let some bindings <- bindNeedPatterns ((Algorithm.parameterPatterns step).map NeedPattern.ofParameter) cells
          | throw Error.badArity
        let next <- needBindingContext ctx bindings
        evalAlgOutputSlots step next (ValEnv.shadow env (Algorithm.params step))


  --------------------------------------------------------------------------
  -- Evaluation
  --------------------------------------------------------------------------

  /-- Evaluate an algorithm's output expressions and collect into a single Result:
      the value projection of `evalAlgOutputPreparedCore`, so the plain and counted
      evaluators can never disagree on an output value. Each NON-spread output
      expression contributes exactly one visible slot, even when it evaluates to
      the empty sequence value `()` (counted output `0`); an explicit spread
      `expr*` contributes its expanded items, so a spread of `()` contributes
      zero items and `(A*, 99)` splices `A`'s items before `99`. The slots are
      combined with `combineOutputSlots`, which preserves singleton slot
      structure and deliberately does NOT apply the general `Result.normalize`,
      which would recursively erase useful one-item sequence structure.
      (Loop-step state reads the same rows as a SUPPLY through
      `evalAlgOutputSlots`, not as this one combined value.)

      A user-defined algorithm value may exist structurally without output, but
      forcing it in value position raises `missingOutput`. A root program is
      also forced in value position when a result is requested; explicit empty
      output is written as `()`, the empty sequence value.

      Forcing a conditional algorithm in value position fails through
      `conditionalValueAccessError?`: branch selection requires call arguments,
      so a conditional must never silently force its empty output list.
      C#: `EvalAlgOutputCore`. -/
  partial def evalAlgOutputCore (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- evalAlgOutputCountedCore a ctx env
    pure out.fst

  /-- Force a user-defined algorithm value to produce output. -/
  partial def evalAlgOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
    evalAlgOutputCore a ctx env

  /-- Evaluate a root program algorithm when a result is requested. The root is
      demanded for its value with NOTHING supplied, so it goes through the ONE
      zero-argument demand funnel: a root declaring no parameter pattern is its
      output exactly as before, and a root whose parameter list accepts an EMPTY
      supply (a collecting-only host-built root) binds that supply first. -/
  partial def evalProgramOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
    evalZeroArgumentDemandOutput a ctx env

  /-- The ROW SUPPLY of an algorithm's output (LOOP-03, VAL-07 applied to a loop
      step): every output row is evaluated once, left to right; a NON-spread row
      supplies exactly one item — its value, `()` included (a row's emitted
      count is at most one since every result, loop results included, is a value
      boundary: Q-26, October 2026) — and a spread row `e*` supplies its spread
      items, possibly none. The supply depends on the rows alone: there is no
      pattern-derived flag (the former LOOP-04 packing of a pattern-bound step's
      spread row was retired by Q-24), so `(a, b)` is one item and `(a, b)*` two
      in every step. The internal `sequenceConstruct` join (never
      parser-produced) may still emit several values and is expanded by
      `countedTopLevelValues`. A builtin has no written rows, so its value is ONE
      row (LOOP-03, Q-23) — never a re-counted supply that would read a `()` result
      as zero slots; a builtin loop step never reaches this arm (`runNeedStepSlots`
      invokes it over the state supply), only a host-built clause body that IS a
      builtin does, read with nothing supplied as the ordinary family call reads it.
      C#: `Evaluator.EvalAlgOutputSlots`. -/
  partial def evalAlgOutputSlots (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM (List Result) := do
    match a with
    | .builtin b => do
        let out <- evalBuiltinValueCounted b
        pure [out.fst]
    | _ =>
      match a.findDuplicatePropName with
      | some n => .error (Error.duplicateProperty n)
      | none =>
        match conditionalValueAccessError? "conditional" a with
        | some err => .error err
        | none => pure ()
        match a with
        | .mk _ _ _ _ [] _ => .error Error.missingOutput
        | _ => pure ()
        let pushedCtx <- enterAlgorithmBody a ctx env
        let rec collect : List Expr -> List Result -> EvalM (List Result)
          | [], acc => pure acc.reverse
          | e :: rest, acc => do
              let out <- evalCounted e pushedCtx env
              let values :=
                match e with
                | .sequenceSpread _ => countedTopLevelValues out
                | _ =>
                    if out.snd = 0 then [out.fst] else countedTopLevelValues out
              collect rest (values.reverse ++ acc)
        collect (Algorithm.output a) []

  /-- Evaluate a higher-order sequence callback on one collected iteration
      item (the `filter` predicate). C#: `EvalSequenceCallbackCall`. -/
  partial def evalSequenceCallbackCall (callee : Algorithm) (item : CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM Result :=
    evalResolvedCallbackCall callee [countedSequenceCallbackItem item] ctx env calleeName

  /-- Counted variant of `evalSequenceCallbackCall` used by `map`: the transform's
      ordinary call result (HO-03). C#: `EvalSequenceCallbackCallCounted`. -/
  partial def evalSequenceCallbackCallCounted (callee : Algorithm) (item : CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult :=
    evalResolvedCallbackCallCounted callee [countedSequenceCallbackItem item] ctx env calleeName

  /-- Evaluate an algorithm's output expressions once, retaining both the combined counted
      value and the explicit evaluated output-slot view. The slot list is the accumulator
      from the same left-to-right pass that constructs the combined value; it never reopens
      or decomposes that value after singleton erasure and never evaluates an expression twice.

      A parenthesized sequence-value expression such as `(a, b)` counts as one emitted value,
      while multiple top-level output expressions `a, b` count as two. Body/root output
      accumulation and the loop-step row protocol retain this distinction. A map/reduce
      callback instead returns its ordinary call result at the value boundary (Q-25). -/
  partial def evalAlgOutputPreparedCore
      (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM PreparedAlgorithmOutput := do
    match a with
    | .builtin b => do
        let counted <- evalBuiltinValueCounted b
        pure { counted := counted, outputSlots := countedTopLevelValues counted }
    | _ =>
      match a.findDuplicatePropName with
      | some n => .error (Error.duplicateProperty n)
      | none =>
        match conditionalValueAccessError? "conditional" a with
        | some err => .error err
        | none => pure ()
        match a with
        | .mk _ _ _ _ [] _ => .error Error.missingOutput
        | _ => pure ()
        let pushedCtx <- enterAlgorithmBody a ctx env
        evalOutputRowsPreparedCore (Algorithm.output a) pushedCtx env

  /-- The ONE shared output-row supply loop: evaluates ordered `OutputBundle`
      rows left to right (a spread row contributes its supplied items, a
      non-spread row contributes exactly one slot) and combines the collected
      slots into one canonical value (`combineOutputSlots`). Algorithm output
      evaluation reaches it after pushing the algorithm's own scope;
      `Expr.capture` evaluation reaches it directly with the surrounding
      context, because a capture owns no scope. Both receivers therefore share
      exactly the same supply semantics rather than duplicating them.
      C#: `EvalOutputRowsPreparedCore`. -/
  partial def evalOutputRowsPreparedCore
      (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv)
      : EvalM PreparedAlgorithmOutput := do
    let rec collect : List Expr -> List Result -> Nat -> EvalM PreparedAlgorithmOutput
      | [], acc, emitted =>
          let outputSlots := acc.reverse
          pure {
            counted := (combineOutputSlots outputSlots, emitted),
            outputSlots := outputSlots
          }
      | expr :: rest, acc, emitted => do
          let out <- evalCounted expr rowCtx env
          match expr with
          | .sequenceSpread _ =>
              collect rest ((countedTopLevelValues out).reverse ++ acc) (emitted + out.snd)
          | _ =>
              -- A non-spread output is always one visible slot, even when it is
              -- the empty sequence value (). Only an explicit spread can
              -- contribute zero items.
              let slotCount := if out.snd = 0 then 1 else out.snd
              collect rest (out.fst :: acc) (emitted + slotCount)
    collect rows [] 0

  /-- Evaluates a `Expr.capture` body's rows in the surrounding context (a
      capture owns no scope, so nothing is pushed) through the shared
      output-row supply loop. The multi-item emitted count is preserved here;
      value-position consumers re-count at the capture's value boundary
      (`Result.valueCount`). An empty bundle captures the empty sequence value.
      C#: `EvalCapturePreparedCore`. -/
  partial def evalCapturePreparedCore
      (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
      : EvalM PreparedAlgorithmOutput :=
    evalOutputRowsPreparedCore rows ctx env

  partial def evalCaptureCountedCore
      (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let out <- evalCapturePreparedCore rows ctx env
    pure out.counted

  /-- Evaluates a capture body to its single canonical captured value. -/
  partial def evalCaptureValue
      (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
      : EvalM Result := do
    let out <- evalCaptureCountedCore rows ctx env
    pure out.fst

  /-- Counted projection of the shared prepared algorithm-output evaluation. -/
  partial def evalAlgOutputCountedCore
      (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let out <- evalAlgOutputPreparedCore a ctx env
    pure out.counted

  /-- Counted forcing variant of `evalAlgOutput`. -/
  partial def evalAlgOutputCounted (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult :=
    evalAlgOutputCountedCore a ctx env

  /-- Evaluate a callable that the ONE zero-argument value-demand law
      (`zeroArgumentDemandError?`) has ACCEPTED, as the zero-argument value it
      denotes. This is the demand's evaluation half, the counterpart of that
      law's rejection half, and the ONE funnel every demand site evaluates
      through:

      * a callable that declares no top-level pattern is its output, exactly as
        before — the overwhelmingly common path, untouched;
      * a callable whose pattern list accepts an EMPTY supply (a collecting-only
        signature such as `Only(*xs) = xs`) is bound by the ORDINARY binder
        against the empty supply first, so its collecting parameter holds the
        exact empty list `[]` while the body runs, and the callee's names shadow
        all three inherited tiers exactly as a written call's do;
      * a clause family that accepts zero supplied arguments dispatches its
        zero-argument branch through ordinary conditional dispatch, so branch
        selection, duplicate-pattern rejection and the value boundary are the
        call's own.

      ELIGIBILITY is what this rule changes; the CACHE is untouched: a
      property-style demand still reaches this funnel through
      `evalZeroArgPropertyAccessCounted` (the run cache), while `Only()` stays an
      ordinary call that bypasses it. C#:
      `EvalZeroArgumentDemandOutputCounted`. -/
  partial def evalZeroArgumentDemandOutputCounted (a : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    match a with
    | .conditional _ _ _ _ => evalConditionalCallCounted a [] ctx env
    -- An alias demanded with zero arguments is its target's zero-supply demand (only an
    -- unnormalized alias — a host-built tree — reaches here; every lookup normalizes first).
    | .alias _ _ _ _ _ => do
        let target <- resolveAliasTarget a ctx
        evalZeroArgumentDemandOutputCounted target ctx env
    | _ =>
      if (Algorithm.parameterPatterns a).isEmpty then
        evalAlgOutputCounted a ctx env
      else do
        let some bindings <- bindNeedPatterns ((Algorithm.parameterPatterns a).map NeedPattern.ofParameter) []
          | throw Error.badArity
        let newCtx <- needBindingContext ctx bindings
        evalAlgOutputCounted a newCtx (ValEnv.shadow env (Algorithm.params a))

  /-- Value projection of `evalZeroArgumentDemandOutputCounted`.
      C#: `EvalZeroArgumentDemandOutput`. -/
  partial def evalZeroArgumentDemandOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM Result := do
    let counted <- evalZeroArgumentDemandOutputCounted a ctx env
    pure counted.fst

  /-- Demand a builtin argument slot for its VALUE with zero explicit arguments.
      The ONE zero-argument value-demand law (`zeroArgumentDemandError?`) decides
      from the resolved algorithm's effective signature BEFORE any body is
      entered — a selected `if` branch, a loop's initial state, the `repeat`
      count, and the `atoms`/`range` arguments reject a callable that cannot
      accept zero supplied arguments exactly like value-position access does
      (`if(true, Inc, 0)` with `Inc(x)` is the property arity error, never
      `unknownName x` from inside `Inc`), while a callable that CAN (a property,
      a captured-binding thunk, a written value, a collecting-only signature)
      evaluates through the shared demand funnel. The law judges the callable
      the argument NAMES (`invoked`); the accepted demand evaluates the VALUE
      channel (`algorithm`), which for a named property is the ordinary property
      read — so the slot reads the property's cached value and never re-runs its
      body. Laziness is untouched: a slot is demanded only when the builtin
      selects it. C#: `EvalResolvedArgumentCounted`. -/
  partial def evalArgumentValueCounted (arg : ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    if let some address := arg.need? then return <- demandNeed address
    if let some err <- argumentParameterValueFailure? arg.source? ctx env then
      throw err
    match zeroArgumentDemandError? arg.source? arg.invoked with
    | some err => .error err
    | none => evalZeroArgumentDemandOutputCounted arg.algorithm ctx env

  /-- Value projection of `evalArgumentValueCounted`. C#: `EvalResolvedArgument`. -/
  partial def evalArgumentValue (arg : ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let counted <- evalArgumentValueCounted arg ctx env
    pure counted.fst

  /-- Property-style zero-parameter access may reuse the per-run cache.
      Explicit calls do not use this helper, so `A()` bypasses only `A`'s
      direct cache entry and does not change nested property references. -/
  partial def evalZeroArgPropertyAccessCounted
      (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm)
      (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx)
      (env : ValEnv) : EvalM CountedResult := do
    if isCacheableZeroArgPropertyAlgorithm resolvedAlgorithm then
      let state <- get
      let key := zeroArgPropertyCacheKey accessKind owner binding ctx env
        (propertyOwnerBindingContext resolvedAlgorithm.parent state)
      match ZeroArgPropertyCache.lookup state.zeroArgPropertyCache key with
      | some cached => pure cached
      | none =>
          let counted <- evalZeroArgumentDemandOutputCounted resolvedAlgorithm ctx env
          let nextState <- get
          set { nextState with
            zeroArgPropertyCache :=
              ZeroArgPropertyCache.insert nextState.zeroArgPropertyCache key counted }
          pure counted
    else
      evalZeroArgumentDemandOutputCounted resolvedAlgorithm ctx env

  partial def evalZeroArgPropertyAccess
      (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm)
      (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx)
      (env : ValEnv) : EvalM Result := do
    let counted <- evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env
    pure counted.fst

  /-- A clause-family callback invocation: the ordinary family dispatch over Ready
      cells, whose result is the ordinary call result (HO-03, PAT-11). -/
  partial def evalConditionalCallbackCallCounted (callee : Algorithm)
      (args : List CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult := do
    let cells <- args.mapM readyNeed
    evalNeedFamilySupply callee cells ctx env calleeName

  /-- Bind pre-evaluated callback arguments to a user algorithm through the ONE
      ordinary counted binder and evaluate its output. THE CALLBACK LAW
      (September 2026): every value a callback operation supplies is ONE
      ordinary argument, bound exactly as the ordinary call with the same
      supply — `map(xs, F)` calls `F(E)` for each element `E`, `reduce` calls
      `R(E, Acc)` — so fixed parameters take their values unchanged, a
      collector collects the supplied values exactly, and only the callee's
      explicit structural patterns open a value (a sequence pattern a sequence
      element, a list pattern a list element). There is no callback row
      convention: `map([(1, 2)], Add)` with `Add(x, y)` is the ordinary arity
      error of `Add((1, 2))`, while `AddPair((x, y))` opens the element
      explicitly. The RESULT is the ordinary call result too (HO-03, Q-25
      resolved October 2026): one value at the call's value boundary, several
      rows arriving as one sequence value. -/
  partial def evalUserCallbackCallCounted (callee : Algorithm)
      (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let cells <- args.mapM readyNeed
    evalNeedUserSupply callee cells ctx env

  /-- Evaluate a resolved algorithm against pre-evaluated callback arguments
      that preserve their emitted top-level counts.

      This is the shared callback-binding path for higher-order sequence
      builtins. Each callback item is a selected value, so inside the callback
      body it behaves exactly like `S:i` — one value, never opened — and it is
      bound as one ordinary argument (`evalUserCallbackCallCounted`). -/
  partial def evalResolvedCallbackCallCounted (callee : Algorithm)
      (args : List CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult := do
    match callee with
    | .builtin b => do
        let cells <- args.mapM readyNeed
        let supplied := cells.map fun address => ({ algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some address } : ResolvedArgumentAlgorithm)
        applyBuiltinCounted b supplied ctx env
    | .conditional _ _ _ _ =>
        match flatBinderUserEquivalent? callee with
        | some simple => evalUserCallbackCallCounted simple args ctx env
        | none =>
            evalConditionalCallbackCallCounted callee args ctx env calleeName
    -- An alias callback is its target, normalized BEFORE any invocation, so the alias charges
    -- nothing. C#: `EvalAliasCallbackCallCounted`.
    | .alias _ _ _ _ _ => do
        let target <- resolveAliasTarget callee ctx
        evalResolvedCallbackCallCounted target args ctx env calleeName
    | _ => evalUserCallbackCallCounted callee args ctx env

  /-- Non-counted wrapper for callback calls (the value projection of
      `evalResolvedCallbackCallCounted`). -/
  partial def evalResolvedCallbackCall (callee : Algorithm)
      (args : List CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM Result := do
    let out <- evalResolvedCallbackCallCounted callee args ctx env calleeName
    pure out.fst

  /-- Evaluate a `reduce` step on one collected iteration item. The reducer is
      an ordinary two-argument callback (THE CALLBACK LAW): it receives the
      element and the accumulator as exactly two arguments, each ONE value —
      `reduce(xs, R, init)` calls `R(E, Acc)` — so a collecting parameter on
      either side collects those argument values exactly and a structured
      accumulator is opened only by the reducer's own explicit pattern
      (`R(x, (a, b))`). The accumulator is always one value: the initial
      accumulator is reified at the value boundary, and each step's result is
      its ordinary call result, passed whole as the next accumulator (HO-03).
      C#: `EvalSequenceReduceStepCounted`. -/
  partial def evalSequenceReduceStepCounted (callee : Algorithm)
      (element : CountedResult) (accumulator : Result)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult :=
    evalResolvedCallbackCallCounted callee
      [ countedSequenceCallbackItem element
      , (accumulator, Result.valueCount accumulator)
      ]
      ctx env calleeName

  /-- Collection-builtin argument supply: the written slots, left to right, as the
      ordinary supply (CALL-02, CALL-03, NEED-01..05), before the arity check and
      before binding. Each slot's ROLE (`SequenceBuiltinMetadata.slotRole`) decides
      what the builtin later does with it.
      - A SPREAD slot is supply formation: its operand is evaluated NOW and supplies
        exactly its spread items, which take the roles of the positions they land
        on. Its failure — of any kind — is the CALL's failure, raised here, before
        any later slot and before the arity check; it is never one phantom supplied
        item (SUP-01, SUP-02, CALL-04). So `take(Bad*)` is `Bad`'s failure, not an
        arity error, and `map([], Bad*)` fails although `map` would never invoke a
        callback: the spread law of every call.
      - Every other slot is transported as its suspended cell (`need?`) and never
        evaluated here. A CALLBACK slot is projected on the CALLABLE channel only
        when the builtin invokes it per element (CALL-03, HO-04): an unused callback
        runs no body, so it has no effect, cannot fail and cannot recurse
        (`map([], A)` never reads `A`, exactly as `repeat(A, 0, 5)` never runs `A`).
        A VALUE slot is demanded only when the builtin executes it, after the arity
        check, through its cell and at most once, so no later read retries it
        (`reduce`'s `initial` included, HO-04). A SURPLUS slot is never demanded:
        the call reports its arity error first (NEED-05). *(Until Model C,
        2026-10-02, a value slot was demanded here, before the arity check, its
        ordinary failure retained on the item, and a surplus slot was prepared like
        a value slot's eager attempt.)*
      A callable-shaped argument (one that declares parameters, or a clause
      family) is never evaluated standalone: its parameters are unbound at this
      collection point, so evaluating its body would resolve those parameter
      names against the surrounding scope (when a sibling argument shares a
      parameter name and was deferred as a self-referential thunk, that stray
      lookup re-enters the same builtin call and never settles). In a VALUE
      position it is demanded through the ONE zero-argument law
      (`demandSequenceBuiltinCallItemValue`). The shape is the NAMED callable's
      (`invoked`), never its value wrapper's; a named zero-parameter property is
      read through its value side — the ordinary property read, served from the
      run cache. C#: `ResolveArgAlgsWithSequenceSpread` → `ResolveNeedSupply`, then
      `BuildCallableCallItems` and `DemandSequenceBuiltinCallItemValue`. -/
    partial def collectSequenceCallableCallItems
      (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
      (metadata : SequenceBuiltinMetadata)
      : EvalM (List CallableCallItem) := do
    let _ := metadata
    let expanded <- expandSequenceSpreadBuiltinArguments args ctx env
    pure (expanded.map fun arg => ({ algorithm? := some arg.algorithm, source? := arg.source?, callable? := arg.callable?, need? := arg.need? } : CallableCallItem))

  /-- Demand ONE collection-builtin call item that binding has placed in a VALUE
      position. Call-item assembly leaves a callable-shaped CALLBACK item
      unevaluated (a CALLBACK slot must receive the algorithm, never a value), so
      the demand happens HERE, once the descriptor has decided the slot is a
      value: an item whose NAMED callable (`CallableCallItem.named?`) the ONE law
      accepts (`acceptsZeroArgumentValueDemand` — a collecting-only signature
      such as `Only` alongside every zero-parameter property) is evaluated
      through the shared demand funnel on its VALUE side — for a named property
      the ordinary property read with its run cache — and every other item is
      returned untouched for `sequenceBuiltinValueDemandError?` to report. An
      item that was already evaluated, or whose evaluation already failed, is
      never re-entered. C#: `DemandSequenceBuiltinCallItemValue`. -/
  partial def demandSequenceBuiltinCallItemValue (item : CallableCallItem)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CallableCallItem := do
    if let some address := item.need? then
      if item.value?.isSome || item.error?.isSome then return item
      match <- evalAttempt (demandNeed address) with
      | .ok value => return { item with value? := some value.fst }
      | .error err => return { item with error? := some err }
    match item.value?, item.error?, item.algorithm? with
    | none, none, some alg =>
        if let some err <- argumentParameterValueFailure? item.source? ctx env then
          return { item with error? := some err }
        if acceptsZeroArgumentValueDemand (item.callable?.getD alg) then
          match <- evalAttempt (evalZeroArgumentDemandOutputCounted alg ctx env) with
          | .ok counted => pure { item with value? := some counted.fst }
          | .error err => pure { item with error? := some err }
        else
          pure item
    | _, _, _ => pure item

    partial def bindSequenceBuiltinArguments
      (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM BoundSequenceBuiltinArguments := do
    let items <- collectSequenceCallableCallItems args ctx env metadata
    -- A collection builtin is an ordinary fixed-arity callable: exactly one
    -- collection argument followed by its fixed control arguments
    -- (`count(collection)`, `take(collection, count)`,
    -- `map(collection, mapper)`). An unspread sequence or list value is ONE
    -- argument at this call boundary, exactly like at every other call
    -- boundary; only explicit caller-site spread alters argument boundaries,
    -- and the spread items obey the same fixed arity
    -- (`count([1, 2, 3]*)` supplies three arguments and is an arity error).
    -- Nothing is opened before binding.
    let expectedArgCount := 1 + metadata.suffixArgs.length
    if items.length != expectedArgCount then
      .error (Error.arityMismatch expectedArgCount items.length)
    match items with
    | [] => .error (Error.arityMismatch expectedArgCount 0)
    | collectionItem :: controlItems => do
        -- The `collection` parameter is a VALUE position, so demand the bound item
        -- through the ONE zero-argument value-demand law before reading its value.
        let collectionItem <- demandSequenceBuiltinCallItemValue collectionItem ctx env
        let collectionValue <-
          match collectionItem.value? with
          | some value => pure value
          | none =>
              match sequenceBuiltinValueDemandError? collectionItem with
              | some err => .error err
              | none => .error Error.badArity
        -- The one-level builtin collection view applies AFTER binding, to the
        -- bound collection value only: a lone sequence or exact list value
        -- opens to its immediate items, and any other value is a one-element
        -- collection (`count(7)` is 1). Opening is never recursive — nested
        -- sequence/list elements stay intact as single items.
        let collectionValues := builtinCollectionItems collectionValue
        let collected : CollectedSequenceBuiltinInput := { items := collectionValues }
        let preparedInput <- prepareSequenceBuiltinInput b metadata collected
        let rec prepareControls :
            List SequenceBuiltinSuffixArgDescriptor ->
            List CallableCallItem ->
            EvalM (List PreparedSequenceBuiltinSuffixArg)
          | [], [] => pure []
          | descriptor :: descriptors, item :: rest => do
              -- A `.value` / `.wholeNumber` control is a VALUE position, so it is
              -- demanded through the ONE law; an `.algorithm` control is a
              -- CALLBACK slot and is never demanded.
              let item <-
                match descriptor.kind with
                | .algorithm => pure item
                | _ => demandSequenceBuiltinCallItemValue item ctx env
              let prepared <- prepareSequenceBuiltinSuffixArgItem b descriptor item
              let tail <- prepareControls descriptors rest
              pure (prepared :: tail)
          | _, _ =>
              internalSequenceBuiltinSuffixArgMetadataError b "mismatched control arguments"
        let suffixArgs <- prepareControls metadata.suffixArgs controlItems
        pure {
          preparedInput := preparedInput
          iterationItems := collectionValues.map (fun value => (value, 1))
          suffixArgs := suffixArgs
        }

    /-- Evaluate `reduce` over the bound collection argument's viewed items.
      `reduce(collection, reducer, initial)` processes top-level
      collection elements from left to right.
      `step(element, accumulator)` receives each item exactly as collected
      from the post-binding collection view and the accumulator as ONE value —
      two ordinary callback arguments (THE CALLBACK LAW); nested sequence
      values stay intact, and only the reducer's own explicit pattern opens a
      structured element or accumulator. Each step's result is its ORDINARY
      call result (HO-03, Q-25 resolved October 2026) — the one value the call
      boundary delivers: several rows arrive as one sequence value, `()` and
      `[]` are ordinary values — passed whole, never spread, as the next
      accumulator with its value-boundary count (`reCountValueBoundary`), so
      `reduce([a, b], R, i)` is `R(b, R(a, i))`.

      The initial accumulator is an ordinary VALUE slot (HO-04): binding has
      already demanded it ONCE — a failure there is the call's failure and is
      never retried — so this function receives its value, never an algorithm
      to evaluate again. A callable that cannot supply a zero-argument value was
      rejected at binding (`reduceInitialRejection`). The value occupies one
      written accumulator slot, reified at the ordinary value boundary before
      reduction, so empty collections return the initial accumulator as ONE
      value. -/
  partial def evalReduceCounted (collection : List CountedResult)
      (stepAlg : Algorithm) (initial : Result)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let rec reduceLoop : List CountedResult -> CountedResult -> EvalM CountedResult
      | [], acc => pure acc
      | item :: rest, (accValue, _) => do
          let stepOut <- withCtx
            "while evaluating reduce step (reduce passes each iterated collection item as collected and the accumulator as one value; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)" <|
            evalSequenceReduceStepCounted stepAlg item accValue ctx env "reduce step"
          reduceLoop rest (reCountValueBoundary stepOut)
    -- The initial accumulator occupies ONE written accumulator slot: its value
    -- is reified as one persistent value at the ordinary value boundary
    -- (`Result.valueCount`, what `reCountValueBoundary` computes) BEFORE
    -- reduction begins, so an initial expression that emitted multiple items
    -- cannot leak that supply through the empty-collection return.
    reduceLoop collection (initial, Result.valueCount initial)

    /-- Evaluate `filter(collection, predicate)`.
      The fixed `collection` argument supplies the items through the
      post-binding collection view, and `predicate` is a fixed control
      argument. Each iterated item is passed to the predicate exactly as
      collected; nested sequence values and nested
      list values stay intact. The kept items remain the original collection
      items and are materialized as one list value, so keeping
      exactly `(1, 2)` yields `[(1, 2)]`. -/
  partial def evalFilterCounted (items : List CountedResult) (predicateAlg : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let rec filterLoop : Nat -> List CountedResult -> EvalM (List Result)
      | _, [] => pure []
      | index, item :: rest => do
        match <- evalAttempt (withCtx (s!"while evaluating filter predicate for item {index}: {resultDiagnosticString item.fst} (filter passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)") <|
          evalSequenceCallbackCall predicateAlg item ctx env "filter predicate") with
          | .error err =>
              .error err
          | .ok pr =>
              -- The predicate must return a Boolean value; a numeric result
              -- (`filter{x}` over numbers) is a value-kind error, never a
              -- nonzero truth test.
              match Result.asBool? pr with
              | some true => do
                  let kept <- filterLoop (index + 1) rest
                  pure (item.fst :: kept)
              | some false =>
                  filterLoop (index + 1) rest
              | none =>
                  .error (Error.typeMismatch
                    (booleanRequiredMessage "filter predicate result" pr))
    let kept <- filterLoop 0 items
    pure (makeCollectionListResult kept)

  /-- Evaluate `map(collection, mapper)`.
      `map` processes top-level collection elements from left to right.
      `transform(element)` receives each item exactly as collected from the
      post-binding collection view; nested sequence values stay intact.
      Each transform result is its ORDINARY call result (HO-03, Q-25 resolved
      October 2026) — the one value the call boundary delivers: several rows
      arrive as one sequence value, `()` and `[]` are ordinary values — and
      becomes ONE element of the list result, never flattened into it, so
      `map(L, F)` is `[F(L:0), …, F(L:n-1)]`. Empty collections yield `[]`, and
      the output preserves the original element order and element count. -/
  partial def evalMapCounted (collection : List CountedResult) (transformAlg : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let rec mapLoop : List CountedResult -> EvalM (List Result)
      | [] => pure []
      | item :: rest => do
          let mappedOut <- withCtx
            "while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)" <|
            evalSequenceCallbackCallCounted transformAlg item ctx env "map transform"
          let restMapped <- mapLoop rest
          pure (mappedOut.fst :: restMapped)
    let mapped <- mapLoop collection
    pure (makeCollectionListResult mapped)

    partial def applyBuiltinCountedSequence
      (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult :=
    do
      let bound <- bindSequenceBuiltinArguments b metadata args ctx env
      let withPreparedItems
          (k : List Result -> EvalM CountedResult) : EvalM CountedResult :=
        k bound.preparedInput.items
      let withPreparedNumericItems
          (k : List Int -> EvalM CountedResult) : EvalM CountedResult := do
        k (<- expectPreparedNumericItems b bound.preparedInput)
      let withPreparedSuffixArgs
          (k : List PreparedSequenceBuiltinSuffixArg -> EvalM CountedResult) : EvalM CountedResult :=
        k bound.suffixArgs
        match b with
        | .filterBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              if bound.iterationItems.isEmpty then return makeCollectionListResult []
              let predicateAlg <-
                expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              evalFilterCounted bound.iterationItems predicateAlg ctx env
        | .mapBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              if bound.iterationItems.isEmpty then return makeCollectionListResult []
              let transformAlg <-
                expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              evalMapCounted bound.iterationItems transformAlg ctx env
        | .orderBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalOrderCounted numbers
        | .orderDescBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalOrderDescCounted numbers
        | .countBuiltin =>
            withPreparedItems fun items =>
              evalCountCounted items
        | .containsBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              let searched <-
                expectPreparedSequenceBuiltinValueSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              withPreparedItems fun items =>
                evalContainsCounted items searched
        | .distinctBuiltin =>
            withPreparedItems fun items =>
              evalDistinctCounted items
        | .firstBuiltin =>
            withPreparedItems fun items =>
              evalFirstCounted items
        | .lastBuiltin =>
            withPreparedItems fun items =>
              evalLastCounted items
        | .takeBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              let count <-
                expectPreparedSequenceBuiltinWholeNumberSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              withPreparedItems fun items =>
                evalTakeCounted items count
        | .skipBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              let count <-
                expectPreparedSequenceBuiltinWholeNumberSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              withPreparedItems fun items =>
                evalSkipCounted items count
        | .minBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalMinCounted numbers
        | .maxBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalMaxCounted numbers
        | .sumBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalSumCounted numbers
        | .avgBuiltin =>
            withPreparedNumericItems fun numbers =>
              evalAvgCounted numbers
        | .reduceBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
              let initial <-
                expectPreparedSequenceBuiltinValueSuffixArg b metadata.suffixArgs preparedSuffixArgs 1
              if bound.iterationItems.isEmpty then return (initial, Result.valueCount initial)
              let stepAlg <-
                expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              evalReduceCounted bound.iterationItems stepAlg initial ctx env
        | _ =>
            .error (builtinArityError b args.length)

  /-- Builtin application with counted output shape (a builtin callback's one
      result is already a value, counted by `Result.valueCount`).
      Every VALUE slot (the `if` condition and branches, loop initial state, the
      `repeat` count, `atoms`, `range`) is demanded through
      `evalArgumentValueCounted`, so a parameterized algorithm in a selected slot
      is the ordinary zero-argument arity rejection and never enters its body;
      ALGORITHM slots (loop steps) invoke the argument's algorithm-channel
      identity (`ResolvedArgumentAlgorithm.invoked`), so a step forwarded through
      a parameter is the callable itself, never its demanded value. -/
  partial def applyBuiltinCounted
      (b : Builtin) (args : List ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult :=
    match sequenceBuiltinMetadata? b with
    | some metadata =>
      applyBuiltinCountedSequence b metadata args ctx env
    | none =>
        match b, args with
        | .ifBuiltin, [c,t,e] => do
            let cr <- evalArgumentValue c ctx env
            -- The selected branch is one argument expression, so `if` observes it
            -- as a single value boundary -- exactly like value-position property
            -- access. A multi-output branch property such as `X = 1, 2, 3`
            -- therefore yields the grouped sequence value `(1, 2, 3)` with emitted
            -- count 1, not three separate outputs; explicit spread opens it.
            -- `if` re-counts the chosen branch value via `Result.valueCount`,
            -- exactly as a completed `while`/`repeat` re-counts its final state
            -- (`loopResultCounted`).
            -- The condition must be a Boolean value: `if(1, a, b)` is a
            -- value-kind error, not a truth test.
            match Result.asBool? cr with
            | some false => do
                let r <- evalArgumentValueCounted e ctx env
                pure (r.fst, Result.valueCount r.fst)
            | some true => do
                let r <- evalArgumentValueCounted t ctx env
                pure (r.fst, Result.valueCount r.fst)
            | none => .error (Error.typeMismatch (booleanRequiredMessage "if condition" cr))

        | .whileBuiltin, step :: initAlgs => do
            if initAlgs.isEmpty then
              .error (builtinArityError b args.length)
            else
            let initialCells <- initAlgs.mapM (fun arg => argumentNeed arg ctx env)
            let stepName <- loopStepName "while" step
            let rec loop (cells : List Nat) : EvalM (List Nat) := do
              let algorithm <- projectInvokingSlot (invokingSlotRole .whileBuiltin) (<- invokeNeed step)
              let outputSlots <- runNeedStepSlots algorithm ctx env cells stepName
              let (nextSlots, cont) <- splitContSlots outputSlots
              if cont then loop (<- nextSlots.mapM (fun value => readyNeed (value, Result.valueCount value)))
              else pure cells
            let finalCells <- loop initialCells
            let finalSlots <- finalCells.mapM (fun address => Prod.fst <$> demandNeed address)
            pure (loopResultCounted finalSlots)

        | .repeatBuiltin, step :: countAlg :: initAlgs => do
            if initAlgs.isEmpty then
              .error (builtinArityError b args.length)
            else
            let cr <- evalArgumentValue countAlg ctx env
            let n <- expectInt cr
            if n < 0 then
              .error (Error.illegalInEval "Repeat count must be >= 0")
            else
              let initialCells <- initAlgs.mapM (fun arg => argumentNeed arg ctx env)
              let stepName <- loopStepName "repeat" step
              let rec repeatLoop (remaining : Int) (cells : List Nat) : EvalM (List Nat) := do
                if remaining = 0 then return cells
                let algorithm <- projectInvokingSlot (invokingSlotRole .repeatBuiltin) (<- invokeNeed step)
                let outputSlots <- runNeedStepSlots algorithm ctx env cells stepName
                let next <- outputSlots.mapM (fun value => readyNeed (value, Result.valueCount value))
                repeatLoop (remaining - 1) next
              let finalCells <- repeatLoop n initialCells
              let finalSlots <- finalCells.mapM (fun address => Prod.fst <$> demandNeed address)
              pure (loopResultCounted finalSlots)

        | .atomsBuiltin, [a] => do
            let r <- evalArgumentValue a ctx env
            -- `atoms` materializes a collection: one list of
            -- the recursively collected numeric atoms (sequence AND list
            -- boundaries open; strings and Boolean values contribute none).
            pure (makeCollectionListResult ((Result.languageAtoms r).map Result.atom))

        | .rangeBuiltin, [startAlg, stopAlg] => do
            let start <- expectInt (<- evalArgumentValue startAlg ctx env)
            let stop <- expectInt (<- evalArgumentValue stopAlg ctx env)
            let xs := inclusiveRange start stop
            -- `range` materializes a collection: one list value.
            pure (makeCollectionListResult (xs.map Result.atom))

        | _, _ =>
            .error (builtinArityError b args.length)

  /-- Builtin application with plain Result output.
      This is the Result projection of `applyBuiltinCounted`: the counted twin
      owns the builtin dispatch and semantics, and the non-counted path only
      discards the emitted-count metadata. The CoreTests builtin projection
      parity guards pin this equivalence (values, error diagnostics, and
      evaluator state) case by case. -/
  partial def applyBuiltin
      (b : Builtin) (args : List ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM Result := do
    let out <- applyBuiltinCounted b args ctx env
    pure out.fst

  partial def expandSequenceSpreadBuiltinArguments
      (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM (List ResolvedArgumentAlgorithm) := do
    -- Spread-marked argument slots are forced exactly once, in left-to-right written
    -- order, and expanding a spread slot is part of evaluating that slot: evaluate and
    -- expand the CURRENT spread slot before recursing into the remaining ones, then
    -- place its expansion before theirs. Non-spread slots pass through untouched as
    -- algorithms — they keep their written position and remain builtin-lazy, evaluated
    -- or skipped later by the builtin's own semantics (an unselected `if` branch never
    -- runs). Recursing first still produced the correct flattened argument order, but
    -- it ran the spread slots' effects and reported their failures right to left, so
    -- two failing spread slots reported the RIGHTMOST failure while the C# runtime
    -- reported the leftmost.
    let rec loop : List ResolvedArgumentAlgorithm -> EvalM (List ResolvedArgumentAlgorithm)
      | [] => pure []
      | arg :: rest => do
          if arg.spreadsSequence then
            let counted <- evalArgumentValueCounted arg ctx env
            let expanded <- (countedTopLevelValues counted).mapM (fun value => do
              let address <- readyNeed (value, 1)
              pure ({ algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some address } : ResolvedArgumentAlgorithm))
            let tail <- loop rest
            pure (expanded ++ tail)
          else
            let tail <- loop rest
            pure (arg :: tail)
    loop args

  partial def applyBuiltinCountedResolved
      (b : Builtin) (args : List ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult :=
    match sequenceBuiltinMetadata? b with
    | some metadata =>
        applyBuiltinCountedSequence b metadata args ctx env
    | none => do
        let expandedArgs <- expandSequenceSpreadBuiltinArguments args ctx env
        applyBuiltinCounted b expandedArgs ctx env

  partial def applyBuiltinResolved
      (b : Builtin) (args : List ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM Result := do
    let out <- applyBuiltinCountedResolved b args ctx env
    pure out.fst

  partial def evalExplicitSequenceValueItems (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      : EvalM (List Result) := do
    match a with
    | .builtin b => do
        let out <- evalBuiltinValueCounted b
        pure (countedTopLevelValues out)
    | _ =>
      match a.findDuplicatePropName with
      | some n => .error (Error.duplicateProperty n)
      | none =>
        match conditionalValueAccessError? "conditional" a with
        | some err => .error err
        | none => pure ()
        match a with
        | .mk _ _ _ _ [] _ => .error Error.missingOutput
        | _ => pure ()
        let pushedCtx <- enterAlgorithmBody a ctx env
        evalExplicitSequenceValueRowSlots (Algorithm.output a) pushedCtx env

  /-- The shared written-slot loop over ordered bundle rows: each row
      contributes its explicit written slots. Algorithm-shaped groupings reach
      it after pushing their own scope; a `Expr.capture` body reaches it
      directly (captures own no scope).
      C#: `EvalExplicitSequenceValueRowSlots`. -/
  partial def evalExplicitSequenceValueRowSlots (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv)
      : EvalM (List Result) := do
    let rec collect : List Expr -> List Result -> EvalM (List Result)
      | [], acc => pure acc.reverse
      | e :: rest, acc => do
          let values <- evalExplicitSequenceValueExprSlots e rowCtx env
          collect rest (values.reverse ++ acc)
    collect rows []

  partial def evalExplicitSequenceValueExprSlots (expr : Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM (List Result) := do
    match expr with
    -- A nested capture or zero-parameter block materializes exactly one item, combined
    -- with the same shallow singleton-erasing rule as ordinary capture
    -- evaluation (`combineOutputSlots`). A host-built single-row capture IS
    -- its already-evaluated item (source `(A)` is erased to `A` by the parser),
    -- and an all-spread-empty capture is `()`, never an orphan such as `(5)`.
    -- This is list-element reification, not an extra pattern-argument view.
    | .capture rows => do
        let items <- evalExplicitSequenceValueRowSlots rows ctx env
        pure [combineOutputSlots items]
    | .algorithmExpr algorithm => do
        let wired := wireToCaller ctx algorithm
        -- Only a plain-output algorithm can take the written-slot fast path. A
        -- captureless pattern still consumes a slot; a family must dispatch.
        let plainOutput := match wired with
          | .conditional _ _ _ _ => false
          -- A callable alias is no output to unfold: it is demanded as its target.
          | .alias _ _ _ _ _ => false
          | _ => (Algorithm.parameterPatterns wired).isEmpty
        if plainOutput then
          let items <- evalExplicitSequenceValueItems wired ctx env
          pure [combineOutputSlots items]
        else
          let out <- evalCounted expr ctx env
          pure [out.fst]
    | .sequenceSpread _ =>
        let out <- evalCounted expr ctx env
        pure (countedTopLevelValues out)
    | _ =>
        let out <- evalCounted expr ctx env
        -- WRITTEN-SLOT REIFICATION: a non-spread expression occupying one
        -- written slot contributes exactly ONE persistent value — the value
        -- its counted supply denotes — regardless of how many items the
        -- expression emitted (zero, one, or many). Only an explicit spread
        -- supplies the value's items into the surrounding item slots.
        pure [out.fst]

  /-- Ordinary calls form a demandable supply in the caller's context, check its
      cardinality, bind through the common inspecting-pattern engine and then
      execute the body. Plain binders transport cells without forcing VALUE.
      The public result remains the ordinary recounted value boundary. -/
  partial def evalUserCallCounted (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let cells <- formNeedSupply args ctx env
    evalNeedUserSupply callee cells ctx env

  /-- Counted conditional call evaluation — the CANONICAL conditional-call
      implementation (`evalConditionalCall` is its value projection).
      1. Assemble the argument supply through the shared call argument
         pipeline (explicit spread expands into ordinary argument slots
         BEFORE clause matching, so a multi-clause callee sees the same
         supply as every other callable shape).
      2. Try branches in order; first match wins.
      3. Evaluate the selected branch body with pattern bindings prepended.
      4. If no branch matches, raise noMatchingBranch.

      **Full-input-specification rule**: the branch body receives its input
      bindings ONLY from the matched pattern. No extra implicit parameters are
      inferred from free identifiers in the body; they must resolve through
      ordinary lexical / property / open / builtin lookup or fail with
      unknownName.

      **Assumes uniform output arity**: after validation
      (validateBranchOutputArities), all branches produce the same top-level
      output arity; the evaluator does not re-check this at runtime.

      The selected branch is a value boundary, so its public result re-counts
      the emitted arity to `Result.valueCount` (via `reCountValueBoundary`) --
      a multi-output branch becomes one sequence value (count 1), matching
      `if` and plain calls. -/
  partial def evalConditionalCallCounted (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult := do
    let cells <- formNeedSupply args ctx env
    evalNeedFamilySupply callee cells ctx env calleeName

  /-- Dispatch an already-resolved callee with plain Result output.
      This is the Result projection of `evalResolvedCallCounted`: the counted
      twin owns the builtin/flat-binder/conditional/user dispatch, and each of
      its arms already ends in a projected family, so the projection is
      compositional. -/
  partial def evalResolvedCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM Result := do
    let out <- evalResolvedCallCounted callee args ctx env calleeName
    pure out.fst

  /-- Dispatch an already-resolved callee in counted evaluation — the
      CANONICAL resolved-callee dispatch (`evalResolvedCall` is its value
      projection). -/
  partial def evalResolvedCallCounted (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult := do
    match callee with
    | .builtin b => do
      let cells <- formNeedSupply args ctx env
      let supplied := cells.map fun address => ({ algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some address } : ResolvedArgumentAlgorithm)
      applyBuiltinCountedResolved b supplied ctx env
    | .conditional _ _ _ _ =>
      match flatBinderUserEquivalent? callee with
      | some simple => evalUserCallCounted simple args ctx env
      | none => evalConditionalCallCounted callee args ctx env calleeName
    -- The dispatch safety net: a callee that reached dispatch as an unnormalized alias (a
    -- host-built tree) calls its target with the same written arguments. Every binding lookup
    -- normalizes first. C#: `EvalAliasCallCounted`.
    | .alias _ _ _ _ _ => do
      let target <- resolveAliasTarget callee ctx
      evalResolvedCallCounted target args ctx env calleeName
    | _ => evalUserCallCounted callee args ctx env

  /-- Context-aware counted call evaluation for expression position — the
      CANONICAL expression-position call dispatch (`evalCallExpr` is its value
      projection); attaches `CtxMsg.call` to resolution and dispatch errors.
      The callee is resolved by `resolveCalleeAlg` (DOT-09). -/
  partial def evalCallCountedExpr (f : Expr) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let callee <- withCtx (CtxMsg.call f) <| resolveCalleeAlg f ctx
    withCtx (CtxMsg.call f) <| evalResolvedCallCounted callee args ctx env (openExprName f)

  /-- Counted extension-call fallback: DOT-CALL PASSES A VALUE (September
      2026). `R.F(args)` resolves the callee and dispatches exactly
      `F(R, args)` — the receiver expression becomes the ordinary FIRST
      written argument slot of the ONE shared call assembly
      (`prepareLexicalDotCallArgs` + `evalResolvedCallCounted`), so every
      callable shape (builtin, flat, collecting, patterned, clause family)
      binds, demands, caches, orders, charges, and rejects the receiver
      exactly as it would that written argument: a builtin's `collection`
      slot demands a named receiver through the zero-argument value-demand law
      like `count(A)` does, a collecting parameter collects the receiver as
      one item (`(1, 2).Coll` is `[(1, 2)]`, `().Coll` is `[()]`), and only a
      spread receiver — the fluent `R*.F` form, which the parser lowers to
      `F(R*)` — opens a boundary. There is no dotted receiver view, no raw
      receiver supply, and no builtin-specific receiver placement.

      The STORED lexical-fallback identity decides the callee channel — the
      front-end's Param-vs-Resolve decision is CONSUMED here, never
      reconstructed from runtime environments: a `.resolve` fallback takes the
      ordinary name-based path, and any other fallback (normally `.param`)
      resolves through canonical `resolveAlg`, so a parameter shadows a
      same-name builtin exactly as in plain-call position. Non-name hand-built
      fallbacks are outside the post-elaboration contract and follow their
      ordinary `resolveAlg` behavior defensively.
      C#: `CallLexicalWithReceiverCounted`. -/
  partial def callLexicalWithReceiverCounted (name : Ident) (receiver : Expr)
      (fallback : Expr)
      (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let combinedArgs := prepareLexicalDotCallArgs receiver extraArgs
    match fallback with
    | .resolve fallbackName =>
      let callee <- resolveAlg (.resolve fallbackName) ctx
      evalResolvedCallCounted callee combinedArgs ctx env fallbackName
    | other =>
      let callee <- resolveAlg other ctx
      evalResolvedCallCounted callee combinedArgs ctx env name

  /-- The `.string` intrinsic is a ZERO-parameter member. A written argument
      list is formed exactly like every call's supply (`formNeedSupply`:
      explicit spreads are opened, every other slot stays a suspended need)
      and then rejected by its cardinality before any argument, or the
      receiver, is demanded — the same outcome as `Obj.V(1)` for a declared
      zero-parameter member — so a written bundle is never silently dropped;
      an EMPTY written list (`x.string()`), or one whose spreads supply no
      item, stays the intrinsic, as `A()` stays a call of `A`.
      C#: `RejectDotStringIntrinsicArguments`. -/
  partial def rejectDotStringIntrinsicArguments (argsOpt : Option OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Unit := do
    match argsOpt with
    | none => pure ()
    | some args =>
      let items <- formNeedSupply args ctx env
      if items.length = 0 then pure ()
      else .error (Error.arityMismatch 0 items.length)

  /-- The VALUE the ordinary-dot `string` intrinsic converts, demanded after the
      zero-argument value-demand law accepted the resolved receiver. HOW A
      PROPERTY VALUE IS CONSUMED DOES NOT AFFECT CACHING, so the intrinsic reads
      its receiver exactly as a value position reads it:
      * a lexical property reference `A` is read through the zero-argument
        property access of its resolved binding (the run cache), so `A.string`
        converts the very value `A` reads;
      * a structurally navigated member `Obj.A` is read through the structural
        property access of the member it selects, so `Obj.A.string` converts the
        very value `Obj.A` reads;
      * a parameter is the ordinary value-position parameter read — its bound
        value, or the failure its argument slot established — so a forwarded
        property value is never re-run through the parameter's algorithm channel
        (`F(v) = v.string` converts the value `F(A)` passed);
      * every other receiver shape (a written block, a capture, a dot result) is
        its resolved algorithm's zero-argument demand, as before.
      C#: `EvalDotStringReceiverAlgOutput`. -/
  partial def evalDotStringReceiverValue (target : Expr) (targetAlg : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    match target with
    | .resolve n =>
        match ctx.callStack with
        | owner :: _ =>
            let resolved <- lookupLexicalProperty owner n ctx
            let counted <- evalZeroArgPropertyAccessCounted .lexical resolved.owner resolved.binding resolved.alg ctx env
            pure counted.fst
        | [] => evalZeroArgumentDemandOutput targetAlg ctx env
    | .param _ => eval target ctx env
    | .dotMember receiver member _ none =>
        -- The same navigation `resolveDotReceiver` just performed (a `string` step
        -- included, Q-17 S-C): a member the container DECLARES is the selected
        -- structural binding (its accessibility was already enforced there);
        -- anything else is a dot result.
        match <- evalAttempt (resolveDotReceiver receiver ctx) with
        | .ok container =>
            match Algorithm.lookupPropDefAny? container member with
            | some p =>
                let accessed := (flatBinderUserEquivalent? targetAlg).getD targetAlg
                let counted <- evalZeroArgPropertyAccessCounted .structural container p accessed ctx env
                pure counted.fst
            | none => evalZeroArgumentDemandOutput targetAlg ctx env
        | .error _ => evalZeroArgumentDemandOutput targetAlg ctx env
    | _ => evalZeroArgumentDemandOutput targetAlg ctx env

  /-- Evaluate dotCall: a.f or a.f(args). The member result is a value boundary:
      structural zero-arg property access and collection builtins re-count to
      `Result.valueCount`, and user/lexical member calls re-count via
      `evalUserCallCounted`, so a multi-output member becomes one sequence value
      (count 1) and only a caller-site spread `value*` re-spreads
      it. This is the single owner
      of dot-call dispatch; `evalDotCall` is its Result projection.
      The ROUTE is decided first, member-first at every edge (DOT-01; Q-17 S-C):
      - Receiver resolution through `resolveDotReceiver`: a chained receiver
        navigates its declared structural members, so the property-first
        rule below holds at every level of `A.B.C.D`
      - ONE structural lookup of the member (a member named `string` included):
        - If no args and 0-param → value access
        - If no args and has params → arity mismatch error
        - If args → direct argument binding (no receiver injection)
      - A branch-only member → `localOnlyProperty`
      - A structural MISS takes the edge's miss route:
        - "string" → the value intrinsic: evaluate the receiver, convert its
          numeric value to text (a lexical `string` is never consulted)
        - otherwise → extension fallback (`callLexicalWithReceiverCounted`):
          DOT-CALL PASSES A VALUE — `a.f(args)` is exactly the call
          `f(a, args)`, the receiver being the ordinary first argument slot
          (never a supply of its own; only the spread receiver `a*.f`, lowered
          to `f(a*)`, opens a boundary).
        Dot resolution therefore has three classes — structural member access,
        the intrinsic `.string`, and extension fallback — and only the
        extension call injects the receiver.

      When receiver resolution returns notAnAlgorithm (a value receiver, e.g. a
      numeric literal), there is no member to select: the miss route applies
      directly.

      (The C# front end consumes the Grace annotation in `a~.f` / `a.~f`, so
      Lean receives the same dotMember and the same structural-first dispatch
      as for ordinary `a.f`.)

      A structurally navigated zero-argument member read goes through the
      zero-argument property access of the member's binding (the run cache,
      `evalZeroArgPropertyAccessCounted`), exactly like the lexical read of the
      same binding; an explicit member call `Obj.A()` does not. -/
  partial def evalDotCallCounted (target : Expr) (name : Ident)
      (fallback : Expr) (argsOpt : Option OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    match <- evalAttempt (resolveDotReceiver target ctx) with
    | .ok targetAlg =>
        -- ONE structural lookup decides the route, whatever the member's spelling: a
        -- declared member wins (a member named `string` included — Q-17 S-C), then a
        -- branch-only member is the local-only error, and only a structural MISS takes
        -- the miss route.
        match Algorithm.lookupPropDefAny? targetAlg name with
        | some p =>
            -- Selection is by declaration (structural access ignores `public`); the
            -- member's accessibility from THIS site is decided afterwards.
            if !(memberAccessible? ctx targetAlg p) then
              .error (Error.localOnlyProperty (openExprName target) name p.exposure)
            else do
            -- A member that is a callable alias is read or called as its TARGET, while its
            -- BINDING `p` keys the zero-argument read (C#: `EvalAliasMemberCounted`).
            let wired <- resolveAliasTarget (childOfInContext targetAlg p.alg ctx) ctx
            match argsOpt with
            | none =>
                -- A structurally navigated member read with NO argument list is an
                -- ordinary zero-argument value demand, so the ONE law decides
                -- (`acceptsZeroArgumentValueDemand`) and the rejection names the
                -- member's true minimum supply (`minimumSuppliedSlots`), never its
                -- flattened declared capture count.
                match flatBinderUserEquivalent? wired with
                | some simple =>
                    if acceptsZeroArgumentValueDemand simple then
                      reCountValueBoundary <$> evalZeroArgPropertyAccessCounted .structural targetAlg p simple ctx env
                    else
                      .error (Error.arityMismatch
                        (ParameterPattern.minimumSuppliedSlots (Algorithm.parameterPatterns simple)) 0)
                | none =>
                    if acceptsZeroArgumentValueDemand wired then
                      reCountValueBoundary <$> evalZeroArgPropertyAccessCounted .structural targetAlg p wired ctx env
                    else
                      match wired with
                      | .conditional _ _ _ _ => .error (Error.noMatchingBranch name)
                      | _ =>
                          .error (Error.arityMismatch
                            (ParameterPattern.minimumSuppliedSlots (Algorithm.parameterPatterns wired)) 0)
            | some args =>
                evalResolvedCallCounted wired args ctx env name
        | none =>
            if Algorithm.conditionalBranchesDefineProperty targetAlg name then
              .error (Error.localOnlyProperty (openExprName target) name .localConditional)
            else if name = "string" then do
              -- A structural miss: `string` is the number-to-text intrinsic (DOT-08) —
              -- it takes the extension call's place, so a lexical `string` is never
              -- consulted.
              -- The intrinsic is a ZERO-parameter member: a written argument list is
              -- formed like every call's supply (explicit spreads opened, every other
              -- slot a suspended need) and rejected by its cardinality before any
              -- argument or the receiver is demanded, exactly as `Obj.V(1)` is for a
              -- declared zero-parameter member; `x.string()` (an empty list) stays the
              -- intrinsic.
              -- C#: `RejectDotStringIntrinsicArguments`.
              rejectDotStringIntrinsicArguments argsOpt ctx env
              -- A receiver that is a callable alias is demanded as its TARGET, read through the
              -- alias's own binding (C#: `EvalAliasDotStringCounted`).
              let targetAlg <- resolveAliasTarget targetAlg ctx
              -- The receiver is demanded for its VALUE with zero arguments, so the ONE
              -- zero-argument demand law decides from the resolved receiver's
              -- signature before its body is entered: `Inc.string` with `Inc(x)` is
              -- the property arity error, a navigated parameterized member the bare
              -- one, and a written parameterized block `unresolvedImplicitParams`.
              -- The accepted receiver is then READ like a value position reads it
              -- (`evalDotStringReceiverValue`): a named property through its cached
              -- property access, a parameter through its bound value.
              -- A PARAMETER receiver with a failure recorded on its algorithm binding
              -- (the legacy Ready tier: no Model-C binding path records one, so for a
              -- source program this is `none`) reports that failure first, before the
              -- law judges its algorithm channel (AT-MOST-ONCE ARGUMENT VALUE
              -- EVALUATION, `parameterValueFailure?`). C#: `EvalDotStringReceiverAlgOutput`.
              match target with
              | .param x =>
                  match <- parameterValueFailure? x ctx env with
                  | some err => .error err
                  | none => pure ()
              | _ => pure ()
              match zeroArgumentDemandError? (some target) targetAlg with
              | some err => .error err
              | none => pure ()
              let val <- evalDotStringReceiverValue target targetAlg ctx env
              let out <- resultToString val
              pure (out, Result.valueCount out)
            else
              callLexicalWithReceiverCounted name target fallback argsOpt ctx env
    | .error (.notAnAlgorithm _) =>
      -- A value receiver declares no member: the edge's miss route applies directly.
      if name = "string" then do
        rejectDotStringIntrinsicArguments argsOpt ctx env
        let val <- eval target ctx env
        let out <- resultToString val
        pure (out, Result.valueCount out)
      else
        callLexicalWithReceiverCounted name target fallback argsOpt ctx env
    | .error e => .error e

  /-- Evaluate a spread operand and supply its immediate items. Spreading an
      operand that has no defined output is the spread-specific
      `spreadMissingOutput` error on EVERY operand shape — the direct
      `.algorithmExpr`/`.capture` specializations translate a missing-output
      failure exactly like the generic arm, so `{A = 1}*` and
      `X = {A = 1}` / `X*` agree.
      C#: `EvalSequenceSpreadOperandItems`. -/
  partial def evalSequenceSpreadOperandItems (e : Expr) (ctx : EvalCtx)
      (env : ValEnv) : EvalM (List Result) := do
    match e with
    | .capture rows =>
        match <- evalAttempt (evalCaptureValue rows ctx env) with
        | .ok value =>
            pure value.spreadItems
        | .error err =>
            if isMissingOutputError err then
              .error Error.spreadMissingOutput
            else
              .error err
    | .algorithmExpr a => do
        -- An inline alias block is demanded as its target, a rejection reported as its written
        -- target reference (FA-OQ-1; C#: `EvalAliasSpreadOperandItems`).
        let wired <- resolveAliasTarget (wireToCaller ctx a) ctx
        -- A spread operand is demanded for its VALUE with zero arguments, so the
        -- ONE law decides and shapes its report here too: a block whose parameter
        -- list accepts an empty supply is demanded through the shared funnel.
        match zeroArgumentDemandError? (some e) wired with
        | some err => .error err
        | none =>
          match <- evalAttempt (evalZeroArgumentDemandOutput wired ctx env) with
          | .ok value =>
              pure value.spreadItems
          | .error err =>
              if isMissingOutputError err then
                .error Error.spreadMissingOutput
              else
                .error err
    | _ =>
        match <- evalAttempt (eval e ctx env) with
        | .ok value =>
            pure value.spreadItems
        | .error err =>
            if isMissingOutputError err then
              .error Error.spreadMissingOutput
            else
              .error err

    /-- Evaluate a unary `sequenceSpread` node by evaluating its single operand
      once and spreading immediate top-level items. Nested sequence-value
      members are not recursively flattened. Directly-nested spreads (`A**`)
      are unwrapped iteratively (`peelSequenceSpreadLayers`, stack-safe for deep
      nesting) and then each written layer is applied COMPOSITIONALLY: every
      written `sequenceSpread` layer opens exactly one boundary of the value
      the previous layer's supply re-captures, so `A**` agrees with `(A*)*`.
      For sequence values
      the extra layers are fixed points (value-equivalent to a single spread);
      a singleton-list chain opens one list boundary per layer
      (`[[7]]**` supplies `7`), while a multi-element list re-captures as
      a sequence after the first layer and then stays fixed
      (`[[1, 2], [3, 4]]**` supplies the two inner lists unchanged). -/
  partial def evalSequenceSpreadCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let (operand, layers) := peelSequenceSpreadLayers e 0
    let supplied <- evalSequenceSpreadOperandItems operand ctx env
    let rec reopen : Nat -> List Result -> List Result
      | 0, items => items
      | n + 1, items =>
          reopen n (Result.spreadItems (Result.normalize (Result.sequenceValue items)))
    let items := reopen (layers - 1) supplied
    pure (Result.normalize (Result.sequenceValue items), items.length)

  /-- Evaluate a surface list literal `[e1, ..., en]` as exactly ONE exact
      immutable list value. Element slots reuse the written-parentheses
      expression-list slot rules (`evalExplicitSequenceValueExprSlots`): an
      explicit spread slot opens its operand's immediate items into the list
      being constructed (an empty spread contributes no elements), a non-spread
      slot is one element even when it evaluates to the empty sequence value
      `()`, and a nested multi-slot capture or zero-parameter `algorithmExpr` is one element
      (its own rows combined to one value).
      Unlike sequence construction the collected elements are stored EXACTLY:
      no singleton erasure and no empty-nesting collapse, so `[7]`, `[[7]]`,
      `[]`, and `[()]` are all distinct list values. A list literal always
      emits one value. C#: `EvalListLiteralCounted`; plain `eval` is this
      function's value projection on both sides. -/
  partial def evalListLiteralCounted (elements : List Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let rec collect : List Expr -> List Result -> EvalM (List Result)
      | [], acc => pure acc.reverse
      | e :: rest, acc => do
          let values <- evalExplicitSequenceValueExprSlots e ctx env
          collect rest (values.reverse ++ acc)
    let items <- collect elements []
    pure (Result.listValue items, 1)

  /-- Evaluate the INTERNAL `sequenceConstruct` join node as one sequence
      value. Join semantics, not written-parentheses semantics: a non-spread
      leaf whose value is `()` contributes NO item (an empty join
      contribution), an explicit spread leaf opens its operand's immediate
      items into the constructed sequence, and the result is normalized.
      Written parentheses parse to `capture` nodes and always keep a
      non-spread `()` item visible — surface syntax must never route through
      this node (see the constructor note on `Expr.sequenceConstruct`).
      C#: `EvalSequenceConstructCounted`; plain `eval` is this function's
      value projection on both sides. -/
  partial def evalSequenceConstructCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let rec loop : List Expr -> List Result -> EvalM CountedResult
      | [], items =>
          let value := Result.normalize (Result.sequenceValue items.reverse)
          pure (value, Result.valueCount value)
      | leaf :: rest, items => do
          match leaf with
          | .sequenceSpread _ => do
              let supplied <- evalSequenceSpreadOperandItems leaf ctx env
              loop rest (supplied.reverse ++ items)
          | _ => do
              let value <- eval leaf ctx env
              if Result.valueCount value = 0 then
                loop rest items
              else
                loop rest (value :: items)
    loop (sequenceConstructLeaves e) []

  /-- Evaluate a unary operator expression as one counted value. The operand is
      read at its value boundary. `not` is the Boolean negation and REQUIRES a
      Boolean operand (a number has no truth value); `-` is numeric negation:
      every non-numeric operand — a string, a Boolean, a sequence (the empty
      sequence value like any other, SYN-01) or a list — is the one value-kind
      error naming the operator and the operand (Q-27), never an arity error.
      Owned here so
      `eval` (the value projection) never carries independent operator
      semantics. C#: `Evaluator.ApplyUnaryOperator`, reached from the unary
      case of `EvalExpressionSpineCounted`. -/
  partial def evalUnaryCounted (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let r <- eval operand ctx env
    match op with
    | .not =>
        match Result.asBool? r with
        | some b => pure (Result.bool (!b), 1)
        | none => .error (Error.typeMismatch
            s!"operator `not` expects a Boolean operand, but the operand was {operandDescription r}")
    | .minus =>
        match Result.asInt? r with
        | some v => pure (Result.atom (-v), 1)
        | none => .error (Error.typeMismatch
            s!"operator `-` expects a numeric scalar operand, but the operand was {operandDescription r}")

  /-- Evaluate a binary (arithmetic or logical) operator expression as one
      counted value. Both operands are read at their value boundaries; strings
      reject every binary operator; everything else follows the numeric-scalar
      core or the Boolean-only logical rule. Comparisons are NOT binary
      operators — every comparison is a link of a comparison chain
      (`evalComparisonCounted`). The empty sequence value `()` is an ORDINARY
      operand here — it has no numeric scalar value, so it is rejected by the
      same operand validation as any other non-scalar value (SYN-01). Empty
      NEUTRALITY belongs to the arity algebra's supply operations
      (capture/collect/spread), never to scalar operators. Owned here so `eval`
      (the value projection) never carries independent operator semantics.
      C#: the binary case of `EvalExpressionSpineCounted` / `ApplyBinaryOperator`. -/
  partial def evalBinaryCounted (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let lr <- eval a ctx env
    let rr <- eval b ctx env
    match op with
    -- The logical operators are Boolean-only: both operands are evaluated
    -- left to right before the operator applies (the established evaluation
    -- order — no short circuit), and each must be a Boolean value. There is
    -- no numeric truthiness, so `1 and 2` is a value-kind error.
    | .and | .or | .xor => do
        let binaryContext := s!"while evaluating `{binaryExprDiagnosticName op a b}`"
        let x <- withCtx binaryContext (requireBooleanOperand op "left" lr)
        let y <- withCtx binaryContext (requireBooleanOperand op "right" rr)
        let value : Bool :=
          match op with
          | .and => x && y
          | .or  => x || y
          | _    => x != y
        pure (Result.bool value, 1)
    | _ =>
      -- SYN-01: the empty sequence value is NOT an identity for scalar
      -- operators. `()` carries no numeric scalar value, so it falls through to
      -- the ordinary operand validation below exactly like `(1, 2)` or `[]` —
      -- `10 / ()`, `() > 10`, `() and 7`, and `() + 'text'` are operand errors,
      -- never a passthrough of the other operand.
      match lr, rr with
      -- Non-equality operators are not defined on strings (they fail here rather
      -- than via expectInt so the diagnostic names the string operands).
      | .str _, .str _ => .error (Error.typeMismatch "Strings only support == and != operators")
      -- Mixed string/number or string/sequence value: fail for any operator
      | .str _, _ => .error (Error.typeMismatch "Cannot apply operator to string and non-string operands")
      | _, .str _ => .error (Error.typeMismatch "Cannot apply operator to string and non-string operands")
      | _, _ => do
        let binaryContext := s!"while evaluating `{binaryExprDiagnosticName op a b}`"
        let x <- withCtx binaryContext (requireNumericScalarOperand op "left" lr)
        let y <- withCtx binaryContext (requireNumericScalarOperand op "right" rr)
        -- Check for division by zero
        if (op == BinaryOp.div || op == BinaryOp.idiv || op == BinaryOp.mod) && y == 0 then
          .error Error.divByZero
        else if op == BinaryOp.pow && y < 0 then do
          let value <- negativeIntPow x y
          pure (value, Result.valueCount value)
        else
          let value : Result :=
            -- The logical operators are handled above; their arm below keeps
            -- the match exhaustive over BinaryOp and is unreachable here.
            match op with
            | .add  => .atom (x + y)
            | .sub  => .atom (x - y)
            | .mul  => .atom (x * y)
            -- Division and modulo truncate toward zero (Int.tdiv / Int.tmod),
            -- matching the C# reference: `-7 div 2 = -3` and `-7 mod 2 = -1`.
            -- `/` on non-divisible operands additionally truncates the exact
            -- decimal quotient as part of the integer-core limitation.
            | .div  => .atom (x.tdiv y)
            | .idiv => .atom (x.tdiv y)
            | .mod  => .atom (x.tmod y)
            | .pow  => .atom (intPow x y.toNat)
            | .and | .or | .xor => .bool false
          pure (value, 1)

  /-- Evaluate a COMPARISON CHAIN `first op1 x1 op2 x2 …` as one counted Boolean
      value — incrementally, left to right: the first operand, then link by
      link, evaluating the link's operand and comparing the PREVIOUS operand's
      value with it (`applyComparison`). Every operand is evaluated EXACTLY ONCE
      (the previous VALUE is carried forward, never its expression), a `false`
      link never stops the chain (KatLang's eager Boolean composition: a later
      invalid comparison is still reported), and an error terminates it before
      any later operand is evaluated. The chain is `true` iff every link held; a
      chain with no links evaluates its first operand and is `true`.
      C#: the Comparison case of `EvalExpressionSpineCounted` /
      `EvalExpressionSpineCountedAsync` and `LoopOptimizer.EvalLoopComparisonPlan`. -/
  partial def evalComparisonCounted (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    let firstValue <- eval first ctx env
    evalComparisonLinksCounted first firstValue true links ctx env

  /-- The link loop of `evalComparisonCounted`: `previous` is the value of
      `previousExpr` (the left side of the next link) and `holds` the verdict of
      the links compared so far. -/
  partial def evalComparisonLinksCounted (previousExpr : Expr) (previous : Result) (holds : Bool)
      (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    match links with
    | [] => pure (Result.bool holds, 1)
    | link :: rest => do
        let next <- eval link.operand ctx env
        let linkHolds <- applyComparison link.op previousExpr link.operand previous next
        evalComparisonLinksCounted link.operand next (holds && linkHolds) rest ctx env

  /-- Evaluate an expression together with the number of top-level values it
      emits at the current algorithm boundary — the CANONICAL expression
      dispatch: it matches EVERY `Expr` variant explicitly (no default arm),
      and plain `eval` is its total value projection. A new `Expr` variant
      therefore fails compilation here until it is given a counted arm — the
      structural guard against silently reintroducing plain-owned semantics.

      Calls, name resolution, collection builtins, and SELECTION (`.index`,
      like `first`/`last`) are value boundaries: they emit `Result.valueCount`
      of the result value (one value for a non-empty result), so a
      multi-output body/collection or a selected sequence/list is observed as
      one value and only a caller-site spread `value*` re-spreads it.
      Block expressions count as one sequence value when non-empty. `sequenceConstruct`
      emits one constructed sequence value. `sequenceSpread`
      emits the immediate spread items of its operand. All other value expressions emit either zero values (empty
      result) or one value. -/
  partial def evalCounted (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    match e with
    | .param x => do
        let (ctx, env) <- parameterContext x ctx env
        if let some address := lookupAssoc x ctx.needEnv then
          return <- demandNeed address
        match ctx.countedParamEnv.lookup x with
        | some counted => pure counted
        | none =>
            match env.lookup x with
            | some v => pure (v, Result.valueCount v)
            | none =>
                -- AT-MOST-ONCE ARGUMENT VALUE EVALUATION (Q-01, September 2026): a
                -- Model-C parameter was read through its need cell above (its first
                -- demand evaluates the supplied computation once; every later read
                -- reuses the completed outcome). A parameter found only on the
                -- algorithm channel belongs to the legacy Ready tier: it reports the
                -- failure recorded beside its algorithm (`AlgBinding.valueFailure?`,
                -- which no Model-C path writes) and never evaluates the algorithm
                -- channel, so a failure cannot heal and the argument's work is never
                -- repeated. The algorithm channel serves invocation and navigation
                -- (`resolveAlg (.param x)`), never this value read.
                match ctx.algEnv.lookupBinding x with
                | some binding => .error (binding.valueFailure?.getD Error.badArity)
                | none => .error (Error.unknownName x)
    | .sequenceConstruct _ _ =>
      evalSequenceConstructCounted e ctx env
    | .emptySequence depth =>
        let value := buildEmptySequenceValue depth
        pure (value, Result.valueCount value)
    | .sequenceSpread _ =>
        evalSequenceSpreadCounted e ctx env
    | .listLiteral elements =>
        evalListLiteralCounted elements ctx env
    | .algorithmExpr a => do
        -- An inline alias block (`{ F }`) is demanded as its TARGET, and a rejected demand is
        -- reported as its written target reference `F` reports it (`zeroArgumentDemandError?`,
        -- FA-OQ-1; C#: `EvalInlineAliasValue`).
        let wired <- resolveAliasTarget (wireToCaller ctx a) ctx
        match zeroArgumentDemandError? (some e) wired with
        | some err => .error err
        | none =>
          let r <- evalZeroArgumentDemandOutput wired ctx env
          pure (r, Result.valueCount r)
    | .capture rows => do
        -- A capture in value position is a value boundary: the body's supply
        -- is captured to one canonical value and re-counted as that value's
        -- valueCount.
        let r <- evalCaptureValue rows ctx env
        pure (r, Result.valueCount r)
    | .resolve n => do
        match ctx.callStack with
        | owner :: _ =>
            let resolved <- lookupLexicalProperty owner n ctx
            match zeroArgumentDemandError? (some e) resolved.alg with
            | some err => .error err
            | none =>
                withMissingOutputCtx (CtxMsg.property n) <| do
                  let counted <- evalZeroArgPropertyAccessCounted .lexical resolved.owner resolved.binding resolved.alg ctx env
                  pure (counted.fst, Result.valueCount counted.fst)
        | [] => .error (Error.unknownName n)
    | .index a i => do
        let ar <- eval a ctx env
        let ir <- eval i ctx env
        let n  <- expectInt ir
        if n < 0 then
          .error Error.badIndex
        else
          -- SELECTION IS A VALUE BOUNDARY: the selected element is returned
          -- exactly as stored and re-counted like any other plain value
          -- (`Result.valueCount`) — a selected sequence or list is ONE value, a
          -- selected `()` emits zero values, and only an explicit spread opens
          -- it. C#: the Index case of `EvalExpressionSpineCounted`.
          match Result.select? ar (Int.toNat n) with
          | some selected => pure (selected, Result.valueCount selected)
          | none => .error Error.badIndex
    | .dotMember o n fallback argsOpt => withCtx (CtxMsg.dotCall o n) do
        evalDotCallCounted o n fallback argsOpt ctx env
    | .call f args =>
        evalCallCountedExpr f args ctx env
    | .num n => pure (Result.atom n, 1)
    | .stringLiteral s => pure (Result.str s, 1)
    | .boolLiteral b => pure (Result.bool b, 1)
    | .unary op operand =>
        evalUnaryCounted op operand ctx env
    | .binary op a b =>
        evalBinaryCounted op a b ctx env
    | .comparison first links =>
        evalComparisonCounted first links ctx env

  /-- User-defined call evaluation with plain Result output.
      This is the Result projection of `evalUserCallCounted`: the counted twin
      owns argument binding (dual-view ABI, patterned/deconstruction/flat
      dispatch) and body evaluation, and the non-counted path only discards
      the emitted-count metadata (`reCountValueBoundary` is value-preserving).
      The CoreTests call projection parity guards pin this equivalence. -/
  partial def evalUserCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM Result := do
    let out <- evalUserCallCounted callee args ctx env
    pure out.fst

  /-- Conditional call evaluation with plain Result output.
      This is the Result projection of `evalConditionalCallCounted`: the
      counted twin owns argument assembly, clause matching, and branch body
      evaluation, and the non-counted path only discards the emitted-count
      metadata (`reCountValueBoundary` is value-preserving). The CoreTests
      call projection parity guards pin this equivalence. -/
  partial def evalConditionalCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM Result := do
    let out <- evalConditionalCallCounted callee args ctx env calleeName
    pure out.fst

  /-- Context-aware direct call evaluation for expression position with plain
      Result output. This is the Result projection of `evalCallCountedExpr`:
      the counted twin owns callee resolution and dispatch, including the
      `CtxMsg.call` error-context attachment, so contexts cannot drift between
      the plain and counted spellings. -/
  partial def evalCallExpr (f : Expr) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- evalCallCountedExpr f args ctx env
    pure out.fst

  /-- Dot-call evaluation with plain Result output.
      This is the Result projection of `evalDotCallCounted`: the counted twin
      owns the dot-call dispatch (receiver resolution, structural lookup,
      lexical fallback with receiver injection, zero-arg property access,
      conditional dispatch, and receiver-spread rules), and the non-counted
      path only discards the emitted-count metadata. The CoreTests dot-call
      projection parity guards pin this equivalence (values, error
      diagnostics, and evaluator state) case by case. -/
  partial def evalDotCall (target : Expr) (name : Ident)
      (fallback : Expr) (argsOpt : Option OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- evalDotCallCounted target name fallback argsOpt ctx env
    pure out.fst

  /-- Expression evaluation with plain Result output.
      This is the TOTAL Result projection of `evalCounted`: the counted
      evaluator owns the per-variant dispatch for every `Expr` constructor
      (leaves included), and this projection only discards the emitted-count
      metadata. Counted code calls it wherever a subexpression is read at a
      value boundary; that recursion is into strictly smaller work, never a
      same-node ownership cycle, because `evalCounted` has no arm that
      delegates back here. -/
  partial def eval (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let out <- evalCounted e ctx env
    pure out.fst

end

--------------------------------------------------------------------------------
-- Surface syntax support: implicit parameter detection
--------------------------------------------------------------------------------

/-- Probe whether a bare name should be treated as an implicit parameter.
    Used by surface syntax parsers to distinguish:
    - `Expr.param name` (implicit parameter) if name does not resolve lexically
    - `Expr.resolve name` (lexical reference) if name resolves in scope

    This uses the ownership-first lexical lookup order already encoded in `lookupLexical`:
    1. Local properties of the current algorithm
    2. Structural properties in parent chain
    3. Opens as fallback

    Returns:
    - `ok true`: name does not resolve → treat as implicit parameter
    - `ok false`: name resolves lexically → emit resolve, not param
    - `error`: propagates resolution errors (e.g., ambiguousOpen for diagnostics)

    Example usage in surface layer:
    ```
    -- Build initial algorithm with known properties/opens
    let alg := Algorithm.mk parent (Algorithm.normalParameters params) opens knownProps []
    let ctx := EvalCtx.push alg parentCtx

    -- For each free identifier token:
    match shouldTreatAsImplicitParam alg name ctx with
    | ok true  => emit (Expr.param name), add name to Algorithm.params
    | ok false => emit (Expr.resolve name)
    | error e  => report diagnostic (e.g., ambiguous open)
    ```

    SCOPE: this is the PROMOTION question only — whether a name that NOTHING
    binds becomes a new implicit parameter of the algorithm being elaborated.
    It is not the ownership question. Once a name IS bound, which binding the
    occurrence selects — an enclosing scope's parameter or a property — is
    `selectOwnedDeclaration` below, and the two are independent: promotion
    still stops at any visible property or opened name, while ownership
    decides between an already-established parameter and a property by owning
    scope. The caller must exclude already-established parameter bindings BEFORE
    invoking this probe. The probe itself only calls `lookupLexical`, the
    projection of `lookupLexicalProperty`: it does not inspect the owner's
    parameter declarations or the value/algorithm binding environments.
    A captured parameter therefore bypasses this probe; ownership selection
    below keeps it from losing to a farther property.

    OPEN TARGETS: `lookupLexical` resolves the level's opens lazily, and a target
    that resolves to nothing fails that resolution. The surface layer never lets
    such a failure reach promotion: it refuses every `open` target that resolves
    to nothing — an unknown head, a missing member, a non-public path step, from
    a name head or an inline block or module head alike — as a static diagnostic
    (C# `DiagnosticCode.UnresolvedOpenTarget`), and a dotted path whose head is
    not itself an open form (`open 5.N`, which `resolveAlgForOpen` rejects through
    its receiver recursion) as C# `DiagnosticCode.BadOpenForm`, so in an accepted
    program this probe only ever sees resolvable targets. Its `.error` arm reports
    genuine lookup failures; an ambiguous open is no longer one of them for a
    WRITTEN name: Q-29 A-U (decided 2026-10-06) makes a written name whose lookup
    reaches two different providers at one open level the surface layer's static
    rejection (C# `DiagnosticCode.AmbiguousOpen`), whether or not evaluation
    demands it, while `ambiguousOpen` stays the evaluator's verdict for a lookup
    only evaluation decides (a dot fallback the receiver decides) and for a
    host-built tree.

    NOTE: This function is used only for ordinary algorithms without an explicit
    parameter-pattern list.  Explicit ordinary algorithms and conditional branch
    bodies do NOT use implicit parameter inference.  Their written pattern in
    `Name(...)` is the complete input specification; free identifiers in the
    body must resolve lexically or produce an error.  Pattern-bound names are
    rewritten to `Expr.param` by the surface layer directly, without using this
    function. -/
def shouldTreatAsImplicitParam (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM Bool := do
  match <- evalAttempt (lookupLexical a name ctx) with
  | .ok _ => .ok false                      -- Name resolves → NOT a param
  | .error (Error.unknownName _) => .ok true  -- Name doesn't resolve → IS a param
  | .error e => .error e                    -- Propagate other errors (ambiguousOpen, etc.)


--------------------------------------------------------------------------------
-- Surface syntax support: owner-aware binding selection
--------------------------------------------------------------------------------

/-- One level of the surface layer's ordered OWNER CHAIN for a bare-name
    occurrence: the scopes enclosing that occurrence, innermost first.

    `parameters` are the parameter BINDINGS the level owns by NAME RESOLUTION —
    an algorithm's written and inferred parameters, or a conditional branch
    body's pattern binders. `properties` are the property names the level
    declares. Both are OWNED declarations; `opens` are deliberately absent,
    because they are not owned by the level and keep the separate later fallback
    policy of `lookupLexicalProperty`.

    `forwarded` are the parameters AUTOMATIC PARAMETER FORWARDING added to the
    level (Q-04, decided 2026-09-28): parameters the level receives only so that
    it can hand them on to a referenced callee that needs them, because no
    parameter binding of that name was available (`forwardingSource` below).
    They complete the level's signature for its callers — and a property of the
    same name still conflicts with them (`conflictingOwnedNames`) — but they are
    NEVER what a written name denotes: the owner walk does not consult them, so
    automatic forwarding cannot change what an existing name refers to. (Before
    the decision the surface layer re-selected every binding against the
    completed signatures, so a lifted parameter captured same-named written
    references — PV-01.)

    A CALLABLE ALIAS (FWD-02, binding indirection, decided 2026-10-01;
    `Algorithm.alias`) contributes no parameters at all: its callable is its
    target's, and it declares no signature of its own, so its level lists only the
    properties its own body declares — renaming the target's binders can never make
    the alias a declaration error.

    A `ScopeCtx` cannot serve as this chain: it carries `props` but no
    parameters, since by the time an `Algorithm` exists every ancestor-parameter
    reference in it is already an `Expr.param` and the binding lives in
    `ValEnv`. The chain is therefore surface-layer information, supplied to the
    walk while the front end is still deciding `param` vs `resolve`.

    The CHAIN, not a separately counted depth, is what says which owner is
    nearer: level `i` is nearer than level `j` exactly when `i < j`. -/
structure OwnerLevel where
  parameters : List Ident
  properties : List Ident
  forwarded : List Ident := []
  deriving Repr, DecidableEq

/-- Every parameter the level's callers bind: its name-resolution parameters and the
    ones automatic forwarding added (the completed signature). -/
def OwnerLevel.signature (level : OwnerLevel) : List Ident :=
  level.parameters ++ level.forwarded

/-- Surface declaration validity, checked after parameter-signature completion and
    before evaluation. Each property whose name is bound by this or an enclosing owner's
    completed signature — forwarded parameters included; a callable alias declares no
    parameters (see `OwnerLevel`) — is a declaration error,
    regardless of visibility or reference order. Pattern binders belong to their branch
    body. Open targets are not declarations and never conflict, but their HEAD name obeys
    the same owner chain (`elaborateOpenHead`). The surface layer reports each written
    conflicting declaration at its source name.
    C#: ParameterPropertyCollisionValidator. This is a front-end validity boundary;
    raw/recovery AST evaluation and lookup do not substitute for this check. -/
def conflictingOwnedNames (owner : OwnerLevel) (ancestors : List OwnerLevel := []) : List Ident :=
  owner.properties.filter fun name =>
    owner.signature.contains name || ancestors.any (fun outer => outer.signature.contains name)

def validOwnedDeclarations : List OwnerLevel -> Bool
  | [] => true
  | owner :: ancestors =>
      (conflictingOwnedNames owner ancestors).isEmpty && validOwnedDeclarations ancestors

/-- What the owner walk selects for a bare name, with the position of the
    DECIDING level in the supplied chain (0 = the occurrence's own body). -/
inductive OwnedDeclaration where
  | none
  | parameter (level : Nat)
  | property  (level : Nat)
  deriving Repr, DecidableEq

/-- THE owner walk, and the specification the surface layer's
    parameter/receiver classification and the editor's visible-name view all
    implement (C#: `ElaboratedScopeLookup.SelectOwnedDeclaration`).

    Search outward by owning scope: the first level that DECLARES `name` wins,
    and within that level an established PARAMETER takes precedence over a
    property. Consequences, in the order they matter:

    * a captured ancestor parameter beats a property owned by any FARTHER scope
      (the root's, and the prelude's — the prelude is simply the outermost
      property level, so `F(pi) = { pi + 1 }` binds the parameter);
    * a nearer property beats an outer parameter in an invalid recovery tree;
    * a level owning BOTH is invalid source (`validOwnedDeclarations`), but its
      recovery tree still selects the parameter consistently for direct and nested
      references, so editor behavior stays deterministic;
    * with several enclosing parameters of one name, the nearest wins, because
      it is reached first.

    `.none` means no owner declares the name; the caller then applies the
    unchanged lookup/promotion policy — `shouldTreatAsImplicitParam`
    above for a body that infers implicit parameters, and an ordinary
    `Expr.resolve` otherwise. -/
def selectOwnedDeclarationFrom : Nat -> List OwnerLevel -> Ident -> OwnedDeclaration
  | _, [],             _    => .none
  | i, level :: outer, name =>
      if level.parameters.contains name then .parameter i
      else if level.properties.contains name then .property i
      else selectOwnedDeclarationFrom (i + 1) outer name

def selectOwnedDeclaration (chain : List OwnerLevel) (name : Ident) : OwnedDeclaration :=
  selectOwnedDeclarationFrom 0 chain name

/-- Whether a bare-name occurrence elaborates to `Expr.param name` (a runtime
    parameter read, resolved through the inherited `ValEnv`/`AlgEnv`) rather
    than to `Expr.resolve name` (ordinary lexical property lookup). The value
    and the callable view of one occurrence share this single decision: the
    elaborated node is the same in both positions. -/
def elaboratesToParameter (chain : List OwnerLevel) (name : Ident) : Bool :=
  match selectOwnedDeclaration chain name with
  | .parameter _ => true
  | _            => false

/-- Static-open ownership (SYN-03 / F2). `open` is STATIC — it never opens a
    runtime value — but lexical ownership still applies to the target name:
    the HEAD of a static open target (`Lib` in `open Lib` or `open Lib.Sub`)
    is a bare-name occurrence like any other, so the surface layer classifies
    it with the SAME owner walk. When the nearest established binding is a
    parameter — written, inferred, collecting, grouped, a branch binder, or any
    of these captured from an enclosing owner (never one automatic forwarding
    added: `OwnerLevel.forwarded` owns no name) — that parameter owns the name
    and the head elaborates to `.param`, exactly as every other
    parameter-owned occurrence does. A `.param` head is NOT an open form
    (`Expr.openForm?` maps it to `none`), so open resolution rejects the
    target with `badOpenForm` and can never reach a farther same-named
    property: whether such a declaration exists changes nothing. The surface
    layer reports the parameter-owned head before evaluation (C#:
    `ParameterDetector.ClassifyOpenTargetHeads`,
    `DiagnosticCode.OpenTargetIsParameter`); `resolveAlgForOpen` therefore
    receives `.resolve` heads only for names no callable parameter owns, and
    its direct lexical lookup (`lookupLexicalDirect`) is sound for them.
    The chain carries CALLABLE bindings: the never-called program root's
    phantom signature is omitted from it by the surface layer (its names are
    unresolved root inputs, reported as such by evaluation, not parameters
    that could own an open target). -/
def elaborateOpenHead (chain : List OwnerLevel) (name : Ident) : Expr :=
  if elaboratesToParameter chain name then .param name else .resolve name

--------------------------------------------------------------------------------
-- Surface syntax support: implicit argument resolution
--------------------------------------------------------------------------------

/- **Implicit argument resolution** (surface syntax pass — runs after parameter
   detection):

   When a property body contains a bare value-position reference to a sibling
   property that REQUIRES supplied arguments — one an ordinary call supplying
   zero arguments could not bind (`liftsBareValueReference` below) — the
   surface layer rewrites that reference into an explicit call, passing the
   sibling's parameter-pattern captures as arguments. Each argument is the
   PARAMETER binding the referencing body can already reach under that name —
   its own, or an enclosing owner's captured parameter or branch binder — and
   only a name no parameter binding supplies is lifted into the referencing
   property's own parameter-pattern list, as a FORWARDED parameter that no
   written name denotes (`forwardingSource` below; Q-04, decided 2026-09-28:
   automatic parameter forwarding must not change what an existing name refers
   to). Properties, opened names and builtins are never forwarded as
   parameters.

   A reference to a sibling that ACCEPTS zero supplied arguments — no
   parameters, or only a top-level collecting parameter such as `Roll(*xs)` —
   is never rewritten, in any position (Q-03, decided 2026-09-28): declaring a
   parameter does not by itself make a bare reference a call. It stays
   `.resolve`, the zero-argument value demand that `zeroArgumentDemandError?`
   accepts and `isCacheableZeroArgPropertyAlgorithm` sends through the property
   cache, so `Roll == Roll` reads ONE value; only a written call (`Roll()`,
   `Roll(args)`) evaluates afresh. Before the decision the surface pass lifted
   every sibling that DECLARED a parameter, so a collecting-only sibling in an
   operator, list, index, spread, strict-Math or alias position became the
   fresh call `Roll(xs*)` and bypassed the cache that its neutral positions
   read. The evaluator was never involved: it evaluates whichever tree the
   surface pass produces, and the law `bare_reference_lifts_iff_not_cacheable`
   (`KatLangArityLaws.lean`) states that an unlifted reference is always a
   cacheable demand.

   Formula lifting is by BINDING NAME, regardless of how many times a name
   occurs in the sibling's parameter patterns (decided 2026-09-29, reversing
   the same day's Q-72 refusal): the referencing body receives ONE parameter
   per name (first occurrence first, skipping names already bound, inside a
   group too), and the rewritten call supplies that one binding to every
   occurrence — `P(x, x) = x` / `D = [P]:0` becomes `D(x) = [P(x, x)]:0`,
   exactly as `H = F + G` with `F(x)` and `G(x)` becomes
   `H(x) = F(x) + G(x)`. The evaluator binds `P`'s two slots as it binds any
   call: both read the same caller binding, so nothing is merged — the
   repeated-name constraint (Q-05; the binder's `bindNeedName`, formerly
   `bindParameterPattern`) concerns independently supplied arguments.

   THE ALIAS AND BARE-FORWARDING RULES (FWD-02, decided 2026-09-29–30; binding
   indirection 2026-10-01) come first: a body whose ONE written row is a bare
   reference to a callable that DECLARES parameterized structure
   (`Algorithm.declaresParameterizedStructure`) is not a formula. An open body is
   a CALLABLE ALIAS (`Algorithm.alias`) — `A = P` names `P`'s callable itself,
   with no wrapper and no copied signature, so a call through it is `P`'s own
   call with `P`'s two independent arguments. A written parameter list or a
   clause branch is BARE
   FORWARDING (`bareForwardingRow`): each of the callee's parameters is supplied
   from an EXISTING compatible binding of the SAME NAME — `Q(x) = P` is
   `Q(x) = P(x, x)`, `G(x, y) = F` with `F(y, x)` is `F(y, x)` — never renamed,
   never matched by position, never added to the closed list, and never
   reshaped from same-named leaves (`G(x) = Single` with `Single([x])` is
   rejected). The explicit call `A(p) = F(p)` is deliberately different: an
   ordinary written call, whose arguments need not match the callee's names. A
   written call `G = F(exprs)` is an ordinary formula whose parameters are the
   free names written in `exprs`.

   Example:
     Surface:   `{ A = x + 1  B = A * 2 }`
     After detection: A.params = [x], B.params = []
     After resolution: B.params = [x], B.output = [Call(A, [Param(x)]) * 2]

     Surface:   `{ A = x + 1  F(x) = { B = A * 2  B } }`
     After resolution: B.params = [], B.output = [Call(A, [Param(x)]) * 2]
       (the `x` is F's: B reuses the captured parameter instead of lifting its own)

     Surface:   `{ A(*xs) = xs.count  B = A * 2 }`
     After resolution: B.params = [], B.output = [Resolve(A) * 2]

   Recursive parameter patterns are preserved by this surface pass: lifting
   `x, *items`, `(*items)`, or `((*history), previous)` keeps that shape
   instead of reconstructing ordinary capture parameters from flattened names.
   A narrow forwarding rule also permits a bare helper reference with one
   forwardable variadic supply — a lone collector inside the helper's one
   group, `H((*xs))` (a helper whose only parameter is a top-level collector
   accepts zero supplied arguments and is never rewritten) — to use a
   containing algorithm's single top-level variadic supply by shape rather
   than by capture-name equality. This is not a general positional
   parameter-matching rule.

   **Transitive ordering invariant**: Properties must be processed in dependency
   order. If property B references property A (even if A currently has zero
   parameters), then A must be resolved before B, so that A's final parameter
   list (which may itself have been augmented by transitive dependencies) is
   visible when resolving B's implicit arguments.

   This ordering is computed by topological sort over ALL bare sibling property
   references — not just those with parameters at detection time — because a
   property with initially zero parameters may acquire parameters through its
   own transitive dependencies during resolution.

   Formally:
     Let G = (properties, edges) where edge (B, A) exists iff B's output
     expressions contain a bare Resolve(A) and A is a sibling property.
     Process properties in topological order of G.
     At each step, the parameter map is updated with the processed property's
     final parameter-pattern signature before processing subsequent dependents.

   Cycles (mutually recursive siblings) are not excluded from lifting: each
   cycle — a strongly connected component of G — is ordered as ONE unit,
   processed once every sibling its members reference outside it has been,
   its members in DECLARATION order, each seeing the signatures completed so
   far (the C# `PropertyDependencyGraph.TopologicalOrder`). That fallback is
   confined to the cycle's members: a property that references a cycle is
   not part of it, so it is processed after all of the cycle's members and
   sees their final signatures, whatever the declaration order. C# also
   anticipates reads through soft preferences: when those close a cycle
   around hard units, the combined component settles before outside
   consumers, retaining the hard scheduler's order inside it (no fixed
   point or call recomputation). This is the
   one documented way two reaches of a node can observe different sibling
   signatures (the "sibling CYCLE" exception of the shared-DAG guarantee in
   `docs/design/language-rules/evaluator-and-hosting.md`). -/

/-- **Implicit-lifting eligibility** (Q-03, decided 2026-09-28; surface syntax
    support — the specification of the surface pass's one lifting decision).
    A bare value-position reference is rewritten into an implicit forwarding
    call exactly when its callee's lifting signature REQUIRES supplied
    arguments: when `ParameterPattern.minimumSuppliedSlots` — the binder's own
    arity rule, the very count `Algorithm.acceptsZeroSuppliedArguments` reads —
    is nonzero. A signature that accepts zero supplied arguments (no pattern, or
    only a top-level collecting capture) is never lifted: its reference stays
    the cached zero-argument value demand. One predicate therefore decides both
    halves, and they cannot disagree about a callable (see
    `bare_reference_lifts_iff_not_cacheable`).

    The argument is the callee's LIFTING signature (`Algorithm.liftingSignature?`,
    one contract for every kind since the unified formula-lifting law of
    2026-09-30): a user algorithm's `parameterPatterns`, a builtin's callable
    interface, a clause family's derived whole-slot signature. C#:
    `ImplicitArgumentResolver.RequiresSuppliedArguments` over
    `CallableSignature.AcceptsZeroSuppliedArguments` /
    `ParameterPattern.AcceptsZeroSuppliedSlots`. -/
def liftsBareValueReference (signature : List ParameterPattern) : Bool :=
  ParameterPattern.minimumSuppliedSlots signature != 0

/-!
### The unified formula-lifting law (decided 2026-09-30)

In an inferring formula, a resolved callable reference is lifted when that occurrence is used as
a VALUE, and its lifting signature is derived from the resolved callable's contract, independent
of the callable's category or the route that resolved it. Two operations, both specified here and
implemented by the C# front end (Lean has no front end):

- `LiftingRole` / `liftingSlotRole` — the role a slot gives the reference that fills it, decided
  by the slot's IMMEDIATE consumer (C# `FormulaLiftingRoles`). Every operator operand, index part,
  spread operand, list and capture element and output row is a VALUE slot; a call's callee is
  CALLABLE; a call's arguments take the roles `liftingSlotRole` gives them. A compound expression
  in a callable slot is still examined: its own children take the roles of THEIR consumers
  (`Twice(A)` keeps `A`, `Twice(A + 0)` lifts it). Laziness does not change a role: an `if` branch
  is a value slot whether or not a run selects it, exactly as a free name written there is a
  parameter (PAR-03).
- `Algorithm.liftingSignature?` — the one lifting signature of every kind.

A lone bare row is not a formula (FWD-02 completes it — a callable alias or bare forwarding,
`Algorithm.declaresParameterizedStructure`), and the never-called root keeps a bare row as the
callable's own rejection. A reference to a callable alias takes the roles and the lifting
signature of the alias's NORMALIZED TARGET (the surface pass resolves the chain first), never of
the alias itself: no alias-specific role exists. -/

/-- The role a slot gives the reference that fills it (C#: `LiftingRole`). -/
inductive LiftingRole where
  | value
  | callable
  deriving Repr, BEq, DecidableEq

/-- What a consumer needs to know about the callable it calls: its KIND, which elaboration never
    changes (C#: `LiftingCalleeKind`). A `strictValue` callee is a Math member or a host
    operation (neither is modeled here beyond this kind). -/
inductive LiftingCalleeKind where
  | dynamic
  | user
  | family
  | builtin (b : Builtin)
  | strictValue
  deriving Repr, BEq

/-- The callee KIND of a resolved callable (C#: `FormulaLiftingRoles.OfAlgorithm`), which decides the
    roles of a call's argument positions (`liftingSlotRole`). A callable ALIAS has no kind of its own:
    a reference to it takes the kind — and so the roles — of its NORMALIZED TARGET (X-45: `A = abs` /
    `K = A(Inc)` gives `Inc` the value role `abs` gives it). Math members and host operations are
    `strictValue` callees, a kind the surface pass reads from their identity; Lean models them only
    as that kind, so they are not derived from an algorithm here. -/
def Algorithm.liftingCalleeKind? : Algorithm -> Option LiftingCalleeKind
  | .mk _ _ _ _ _ _ => some .user
  | .builtin b => some (.builtin b)
  | .conditional _ _ _ _ => some .family
  | .alias _ _ _ _ _ => none

/-- A loop builtin invokes its step (position 0); its count and initial state are values. -/
def Builtin.isLoop : Builtin -> Bool
  | .whileBuiltin | .repeatBuiltin => true
  | _ => false

/-- The role of supplied position `position` of a builtin: only a callback keeps its callable
    identity. The collection, the value controls and a SURPLUS position beyond the signature are
    values — a surplus slot is value-evaluated like a value slot before the arity verdict, just as
    every argument of a Math member, a host operation and a clause family is a value whatever the
    call's arity, so no role depends on how many arguments a call supplies. A loop's step is
    invoked and every later position is a value; `if`, `atoms` and `range` take values only. -/
def builtinLiftingSlotRole (b : Builtin) (position : Nat) : LiftingRole :=
  match sequenceBuiltinMetadata? b with
  | some metadata => if metadata.slotRole position == .callback then .callable else .value
  | none => if b.isLoop && position == 0 then .callable else .value

/-- Whether every position of a builtin is a value slot (a position after a spread slot is known
    only at run time, so it is a value slot only then). -/
def builtinEverySlotIsValue (b : Builtin) : Bool :=
  match sequenceBuiltinMetadata? b with
  | some metadata => metadata.suffixArgs.all (fun suffix => suffix.kind != .algorithm)
  | none => !b.isLoop

/-- THE ROLE TABLE of a call's supplied positions (C#: `FormulaLiftingRoles.SlotRole`): a clause
    family, a Math member and a host operation demand every argument's value (a family before any
    clause is tried, PAT-07); a builtin reads its registry role; a user callable's argument stays
    NEUTRAL — its binder decides at run time, a plain capture keeping both channels — and so does
    a callee known only at run time. `positionKnown` is false once a spread slot precedes it. -/
def liftingSlotRole (callee : LiftingCalleeKind) (position : Nat) (positionKnown : Bool) : LiftingRole :=
  match callee with
  | .family | .strictValue => .value
  | .builtin b =>
      if positionKnown then builtinLiftingSlotRole b position
      else if builtinEverySlotIsValue b then .value else .callable
  | .user | .dynamic => .callable

/-- The top-level argument positions of a clause head: the head's own argument list
    (`sequenceValue`), or its lone pattern (`Pattern.topLevelArity`). -/
def Pattern.topLevelPositions : Pattern -> List Pattern
  | .sequenceValue ps => ps
  | p => [p]

/-- The name one clause votes for a position: the plain binder it binds there. A literal, a
    structural pattern and a binderless group name nothing. -/
def Pattern.positionName? : Pattern -> Option Ident
  | .bind x => some x
  | _ => none

/-- The name the clauses agree on for position `position`: every vote equal, at least one vote. -/
def familyPositionName? (heads : List Pattern) (position : Nat) : Option Ident :=
  match heads.filterMap (fun head => (head.topLevelPositions[position]?).bind Pattern.positionName?) with
  | [] => none
  | first :: rest => if rest.all (· == first) then some first else none

/-- A CLAUSE FAMILY'S LIFTING SIGNATURE (decided 2026-09-30): one whole-value slot per top-level
    argument position (the family's common arity, PAT-03), each named by the plain parameter the
    clauses that bind it agree on, the names of different positions distinct. The lifted call hands
    the family the caller's arguments whole, so dispatch is exactly the explicit call's. A family
    whose clauses leave a position unnamed, name it differently, or give two positions one name has
    none (`none`): it stays explicitly callable, and a formula that would lift it is the C# front
    end's `UnliftableClauseFamily`. No name is ever invented.
    C#: `ImplicitArgumentResolver.DeriveFamilyLiftingSignature`. -/
def familyLiftingSignature? (branches : List CondBranch) : Option (List ParameterPattern) :=
  match branches with
  | [] => none
  | first :: _ =>
      let heads := branches.map (·.pattern)
      let arity := first.pattern.topLevelArity
      if heads.any (fun head => head.topLevelArity != arity) then none
      else
        let names := (List.range arity).map (familyPositionName? heads)
        let named := names.filterMap id
        if named.length == arity && named.eraseDups.length == named.length
        then some (named.map (fun name => ParameterPattern.capture { name := name }))
        else none

/-- A builtin's callable interface as formula lifting reads it (C#: `ToolingPlainSignature`): a
    collection builtin's registry parameters, `if`'s three, `atoms`' value, `range`'s bounds, and a
    loop's step (and count) with its variadic initial state `*init`. -/
def builtinLiftingSignature (b : Builtin) : List ParameterPattern :=
  let fixed (names : List Ident) := names.map (fun name => ParameterPattern.capture { name := name })
  match sequenceBuiltinMetadata? b with
  | some metadata => metadata.parameters.map ParameterPattern.capture
  | none =>
      match b with
      | .ifBuiltin => fixed ["condition", "whenTrue", "whenFalse"]
      | .whileBuiltin => fixed ["step"] ++ [.capture { name := "init", kind := .collecting }]
      | .repeatBuiltin => fixed ["step", "count"] ++ [.capture { name := "init", kind := .collecting }]
      | .atomsBuiltin => fixed ["value"]
      | .rangeBuiltin => fixed ["start", "stop"]
      | _ => []

/-- THE ONE LIFTING SIGNATURE of every algorithm kind (the unified formula-lifting law): a user
    algorithm's parameter patterns, a builtin's callable interface, a clause family's derived
    whole-slot signature (or none). It is also the callable's FORWARDING CONTRACT — the names
    bare forwarding supplies by (`bareForwardingRowOf`). A callable alias has none of its own:
    every callable question is asked of its NORMALIZED TARGET (the surface pass resolves the
    alias chain first, exactly as the evaluator does, `resolveAliasTarget`), so lifting and
    forwarding through an alias are the target's, never a copied signature.
    C#: `ImplicitArgumentResolver.TryResolveLiftable`. -/
def Algorithm.liftingSignature? : Algorithm -> Option (List ParameterPattern)
  | .mk _ parameters _ _ _ _ => some parameters
  | .builtin b => some (builtinLiftingSignature b)
  | .conditional _ _ branches _ => familyLiftingSignature? branches
  | .alias _ _ _ _ _ => none

/-- **Lone-row eligibility** (FWD-02, binding indirection — decided 2026-10-01; surface syntax
    support — the specification of the surface pass's decision for a body whose ONE written
    row is a bare reference). Such a row names the callable ITSELF, so the decision reads the
    DECLARED callable structure of the ONE identity name resolution selects (owner walk →
    prelude → opens → structural dot path, looking through aliases to the normalized target),
    never the lookup route and never zero-argument acceptance: a callable that DECLARES
    PARAMETERIZED STRUCTURE — every builtin (`if`, the callback builtins and the loops
    included), every clause family (nameable or not), a user algorithm with at least one
    parameter pattern (`Only(*xs)` included, although `Only()` is legal), a Math member or a
    host operation — makes an OPEN body a callable ALIAS (`Algorithm.alias`: binding
    indirection, no wrapper, no inherited signature) and a CLOSED body bare forwarding
    (`bareForwardingRowOf`). A zero-parameter callable is no alias target: `A = Z` stays an
    ordinary property whose body reads `Z`, cached as usual. C#:
    `ImplicitArgumentResolver.DeclaresParameterizedStructure`. -/
def Algorithm.declaresParameterizedStructure : Algorithm -> Bool
  | .mk _ parameters _ _ _ _ => !parameters.isEmpty
  | .builtin _ => true
  | .conditional _ _ _ _ => true
  | .alias _ _ _ _ _ => true

/-- The tree of a WRITTEN sequence group `(e1, …, en)` (SYN-06): `()` for no
    items, the one item itself for a lone non-spread item (a one-slot group IS
    its content; there is no one-item sequence value), and otherwise a capture of
    the slots — a lone spread slot `(xs*)` included, which a group keeps.
    C#: `ImplicitArgumentResolver.BuildSequenceArgument`. -/
def sequenceArgument : List Expr -> Expr
  | [] => .emptySequence 0
  | [only] =>
      match only with
      | .sequenceSpread operand => .capture [.sequenceSpread operand]
      | _ => only
  | first :: second :: rest => .capture (first :: second :: rest)

mutual
  /-- **Pattern reconstruction** (FWD-02; surface syntax support — the ONE
      reconstruction the alias and bare-forwarding rules share). The argument that
      rebuilds one parameter pattern from its own bindings — exactly the argument a
      programmer would write:

      * a fixed capture is its binding, `x`;
      * a collecting capture re-spreads the items it collected, `xs*`, at any
        level — so a `[first, *middle, last]` pattern rebuilds
        `[first, middle*, last]`;
      * a sequence pattern rebuilds a sequence (`sequenceArgument`) and a list
        pattern a list, of the same shape, at every depth — never the other kind;
      * the unpacking receiver (never written in a signature) rebuilds the list of
        its items.

      BARE FORWARDING rebuilds a callee's structural parameter this way only when the
      forwarding body declares the SAME pattern (`bareForwardingArgument`). (A callable
      alias rebuilds nothing: it IS its target's callable, `Algorithm.alias`.)
      C#: `ImplicitArgumentResolver.BuildPatternArgument`; `CoreTests/AliasForwarding.lean`. -/
  def ParameterPattern.sourceArgument : ParameterPattern -> Expr
    | .capture parameter =>
        match parameter.kind with
        | .normal => .param parameter.name
        | .collecting => .sequenceSpread (.param parameter.name)
    | .sequenceValue items => sequenceArgument (ParameterPattern.sourceArguments items)
    | .listValue items => .listLiteral (ParameterPattern.sourceArguments items)
    | .unpacking items => .listLiteral (ParameterPattern.sourceArguments items)

  /-- The rebuilt arguments of a pattern list: one per pattern, in order. -/
  def ParameterPattern.sourceArguments : List ParameterPattern -> List Expr
    | [] => []
    | pattern :: rest => ParameterPattern.sourceArgument pattern :: ParameterPattern.sourceArguments rest
end

mutual
  /-- Whether two parameter patterns declare the same CONTRACT — the same kind and
      shape, the same names and the same collectors at every depth. Bare forwarding
      compares whole TOP-LEVEL patterns by this relation, never their leaf names alone
      (C#: `ParameterPattern.ContractComparer`, never display equality). -/
  def ParameterPattern.sameContract : ParameterPattern -> ParameterPattern -> Bool
    | .capture left, .capture right => left.name == right.name && left.kind == right.kind
    | .sequenceValue left, .sequenceValue right => ParameterPattern.sameContracts left right
    | .listValue left, .listValue right => ParameterPattern.sameContracts left right
    | .unpacking left, .unpacking right => ParameterPattern.sameContracts left right
    | _, _ => false

  /-- Pairwise `sameContract` over two pattern lists of equal length. -/
  def ParameterPattern.sameContracts : List ParameterPattern -> List ParameterPattern -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        ParameterPattern.sameContract left right && ParameterPattern.sameContracts lefts rights
    | _, _ => false
end

/-- BARE FORWARDING's verdict for one callee parameter pattern (`bareForwardingArgument`). -/
inductive BareForwardingVerdict where
  /-- An existing compatible binding supplies the parameter: this argument. -/
  | supplied (argument : Expr)
  /-- A collector that no binding of its name supplies: it receives no argument. -/
  | optional
  /-- No existing compatible binding supplies the parameter: the definition is a
      front-end error (C# `DiagnosticCode.UnforwardableParameter`). -/
  | unforwardable
  deriving Repr

/-- The argument that forwards an existing binding named like the capture
    `destination`: a collecting SOURCE binding re-spreads into a collecting destination
    (FWD-01, `spread (collect S) = S`); every other pair passes the binding as ONE
    argument, unchanged — only the source binding's kind decides a spread (FWD-02). -/
def bareForwardedBinding (destination : CallableParameter) (sourceKind : ParameterKind) : Expr :=
  if destination.kind == .collecting && sourceKind == .collecting then
    .sequenceSpread (.param destination.name)
  else
    .param destination.name

/-- **Bare forwarding** (FWD-02, decided 2026-09-30; surface syntax support — the
    specification of the surface pass's decision for a CLOSED body whose ONE written
    row is a bare reference to a callable that declares parameters: a written
    parameter list `A(p) = F` or a clause branch `A(head) = F`). Bare forwarding
    REUSES EXISTING COMPATIBLE BINDINGS BY NAME: it never renames a binding, never
    adds one to the closed list, never matches by position, and never converts an
    incompatible top-level parameter pattern because nested leaf names coincide. The
    inputs:

    * `own` — the closed body's own TOP-LEVEL parameter patterns (a branch: its
      literal-free top-level head items, `Pattern.bareForwardingOwn`);
    * `ownNames` — every name the body binds, at any depth;
    * `captured` — the ENCLOSING parameter bindings a written name would denote
      in the body when the body binds no such name itself (Q-04: the
      `.capturedParameter` results of `forwardingSource`), with their kinds.

    One callee parameter pattern is then:

    * a capture `n`: supplied by the body's own top-level capture `n`
      (`bareForwardedBinding` decides a re-spread from that SOURCE's kind); if the
      body binds `n` only INSIDE one of its structural patterns, that `n` is an
      element, not a whole-value parameter — unforwardable; otherwise supplied by
      the enclosing binding `n`, if any; otherwise a collector is OPTIONAL (it
      accepts no argument) and a fixed capture is unforwardable;
    * a structural pattern: supplied only by one of the body's own top-level
      patterns with the SAME contract (`ParameterPattern.sameContract`), rebuilt as
      itself (`ParameterPattern.sourceArgument`) — never assembled from same-named
      leaves, and never from enclosing bindings, which are plain named values.

    So `F(p) = p * 2` / `A(p) = F` forwards `A.p` to `F.p`, while `F(q) = q * 2` /
    `A(p) = F` is rejected (never `F(p)`), `F(p, q)` / `A(p) = F` is rejected (never
    an inferred `q`), `F(y, x)` / `G(x, y) = F` is `F(y, x)` BY NAME (never positional),
    `Single([x])` / `G(x) = Single` is rejected while `G([x]) = Single` forwards, and an
    unused parameter of the body (`A(p, unused) = F`) stays unused. The explicit call
    `A(p) = F(p)` is an ordinary written call and never reaches this rule; formula
    lifting (`forwardingSource`) is a separate mechanism, which infers into an OPEN
    body what bare forwarding refuses to add to a closed one.
    C#: `ImplicitArgumentResolver.BareForwardingArgument`;
    `KatLangArityLaws.lean`, `CoreTests/AliasForwarding.lean`. -/
def bareForwardingArgument (own : List ParameterPattern) (ownNames : List Ident)
    (captured : List CallableParameter) : ParameterPattern -> BareForwardingVerdict
  | .capture parameter =>
      match ParameterPattern.topLevelCaptureKind? parameter.name own with
      | some kind => .supplied (bareForwardedBinding parameter kind)
      | none =>
          if ownNames.contains parameter.name then
            .unforwardable
          else
            match captured.find? (fun binding => binding.name == parameter.name) with
            | some binding => .supplied (bareForwardedBinding parameter binding.kind)
            | none => if parameter.kind == .collecting then .optional else .unforwardable
  | pattern =>
      if own.any (ParameterPattern.sameContract pattern) then
        .supplied (ParameterPattern.sourceArgument pattern)
      else
        .unforwardable

/-- Bare forwarding of a whole callee signature: the supplied arguments in the
    callee's parameter order (an optional collector contributes none), or `none` when
    any parameter is unforwardable — the front-end rejection. -/
def bareForwardingArguments (own : List ParameterPattern) (ownNames : List Ident)
    (captured : List CallableParameter) : List ParameterPattern -> Option (List Expr)
  | [] => some []
  | parameter :: rest =>
      match bareForwardingArgument own ownNames captured parameter,
            bareForwardingArguments own ownNames captured rest with
      | .supplied argument, some arguments => some (argument :: arguments)
      | .optional, some arguments => some arguments
      | _, _ => none

/-- The row a bare-forwarding body elaborates to: the call of `callee` with the
    forwarded arguments; the BARE NAME when nothing is forwarded (every callee
    parameter an optional collector, so the callee works with no arguments and the
    row is Q-03's cached value read, never an invented call); or `none` when a
    parameter is unforwardable (C# `DiagnosticCode.UnforwardableParameter`, the row
    left as written). -/
def bareForwardingRow (callee : Ident) (own : List ParameterPattern) (ownNames : List Ident)
    (captured : List CallableParameter) (signature : List ParameterPattern) : Option Expr :=
  match bareForwardingArguments own ownNames captured signature with
  | none => none
  | some [] => some (.resolve callee)
  | some arguments => some (.call (.resolve callee) arguments)

/-- Why a closed lone row cannot bare-forward its callee. -/
inductive BareForwardingRejection where
  /-- A callee parameter that no existing compatible binding of its name supplies
      (C# `DiagnosticCode.UnforwardableParameter`). -/
  | unforwardableParameter
  /-- The callee — through every alias, its NORMALIZED target — has NO forwarding contract
      at all: an unnameable clause family names no input to forward by (narrowed Q-77,
      decided 2026-10-01; C# `DiagnosticCode.UnforwardableCallable`). -/
  | noForwardingContract
  deriving Repr, DecidableEq

/-- **Bare forwarding of a callable** (FWD-02 with narrowed Q-77, decided 2026-10-01): the row a
    CLOSED body whose one row is the bare `callee` elaborates to, given the callee's NORMALIZED
    target. The forwarding contract is the target's lifting signature
    (`Algorithm.liftingSignature?`, identity-keyed, so an alias, an opened or dotted member, a
    builtin, a Math member, a host operation and a nameable family forward alike); a target
    without one — an unnameable clause family — is the front-end error
    `noForwardingContract`, never a silent zero-argument demand. A callable alias of such a
    family is still a valid ALIAS (`unnameable_family_can_be_aliased`): aliasing needs callable
    identity, forwarding needs names. C#: `ImplicitArgumentResolver.TryCompleteLoneCalleeRow`. -/
def bareForwardingRowOf (callee : Ident) (own : List ParameterPattern) (ownNames : List Ident)
    (captured : List CallableParameter) (target : Algorithm) : Except BareForwardingRejection Expr :=
  match target.liftingSignature? with
  | none => .error .noForwardingContract
  | some signature =>
      match bareForwardingRow callee own ownNames captured signature with
      | some row => .ok row
      | none => .error .unforwardableParameter

/-- A clause branch's OWN inputs for bare forwarding: a top-level sequence pattern IS
    the branch's parameter list and any other head is its one parameter; an item that
    holds a literal at any depth declares no literal-free pattern, so it offers
    nothing (its binders still count as bound names, `Pattern.boundNames`). C#:
    `BareForwardingSources.OfBranchHead`. -/
def Pattern.bareForwardingOwn (head : Pattern) : List ParameterPattern :=
  let items := match head with
    | .sequenceValue items => items
    | other => [other]
  items.filterMap Pattern.parameterPattern?

/-- Where AUTOMATIC PARAMETER FORWARDING takes the argument for one callee parameter
    (Q-04, decided 2026-09-28): see `forwardingSource`. -/
inductive ForwardingSource where
  /-- The referencing body binds the name itself: a written or inferred parameter, or
      its branch binder. -/
  | ownParameter
  /-- An enclosing owner binds it (at chain level `level`, a clause-branch binder
      included): forwarding hands the callee THAT binding. -/
  | capturedParameter (level : Nat)
  /-- No parameter binding exists and the body infers its parameters: it receives a new
      FORWARDED parameter of that name (`OwnerLevel.forwarded`). -/
  | forwardedParameter
  /-- No parameter binding exists and the body's inputs are CLOSED (a written parameter
      list or a branch pattern): nothing is forwarded. -/
  | unavailable
  deriving Repr, DecidableEq

/-- **Automatic parameter forwarding** (Q-04, decided 2026-09-28; surface syntax
    support — the specification of the surface pass's one forwarding decision).
    THE LAW: automatic parameter forwarding must not change what an existing name
    refers to. Forwarding therefore reuses PARAMETER bindings only: when a lifted
    reference forwards a callee parameter `name` from the referencing body — level 0
    of `chain`, the body's name-resolution owner chain, innermost first — the argument
    is the binding the owner walk (`selectOwnedDeclaration`) gives a WRITTEN occurrence
    of `name` there, if that binding is a parameter: the body's own
    (`.ownParameter`), or an accessible captured parameter of an enclosing owner, a
    clause-branch binder included (`.capturedParameter`). Properties, opened names,
    module members and prelude builtins are never forwarded as parameters: when the
    walk finds a property, or nothing, an inferring body (`inferring = true`) receives a
    new forwarded parameter and a closed body gets nothing. So a body never acquires a
    parameter that would capture a name it already reads from an enclosing owner — the
    former rule, which lifted every callee parameter the body did not bind itself and
    then re-selected the written references against the completed signature, made
    `A = y + 1` / `F(y) = { G = y * 1000 + A ⏎ H(y) = G ⏎ H(100) }` / `F(3)` give 100101
    where the inlined helper gives 3004 (PV-01) — and a forwarded parameter is never
    what a written name denotes (`OwnerLevel.forwarded`; the owner walk does not read
    it). C#: `ImplicitArgumentResolver.ForwardableParameters` (the enclosing parameter
    bindings), `LiftSignature`, `MissingClosedListForwardingNames`,
    `BuildImplicitCallArguments`; laws in `KatLangArityLaws.lean`, guards in
    `CoreTests/ForwardingBindings.lean`.

    FORMULA LIFTING IS BY BINDING NAME, regardless of how many times the name
    occurs in the callee's parameter patterns: every capture occurrence of `name`
    receives the one source this function returns, so a callee that repeats a
    name (`P(x, x)`, `P((x, a), x)`) receives the caller's ONE binding at every
    occurrence — `D = [P]:0` is `D(x) = [P(x, x)]:0` — the rule by-name sharing
    ACROSS callees already follows (`H = F + G` is `H(x) = F(x) + G(x)`). Each
    occurrence is then an ordinary argument slot reading that binding; the
    binder's repeated-name constraint (Q-05) concerns independently supplied
    arguments and merges nothing. (Decided 2026-09-29, reversing the same day's
    Q-72 refusal of such callees; Lean models no signature construction.) This
    decision is FORMULA lifting's: a body whose one row is the bare callee is a
    callable alias (`Algorithm.alias`), which reuses no binding and gains no
    parameter, or bare forwarding (`bareForwardingArgument`), which reuses the same
    parameter bindings by name — the body's own, else the `.capturedParameter`
    this function selects — but never adds one: what a formula in an OPEN body
    infers (`.forwardedParameter`), a closed body's bare row rejects. -/
def forwardingSource (chain : List OwnerLevel) (inferring : Bool) (name : Ident) : ForwardingSource :=
  match selectOwnedDeclaration chain name with
  | .parameter 0 => .ownParameter
  | .parameter (level + 1) => .capturedParameter (level + 1)
  | _ => if inferring then .forwardedParameter else .unavailable

/-- The chain level whose parameter binding a forwarding reuses, if it reuses one. -/
def ForwardingSource.reusedLevel? : ForwardingSource -> Option Nat
  | .ownParameter => some 0
  | .capturedParameter level => some level
  | .forwardedParameter => none
  | .unavailable => none

/-- The chain level whose parameter the owner walk selected, if it selected one. -/
def OwnedDeclaration.parameterLevel? : OwnedDeclaration -> Option Nat
  | .parameter level => some level
  | .property _ => Option.none
  | .none => Option.none

/-- The chain once forwarding added a parameter `name` to the referencing body. -/
def forwardParameter : List OwnerLevel -> Ident -> List OwnerLevel
  | [], _ => []
  | level :: outer, name => { level with forwarded := level.forwarded ++ [name] } :: outer

-- Surface syntax support: while/repeat initial-state boundaries
--------------------------------------------------------------------------------

/- **Ordinary parentheses** construct sequence values.  There is no special
   "double-parens" syntax.  `((expr))` in any position is nested sequence-value
   construction.  `f((a + b) mod 2, c)` parses normally as two arguments.

   **while/repeat initial state** preserves explicit argument boundaries.
   The evaluator accepts variable arity for these builtins:

     while(step, s1, s2, ..., sk)         -- k ≥ 1
     repeat(step, count, s1, s2, ..., sk) -- k ≥ 1

   Each explicit init argument is supplied independently (one demand cell,
   never evaluated by the loop itself) and becomes exactly one initial state
   slot.  Therefore `repeat(Step, 3, a, b)` starts with two
   slots, while `repeat(Step, 3, Pair)` starts with one slot even if `Pair`
   evaluates to multiple values.  Use explicit selections such as `Pair:0,
   Pair:1` when the intended initial state is two slots.

   DotCall lexical fallback (`Step.repeat(...)` / `Step.while(...)`) injects
   the receiver as the step argument and keeps the remaining explicit args in
   the same boundary-preserving form after structural property lookup.

   Any callable is a step (LOOP-08, Q-23, October 2026): each iteration
   invokes it as the ORDINARY call over the current state slots
   (`runNeedStepSlots`) — a clause family dispatches its clauses, a builtin
   binds them through its argument roles — so `repeat(F, 1, s)` is `F(s)` for
   every callable; a builtin's one result value is one next-state slot
   (`loopStepBuiltinRows`), and a value with no callable identity is no step.

   Step outputs define the state slots for the next iteration as a ROW SUPPLY
   (LOOP-03): each non-spread output row is one next-state slot and each spread
   row `e*` supplies its items.  The step's parameter patterns only bind the
   incoming state; they never repack its rows (Q-24, October 2026).  To keep
   one structured slot across iterations, write it as one value — a capture
   `(history*, next)` or a list `[history*, next]`; multi-output steps
   intentionally become many next-state slots.  A nested loop written as a
   step row is ONE slot like any other result (Q-26): `repeat(Inner, 2, a, b)*`
   supplies its final state's items.

   The completed loop is ONE value with emitted count `Result.valueCount`
   (`loopResultCounted`), so `Fibonacci.repeat(10, 0, 1)` is one row `(55, 89)`
   and `Fibonacci.repeat(10, 0, 1)*` two rows.

   Expr.capture semantics
   ----------------------
   No tuple constructor exists in the Lean core AST; written sequence-value
   construction is expressed via `Expr.capture` over an OutputBundle of row
   expressions.  Free identifiers inside a capture bubble up to the enclosing
   algorithm through ParameterDetector, because a capture owns no scope.

   Examples
   --------
     while(Step, 5, 0)       -- initial state has two slots
     repeat(Step, 3, 0, 0)   -- initial state has two slots
     Step.while(x, 0)        -- initial state has two slots
     Step.repeat(3, x, 0)    -- initial state has two slots
     Step.while((x, 0))      -- initial state has one sequence-value slot
     while(Step, init)        -- initial state has one slot
     repeat(Step, n, init)    -- initial state has one slot -/

/- **Collection builtin inputs** are evaluated at the builtin-dispatch
   layer, not by parser rewriting.

   Builtins such as `order`, `orderDesc`, `count`, `first`, `last`, `min`,
   `max`, `sum`, `avg`, `filter`, `map`, and `reduce` operate on one bound
   collection value's top-level items.

   - Collection builtins are ordinary fixed-arity callables: one fixed
     `collection` parameter followed by fixed control parameters such as
     `count`, `mapper`, or `predicate`. Nothing is opened before binding.
   - A plain call's first argument and a dot-call receiver both fill the
     `collection` parameter; the post-binding collection view then opens one
     outer boundary of a bound sequence or list value (any other value is a
     one-element collection).
   - Nested sequence values are never recursively flattened unless a builtin
     explicitly says so (for example `atoms`). -/

--------------------------------------------------------------------------------
-- Surface syntax support: trailing brace-block call sugar
--------------------------------------------------------------------------------

/- **Trailing brace-block call** is a parser-level desugaring that allows
   passing an inline anonymous algorithm to a call target using brace syntax
   immediately following an identifier or dotCall target.

   Triggering syntax
   -----------------
     Algo{e}              -- trailing block on resolve
     A.Apply{e}           -- trailing block on dotCall

   Desugaring
   ----------
   The parser constructs one algorithm and places it in the argument bundle:

   1. **Inline algorithm** (`inlineAlg`): the parametrized algorithm inferred
      from the brace body.  Free lowercase identifiers inside the body become
      implicit parameters via ParameterDetector, exactly as for `func`-style
      algorithms.  This is the algorithm that `{e}` denotes.

   2. **Argument bundle**: call/dotCall arguments are an OutputBundle
      (`List Expr`) of the original written argument expressions, consumed
      directly in the caller's context.  The trailing brace lowers to the
      single bundle slot `[Expr.algorithmExpr inlineAlg]` — there is no
      argument-wrapper Algorithm.

   The trailing brace is therefore equivalent to parenthesised call syntax:

     Algo{e}       ≡  Algo({e})
     A.Apply{e}    ≡  A.Apply({e})

   Lowered AST:

     Algo{e}
       =>  call (resolve "Algo") [Expr.algorithmExpr inlineAlg]

     A.Apply{e}
       =>  dotCall (resolve "A") "Apply" (some [Expr.algorithmExpr inlineAlg])

   Note: the parser does NOT place `inlineAlg` in the bundle as a bare
   Algorithm — a bundle slot is an Expr, and the brace algorithm always
   appears as an `Expr.algorithmExpr` slot. This allows per-slot argument
   resolution to see the `Expr.algorithmExpr` node and return the inner
   algorithm, which is essential for higher-order binding via AlgEnv.
   (Per-expression Algorithm resolution remains separate from value
   evaluation, and the runtime may still construct one-expression
   Algorithm adapters — `Algorithm.ofExpr`, `countedArgAlgorithm`, the
   capture value thunk — for deferred/lazy evaluation of individual
   slots; those adapters are runtime machinery, not the source AST.)

   Evaluation semantics of `Expr.algorithmExpr` in value position
   ---------------------------------------------------------------
   `Expr.algorithmExpr` represents an inline anonymous algorithm.  When
   evaluated directly (not resolved as an algorithm via resolveAlg):
   - 0-param block: auto-evaluates via evalAlgOutput (thunk semantics)
   - block with parameters: returns arityMismatch (needs explicit arguments)

   `resolveAlg(.algorithmExpr a)` always returns the algorithm (wired to
   caller scope), regardless of parameter count. `resolveAlg(.capture rows)`,
   by contrast, returns only a fresh zero-parameter output thunk over the
   bundle — capture is not algorithm identity.

   Higher-order flow
   -----------------
   When a block is passed as an argument to a user-defined call:

     Algo = func(9)
     Algo{a + 1}

   1. The parser emits `call (resolve "Algo") [Expr.algorithmExpr inlineAlg]`
      where `inlineAlg.params = ["a"]`.
   2. `evalCallExpr` resolves `Algo` and dispatches through
      `evalResolvedCall` into `evalUserCall`.
   3. `projectNeedCallable` resolves an `Expr.algorithmExpr inlineAlg` on
      that bundle slot, which returns `inlineAlg` (wired to caller scope).
   4. The callee's `func` parameter is bound in AlgEnv to `inlineAlg`.
   5. When the callee evaluates `func(9)`, the value `9` is bound to `a` and
      the output `a + 1` evaluates to `10`.

   Examples
   --------
     Algo = func(9); Algo{a + 1}          -- => 10
     Apply = func(x); Apply({a + 1}, 5)   -- => 6
     Use = func; Use{42}                  -- => 42
     Use = func; Use{a + 1}              -- => arityMismatch (block has param a)

   The last example shows that `{a + 1}` in value position (not passed to a
   caller that binds it) triggers arityMismatch because the block has an
   unbound parameter. -/

--------------------------------------------------------------------------------
-- Entry points
--------------------------------------------------------------------------------

/-- Helper to create a private property (default visibility). -/
def privateProp (name : Ident) (alg : Algorithm) : PropDef :=
  { name := name, alg := alg, isPublic := false, exposure := .exported }

/-- Helper to create a public property. -/
def publicProp (name : Ident) (alg : Algorithm) : PropDef :=
  { name := name, alg := alg, isPublic := true, exposure := .exported }

/-- Helper to create a private local-only property. -/
def privateLocalProp (name : Ident) (exposure : PropExposure) (alg : Algorithm) : PropDef :=
  { name := name, alg := alg, isPublic := false, exposure := exposure }

/-- Helper to create a public local-only property. -/
def publicLocalProp (name : Ident) (exposure : PropExposure) (alg : Algorithm) : PropDef :=
  { name := name, alg := alg, isPublic := true, exposure := exposure }

/-- Migration helper: convert assoc list to private PropDefs. -/
def propsPrivate (xs : List (Prod Ident Algorithm)) : List PropDef :=
  xs.map (fun (n, a) => privateProp n a)

/-- Prelude algorithm providing builtin operations in scope by default.
    Builtins are injected into the initial call stack by adding preludeAlg.
    All builtins are public for use in opened contexts. -/
def preludeAlg : Algorithm :=
  Algorithm.mk none [] []
    [ publicProp "if" (Algorithm.builtin .ifBuiltin)
    , publicProp "while" (Algorithm.builtin .whileBuiltin)
    , publicProp "repeat" (Algorithm.builtin .repeatBuiltin)
    , publicProp "atoms" (Algorithm.builtin .atomsBuiltin)
    , publicProp "range" (Algorithm.builtin .rangeBuiltin)
    , publicProp "filter" (Algorithm.builtin .filterBuiltin)
    , publicProp "map" (Algorithm.builtin .mapBuiltin)
    , publicProp "order" (Algorithm.builtin .orderBuiltin)
    , publicProp "orderDesc" (Algorithm.builtin .orderDescBuiltin)
    , publicProp "count" (Algorithm.builtin .countBuiltin)
    , publicProp "contains" (Algorithm.builtin .containsBuiltin)
    , publicProp "first" (Algorithm.builtin .firstBuiltin)
    , publicProp "last" (Algorithm.builtin .lastBuiltin)
    , publicProp "distinct" (Algorithm.builtin .distinctBuiltin)
    , publicProp "take" (Algorithm.builtin .takeBuiltin)
    , publicProp "skip" (Algorithm.builtin .skipBuiltin)
    , publicProp "min" (Algorithm.builtin .minBuiltin)
    , publicProp "max" (Algorithm.builtin .maxBuiltin)
    , publicProp "sum" (Algorithm.builtin .sumBuiltin)
    , publicProp "avg" (Algorithm.builtin .avgBuiltin)
    , publicProp "reduce" (Algorithm.builtin .reduceBuiltin)
    ]
    []

/- Allocate declaration identities once, before execution. Lean ASTs are
    immutable values: two different declarations can have identical bodies,
    so `reprStr` alone cannot identify them. These numbers identify written
    declarations, not activations. Host-supplied sharing identities survive.
    This pass changes no names, ownership, exposure, or executable expression. -/
mutual
  partial def identifyPropertyExpr : Expr -> StateM Nat Expr
    | .param n => pure (.param n)
    | .num n => pure (.num n)
    | .stringLiteral s => pure (.stringLiteral s)
    | .boolLiteral b => pure (.boolLiteral b)
    | .resolve n => pure (.resolve n)
    | .emptySequence n => pure (.emptySequence n)
    | .unary op e => return .unary op (<- identifyPropertyExpr e)
    | .binary op a b => return .binary op (<- identifyPropertyExpr a) (<- identifyPropertyExpr b)
    | .comparison first links =>
        return .comparison (<- identifyPropertyExpr first)
          (<- links.mapM (fun link => do
            return { link with operand := (<- identifyPropertyExpr link.operand) }))
    | .index a b => return .index (<- identifyPropertyExpr a) (<- identifyPropertyExpr b)
    | .sequenceConstruct a b => return .sequenceConstruct (<- identifyPropertyExpr a) (<- identifyPropertyExpr b)
    | .sequenceSpread e => return .sequenceSpread (<- identifyPropertyExpr e)
    | .listLiteral es => return .listLiteral (<- es.mapM identifyPropertyExpr)
    | .capture es => return .capture (<- es.mapM identifyPropertyExpr)
    | .algorithmExpr a => return .algorithmExpr (<- identifyPropertyAlgorithm a)
    | .call f args => return .call (<- identifyPropertyExpr f) (<- args.mapM identifyPropertyExpr)
    | .dotMember target name fallback args =>
        return .dotMember (<- identifyPropertyExpr target) name
          (<- identifyPropertyExpr fallback) (<- args.mapM (List.mapM identifyPropertyExpr))

  partial def identifyPropertyAlgorithm (algorithm : Algorithm) : StateM Nat Algorithm := do
    let identity <- match algorithm.declarationId with
      | some (.shared n) => pure (.shared n)
      | some (.module n) => pure (.module n)
      | _ => do
          let next <- get
          set (next + 1)
          pure (.syntax next)
    match algorithm with
    | .builtin b => pure (.builtin b)
    | .mk parent parameters opens props output _ =>
        return .mk (<- parent.mapM identifyPropertyScope) parameters
          (<- opens.mapM identifyPropertyExpr) (<- props.mapM identifyPropertyDefinition)
          (<- output.mapM identifyPropertyExpr) (some identity)
    | .conditional parent opens branches _ =>
        return .conditional (<- parent.mapM identifyPropertyScope)
          (<- opens.mapM identifyPropertyExpr)
          (<- branches.mapM fun b => return { b with body := (<- identifyPropertyAlgorithm b.body) }) (some identity)
    | .alias parent opens props target _ =>
        return .alias (<- parent.mapM identifyPropertyScope)
          (<- opens.mapM identifyPropertyExpr) (<- props.mapM identifyPropertyDefinition)
          (<- identifyPropertyExpr target) (some identity)

  partial def identifyPropertyScope : ScopeCtx -> StateM Nat ScopeCtx
    | .mk parent params opens props output branches _ id =>
        return .mk (<- parent.mapM identifyPropertyScope) params
          (<- opens.mapM identifyPropertyExpr) (<- props.mapM identifyPropertyDefinition)
          (<- output.mapM identifyPropertyExpr)
          (<- branches.mapM fun b => return { b with body := (<- identifyPropertyAlgorithm b.body) }) none id

  partial def identifyPropertyDefinition (p : PropDef) : StateM Nat PropDef := do
    let identity <- match p.identity with
      | some (.shared n) => pure (.shared n)
      | _ => do
          let next <- get
          set (next + 1)
          pure (.syntax next)
    return { p with identity := some identity, alg := (<- identifyPropertyAlgorithm p.alg) }
end

def runResultM (e : Expr) : EvalM Result := do
  let e := (identifyPropertyExpr e).run' 0
  validateExplicitParamOutputInvariantExpr e
  let ctx := { callStack := [preludeAlg], algEnv := [] }
  match e with
  | .algorithmExpr a =>
      let wired := wireToCaller ctx a
      -- The program root is demanded for its value with nothing supplied, so the
      -- ONE zero-supply rule decides: a root whose parameter list still REQUIRES
      -- a supplied argument has unresolved implicit parameters, while one that
      -- accepts an empty supply (a collecting-only host-built root) binds it
      -- through the shared demand funnel (`evalProgramOutput`).
      if Algorithm.acceptsZeroSuppliedArguments wired then
        evalProgramOutput wired ctx []
      else
        .error (Error.unresolvedImplicitParams (Algorithm.params wired))
  | _ => eval e ctx []

def runResultWithState (e : Expr) : Except Error (Result × EvalState) :=
  runResultM e |>.run EvalState.empty

def runResult (e : Expr) : Except Error Result :=
  match runResultWithState e with
  | .ok (result, _) => .ok result
  | .error err => .error err

def runFlat (e : Expr) : Except Error (List Int) := do
  pure (Result.hostAtoms (<- runResult e))

--------------------------------------------------------------------------------
-- Core sugar (surface syntax is external)
--------------------------------------------------------------------------------

open Expr

def param (s : Ident) : Expr := .param s
def num (n : Int) : Expr := .num n
def index (a i : Expr) : Expr := .index a i
def resolve (n : Ident) : Expr := .resolve n
def algorithmExpr (a : Algorithm) : Expr := .algorithmExpr a
def capture (rows : OutputBundle) : Expr := .capture rows
def call (f : Expr) (args : List Expr) : Expr := .call f args
def dotCall (o : Expr) (n : Ident) : Expr := .dotCall o n none
def sequenceConstruct (a b : Expr) : Expr := .sequenceConstruct a b
def sequenceSpread (a : Expr) : Expr := .sequenceSpread a
def listLiteral (items : List Expr) : Expr := .listLiteral items

/-- Convenience constructor for algorithms with private properties by default.
    To make properties public, use `publicProp` when building the props list. -/
def alg (ps : List Ident) (op : List Expr) (props : List PropDef) (out : List Expr) : Algorithm :=
  Algorithm.mk none (Algorithm.normalParameters ps) op props out

def algWithParameters (parameters : List CallableParameter)
    (op : List Expr) (props : List PropDef) (out : List Expr) : Algorithm :=
  Algorithm.mk none (ParameterPattern.fromParameters parameters) op props out

def algWithParameterPatterns (patterns : List ParameterPattern)
    (op : List Expr) (props : List PropDef) (out : List Expr) : Algorithm :=
  Algorithm.mk none patterns op props out

/-- Convenience constructor accepting (name, alg) pairs as private properties. -/
def algPrivate (ps : List Ident) (op : List Expr) (props : List (Prod Ident Algorithm)) (out : List Expr) : Algorithm :=
  Algorithm.mk none (Algorithm.normalParameters ps) op (propsPrivate props) out

infixl:65 " + " => fun a b => Expr.binary BinaryOp.add a b
infixl:65 " - " => fun a b => Expr.binary BinaryOp.sub a b
infixl:70 " * " => fun a b => Expr.binary BinaryOp.mul a b
infixl:70 " / " => fun a b => Expr.binary BinaryOp.div a b
infixr:75 " ^ " => fun a b => Expr.binary BinaryOp.pow a b

--------------------------------------------------------------------------------
-- load elaboration (compile-time module loading)
--------------------------------------------------------------------------------

/-- Elaboration errors for load directives (distinct from runtime EvalM errors).
    These are reported during the elaboration pass, before evaluation. -/
inductive LoadError where
  | domainNotAllowed : String -> LoadError           -- host not in allowlist
  | invalidUrl       : String -> LoadError           -- malformed URL
  | notHttps         : String -> LoadError           -- non-HTTPS scheme
  | urlNotLiteral    : LoadError                     -- non-constant URL expression
  | runtimePosition  : LoadError                     -- load in non-allowed position
  | cycleDetected    : List String -> LoadError      -- URL cycle stack
  | fetchFailed      : String -> String -> LoadError -- url, reason
  | sizeLimitExceeded : String -> Nat -> LoadError   -- url, size
  | parseError       : String -> LoadError           -- url with parse errors
  deriving Repr

/-- Context for the load elaboration pass. Tracks:
    - allowedHosts: set of permitted domain names
    - cache: previously loaded URLs → their elaborated algorithms
    - inProgress: URLs currently being loaded (for cycle detection)
    - fetch: abstract code fetcher URL → source text -/
structure LoadCtx where
  allowedHosts : List String
  cache        : Assoc String Algorithm
  inProgress   : List String
  fetch        : String -> Option String   -- abstract host acquisition; C# awaits DownloadCode before this model

/-- Positions where load is allowed (compile-time only).
    load is a directive, not a runtime expression. -/
inductive LoadPosition where
  | propertyDef : LoadPosition   -- RHS of Name = load('url')
  | openList    : LoadPosition   -- inside open load('url') or open target1, target2
  deriving Repr, BEq

/- **load elaboration judgment**

  The elaboration pass transforms surface `Call(Resolve("load"), ...)` nodes into
  `Expr.algorithmExpr (parseModule (fetch url))` nodes.  `load` is NOT a core Expr
  constructor — it exists only as surface syntax represented via
  `call (resolve "load") (alg with output = [stringLiteral url])`.
  The elaborator extracts the URL from the stringLiteral argument and enforces:

  2. **Allowed position**: load may only appear in:
     - Property definition RHS: `Lib = load('https://katlang.org/lib.kat')`
     - Open declarations: `open load('https://katlang.org/lib.kat')`
     load in runtime positions (binary expressions, call arguments, if/while
     branches, etc.) is rejected.

  3. **Domain allowlist**: The URL's host must be in `LoadCtx.allowedHosts`
     (default: ["katlang.org"]). Subdomains are permitted.

  4. **HTTPS only**: Only `https://` URLs are accepted.

  5. **Cycle detection**: If URL is in `LoadCtx.inProgress`, elaboration fails
     with `cycleDetected`.

  6. **Caching**: If URL is in `LoadCtx.cache`, the cached algorithm is reused.
     Same URL → same content → same AST (determinism within a run).

  7. **Size limit**: Fetched source must not exceed a reasonable limit.

  **Post-condition (invariant)**: After elaboration completes successfully,
  the resulting AST satisfies `postElabInvariant` / `postElabInvariantAlg`,
  which guarantees:
    1. Runtime `Expr.stringLiteral` nodes may remain as ordinary first-class values.
    2. No unresolved load calls remain (i.e., no `call (resolve "load") _` nodes).
  All load directives have been replaced with `Expr.algorithmExpr` containing the
  parsed and elaborated remote algorithm. The evaluator never sees unresolved
  load calls.

  Formally:
    elaborate(call(resolve("load"), [stringLiteral url])) = block(parseModule(fetch(url)))
    ∀ e ∈ elaborated AST, e ≠ Expr.call (Expr.resolve "load") _
-/
mutual
/-- Post-elaboration invariant: returns true iff the expression tree contains
    no unresolved load calls (`call (resolve "load") _`) and every dot edge
    satisfies the elaborated dot-edge contract. Runtime `Expr.stringLiteral`
    nodes are allowed as ordinary first-class values.
    An AST satisfying this predicate is ready for semantic evaluation. -/
partial def postElabInvariant : Expr -> Bool
  | .stringLiteral _ => true
  | .boolLiteral _   => true
  | .unary _ e       => postElabInvariant e
  | .binary _ a b    => postElabInvariant a && postElabInvariant b
  | .comparison first links => postElabInvariant first && links.all (fun link => postElabInvariant link.operand)
  | .index a b       => postElabInvariant a && postElabInvariant b
  | .sequenceConstruct a b  => postElabInvariant a && postElabInvariant b
  | .sequenceSpread a       => postElabInvariant a
  | .listLiteral items      => items.all postElabInvariant
  | .call (.resolve "load") _ => false  -- unresolved load call
  | .call f args     => postElabInvariant f && args.all postElabInvariant
  -- Elaborated dot-edge contract (C#: DotCallElaborationInvariant): the
  -- stored lexical fallback is exactly `.resolve` or `.param` and its
  -- identifier equals the structural member name — the two identities name
  -- the same written member. Any other fallback expression is not a valid
  -- elaborated dot edge. Lean's representation has no nullable
  -- host-compatibility state: `Expr.dotCall` (the ordinary/lexical smart
  -- constructor) already builds a coherent edge, so this arm rejects only
  -- hand-built incoherence.
  | .dotMember a n fallback args =>
      (match fallback with
       | .resolve fn => fn == n
       | .param fn   => fn == n
       | _           => false) &&
      postElabInvariant a &&
      match args with
      | some slots => slots.all postElabInvariant
      | none => true
  | .algorithmExpr alg => postElabInvariantAlg alg
  | .capture rows    => rows.all postElabInvariant
  | _                => true  -- param, num, resolve

/-- Algorithm-level post-elaboration invariant: all contained expressions
  satisfy `postElabInvariant`. -/
partial def postElabInvariantAlg : Algorithm -> Bool
  | .builtin _ => true
  | .mk _ _ opens props output _ =>
      opens.all postElabInvariant &&
      props.all (fun p => postElabInvariantAlg p.alg) &&
      output.all postElabInvariant
  | .conditional _ opens branches _ =>
      opens.all postElabInvariant &&
      branches.all (fun b => postElabInvariantAlg b.body)
  | .alias _ opens props target _ =>
      opens.all postElabInvariant &&
      props.all (fun p => postElabInvariantAlg p.alg) &&
      postElabInvariant target
end

end KatLang
