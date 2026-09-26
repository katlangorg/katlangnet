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
--   (`7 / 2 = 3` and `avg(1, 2) = 1`) but yield decimals in the runtime
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
--       recursive parameter pattern made only of captures and structural sequence-value patterns
--       (for example `Apply(f) = f(4)`, `PairSum((x, y)) = x + y`, or
--       `CountSequenceValue((*values)) = values.count`)
--     - multi-clause families and clause heads that require literal or
--       whole-argument conditional matching elaborate to `Algorithm.conditional`
--
--   This split is intentional: ordinary elaboration preserves dual-view call
--   binding for higher-order arguments, while true conditional algorithms keep
--   their full-input-specification and whole-argument matching semantics.
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

inductive ParameterPattern where
  | capture : CallableParameter -> ParameterPattern
  | sequenceValue : List ParameterPattern -> ParameterPattern
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

  def fromParameters (parameters : List CallableParameter) : List ParameterPattern :=
    parameters.map .capture

  def normalPatterns (ps : List Ident) : List ParameterPattern :=
    ps.map (fun p => .capture { name := p })

  def hasStructured (patterns : List ParameterPattern) : Bool :=
    patterns.any (fun
      | .sequenceValue _ => true
      | _ => false)

  /-- True when the pattern list itself contains a collecting binding (nested
      captures inside sequence-value patterns do not count).
      C#: `ParameterPattern.HasCollectingCaptureAtCurrentLevel`. -/
  def hasCollectingCaptureAtCurrentLevel (patterns : List ParameterPattern) : Bool :=
    patterns.any (fun
      | .capture parameter => parameter.kind == ParameterKind.collecting
      | _ => false)

  /-- The MINIMUM number of supplied argument slots a parameter-pattern list
      accepts — the ONE rule `bindParameterPatternList` (and its counted twin)
      enforces, factored out so no other layer can re-derive it:

      * every pattern consumes exactly ONE supplied slot, whatever it contains —
        a sequence-value group is one slot that the binder opens afterwards, so
        nested structure never changes the count at this level;
      * a collecting capture at THIS level consumes NONE: it collects whatever
        slots are left over after the fixed prefix and suffix bind, and an empty
        leftover is the exact empty list (`collectSegment [] = []`).

      So `Only(*xs)` accepts zero supplied slots, while `Head(x, *rest)`,
      `Tail(*rest, z)`, `P((x, *rest))` and `Pair(x, y)` each require at least
      one. A list with two collecting captures is a rejected signature, never a
      lower minimum. C#: `ParameterPattern.MinimumSuppliedSlots`. -/
  def minimumSuppliedSlots (patterns : List ParameterPattern) : Nat :=
    if hasCollectingCaptureAtCurrentLevel patterns then patterns.length - 1 else patterns.length

  def hasRepeatedCaptureNames (patterns : List ParameterPattern) : Bool :=
    let names := (patterns.flatMap captures).map (fun parameter => parameter.name)
    names.length != names.eraseDups.length

  partial def containsCaptureName (name : Ident) : ParameterPattern -> Bool
    | .capture parameter => parameter.name = name
    | .sequenceValue items => items.any (containsCaptureName name)

  mutual
    /-- Whether a pattern binds `name` at any depth — the STATIC fact the
        pattern-list binders read to tell whether every contribution of a
        repeated name at one level is already known (see
        `settlePatternRange`). A total twin of `containsCaptureName`, so the
        binder bridge laws can unfold it. C#: `ParameterPatternBindsName`. -/
    def bindsName (name : Ident) : ParameterPattern -> Bool
      | .capture parameter => parameter.name == name
      | .sequenceValue items => anyBindsName name items

    /-- Whether any pattern of a list binds `name` at any depth. -/
    def anyBindsName (name : Ident) : List ParameterPattern -> Bool
      | [] => false
      | pattern :: rest => bindsName name pattern || anyBindsName name rest
  end

  def topLevelCaptureKind? (name : Ident) : List ParameterPattern -> Option ParameterKind
    | [] => none
    | .capture parameter :: rest =>
        if parameter.name = name then some parameter.kind else topLevelCaptureKind? name rest
    | .sequenceValue _ :: rest => topLevelCaptureKind? name rest
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
  | notAnAlgorithm   : String -> Error
  | illegalInOpen    : String -> Error                -- semantic restriction (e.g., builtin not allowed)
  | badOpenForm      : String -> Error                -- syntactic form not allowed in open
  | illegalInEval    : String -> Error                -- not evaluable to a value
  | ambiguousOpen    : Ident -> List String -> Error   -- name, providers
  | arityMismatch    : Nat -> Nat -> Error     -- expected, actual
  | badArity         : Error                   -- shape / unpacking failure
  | typeMismatch     : String -> Error          -- type error (e.g. string where number expected)
  | badIndex         : Error
  | divByZero        : Error                   -- division or modulo by zero
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

/-- Variable-middle collecting-parameter binding (mirrors C# `BindCallableArguments`). The fixed
    prefix binds from the front, the fixed suffix from the back, and the collecting
    captures the remaining middle items (zero or more). The minimum is the FIXED
    (non-collecting) parameter count: like every other collecting binding, the collecting parameter may
    collect ZERO items (an empty collected segment is the exact list `[]`) — the same rule the
    shared pattern binder applies (`bindParameterPatternList`: required =
    patterns - 1).
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

inductive SequenceBuiltinEmptyPolicy where
  | allowEmpty
  | requireAnyItem
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
      emptyPolicy := .requireAnyItem
    }
  | .lastBuiltin => some {
      emptyPolicy := .requireAnyItem
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
      suffixArgs := [
        { name := "reducer" },
        { name := "initial" }
      ]
    }
  | _ => none

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

def builtinArityError (b : Builtin) (actual : Nat) : Error :=
  -- The numeric payload mirrors the C# `WrongBuiltinArity`: `if` is the one
  -- builtin whose expected count is populated (it requires exactly 3
  -- arguments); every other builtin still carries the placeholder 0 beside
  -- the descriptive `builtinArityDesc` context.
  let expected : Nat :=
    match b with
    | .ifBuiltin => 3
    | _ => 0
  Error.withContext s!"expected {builtinArityDesc b} arguments" (Error.arityMismatch expected actual)

--------------------------------------------------------------------------------
-- Patterns (for clause heads and conditional algorithms)
--------------------------------------------------------------------------------

/-- Pattern language for clause heads and conditional algorithm branch matching.
    Recursive capture/sequence-value patterns can elaborate to ordinary explicit
    parameter patterns. Conditional patterns match against Result values at
    call time.
    - `bind x`: matches any Result and binds it to name `x`
    - `litInt n`: matches only `Result.atom n`
    - `litBool b`: matches only `Result.bool b` (the reserved literals `true` /
      `false` in a clause head; a Boolean is never a number, so `F(1)` and
      `F(true)` are different clauses)
    - `sequenceValue ps`: matches `Result.sequenceValue rs` with same arity, each sub-pattern
      matching; a singleton sequence-value pattern also matches a non-sequence-value
      result because normalization collapses singleton sequence values
      (see `patternSequenceValueMembers?`)

    Patterns are a separate semantic type, distinct from Expr.
    They do not appear in executable expression positions.

    **Full-input-specification rule**: In a conditional algorithm, the branch
    pattern in `Name(...)` is the COMPLETE INPUT SPECIFICATION of that branch.
    - All branch inputs must appear in the pattern.
    - Branch bodies do NOT infer additional implicit parameters from free
      identifiers.  Only names bound by the pattern (plus ordinary lexical /
      property / open / builtin resolution) are available in the body.
    - Unused pattern-bound names are allowed.
    - Grace `~` is NOT permitted in patterns or branch bodies.  Patterns
      contain only matching constructs (binders, integer literals, nested
      sequence-value patterns).  Branch bodies must not use Grace because conditional branches
      have no implicit parameter inference or reordering to apply it to.

    This keeps conditional algorithms self-contained: branch selection and
    branch binding are the same operation, with no hidden remaining parameters
    and no interaction with Grace-based parameter reordering. -/
inductive Pattern where
  | bind      : Ident -> Pattern
  | litInt    : Int -> Pattern
  | litString : String -> Pattern    -- matches only Result.str s (exact string equality)
  | litBool   : Bool -> Pattern      -- matches only Result.bool b (C#: Pattern.LitBool)
  | sequenceValue     : List Pattern -> Pattern
  deriving Repr, BEq

namespace Pattern
  /-- Collect all binder names in a pattern (left-to-right). -/
  def boundNames : Pattern -> List Ident
    | .bind x      => [x]
    | .litInt _    => []
    | .litString _ => []
    | .litBool _   => []
    | .sequenceValue ps    => ps.flatMap boundNames

  /-- Compute the top-level arity of a pattern.
      - `sequenceValue [p1, ..., pn] ⟹ n`
      - any non-sequence-value pattern  ⟹ 1

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
      recursive binder/sequence-value parameter patterns.

      This is only an eligibility helper for the whole same-name clause-group
      elaboration rule; it does not by itself decide ordinary-vs-conditional.

      Rejected on purpose:
      - literal or mixed non-binder pattern structure

      This is the ordinary clause-elaboration boundary: capture/sequence-value-only
      recursive parameter patterns elaborate as ordinary algorithms, while
      literal or mixed patterns stay conditional. -/
  partial def parameterPattern? : Pattern -> Option ParameterPattern
    | .bind x => some (.capture { name := x })
    | .sequenceValue ps => do
        let patterns <- ps.mapM parameterPattern?
        some (.sequenceValue patterns)
    | _ => none

  partial def plainClauseParameterPatterns? : Pattern -> Option (List ParameterPattern)
    | .bind x => some [.capture { name := x }]
    | .sequenceValue ps => ps.mapM parameterPattern?
    | _ => none

  def plainClauseParamNames? : Pattern -> Option (List Ident)
    | p => (plainClauseParameterPatterns? p).map (fun patterns => (patterns.flatMap ParameterPattern.captures).map (fun parameter => parameter.name))

  /-- Check whether two patterns are match-equivalent. Binder spelling is
      irrelevant, but repeated-name equality positions must agree:
      - `bind _` ≡ `bind _` (any binder matches everything)
      - `litInt m` ≡ `litInt n` iff `m = n` (likewise `litString`, `litBool`)
      - `sequenceValue ps` ≡ `sequenceValue qs` iff same length and pairwise match-equivalent

      Used to detect duplicate branch patterns in conditional algorithms.

      Equivalence is structural, not extensional: because matching adapts
      singleton sequence-value patterns to non-sequence-value values (`patternSequenceValueMembers?`),
      `sequenceValue [bind _]` accepts the same runtime inputs as `bind _`, yet the
      two are not considered equivalent here.  Duplicate detection therefore
      flags only structurally identical match behavior. -/
  def binderRenaming? (name : Ident) : List (Ident × Ident) -> Option Ident
    | [] => none
    | (left, right) :: rest =>
        if left = name then some right else binderRenaming? name rest

  def binderTargetUsed (name : Ident) : List (Ident × Ident) -> Bool
    | [] => false
    | (_, right) :: rest => right = name || binderTargetUsed name rest

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
    | _, _, _ => none

  def isMatchEquivalent (left right : Pattern) : Bool :=
    (matchEquivalentWithRenaming left right []).isSome
end Pattern

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

/-- Declaration identity is independent of executable body equality. Ordinary
    tree declarations receive a fresh `syntax` identity once at run preparation.
    `shared` represents a host AST declaration reused at several syntax sites
    (C# binding plus declaring-scope identity); encoders preserve that sharing explicitly. -/
inductive PropertyIdentity where
  | syntax : Nat -> PropertyIdentity
  | shared : Nat -> PropertyIdentity
  | runtime : Nat -> PropertyIdentity
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
      from free identifiers in the body.  Grace `~` is not allowed in patterns
      or branch bodies.
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
        At call time, arguments are evaluated and matched against branch patterns
        in source order.  The first matching branch body is evaluated.
        If no branch matches, evaluation fails with noMatchingBranch.

        **Full-input-specification invariant**: each branch pattern `Name(...)`
        declares the complete input interface of that branch.  Branch bodies do
        NOT infer additional implicit parameters from free identifiers — only
        names bound by the pattern and names resolvable through ordinary lexical /
        property / open / builtin lookup are available.  Grace `~` is forbidden
        in both patterns and branch bodies.

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
        and that sole head is a recursive capture/sequence-value parameter pattern such
        as `Apply(f) = f(4)`, `PairSum((x, y)) = x + y`, or
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
  - that sole clause head is a recursive capture/sequence-value parameter pattern

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
      explicit openers are the spread marker (`spreadItems`), explicit
      sequence-value patterns and deconstruction (`structureItems?`), the
      indexing `:` TARGET position view (`projectionItems` — the target's
      positions, never the selected element), and the post-binding builtin
      collection view (`builtinCollectionItems`, applied to the bound
      `collection` argument); each opens a sequence and a list alike. -/
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

  /-- Deconstruction-openable structure view shared by the sequence-value
      parameter pattern binders: a received sequence value or exact list value
      opens to its immediate items; atoms, strings, and Booleans are not
      openable (`sequenceValuePatternItems` adds the ONE scalar one-item
      fallback both binders share). Call-argument binding never uses this
      view — every non-spread argument stays one argument, a sequence or a
      list alike; only an explicit pattern or spread opens it.
      C#: `Result.StructureItems`. -/
  def structureItems? : Result -> Option (List Result)
    | sequenceValue rs => some rs
    | listValue rs => some rs
    | _ => none

  /-- NESTED-PATTERN OPENING (September 2026, S3): the items a sequence-value
      parameter pattern binds against, given the ONE value its slot supplies.
      This is the ONE rule shared by the ordinary binder (`bindParameterPattern`)
      and the counted callback binder (`bindCountedParameterPattern`), so a
      callback that supplies one value `V` to a pattern `P` binds exactly as
      the ordinary call `P(V)` does — callback provenance changes nothing.
      A sequence value or exact list value opens to its immediate items
      (`structureItems?`, ONE boundary of either kind); any other value — a
      number, a string, a Boolean — is a ONE-item supply (the scalar one-item
      fallback), at every pattern level and for every group size: `(x)`,
      `(x, *rest)`, `(*xs)`, and `(*init, z)` bind it, while `(x, y)` and
      `(x, *r, z)` reject it through the nested group's ordinary arity check
      (one value supplied). The fallback supplies one value, never zero, and
      it never opens anything further. C#: `Evaluator.SequenceValuePatternItems`. -/
  def sequenceValuePatternItems (value : Result) : List Result :=
    (structureItems? value).getD [value]

  /-- Count emitted top-level values when a result is already in hand.
      Empty results emit 0. Any non-empty atomic, string, or sequence value
      counts as one value. List values ALWAYS count as one visible value,
      including the empty list `[]` — only the empty SEQUENCE value `()` is
      the invisible-able empty result.

      This is used by `reduce` and `map`, where sequence-value accumulator / mapped
      values are valid as long as the step / transform returns exactly one
      top-level value. -/
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

/-- Algorithm environment: maps parameter names to algorithms.
    Used for higher-order algorithm parameters — when a caller passes an
    algorithm as an argument, the callee can invoke it by name.
    Parallel to ValEnv (which maps names to Results). -/
abbrev AlgEnv := Assoc Ident Algorithm

namespace AlgEnv
  def lookup (env : AlgEnv) (x : Ident) : Option Algorithm :=
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
    semantic LAW (C#: `ZeroArgPropertyCacheKey`). The scope of a stored value
    follows the binding's exposure classification:

    * an EXPORTED binding is self-contained — its value depends on no input that
      an enclosing owner's call binds — so the binding context at the access is
      not a determinant of the value: ONE entry per run per declaring scope
      serves every property-style access, from any call, callback, loop
      iteration, or explicit outer call. Its environment components are `none`.
    * a LOCAL-ONLY binding reads an input an enclosing owner's call binds
      through the dynamically threaded environments, so its value is a
      function of the binding context: the key carries the three environments
      at the access (`some`) plus a fresh binding-context identity, and two
      activations never share an entry, even if all their values are equal.

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

/-- The three binding channels saved by one lexical owner activation. -/
structure ParameterActivation where
  values : ValEnv
  algorithms : AlgEnv
  counted : CountedParamEnv
  deriving Repr

/-- Per-run evaluator state. The zero-parameter property cache is part of the
    Lean semantics because property-style `A` and explicit `A()` now have
    distinct observable call shapes. The state is created fresh for each
    top-level `runResult`; it is not general memoization and does not cache
    arbitrary calls or expression results. -/
structure EvalState where
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

/-- Evaluation context threaded through resolution and evaluation.
    Wraps the algorithm chain (current algorithm + enclosing callers) used for
    both lexical resolution and runtime dispatch.
  algEnv carries algorithm-typed parameter bindings for higher-order dispatch.

  The evaluator state carries the per-run zero-parameter property cache. This
  cache is core KatLang semantics because `A` and `A()` are distinct: property-
  style `A` may read/write the cache, while explicit zero-parameter calls
  bypass only the directly called property's cache entry. The cache is scoped
  to one top-level `runResult`; it is not general memoization and does not
  apply to arbitrary calls. -/
structure EvalCtx where
  callStack : List Algorithm
  algEnv    : AlgEnv := []
  countedParamEnv : CountedParamEnv := []
  bindingContext : Nat := 0
  headScope : Option ScopeCtx := none
  deriving Repr

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
      bound parameter names removed from BOTH inherited tiers (`AlgEnv.shadow`,
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
      algEnv := algBindings ++ AlgEnv.shadow ctx.algEnv names,
      countedParamEnv := countedBindings ++ CountedParamEnv.shadow ctx.countedParamEnv names }
end EvalCtx

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

namespace Algorithm
  def normalCallableParameters (ps : List Ident) : List CallableParameter :=
    ps.map (fun p => { name := p })

  def normalParameters (ps : List Ident) : List ParameterPattern :=
    ParameterPattern.normalPatterns ps

  def parent : Algorithm -> Option ScopeCtx
    | .mk p _ _ _ _ _ => p
    | .builtin _ => none
    | .conditional p _ _ _ => p
  def parameterPatterns : Algorithm -> List ParameterPattern
    | .mk _ parameterPatterns _ _ _ _ => parameterPatterns
    | .builtin _ => []
    | .conditional _ _ _ _ => []

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
  def props : Algorithm -> List PropDef
    | .mk _ _ _ pr _ _ => pr
    | .builtin _ => []
    | .conditional _ _ _ _ => []
  /-- The algorithm's output as an `OutputBundle` — ordered original written
      expression rows. The algorithm is the scope-owning DEFINITION of this
      bundle; the bundle itself owns no scope. -/
  def output : Algorithm -> OutputBundle
    | .mk _ _ _ _ out _ => out
    | .builtin _ => []
    | .conditional _ _ _ _ => []

  /-- Access branches for conditional algorithms. Returns [] for other forms. -/
  def branches : Algorithm -> List CondBranch
    | .conditional _ _ bs _ => bs
    | _ => []

  def declarationId : Algorithm -> Option PropertyIdentity
    | .mk _ _ _ _ _ id => id
    | .conditional _ _ _ id => id
    | .builtin _ => none

  def withDeclarationId (id : Option PropertyIdentity) : Algorithm -> Algorithm
    | .mk p ps op pr out _ => .mk p ps op pr out id
    | .conditional p op bs _ => .conditional p op bs id
    | .builtin b => .builtin b

  def withParent (p : Option ScopeCtx) : Algorithm -> Algorithm
    | .mk _ parameterPatterns op pr out id => .mk p parameterPatterns op pr out id
    | .builtin b => .builtin b
    | .conditional _ op bs id => .conditional p op bs id

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

  def withParameterPatterns (patterns : List ParameterPattern) : Algorithm -> Algorithm
    | .mk p _ op pr out id => .mk p patterns op pr out id
    | .builtin b => .builtin b
    | .conditional p op bs id => .conditional p op bs id

  def hasStructuredParameterPattern (a : Algorithm) : Bool :=
    ParameterPattern.hasStructured (parameterPatterns a)

  def hasRepeatedParameterNames (a : Algorithm) : Bool :=
    ParameterPattern.hasRepeatedCaptureNames (parameterPatterns a)

  def requiresPatternBinding (a : Algorithm) : Bool :=
    hasStructuredParameterPattern a || hasRepeatedParameterNames a

  def topLevelParameterKind? (a : Algorithm) (name : Ident) : Option ParameterKind :=
    ParameterPattern.topLevelCaptureKind? name (parameterPatterns a)

  def declaresParameterName (a : Algorithm) (name : Ident) : Bool :=
    (parameterPatterns a).any (ParameterPattern.containsCaptureName name)

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
      clause and that sole head is a recursive capture/sequence-value parameter pattern.
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
      it has exactly one clause and that sole head is a recursive capture/sequence-value
      parameter pattern; otherwise the whole family elaborates as
      `Algorithm.conditional`.

      This preserves higher-order ordinary call semantics for single-clause
      families such as `Apply(f) = f(4)` and
      `Choose(x, predicate) = if(predicate(x), x, 0)`, and preserves sequence-value
      ordinary parameter shapes such as `PairSum((x, y)) = x + y`, while keeping
      multi-clause and literal/mixed families conditional.

      Opens handling (descriptive, relied on by the front-end): the
      conditional's own opens list is taken from the FIRST branch's body, and
      every branch body also keeps its own opens.  Surface clause bodies are
      expressions, so in practice all clause bodies of a family carry the same
      (usually empty) opens; the front-end does not produce families whose
      branch bodies declare differing opens. -/
  def elaborateClauseGroup : List CondBranch -> Algorithm
    | [branch] =>
        match clauseGroupDefinitionKind [branch] with
        | .ordinary patterns => branch.body.withParameterPatterns patterns
        | .conditional =>
            .conditional (parent branch.body) (opens branch.body) [{
              pattern := branch.pattern
              body := branch.body.withParams []
            }]
    | branches =>
        .conditional
          (branches.head?.map (fun branch => parent branch.body) |>.join)
          (branches.head?.map (fun branch => opens branch.body) |>.getD [])
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
    | .mk _ _ _ ps _ _ =>
        let names := ps.map (·.name)
        let rec go : List Ident -> List Ident -> Option Ident
          | [],        _    => none
          | n :: rest, seen =>
              if seen.elem n then some n
              else go rest (n :: seen)
        go names []
    | _ => none

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

mutual
  /-- Pre-evaluation structural validation over a whole algorithm tree:
      - explicit algorithm parameters only appear on algorithms that define
        output (`explicitParamsRequireOutput`)
      - conditional algorithms have uniform top-level branch pattern arity and
        uniform top-level branch output arity (`branchArityMismatch`,
        `branchOutputArityMismatch`)

      `name` labels conditional arity diagnostics with the nearest enclosing
      property name; anonymous algorithms report the placeholder
      `conditional`. -/
  partial def validateExplicitParamOutputInvariant (a : Algorithm)
      (name : Ident := "conditional") : EvalM Unit := do
    match a with
    | .mk _ parameters op pr out _ =>
        if !parameters.isEmpty && out.isEmpty then
          .error Error.explicitParamsRequireOutput
        for openExpr in op do
          validateExplicitParamOutputInvariantExpr openExpr
        for prop in pr do
          validateExplicitParamOutputInvariant prop.alg prop.name
        for expr in out do
          validateExplicitParamOutputInvariantExpr expr
    | .builtin _ => pure ()
    | .conditional _ op branches _ =>
        validateConditionalBranchArities name a
        for openExpr in op do
          validateExplicitParamOutputInvariantExpr openExpr
        for branch in branches do
          validateExplicitParamOutputInvariant branch.body name

  /-- Traverse expressions so nested block literals and call-argument
      algorithms also satisfy the same pre-evaluation invariants. -/
  partial def validateExplicitParamOutputInvariantExpr : Expr -> EvalM Unit
    | .param _ => pure ()
    | .num _ => pure ()
    | .stringLiteral _ => pure ()
    | .boolLiteral _ => pure ()
    | .resolve _ => pure ()
    | .unary _ operand =>
        validateExplicitParamOutputInvariantExpr operand
    | .binary _ left right => do
        validateExplicitParamOutputInvariantExpr left
        validateExplicitParamOutputInvariantExpr right
    | .comparison first links => do
        validateExplicitParamOutputInvariantExpr first
        links.forM (fun link => validateExplicitParamOutputInvariantExpr link.operand)
    | .index target selector => do
        validateExplicitParamOutputInvariantExpr target
        validateExplicitParamOutputInvariantExpr selector
    | .sequenceConstruct left right => do
      validateExplicitParamOutputInvariantExpr left
      validateExplicitParamOutputInvariantExpr right
    | .emptySequence _ => pure ()
    | .sequenceSpread operand => do
        validateExplicitParamOutputInvariantExpr operand
    | .listLiteral items =>
        items.forM validateExplicitParamOutputInvariantExpr
    | .algorithmExpr alg =>
        validateExplicitParamOutputInvariant alg
    | .capture rows =>
        rows.forM validateExplicitParamOutputInvariantExpr
    | .call fn args => do
        validateExplicitParamOutputInvariantExpr fn
        args.forM validateExplicitParamOutputInvariantExpr
    | .dotMember target _ fallback args? => do
        validateExplicitParamOutputInvariantExpr target
        -- The stored lexical fallback is a real child (Resolve/Param for
        -- front-end trees, but hand-built trees could hide algorithms in it),
        -- so the validation walk covers it like every other reference.
        validateExplicitParamOutputInvariantExpr fallback
        match args? with
        | some args => args.forM validateExplicitParamOutputInvariantExpr
        | none => pure ()
end

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
      (explicit or inferred parameters) or a clause family (whose branches always take
      arguments). Such an algorithm is not an `open` provider — `open` imports a namespace
      and never creates an activation, so there is no value its members could read their
      inputs from (C#: `Evaluator.RequiresArguments`). -/
  def requiresArguments : Algorithm -> Bool
    | .conditional _ _ _ _ => true
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
    algorithms := ctx.algEnv.filter (fun b => names.contains b.fst)
    counted := ctx.countedParamEnv.filter (fun b => names.contains b.fst) }
  set { state with
    lexicalActivations := state.lexicalActivations.push activation }
  pure id

def enterAlgorithmBody (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM EvalCtx := do
  if a.params.isEmpty then pure (ctx.push a)
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
      let parameterCtx := { ctx with algEnv := activation.algorithms, countedParamEnv := activation.counted }
      pure (parameterCtx, activation.values)

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

/-- Coerce a Result to Int, or raise typeMismatch for strings, badArity otherwise. -/
def expectInt (r : Result) : EvalM Int :=
  match r with
  | .str _ => .error (Error.typeMismatch "Expected a number, got a string")
  | .bool _ => .error (Error.typeMismatch "Expected a number, got a Boolean value")
  | _ => match Result.asInt? r with
    | some n => pure n
    | none   => .error Error.badArity

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

structure CountedParameterPatternBindings where
  countedParamEnv : CountedParamEnv := []
  deriving Repr

/-- Flat fixed binding preserves each supplied value. Check the complete supply
    before zipping, so an arity error reports the original lengths, not the
    unmatched recursive tails. This agrees with the pattern/callback binders
    and C# `BindParams`: two parameters and one pair value is `(2, 1)`. -/
def bindParams (ps : List Ident) (vs : List Result) : EvalM ValEnv :=
  if ps.length != vs.length then
    .error (Error.arityMismatch ps.length vs.length)
  else
    pure (ps.zip vs)

/-- Bind algorithm-typed parameters: zip parameter names with algorithms.
    Only includes entries where the argument resolved to an algorithm.
    Result entries are skipped (they go through bindParams / ValEnv). -/
def bindAlgParams (ps : List Ident) (algs : List (Option Algorithm)) : AlgEnv :=
  match ps, algs with
  | [], _ => []
  | _, [] => []
  | p::ps', a::as' =>
    match a with
    | some alg => (p, alg) :: bindAlgParams ps' as'
    | none     => bindAlgParams ps' as'

structure FlatFixedCallSlot where
  value? : Option Result := none
  algorithm? : Option Algorithm := none
  error? : Option Error := none
  deriving Repr

structure CallableCallItem where
  value? : Option Result := none
  algorithm? : Option Algorithm := none
  error? : Option Error := none
  skipMissingValue : Bool := false
  source? : Option Expr := none
  /-- The parameter's ALGORITHM-channel binding, carried beside the value-side
      `algorithm?` (`ResolvedArgumentAlgorithm.callable?`). -/
  callable? : Option Algorithm := none
  deriving Repr

/-- One supplied item prepared for parameter binding: its value view
    (`value?`), its algorithm view where resolvable, and a retained value
    error. VALUES STAY VALUES (September 2026): every item is exactly ONE
    argument whatever supplied it — a non-spread written argument (whatever its
    value: scalar, sequence, list, `()`, `[]`), an explicit spread item, an
    extension dot-call receiver (`R.F(args)` assembles exactly the items of
    `F(R, args)`), a pattern-opened item, or a loop-state slot. No item
    records how it was written, because no binder reinterprets one item as
    several: only explicit spread and explicit structural patterns open a
    value. C#: `ParameterPatternInput`. -/
structure ParameterPatternInput where
  value? : Option Result := none
  algorithm? : Option Algorithm := none
  error? : Option Error := none
  deriving Repr

structure ParameterPatternBindings where
  argEnv : ValEnv := []
  countedParamEnv : CountedParamEnv := []
  algEnv : AlgEnv := []
  deriving Repr

/-- Whether one pattern's bindings bind `name` on any channel. -/
def ParameterPatternBindings.binds (bindings : ParameterPatternBindings) (name : Ident) : Bool :=
  (lookupAssoc name bindings.argEnv).isSome || (lookupAssoc name bindings.countedParamEnv).isSome
    || (lookupAssoc name bindings.algEnv).isSome

/-- The names one pattern's bindings bind, each once. -/
def ParameterPatternBindings.names (bindings : ParameterPatternBindings) : List Ident :=
  (bindings.argEnv.map Prod.fst ++ bindings.countedParamEnv.map Prod.fst
    ++ bindings.algEnv.map Prod.fst).eraseDups

/-- Append the entries of `incoming` whose name `acc` does not bind yet: the
    first binding of a name is the one that stays. -/
def appendFirstOccurrences {A} (acc incoming : Assoc Ident A) : Assoc Ident A :=
  incoming.foldl (fun merged entry =>
    if (lookupAssoc entry.1 merged).isSome then merged else merged ++ [entry]) acc

/-- The merged bindings of one pattern level: each name keeps its FIRST binding
    on each channel. Every repeated name has passed `repeatedNameFailure`
    before this runs, so discarded entries agree on the complete value/counted
    channels and callable identity. This storage choice gives no callable
    positional precedence (`repeated_name_complete_binding_is_permutation_invariant`). -/
def mergeFirstOccurrences (contributions : List ParameterPatternBindings) : ParameterPatternBindings :=
  contributions.foldl (fun merged contribution => {
    argEnv := appendFirstOccurrences merged.argEnv contribution.argEnv,
    countedParamEnv := appendFirstOccurrences merged.countedParamEnv contribution.countedParamEnv,
    algEnv := appendFirstOccurrences merged.algEnv contribution.algEnv }) {}

/-- REPEATED-NAME VERDICT, value channel: some PAIR of the values carried by
    `name`'s contributions differs (every contribution that carries a value must
    carry an equal one). Stated over all pairs, so it depends only on the
    multiset of contributions (`repeated_name_failure_is_permutation_invariant`). -/
def repeatedNameValueConflict (name : Ident) (contributions : List ParameterPatternBindings) : Bool :=
  let values := contributions.filterMap (fun contribution => lookupAssoc name contribution.argEnv)
  values.any (fun first => values.any (fun second => !(first == second)))

/-- REPEATED-NAME VERDICT, counted channel: compare the complete counted binding,
    including emitted count. Ordinary binder inputs use value-boundary counts,
    but successful merge invariance must not rely on discarding this component. -/
def repeatedNameCountedConflict (name : Ident) (contributions : List ParameterPatternBindings) : Bool :=
  let values := contributions.filterMap (fun contribution => lookupAssoc name contribution.countedParamEnv)
  values.any (fun first => values.any (fun second => !(first == second)))

/-- REPEATED-NAME VERDICT, algorithm channel: when two or more contributions
    bind `name` on the algorithm channel, EACH of them must also carry a value,
    because repeated-bind equality compares values and an algorithm-only
    argument has none. -/
def repeatedNameAlgorithmConflict (name : Ident) (contributions : List ParameterPatternBindings) : Bool :=
  let carriers := contributions.filter (fun contribution => (lookupAssoc name contribution.algEnv).isSome)
  2 ≤ carriers.length && carriers.any (fun contribution => (lookupAssoc name contribution.argEnv).isNone)

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

/-- Equal values are insufficient when selecting either callable can change an invocation.
    All callable contributions must have the same identity, even for just two occurrences. -/
def repeatedNameCallableIdentityConflict (name : Ident) (contributions : List ParameterPatternBindings) : Bool :=
  let algorithms := contributions.filterMap (fun contribution => lookupAssoc name contribution.algEnv)
  algorithms.any (fun first => algorithms.any (fun second => !sameRepeatedCallableIdentity first second))

/-- REPEATED-NAME BINDING IS ORDER-INDEPENDENT (September 2026). The failure,
    if any, of the names that become COMPLETE at one merge — every one of their
    contributions at this pattern level is in `contributions`. A repeated name
    binds iff every PAIR of its contributions is compatible under the
    two-binding rule (equal values; equal complete counted pairs; two algorithm-channel
    bindings only when both carry a value and have the same callable identity), so the verdict depends on the
    multiset of contributions and never on their order or on how the merges are
    grouped: `P(f, f, f)` rejects `(Inc, 5, A)` in every permutation. Two distinct
    callable identities now reject even if their values agree. Within one merge
    an unequal value or counted value (`badArity`) is reported before an
    algorithm-channel conflict (`typeMismatch`). C#: `RepeatedNameAggregate`. -/
def repeatedNameFailure (names : List Ident) (contributions : List ParameterPatternBindings) : Option Error :=
  if names.any (fun name => repeatedNameValueConflict name contributions) then some Error.badArity
  else if names.any (fun name => repeatedNameCountedConflict name contributions) then some Error.badArity
  else if names.any (fun name => repeatedNameAlgorithmConflict name contributions) then
    some (Error.typeMismatch "Repeated bind equality is not supported for algorithm-only arguments")
  else if names.any (fun name => repeatedNameCallableIdentityConflict name contributions) then
    some (Error.typeMismatch "Repeated bind equality requires the same callable identity")
  else none

/-- The merges of one bound range (Lean's `bindPairs` order,
    `merge c₁ (merge c₂ (… cₙ))`): the innermost merge runs first, and a
    repeated name is decided at the ONE merge where its last contribution
    joins — the step of its first occurrence in the range — unless the level
    binds it outside this range too (`outside`: the other range or the
    collector), in which case the later cross merge decides it with every
    contribution in hand. `earlier` holds the range's contributions left of the
    current one. C#: `FindRangeRepeatedNameFailure`. -/
def settlePatternRange (outside : Ident -> Bool)
    : List ParameterPatternBindings -> List ParameterPatternBindings -> Option Error
  | [], _ => none
  | current :: rest, earlier =>
      match settlePatternRange outside rest (earlier ++ [current]) with
      | some error => some error
      | none =>
          let completing := current.names.filter (fun name =>
            rest.any (fun contribution => contribution.binds name)
              && !earlier.any (fun contribution => contribution.binds name)
              && !outside name)
          repeatedNameFailure completing (current :: rest)

/-- Builtin collection-item view of the bound collection argument: opens
  exactly one outer sequence or exact-list boundary to its immediate items;
  any other value supplies itself as one item (a scalar is a one-element
  collection). Never recursive — nested sequence values and nested list
  values stay intact as single items.
  Applied strictly AFTER ordinary fixed parameter binding, to the already
  bound `collection` parameter only — argument boundaries are never altered
  before binding. Call parameter binding never uses this view, and
  assignment deconstruction opens its received value through the
  sequence-value parameter pattern instead. C#: `BuiltinCollectionItems`. -/
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
      `P((x, *rest))`, `P((x))` and `Pair(x, y)` do not. A COLLECTING parameter
      contributes ZERO required slots; a nested pattern still consumes one, and
      its scalar one-item fallback binds ONE supplied value, never none;
    * a clause family accepts iff some branch's top-level pattern has arity
      zero — exactly the branch `matchCallBranches` selects for an empty
      argument list. A flat multi-binder core equivalent
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

/-- Validate the output shape required by counted builtins that must emit
    exactly one top-level value.

    Non-empty sequence values are valid; the empty sequence value `()` and
    multiple top-level outputs are rejected. (An empty-sequence output is a visible
    slot at the output boundary, but these builtins require a substantive single
    element.) -/
def expectSingleValueWith (msg : String) (out : CountedResult) : EvalM Result :=
  match out with
  | (Result.sequenceValue [], 1) => .error (Error.withContext msg Error.badArity)
  | (value, 1) => pure value
  | _ => .error (Error.withContext
    msg
    Error.badArity)

/-- Validate the output shape required by `reduce`.
    The step must emit exactly one accumulator value. -/
def expectSingleAccumulator (out : CountedResult) : EvalM Result :=
  expectSingleValueWith
    "reduce step must return a single accumulator value"
    out

/-- Validate the output shape required by `map`.
    The transform must emit exactly one mapped element: one atom, one string,
    one sequence value, or one exact list value is valid (the empty list `[]`
    counts as one value), while empty-sequence and multi-output results are
    rejected. -/
def expectSingleMappedElement (out : CountedResult) : EvalM Result :=
  expectSingleValueWith
    "map transform must return a single element"
    out

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
    callable-shaped — a builtin, a conditional clause family, or an algorithm
    declaring parameters/patterns — as opposed to a zero-parameter VALUE
    property that merely resolved through the dual algorithm channel. Used to
    decide whether a valueless argument bound by a collecting parameter gets the targeted
    "collects values, but ... is a callable" diagnostic or surfaces its
    genuine value-evaluation error. C#: `IsFunctionShapedAlgorithm`. -/
def Algorithm.isFunctionShaped : Algorithm -> Bool
  | .builtin _ => true
  | .conditional _ _ _ _ => true
  | a => !(Algorithm.params a).isEmpty || !(Algorithm.parameterPatterns a).isEmpty

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
    binds exactly the items allocated to it through this single helper and
    never inspects their values. A collector opens nothing: one written
    argument is one item whatever its value, so `Coll((1, 2))` is
    `[(1, 2)]`, `Coll([1, 2])` is `[[1, 2]]`, `Coll(())` is `[()]`, and
    `Coll([])` is `[[]]` — only the caller's explicit spread turns a value into
    several items (`Coll((1, 2)*)` and `Coll([1, 2]*)` are `[1, 2]`).
    Deconstruction and nested sequence-value patterns open their one value
    BEFORE allocation, as explicit structural syntax, and the collector then
    collects the opened items exactly. The round trip
    `Result.spreadItems (collectSegment xs) = xs` makes collecting-parameter
    forwarding ordinary list spread: `Forward(*items) = Target(items*)`
    re-supplies exactly the collected items with no hidden raw-supply
    metadata. A collecting value is one visible value, so its emitted count is
    always 1 (including `[]`). C#: `CollectSegment` (inside
    `CreateCollectingCapture`). -/
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
    applied only to public result boundaries, never to internal
    body/root output accumulation (`evalAlgOutputCountedCore`), which must keep
    its multi-item counts. (Collecting parameter storage needs no re-count:
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

/-- Reify a counted argument shape as a zero-parameter algorithm that preserves
    the same value and emitted top-level count when evaluated. -/
def countedArgAlgorithm (arg : CountedResult) : Algorithm :=
  let output :=
    match arg with
    | (_, 0) => [emptyResultExpr]
    | _ => (countedTopLevelValues arg).map resultToExpr
  Algorithm.mk none [] [] [] output

mutual
partial def bindCountedParameterPattern (pattern : ParameterPattern) (input : CountedResult)
    : EvalM CountedParameterPatternBindings := do
  match pattern with
  | .capture parameter =>
      match parameter.kind with
      | .normal => pure { countedParamEnv := [(parameter.name, input)] }
      | .collecting => .error Error.badArity
  | .sequenceValue items =>
      -- This counted matcher is the callback binding path, and it opens the
      -- callback value through the SAME nested-pattern rule as the ordinary
      -- binder `bindParameterPattern` (`Result.sequenceValuePatternItems`):
      -- a sequence or list value opens one level, and any other value is a
      -- one-item supply at every level and for every group size, so
      -- `map([7], P)` with `P((x, *rest))` binds `x = 7, rest = []` exactly
      -- like `P(7)`, and `P((x, y))` rejects a scalar with the nested group's
      -- ordinary `arityMismatch 2 1` in both (September 2026, S3; the
      -- callback path formerly fell back only for one-item groups).
      -- The pattern's explicit structure opens exactly this one boundary; a
      -- nested collecting binding collects the opened items exactly.
      let nestedInputs := (Result.sequenceValuePatternItems input.fst).map (fun value =>
        (value, Result.valueCount value))
      bindCountedParameterPatternList items nestedInputs

partial def bindCountedParameterPatternList (patterns : List ParameterPattern)
  (inputs : List CountedResult) : EvalM CountedParameterPatternBindings := do
  let rec findCollecting : List ParameterPattern -> Nat -> Option (Nat × CallableParameter)
    | [], _ => none
    | (.capture parameter) :: rest, index =>
        match parameter.kind with
        | .collecting => some (index, parameter)
        | .normal => findCollecting rest (index + 1)
    | (.sequenceValue _) :: rest, index => findCollecting rest (index + 1)
  -- The same binding and merge order as `bindParameterPatternList`: every
  -- pattern of a range binds before anything merges, and each repeated name
  -- is decided once, symmetrically, when its last contribution joins
  -- (`settlePatternRange`); counted contributions carry only the counted
  -- channel, so an unequal repeat is `badArity`.
  let asContribution (bindings : CountedParameterPatternBindings) : ParameterPatternBindings :=
    { countedParamEnv := bindings.countedParamEnv }
  let rec bindPairs : List ParameterPattern -> List CountedResult -> EvalM (List ParameterPatternBindings)
    | [], [] => pure []
    | pattern :: patterns', input :: inputs' => do
        let current <- bindCountedParameterPattern pattern input
        let rest <- bindPairs patterns' inputs'
        pure (asContribution current :: rest)
    | _, _ => .error (Error.arityMismatch patterns.length inputs.length)
  let settle (outside : Ident -> Bool) (bound : List ParameterPatternBindings) : EvalM Unit :=
    match settlePatternRange outside bound [] with
    | some error => .error error
    | none => pure ()
  let merged (contributions : List ParameterPatternBindings) : CountedParameterPatternBindings :=
    { countedParamEnv := (mergeFirstOccurrences contributions).countedParamEnv }
  -- The accepted supply is the ONE minimum-supply rule
  -- (`ParameterPattern.minimumSuppliedSlots`): without a collecting capture
  -- every pattern needs its own slot, so the count is EXACT; with one the
  -- minimum is a lower bound and the collector takes whatever is left over.
  match findCollecting patterns 0 with
  | none =>
      let required := ParameterPattern.minimumSuppliedSlots patterns
      if inputs.length != required then
        .error (Error.arityMismatch required inputs.length)
      else do
        let bound <- bindPairs patterns inputs
        settle (fun _ => false) bound
        pure (merged bound)
  | some (collectingIndex, collectingParameter) =>
      let required := ParameterPattern.minimumSuppliedSlots patterns
      if inputs.length < required then
        .error (Error.arityMismatch required inputs.length)
      else
        let prefixPatterns := patterns.take collectingIndex
        let prefixInputs := inputs.take collectingIndex
        let suffixCount := patterns.length - collectingIndex - 1
        let suffixPatterns := patterns.drop (collectingIndex + 1)
        let suffixInputs := inputs.drop (inputs.length - suffixCount)
        let capturedInputs := (inputs.drop collectingIndex).take (inputs.length - suffixCount - collectingIndex)
        let prefixBound <- bindPairs prefixPatterns prefixInputs
        settle (fun name => ParameterPattern.anyBindsName name suffixPatterns
          || collectingParameter.name == name) prefixBound
        let suffixBound <- bindPairs suffixPatterns suffixInputs
        settle (fun name => ParameterPattern.anyBindsName name prefixPatterns
          || collectingParameter.name == name) suffixBound
        -- Collecting binding COLLECTS exactly the items allocated to it as one
        -- exact immutable list value, emitted count 1 (a list is one visible
        -- value): it never opens an item (THE EXACT COLLECTOR LAW).
        let captured := collectSegment (capturedInputs.map Prod.fst)
        let capturedBinding := (collectingParameter.name, (captured, 1))
        let collectingBindings : ParameterPatternBindings :=
          { countedParamEnv := [capturedBinding] }
        let leftSide := prefixBound ++ [collectingBindings]
        let atCollector := [collectingParameter.name].filter (fun name =>
          prefixBound.any (fun contribution => contribution.binds name)
            && !ParameterPattern.anyBindsName name suffixPatterns)
        match repeatedNameFailure atCollector leftSide with
        | some error => .error error
        | none =>
            let atSuffix := (suffixBound.flatMap ParameterPatternBindings.names).eraseDups.filter
              (fun name => leftSide.any (fun contribution => contribution.binds name))
            match repeatedNameFailure atSuffix (leftSide ++ suffixBound) with
            | some error => .error error
            | none => pure (merged (leftSide ++ suffixBound))
      end

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

inductive PreparedSequenceBuiltinSuffixArg where
  | algorithm (value : Algorithm) (source? : Option Expr := none)
      (callable? : Option Algorithm := none)
  | value (value : Result)
  | wholeNumber (value : Int)
  deriving Repr

structure BoundSequenceBuiltinArguments where
  preparedInput : PreparedSequenceBuiltinInput
  iterationItems : List CountedResult
  suffixArgs : List PreparedSequenceBuiltinSuffixArg
  deriving Repr

structure ResolvedArgumentAlgorithm where
  algorithm : Algorithm
  spreadsSequence : Bool := false
  /-- The written argument expression this algorithm was resolved from: the
      demand-site identity `zeroArgumentDemandError?` reports through when a
      builtin VALUE slot demands the algorithm with zero arguments. `none` for
      value-reified arguments (prepared callback data, expanded spread items,
      dotted receivers), whose algorithms carry no parameters. -/
  source? : Option Expr := none
  /-- A parameter argument bound on BOTH channels resolves to its value side
      (`algorithm`, a wrapper that reads the bound value, so a VALUE slot never
      re-runs the argument's body) and keeps its ALGORITHM-channel binding here.
      A slot that INVOKES its argument — a sequence callback or a loop step —
      calls `invoked`, so `Apply(f, xs) = map(xs, f)` applies the callable `f`
      exactly as `map(xs, Cnt)` does even when `Cnt` also satisfies a
      zero-argument value demand. `none` for every other argument, whose
      `algorithm` already is its algorithm-channel identity. -/
  callable? : Option Algorithm := none
  deriving Repr

/-- The algorithm an ALGORITHM slot (a sequence callback or a loop step)
    invokes: a parameter's algorithm-channel binding when it has one, otherwise
    the resolved algorithm. VALUE slots read `algorithm`. -/
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
  -- A capture is a value boundary, not algorithm/namespace identity, so
  -- `open (M)` is NOT an open form: it is rejected by open-form validation
  -- with badOpenForm, exactly like a spread-marked target.
  | .resolve n       => some (.resolve n)
  -- Only argumentless dot paths are open forms. The C# front end rejects a
  -- Grace-marked open target such as `open A~.B` before Lean encoding; valid
  -- graced dot sources otherwise encode as the same dotMember as ordinary dot.
  | .dotMember o n _ none => some (.dotCall o n)
  | _                => none          -- capture, argument-bearing dot forms, call, and all other forms are rejected

def Expr.isOpenForm (e : Expr) : Bool :=
  (Expr.openForm? e).isSome

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
    VALUE with zero explicit arguments: the value-position `param` / `resolve` /
    `algorithmExpr` arms of `evalCounted`, every lazy builtin VALUE slot (the `if`
    condition and branches, `while`/`repeat` initial state, the `repeat` count,
    `atoms`, `range` — `evalArgumentValueCounted`), and the ordinary-dot `string`
    intrinsic's receiver.

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
    - a written brace block (`.algorithmExpr`): `unresolvedImplicitParams`;
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

/-- Recover the member list a sequence-value pattern should match against.
    `Result.normalize` collapses `sequenceValue [x]` -> `x` at every algorithm boundary,
    so singleton sequence values never exist at runtime. A singleton sequence-value
    pattern such as `(b)` therefore must also match a non-sequence-value result by
    treating it as `sequenceValue [result]`.

    This rule is shared by `matchPattern` and `matchCountedPattern` so direct
    conditional calls and counted callback calls (map/filter/reduce) accept
    exactly the same input shapes. -/
def patternSequenceValueMembers? (patternCount : Nat) (r : Result) : Option (List Result) :=
  match r with
  | .sequenceValue rs => if rs.length == patternCount then some rs else none
  | _ => if patternCount == 1 then some [r] else none

/-- Match a pattern against a Result, returning accumulated bindings on success.
    - `bind x` matches any Result, binding x → r
    - `litInt n` matches only `Result.atom n`; `litBool b` only `Result.bool b`
    - `sequenceValue ps` matches `Result.sequenceValue rs` with same length, recursively;
      a singleton sequence-value pattern also matches a non-sequence-value result because
      normalization collapses singleton sequence values (`patternSequenceValueMembers?`)

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
  | .sequenceValue ps  =>
      match patternSequenceValueMembers? ps.length r with
      | none => none
      | some rs =>
          let rec go : List Pattern -> List Result -> ValEnv -> Option ValEnv
            | [], [], current => some current
            | p::ps', r::rs', current => do
                let next <- matchPatternInto p r current
                go ps' rs' next
            | _, _, _ => none
          go ps rs env

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
      match patternSequenceValueMembers? ps.length arg.fst with
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

/-- Builtin argument adapters reify each written slot as one value-producing
    adapter. A zero-declaration algorithm block slot keeps its one-slot value
    boundary here (written-slot reification: `repeat(step, n, {1, 2})`
    supplies ONE initial state slot), exactly as before the block's algorithm
    identity became visible to user-call higher-order binding. Blocks with
    parameters, properties, or opens still resolve as algorithms for
    algorithm-consuming builtin arguments (callbacks). -/
def zeroDeclarationBlockValueSlot : Expr -> Bool
  | .algorithmExpr (.mk _ patterns opens props _ _) =>
      patterns.isEmpty && opens.isEmpty && props.isEmpty
  | _ => false

def isLiftableArgResolutionError : Error → Bool
  | .notAnAlgorithm _ => true
  | .illegalInEval _  => true
  | .withContext _ e   => isLiftableArgResolutionError e
  | _                  => false

def bindLoopStepValueEnv (parameters : List CallableParameter)
    (normalBindings : List (Prod Ident Result))
    (collectingName : Ident) (captured : Result) : EvalM ValEnv :=
  match parameters with
  | [] =>
      match normalBindings with
      | [] => pure []
      | _ => .error Error.badArity
  | parameter :: rest =>
      match parameter.kind with
      | .collecting => do
          let vals <- bindLoopStepValueEnv rest normalBindings collectingName captured
          pure ((collectingName, captured) :: vals)
      | .normal =>
          match normalBindings with
          | [] => .error Error.badArity
          | binding :: bindings' => do
              let vals <- bindLoopStepValueEnv rest bindings' collectingName captured
              pure ((binding.fst, binding.snd) :: vals)

def loopStateResult (stateSlots : List Result) : Result :=
  Result.normalize (.sequenceValue stateSlots)

/-- Split a loop step output into next state slots and the continuation flag.
    The step's LAST output is the flag and must be a Boolean value (`true`
    continues, `false` stops); a number, string, sequence, or list there is a
    value-kind error, never a truth test. A single-output step keeps the
    established shape — its one slot is both the next state and the flag — so
    it must be Boolean too. C#: `Evaluator.SplitContSlots`. -/
def splitContSlots (outputSlots : List Result) : EvalM (List Result × Bool) := do
  match outputSlots with
  | [] => .error Error.badArity
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
    bare `x` output row, `x.Coll` on a collecting receiver, the map/reduce
    single-element checks), a `()` item emits zero values, and only an explicit
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
    C#: the zero-argument property access path
    (`GetOrEvaluateZeroArgPropertyResult`), entered by callers only after the
    law accepted. -/
def isCacheableZeroArgPropertyAlgorithm (a : Algorithm) : Bool :=
  Algorithm.acceptsZeroSuppliedArguments a

/-- The cache key of one property-style access (see `ZeroArgPropertyCacheKey`
    for the law it encodes): an exported binding's key carries no environment
    components, a local-only binding's key carries all three. -/
def zeroArgPropertyCacheKey (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (ctx : EvalCtx) (env : ValEnv)
    : ZeroArgPropertyCacheKey :=
  let bindingContextFree := binding.exposure.isExported
  {
    accessKind := if bindingContextFree then .lexical else accessKind,
    owner := reprStr (cacheScopeShape owner.asScopeCtx),
    propertyName := binding.name,
    propertyAlgorithm := reprStr (cacheAlgorithmShape binding.alg),
    valEnv := if bindingContextFree then none else some (reprStr env),
    algEnv := if bindingContextFree then none else some (reprStr ctx.algEnv),
    countedParamEnv := if bindingContextFree then none else some (reprStr ctx.countedParamEnv),
    bindingContext := if bindingContextFree then none else some ctx.bindingContext
  }

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
  | .requireAnyItem =>
      if collected.totalItemCount = 0 then
        .error (Error.withContext
          s!"{builtinDisplayName b} requires a non-empty collection"
          Error.badArity)
      else
        pure collected

/-- Collect top-level collection elements as single atomic numeric values.
    Used by numeric ordering and aggregation builtins, which reject strings
    and sequence values instead of inventing mixed-type or structural
    interpretation.

    Diagnostics identify the 0-based collection item index so numeric shape
    failures remain debuggable after counted top-level extraction. -/
def collectSingleAtomicNumbers (b : Builtin)
    : Nat -> List Result -> EvalM (List Int)
  | _, [] => pure []
  | index, item :: rest =>
      match Result.singleAtomicNumber? item with
      | some n => do
          let tail <- collectSingleAtomicNumbers b (index + 1) rest
          pure (n :: tail)
      | none =>
          .error (Error.withContext
            (numericSequenceItemErrorContext b index item)
            Error.badArity)

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
    an unevaluated callable using its written source. Preserve a valid value's
    body error; callback positions never consult this helper. -/
def sequenceBuiltinValueDemandError? (item : CallableCallItem) : Option Error :=
  match item.algorithm? with
  | some alg => (zeroArgumentDemandError? item.source? alg).or item.error?
  | none => item.error?

def prepareSequenceBuiltinSuffixArgItem
    (b : Builtin) (descriptor : SequenceBuiltinSuffixArgDescriptor)
    (item : CallableCallItem) : EvalM PreparedSequenceBuiltinSuffixArg := do
  match descriptor.kind with
  | .algorithm =>
    match item.algorithm? with
    | some alg => pure (.algorithm alg item.source? item.callable?)
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
        match sequenceBuiltinValueDemandError? item with
        | some err => .error err
        | none =>
        .error (Error.withContext
          (sequenceBuiltinSuffixArgErrorContext b descriptor)
          Error.badArity)
  | .wholeNumber =>
    match item.value? with
    | some value =>
      match Result.singleAtomicNumber? value with
      | some number => pure (.wholeNumber number)
      | none =>
          .error (Error.withContext
            (sequenceBuiltinSuffixArgErrorContext b descriptor)
            Error.badArity)
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

def expectPreparedSequenceBuiltinAlgorithmSuffixArgFull
    (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor)
    (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) : EvalM ResolvedArgumentAlgorithm :=
  expectPreparedSequenceBuiltinSuffixArgAt b descriptors args index .algorithm fun descriptor arg =>
    match arg with
    | .algorithm algorithm source? callable? =>
        pure { algorithm := algorithm, source? := source?, callable? := callable? }
    | _ =>
        internalSequenceBuiltinSuffixArgMetadataError b
          s!"prepared suffix argument {index + 1} ({descriptor.name}) did not match metadata kind {sequenceBuiltinSuffixArgKindDesc .algorithm}"

/-- The CALLBACK a sequence builtin invokes from an algorithm suffix slot (the
    `filter` predicate, the `map` mapper, the `reduce` reducer): the argument's
    algorithm-channel identity (`ResolvedArgumentAlgorithm.invoked`). `reduce`'s
    `initial` shares the algorithm metadata kind but is a VALUE slot, so it
    reads the full argument (`...Full`) and demands its value side. -/
def expectPreparedSequenceBuiltinAlgorithmSuffixArg
    (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor)
    (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) : EvalM Algorithm := do
  let arg <- expectPreparedSequenceBuiltinAlgorithmSuffixArgFull b descriptors args index
  pure arg.invoked

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

def reduceInitialAccumulatorRequiresValueError : Error :=
  Error.withContext "while preparing reduce initial accumulator" Error.badArity

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

    Each atom, string, or sequence value counts as one top-level element.
    Sequence values are not flattened or recursively inspected, and empty
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
    The collection must be non-empty. Law: `first_is_select_zero`.
    C#: `EvalFirstCounted`. -/
def evalFirstCounted (items : List Result) : EvalM CountedResult := do
  match items with
  | first :: _ => pure (first, Result.valueCount first)
  | [] => .error Error.badArity

/-- Evaluate `last(collection)`: SELECT the last top-level collection element
    through the same value boundary as `evalFirstCounted` and
    `collection:(count - 1)`. The collection must be non-empty.
    Law: `last_is_select_last`. C#: `EvalLastCounted`. -/
def evalLastCounted (items : List Result) : EvalM CountedResult := do
  match items.getLast? with
  | some last => pure (last, Result.valueCount last)
  | none => .error Error.badArity

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
  | [] => .error Error.badArity
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
  | [] => .error Error.badArity
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
  | [] => .error Error.badArity
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
  -- `open (M)` is not openable. Top-level capture targets are already
  -- rejected by resolveAllOpens' open-form validation; this arm is reached
  -- through dotted-path recursion (`open (X).B`) and prebuilt ASTs.
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

/-- Resolve all opens of an algorithm upfront.
    Deduplicates named opens by `openExprName` (first occurrence wins) to
    avoid repeated resolution and spurious ambiguity.  Inline blocks are never
    deduplicated (each gets a unique positional key).
    Validates all open expressions first for fail-fast diagnostics. -/
def resolveAllOpens (a : Algorithm) (ctx : EvalCtx) : EvalM (List ResolvedOpen) := do
  let rawOpens := Algorithm.opens a
  -- Deduplicate by key (first occurrence wins); inline blocks use positional keys
  let tagged := rawOpens.mapIdx (fun idx e =>
    let key := match e with
      | .algorithmExpr _ => s!"(inline#{idx})"   -- * unique per original position, never deduped
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
  -- Then resolve (each open wrapped with context using its dedup key)
  acc.mapM (fun (key, e) => do
    let lib <- withCtx (CtxMsg.openMsg key) (resolveOpen e ctx)
    pure { key := key, expr := e, lib := lib })

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
    ownership-first / dedup / ambiguity rules exist exactly once. -/
def lookupLexicalProperty (a : Algorithm) (name : Ident) (ctx : EvalCtx)
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

def resolveAlg (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  match e with
  | .sequenceConstruct _ _ =>
    .error (Error.notAnAlgorithm "sequence construct expression")
  | .sequenceSpread _ =>
    .error (Error.notAnAlgorithm "spread expression")
  | .algorithmExpr a => pure (wireToCaller ctx a)
  -- Capture is not algorithm identity: the algorithm channel sees only a
  -- zero-parameter value thunk over the bundle, exactly as the pre-split
  -- transparent wrapper behaved. `Apply((Inc, Dec))` therefore never receives
  -- either callable identity (`f(9)` on the thunk is an arity error), while
  -- the redundant group `Apply((Increment))` IS `Apply(Increment)` — the
  -- parser erases it before this node exists (parentheses group syntax).
  -- C#: `CaptureValueThunk`.
  | .capture rows => identifyRuntimeAlgorithm (wireToCaller ctx (Algorithm.mk none [] [] [] rows))
  | .resolve n =>
      match ctx.callStack with
      | a::_ => lookupLexical a n ctx
      | []   => .error (Error.unknownName n)
  | .dotMember o n fallback args =>
      -- Lift a.f / a.f(args) to a wrapper algorithm; evalDotCall handles all
      -- semantics (builtin property special cases, structural property,
      -- receiver injection, lexical fallback). The whole node — including its
      -- elaborated fallback identity — rides along unchanged. This is the
      -- higher-order/value identity of a dot RESULT; a dot edge in RECEIVER
      -- position resolves through `resolveDotReceiver` below, which navigates
      -- an argumentless chain's declared structural members before falling
      -- back to this memberless wrapper.
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

/-- Resolve a dot edge's RECEIVER in algorithm position — the structural half
    of the ordinary DotCall law applied at EVERY level of a chain.

    Every receiver shape resolves through canonical `resolveAlg` except an
    argumentless, non-`string` dot edge `X.M`, which NAVIGATES: when `X`
    (resolved the same way, recursively) is an algorithm that declares an
    exported `M`, the receiver IS that member algorithm wired to `X`
    (`Algorithm.childOf`), so `Lib.Sub.Q` reads `Sub`'s own `Q` before any
    lexical `Q(x)` is considered, exactly as `Lib.Q` reads `Lib`'s. A declared
    but local-only `M`, or one defined only inside conditional branches, is
    the same structural error that evaluating `X.M` itself reports — never a
    fallback. When `X` does not declare `M` (or is not an algorithm at all),
    the edge is an ordinary dot RESULT — its lexical fallback's value, or the
    `string` intrinsic — and resolves to `resolveAlg`'s memberless wrapper, so
    the chain continues by value (`3.A.B` stays `B(A(3))`). An argument-bearing
    edge is a call, hence a value, and never navigates; a capture receiver
    keeps suppressing structural identity (`(A, B).V` and `(A*).V` fall back —
    a redundant group never reaches this node, so the sources `(Obj).V` and
    `(Lib.Sub).Q` are simply `Obj.V` and `Lib.Sub.Q`: parentheses group
    syntax and never change which receiver is navigated).

    The resolution is identity navigation only: no intermediate edge is
    evaluated, so a parameterized or output-less container navigates exactly
    as it does at the first level (`F.Q` works while `F` alone is an arity or
    missing-output error). The higher-order channel is untouched: `resolveAlg`
    still lifts every general argumentless dot expression to its
    zero-parameter wrapper identity. C#: `ResolveDotReceiver`. -/
def resolveDotReceiver (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
  match e with
  | .dotMember o n _ none =>
      if n = "string" then resolveAlg e ctx
      else do
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
  | _ => resolveAlg e ctx


/-- Resolve one builtin argument expression to its algorithm, paired with the
    parameter's ALGORITHM-channel binding when the argument is a parameter
    reference resolved to its value side (`ResolvedArgumentAlgorithm.callable?`).
    A parameter with a value binding resolves to a wrapper that reads that value,
    so a VALUE slot never re-runs the argument's body; the algorithm binding rides
    along for the slots that INVOKE their argument. A parameter bound only on the
    value channel has no algorithm binding (`resolveAlg` reports `notAnAlgorithm`),
    so it carries none. -/
def resolveArgAlgExpr (e : Expr) (ctx : EvalCtx) (env : ValEnv)
    : EvalM (Algorithm × Option Algorithm) := do
  let shouldUseValueSide <- match e with
    | .param name => do
        let (parameterCtx, values) <- parameterContext name ctx env
        pure ((parameterCtx.countedParamEnv.lookup name).isSome || (values.lookup name).isSome)
    | _ => pure false
  if shouldWrapArgExprAsValue e || zeroDeclarationBlockValueSlot e then
    pure (wireToCaller ctx (Algorithm.ofExpr e), none)
  else if shouldUseValueSide then
    let callable? <-
      match <- evalAttempt (resolveAlg e ctx) with
      | .ok a => pure (some a)
      | .error (.notAnAlgorithm _) => pure none
      | .error err => .error err
    pure (wireToCaller ctx (Algorithm.ofExpr e), callable?)
  else
    match <- evalAttempt (resolveAlg e ctx) with
    | .ok a    => pure (a, none)
    | .error err =>
      if isLiftableArgResolutionError err then
        pure (wireToCaller ctx (Algorithm.ofExpr e), none)
      else
        .error err

/-- Resolve argument expressions to algorithms for builtin dispatch, tagging
    each argument with whether it is a spread expression.
    Unlike a strict `mapM resolveAlg`, this wraps *liftable* non-resolvable
    expressions (`notAnAlgorithm`, `illegalInEval`) in trivial
    `Algorithm.ofExpr` wrappers wired to the caller scope (see
    `resolveArgAlgExpr`).  This enables ergonomic builtin syntax such as
    `If(X >= 5, 1, 0)` without requiring explicit `{…}` blocks around every
    argument.

    Wrapping is safe because builtins evaluate their algorithm arguments
    lazily via `evalAlgOutput`, so the expression is evaluated on demand
    within the correct scope rather than resolved structurally upfront.

    Errors that indicate genuine lookup or semantic failures (`unknownName`,
    `unknownProperty`, `ambiguousOpen`, etc.) are propagated immediately so
    diagnostics remain precise.

    Non-builtin call paths are unaffected — user-defined calls still evaluate
    arguments eagerly through the expression-position call path
    (`evalCallExpr` / `evalCallCountedExpr`). -/
def resolveArgAlgsWithSequenceSpread (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    : EvalM (List ResolvedArgumentAlgorithm) :=
  args.mapM (fun e => do
    let (alg, callable?) <- resolveArgAlgExpr e ctx env
    let spreadsSequence :=
      match e with
      | .sequenceSpread _ => true
      | _ => false
    pure { algorithm := alg, spreadsSequence := spreadsSequence, source? := some e,
           callable? := callable? })

/-- Try to resolve each argument expression to an algorithm.
    Returns `some alg` for expressions that resolve, `none` for those that don't
    (e.g., numeric literals, arithmetic). Every `algorithmExpr` contributes its
    contained algorithm regardless of declaration/output count. A `capture`
    contributes only its zero-parameter value thunk, never the algorithm
    identity of an expression it contains. Only liftable
    errors → none; genuine lookup failures propagate.
    Used by the shared call argument-slot assembly
    (`collectVariadicCallItems`, serving every callable shape) to build AlgEnv
    for higher-order algorithm parameters. -/
def tryResolveArgAlgs (args : OutputBundle) (ctx : EvalCtx) : EvalM (List (Option Algorithm)) :=
  args.mapM (fun e => do
    if shouldWrapArgExprAsValue e then
      pure none
    else
      match <- evalAttempt (resolveAlg e ctx) with
      | .ok a    => pure (some a)
      | .error err =>
        if isLiftableArgResolutionError err then
          pure none
        else
          .error err)

/-- `sizeOf` of a list prefix never exceeds the list's `sizeOf`.
    Termination support for the pattern-binding mutual pair below. -/
private theorem list_take_sizeOf_le [SizeOf α] (n : Nat) (xs : List α) :
    sizeOf (List.take n xs) ≤ sizeOf xs := by
  induction xs generalizing n with
  | nil => cases n <;> simp [List.take]
  | cons x xs ih =>
      cases n with
      | zero => simp [List.take]; omega
      | succ n =>
          simp only [List.take, List.cons.sizeOf_spec]
          have := ih n
          omega

/-- `sizeOf` of a list suffix never exceeds the list's `sizeOf`.
    Termination support for the pattern-binding mutual pair below. -/
private theorem list_drop_sizeOf_le [SizeOf α] (n : Nat) (xs : List α) :
    sizeOf (List.drop n xs) ≤ sizeOf xs := by
  induction xs generalizing n with
  | nil => cases n <;> simp [List.drop]
  | cons x xs ih =>
      cases n with
      | zero => simp [List.drop]
      | succ n =>
          simp only [List.drop, List.cons.sizeOf_spec]
          have := ih n
          omega

mutual
  def bindParameterPattern (pattern : ParameterPattern) (input : ParameterPatternInput)
      (allowAlgorithmBindings : Bool) : EvalM ParameterPatternBindings := do
    match pattern with
    | .capture parameter =>
        match parameter.kind with
        | .normal =>
            let argEnv := match input.value? with
              | some value => [(parameter.name, value)]
              | none => []
            let algEnv :=
              if allowAlgorithmBindings then
                match input.algorithm? with
                | some algorithm => [(parameter.name, algorithm)]
                | none => []
              else []
            if input.value?.isNone && (input.algorithm?.isNone || !allowAlgorithmBindings) then
              .error (input.error?.getD Error.badArity)
            else
              pure { argEnv := argEnv, countedParamEnv := [], algEnv := algEnv }
        | .collecting => .error Error.badArity
    | .sequenceValue items => do
        -- PATTERN PARENTHESES ARE CALL-SHAPE SYNTAX, NOT A RUNTIME BOUNDARY: a
        -- sequence-value pattern consumes ONE argument slot and opens that
        -- slot's VALUE (September 2026). A received sequence value or exact
        -- list value opens to its immediate items (`Result.structureItems?`)
        -- — the deconstruction receiver opens ONE lone structure boundary of
        -- either kind, so `x, y, z = [1, 2, 3]` binds like
        -- `x, y, z = [1, 2, 3]*` — and any other value is a one-item supply
        -- for the prefix/collecting/suffix matcher. Nothing about how the slot
        -- was WRITTEN survives here: `F((1, 2))`, `F(S)` with `S = 1, 2`,
        -- `F(((1, 2)))`, `F({S})`, and `F((S*))` all bind the value `(1, 2)`
        -- (the former written-slot view, which let a group's own written
        -- rows override the value, is gone: parentheses group syntax and
        -- never suspend normalization). The opening is the ONE nested-pattern
        -- rule `Result.sequenceValuePatternItems`, shared with the counted
        -- callback binder `bindCountedParameterPattern` (S3).
        let sequenceValueItems? :=
          match input.value? with
          | some value => some (Result.sequenceValuePatternItems value)
          | none => none
        match sequenceValueItems? with
        | none => .error (input.error?.getD Error.badArity)
        | some sequenceValueItems =>
            let nestedInputs := sequenceValueItems.map (fun value => { value? := some value : ParameterPatternInput })
            bindParameterPatternList items nestedInputs false
  -- Termination: the pattern-side `sizeOf` shrinks around the recursion cycle;
  -- the +1 tag on the list function breaks the tie for same-list entry calls.
  termination_by 2 * sizeOf pattern
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def bindParameterPatternList (patterns : List ParameterPattern)
      (inputs : List ParameterPatternInput) (allowAlgorithmBindings : Bool)
      : EvalM ParameterPatternBindings := do
    let rec findCollecting : List ParameterPattern -> Nat -> Option (Nat × CallableParameter)
      | [], _ => none
      | (.capture parameter) :: rest, index =>
          match parameter.kind with
          | .collecting => some (index, parameter)
          | .normal => findCollecting rest (index + 1)
      | (.sequenceValue _) :: rest, index => findCollecting rest (index + 1)
    -- `bindPairs` binds EVERY pattern of a range, left to right, before
    -- anything merges: the first binding failure wins over any repeated-name
    -- conflict of the range (September 2026). `settle` then decides the
    -- range's repeated names in the merge order (`settlePatternRange`).
    let rec bindPairs : List ParameterPattern -> List ParameterPatternInput
        -> EvalM (List ParameterPatternBindings)
      | [], [] => pure []
      | pattern :: patterns', input :: inputs' => do
          let current <- bindParameterPattern pattern input allowAlgorithmBindings
          let rest <- bindPairs patterns' inputs'
          pure (current :: rest)
      | _, _ => .error (Error.arityMismatch patterns.length inputs.length)
      termination_by ps _ => 2 * sizeOf ps
      decreasing_by
        all_goals simp_wf
        all_goals omega
    let settle (outside : Ident -> Bool) (bound : List ParameterPatternBindings) : EvalM Unit :=
      match settlePatternRange outside bound [] with
      | some error => .error error
      | none => pure ()
    -- The accepted supply is the ONE minimum-supply rule
    -- (`ParameterPattern.minimumSuppliedSlots`): without a collecting capture
    -- every pattern needs its own slot, so the count is EXACT; with one the
    -- minimum is a lower bound and the collector takes whatever is left over.
    match findCollecting patterns 0 with
    | none =>
        let required := ParameterPattern.minimumSuppliedSlots patterns
        if inputs.length != required then
          .error (Error.arityMismatch required inputs.length)
        else do
          let bound <- bindPairs patterns inputs
          settle (fun _ => false) bound
          pure (mergeFirstOccurrences bound)
    | some (collectingIndex, collectingParameter) =>
        let required := ParameterPattern.minimumSuppliedSlots patterns
        if inputs.length < required then
          .error (Error.arityMismatch required inputs.length)
        else
          let prefixPatterns := patterns.take collectingIndex
          let prefixInputs := inputs.take collectingIndex
          let suffixCount := patterns.length - collectingIndex - 1
          let suffixPatterns := patterns.drop (collectingIndex + 1)
          let suffixInputs := inputs.drop (inputs.length - suffixCount)
          let capturedInputs := (inputs.drop collectingIndex).take (inputs.length - suffixCount - collectingIndex)
          -- The prefix binds and settles its own repeated names, then the
          -- suffix; a name the level also binds on the other side of the
          -- collector (or as the collector) waits for the cross merges below.
          let prefixBound <- bindPairs prefixPatterns prefixInputs
          settle (fun name => ParameterPattern.anyBindsName name suffixPatterns
            || collectingParameter.name == name) prefixBound
          let suffixBound <- bindPairs suffixPatterns suffixInputs
          settle (fun name => ParameterPattern.anyBindsName name prefixPatterns
            || collectingParameter.name == name) suffixBound
          let rec collectValues : List ParameterPatternInput -> EvalM (List Result)
            | [] => pure []
            | input :: rest =>
                match input.value? with
                | some value => do
                    let values <- collectValues rest
                    -- Every item allocated to the flat top-level collecting
                    -- position contributes its ONE reified value, unopened.
                    pure (value :: values)
                | none =>
                    -- A collecting binding collects VALUES. A callable-shaped
                    -- argument (builtin, clause family, or parameterized
                    -- algorithm) has no value to collect — only fixed
                    -- parameters keep the dual algorithm channel — so name
                    -- the actual conflict instead of surfacing the argument's
                    -- incidental value-evaluation error. A zero-parameter
                    -- VALUE property whose body failed is NOT callable-shaped: its
                    -- genuine evaluation error surfaces.
                    -- C#: `BindParameterPatternList` (whose message also
                    -- names the collecting parameter).
                    match input.algorithm? with
                    | some alg =>
                        if alg.isFunctionShaped then
                          .error (Error.typeMismatch
                            "A collecting parameter collects values, but a supplied argument is a callable. Pass a value, or call the callable so its result is collected.")
                        else
                          .error (input.error?.getD Error.badArity)
                    | none => .error (input.error?.getD Error.badArity)
          let segment <- collectValues capturedInputs
          -- Collecting binding COLLECTS exactly the items allocated to it as
          -- one exact immutable list value, emitted count 1 (a list is one
          -- visible value): it never opens an item (THE EXACT COLLECTOR LAW).
          let captured := collectSegment segment
          let collectingBindings : ParameterPatternBindings :=
            { argEnv := [(collectingParameter.name, captured)],
              countedParamEnv := [(collectingParameter.name, (captured, 1))],
              algEnv := [] }
          -- Merge the prefix with the collector, then that with the suffix:
          -- the collector's name completes at the first merge unless the
          -- suffix binds it too, and every name shared with the suffix
          -- completes at the second.
          let leftSide := prefixBound ++ [collectingBindings]
          let atCollector := [collectingParameter.name].filter (fun name =>
            prefixBound.any (fun contribution => contribution.binds name)
              && !ParameterPattern.anyBindsName name suffixPatterns)
          match repeatedNameFailure atCollector leftSide with
          | some error => .error error
          | none =>
              let atSuffix := (suffixBound.flatMap ParameterPatternBindings.names).eraseDups.filter
                (fun name => leftSide.any (fun contribution => contribution.binds name))
              match repeatedNameFailure atSuffix (leftSide ++ suffixBound) with
              | some error => .error error
              | none => pure (mergeFirstOccurrences (leftSide ++ suffixBound))
  termination_by 2 * sizeOf patterns + 1
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have take_le := list_take_sizeOf_le collectingIndex patterns
         omega)
      | (have drop_le := list_drop_sizeOf_le (collectingIndex + 1) patterns
         omega)
end

def bindStructuredLoopState (step : Algorithm) (stateValues : List Result)
    : EvalM (ValEnv × CountedParamEnv) := do
  let inputs := stateValues.map (fun value => { value? := some value : ParameterPatternInput })
  let bindings <- bindParameterPatternList (Algorithm.parameterPatterns step) inputs false
  pure (bindings.argEnv, bindings.countedParamEnv)

def bindLoopStepState (step : Algorithm) (stateValues : List Result)
    : EvalM (ValEnv × CountedParamEnv) := do
  if Algorithm.requiresPatternBinding step then
    bindStructuredLoopState step stateValues
  else
    match Algorithm.collectingParam? step with
    | none => do
        let argEnv <- bindParams (Algorithm.params step) stateValues
        pure (argEnv, [])
    | some _ => do
        let signature := Algorithm.callableSignature "loop step" step
        let bindings <-
          match bindCallableArguments signature stateValues (fun required actual => Error.arityMismatch required actual) with
          | .ok value => pure value
          | .error err => .error err
        match bindings.collectingName? with
        | none => .error Error.badArity
        | some collectingName =>
            -- Collecting binding COLLECTS (same rule as the pattern binders): the
            -- assigned state slots become one list value.
            let captured := collectSegment bindings.collectingItems
            let argEnv <- bindLoopStepValueEnv signature.parameters bindings.normalBindings collectingName captured
            let collectingBinding := (collectingName, (captured, 1))
            pure (argEnv, [collectingBinding])

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
mutual

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
      (Loop-step state, which must keep a collecting `*history` structured, goes
      through `evalAlgOutputSlots` with its explicit preserve flag, not here.)

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

  partial def evalAlgOutputSlots (a : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      (preserveSequenceSpreadExpressionBoundaries : Bool := false)
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
        let rec collect : List Expr -> List Result -> EvalM (List Result)
          | [], acc => pure acc.reverse
          | e :: rest, acc => do
              let out <- evalCounted e pushedCtx env
              let values :=
                if preserveSequenceSpreadExpressionBoundaries then
                  match e with
                  | .sequenceSpread _ => if out.snd = 0 then [] else [out.fst]
                  | _ =>
                      if out.snd = 0 then [out.fst] else countedTopLevelValues out
                else
                  match e with
                  | .sequenceSpread _ => countedTopLevelValues out
                  | _ =>
                      if out.snd = 0 then [out.fst] else countedTopLevelValues out
              collect rest (values.reverse ++ acc)
        collect (Algorithm.output a) []

  partial def runStepSlots (step : Algorithm) (ctx : EvalCtx) (env : ValEnv)
      (stateSlots : List Result) : EvalM (List Result) := do
    let (argEnv, countedParamEnv) <- bindLoopStepState step stateSlots
    let stepCtx <- ctx.bindParameters (Algorithm.params step) [] countedParamEnv
    evalAlgOutputSlots step stepCtx (argEnv ++ env) (Algorithm.requiresPatternBinding step)

  /-- Initial loop state preserves explicit argument boundaries: `repeat(Step, 3, a, b)`
      starts with two slots, while `repeat(Step, 3, Pair)` starts with one slot even when
      `Pair` evaluates to multiple values. Step outputs define later state slots; capture a
      step result to keep one structured slot across iterations. -/
  partial def evalInitialLoopStateSlots (inits : List ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM (List Result) :=
    inits.mapM (fun init => evalArgumentValue init ctx env)

  /-- Evaluate a higher-order sequence callback on one collected iteration
      item. -/
  partial def evalSequenceCallbackCall (callee : Algorithm) (item : CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM Result :=
    evalResolvedCallbackCall callee [countedSequenceCallbackItem item] ctx env calleeName

  /-- Counted variant of `evalSequenceCallbackCall` used by `map`. -/
  partial def evalSequenceCallbackCallCounted (callee : Algorithm) (item : CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult :=
    evalResolvedCallbackCallCounted callee [countedSequenceCallbackItem item] ctx env calleeName

  /-- Evaluate an algorithm's output expressions once, retaining both the combined counted
      value and the explicit evaluated output-slot view. The slot list is the accumulator
      from the same left-to-right pass that constructs the combined value; it never reopens
      or decomposes that value after singleton erasure and never evaluates an expression twice.

      A parenthesized sequence-value expression such as `(a, b)` counts as one emitted value,
      while multiple top-level output expressions `a, b` count as two. `reduce`
      uses this to distinguish sequence-value accumulator values from multi-output
      step results. -/
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
    | _ =>
      if (Algorithm.parameterPatterns a).isEmpty then
        evalAlgOutputCounted a ctx env
      else do
        let bindings <- bindParameterPatternList (Algorithm.parameterPatterns a) [] true
        let names := Algorithm.params a
        let newCtx <- ctx.bindParameters names bindings.algEnv bindings.countedParamEnv
        let shadowedEnv := ValEnv.shadow env names
        evalAlgOutputCounted a newCtx (bindings.argEnv ++ shadowedEnv)

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
      evaluates through the shared demand funnel. Laziness is untouched: a slot is
      demanded only when the builtin selects it. C#: `EvalResolvedArgumentCounted`. -/
  partial def evalArgumentValueCounted (arg : ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
    match zeroArgumentDemandError? arg.source? arg.algorithm with
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
      let key := zeroArgPropertyCacheKey accessKind owner binding ctx env
      let state <- get
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

  partial def evalConditionalCallbackCallCounted (callee : Algorithm)
      (args : List CountedResult)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult := do
    if callee.hasDuplicateBranchPatterns then
      .error Error.duplicateBranchPattern
    else
      match matchCountedCallBranches (Algorithm.branches callee) args with
      | some (branch, bindings) =>
          let names := bindings.map Prod.fst
          let newCtx <- (EvalCtx.push callee ctx).bindParameters names [] bindings
          let newEnv := (bindings.map fun | (name, value) => (name, value.fst)) ++ env
          let wiredBody <- wireSelectedBranchBody callee branch.body names newCtx newEnv
          evalAlgOutputCounted wiredBody newCtx newEnv
      | none =>
          .error (Error.noMatchingBranch calleeName)

  /-- Bind pre-evaluated callback arguments to a user algorithm through the ONE
      ordinary counted binder and evaluate its output. THE CALLBACK LAW
      (September 2026): every value a callback operation supplies is ONE
      ordinary argument, bound exactly as the ordinary call with the same
      supply — `map(xs, F)` calls `F(E)` for each element `E`, `reduce` calls
      `R(E, Acc)` — so fixed parameters take their values unchanged, a
      collector collects the supplied values exactly, and only the callee's
      explicit sequence-value patterns open a value. There is no callback row
      convention: `map([(1, 2)], Add)` with `Add(x, y)` is the ordinary arity
      error of `Add((1, 2))`, while `AddPair((x, y))` opens the element
      explicitly. -/
  partial def evalUserCallbackCallCounted (callee : Algorithm)
      (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    if (Algorithm.output callee).isEmpty then
      .error Error.missingOutput
    else do
      let bindings <- bindCountedParameterPatternList (Algorithm.parameterPatterns callee) args
      let names := bindings.countedParamEnv.map Prod.fst
      let newCtx <- ctx.bindParameters names [] bindings.countedParamEnv
      evalAlgOutputCounted callee newCtx env

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
    | .builtin b =>
        applyBuiltinCounted b (args.map fun arg => { algorithm := countedArgAlgorithm arg }) ctx env
    | .conditional _ _ _ _ =>
        match flatBinderUserEquivalent? callee with
        | some simple => evalUserCallbackCallCounted simple args ctx env
        | none =>
            evalConditionalCallbackCallCounted callee args ctx env calleeName
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
      accumulator is reified at the value boundary and every step must return
      exactly one value (`expectSingleAccumulator`). -/
  partial def evalSequenceReduceStepCounted (callee : Algorithm)
      (element : CountedResult) (accumulator : Result)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM CountedResult :=
    evalResolvedCallbackCallCounted callee
      [ countedSequenceCallbackItem element
      , (accumulator, Result.valueCount accumulator)
      ]
      ctx env calleeName

    partial def collectSequenceCallableCallItems
      (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
      (valueSlots : SequenceBuiltinMetadata)
      : EvalM (List CallableCallItem) := do
    let isValueSlot (slot : Nat) : Bool :=
      slot == 0 || match valueSlots.suffixArgs[slot - 1]? with
        | some descriptor => descriptor.kind != .algorithm
        | none => false
    let rec loop : List ResolvedArgumentAlgorithm -> Nat -> EvalM (List CallableCallItem)
      | [], _ => pure []
      | arg :: rest, slot => do
          let alg := arg.algorithm
          -- A callback argument (a callable that declares parameters) is applied
          -- per element by the consuming sequence builtin, never used as a value here.
          -- Its parameters are unbound at this collection point, so evaluating its body
          -- standalone would resolve those parameter names against the surrounding scope;
          -- when a sibling argument shares a parameter name and was deferred as a
          -- self-referential thunk, that stray lookup re-enters the same builtin call and
          -- never settles. Keep the algorithm unevaluated so it is applied with bound
          -- parameters later; only value-shaped arguments are materialized eagerly.
          let callableShaped := match alg with
            | .conditional _ _ _ _ => true
            | _ => !(Algorithm.parameterPatterns alg).isEmpty
          let head <-
            if callableShaped then do
              let item : CallableCallItem :=
                { value? := none, algorithm? := some alg, error? := none, skipMissingValue := false, source? := arg.source? }
              -- The descriptor binds this slot's role before later argument effects.
              -- Only VALUE positions demand newly eligible callables; callbacks do not.
              let item <- if isValueSlot slot then demandSequenceBuiltinCallItemValue item ctx env else pure item
              pure [item]
            else do
              match <- evalAttempt (evalZeroArgumentDemandOutputCounted alg ctx env) with
              | .ok counted =>
                  if arg.spreadsSequence then
                    pure ((countedTopLevelValues counted).map (fun value =>
                      { value? := some value, algorithm? := some alg, error? := none, skipMissingValue := false }))
                  else
                    pure [{ value? := some counted.fst, algorithm? := some alg, error? := none, skipMissingValue := false, source? := arg.source?, callable? := arg.callable? }]
              | .error err =>
                  pure [{ value? := none, algorithm? := some alg, error? := some err, skipMissingValue := false, source? := arg.source?, callable? := arg.callable? }]
          let tail <- loop rest (slot + head.length)
          pure (head ++ tail)
    loop args 0


  /-- Demand ONE collection-builtin call item that binding has placed in a VALUE
      position. Call-item assembly leaves a callable-shaped CALLBACK item
      unevaluated (a CALLBACK slot must receive the algorithm, never a value), so
      the demand happens HERE, once the descriptor has decided the slot is a
      value: an item the ONE law accepts (`acceptsZeroArgumentValueDemand` — a
      collecting-only signature such as `Only` alongside every zero-parameter
      property) is evaluated through the shared demand funnel, and every other
      item is returned untouched for `sequenceBuiltinValueDemandError?` to
      report. An item that was already evaluated, or whose evaluation already
      failed, is never re-entered. C#: `DemandSequenceBuiltinCallItemValue`. -/
  partial def demandSequenceBuiltinCallItemValue (item : CallableCallItem)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CallableCallItem := do
    match item.value?, item.error?, item.algorithm? with
    | none, none, some alg =>
        if acceptsZeroArgumentValueDemand alg then
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
      structured element or accumulator. The step must
      return exactly one accumulator value: one atom, one string, one sequence
      value, or one exact list value is valid (the empty list `[]` counts as
      one value), while empty-sequence and multi-output results are rejected.

      The initial accumulator expression occupies one written accumulator
      slot (reified via `reCountValueBoundary` before reduction), so empty
      collections return the initial accumulator as ONE value. -/
  partial def evalReduceCounted (collection : List CountedResult)
      (stepAlg : Algorithm) (initial : ResolvedArgumentAlgorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    -- The initial accumulator is a VALUE slot: a parameterized algorithm there is
    -- rejected from its signature at this boundary — never by entering its body
    -- and reinterpreting the failure — with reduce's dedicated hint, the same
    -- rejection the dotted `Values.reduce(Add)` form reports for a visibly
    -- parameterized reducer.
    let initOut <-
      match zeroArgumentDemandError? initial.source? initial.algorithm with
      | some err =>
          if (Algorithm.params initial.algorithm).isEmpty then .error err
          else .error reduceInitialAccumulatorRequiresValueError
      | none => evalZeroArgumentDemandOutputCounted initial.algorithm ctx env
    let rec reduceLoop : List CountedResult -> CountedResult -> EvalM CountedResult
      | [], acc => pure acc
      | item :: rest, (accValue, _) => do
          let stepOut <- withCtx
            "while evaluating reduce step (reduce passes each iterated collection item as collected and the accumulator as one value; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)" <|
            evalSequenceReduceStepCounted stepAlg item accValue ctx env "reduce step"
          let next <- expectSingleAccumulator stepOut
          reduceLoop rest (next, 1)
    -- The initial accumulator expression occupies ONE written accumulator
    -- slot: its result is reified as one persistent value at the ordinary
    -- value boundary (`reCountValueBoundary`) BEFORE reduction begins, so an
    -- initial expression that emitted multiple items cannot leak that supply
    -- through the empty-collection return.
    reduceLoop collection (reCountValueBoundary initOut)

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
      It must return exactly one mapped element:
      one atom, one sequence value, or one exact list value is valid, while
      empty and multi-output results are rejected.

      Sequence-value and list-value mapped elements are accepted as single
      output elements. Each captured callback result becomes one element of
      the list result (mapped elements are never flattened
      into the outer list), empty collections yield `[]`, and the output
      preserves the original element order and element count. -/
  partial def evalMapCounted (collection : List CountedResult) (transformAlg : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let rec mapLoop : List CountedResult -> EvalM (List Result)
      | [] => pure []
      | item :: rest => do
          let mappedOut <- withCtx
            "while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)" <|
            evalSequenceCallbackCallCounted transformAlg item ctx env "map transform"
          let mapped <- expectSingleMappedElement mappedOut
          let restMapped <- mapLoop rest
          pure (mapped :: restMapped)
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
              let predicateAlg <-
                expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              evalFilterCounted bound.iterationItems predicateAlg ctx env
        | .mapBuiltin =>
            withPreparedSuffixArgs fun preparedSuffixArgs => do
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
              let stepAlg <-
                expectPreparedSequenceBuiltinAlgorithmSuffixArg b metadata.suffixArgs preparedSuffixArgs 0
              let initialAlg <-
                expectPreparedSequenceBuiltinAlgorithmSuffixArgFull b metadata.suffixArgs preparedSuffixArgs 1
              evalReduceCounted bound.iterationItems stepAlg initialAlg ctx env
        | _ =>
            .error (builtinArityError b args.length)

  /-- Builtin application with counted output shape.
      Used by `reduce` to validate that the step emits exactly one accumulator
      value without flattening sequence values.
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
            -- Unlike `while`/`repeat`, which preserve multi-slot loop state, `if`
            -- re-counts the chosen branch value via `Result.valueCount`.
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
            let initialSlots <- evalInitialLoopStateSlots initAlgs ctx env
            let rec loop (stateSlots : List Result) : EvalM (List Result) := do
              let outputSlots <- runStepSlots step.invoked ctx env stateSlots
              let (nextSlots, cont) <- splitContSlots outputSlots
              -- `false` stops (the current state is returned; the producing
              -- iteration's next state is never committed), `true` continues.
              if cont then loop nextSlots else pure stateSlots
            let finalSlots <- loop initialSlots
            let final := loopStateResult finalSlots
            pure (final, finalSlots.length)

        | .repeatBuiltin, step :: countAlg :: initAlgs => do
            if initAlgs.isEmpty then
              .error (builtinArityError b args.length)
            else
            let cr <- evalArgumentValue countAlg ctx env
            let n <- expectInt cr
            if n < 0 then
              .error (Error.illegalInEval "Repeat count must be >= 0")
            else
              let initialSlots <- evalInitialLoopStateSlots initAlgs ctx env
              let rec repeatLoop (k : Int) (stateSlots : List Result) : EvalM (List Result) :=
                if k = 0 then pure stateSlots else do
                  let outputSlots <- runStepSlots step.invoked ctx env stateSlots
                  repeatLoop (k-1) outputSlots
              let finalSlots <- repeatLoop n initialSlots
              let final := loopStateResult finalSlots
              pure (final, finalSlots.length)

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
            let expanded := (countedTopLevelValues counted).map
              (fun value => ({ algorithm := countedArgAlgorithm (value, 1) } : ResolvedArgumentAlgorithm))
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

  /-- Shared call argument-slot assembly used by EVERY callable shape (flat
      fixed, flat/mixed variadic, patterned, and multi-clause conditional):
      each written argument slot is evaluated exactly once, left to right; every non-spread slot is
      reified as exactly ONE argument value (with its dual algorithm view
      where resolvable) whatever that value is — a scalar, a sequence, a list,
      `()`, or `[]` — and every explicit spread slot is expanded by exactly one
      value boundary into ordinary argument slots. VALUES STAY VALUES: this is
      the ONLY place a call turns one value into several supplied items, and it
      does so only for a written spread. The final argument supply is formed
      BEFORE any arity checking, clause selection, conditional dispatch, or
      pattern binding, and no binder reinterprets an item afterwards — the
      callee's internal representation never influences the meaning of
      caller-side spread.
      DOT-CALL PASSES A VALUE: an extension dot-call receiver reaches this
      assembly as the ordinary FIRST slot of `F(R, args)`
      (`prepareLexicalDotCallArgs`) — one reified value like any written
      argument, never a supply of its own; only a spread receiver `R*` (the
      fluent form lowers to `F(R*, args)`) opens one boundary, exactly as a
      written spread slot does.
      Every non-spread slot is evaluated at its VALUE boundary through the ONE
      `evalCounted` (a capture, a block, a name, a call, and a literal alike):
      argument slots evaluate directly in the CALLER's context — the bundle
      owns no scope, so there is no argument-level lexical frame — and no
      callee shape receives a second, written-slot view of a slot (PARENTHESES
      GROUP SYNTAX, September 2026: a patterned callee opens the slot's value
      in `bindParameterPattern`, never the rows a group was written with).
      C#: `BuildCallArgumentInputs`. -/
  partial def collectVariadicCallItems (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM (List ParameterPatternInput) := do
    let maybeAlgs <- tryResolveArgAlgs args ctx
    let rec appendCounted (counted : CountedResult) (maybeAlg : Option Algorithm) (expand : Bool)
        (acc : List ParameterPatternInput) : List ParameterPatternInput :=
      if expand then
        -- Explicit spread supplies the operand's items, one level.
        let expanded := (countedTopLevelValues counted).map (fun value =>
          { value? := some value : ParameterPatternInput })
        expanded.reverse ++ acc
      else
        -- A non-spread slot is exactly ONE item: its value, never opened.
        { value? := some counted.fst,
          algorithm? := maybeAlg : ParameterPatternInput } :: acc
    let shouldExpand (e : Expr) : Bool :=
      match e with
      | .sequenceSpread _ => true
      | _ => false
    let rec loop : List Expr -> List (Option Algorithm) -> List ParameterPatternInput
        -> EvalM (List ParameterPatternInput)
      | [], _, acc => pure acc.reverse
      | e :: es, ma :: mas, acc => do
          let expand := shouldExpand e
          match <- evalAttempt (evalCounted e ctx env) with
          | .ok counted =>
            loop es mas (appendCounted counted ma expand acc)
          | .error err =>
            match ma with
            | some alg => loop es mas ({ algorithm? := some alg, error? := some err : ParameterPatternInput } :: acc)
            | none => .error err
      | e :: es, [], acc => do
          let expand := shouldExpand e
          match <- evalAttempt (evalCounted e ctx env) with
          | .ok counted =>
            loop es [] (appendCounted counted none expand acc)
          | .error err => .error err
    loop args maybeAlgs []

  /-- Bind a call to an item-supply parameter list (any top-level variadic).
      The call argument supply is already the receiver for parameter binding: a
      plain sequence-valued argument contributes one item, while explicit spread
      contributes the operand's items. -/
  partial def bindDeconstructionUserCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM (ValEnv × CountedParamEnv × AlgEnv) := do
    let inputs <- collectVariadicCallItems args ctx env
    let bindings <- bindParameterPatternList (Algorithm.parameterPatterns callee) inputs true
    pure (bindings.argEnv, bindings.countedParamEnv, bindings.algEnv)

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

  partial def bindPatternedUserCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM (ValEnv × CountedParamEnv × AlgEnv) := do
    let inputs <- collectVariadicCallItems args ctx env
    let bindings <- bindParameterPatternList (Algorithm.parameterPatterns callee) inputs true
    pure (bindings.argEnv, bindings.countedParamEnv, bindings.algEnv)

  partial def bindFlatFixedUserCall (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM (ValEnv × AlgEnv) := do
    let params := Algorithm.params callee
    -- Shared argument-slot assembly (spread expansion happens there, before
    -- any arity checking).
    let items <- collectVariadicCallItems args ctx env
    let slots := items.map (fun item =>
      { value? := item.value?, algorithm? := item.algorithm?, error? := item.error? : FlatFixedCallSlot })
    if slots.length > params.length then
      .error (Error.arityMismatch params.length slots.length)
    else
      let rec collect : List Ident -> List FlatFixedCallSlot -> EvalM (List Ident × List Result × AlgEnv)
        | [], _ => pure ([], [], [])
        | p :: ps, [] => do
            let (valueParams, values, algBindings) <- collect ps []
            pure (p :: valueParams, values, algBindings)
        | p :: ps, slot :: rest => do
            let (valueParams, values, algBindings) <- collect ps rest
            let algBindings :=
              match slot.algorithm? with
              | some alg => (p, alg) :: algBindings
              | none => algBindings
            match slot.value? with
            | some value => pure (p :: valueParams, value :: values, algBindings)
            | none =>
                match slot.algorithm? with
                | some _ => pure (valueParams, values, algBindings)
                | none => .error (slot.error?.getD Error.badArity)
      let (valueParams, values, algBindings) <- collect params slots
      let argEnv <- bindParams valueParams values
      pure (argEnv, algBindings)

  /-- Counted user-defined call evaluation — the CANONICAL user-call
      implementation (`evalUserCall` is its value projection).

      Shared user-defined call binding logic. Preserves the eager value ABI
      while layering AlgEnv for higher-order arguments. Each original argument
      expression is interpreted independently in two ways:
      - structural algorithm resolution for AlgEnv
      - ordinary eager value evaluation for ValEnv

      If both succeed, the parameter gets both meanings. If only one succeeds,
      only that view is bound. A parameter bound only through `AlgEnv` still
      SHADOWS the caller's inherited value environment (`ValEnv.shadow`, the
      value-tier counterpart of `CountedParamEnv.shadow`), so a value-position
      read of that parameter reaches its algorithm binding — the ordinary
      zero-argument value demand or its arity error — instead of silently
      answering with a same-named caller value. Symmetrically, a parameter
      bound only through `ValEnv` SHADOWS the caller's inherited algorithm
      environment (`AlgEnv.shadow`, applied together with the counted tier by
      `EvalCtx.bindParameters`), so a call-position read of that parameter
      fails as not-callable instead of invoking a same-named caller callable:
      the callee's parameter list owns its names on every channel. If both
      fail, the ordinary
      eager-evaluation error is propagated. Every `algorithmExpr` contributes
      its contained algorithm to the `AlgEnv` side regardless of declaration/output count;
      a `capture` contributes only its fresh zero-parameter value thunk and
      never exposes contained algorithm identity.

      Flat fixed calls bind call-site structure: each comma argument is one
      argument expression, while a bare `sequenceSpread` expression explicitly
      contributes its spread top-level items. Multi-output values from ordinary
      expressions, including `.atoms`, remain one argument expression. Earlier
      explicit argument positions stay distinct on the eager value side even if
      some later arguments bind only through `AlgEnv`.

      A user/property call is a value boundary: the public result preserves the
      structural value while re-counting the emitted arity to
      `Result.valueCount` (via `reCountValueBoundary`). A multi-output body
      therefore becomes one sequence value (count 1); only a caller-site spread
      `value*` re-spreads it. -/
  partial def evalUserCallCounted (callee : Algorithm) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM CountedResult := do
    if (Algorithm.output callee).isEmpty then
      .error Error.missingOutput
    else if Algorithm.requiresPatternBinding callee then do
          let (argEnv, countedParamEnv, algBindings) <-
            bindPatternedUserCall callee args ctx env
          let shadowedEnv := ValEnv.shadow env (Algorithm.params callee)
          let newCtx <- ctx.bindParameters (Algorithm.params callee) algBindings countedParamEnv
          reCountValueBoundary <$> evalAlgOutputCounted callee newCtx (argEnv ++ shadowedEnv)
    else match Algorithm.collectingParam? callee with
      | some _ =>
          -- Any top-level variadic binds the supplied call argument supply.
          let (argEnv, countedParamEnv, algBindings) <-
            bindDeconstructionUserCall callee args ctx env
          let shadowedEnv := ValEnv.shadow env (Algorithm.params callee)
          let newCtx <- ctx.bindParameters (Algorithm.params callee) algBindings countedParamEnv
          reCountValueBoundary <$> evalAlgOutputCounted callee newCtx (argEnv ++ shadowedEnv)
      | none =>
      do
        let (argEnv, algBindings) <- bindFlatFixedUserCall callee args ctx env
        let newCtx <- ctx.bindParameters (Algorithm.params callee) algBindings []
        let shadowedEnv := ValEnv.shadow env (Algorithm.params callee)
        reCountValueBoundary <$> evalAlgOutputCounted callee newCtx (argEnv ++ shadowedEnv)

  /-- Assemble the evaluated argument values for a conditional (multi-clause)
      call through the shared call argument pipeline
      (`collectVariadicCallItems`): non-spread slots reify as one value each
      and explicit spread expands by one value boundary, exactly as for every
      other callable shape. Clause matching needs plain values, so an
      algorithm-only argument surfaces its value-evaluation error.
      C#: `EvalConditionalCallArguments`. -/
  partial def evalConditionalCallArguments (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM (List Result) := do
    let items <- collectVariadicCallItems args ctx env
    items.mapM (fun item =>
      match item.value? with
      | some value => pure value
      | none => .error (item.error?.getD Error.badArity))

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
    let argResults <- evalConditionalCallArguments args ctx env
    if callee.hasDuplicateBranchPatterns then
      .error Error.duplicateBranchPattern
    else
      match matchCallBranches (Algorithm.branches callee) argResults with
      | some (branch, bindings) =>
          let names := bindings.map Prod.fst
          let newCtx <- (EvalCtx.push callee ctx).bindParameters names [] []
          let wiredBody <- wireSelectedBranchBody callee branch.body names newCtx (bindings ++ env)
          reCountValueBoundary <$> evalAlgOutputCounted wiredBody newCtx (bindings ++ env)
      | none =>
          .error (Error.noMatchingBranch calleeName)

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
      let argAlgs <- resolveArgAlgsWithSequenceSpread args ctx env
      applyBuiltinCountedResolved b argAlgs ctx env
    | .conditional _ _ _ _ =>
      match flatBinderUserEquivalent? callee with
      | some simple => evalUserCallCounted simple args ctx env
      | none => evalConditionalCallCounted callee args ctx env calleeName
    | _ => evalUserCallCounted callee args ctx env

  /-- Context-aware counted call evaluation for expression position — the
      CANONICAL expression-position call dispatch (`evalCallExpr` is its value
      projection); attaches `CtxMsg.call` to resolution and dispatch errors. -/
  partial def evalCallCountedExpr (f : Expr) (args : OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    let callee <- withCtx (CtxMsg.call f) <| resolveAlg f ctx
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
      list is assembled exactly like every call's (each written slot evaluated
      once, left to right, spreads opened) and then rejected by arity — the
      same outcome as `Obj.V(1)` for a declared zero-parameter member — so a
      written bundle is never silently dropped; an EMPTY written list
      (`x.string()`) stays the intrinsic, as `A()` stays a call of `A`.
      C#: `RejectDotStringIntrinsicArguments`. -/
  partial def rejectDotStringIntrinsicArguments (argsOpt : Option OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Unit := do
    match argsOpt with
    | none => pure ()
    | some args =>
      let items <- collectVariadicCallItems args ctx env
      if items.length = 0 then pure ()
      else .error (Error.arityMismatch 0 items.length)

  /-- Evaluate dotCall: a.f or a.f(args). The member result is a value boundary:
      structural zero-arg property access and collection builtins re-count to
      `Result.valueCount`, and user/lexical member calls re-count via
      `evalUserCallCounted`, so a multi-output member becomes one sequence value
      (count 1) and only a caller-site spread `value*` re-spreads
      it. This is the single owner
      of dot-call dispatch; `evalDotCall` is its Result projection.
      Smart dispatch:
      - Receiver resolution through `resolveDotReceiver`: a chained receiver
        navigates its declared structural members, so the property-first
        rule below holds at every level of `A.B.C.D`
      - "string" value intrinsic → evaluate target, convert numeric result to string
      - Structural property found (navigation-only):
        - If no args and 0-param → value access
        - If no args and has params → arity mismatch error
        - If args → direct argument binding (no receiver injection)
      - No property → extension fallback (`callLexicalWithReceiverCounted`):
        DOT-CALL PASSES A VALUE — `a.f(args)` is exactly the call
        `f(a, args)`, the receiver being the ordinary first argument slot
        (never a supply of its own; only the spread receiver `a*.f`, lowered
        to `f(a*)`, opens a boundary). Dot resolution therefore has three
        classes — structural member access, the intrinsic `.string`, and
        extension fallback — and only the third one injects the receiver.

      When receiver resolution returns notAnAlgorithm (e.g. numeric literal
      target), value-based intrinsics are checked before lexical fallback.

      (The C# front end consumes the Grace annotation in `a~.f` / `a.~f`, so
      Lean receives the same dotMember and the same structural-first dispatch
      as for ordinary `a.f`.)

      Optimization note for executable evaluators: repeated references to the
      same eligible structural or lexical property may be reused within one
      top-level run when the property is fully wired and requires no further
      arguments in the current evaluation context. This is intentionally local
      to one run and must not be interpreted as memoizing arbitrary calls or as
      changing the semantic behavior of dotCall itself. -/
  partial def evalDotCallCounted (target : Expr) (name : Ident)
      (fallback : Expr) (argsOpt : Option OutputBundle)
      (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
    match <- evalAttempt (resolveDotReceiver target ctx) with
    | .ok targetAlg =>
      if name = "string" then do
        -- The intrinsic is a ZERO-parameter member: a written argument list is
        -- assembled like every call's (each slot evaluated once, spreads opened)
        -- and then rejected by arity exactly as `Obj.V(1)` is for a declared
        -- zero-parameter member; `x.string()` (an empty list) stays the intrinsic.
        -- C#: `RejectDotStringIntrinsicArguments`.
        rejectDotStringIntrinsicArguments argsOpt ctx env
        -- The receiver is demanded for its VALUE with zero arguments, so the ONE
        -- zero-argument demand law decides from the resolved receiver's
        -- signature before its body is entered: `Inc.string` with `Inc(x)` is
        -- the property arity error, a navigated parameterized member the bare
        -- one, and a written parameterized block `unresolvedImplicitParams`.
        -- C#: `EvalDotStringReceiverAlgOutput`.
        match zeroArgumentDemandError? (some target) targetAlg with
        | some err => .error err
        | none => pure ()
        let val <- evalZeroArgumentDemandOutput targetAlg ctx env
        let out <- resultToString val
        pure (out, Result.valueCount out)
      else
        match Algorithm.lookupPropDefAny? targetAlg name with
        | some p =>
            -- Selection is by declaration (structural access ignores `public`); the
            -- member's accessibility from THIS site is decided afterwards.
            if !(memberAccessible? ctx targetAlg p) then
              .error (Error.localOnlyProperty (openExprName target) name p.exposure)
            else
            let wired := childOfInContext targetAlg p.alg ctx
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
            else
              callLexicalWithReceiverCounted name target fallback argsOpt ctx env
    | .error (.notAnAlgorithm _) =>
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
    | .algorithmExpr a =>
        let wired := wireToCaller ctx a
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
      Boolean operand (a number has no truth value); `-` is numeric negation
      and rejects a Boolean operand as a value-kind error, keeping the
      established string rejection and the numeric-conversion failure for
      every other non-numeric operand — the empty sequence value follows the
      same validation as other non-scalar values (SYN-01). Owned here so
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
        match r with
        | .str _ => .error (Error.typeMismatch "Unary operator is not supported for strings")
        | .bool _ => .error (Error.typeMismatch
            s!"operator `-` expects a numeric scalar operand, but the operand was {operandDescription r}")
        | _ => do
          let v <- expectInt r
          pure (Result.atom (-v), 1)

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
        match ctx.countedParamEnv.lookup x with
        | some counted => pure counted
        | none =>
            match env.lookup x with
            | some v => pure (v, Result.valueCount v)
            | none =>
                match ctx.algEnv.lookup x with
                | some alg =>
                    match zeroArgumentDemandError? (some e) alg with
                    | some err => .error err
                    | none => do
                        let value <- evalZeroArgumentDemandOutput alg ctx env
                        pure (value, Result.valueCount value)
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
        let wired := wireToCaller ctx a
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
    to nothing — an unknown head, a missing member, a non-public path step — as a
    static diagnostic (C# `DiagnosticCode.UnresolvedOpenTarget`), so in an
    accepted program this probe only ever sees resolvable targets, and its
    `.error` arm reports genuine lookup failures such as an ambiguous open.

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

    `parameters` are the parameter BINDINGS the level owns — an algorithm's
    written and inferred parameters (including parameters later lifted through
    implicit forwarding), or a conditional branch body's pattern binders.
    The chain contains COMPLETE declarations: selection is applied after signature
    completion, retaining the discovered parameter lists, pattern shapes, and Grace
    order. A changed selection requires rebuilding forwarding and closed-input
    diagnostics from the written expressions, not inferring additional names from
    a newly available receiver fallback. `properties` are the property names the level declares. Both are
    OWNED declarations; `opens` are deliberately absent, because they are not
    owned by the level and keep the separate later fallback policy of
    `lookupLexicalProperty`.

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
  deriving Repr, DecidableEq

/-- Surface declaration validity, checked after parameter-signature completion and
    before evaluation. Each property whose name is bound by this or an enclosing owner is a
    declaration error, regardless of visibility or reference order. Pattern binders
    belong to their branch body. Open targets are not declarations and never conflict,
    but their HEAD name obeys the same owner chain (`elaborateOpenHead`). The surface
    layer reports each written conflicting declaration at its source name.
    C#: ParameterPropertyCollisionValidator. This is a front-end validity boundary;
    raw/recovery AST evaluation and lookup do not substitute for this check. -/
def conflictingOwnedNames (owner : OwnerLevel) (ancestors : List OwnerLevel := []) : List Ident :=
  owner.properties.filter fun name =>
    owner.parameters.contains name || ancestors.any (fun outer => outer.parameters.contains name)

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
    parameter — written, inferred, lifted, collecting, grouped, a branch
    binder, or any of these captured from an enclosing owner — that parameter
    owns the name and the head elaborates to `.param`, exactly as every other
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

   When a property body contains a bare reference to a sibling property that has
   parameters, the surface layer rewrites that reference into an explicit call,
   passing the sibling's parameter-pattern captures as arguments (lifted into
   the referencing property's own parameter-pattern list when they are not
   already provided by the caller).

   Example:
     Surface:   `{ A = x + 1  B = A * 2 }`
     After detection: A.params = [x], B.params = []
     After resolution: B.params = [x], B.output = [Call(A, [Param(x)]) * 2]

   Recursive parameter patterns are preserved by this surface pass: lifting
   `*items`, `(*items)`, or `((*history), previous)` keeps that shape
   instead of reconstructing ordinary capture parameters from flattened names.
   A narrow forwarding rule also permits a bare helper reference with one
   forwardable variadic supply to use a containing algorithm's single
   top-level variadic supply by shape rather than by capture-name equality.
   This is not a general positional parameter-matching rule.

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

   Cycles (mutually recursive siblings) are not excluded from lifting: the
   acyclic prefix is processed in topological order and the members of every
   cycle are then processed in DECLARATION order, each seeing the signatures
   completed so far (the C# `PropertyDependencyGraph.TopologicalOrder`). This
   is the one documented way two reaches of a node can observe different
   sibling signatures (the "sibling CYCLE" exception of the shared-DAG
   guarantee in `docs/design/language-rules/evaluator-and-hosting.md`). -/

-- Surface syntax support: while/repeat initial-state boundaries
--------------------------------------------------------------------------------

/- **Ordinary parentheses** construct sequence values.  There is no special
   "double-parens" syntax.  `((expr))` in any position is nested sequence-value
   construction.  `f((a + b) mod 2, c)` parses normally as two arguments.

   **while/repeat initial state** preserves explicit argument boundaries.
   The evaluator accepts variable arity for these builtins:

     while(step, s1, s2, ..., sk)         -- k ≥ 1
     repeat(step, count, s1, s2, ..., sk) -- k ≥ 1

   Each explicit init argument is evaluated independently and becomes exactly
   one initial state slot.  Therefore `repeat(Step, 3, a, b)` starts with two
   slots, while `repeat(Step, 3, Pair)` starts with one slot even if `Pair`
   evaluates to multiple values.  Use explicit selections such as `Pair:0,
   Pair:1` when the intended initial state is two slots.

   DotCall lexical fallback (`Step.repeat(...)` / `Step.while(...)`) injects
   the receiver as the step argument and keeps the remaining explicit args in
   the same boundary-preserving form after structural property lookup.

   Step outputs still define the state slots for the next iteration by emitted
   top-level output boundaries.  To keep one structured slot across iterations,
   return a sequence-value step result; multi-output steps intentionally
   become many next-state slots.

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
   3. `tryResolveArgAlgs` calls `resolveAlg(Expr.algorithmExpr inlineAlg)` on
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
end

end KatLang
