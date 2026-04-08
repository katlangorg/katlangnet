-- KatLang v0.8.13 (core AST + semantics + while/repeat init lowering + higher-order alg params + conditional algorithms + first-class strings)
-- Core semantics are authoritative. Surface syntax handled externally except
-- where noted (implicit parameter detection, while/repeat init lowering).
-- Load elaboration is handled entirely in the front-end / elaboration layer;
-- the core AST never contains load nodes (see load elaboration section below).
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
--     - combine:        `open A; B`            → Combine(Resolve("A"), Resolve("B"))
--     - inline block:   `open (public X = 1)`  → Block(...)
--
--   Exact-syntax sugar (parser-only, not in core model):
--     - `open 'url'` desugars to `open load('url')` before elaboration.
--     Raw string literals do NOT survive into the canonical open list.
--
-- Conditional branch syntax (parser-only, not in core model):
--   Conditional algorithm branches use clause-style syntax:
--     `Name(pattern) = body`
--   This form is recognized only in definition position.
--   In expression position, `Name(args)` remains an ordinary call.
--   On the left-hand side of `=` in definition context, `Name(...)` is not a
--   call expression — it is pattern syntax for a conditional algorithm branch.
--   All clause-style definitions elaborate to the same CondBranch semantic representation.
--
-- Explicit output syntax (exact-syntax sugar, parser-only):
--   `Output = expr` inside an algorithm body is special output-definition syntax.
--   It is NOT a normal property assignment — it lowers to the Algorithm's `output`
--   field (the same representation used by implicit trailing output).
--
--   Equivalence:
--     Implicit:  `A = 6\n A`           → Algorithm.mk ... output=[Resolve("A")]
--     Explicit:  `A = 6\n Output = A`  → Algorithm.mk ... output=[Resolve("A")]
--
--   Rules:
--     - Each algorithm may define output at most once.
--     - The user may choose either implicit output OR explicit `Output = expr`,
--       but not both in the same algorithm.
--     - `Output = expr` may appear anywhere in the property list (not only at end).
--     - The name `Output` in assignment position is reserved for this syntax;
--       users cannot define a normal property named `Output`.
--     - `Output` can still be used as a free identifier / parameter name in
--       expressions (only the `Output = ...` assignment form is special).
--
--   Semantic rules (enforced by evaluator, not parser):
--     - Opens provide PUBLIC properties only (lookupOpens filters by isPublic).
--     - Strict isolation: opening a library does NOT import its transitive opens
--       (combineAlg .closed closes opens).
--     - Ambiguity: if multiple open targets provide the same public name, and no
--       owned/local/parent property shadows it, `ambiguousOpen` is raised.
--     - Owned/local/parent lookup takes precedence over opens (ownership-first).

namespace KatLang

--------------------------------------------------------------------------------
-- Typed identifiers (lightweight aliases for future-proofing)
--------------------------------------------------------------------------------

abbrev Ident := String    -- algorithm / property / parameter names
abbrev Assoc (K V : Type) := List (Prod K V)  -- association list

--------------------------------------------------------------------------------
-- Errors / Monad
--------------------------------------------------------------------------------

inductive Error where
  | unknownName      : Ident -> Error
  | unknownProperty  : String -> Ident -> Error        -- object desc, property name
  | notPublicProperty : String -> Ident -> Error       -- object desc, property name (exists but private)
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
  | branchArityMismatch : Ident -> Nat -> Nat -> Error  -- conditional algorithm: branch top-level arity mismatch (name, expected, actual)
  | branchOutputArityMismatch : Ident -> Nat -> Nat -> Error  -- conditional algorithm: branch top-level output arity mismatch (name, expected, actual)
  | duplicateProperty : Ident -> Error         -- algorithm defines the same property name more than once
  | duplicateBranchPattern : Error             -- conditional algorithm has match-equivalent branch patterns
  | unresolvedImplicitParams : List Ident -> Error  -- top-level block has unresolved implicit parameters
  | withContext      : String -> Error -> Error -- contextual wrapper
  deriving Repr

abbrev EvalM := Except Error

-- * IMPORTANT: Needed for compiling `partial` definitions.
-- Lean requires `Nonempty` for the function types of partial defs.
instance : Nonempty Error := Nonempty.intro Error.badArity
instance {A : Type} : Nonempty (EvalM A) := Nonempty.intro (Except.error Error.badArity)

--------------------------------------------------------------------------------
-- Operators
--------------------------------------------------------------------------------

inductive BinaryOp where
  | add | sub | mul | div | idiv | mod | pow
  | lt | gt | le | ge | eq | ne
  | and | or | xor
  deriving Repr, BEq, DecidableEq

inductive UnaryOp where
  | minus | not
  deriving Repr

inductive Builtin where
  | ifBuiltin | whileBuiltin | repeatBuiltin | atomsBuiltin | rangeBuiltin | filterBuiltin
  deriving Repr, BEq, DecidableEq

/-- Check whether a builtin accepts a given argument count.
    ifBuiltin accepts 2 (conditional output) or 3 (if-then-else).
    rangeBuiltin accepts 2 integer bounds: start and stop.
    filterBuiltin accepts 2 arguments: a collection and a predicate. -/
def builtinAcceptsArity : Builtin -> Nat -> Bool
  | .ifBuiltin, 2 => true | .ifBuiltin, 3 => true
  | .whileBuiltin, 2 => true
  | .repeatBuiltin, 3 => true
  | .atomsBuiltin, 1 => true
  | .rangeBuiltin, 2 => true
  | .filterBuiltin, 2 => true
  | _, _ => false

/-- Human-readable expected arity string for error messages. -/
def builtinArityDesc : Builtin -> String
  | .ifBuiltin => "2 or 3"
  | .whileBuiltin => "2"
  | .repeatBuiltin => "3"
  | .atomsBuiltin => "1"
  | .rangeBuiltin => "2"
  | .filterBuiltin => "2"

--------------------------------------------------------------------------------
-- Patterns (for conditional algorithms)
--------------------------------------------------------------------------------

/-- Pattern language for conditional algorithm branch matching.
    Patterns match against Result values at call time.
    - `bind x`: matches any Result and binds it to name `x`
    - `litInt n`: matches only `Result.atom n`
    - `group ps`: matches `Result.group rs` with same arity, each sub-pattern matching

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
      groups).  Branch bodies must not use Grace because conditional branches
      have no implicit parameter inference or reordering to apply it to.

    This keeps conditional algorithms self-contained: branch selection and
    branch binding are the same operation, with no hidden remaining parameters
    and no interaction with Grace-based parameter reordering. -/
inductive Pattern where
  | bind      : Ident -> Pattern
  | litInt    : Int -> Pattern
  | litString : String -> Pattern    -- matches only Result.str s (exact string equality)
  | group     : List Pattern -> Pattern
  deriving Repr, BEq

namespace Pattern
  /-- Collect all binder names in a pattern (left-to-right). -/
  def boundNames : Pattern -> List Ident
    | .bind x      => [x]
    | .litInt _    => []
    | .litString _ => []
    | .group ps    => ps.flatMap boundNames

  /-- Check whether a pattern contains duplicate binder names. -/
  def hasDuplicateBinds (p : Pattern) : Bool :=
    let names := boundNames p
    names.length != names.eraseDups.length

  /-- Compute the top-level arity of a pattern.
      - `group [p1, ..., pn]` ⟹ n
      - any non-group pattern  ⟹ 1

      This defines the outer call interface of a conditional algorithm branch.
      Conditional algorithms require a uniform top-level interface across branches:
      all branches of the same conditional algorithm must have the same
      top-level pattern arity.  Nested substructure may vary, but the outer
      number of inputs must remain consistent. -/
  def topLevelArity : Pattern -> Nat
    | .group ps => ps.length
    | _         => 1

  /-- Check whether two patterns are match-equivalent, i.e., they match the
      same set of inputs.  Binder names are irrelevant for matching:
      - `bind _` ≡ `bind _` (any binder matches everything)
      - `litInt m` ≡ `litInt n` iff `m = n`
      - `group ps` ≡ `group qs` iff same length and pairwise match-equivalent

      Used to detect duplicate branch patterns in conditional algorithms. -/
  partial def isMatchEquivalent : Pattern -> Pattern -> Bool
    | .bind _,   .bind _    => true
    | .litInt m, .litInt n  => m == n
    | .litString s, .litString t => s == t
    | .group ps, .group qs  =>
        ps.length == qs.length &&
        (ps.zip qs).all (fun (p, q) => isMatchEquivalent p q)
    | _, _ => false
end Pattern

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

mutual
  inductive Expr where
    | param   : Ident -> Expr
    | num     : Int -> Expr
    | stringLiteral : String -> Expr  -- * string literal: first-class value (evaluates to Result.str)
    | unary   : UnaryOp -> Expr -> Expr
    | binary  : BinaryOp -> Expr -> Expr -> Expr
    | index   : Expr -> Expr -> Expr
    | combine : Expr -> Expr -> Expr
    | resolve : Ident -> Expr
    | block   : Algorithm -> Expr
    | call    : Expr -> Algorithm -> Expr
    | dotCall : Expr -> Ident -> Option Algorithm -> Expr    -- a.f or a.f(args)
    -- NOTE: load('url') is surface-only syntax, represented as Call(Resolve("load"), ...)
    -- in the parser and elaborated to Block(...) by the load elaboration pass.
    -- It is NOT a core Expr constructor.  See load elaboration section below.
    deriving Repr

  /-- Property definition with visibility metadata. -/
  structure PropDef where
    name     : Ident
    alg      : Algorithm
    isPublic : Bool
    deriving Repr

  /-- A branch of a conditional algorithm: a pattern and a body algorithm.
      The pattern is the complete input specification of the branch.
      Branch bodies receive bindings ONLY from the matched pattern (plus
      ordinary lexical resolution).  No extra implicit parameters are inferred
      from free identifiers in the body.  Grace `~` is not allowed in patterns
      or branch bodies.

      The top-level output arity of a branch is the number of top-level output
      expressions in its body (`body.output.length`).  All branches of the same
      conditional algorithm must have the same top-level output arity.
      Nested internal output structure may vary. -/
  structure CondBranch where
    pattern : Pattern
    body    : Algorithm
    deriving Repr

  inductive Algorithm where
    /-- User-defined algorithm with properties, parameters, opens, and output.

        **Unique property name invariant**: the `properties` list must not
        contain two entries with the same `name`.  Properties are immutable
        bindings; redefining a property is a static error detected by the
        front-end / parser.  This invariant ensures that `lookupPropDefAny?`
        (which returns the first match) is unambiguous. -/
    | mk :
        (parent     : Option ScopeCtx) ->
        (params     : List Ident) ->
        (opens      : List Expr) ->
        (properties : List PropDef) ->
        (output     : List Expr) ->
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
        front-end / parser. -/
    | conditional :
        (parent   : Option ScopeCtx) ->
        (opens    : List Expr) ->
        (branches : List CondBranch) ->
        Algorithm
    deriving Repr

  inductive ScopeCtx where
    | mk :
        (parent  : Option ScopeCtx) ->
        (opens   : List Expr) ->
        (props   : List PropDef) ->
        ScopeCtx
    deriving Repr
end

--------------------------------------------------------------------------------
-- Result (structured evaluation artifact)
--------------------------------------------------------------------------------

inductive Result where
  | atom  : Int -> Result
  | str   : String -> Result     -- first-class string value (exact equality, no ordering/coercion)
  | group : List Result -> Result
  deriving Repr

namespace Result
  def normalize : Result -> Result
    | atom n => atom n
    | str s  => str s
    | group rs =>
        let rs' := rs.map normalize
        match rs' with
        | [r] => r
        | _   => group rs'

  def atoms : Result -> List Int
    | atom n    => [n]
    | str _     => []       -- strings are not numeric; silently omitted from atom lists
    | group rs => rs.flatMap atoms

  /-- KatLang truth testing used by builtins like `if`.
      Zero is false, any other numeric atom is true.
      Results with no numeric atoms are invalid for truth testing.

      This intentionally follows the current builtin convention based on the
      first numeric atom of the flattened result. Builtins with stricter
      contracts, such as `filter`, should use a dedicated helper instead. -/
  def truthValue? (r : Result) : Option Bool :=
    match atoms r with
    | 0::_ => some false
    | _::_ => some true
    | _    => none

  /-- Strict truth testing for `filter` predicates.
      Accepts exactly one atomic numeric result: `0` is false and any other
      atom is true.

      Grouped values, multi-output results, empty results, and strings are all
      rejected. This is intentionally stricter than `truthValue?`, because
      `filter` must not derive truth from flattened atoms. -/
  def singleAtomicTruthValue? : Result -> Option Bool
    | atom 0 => some false
    | atom _ => some true
    | _      => none

  def asInt? : Result -> Option Int
    | atom n => some n
    | str _  => none
    | group rs =>
        match normalize (group rs) with
        | atom n => some n
        | _      => none

  /-- Extract top-level items from a result.
      Atom → singleton list; Group → its items. -/
  def toItems : Result -> List Result
    | atom n   => [atom n]
    | str s    => [str s]
    | group rs => rs

  /-- Structural indexing (preserves grouping). -/
  def index? : Result -> Nat -> Option Result
    | atom n, 0   => some (atom n)
    | atom _, _   => none
    | str s, 0    => some (str s)
    | str _, _    => none
    | group rs, i => rs[i]?
end Result

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
end AlgEnv

/-- Evaluation context threaded through resolution and evaluation.
    Wraps the algorithm chain (current algorithm + enclosing callers) used for
    both lexical resolution and runtime dispatch.
    algEnv carries algorithm-typed parameter bindings for higher-order dispatch. -/
structure EvalCtx where
  callStack : List Algorithm
  algEnv    : AlgEnv := []
  deriving Repr

namespace EvalCtx
  def empty : EvalCtx := { callStack := [], algEnv := [] }
  def push (a : Algorithm) (ctx : EvalCtx) : EvalCtx :=
    { callStack := a :: ctx.callStack, algEnv := ctx.algEnv }
  def head? (ctx : EvalCtx) : Option Algorithm := ctx.callStack.head?
  def withAlgEnv (env : AlgEnv) (ctx : EvalCtx) : EvalCtx :=
    { callStack := ctx.callStack, algEnv := env }
end EvalCtx

abbrev ValEnv.lookup (env : ValEnv) (x : Ident) : Option Result :=
  lookupAssoc x env

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

/-- Primary helper: Lookup PropDef by name (public only). -/
def lookupPropDefPublic? (ps : List PropDef) (k : Ident) : Option PropDef :=
  ps.find? (fun p => p.name = k && p.isPublic)

/-- Private aliases for backwards compatibility. -/
private def findPropAny? := @lookupPropDefAny?
private def findPropPublic? := @lookupPropDefPublic?

/-- Lookup Algorithm from PropDef list (any visibility). -/
def lookupPropAny (ps : List PropDef) (k : Ident) : Option Algorithm :=
  (lookupPropDefAny? ps k).map (fun propDef => propDef.alg)

/-- Lookup Algorithm from PropDef list (public only). -/
def lookupPropPublic (ps : List PropDef) (k : Ident) : Option Algorithm :=
  (lookupPropDefPublic? ps k).map (fun propDef => propDef.alg)

/-- Check if PropDef list contains a property (any visibility). -/
def hasPropAny (ps : List PropDef) (k : Ident) : Bool :=
  (lookupPropDefAny? ps k).isSome

/-- Check if PropDef list contains a public property. -/
def hasPropPublic (ps : List PropDef) (k : Ident) : Bool :=
  (lookupPropDefPublic? ps k).isSome

namespace Algorithm
  def parent : Algorithm -> Option ScopeCtx
    | .mk p _ _ _ _ => p
    | .builtin _ => none
    | .conditional p _ _ => p
  def params : Algorithm -> List Ident
    | .mk _ ps _ _ _ => ps
    | .builtin _ => []
    | .conditional _ _ _ => []
  def opens : Algorithm -> List Expr
    | .mk _ _ op _ _ => op
    | .builtin _ => []
    | .conditional _ op _ => op
  def props : Algorithm -> List PropDef
    | .mk _ _ _ pr _ => pr
    | .builtin _ => []
    | .conditional _ _ _ => []
  def output : Algorithm -> List Expr
    | .mk _ _ _ _ out => out
    | .builtin _ => []
    | .conditional _ _ _ => []

  /-- Access branches for conditional algorithms. Returns [] for other forms. -/
  def branches : Algorithm -> List CondBranch
    | .conditional _ _ bs => bs
    | _ => []

  def withParent (p : Option ScopeCtx) : Algorithm -> Algorithm
    | .mk _ ps op pr out => .mk p ps op pr out
    | .builtin b => .builtin b
    | .conditional _ op bs => .conditional p op bs

  def asScopeCtx (a : Algorithm) : ScopeCtx :=
    ScopeCtx.mk (parent a) (opens a) (props a)

  def isBuiltin : Algorithm -> Bool
    | .builtin _ => true
    | _          => false

  /-- Unfiltered property lookup (sees private properties). -/
  def lookupProp (a : Algorithm) (k : Ident) : Option Algorithm :=
    lookupPropAny (props a) k

  /-- Public-only property lookup (for open resolution). -/
  def lookupPublicProp (a : Algorithm) (k : Ident) : Option Algorithm :=
    lookupPropPublic (props a) k

  /-- Lookup PropDef by name (any visibility). -/
  def lookupPropDefAny? (a : Algorithm) (k : Ident) : Option PropDef :=
    KatLang.lookupPropDefAny? (props a) k

  /-- Lookup PropDef by name (public only). -/
  def lookupPropDefPublic? (a : Algorithm) (k : Ident) : Option PropDef :=
    KatLang.lookupPropDefPublic? (props a) k

  /-- Wire a child algorithm to its parent's scope context. -/
  def childOf (a : Algorithm) (child : Algorithm) : Algorithm :=
    child.withParent (some (a.asScopeCtx))

  /-- Validate that all branches of a conditional algorithm have the same
      top-level pattern arity.  Returns `none` if valid (or non-conditional),
      `some (expected, actual)` for the first mismatching branch.
      This enforces the uniform top-level arity invariant:
      conditional algorithms are "one algorithm, one outer interface, many branches". -/
  def validateBranchArities : Algorithm -> Option (Nat × Nat)
    | .conditional _ _ bs =>
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
      outputs must remain consistent. -/
  def validateBranchOutputArities : Algorithm -> Option (Nat × Nat)
    | .conditional _ _ bs =>
        match bs with
        | [] => none
        | b :: rest =>
            let expected := b.body.output.length
            if rest.any (fun br => br.body.output.length != expected)
            then
              match rest.find? (fun br => br.body.output.length != expected) with
              | some bad => some (expected, bad.body.output.length)
              | none     => none  -- unreachable
            else none
    | _ => none

  /-- Check whether the property list of an Algorithm.mk contains duplicate
      property names.  Returns the first duplicate name found, or `none`
      if all names are unique.  This enforces the unique property name invariant. -/
  def findDuplicatePropName : Algorithm -> Option Ident
    | .mk _ _ _ ps _ =>
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
    | .conditional _ _ bs =>
        let rec go : List CondBranch -> Bool
          | [] => false
          | b :: rest =>
              if rest.any (fun br => b.pattern.isMatchEquivalent br.pattern)
              then true
              else go rest
        go bs
    | _ => false
end Algorithm

namespace ScopeCtx
  def parent : ScopeCtx -> Option ScopeCtx
    | .mk p _ _ => p
  def opens : ScopeCtx -> List Expr
    | .mk _ op _ => op
  def props : ScopeCtx -> List PropDef
    | .mk _ _ ps => ps
end ScopeCtx

namespace Algorithm
  /-- Create a temporary algorithm from a ScopeCtx for open resolution. -/
  def forOpens (sc : ScopeCtx) : Algorithm :=
    .mk (some sc) [] (ScopeCtx.opens sc) [] []

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

/-- Unwired parent-chain lookup: returns the algorithm as stored at its
    definition site, without rewiring its parent to the opener.
    Used exclusively by open resolution to enforce isolation. -/
partial def lookupInParentsDirectUnwired (sc : ScopeCtx) (name : Ident) : Option Algorithm :=
  match lookupPropAny (ScopeCtx.props sc) name with
  | some child => some child
  | none =>
      match ScopeCtx.parent sc with
      | some sc' => lookupInParentsDirectUnwired sc' name
      | none     => none

/-- Unwired direct lexical lookup: same search path as `lookupLexicalDirect`
    but returns algorithms without rewiring to the caller.
    The returned algorithm's parent chain is the one from its definition site.
    Used by `resolveAlgForOpen` to preserve open isolation. -/
partial def lookupLexicalDirectUnwired (a : Algorithm) (name : Ident) : Option Algorithm :=
  match Algorithm.lookupProp a name with
  | some child => some child
  | none =>
    match Algorithm.parent a with
    | some sc => lookupInParentsDirectUnwired sc name
    | none    => none

/-- Public-only unwired parent-chain lookup: returns public properties only.
    Used by open resolution to enforce strict public-only open targets. -/
partial def lookupInParentsDirectUnwiredPublic (sc : ScopeCtx) (name : Ident) : Option Algorithm :=
  match lookupPropPublic (ScopeCtx.props sc) name with
  | some child => some child
  | none =>
      match ScopeCtx.parent sc with
      | some sc' => lookupInParentsDirectUnwiredPublic sc' name
      | none     => none

/-- Public-only unwired direct lexical lookup: searches local then parent chain
    for public properties only, returning algorithms unwired (definition-site parent preserved).
    Used by `resolveAlgForOpen` to enforce strict public-only open targets. -/
partial def lookupLexicalDirectUnwiredPublic (a : Algorithm) (name : Ident) : Option Algorithm :=
  match Algorithm.lookupPublicProp a name with
  | some child => some child
  | none =>
    match Algorithm.parent a with
    | some sc => lookupInParentsDirectUnwiredPublic sc name
    | none    => none

def wireToCaller (ctx : EvalCtx) (a : Algorithm) : Algorithm :=
  match ctx.callStack.head? with
  | some caller => Algorithm.childOf caller a
  | none        => a

--------------------------------------------------------------------------------
-- Intrinsics
--------------------------------------------------------------------------------

/-- Predicate for intrinsic (non-builtin) property names.
    These names are handled specially in resolveAlg / evalDotCall
    rather than being looked up as structural properties.

    Intrinsic kinds:
    - "length": structural — returns the count of output expressions (no evaluation needed)
    - "string": value-based — evaluates the algorithm output, converts numeric result to string -/
def isIntrinsic (name : Ident) : Bool :=
  name = "length" || name = "string"

/-- Convert a numeric Result to its canonical string representation.
    Only atomic numeric values are supported; other forms raise typeMismatch.
    Canonical representation: Int.repr (e.g., 123 → "123", -5 → "-5", 0 → "0"). -/
def resultToString (r : Result) : EvalM Result :=
  match r with
  | .atom n => pure (Result.str (toString n))
  | _ => .error (Error.typeMismatch "builtin property `string` expects a numeric receiver")

/-- Evaluate a structural intrinsic property on a resolved algorithm.
    Returns `some result` if `name` is a recognized structural intrinsic, `none` otherwise.
    Value-based intrinsics (e.g. `string`) are handled inside evalDotCall
    because they require evaluation context. -/
def evalStructuralIntrinsic? (targetAlg : Algorithm) (name : Ident) : EvalM (Option Result) :=
  if name = "length" then
    pure (some (Result.atom (Int.ofNat (Algorithm.output targetAlg).length)))
  else
    pure none

--------------------------------------------------------------------------------
-- Semantics
--------------------------------------------------------------------------------

/-- Coerce a Result to Int, or raise typeMismatch for strings, badArity otherwise. -/
def expectInt (r : Result) : EvalM Int :=
  match r with
  | .str _ => .error (Error.typeMismatch "Expected a number, got a string")
  | _ => match Result.asInt? r with
    | some n => pure n
    | none   => .error Error.badArity

/-- Build the inclusive integer sequence for `range(start, stop)`.
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

/-- Step output: state and continuation flag. -/
abbrev StepOut := Prod Result Int

/-- Split a step result into (state, continue-flag).
    Convention: the last atom is the continue flag (nonzero = keep going). -/
def splitCont (out : Result) : EvalM StepOut := do
  match out with
  | .atom n => pure (.atom n, n)
  | .str _  => .error Error.badArity
  | .group rs =>
      match rs.getLast? with
      | some last =>
          let c <- expectInt last
          let state := Result.normalize (.group rs.dropLast)
          pure (state, c)
      | none => .error Error.badArity

partial def bindParams (ps : List Ident) (vs : List Result) : EvalM ValEnv :=
  match ps, vs with
  | [], [] => .ok []
  | p::ps', v::vs' => do
      let rest <- bindParams ps' vs'
      pure ((p,v)::rest)
  | _, _ => .error (Error.arityMismatch ps.length vs.length)

/-- Argument passing rule: a single atom is wrapped in a one-element list;
    a group is unpacked into its elements.  This is the canonical ABI for
    translating an evaluated Result into positional arguments for bindParams. -/
def unpackArgs (r : Result) : List Result :=
  match r with
  | .atom _ => [r]
  | .str _  => [r]
  | .group rs => rs

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

/-- Attach context to any error raised by `m`. -/
def withCtx (ctx : String) (m : EvalM A) : EvalM A :=
  m.mapError (Error.withContext ctx)

/-- Reify a normalized Result as an expression that evaluates back to the same
    value/shape. Grouped results become block expressions so nested structure is
    preserved exactly. -/
def resultToExpr : Result -> Expr
  | .atom n => .num n
  | .str s => .stringLiteral s
  | .group rs => .block (Algorithm.mk none [] [] [] (rs.map resultToExpr))

def intPow (b : Int) : Nat -> Int
  | 0 => 1
  | n + 1 => b * intPow b n

/-- Policy controlling how opens are handled when combining two algorithms. -/
inductive OpenPolicy where
  /-- Merge opens from both algorithms (`a.opens ++ b.opens`). -/
  | merge
  /-- Discard all opens (result has `opens = []`).
      Enforces isolation: libraries cannot smuggle in transitive opens. -/
  | closed
  deriving Repr, BEq

/-- Combine two algorithms, using `policy` to control open handling.
    - `OpenPolicy.merge`:  opens are concatenated (normal combination).
    - `OpenPolicy.closed`: opens are discarded (strict isolation for open resolution). -/
def combineAlg (policy : OpenPolicy := .merge) (a b : Algorithm) : Algorithm :=
  let opens := match policy with
    | .merge  => a.opens ++ b.opens
    | .closed => []
  Algorithm.mk
    none
    (a.params ++ b.params)           -- params merged
    opens                            -- opens per policy
    (a.props  ++ b.props)            -- properties merged
    [ Expr.block a, Expr.block b ]   -- output preserves boundaries

/-- Predicate defining which expression forms are allowed in open position
    **after elaboration**.  Only structural references to libraries are permitted.

    OpenForm is the *post-elaboration* set of permitted open expressions.
    Surface-level `load('url')` calls (represented as `Call(Resolve("load"), ...)`)
    may appear in source open lists, but the load elaboration pass MUST rewrite
    every such call into `Expr.block` before open resolution or validation runs.

    Note: the C# parser produces DotCall for all dot syntax (e.g. `Lib.Sub`).
    `DotCall(obj, name, none)` is the canonical form for open dot paths.
    `DotCall(obj, name, some args)` is rejected as an invalid open form.
    After normalization and load elaboration, opens contain only the forms
    listed below.

    Additionally, the exact-syntax sugar `open 'url'` is desugared to
    `open load('url')` at parse time, so raw string literals never appear
    in the canonical open list.  The load elaboration pass then rewrites
    `Call(Resolve("load"), ...)` into `Block(parsed module)` as usual. -/
inductive OpenForm where
  | combine : Expr -> Expr -> OpenForm
  | block   : Algorithm -> OpenForm
  | resolve : Ident -> OpenForm
  | dotCall : Expr -> Ident -> OpenForm     -- a.f (no-arg dotCall)

def Expr.openForm? : Expr -> Option OpenForm
  | .combine a b     => some (.combine a b)
  | .block a         => some (.block a)
  | .resolve n       => some (.resolve n)
  | .dotCall o n none => some (.dotCall o n)
  | _                => none          -- dotCall with args, call, and all other forms are rejected

def Expr.isOpenForm (e : Expr) : Bool :=
  (Expr.openForm? e).isSome

/-- Human-readable constructor kind for diagnostics. -/
def Expr.kind : Expr -> String
  | .param _      => "param"
  | .num _        => "num"
  | .stringLiteral _ => "stringLiteral"
  | .unary _ _    => "unary"
  | .binary _ _ _ => "binary"
  | .index _ _    => "index"
  | .combine _ _  => "combine"
  | .resolve _    => "resolve"
  | .block _      => "block"
  | .call _ _     => "call"
  | .dotCall _ _ _  => "dotCall"

/-- Extract a descriptive name from an open expression for error messages. -/
def openExprName (e : Expr) : String :=
  match e with
  | .resolve n => n
  | .dotCall o n _ => openExprName o ++ "." ++ n
  | .block _ => "(inline library)"
  | .combine a b => openExprName a ++ " + " ++ openExprName b
  | _ => s!"({Expr.kind e})"            -- * informative fallback using constructor kind

namespace CtxMsg
  def openMsg (k : String)              := s!"while resolving open: {k}"
  def call   (f : Expr)               := s!"while evaluating call to {openExprName f}"
  def dotCall (obj : Expr) (n : Ident) := s!"while evaluating dotCall .{n} of {openExprName obj}"
end CtxMsg

--------------------------------------------------------------------------------
-- Open resolution structures
--------------------------------------------------------------------------------

/-- A resolved open: its canonical dedup key, original expression, and resolved algorithm. -/
structure ResolvedOpen where
  key  : String
  expr : Expr
  lib  : Algorithm
  deriving Repr

/-- A single hit from open lookup: which provider supplied it, the library, and the child algorithm. -/
structure OpenHit where
  provider : String
  lib      : Algorithm
  child    : Algorithm
  deriving Repr

--------------------------------------------------------------------------------
-- Pattern matching (for conditional algorithms)
--------------------------------------------------------------------------------

/-- Match a pattern against a Result, returning accumulated bindings on success.
    - `bind x` matches any Result, binding x → r
    - `litInt n` matches only `Result.atom n`
    - `group ps` matches `Result.group rs` with same length, recursively

    Bindings accumulate left-to-right. Callers should reject duplicate binder
    names at elaboration/parse time. -/
def matchPattern (p : Pattern) (r : Result) : Option ValEnv :=
  match p with
  | .bind x    => some [(x, r)]
  | .litInt n  =>
      match r with
      | .atom v => if v = n then some [] else none
      | _       => none
  | .litString s =>
      match r with
      | .str v => if v = s then some [] else none
      | _      => none
  | .group ps  =>
      match r with
      | .group rs =>
          if ps.length != rs.length then none
          else
            let rec go : List Pattern -> List Result -> Option ValEnv
              | [], []           => some []
              | p::ps', r::rs'   => do
                  let env1 <- matchPattern p r
                  let env2 <- go ps' rs'
                  pure (env1 ++ env2)
              | _, _             => none
            go ps rs
      | _ => none

/-- Try to match branches in order. Returns the first matching branch and its bindings. -/
def matchBranches (bs : List CondBranch) (arg : Result) : Option (CondBranch × ValEnv) :=
  match bs with
  | []     => none
  | b::bs' =>
      match matchPattern b.pattern arg with
      | some env => some (b, env)
      | none     => matchBranches bs' arg

mutual

  --------------------------------------------------------------------------
  -- Open resolution
  --------------------------------------------------------------------------

  /-- Algorithm resolution using only direct lexical lookup (no opens).
      Used for resolving open expressions to avoid circularity.

      Open resolution returns algorithms without rewiring to the opener.
      The returned algorithm's parent chain is the one from its definition
      site (if any).  This enforces open isolation: a library's internal
      lexical structure is self-contained and never smuggles caller context.

      Open restrictions:
      - Only `Expr.openForm?` forms are permitted (structural references to libraries only).
      - Builtins are rejected: they are not valid open targets.
      - **Public-path policy**: Property access in open paths (e.g., `Open = Lib.Sub`) requires
        all intermediate properties to be public. `Algorithm.lookupPublicProp` enforces this.

      Examples:
      - `open Lib` where `Lib` has `{ publicProp "Sub" ... }` → OK, exposes public properties of Sub
      - `open Lib.PrivateSub` where `PrivateSub` has `isPublic = false` → Error (unknownProperty)
      - Structural access `Lib.PrivateSub.X` in code → OK (uses Algorithm.lookupProp, sees private)
      - `open Lib` does NOT expose private properties of Lib (filtered by lookupOpens) -/
  partial def resolveAlgForOpen (e : Expr) (ctx : EvalCtx) : EvalM Algorithm := do
    match Expr.openForm? e with
    | some (.combine e1 e2) => do
      let a <- resolveAlgForOpen e1 ctx
      let b <- resolveAlgForOpen e2 ctx
      pure (combineAlg .closed a b)  -- * no wiring, no open merging (strict isolation)
    | some (.block a) => pure a       -- * no wiring for opens
    | some (.resolve n) =>
      match ctx.callStack with
      | a::_ =>
        match lookupLexicalDirectUnwiredPublic a n with
        | some r =>
            if r.isBuiltin then .error (Error.illegalInOpen s!"builtin '{n}'")
            else pure r       -- * unwired: preserves definition-site parent chain
        | none =>
            -- Try unfiltered lookup to distinguish private vs missing
            match lookupLexicalDirectUnwired a n with
            | some _ => .error (Error.notPublicProperty "(lexical)" n)
            | none   => .error (Error.unknownName n)
      | [] => .error (Error.unknownName n)
    | some (.dotCall o n) => do
      let a <- resolveAlgForOpen o ctx
      -- First check if property exists at all to distinguish missing vs private
      match Algorithm.lookupProp a n with
      | some p =>
          if p.isBuiltin then
            .error (Error.illegalInOpen s!"builtin not allowed in open: {openExprName o}.{n}")
          else
            -- Property exists; check if it's public
            match Algorithm.lookupPublicProp a n with
            | some publicAlg => pure publicAlg  -- * no wiring (pure resolution) - return public algorithm
            | none   => .error (Error.notPublicProperty (openExprName o) n)
      | none => .error (Error.unknownProperty (openExprName o) n)
    -- load('url') is not a core Expr constructor; it is represented as
    -- Call(Resolve("load"), ...) at parse time and elaborated to Block before
    -- open resolution.  If it reaches here un-elaborated, it falls through to
    -- the call/default case below.
    | none =>
        throw (Error.badOpenForm s!"{Expr.kind e}: {openExprName e}")

  /-- Resolve an open expression to a library algorithm. -/
  partial def resolveOpen (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
    resolveAlgForOpen e ctx

  /-- Resolve all opens of an algorithm upfront.
      Deduplicates named opens by `openExprName` (first occurrence wins) to
      avoid repeated resolution and spurious ambiguity.  Inline blocks are never
      deduplicated (each gets a unique positional key).
      Validates all open expressions first for fail-fast diagnostics. -/
  partial def resolveAllOpens (a : Algorithm) (ctx : EvalCtx) : EvalM (List ResolvedOpen) := do
    let rawOpens := Algorithm.opens a
    -- Deduplicate by key (first occurrence wins); inline blocks use positional keys
    let tagged := rawOpens.mapIdx (fun idx e =>
      let key := match e with
        | .block _ => s!"(inline#{idx})"   -- * unique per original position, never deduped
        | _        => openExprName e
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

  /-- Lookup in opened namespaces with ambiguity error.
      Ordering rule: opens are searched in declaration order (first wins for
      single-provider lookups; multiple providers trigger ambiguousOpen).
      Only public properties are visible through opens.
      Returns:
        * ok none              if no open provides `name` publicly
        * ok (some alg)        if exactly one open provides it publicly (wired to library parent)
        * error ambiguousOpen if multiple opens provide it publicly -/
  partial def lookupOpens (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM (Option Algorithm) := do
    let ctx' := EvalCtx.push a ctx
    let resolvedOpens <- resolveAllOpens a ctx'

    -- * Public-only filtering: only public properties visible through opens
    -- Keys from resolveAllOpens are used directly as provider tags.
    let mut hits : List OpenHit := []
    for ri in resolvedOpens do
      match Algorithm.lookupPublicProp ri.lib name with
      | some child =>
          hits := { provider := ri.key, lib := ri.lib, child := child } :: hits
      | none => pure ()
    hits := hits.reverse

    match hits with
    | [] => pure none  -- No public matches found
    | [h] =>
        pure <| some (Algorithm.childOf h.lib h.child)
    | hs =>
      .error (Error.ambiguousOpen name (hs.map (fun hit => hit.provider)))

  --------------------------------------------------------------------------
  -- Lexical resolution
  --------------------------------------------------------------------------

  /-- Structural-only lookup in parent chain (no opens anywhere).
      Ownership-first model: structural properties take precedence.
      Example: If parent defines Pi and opens Math also exports Pi,
      the parent's Pi wins. To get Math.Pi, use Math.Pi syntax. -/
  partial def lookupInParentsStructural (sc : ScopeCtx) (name : Ident) : Option Algorithm :=
    match lookupPropAny (ScopeCtx.props sc) name with
    | some child => some (Algorithm.withParent (some sc) child)
    | none =>
        match ScopeCtx.parent sc with
        | some sc' => lookupInParentsStructural sc' name
        | none     => none

  /-- Open-based lookup in parent chain (helper for lookupOpensInChain). -/
  partial def lookupOpensInParentChain (sc : ScopeCtx) (name : Ident) (ctx : EvalCtx) : EvalM (Option Algorithm) := do
    let tempAlg := Algorithm.forOpens sc
    match (<- lookupOpens tempAlg name ctx) with
    | some r => pure (some r)
    | none =>
        match ScopeCtx.parent sc with
        | some sc' => lookupOpensInParentChain sc' name ctx
        | none     => pure none

  /-- Open-based lookup across the algorithm chain (current first, then parents).
      Checks opens at each level of the parent chain as fallback. -/
  partial def lookupOpensInChain (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM (Option Algorithm) := do
    -- Try opens at current level
    match (<- lookupOpens a name ctx) with
    | some r => pure (some r)
    | none =>
        -- Try parent chain
        match Algorithm.parent a with
        | some sc => lookupOpensInParentChain sc name ctx
        | none    => pure none

  /-- Full lexical lookup with ownership-first model:
      1. Local properties (owned by this algorithm)
      2. Parent chain structural properties (owned by ancestors)
      3. Opens as fallback (foreign namespaces)

      This ensures structural ownership always takes precedence over opens. -/
  partial def lookupLexical (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM Algorithm := do
    -- 1. local properties
    match Algorithm.lookupProp a name with
    | some child =>
        pure (Algorithm.childOf a child)
    | none =>
        -- 2. parent chain structural only
        match Algorithm.parent a with
        | some sc =>
            match lookupInParentsStructural sc name with
            | some r => pure r
            | none =>
                -- 3. opens fallback across chain
                match (<- lookupOpensInChain a name ctx) with
                | some r => pure r
                | none   => .error (Error.unknownName name)
        | none =>
            -- no parents: try opens fallback
            match (<- lookupOpensInChain a name ctx) with
            | some r => pure r
            | none   => .error (Error.unknownName name)

  partial def resolveAlg (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
    match e with
    | .combine e1 e2 => do
        let a <- resolveAlg e1 ctx
        let b <- resolveAlg e2 ctx
        pure (wireToCaller ctx (combineAlg .merge a b))
    | .block a => pure (wireToCaller ctx a)
    | .resolve n =>
        match ctx.callStack with
        | a::_ => lookupLexical a n ctx
        | []   => .error (Error.unknownName n)
    | .dotCall o n args =>
        -- Lift a.f / a.f(args) to a wrapper algorithm; evalDotCall handles all semantics
        -- (length intrinsic, structural property, receiver injection, lexical fallback)
        pure (wireToCaller ctx (Algorithm.ofExpr (.dotCall o n args)))
    -- Explicit errors for syntactic forms that cannot resolve to algorithms
    | .param x =>
        -- Higher-order parameter: if x is bound in AlgEnv, return the algorithm
        match ctx.algEnv.lookup x with
        | some alg => pure alg
        | none     => .error (Error.notAnAlgorithm s!"param({x})")
    | .num n   => .error (Error.notAnAlgorithm s!"num({n})")
    | .unary _ _ => .error (Error.notAnAlgorithm "unary expression")
    | .binary _ _ _ => .error (Error.notAnAlgorithm "binary expression")
    | .index _ _ => .error (Error.notAnAlgorithm "index expression")
    | .call _ _ => .error (Error.notAnAlgorithm "call expression")
    | .stringLiteral _ => .error (Error.notAnAlgorithm "string literal")

  /-- Resolve argument expressions to algorithms for builtin dispatch.
      Unlike the earlier strict formulation (`mapM resolveAlg`), this function
      wraps *liftable* non-resolvable expressions (`notAnAlgorithm`,
      `illegalInEval`) in trivial `Algorithm.ofExpr` wrappers wired to the
      caller scope.  This enables ergonomic builtin syntax such as
      `If(X >= 5, 1, 0)` without requiring explicit `{…}` blocks around every
      argument.

      Wrapping is safe because builtins evaluate their algorithm arguments
      lazily via `evalAlgOutput`, so the expression is evaluated on demand
      within the correct scope rather than resolved structurally upfront.

      Errors that indicate genuine lookup or semantic failures (`unknownName`,
      `unknownProperty`, `ambiguousOpen`, etc.) are propagated immediately so
      diagnostics remain precise.

      Non-builtin call paths are unaffected — user-defined calls still evaluate
      arguments eagerly through `evalCall`. -/
  partial def resolveArgAlgs (args : Algorithm) (ctx : EvalCtx) : EvalM (List Algorithm) :=
    (Algorithm.output args).mapM (fun e => do
      match resolveAlg e ctx with
      | .ok a    => pure a
      | .error err =>
        if isLiftableError err then
          pure (wireToCaller ctx (Algorithm.ofExpr e))
        else
          .error err)
  where
    isLiftableError : Error → Bool
      | .notAnAlgorithm _ => true
      | .illegalInEval _  => true
      | .withContext _ e   => isLiftableError e
      | _                  => false

  /-- Try to resolve each argument expression to an algorithm.
      Returns `some alg` for expressions that resolve, `none` for those that don't
      (e.g., numeric literals, arithmetic).  Only liftable errors → none;
      genuine lookup failures propagate.
      Used by evalCall to build AlgEnv for higher-order algorithm parameters. -/
  partial def tryResolveArgAlgs (args : Algorithm) (ctx : EvalCtx) : EvalM (List (Option Algorithm)) :=
    (Algorithm.output args).mapM (fun e => do
      match resolveAlg e ctx with
      | .ok a    => pure (some a)
      | .error err =>
        if isLiftableError err then
          pure none
        else
          .error err)
  where
    isLiftableError : Error → Bool
      | .notAnAlgorithm _ => true
      | .illegalInEval _  => true
      | .withContext _ e   => isLiftableError e
      | _                  => false

  --------------------------------------------------------------------------
  -- Evaluation
  --------------------------------------------------------------------------

  /-- Evaluate an algorithm's output expressions and collect into a single Result.
      Normalization invariant: outputs are always normalized at algorithm boundaries.
      Singleton groups are collapsed here (and only here) so downstream consumers
      never see `group [x]`.  Builtins that synthesize fresh groups (e.g. Atoms)
      must normalize their own output explicitly. -/
  partial def evalAlgOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    match a.findDuplicatePropName with
    | some n => .error (Error.duplicateProperty n)
    | none =>
      let rs <- (Algorithm.output a).mapM (fun e => eval e (EvalCtx.push a ctx) env)
      pure (Result.normalize (Result.group rs))

  /-- Evaluate an expression and coerce the result to Int. -/
  partial def evalInt (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Int := do
    expectInt (<- eval e ctx env)

  /-- Run a step algorithm with the given state bound to its params. -/
  partial def runStep (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : Result) : EvalM Result := do
    let argEnv <- bindParams (Algorithm.params step) (unpackArgs s)
    evalAlgOutput step ctx (argEnv ++ env)

  /-- Evaluate a conditional algorithm against an already assembled argument
      Result shape. Used by ordinary conditional calls and by builtins that
      must pass one whole result value (for example `filter` elements) without
      flattening grouped structure. -/
  partial def evalConditionalShape (callee : Algorithm) (argShape : Result)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM Result := do
    if callee.hasDuplicateBranchPatterns then
      .error Error.duplicateBranchPattern
    else
      match matchBranches (Algorithm.branches callee) argShape with
      | some (branch, bindings) =>
          let wiredBody := Algorithm.childOf callee branch.body
          let newCtx := EvalCtx.push callee ctx
          evalAlgOutput wiredBody newCtx (bindings ++ env)
      | none =>
          .error (Error.noMatchingBranch calleeName)

  /-- Evaluate a resolved algorithm on one whole result value.
      Unlike ordinary eager calls, grouped results are bound as a single input
      value and are never unpacked into multiple positional arguments.
      This is used by `filter`, whose predicate must see each collection element
      as a whole unit. -/
  partial def evalWholeArgCall (callee : Algorithm) (arg : Result)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional")
      : EvalM Result := do
    match callee with
    | .builtin b =>
        applyBuiltin b [Algorithm.ofExpr (resultToExpr arg)] ctx env
    | .conditional _ _ _ =>
        evalConditionalShape callee (Result.normalize arg) ctx env calleeName
    | _ => do
        let argEnv <- bindParams (Algorithm.params callee) [arg]
        evalAlgOutput callee ctx (argEnv ++ env)

  partial def applyBuiltin
      (b : Builtin) (args : List Algorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM Result :=
    match b, args with

    -- if(cond, thenBranch, elseBranch): standard 3-arg conditional.
    | .ifBuiltin, [c,t,e] => do
        let cr <- evalAlgOutput c ctx env
        match Result.truthValue? cr with
        | some false => evalAlgOutput e ctx env
        | some true => evalAlgOutput t ctx env
        | none => .error Error.badArity

    -- if(cond, value): 2-arg conditional output / emit-on-true.
    -- True → evaluate and return value.
    -- False → produce no output (empty group).
    | .ifBuiltin, [c,v] => do
        let cr <- evalAlgOutput c ctx env
        match Result.truthValue? cr with
        | some false => pure (Result.group [])   -- false: no output
        | some true => evalAlgOutput v ctx env   -- true: produce value
        | none => .error Error.badArity

    | .whileBuiltin, [step, init] => do
        let s0r <- evalAlgOutput init ctx env
        let rec loop (s : Result) : EvalM Result := do
          let out <- runStep step ctx env s
          let (next, cont) <- splitCont out
          if cont = 0 then pure s else loop next
        pure (<- loop s0r)

    | .repeatBuiltin, [step, countAlg, init] => do
        let cr <- evalAlgOutput countAlg ctx env
        let n <- expectInt cr
        if n < 0 then
          .error (Error.illegalInEval "Repeat count must be >= 0")
        else
          let s0r <- evalAlgOutput init ctx env
          let rec repeatLoop (k : Int) (s : Result) : EvalM Result :=
            if k = 0 then pure s else do
              let out <- runStep step ctx env s
              repeatLoop (k-1) out
          repeatLoop n s0r

    | .atomsBuiltin, [a] => do
        let r <- evalAlgOutput a ctx env
        let xs := Result.atoms r
        pure (Result.normalize (Result.group (xs.map Result.atom)))

    | .rangeBuiltin, [startAlg, stopAlg] => do
      let start <- expectInt (<- evalAlgOutput startAlg ctx env)
      let stop <- expectInt (<- evalAlgOutput stopAlg ctx env)
      let xs := inclusiveRange start stop
      pure (Result.normalize (Result.group (xs.map Result.atom)))

    -- filter(collection, predicate): evaluate the collection left-to-right,
    -- applying predicate(element) to each top-level element as a whole unit.
    -- The predicate must return exactly one atomic numeric value: 0 rejects the
    -- item and any nonzero atom keeps it. Grouped, multi-output, empty, or
    -- string predicate results are invalid.
    -- Kept elements are preserved unchanged and in order; rejected elements are
    -- omitted entirely. The output is compact and grouped elements are never
    -- flattened or partially retained.
    | .filterBuiltin, [collectionAlg, predicateAlg] => do
      let collection <- evalAlgOutput collectionAlg ctx env
      let rec filterLoop : List Result -> EvalM (List Result)
        | [] => pure []
        | item :: rest => do
            let pr <- withCtx "while evaluating filter predicate (filter passes each collection item as one argument to the predicate)" <|
              evalWholeArgCall predicateAlg item ctx env "filter predicate"
            match Result.singleAtomicTruthValue? pr with
            | some true => do
                let kept <- filterLoop rest
                pure (item :: kept)
            | some false =>
                filterLoop rest
            | none =>
                .error (Error.withContext
                  "filter predicate must return exactly one atomic numeric value"
                  Error.badArity)
      let kept <- filterLoop collection.toItems
      pure (Result.normalize (Result.group kept))

    | _, _ =>
        .error (Error.withContext s!"expected {builtinArityDesc b} arguments" (Error.arityMismatch 0 args.length))

  /-- Shared user-defined call binding logic.
      Preserves the eager value ABI while layering AlgEnv for higher-order
      arguments. Each original argument expression is interpreted independently
      in two ways:
      - structural algorithm resolution for AlgEnv
      - ordinary eager value evaluation for ValEnv

      If both succeed, the parameter gets both meanings. If only one succeeds,
      only that view is bound. If both fail, the ordinary eager-evaluation
      error is propagated.

      Argument expressions may be fewer than parameters because a single eager
      value can unpack to multiple positional results, but an explicit argument
      list may not contain more expressions than the callee has parameters.
      This prevents extra higher-order arguments from being silently ignored by
      zipped AlgEnv binding. -/
  partial def evalUserCall (callee : Algorithm) (args : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let wiredArgs := wireToCaller ctx args
    let argExprs := Algorithm.output wiredArgs
    let paramCount := (Algorithm.params callee).length
    if argExprs.length > paramCount then
      .error (Error.arityMismatch paramCount argExprs.length)
    else do
      let maybeAlgs <- tryResolveArgAlgs wiredArgs ctx
      let algBindings := bindAlgParams (Algorithm.params callee) maybeAlgs
      let argEvalCtx := EvalCtx.push wiredArgs ctx
      -- For each (param, argExpr, maybeAlg) triple, independently try eval.
      -- Collect (param, value) for args whose eval succeeds.
      -- If eval fails but the arg resolved as algorithm, skip value binding.
      -- If eval fails and no algorithm, propagate the error.
      let rec collectValues
          (ps : List Ident) (es : List Expr)
          (mas : List (Option Algorithm))
          : EvalM (List Ident × List Result) :=
        match ps, es, mas with
        | [], _, _ => pure ([], [])
        | ps, [], _ => pure (ps, [])
        | p :: ps', e :: es', ma :: mas' =>
            match eval e argEvalCtx env with
            | .ok value => do
                let (rps, rvs) <- collectValues ps' es' mas'
                pure (p :: rps, value :: rvs)
            | .error err =>
                match ma with
                | some _ => collectValues ps' es' mas'
                | none => .error err
        | _, _, [] => .error (Error.arityMismatch paramCount argExprs.length)
      let (valueParams, valueResults) <- collectValues
          (Algorithm.params callee) argExprs maybeAlgs
      let unpackedValueResults :=
        match valueResults with
        | [] => []
        | rs => unpackArgs (Result.normalize (Result.group rs))
      let argEnv <- bindParams valueParams unpackedValueResults
      let newCtx := ctx.withAlgEnv (algBindings ++ ctx.algEnv)
      evalAlgOutput callee newCtx (argEnv ++ env)

  /-- Evaluate a conditional algorithm call.
      1. Evaluate argument expressions eagerly (same as normal call ABI).
      2. Assemble full argument Result shape (preserving grouping for pattern matching).
      3. Try branches in order; first match wins.
      4. Evaluate selected branch body with pattern bindings prepended to env.
      5. If no branch matches, raise noMatchingBranch error.

      Unlike evalUserCall, conditional algorithms do NOT use params/unpackArgs.
      The full argument shape is matched structurally against branch patterns.

      **Full-input-specification rule**: the branch body receives its input
      bindings ONLY from the matched pattern.  No extra implicit parameters are
      inferred from free identifiers in the body.  Free identifiers in the body
      must resolve through ordinary lexical / property / open / builtin lookup,
      or evaluation fails with unknownName.

      **Assumes uniform output arity**: after validation (validateBranchOutputArities),
      all branches produce the same top-level output arity.  The evaluator does
      not re-check this at runtime. -/
  partial def evalConditionalCall (callee : Algorithm) (args : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) (calleeName : String := "conditional") : EvalM Result := do
    let wiredArgs := wireToCaller ctx args
    let argExprs := Algorithm.output wiredArgs
    let argEvalCtx := EvalCtx.push wiredArgs ctx
    -- Evaluate all argument expressions eagerly
    let argResults <- argExprs.mapM (fun e => eval e argEvalCtx env)
    -- Assemble full argument shape: normalize group for pattern matching
    let argShape := Result.normalize (Result.group argResults)
    evalConditionalShape callee argShape ctx env calleeName

  partial def evalCall (f : Expr) (args : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let callee <- resolveAlg f ctx
    match callee with
    | .builtin b => do
        let argAlgs <- resolveArgAlgs args ctx
        applyBuiltin b argAlgs ctx env
    | .conditional _ _ _ => evalConditionalCall callee args ctx env (openExprName f)
    | _ => evalUserCall callee args ctx env

  /-- Resolve name lexically and call with receiver prepended to args.
      Delegates to evalCall to get builtin dispatch for free. -/
  partial def callLexicalWithReceiver (name : Ident) (receiver : Expr)
      (extraArgs : Option Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let outputExprs := [receiver] ++ match extraArgs with
      | some ea => Algorithm.output ea
      | none => []
    let combinedArgs := Algorithm.mk none [] [] [] outputExprs
    evalCall (.resolve name) combinedArgs ctx env

  /-- Evaluate dotCall: a.f or a.f(args)
      Smart dispatch:
      - "length" structural intrinsic → output expression count of target
      - "string" value intrinsic → evaluate target, convert numeric result to string
      - Structural property found (navigation-only):
        - If no args and 0-param → value access
        - If no args and has params → arity mismatch error
        - If args → direct argument binding (no receiver injection)
      - No property → lexical fallback (receiver injection)

      When resolveAlg returns notAnAlgorithm (e.g. numeric literal target),
      value-based intrinsics are checked before lexical fallback. -/
  partial def evalDotCall (target : Expr) (name : Ident) (argsOpt : Option Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    match resolveAlg target ctx with
    | .ok targetAlg =>
      match (<- evalStructuralIntrinsic? targetAlg name) with
      | some r => pure r
      | none =>
        -- Value-based intrinsic: "string" — evaluate algorithm output and convert
        if name = "string" then do
          let val <- evalAlgOutput targetAlg ctx env
          resultToString val
        else
          match Algorithm.lookupProp targetAlg name with
          | some p =>
              let wired := Algorithm.childOf targetAlg p
              match argsOpt with
              | none =>
                  match wired with
                  | .conditional _ _ _ => .error (Error.noMatchingBranch name)  -- no args to match against
                  | _ =>
                    if (Algorithm.params wired).length = 0 then
                      evalAlgOutput wired ctx env
                    else
                      -- Navigation only: no receiver injection, need explicit args
                      .error (Error.arityMismatch (Algorithm.params wired).length 0)
              | some args =>
                  match wired with
                  | .conditional _ _ _ => evalConditionalCall wired args ctx env name
                  | _ =>
                    -- Navigation only: direct argument binding, no receiver
                    evalUserCall wired args ctx env
          | none => callLexicalWithReceiver name target argsOpt ctx env
    | .error (.notAnAlgorithm _) =>
      -- Value-only target (e.g. numeric literal): check value-based intrinsics
      if name = "string" then do
        let val <- eval target ctx env
        resultToString val
      else
        callLexicalWithReceiver name target argsOpt ctx env
    | .error e => .error e

  partial def eval (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
    match e with
    | .num n => pure (Result.atom n)

    | .stringLiteral s => pure (Result.str s)

    | .param x =>
        match env.lookup x with
        | some v => pure v
        | none   =>
            -- Higher-order fallback: if x is bound in AlgEnv as a 0-param algorithm,
            -- auto-evaluate it (thunk semantics).  Multi-param algorithms require
            -- explicit call syntax and produce arityMismatch.
            match ctx.algEnv.lookup x with
            | some alg =>
                if (Algorithm.params alg).length = 0 then
                  evalAlgOutput alg ctx env
                else
                  .error (Error.arityMismatch (Algorithm.params alg).length 0)
            | none => .error (Error.unknownName x)

    | .unary op e => do
        let r <- eval e ctx env
        match r with
        | .group [] => pure (Result.group [])   -- empty propagates through unary
        | .str _ => .error (Error.typeMismatch "Unary operator is not supported for strings")
        | _ => do
          let v <- expectInt r
          pure (Result.atom <|
            match op with
            | .minus => -v
            | .not   => if v = 0 then 1 else 0)

    | .binary op a b => do
        let lr <- eval a ctx env
        let rr <- eval b ctx env
        -- Empty result handling: if(false, v) produces group [] (2-arg form).
        -- Empty results are transparent in binary expressions.
        match lr, rr with
        | .group [], _ => pure rr
        | _, .group [] => pure lr
        -- String equality/inequality: both operands must be strings.
        -- Other operations on strings fail via expectInt below.
        | .str s, .str t =>
            match op with
            | .eq => pure (Result.atom (if s = t then 1 else 0))
            | .ne => pure (Result.atom (if s != t then 1 else 0))
            | _   => .error (Error.typeMismatch "Strings only support == and != operators")
        -- Mixed string/number or string/group: fail for any operator
        | .str _, _ => .error (Error.typeMismatch "Cannot apply operator to string and non-string operands")
        | _, .str _ => .error (Error.typeMismatch "Cannot apply operator to string and non-string operands")
        | _, _ => do
          let x <- expectInt lr
          let y <- expectInt rr
          -- Check for division by zero
          if (op == BinaryOp.div || op == BinaryOp.idiv || op == BinaryOp.mod) && y == 0 then
            .error Error.divByZero
          else
            pure (Result.atom <|
              match op with
              | .add  => x + y
              | .sub  => x - y
              | .mul  => x * y
              | .div  => x / y
              | .idiv => x / y
              | .mod  => x % y
              | .pow  => if y < 0 then 0 else intPow x y.toNat
              | .lt   => if x < y then 1 else 0
              | .gt   => if x > y then 1 else 0
              | .le   => if x <= y then 1 else 0
              | .ge   => if x >= y then 1 else 0
              | .eq   => if x = y then 1 else 0
              | .ne   => if x != y then 1 else 0
              | .and  => if x != 0 then (if y != 0 then 1 else 0) else 0
              | .or   => if x != 0 then 1 else (if y != 0 then 1 else 0)
              | .xor  => if x != 0 then (if y = 0 then 1 else 0) else (if y != 0 then 1 else 0))

    | .combine e1 e2 => do
        let r1 <- eval e1 ctx env
        let r2 <- eval e2 ctx env
        pure (Result.normalize (Result.group (r1.toItems ++ r2.toItems)))

    | .block a =>
        let wired := wireToCaller ctx a
        if (Algorithm.params wired).length = 0 then
          evalAlgOutput wired ctx env
        else
          .error (Error.unresolvedImplicitParams (Algorithm.params wired))

    | .resolve n => do
        let a <- resolveAlg (.resolve n) ctx
        evalAlgOutput a ctx env

    | .dotCall o n argsOpt => withCtx (CtxMsg.dotCall o n) do
        evalDotCall o n argsOpt ctx env

    -- Call semantics:
    -- 1. Resolve f to an Algorithm
    -- 2. If builtin: args resolved lazily as algorithms, passed to builtin dispatch
    -- 3. If user alg: args evaluated eagerly to values, bound to params
    | .call f args => withCtx (CtxMsg.call f) do
        evalCall f args ctx env

    | .index a i => do
        let ar <- eval a ctx env
        let ir <- eval i ctx env
        let n  <- expectInt ir
        if n < 0 then
          .error Error.badIndex
        else
          match Result.index? ar (Int.toNat n) with
          | some r => pure r
          | none   => .error Error.badIndex

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
    let alg := Algorithm.mk parent params opens knownProps []
    let ctx := EvalCtx.push alg parentCtx

    -- For each free identifier token:
    match shouldTreatAsImplicitParam alg name ctx with
    | ok true  => emit (Expr.param name), add name to Algorithm.params
    | ok false => emit (Expr.resolve name)
    | error e  => report diagnostic (e.g., ambiguous open)
    ```

    IMPORTANT: Opens CAN suppress implicit parameters. If an opened library
    provides `name`, the surface layer emits `Expr.resolve name`, not a param.
    This is intentional: opens have lexical precedence in the ownership-first model.
    The trade-off is accepted: shadowing via opens is rare and explicit (listed in `opens:`).

    NOTE: This function is used only for ORDINARY algorithms.
    Conditional algorithm branch bodies do NOT use implicit parameter inference.
    In a conditional branch, the pattern in `Name(...)` is the complete input
    specification; free identifiers in the body must resolve lexically or produce
    an error.  Pattern-bound names are rewritten to `Expr.param` by the surface
    layer directly, without using this function. -/
def shouldTreatAsImplicitParam (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM Bool :=
  match lookupLexical a name ctx with
  | .ok _ => .ok false                      -- Name resolves → NOT a param
  | .error (Error.unknownName _) => .ok true  -- Name doesn't resolve → IS a param
  | .error e => .error e                    -- Propagate other errors (ambiguousOpen, etc.)

--------------------------------------------------------------------------------
-- Surface syntax support: implicit argument resolution
--------------------------------------------------------------------------------

/- **Implicit argument resolution** (surface syntax pass — runs after parameter
   detection):

   When a property body contains a bare reference to a sibling property that has
   parameters, the surface layer rewrites that reference into an explicit call,
   passing the sibling's parameters as arguments (lifted into the referencing
   property's own parameter list).

   Example:
     Surface:   `(A = x + 1;  B = A * 2)`
     After detection: A.params = [x], B.params = []
     After resolution: B.params = [x], B.output = [Call(A, [Param(x)]) * 2]

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
     final parameter list before processing subsequent dependents.

   Cycles are handled by leaving cyclic properties unmodified (no implicit
   argument lifting for properties involved in mutual recursion). -/

--------------------------------------------------------------------------------
-- Surface syntax support: while/repeat multi-item init lowering
--------------------------------------------------------------------------------

/- **Ordinary parentheses** always mean ordinary grouping.  There is no
   special "double-parens" syntax.  `((expr))` in any position is equivalent
   to `(expr)`.  `f((a + b) mod 2, c)` parses normally as two arguments.

   **while/repeat multi-item init lowering** is a targeted transformation
   that packages trailing arguments as a single `Expr.block` init-state
   argument for the `while` and `repeat` builtins.  It occurs in two places:

   1. Parser-level lowering for lexical (direct) calls
   --------------------------------------------------
   When the callee is exactly `resolve("while")` or `resolve("repeat")`:

     while(step, s1, s2, ..., sk)   -- k ≥ 2
       =>  while(step, block(Algorithm.mk(none, [], [], [], [s1, s2, ..., sk])))

     repeat(step, count, s1, s2, ..., sk)   -- k ≥ 2
       =>  repeat(step, count, block(Algorithm.mk(none, [], [], [], [s1, ..., sk])))

   When the arg count matches the builtin arity (2 for while, 3 for repeat),
   no rewriting occurs — the arguments are passed through unchanged.

   This rewriting is safe in the parser because the callee is a known name.

   2. Evaluator-level packaging for dotCall lexical fallback
   ---------------------------------------------------------
   For dotCall (`a.f(args)`), structural property lookup must happen first.
   Only when no structural property named "while" or "repeat" exists does
   lexical fallback fire, and THEN the evaluator packages multi-item init:

     Step.while(s1, s2, ...)      -- ≥2 explicit args
       =>  while(Step, block([s1, s2, ...]))

     Step.repeat(n, s1, s2, ...)  -- ≥3 explicit args
       =>  repeat(Step, n, block([s1, s2, ...]))

   When fewer explicit args are provided:
     Step.while(init)             -- 1 explicit arg → pass through (2 builtin args)
     Step.repeat(n, init)         -- 2 explicit args → pass through (3 builtin args)

   This two-level design ensures that:
   - Structural property precedence is preserved for dotCall
   - If algorithm A has a real property named "while", A.while(x, 0)
     resolves as a property call, not as lexical builtin fallback
   - Direct calls get rewritten early (parser)
   - DotCall gets rewritten late (evaluator), only after confirming
     no structural property shadows the name

   Expr.block semantics
   --------------------
   No `tuple` constructor exists in the Lean core AST; grouping is expressed
   purely via `Expr.block`.  Free identifiers inside the block bubble up to
   the enclosing algorithm through ParameterDetector, because the synthetic
   block has no params of its own (non-parametrized).

   Examples
   --------
     while(Step, 5, 0)       -- parser lowers to while(Step, block([5, 0]))
     repeat(Step, 3, 0, 0)   -- parser lowers to repeat(Step, 3, block([0, 0]))
     Step.while(x, 0)        -- evaluator packages to while(Step, block([x, 0]))
     Step.repeat(3, x, 0)    -- evaluator packages to repeat(Step, 3, block([x, 0]))
     Step.while((x, 0))      -- (x, 0) is ordinary grouping producing a block;
                              -- single arg, no packaging needed
     while(Step, init)        -- 2 args, no lowering
     repeat(Step, n, init)    -- 3 args, no lowering -/

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
   The parser constructs two layers:

   1. **Inline algorithm** (`inlineAlg`): the parametrized algorithm inferred
      from the brace body.  Free lowercase identifiers inside the body become
      implicit parameters via ParameterDetector, exactly as for `func`-style
      algorithms.  This is the algorithm that `{e}` denotes.

   2. **Argument-wrapper algorithm** (`argsAlg`): a zero-parameter algorithm
      whose single output expression is `Expr.block inlineAlg`.  This wrapper
      is what the parser emits as the call/dotCall argument.

   The trailing brace is therefore equivalent to parenthesised call syntax:

     Algo{e}       ≡  Algo({e})
     A.Apply{e}    ≡  A.Apply({e})

   Lowered AST:

     Algo{e}
       =>  call(resolve("Algo"), argsAlg)
           where  argsAlg = Algorithm.mk(none, [], [], [], [Expr.block inlineAlg])

     A.Apply{e}
       =>  dotCall(resolve("A"), "Apply", some argsAlg)
           where  argsAlg = Algorithm.mk(none, [], [], [], [Expr.block inlineAlg])

   Note: the parser does NOT pass `inlineAlg` as the args algorithm directly.
   It always wraps it inside `Expr.block` within the zero-parameter `argsAlg`.
   This allows `resolveAlg` to see the `Expr.block` node and return the inner
   algorithm, which is essential for higher-order binding via AlgEnv.

   Evaluation semantics of `Expr.block` in value position
   ------------------------------------------------------
   `Expr.block` represents an inline anonymous algorithm.  When evaluated
   directly (not resolved as an algorithm via resolveAlg):
   - 0-param block: auto-evaluates via evalAlgOutput (thunk semantics)
   - parametrized block: returns arityMismatch (needs explicit arguments)

   `resolveAlg(.block a)` always returns the algorithm (wired to caller scope),
   regardless of parameter count.

   Higher-order flow
   -----------------
   When a block is passed as an argument to a user-defined call:

     Algo = func(9)
     Algo{a + 1}

   1. The parser emits `call(resolve("Algo"), argsAlg)` where
      `argsAlg.output = [Expr.block inlineAlg]` and `inlineAlg.params = ["a"]`.
   2. `evalCall` resolves `Algo` and enters `evalUserCall`.
   3. `tryResolveArgAlgs` calls `resolveAlg(Expr.block inlineAlg)`, which
      returns `inlineAlg` (wired to caller scope).
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
  { name := name, alg := alg, isPublic := false }

/-- Helper to create a public property. -/
def publicProp (name : Ident) (alg : Algorithm) : PropDef :=
  { name := name, alg := alg, isPublic := true }

/-- Migration helper: convert assoc list to private PropDefs. -/
def propsPrivate (xs : List (Prod Ident Algorithm)) : List PropDef :=
  xs.map (fun (n, a) => privateProp n a)

/-- Migration helper: convert assoc list to public PropDefs. -/
def propsPublic (xs : List (Prod Ident Algorithm)) : List PropDef :=
  xs.map (fun (n, a) => publicProp n a)

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
    ]
    []

def runResult (e : Expr) : EvalM Result :=
  eval e { callStack := [preludeAlg], algEnv := [] } []

def runFlat (e : Expr) : EvalM (List Int) := do
  pure (Result.atoms (<- runResult e))

--------------------------------------------------------------------------------
-- Core sugar (surface syntax is external)
--------------------------------------------------------------------------------

open Expr

def param (s : Ident) : Expr := .param s
def num (n : Int) : Expr := .num n
def index (a i : Expr) : Expr := .index a i
def resolve (n : Ident) : Expr := .resolve n
def block (a : Algorithm) : Expr := .block a
def call (f : Expr) (a : Algorithm) : Expr := .call f a
def dotCall (o : Expr) (n : Ident) : Expr := .dotCall o n none
def combine (a b : Expr) : Expr := .combine a b

/-- Convenience constructor for algorithms with private properties by default.
    To make properties public, use `publicProp` when building the props list. -/
def alg (ps : List Ident) (op : List Expr) (props : List PropDef) (out : List Expr) : Algorithm :=
  Algorithm.mk none ps op props out

/-- Convenience constructor accepting (name, alg) pairs as private properties. -/
def algPrivate (ps : List Ident) (op : List Expr) (props : List (Prod Ident Algorithm)) (out : List Expr) : Algorithm :=
  Algorithm.mk none ps op (propsPrivate props) out

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
  fetch        : String -> Option String   -- abstract; in C# this is Func<string,string>

/-- Positions where load is allowed (compile-time only).
    load is a directive, not a runtime expression. -/
inductive LoadPosition where
  | propertyDef : LoadPosition   -- RHS of Name = load('...')
  | openList    : LoadPosition   -- inside open load('...') or open target1, target2
  deriving Repr, BEq

/- **load elaboration judgment**

  The elaboration pass transforms surface `Call(Resolve("load"), ...)` nodes into
  `Expr.block (parseModule (fetch url))` nodes.  `load` is NOT a core Expr
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
    1. No `Expr.stringLiteral` nodes remain (they only exist to carry load URLs).
    2. No unresolved load calls remain (i.e., no `call (resolve "load") _` nodes).
  All load directives have been replaced with `Expr.block` containing the
  parsed and elaborated remote algorithm. The evaluator never sees load calls.

  Formally:
    elaborate(call(resolve("load"), [stringLiteral url])) = block(parseModule(fetch(url)))
    ∀ e ∈ elaborated AST, e ≠ Expr.stringLiteral _
    ∀ e ∈ elaborated AST, e ≠ Expr.call (Expr.resolve "load") _
-/
mutual
/-- Post-elaboration invariant: returns true iff the expression tree contains
    no `Expr.stringLiteral` nodes and no unresolved load calls
    (`call (resolve "load") _`).  An AST satisfying this predicate is ready
    for semantic evaluation. -/
partial def postElabInvariant : Expr -> Bool
  | .stringLiteral _ => false
  | .unary _ e       => postElabInvariant e
  | .binary _ a b    => postElabInvariant a && postElabInvariant b
  | .index a b       => postElabInvariant a && postElabInvariant b
  | .combine a b     => postElabInvariant a && postElabInvariant b
  | .call (.resolve "load") _ => false  -- unresolved load call
  | .call f args     => postElabInvariant f && postElabInvariantAlg args
  | .dotCall a _ args =>
      postElabInvariant a &&
      match args with
      | some alg => postElabInvariantAlg alg
      | none => true
  | .block alg       => postElabInvariantAlg alg
  | _                => true  -- param, num, resolve

/-- Algorithm-level post-elaboration invariant: all contained expressions
    satisfy `postElabInvariant`. -/
partial def postElabInvariantAlg : Algorithm -> Bool
  | .builtin _ => true
  | .mk _ _ opens props output =>
      opens.all postElabInvariant &&
      props.all (fun p => postElabInvariantAlg p.alg) &&
      output.all postElabInvariant
  | .conditional _ opens branches =>
      opens.all postElabInvariant &&
      branches.all (fun b => postElabInvariantAlg b.body)
end

end KatLang
