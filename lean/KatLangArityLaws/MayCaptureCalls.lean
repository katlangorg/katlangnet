import KatLang

/-!
# The program gate of invocation-plan retention, in Lean (ledger E-21; E-18's domain)

C# retains invocation plans only in a run whose admitted program MAY CAPTURE CALLS
(`AstStructuralPreflight.MayCaptureCalls`, "J7"); in every other run a call written as an argument
is an ordinary cell. Lean plans every such call (`NeedDemand.suspendedValue`). This module states
the gate as a Lean predicate over the Lean AST, so that "a program that cannot capture calls" is a
definition proofs can use:

* `Expr.mayCaptureCalls` / `Algorithm.mayCaptureCalls` / `ScopeCtx.mayCaptureCalls`.

A node fires the gate when it is

* a `meta` capture of a parameter list, at any depth (`ParameterPattern.anyHasMetaCapture`; C#:
  `IsMetaBinder`, a `CaptureParameterPattern` of kind `Meta`). Lean's clause binder `Pattern.bind`
  has no META kind (it carries only its collecting flag), so the clause-binder half of C#'s clause has no Lean form
  (`ParameterPattern.metaViolation?`'s note: the C# front end and preflight reject one);
* a name `Expr.resolve` or a dot edge `Expr.dotMember` spelled with the prelude name of a builtin
  whose signature declares a `meta` parameter (`metaBuiltinNames`: `while`, `repeat`), whatever it
  resolves to (C#: `BuiltinRegistry.MetaBuiltinNames`);
* a builtin node `Algorithm.builtin` whose signature declares one (`builtinDeclaresMeta`).

C#'s first clause, a deferred module region, has no Lean form: Lean has no loader and no deferred
region. A C# tree that holds one is outside every Lean comparison.

The walk is C#'s child enumeration (`AstStructuralPreflight.TryGetChild`): an algorithm's attached
parent scope, opens, property values, output rows, clause branches (pattern and body) and parameter
patterns; an alias's target row; and every subexpression, including a dot edge's elaborated
fallback and arguments. At a parent scope the walk follows its parent, opens and property values.
Lean additionally retains `output` and `branches` there for owner reconstruction. These fields
have no C# scope counterpart and the encoder emits them empty. The prelude
is not part of a program and is not walked, which is why the builtin clause keys on the spelled
name.

This module imports `KatLang` only: the generated agreement file
(`KatLangArityLaws/MayCaptureCallsCorpus.lean`) depends on no proof.
-/

namespace KatLang

/-- The prelude names of the builtins whose signature declares a `meta` parameter, read from the
    prelude itself (`preludeAlg`, `builtinDeclaresMeta`). C#: `BuiltinRegistry.MetaBuiltinNames`. -/
def metaBuiltinNames : List Ident :=
  match preludeAlg with
  | .mk _ _ _ properties _ _ =>
      properties.filterMap fun property =>
        match property.alg with
        | .builtin b => if builtinDeclaresMeta b then some property.name else none
        | _ => none
  | _ => []

/-- Whether `name` is the prelude name of a builtin that declares a `meta` parameter. -/
def isMetaBuiltinName (name : Ident) : Bool := metaBuiltinNames.contains name

mutual
  /-- Whether an expression may capture calls: the gate over the expression's own nodes and every
      node its walk reaches. C#: `AstStructuralPreflight.MayCaptureCalls` over
      `CheckAdmittedProgram`'s walk. -/
  def Expr.mayCaptureCalls : Expr → Bool
    | .param _ => false
    | .num _ => false
    | .stringLiteral _ => false
    | .boolLiteral _ => false
    | .emptySequence _ => false
    | .resolve name => isMetaBuiltinName name
    | .unary _ operand => Expr.mayCaptureCalls operand
    | .binary _ a b => Expr.mayCaptureCalls a || Expr.mayCaptureCalls b
    | .comparison first links => Expr.mayCaptureCalls first || mayCaptureCallsLinks links
    | .index receiver selectors => Expr.mayCaptureCalls receiver || mayCaptureCallsExprs selectors
    | .sequenceConstruct a b => Expr.mayCaptureCalls a || Expr.mayCaptureCalls b
    | .sequenceSpread operand => Expr.mayCaptureCalls operand
    | .listLiteral items => mayCaptureCallsExprs items
    | .algorithmExpr a => Algorithm.mayCaptureCalls a
    | .capture rows => mayCaptureCallsExprs rows
    | .call callee arguments => Expr.mayCaptureCalls callee || mayCaptureCallsExprs arguments
    | .dotMember target name fallback arguments =>
        isMetaBuiltinName name || Expr.mayCaptureCalls target || Expr.mayCaptureCalls fallback ||
          mayCaptureCallsOptExprs arguments

  /-- The gate over a list of expressions (rows, arguments, selectors, opens). -/
  def mayCaptureCallsExprs : List Expr → Bool
    | [] => false
    | e :: rest => Expr.mayCaptureCalls e || mayCaptureCallsExprs rest

  /-- The gate over a dot edge's optional argument list. -/
  def mayCaptureCallsOptExprs : Option (List Expr) → Bool
    | none => false
    | some items => mayCaptureCallsExprs items

  /-- The gate over a comparison chain's links. -/
  def mayCaptureCallsLinks : List ComparisonLink → Bool
    | [] => false
    | link :: rest => mayCaptureCallsLink link || mayCaptureCallsLinks rest

  /-- The gate over one comparison link: its operand. -/
  def mayCaptureCallsLink : ComparisonLink → Bool
    | ⟨_, operand⟩ => Expr.mayCaptureCalls operand

  /-- Whether an algorithm may capture calls. A builtin node fires when its signature declares a
      `meta` parameter; a user algorithm when a parameter pattern holds a `meta` capture; every
      variant through the nodes its walk reaches, its attached parent scope included. -/
  def Algorithm.mayCaptureCalls : Algorithm → Bool
    | .builtin b => builtinDeclaresMeta b
    | .mk parent patterns opens properties output _ =>
        mayCaptureCallsOptScope parent || ParameterPattern.anyHasMetaCapture patterns ||
          mayCaptureCallsExprs opens || mayCaptureCallsProps properties || mayCaptureCallsExprs output
    | .conditional parent opens branches _ =>
        mayCaptureCallsOptScope parent || mayCaptureCallsExprs opens || mayCaptureCallsBranches branches
    | .alias parent opens properties target _ _ =>
        mayCaptureCallsOptScope parent || mayCaptureCallsExprs opens ||
          mayCaptureCallsProps properties || Expr.mayCaptureCalls target

  /-- Whether a scope level, or a level above it, may capture calls. -/
  def ScopeCtx.mayCaptureCalls : ScopeCtx → Bool
    | .mk parent _ opens properties _ _ _ _ =>
        mayCaptureCallsOptScope parent || mayCaptureCallsExprs opens || mayCaptureCallsProps properties

  /-- The gate over an optional parent scope. -/
  def mayCaptureCallsOptScope : Option ScopeCtx → Bool
    | none => false
    | some scope => ScopeCtx.mayCaptureCalls scope

  /-- The gate over a property list: each property's algorithm. -/
  def mayCaptureCallsProps : List PropDef → Bool
    | [] => false
    | property :: rest => mayCaptureCallsProp property || mayCaptureCallsProps rest

  /-- The gate over one property: its algorithm. -/
  def mayCaptureCallsProp : PropDef → Bool
    | ⟨_, a, _, _, _, _⟩ => Algorithm.mayCaptureCalls a

  /-- The gate over a clause family's branches. -/
  def mayCaptureCallsBranches : List CondBranch → Bool
    | [] => false
    | branch :: rest => mayCaptureCallsBranch branch || mayCaptureCallsBranches rest

  /-- The gate over one branch: its body (a Lean clause pattern holds no `meta` binder). -/
  def mayCaptureCallsBranch : CondBranch → Bool
    | ⟨_, body⟩ => Algorithm.mayCaptureCalls body
end

end KatLang
