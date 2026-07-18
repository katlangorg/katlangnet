/-
Core arity algebra definitions.

This file intentionally contains only the definition layer of the core
arity algebra used in the paper. It distinguishes:

- temporary item supplies (`Supply`) from persistent values (`Val`), with
  `Val.seq` as raw sequence construction and `Val.list` as the exact
  immutable list value;
- the total item view `items`, the formal meaning of KatLang's surface
  spread operator `...` (`open : Value -> Supply`);
- persistent-value canonicalization `normalize`, with `capture` as the
  canonicalizing ordinary value-capture boundary
  (`capture : Supply -> Value`);
- exact rest collection `collect`, the rest/variadic binding operation
  (`collect : Supply -> ListValue`, implemented as `Supply -> Val` with a
  proven `Val.list` result kind);
- deconstruction-specific lone-structure opening of a supply,
  `openLoneStructure`;
- the shared name/rest binder `bindPats`, consumed by ordinary call binding
  (`bindArgs`) and by deconstruction binding (`bindDeconstruct`).

Proofs and executable checks are kept in CoreArityAlgebraProofs.lean.

Provenance table / implementation correspondence:

CoreArityAlgebra.lean           KatLang.lean correspondence
-------------------------------------------------------------
Val / Supply                    Result values and item supplies
Val.seq                         Result.sequenceValue
Val.list                        Result.listValue
sequenceItems? / listItems?     artifact-local structural projections (the
                                full model pattern-matches the payloads
                                directly)
items                           Result.spreadItems (the surface `...` view,
                                which opens one sequence OR list boundary;
                                the full model's non-spread `Result.toItems`
                                keeps lists opaque and is not modeled here)
normalize                       Result.normalize
capture                         Result.normalize after Result.sequenceValue
collect                         collectRest (exact immutable list collection)
openLoneStructure               deconstruction receiver opening of a lone
                                sequence or lone list
                                (SequenceValueParameterPattern via
                                Result.structureItems?); the collection
                                builtins' POST-BINDING view
                                builtinCollectionItems applies the same
                                one-boundary opening to the bound
                                `collection` argument
Pat / bindArgs / bindDeconstruct / bindPats
                                bindParameterPatternList name/rest binding model;
                                bindDeconstruct adds the deconstruction-receiver
                                lone-structure opening

This file is not a full semantics of KatLang. It isolates only the arity
machinery used by the paper.
-/

namespace CoreArityAlgebra

inductive Val where
  | atom : Int -> Val
  | seq  : List Val -> Val
  | list : List Val -> Val

abbrev Supply := List Val

/--
Returns the stored items when the value is a sequence value.

This is a partial structural projection, not the semantics of KatLang's
surface spread operator: surface spread is total and is modeled by `items`.
The projection observes raw sequence structure (`sequenceItems? (Val.seq [v])
= some [v]` even where `normalize` would erase the boundary), which the
proofs use to state section laws and to distinguish raw construction from
`capture`.
-/
def sequenceItems? : Val -> Option Supply
  | Val.seq xs => some xs
  | _ => none

/--
Returns the stored elements when the value is an exact list value.

The list twin of `sequenceItems?`. Unlike the sequence case, `Val.list` is
never canonicalized away, so this projection is a section of the constructor
on every payload, including singletons (`listItems? (collect [v]) = some [v]`).
-/
def listItems? : Val -> Option Supply
  | Val.list xs => some xs
  | _ => none

/--
The total item view of a value: `open : Value -> Supply`.

An atom supplies itself as one item; a sequence value supplies its stored
items; an exact list value supplies its stored elements. This operation gives
the formal meaning of KatLang's surface spread operator `...`. It opens only
the outermost structure boundary: nested sequence and list values remain
single items and are not recursively flattened.
-/
def items : Val -> Supply
  | Val.atom n => [Val.atom n]
  | Val.seq xs => xs
  | Val.list xs => xs

mutual
  /--
  Canonicalizes a persistent value by recursively removing redundant
  singleton sequence boundaries. This is value-level canonicalization: it
  defines the canonical form of one stored value. List values are exact:
  their elements canonicalize, but the list boundary itself never collapses
  (`[7]` stays `[7]`). It does not prepare item supplies for binding —
  deconstruction-specific supply preparation is the separate
  `openLoneStructure`.
  -/
  def normalize : Val -> Val
    | Val.atom n => Val.atom n
    | Val.seq xs =>
        match normalizeList xs with
        | [v] => v
        | ys  => Val.seq ys
    | Val.list xs => Val.list (normalizeList xs)

  def normalizeList : List Val -> List Val
    | [] => []
    | x :: xs => normalize x :: normalizeList xs
end

/-- `Val.seq xs` is raw sequence construction. `capture xs` is the canonical
ORDINARY value-capture boundary (`capture : Supply -> Value`): it groups the
supplied items and normalizes the result, so singleton sequence boundaries
are erased before the captured value is observed (`x = 1, 2, 3` captures
`(1, 2, 3)`; one supplied item captures as itself). Rest binding does NOT use
this operation — rest binding is `collect`.

Raw `Val.seq` may still be appropriate internally, for example when modeling
syntax, pre-normalization structure, or already-canonical shallow combination
(the full model's `combineOutputSlots`, which
coincides with `normalize` on canonical items). The invariant is only that
observable capture/construction boundaries must not mint literal-unwritable
singleton "orphan" values such as a stored `(5)` that compares unequal to `5`.

Equality remains ordinary structural equality; missed canonicalization should
be fixed at the construction/capture boundary, not inside equality. -/
def capture (xs : Supply) : Val := normalize (Val.seq xs)

/--
Exact rest collection: `collect : Supply -> ListValue`.

Every rest binding — deconstruction rest, rest-only variadic parameters, and
mixed prefix/rest/suffix parameter lists — materializes its assigned item
supply as one EXACT immutable list value: `collect [] = []`,
`collect [v] = [v]` (never erased to the item), `collect [v, w] = [v, w]`.
The implementation type is `Supply -> Val`; the proofs establish that the
result is always `Val.list` with exactly the assigned items
(`collect_is_list`, `items_collect`). The round trip
`items (collect xs) = xs` makes variadic forwarding ordinary list spread.

This supersedes the pre-list `captureVariadic := capture` model, under which
rest binding canonicalized to a sequence value and a singleton rest collapsed
to its item. That coincidence-based model (grouped call `F(A)` agreeing with
spread call `F(A...)` for rest-only parameters) is intentionally obsolete:
`collect` preserves the boundary around every assigned item, so the two calls
are observably different.
-/
def collect (xs : Supply) : Val := Val.list xs

/--
Deconstruction-specific lone-structure opening.

If the complete item supply consists of exactly one sequence value or exactly
one exact list value, this operation removes that one outer boundary; every
other supply — empty, a lone atom, or two or more items — is unchanged. It
does not recursively normalize the values inside the supply.

It prepares the supply for assignment-deconstruction binding
(`bindDeconstruct`); in the full model the same one-boundary opening also
underlies the collection builtins' post-binding collection view. It is NOT
applied by function-call binding (`bindArgs`): a stored sequence or list
value is reopened for a call only by an explicit spread.

(Before exact list values entered the algebra this operation was named
`openLoneSequence` and opened lone sequence values only.)
-/
def openLoneStructure : Supply -> Supply
  | [Val.seq xs] => xs
  | [Val.list xs] => xs
  | xs => xs

inductive Pat where
  | name : String -> Pat
  | rest : String -> Pat

abbrev Env := List (String × Val)

def Pat.key : Pat -> String
  | Pat.name s => s
  | Pat.rest s => s

def Pat.isRest : Pat -> Bool
  | Pat.rest _ => true
  | Pat.name _ => false

def bindFixed (ps : List Pat) (vs : Supply) : Env :=
  List.zipWith (fun p v => (p.key, v)) ps vs

def bindPats (ps : List Pat) (xs : Supply) : Option Env :=
  match ps.filter Pat.isRest with
  | [] =>
      if ps.length = xs.length then some (bindFixed ps xs) else none
  | [restPat] =>
      match ps.findIdx? Pat.isRest with
      | none => none
      | some i =>
          if xs.length < ps.length - 1 then none
          else
            let front       := ps.take i
            let back        := ps.drop (i + 1)
            let suffixCount := back.length
            let frontVals   := xs.take i
            let backVals    := xs.drop (xs.length - suffixCount)
            let midVals     := (xs.drop i).take (xs.length - suffixCount - i)
            some (bindFixed front frontVals
                  ++ (restPat.key, collect midVals)
                     :: bindFixed back backVals)
  | _ => none

/-- Function-call binding consumes the call's item supply exactly as supplied.

A lone rest pattern is valid here because it models variadic capture:
`bindArgs [Pat.rest x] xs`. This is an abstract binding shape, not a claim that
KatLang surface assignment accepts rest-only targets such as `x... = 1, 2, 3`.
-/
def bindArgs (ps : List Pat) (xs : Supply) : Option Env :=
  bindPats ps xs

/--
Assignment deconstruction applies lone-structure opening before the shared
name/rest binder: a lone sequence- or list-valued right-hand side `A` is
opened into its items and matched element-by-element, so `x, y, z = A` splits
`A`, and `x, y, z = A...` supplies the same items. The opening is
deconstruction-specific: ordinary call binding (`bindArgs`) does not perform
it, so `Add(A)` stays one argument while `Add(A...)` opens.
-/
def bindDeconstruct (ps : List Pat) (xs : Supply) : Option Env :=
  bindPats ps (openLoneStructure xs)

end CoreArityAlgebra
