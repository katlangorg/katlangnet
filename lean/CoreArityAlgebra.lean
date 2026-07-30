/-
Core arity algebra definitions.

This file intentionally contains only the definition layer of the core
arity algebra used in the paper. It distinguishes:

- temporary item supplies (`Supply`) from persistent values (`Val`), with
  `Val.seq` as raw sequence construction and `Val.list` as the exact
  immutable list value;
- the total item view `items`, the formal meaning of KatLang's surface
  spread marker (the one spelling `expr*`,
  with semantic direction `spread : Value -> Supply`);
- persistent-value canonicalization `normalize`, with `capture` as the
  canonicalizing ordinary value-capture boundary
  (`capture : Supply -> Value`), and `canonicalSupply` as the invariant that
  an observable item supply already holds canonical values;
- exact segment collection `collect`, the collecting-binding operation
  (`collect : Supply -> ListValue`, implemented as `Supply -> Val` with a
  proven `Val.list` result kind);
- the shared openable-structure projection `structureItems?` with the
  deconstruction-specific lone-structure opening of a supply,
  `openLoneStructure`, and its characterizing predicate `loneStructure`;
- the shared fixed/collecting binder `bindPats`, consumed by ordinary call binding
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
structureItems?                 Result.structureItems? (the shared
                                deconstruction-openable structure view: a
                                sequence or list value opens to its items)
items                           Result.spreadItems (the spread-marker view,
                                which opens one sequence OR list boundary;
                                the full model's non-spread `Result.toItems`
                                keeps lists opaque and is not modeled here)
normalize                       Result.normalize
capture                         Result.normalize after Result.sequenceValue
canonicalSupply                 invariant of observable supplies (the full
                                model normalizes at every construction
                                boundary rather than naming the invariant)
collect                         collectSegment (exact immutable list collection)
openLoneStructure               deconstruction receiver opening of a lone
                                sequence or lone list
                                ((Result.structureItems? value).getD [value]
                                inside the sequence-value parameter pattern
                                binder); the collection builtins'
                                POST-BINDING view builtinCollectionItems
                                applies the same one-boundary opening to the
                                bound `collection` argument
loneStructure                   artifact-local characterization of the one
                                supply shape openLoneStructure rewrites
Pat / bindArgs / bindDeconstruct / bindPats
                                bindParameterPatternList fixed/collecting-binding model;
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
surface spread marker: surface spread is total and is modeled by `items`.
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
The shared openable-structure projection: the stored items of either
collection kind. A sequence value or an exact list value projects to its
immediate items; an atom is not an openable structure.

This is the deconstruction receiver's structure view (the full model's
`Result.structureItems?`): `openLoneStructure` opens a single received value
through it, with a one-item fallback for non-structures. It is partial where
`items` (surface spread) is total — spread supplies an atom as itself, while
deconstruction distinguishes "openable structure" from "scalar". The
kind-specific projections `sequenceItems?` / `listItems?` remain for
constructor-section laws; this projection unifies their openable half.
-/
def structureItems? : Val -> Option Supply
  | Val.seq xs => some xs
  | Val.list xs => some xs
  | _ => none

/--
The total item view of a value: `spread : Value -> Supply`.

An atom supplies itself as one item; a sequence value supplies its stored
items; an exact list value supplies its stored elements. This operation gives
the formal meaning of KatLang's surface spread marker. It opens only
the outermost structure boundary: nested sequence and list values remain
single items and are not recursively flattened.

Because `items v` is a `Supply`, a further spread cannot apply to it
directly: the second star of a repeated surface spread applies across an
ordinary capture boundary, so the arity interpretation of both `value**` and
`(value*)*` is `items (capture (items v))` — see the repeated-spread section
of `CoreArityAlgebraProofs.lean` for its exact cardinality laws.
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
`(1, 2, 3)`; one supplied item captures as itself). Collecting binding does NOT use
this operation — collecting binding is `collect`.

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
The canonical-supply invariant: every value in the supply is already in
canonical form (`normalizeList xs = xs`, equivalently `normalize v = v` for
each member — `canonicalSupply_iff_forall`).

The abstract `Supply` type admits raw non-canonical members, but observable
runtime supplies satisfy this invariant: they are assembled from literals,
canonical stored values, and spreads of canonical values (opening a canonical
value yields a canonical supply — `canonicalSupply_items_of_canonical`), and
every construction/capture boundary normalizes before storing. The invariant
is what makes `collect` exactness meaningful without extra work: `collect`
preserves the number, order, kinds, and boundaries of the supplied values
as-is, and canonicality of the input — not renormalization inside `collect` —
guarantees the collected list is canonical
(`normalize_collect_of_canonicalSupply`).
-/
def canonicalSupply (xs : Supply) : Prop := normalizeList xs = xs

/--
Exact segment collection: `collect : Supply -> ListValue`.

Every collecting binding — deconstruction collecting bindings, single collecting parameters, and
mixed prefix/collecting/suffix parameter lists — materializes its assigned item
supply as one EXACT immutable list value: `collect [] = []`,
`collect [v] = [v]` (never erased to the item), `collect [v, w] = [v, w]`.
The implementation type is `Supply -> Val`; the proofs establish that the
result is always `Val.list` with exactly the assigned items
(`collect_is_list`, `items_collect`). The round trip
`items (collect xs) = xs` makes collecting-parameter forwarding ordinary
list spread.

This supersedes the pre-list `captureVariadic := capture` model, under which
collecting binding canonicalized to a sequence value and a singleton collected segment collapsed
to its item. That coincidence-based model (grouped call `F(A)` agreeing with
spread call `F(A*)` for a single collecting parameter) is intentionally obsolete:
`collect` preserves the boundary around every assigned item, so the two calls
are observably different.
-/
def collect (xs : Supply) : Val := Val.list xs

/--
Deconstruction-specific lone-structure opening.

If the complete item supply consists of exactly one openable structure — one
sequence value or one exact list value (`structureItems?`) — this operation
removes that one outer boundary; every other supply — empty, a lone atom, or
two or more items — is unchanged. It does not recursively normalize the
values inside the supply.

It prepares the supply for assignment-deconstruction binding
(`bindDeconstruct`); in the full model the same one-boundary opening also
underlies the collection builtins' post-binding collection view. Those are
two runtime code paths with the same one-boundary behaviour, unified here as
one operation — not a claim that assignment deconstruction and collection
builtins share one runtime call path. It is NOT applied by function-call
binding (`bindArgs`): a stored sequence or list value is re-spread for a call
only by an explicit spread.

(Before exact list values entered the algebra this operation was named
`openLoneSequence` and opened lone sequence values only.)
-/
def openLoneStructure : Supply -> Supply
  | [v] => (structureItems? v).getD [v]
  | xs => xs

/--
Characterizes exactly the supplies `openLoneStructure` rewrites: a single
openable structure value — `[Val.seq ys]` or `[Val.list ys]`. On every supply
with `loneStructure xs = false` the call and deconstruction receivers agree
(`receivers_agree_outside_lone_structure`); on every supply with
`loneStructure xs = true` they never share a successful binding
(`receivers_never_same_on_lone_structure`).
-/
def loneStructure : Supply -> Bool
  | [v] => (structureItems? v).isSome
  | _ => false

inductive Pat where
  | name : String -> Pat
  | collecting : String -> Pat

abbrev Env := List (String × Val)

def Pat.key : Pat -> String
  | Pat.name s => s
  | Pat.collecting s => s

def Pat.isCollecting : Pat -> Bool
  | Pat.collecting _ => true
  | Pat.name _ => false

def bindFixed (ps : List Pat) (vs : Supply) : Env :=
  List.zipWith (fun p v => (p.key, v)) ps vs

def bindPats (ps : List Pat) (xs : Supply) : Option Env :=
  match ps.filter Pat.isCollecting with
  | [] =>
      if ps.length = xs.length then some (bindFixed ps xs) else none
  | [collectingPat] =>
      match ps.findIdx? Pat.isCollecting with
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
                  ++ (collectingPat.key, collect midVals)
                     :: bindFixed back backVals)
  | _ => none

/-- Function-call binding consumes the call's item supply exactly as supplied.

A lone collecting pattern is valid here: it models the single collecting
parameter, `bindArgs [Pat.collecting x] xs`. The lone-collecting surface
assignment `*x = 1, 2, 3` is the deconstruction receiver's instance of the same shape (see `bindDeconstruct`).
-/
def bindArgs (ps : List Pat) (xs : Supply) : Option Env :=
  bindPats ps xs

/--
Assignment deconstruction applies lone-structure opening before the shared
fixed/collecting binder: a lone sequence- or list-valued right-hand side `A` is
opened into its items and matched element-by-element, so `x, y, z = A` splits
`A`. At this receiver boundary, `bindDeconstruct ps [A]` therefore binds the
same immediate supply that `bindArgs ps (items A)` receives. This is not an
unrestricted surface rewrite from `x, y = A` to `x, y = A*`: a written
deconstruction RHS is captured before this receiver runs, and that capture can
erase a singleton sequence boundary before the receiver opens again (pinned by
`deconstruct_spread_capture_can_open_further`). The opening remains
deconstruction-specific: ordinary call binding (`bindArgs`) does not perform
it, so `Add(A)` stays one argument while `Add(A*)` opens.
-/
def bindDeconstruct (ps : List Pat) (xs : Supply) : Option Env :=
  bindPats ps (openLoneStructure xs)

end CoreArityAlgebra
