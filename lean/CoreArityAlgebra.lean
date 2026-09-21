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
- persistent-value normalization `normalize`, with `capture` as the
  normalizing ordinary value-capture boundary
  (`capture : Supply -> Value`), and `canonicalSupply` as the invariant that
  an observable item supply already holds canonical values;
- exact segment collection `collect`, the collecting-binding operation
  (`collect : Supply -> ListValue`, implemented as `Supply -> Val` with a
  proven `Val.list` result kind);
- the shared openable-structure projection `structureItems?` with the
  deconstruction-specific lone-structure opening of a supply,
  `openLoneStructure`, and its characterizing predicate `loneStructure`;
- the shared fixed/collecting binder `bindPats`, consumed by ordinary call binding
  (`bindArgs`) and by deconstruction binding (`bindDeconstruct`);
- the call supply `CallSupply` — each supplied item with its `Origin`
  (a non-spread written slot, or an item explicit spread already produced) —
  and the COLLECTOR SUPPLY-BOUNDARY LAW `collectorSupply` /
  `fuseCollectorSegment` that `bindArgs` applies to the collector's
  allocated segment (September 2026): a lone written sequence slot stands for
  the collector's whole supply, exactly one level; everything else is
  collected exactly.

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
collect                         collectSegment (exact list collection)
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
Origin / CallSupply             SupplyOrigin (`writtenSlot` / `finalItem`) on
                                ParameterPatternInput / VariadicItem, recorded by
                                collectVariadicCallItems
collectorSupply                 collectorSupply (the collector supply-boundary
                                law on the allocated segment)
fuseCollectorSegment            the same law expressed as a call-supply
                                preparation: the full model applies
                                collectorSupply inside bindParameterPatternList
                                to the segment it allocated, which is the same
                                segment this preparation rewrites
Pat / bindArgs / bindDeconstruct / bindPats
                                bindParameterPatternList fixed/collecting-binding model;
                                bindArgs adds the collector supply-boundary law
                                on the collector's segment, bindDeconstruct the
                                deconstruction-receiver lone-structure opening

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
never normalized away, so this projection is a section of the constructor
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
  Normalizes a persistent value by recursively removing redundant
  singleton sequence boundaries. This is value-level sequence normalization: it
  defines the canonical form of one stored value. List values are exact:
  their elements normalize, but the list boundary itself never collapses
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

Equality remains ordinary structural equality; missed normalization should
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
supply as one EXACT list value: `collect [] = []`,
`collect [v] = [v]` (never erased to the item), `collect [v, w] = [v, w]`.
The implementation type is `Supply -> Val`; the proofs establish that the
result is always `Val.list` with exactly the assigned items
(`collect_is_list`, `items_collect`). The round trip
`items (collect xs) = xs` makes collecting-parameter forwarding ordinary
list spread.

This supersedes the pre-list `captureVariadic := capture` model, under which
collecting binding normalized to a sequence value and a singleton collected segment collapsed
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
builtins share one runtime call path. It is NOT applied by call-argument
binding (`bindArgs`): a call opens a lone written SEQUENCE only where it is a
collector's entire allocated segment (`fuseCollectorSegment`), never a lone
list and never for a fixed pattern; otherwise a stored value is re-spread for
a call only by an explicit spread.

(Before exact list values entered the algebra this operation was named
`openLoneSequence` and opened lone sequence values only.)
-/
def openLoneStructure : Supply -> Supply
  | [v] => (structureItems? v).getD [v]
  | xs => xs

/--
Characterizes exactly the supplies `openLoneStructure` rewrites: a single
openable structure value — `[Val.seq ys]` or `[Val.list ys]`. On every FINAL
supply with `loneStructure xs = false` the call and deconstruction receivers
agree (`receivers_agree_outside_lone_structure`); on a lone written LIST they
never share a successful binding (`receivers_never_same_on_lone_list`), on a
lone written SEQUENCE they never share one for any pattern list with a fixed
position (`receivers_never_same_on_lone_seq_with_fixed`) and coincide exactly
at the lone collecting pattern (`receivers_agree_on_lone_seq_lone_collecting`),
where the collector supply-boundary law opens the sequence one level.
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

/--
The supply origin of one call-argument slot — the ONE provenance fact the
collector supply-boundary law reads (full model: `SupplyOrigin`).

- `written`: a non-spread written argument slot (a written argument, the
  extension dot-call receiver, a whole callback item). It is one value; when
  it is the collector's ENTIRE allocated segment and holds a sequence value,
  that sequence may fuse with the collector's supply boundary.
- `final`: an item that a boundary opening already produced — an explicit
  spread item, a callback row slot, a sequence-value pattern item, a
  loop-state slot, a reducer accumulator slot. Final items are collected
  exactly.

This is slot provenance, never result provenance: `written [Val.seq ys]`
(`Coll((1, 2))`) and `final [Val.seq ys]` (`Coll([(1, 2)]*)`) hold the same
value and bind differently, while every origin of that value — a literal, a
property, a call result, a selection — is the same written slot.
-/
inductive Origin where
  | written
  | final
  deriving Repr, DecidableEq

/-- A call's argument supply: each supplied item with its origin. -/
abbrev CallSupply := List (Val × Origin)

/-- The supply of non-spread written slots (`F(a, b, c)`). -/
def written (xs : Supply) : CallSupply := xs.map (fun v => (v, Origin.written))

/-- The supply of final items (`F(A*)`: the items explicit spread produced). -/
def final (xs : Supply) : CallSupply := xs.map (fun v => (v, Origin.final))

/-- The values of a call supply, origins forgotten. -/
def values (xs : CallSupply) : Supply := xs.map Prod.fst

/-- The one shape the collector supply-boundary law rewrites: a segment that is
exactly one written slot holding a sequence value, projected to its items. -/
def loneWrittenSeq? : CallSupply -> Option Supply
  | [(Val.seq ys, Origin.written)] => some ys
  | _ => none

/--
THE COLLECTOR SUPPLY-BOUNDARY LAW, on the segment allocated to a collecting
binding: several supplied items are collected exactly as supplied; ONE lone
non-spread sequence value may stand for the collector's whole supply, so its
immediate items are the supply — exactly one level (`collectorSupply
(written [Val.seq ys]) = ys`, hence `Coll((1, 2))` is `[1, 2]`,
`Coll(((1, 2), 3))` is `[(1, 2), 3]`, and `Coll(())` is `[]` by the same rule);
lists are exact values and never open here; a final item is collected
unchanged even when it is the lone item (`Coll([(1, 2)]*)` is `[(1, 2)]`).
-/
def collectorSupply (segment : CallSupply) : Supply :=
  match loneWrittenSeq? segment with
  | some ys => ys
  | none => values segment

/--
The collector supply-boundary law as a call-supply preparation for the shared
binder: locate the collector's allocated segment exactly as `bindPats` will
(`i` fixed patterns before it, `suffixCount` after it); when that segment is
exactly ONE slot holding a written sequence value, replace the slot by the
sequence's items; every other supply — no collector, an under-supplied call,
a segment of several items, a lone list, a lone atom, a lone final item —
keeps its values unchanged. Because front/back allocation is decided by
counts, `bindPats ps (fuseCollectorSegment ps xs)` allocates the same fixed
items as the unfused supply and gives the collector `collectorSupply` of its
segment — which is exactly what the full model does inside
`bindParameterPatternList` after allocation.
-/
def fuseCollectorSegment (ps : List Pat) (xs : CallSupply) : Supply :=
  match ps.findIdx? Pat.isCollecting with
  | none => values xs
  | some i =>
      let suffixCount := (ps.drop (i + 1)).length
      let segment := (xs.drop i).take (xs.length - suffixCount - i)
      match loneWrittenSeq? segment with
      | some ys => values (xs.take i) ++ ys ++ values (xs.drop (xs.length - suffixCount))
      | none => values xs

/-- Call-argument binding: fixed front/back captures bind the supplied values
unchanged, and the collector consumes its allocated segment through the
collector supply-boundary law (`fuseCollectorSegment`), so
`bindArgs [Pat.collecting x] (written [Val.seq ys])` binds `x` to
`collect ys` while `bindArgs [Pat.collecting x] (final [Val.seq ys])` binds it
to `collect [Val.seq ys]`. A lone collecting pattern is valid here: it models
the single collecting parameter. The lone-collecting surface assignment
`*x = 1, 2, 3` is the deconstruction receiver's instance of the same shape
(see `bindDeconstruct`).
-/
def bindArgs (ps : List Pat) (xs : CallSupply) : Option Env :=
  bindPats ps (fuseCollectorSegment ps xs)

/--
Assignment deconstruction applies lone-structure opening before the shared
fixed/collecting binder: a lone sequence- or list-valued right-hand side `A` is
opened into its items and matched element-by-element, so `x, y, z = A` splits
`A`. At this receiver boundary, `bindDeconstruct ps [A]` therefore binds the
same immediate supply that `bindArgs ps (final (items A))` receives. This is
not an unrestricted surface rewrite from `x, y = A` to `x, y = A*`: a written
deconstruction RHS is captured before this receiver runs, and that capture can
erase a singleton sequence boundary before the receiver opens again (pinned by
`deconstruct_spread_capture_can_open_further`). The opening remains
deconstruction-specific: ordinary call binding (`bindArgs`) opens nothing for
a FIXED pattern (`Add(A)` stays one argument while `Add(A*)` opens) and never
opens a lone LIST; only a collector's lone written sequence slot fuses with
the collector's own boundary (`fuseCollectorSegment`), which is why
`Coll(A)` and `*x = A` agree for a sequence `A` and differ for a list.
-/
def bindDeconstruct (ps : List Pat) (xs : Supply) : Option Env :=
  bindPats ps (openLoneStructure xs)

end CoreArityAlgebra
