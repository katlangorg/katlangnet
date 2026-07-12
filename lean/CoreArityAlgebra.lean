/-
Core arity algebra definitions.

This file intentionally contains only the definition layer of the core
arity algebra used in the paper. It distinguishes:

- temporary item supplies (`Supply`) from persistent values (`Val`), with
  `Val.seq` as raw sequence construction;
- the total item view `items`, the formal meaning of KatLang's surface
  spread operator `...`;
- persistent-value canonicalization `normalize`, with `capture` /
  `captureVariadic` as the canonicalizing capture boundaries;
- deconstruction-specific lone-sequence opening of a supply,
  `openLoneSequence`;
- the shared name/rest binder `bindPats`, consumed by ordinary call binding
  (`bindArgs`) and by deconstruction binding (`bindDeconstruct`).

Proofs and executable checks are kept in CoreArityAlgebraProofs.lean.

Provenance table / implementation correspondence:

CoreArityAlgebra.lean           KatLang.lean correspondence
-------------------------------------------------------------
Val / Supply                    Result values and item supplies
Val.seq                         Result.sequenceValue
sequenceItems?                  artifact-local structural projection (the
                                full model pattern-matches
                                Result.sequenceValue payloads directly)
items                           Result.toItems
normalize                       Result.normalize
capture                         Result.normalize after Result.sequenceValue
openLoneSequence                normalizeSingletonBoundaryForItemSupplyOf /
                                normalizeSingletonBoundaryForItemSupply
                                (sequence-builtin collection binding; the
                                deconstruction receiver reaches the same
                                one-boundary opening via the sequence-value
                                parameter pattern, not via this function)
captureVariadic                 variadic call argument capture
Pat / bindArgs / bindDeconstruct / bindPats
                                bindParameterPatternList name/rest binding model;
                                bindDeconstruct adds the deconstruction-receiver
                                lone-sequence opening (SequenceValueParameterPattern)

This file is not a full semantics of KatLang. It isolates only the arity
machinery used by the paper.
-/

namespace CoreArityAlgebra

inductive Val where
  | atom : Int -> Val
  | seq  : List Val -> Val

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
  | Val.atom _ => none

/--
The total item view of a value.

An atom supplies itself as one item; a sequence value supplies its stored
items. This operation gives the formal meaning of KatLang's surface spread
operator `...`. It opens only the outermost sequence boundary: nested
sequence values remain single items and are not recursively flattened.
-/
def items : Val -> Supply
  | Val.atom n => [Val.atom n]
  | Val.seq xs => xs

mutual
  /--
  Canonicalizes a persistent value by recursively removing redundant
  singleton sequence boundaries. This is value-level canonicalization: it
  defines the canonical form of one stored value. It does not prepare item
  supplies for binding — deconstruction-specific supply preparation is the
  separate `openLoneSequence`.
  -/
  def normalize : Val -> Val
    | Val.atom n => Val.atom n
    | Val.seq xs =>
        match normalizeList xs with
        | [v] => v
        | ys  => Val.seq ys

  def normalizeList : List Val -> List Val
    | [] => []
    | x :: xs => normalize x :: normalizeList xs
end

/-- `Val.seq xs` is raw sequence construction. `capture xs` is the canonical
value-capture boundary: it groups the supplied items and normalizes the
result, so singleton sequence boundaries are erased before the captured value
is observed.

Raw `Val.seq` may still be appropriate internally, for example when modeling
syntax, pre-normalization structure, or already-canonical shallow combination
(the full model's `combineOutputSlots` / `combineCollectionResult`, which
coincide with `normalize` on canonical items). The invariant is only that
observable capture/construction boundaries must not mint literal-unwritable
singleton "orphan" values such as a stored `(5)` that compares unequal to `5`.

Equality remains ordinary structural equality; missed canonicalization should
be fixed at the construction/capture boundary, not inside equality. -/
def capture (xs : Supply) : Val := normalize (Val.seq xs)

/--
Deconstruction-specific lone-sequence opening.

If the complete item supply consists of exactly one sequence value, this
operation removes that one outer sequence boundary; every other supply —
empty, a lone atom, or two or more items — is unchanged. It does not
recursively normalize the values inside the supply.

It prepares the supply for assignment-deconstruction binding
(`bindDeconstruct`); in the full model the same one-boundary opening also
underlies sequence-builtin collection binding. It is NOT applied by
function-call binding (`bindArgs`): a stored sequence value is reopened for
a call only by an explicit spread.
-/
def openLoneSequence : Supply -> Supply
  | [Val.seq xs] => xs
  | xs => xs

def captureVariadic (xs : Supply) : Val := capture xs

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
                  ++ (restPat.key, capture midVals)
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
Assignment deconstruction applies lone-sequence opening before the shared
name/rest binder: a lone sequence-valued right-hand side `A` is opened into
its items and matched element-by-element, so `x, y, z = A` splits `A`, and
`x, y, z = A...` supplies the same items. The opening is
deconstruction-specific: ordinary call binding (`bindArgs`) does not perform
it, so `Add(A)` stays one argument while `Add(A...)` opens.
-/
def bindDeconstruct (ps : List Pat) (xs : Supply) : Option Env :=
  bindPats ps (openLoneSequence xs)

end CoreArityAlgebra
