/-
Core arity algebra definitions.

This file intentionally contains only the definition layer of the core
arity algebra used in the paper: values, item supplies, raw sequence
construction, the items operation, capture, singleton-boundary normalization,
variadic capture, and name/rest binding.

Proofs and executable checks are kept in CoreArityAlgebraProofs.lean.

Provenance table / implementation correspondence:

CoreArityAlgebra.lean           KatLang.lean correspondence
-------------------------------------------------------------
Val / Supply                    Result values and item supplies
Val.seq                         Result.sequenceValue
spread                          structural sequence-value opening
items                           Result.toItems
normalize                       Result.normalize
capture                         Result.normalize after Result.sequenceValue
normalizeSupply                 normalizeSingletonBoundaryForItemSupplyOf /
                                normalizeSingletonBoundaryForItemSupply
                                (sequence-builtin collection binding; the
                                deconstruction receiver reaches the same
                                one-boundary opening via the sequence-value
                                parameter pattern, not via this function)
captureVariadic                 variadic call argument capture
Pat / bindArgs / bindDeconstruct / bindPats
                                bindParameterPatternList name/rest binding model;
                                bindDeconstruct adds the deconstruction-receiver
                                singleton opening (SequenceValueParameterPattern)

This file is not a full semantics of KatLang. It isolates only the arity
machinery used by the paper.
-/

namespace CoreArityAlgebra

inductive Val where
  | atom : Int -> Val
  | seq  : List Val -> Val

abbrev Supply := List Val

def spread : Val -> Option Supply
  | Val.seq xs => some xs
  | Val.atom _ => none

def items : Val -> Supply
  | Val.atom n => [Val.atom n]
  | Val.seq xs => xs

mutual
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

/-- Singleton-boundary opening: while the supplied item supply is exactly one grouped
sequence value, that value IS the collection/receiver and is opened once into its
items. Used by assignment-deconstruction binding (`bindDeconstruct`, the unpacking
receiver) and sequence-builtin collection binding. It is NOT used by function-call
binding (`bindArgs`); a stored sequence value is reopened for a call only by an
explicit spread. -/
def normalizeSupply : Supply -> Supply
  | [v] => (spread v).getD [v]
  | xs  => xs

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

/-- Assignment-style deconstruction is an unpacking receiver (Python-style): a single
sequence-valued right-hand side `A` is opened into its items and matched
element-by-element, so `x, y, z = A` splits `A`. It applies `normalizeSupply` (the
deconstruction-receiver singleton opening) before the shared name/rest binder. This
opening is deconstruction-specific: `bindArgs` (function calls) does NOT open, so
`Add(A)` stays one argument while `Add(A...)` opens. -/
def bindDeconstruct (ps : List Pat) (xs : Supply) : Option Env :=
  bindPats ps (normalizeSupply xs)

end CoreArityAlgebra
