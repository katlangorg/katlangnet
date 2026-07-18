/-
Proofs and executable checks for CoreArityAlgebra.

The definitions live in CoreArityAlgebra.lean. This file contains the
small laws, edge-case checks, and binding examples used by the paper and by
reviewers to validate the algebra.
-/

import CoreArityAlgebra

namespace CoreArityAlgebra

mutual
  def Val.decEq : (a b : Val) -> Decidable (a = b)
    | .atom m, .atom n =>
        if h : m = n then .isTrue (by rw [h]) else .isFalse (by intro he; cases he; exact h rfl)
    | .seq xs, .seq ys =>
        match Val.decEqList xs ys with
        | .isTrue h => .isTrue (by rw [h])
        | .isFalse h => .isFalse (by intro he; cases he; exact h rfl)
    | .list xs, .list ys =>
        match Val.decEqList xs ys with
        | .isTrue h => .isTrue (by rw [h])
        | .isFalse h => .isFalse (by intro he; cases he; exact h rfl)
    | .atom _, .seq _ => .isFalse (by intro he; cases he)
    | .atom _, .list _ => .isFalse (by intro he; cases he)
    | .seq _, .atom _ => .isFalse (by intro he; cases he)
    | .seq _, .list _ => .isFalse (by intro he; cases he)
    | .list _, .atom _ => .isFalse (by intro he; cases he)
    | .list _, .seq _ => .isFalse (by intro he; cases he)

  def Val.decEqList : (xs ys : List Val) -> Decidable (xs = ys)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro he; cases he)
    | _ :: _, [] => .isFalse (by intro he; cases he)
    | x :: xs, y :: ys =>
        match Val.decEq x y, Val.decEqList xs ys with
        | .isTrue hx, .isTrue ht => .isTrue (by rw [hx, ht])
        | .isFalse hx, _ => .isFalse (by intro he; cases he; exact hx rfl)
        | _, .isFalse ht => .isFalse (by intro he; cases he; exact ht rfl)
end

instance : DecidableEq Val := Val.decEq

theorem sequenceItems?_seq (xs : Supply) : sequenceItems? (Val.seq xs) = some xs := rfl

theorem listItems?_list (xs : Supply) : listItems? (Val.list xs) = some xs := rfl

theorem items_seq (xs : Supply) : items (Val.seq xs) = xs := rfl

/-- Spread opens one LIST boundary exactly like one sequence boundary
(`[1, 2, 3]...` supplies the items). -/
theorem items_list (xs : Supply) : items (Val.list xs) = xs := rfl

/-- Spreading the empty sequence contributes no items. -/
theorem items_empty :
    items (Val.seq []) = [] := rfl

/-- Spreading the empty list contributes no items either. -/
theorem items_empty_list :
    items (Val.list []) = [] := rfl

/-- An empty spread contributes nothing to a surrounding item supply. -/
theorem spread_empty_neutral (before after : Supply) :
    before ++ items (Val.seq []) ++ after = before ++ after := by
  simp [items]

theorem seq_items_seq (xs : Supply) : Val.seq (items (Val.seq xs)) = Val.seq xs := rfl

theorem seq_items_atom (n : Int) : Val.seq (items (Val.atom n)) = Val.seq [Val.atom n] := rfl

example : Val.seq (items (Val.atom 7)) ≠ Val.atom 7 := by decide

example : (Val.seq [Val.atom 1, Val.atom 2]) = (Val.seq [Val.atom 1, Val.atom 2]) := rfl

theorem nesting_matters :
    Val.seq [Val.atom 1, Val.seq [Val.atom 2, Val.atom 3]]
      ≠ Val.seq [Val.seq [Val.atom 1, Val.atom 2], Val.atom 3] := by
  decide

/-- A list value never equals the sequence value with the same elements: the
two collection kinds stay distinct. -/
theorem list_ne_seq (xs : Supply) : Val.list xs ≠ Val.seq xs := by
  intro he; cases he

theorem normalize_atom (n : Int) : normalize (Val.atom n) = Val.atom n := rfl

theorem normalize_empty : normalize (Val.seq []) = Val.seq [] := rfl

theorem normalize_singleton (v : Val) : normalize (Val.seq [v]) = normalize v := rfl

theorem normalize_nested_empty_collapses :
    normalize (Val.seq [Val.seq []]) = Val.seq [] := rfl

theorem normalize_deep_nested_empty_collapses :
  normalize (Val.seq [Val.seq [Val.seq []]]) = Val.seq [] := rfl

theorem normalize_keeps_pair (a b : Val) :
    normalize (Val.seq [a, b]) = Val.seq [normalize a, normalize b] := rfl

/-- List normalization is element-wise only: the boundary never collapses,
so `[7]` stays `[7]` and `[]` stays `[]`. -/
theorem normalize_list_exact (xs : Supply) :
    normalize (Val.list xs) = Val.list (normalizeList xs) := rfl

theorem normalize_singleton_list_kept (v : Val) :
    normalize (Val.list [v]) = Val.list [normalize v] := rfl

theorem capture_eq_normalize_seq (xs : Supply) :
    capture xs = normalize (Val.seq xs) := rfl

theorem capture_empty : capture [] = Val.seq [] := rfl

theorem capture_singleton (v : Val) : capture [v] = normalize v := rfl

theorem capture_singleton_empty : capture [Val.seq []] = Val.seq [] := rfl

theorem capture_singleton_atom (n : Int) : capture [Val.atom n] = Val.atom n := rfl

theorem capture_pair (a b : Val) :
    capture [a, b] = Val.seq [normalize a, normalize b] := rfl

theorem capture_singleton_atom_ne_seq :
    capture [Val.atom 1] ≠ Val.seq [Val.atom 1] := by
  decide

theorem sequenceItems?_capture_pair :
    sequenceItems? (capture [Val.atom 1, Val.atom 2])
      = some [Val.atom 1, Val.atom 2] := by
  decide

theorem sequenceItems?_capture_singleton_atom :
    sequenceItems? (capture [Val.atom 1]) = none := by
  decide

/-! ## Empty spread neutrality

`Val.seq []` is the empty sequence value `()`, and `items (Val.seq [])` is
the item supply of the explicit spread `()...`: it contributes zero items
(`items_empty`, `spread_empty_neutral`). The theorems below lift that
neutrality to `capture`, the canonical written-construction boundary. The
core model does not model root output, so the claims here are about item
supplies and captured values, not output emission.
-/

/-- An empty spread is neutral at a canonical capture or written-construction
boundary: `()...` contributes no items to the surrounding supply, so the
captured value is unchanged wherever the empty spread is inserted. -/
theorem capture_empty_spread_neutral
    (before after : Supply) :
    capture (before ++ items (Val.seq []) ++ after) =
      capture (before ++ after) :=
  congrArg capture (spread_empty_neutral before after)

/-- `(n, ()...) == n`. `Val.seq []` is the empty sequence value `()`,
`items (Val.seq [])` is its explicit spread `()...`, and the surrounding
`capture` is the canonical written-construction boundary. The spread
contributes zero items, so the boundary captures the one-item supply
`[Val.atom n]`, and singleton normalization returns the number itself
(`capture_singleton_atom`). The claim would not hold for the raw constructor:
`Val.seq [Val.atom n]` is deliberately distinct from `Val.atom n` before
canonicalization (`capture_singleton_atom_ne_seq`). -/
theorem capture_atom_empty_spread (n : Int) :
    capture ([Val.atom n] ++ items (Val.seq [])) = Val.atom n := by
  calc
    capture ([Val.atom n] ++ items (Val.seq []))
        = capture [Val.atom n] := by
          simpa using capture_empty_spread_neutral [Val.atom n] []
    _ = Val.atom n := capture_singleton_atom n

theorem openLoneStructure_empty : openLoneStructure [] = [] := rfl

theorem openLoneStructure_singleSeq (xs : Supply) :
    openLoneStructure [Val.seq xs] = xs := rfl

/-- Deconstruction opens a lone LIST exactly like a lone sequence value. -/
theorem openLoneStructure_singleList (xs : Supply) :
    openLoneStructure [Val.list xs] = xs := rfl

theorem openLoneStructure_singleAtom (n : Int) :
    openLoneStructure [Val.atom n] = [Val.atom n] := rfl

theorem openLoneStructure_multi (a b : Val) (rest : Supply) :
    openLoneStructure (a :: b :: rest) = a :: b :: rest := by
  cases a <;> rfl

theorem openLoneStructure_nested_empty_opens_one_boundary :
    openLoneStructure [Val.seq [Val.seq []]] = [Val.seq []] := rfl

/-! ## Exact rest collection (`collect`)

`collect : Supply -> ListValue` is the rest/variadic binding operation.
The laws below establish the required exactness properties: stable result
kind, exact length and elements, singleton preservation, the open/collect
round trip, and provenance independence. They intentionally supersede the
pre-list `captureVariadic := capture` coincidence model.
-/

/-- Stable result kind + exact elements: `collect` always produces the exact
list of precisely the assigned items (`listItems?` is total on collect
results — a section law that `capture` deliberately fails on singletons). -/
theorem collect_is_list (xs : Supply) : listItems? (collect xs) = some xs := rfl

/-- Exact length: collecting never adds, drops, or merges items. -/
theorem collect_length (xs : Supply) : (items (collect xs)).length = xs.length := rfl

/-- Zero assigned items collect to the empty list `[]` — a visible exact
value, never the empty sequence value `()`. -/
theorem collect_empty : collect [] = Val.list [] := rfl

theorem collect_empty_ne_empty_seq : collect [] ≠ Val.seq [] := by decide

/-- Singleton preservation: one assigned item collects to the one-element
list `[v]`, for every value kind. -/
theorem collect_singleton (v : Val) : collect [v] = Val.list [v] := rfl

example : collect [Val.atom 7] = Val.list [Val.atom 7] := rfl
example : collect [Val.seq []] = Val.list [Val.seq []] := rfl
example : collect [Val.list []] = Val.list [Val.list []] := rfl
example : collect [Val.seq [Val.atom 2, Val.atom 3]]
    = Val.list [Val.seq [Val.atom 2, Val.atom 3]] := rfl

/-- No value is an element of its own payload list: an element of `ys` is
structurally smaller than `Val.seq ys`. -/
theorem mem_ne_seq {w : Val} {ys : List Val} (h : w ∈ ys) : w ≠ Val.seq ys := by
  intro he
  have hlt : sizeOf w < sizeOf ys := List.sizeOf_lt_of_mem h
  have hsz : sizeOf (Val.seq ys) = 1 + sizeOf ys := by simp
  rw [he, hsz] at hlt
  omega

/-- The list twin of `mem_ne_seq`. -/
theorem mem_ne_list {w : Val} {ys : List Val} (h : w ∈ ys) : w ≠ Val.list ys := by
  intro he
  have hlt : sizeOf w < sizeOf ys := List.sizeOf_lt_of_mem h
  have hsz : sizeOf (Val.list ys) = 1 + sizeOf ys := by simp
  rw [he, hsz] at hlt
  omega

/-- A singleton rest is NEVER erased to its item: `collect [v] ≠ v`. This is
the load-bearing difference from canonical capture (`capture [v] = normalize v`),
and what keeps one remaining structured row distinct from the row's own
elements. -/
theorem collect_singleton_ne_item (v : Val) : collect [v] ≠ v := by
  intro he
  exact absurd he.symm (mem_ne_list List.mem_cons_self)

/-- `collect` and `capture` are different operations on the same supply. -/
theorem collect_singleton_atom_ne_capture (n : Int) :
    collect [Val.atom n] ≠ capture [Val.atom n] := by
  intro he
  rw [capture_singleton_atom] at he
  exact collect_singleton_ne_item (Val.atom n) he

/-- Open/collect round trip: surface spread (`items`, the `open` operation)
re-supplies EXACTLY the collected items, so variadic forwarding
(`Forward(items...) = Target(items...)`) is ordinary list spread. -/
theorem items_collect (xs : Supply) : items (collect xs) = xs := rfl

/-- Provenance independence: `collect` depends only on the assembled item
supply, never on which structures were spread to produce it. Collecting the
concatenation of two spread supplies is exactly the list of those items,
whatever `a` and `b` were (`first, rest... = 1, [2, 3]..., (4, 5)...` gives
`rest = [2, 3, 4, 5]`). -/
theorem collect_spread_concat_exact (a b : Val) :
    collect (items a ++ items b) = Val.list (items a ++ items b) := rfl

/-- Equal supplies collect equal lists — the general form of provenance
independence (a function of the supply alone). -/
theorem collect_congr {xs ys : Supply} (h : xs = ys) : collect xs = collect ys :=
  congrArg collect h

/-- Grouped and spread supplies collect DIFFERENT values: `collect` of one
grouped sequence value is the one-element list holding it, never the collect
of its stored items (unless the sequence were its own element, which the
structural order excludes). Supersedes the obsolete coincidence
`captureVariadic [Val.seq ys] = captureVariadic ys` of the pre-list model. -/
theorem collect_lone_seq_ne_collect_items (ys : Supply) :
    collect [Val.seq ys] ≠ collect (items (Val.seq ys)) := by
  intro he
  have hpay : [Val.seq ys] = ys := by
    simpa [collect, items] using he
  cases ys with
  | nil => cases hpay
  | cons w t =>
      have hw : Val.seq (w :: t) = w := by
        have := List.cons.inj hpay
        exact this.1
      have ht : t = [] := by
        have := List.cons.inj hpay
        simpa using this.2.symm
      subst ht
      exact absurd hw.symm (mem_ne_seq List.mem_cons_self)

/-- The list twin: a grouped list argument and its spread items collect
different values as well. -/
theorem collect_lone_list_ne_collect_items (ys : Supply) :
    collect [Val.list ys] ≠ collect (items (Val.list ys)) := by
  intro he
  have hpay : [Val.list ys] = ys := by
    simpa [collect, items] using he
  cases ys with
  | nil => cases hpay
  | cons w t =>
      have hw : Val.list (w :: t) = w := by
        have := List.cons.inj hpay
        exact this.1
      have ht : t = [] := by
        have := List.cons.inj hpay
        simpa using this.2.symm
      subst ht
      exact absurd hw.symm (mem_ne_list List.mem_cons_self)

/-! ## Binding checks -/

theorem rest_tail :
    bindArgs [Pat.name "x", Pat.rest "rest"] [Val.atom 1, Val.atom 2, Val.atom 3]
      = some [("x", Val.atom 1), ("rest", Val.list [Val.atom 2, Val.atom 3])] := by
  decide

theorem rest_empty :
    bindArgs [Pat.name "x", Pat.rest "rest"] [Val.atom 1]
      = some [("x", Val.atom 1), ("rest", Val.list [])] := by
  decide

theorem rest_head :
    bindArgs [Pat.rest "head", Pat.name "last"] [Val.atom 1, Val.atom 2, Val.atom 3]
      = some [("head", Val.list [Val.atom 1, Val.atom 2]), ("last", Val.atom 3)] := by
  decide

theorem rest_middle :
    bindArgs [Pat.name "first", Pat.rest "middle", Pat.name "last"]
        [Val.atom 1, Val.atom 2, Val.atom 3, Val.atom 4]
      = some [("first", Val.atom 1),
              ("middle", Val.list [Val.atom 2, Val.atom 3]),
              ("last", Val.atom 4)] := by
  decide

/-- A one-item rest stays a one-element list: no singleton collapse
(the pre-list model bound `rest = 2` here; exact collection binds `[2]`). -/
theorem rest_singleton_collected :
    bindArgs [Pat.name "x", Pat.rest "rest"] [Val.atom 1, Val.atom 2]
      = some [("x", Val.atom 1), ("rest", Val.list [Val.atom 2])] := by
  decide

theorem call_bind_rest_does_not_open_lone_sequence :
    bindArgs [Pat.name "x", Pat.rest "rest"] [Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]]
      = some [("x", Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]), ("rest", Val.list [])] := by
  decide

-- Assignment deconstruction is an unpacking receiver: a single stored sequence
-- or list value is opened and matched element-by-element. Function calls
-- (`bindArgs`) do NOT open. These checks pin that contrast.

/-- `Add(A)` / function parameter binding: a single sequence-valued argument against
two fixed parameters is an arity error — the call binder does not open `A`. -/
theorem args_fixed_single_sequence_rejected :
    bindArgs [Pat.name "x", Pat.name "y"]
      [Val.seq [Val.atom 1, Val.atom 2]]
      = none := by
  decide

/-- The list twin: `Add(A)` with a stored list is an arity error too. -/
theorem args_fixed_single_list_rejected :
    bindArgs [Pat.name "x", Pat.name "y"]
      [Val.list [Val.atom 1, Val.atom 2]]
      = none := by
  decide

/-- `x, y = A`: deconstruction opens the single sequence-valued right-hand side, so
the two targets bind `x = 1`, `y = 2`. -/
theorem deconstruct_fixed_single_sequence_opens :
    bindDeconstruct [Pat.name "x", Pat.name "y"]
      [Val.seq [Val.atom 1, Val.atom 2]]
      = some [("x", Val.atom 1), ("y", Val.atom 2)] := by
  decide

/-- `x, y = [1, 2]`: deconstruction opens a lone LIST the same way. -/
theorem deconstruct_fixed_single_list_opens :
    bindDeconstruct [Pat.name "x", Pat.name "y"]
      [Val.list [Val.atom 1, Val.atom 2]]
      = some [("x", Val.atom 1), ("y", Val.atom 2)] := by
  decide

/-- `x, y = A...`: the explicit spread supplies `A`'s items directly, which bind the
two fixed targets — the same result as the bare unpack. (`items` is the surface
`...` view.) -/
theorem deconstruct_fixed_explicit_spread_succeeds :
    bindDeconstruct [Pat.name "x", Pat.name "y"]
      (items (Val.seq [Val.atom 1, Val.atom 2]))
      = some [("x", Val.atom 1), ("y", Val.atom 2)] := by
  decide

/-- `first, rest... = A`: deconstruction opens `A`, so `first = 1` and the rest
COLLECTS the remaining items as the exact list `[2, 3]`. -/
theorem deconstruct_rest_single_sequence_opens :
    bindDeconstruct [Pat.name "first", Pat.rest "rest"]
      [Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]]
      = some [("first", Val.atom 1),
              ("rest", Val.list [Val.atom 2, Val.atom 3])] := by
  decide

/-- `first, rest... = [1, 2, 3]`: the lone-list right-hand side opens the same
way, and the rest collects `[2, 3]`. -/
theorem deconstruct_rest_single_list_opens :
    bindDeconstruct [Pat.name "first", Pat.rest "rest"]
      [Val.list [Val.atom 1, Val.atom 2, Val.atom 3]]
      = some [("first", Val.atom 1),
              ("rest", Val.list [Val.atom 2, Val.atom 3])] := by
  decide

/-- `first, rest... = A...`: the explicit spread supplies the same opened items as
the bare unpack above. -/
theorem deconstruct_rest_explicit_spread :
    bindDeconstruct [Pat.name "first", Pat.rest "rest"]
      (items (Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]))
      = some [("first", Val.atom 1),
              ("rest", Val.list [Val.atom 2, Val.atom 3])] := by
  decide

/-- Deconstruction opens where the call binder preserves: on a single stored
sequence value the two modes disagree, so they are not the same function. -/
theorem deconstruct_opens_where_args_preserves :
    bindDeconstruct [Pat.name "x", Pat.name "y"] [Val.seq [Val.atom 1, Val.atom 2]]
      ≠ bindArgs [Pat.name "x", Pat.name "y"] [Val.seq [Val.atom 1, Val.atom 2]] := by
  decide

theorem fixed_arity_mismatch_rejected :
    bindArgs [Pat.name "x", Pat.name "y"] [Val.atom 1] = none := by
  decide

theorem fixed_arity_surplus_rejected :
    bindArgs [Pat.name "x", Pat.name "y"] [Val.atom 1, Val.atom 2, Val.atom 3] = none := by
  decide

theorem two_rests_rejected :
    bindPats [Pat.rest "a", Pat.rest "b"] [Val.atom 1, Val.atom 2] = none := by
  decide

/--
The lone rest pattern is the abstract variadic capture case. Surface assignment
syntax can still reject rest-only assignment targets before they reach this
binder model.
-/
theorem variadic_is_single_rest (xs : Supply) :
    bindArgs [Pat.rest "x"] xs = some [("x", collect xs)] := by
  unfold bindArgs
  simp [bindPats, bindFixed, Pat.isRest, Pat.key, List.take_length, List.drop_length]

/-! ## Receiver theorems

The concrete checks above pin the call/deconstruction contrast on specific
values. The theorems below establish the contrast in general:

* `receivers_agree_of_not_lone_structure` — the two receivers agree on every
  supply that is not a single sequence or list value, so the entire asymmetry
  is confined to the lone-structure case;
* `deconstruct_singleton_eq_args_items` — on a single-value supply the
  deconstruction receiver binds exactly the value's item view, the item supply
  an explicit spread provides (`x, y = A` binds as `x, y = A...`);
* `receivers_never_agree_on_lone_seq` — on a lone sequence value the two
  receivers NEVER produce the same successful binding, for any pattern list.
  This replaces the pre-list characterization
  (`agree_on_lone_seq_iff_lone_rest`), whose rest-only agreement depended on
  the canonical-capture coincidence: exact rest collection distinguishes the
  grouped argument (`rest = [A]`) from the opened items (`rest = [a1, …]`),
  so even the lone-rest shape now disagrees;
* `lone_rest_disagrees_on_lone_list` — the concrete lone-rest disagreement on
  a lone LIST supply, mirroring the sequence-side theorem on the list kind.
-/

/-- The deconstruction receiver's implicit opening of a single-value supply is
the total item view `items` — the same item supply the surface spread `...`
provides. -/
theorem openLoneStructure_singleton (v : Val) : openLoneStructure [v] = items v := by
  cases v <;> rfl

/-- Localization: the call and deconstruction receivers agree on every supply
that is not a single sequence value and not a single list value. -/
theorem receivers_agree_of_not_lone_structure (ps : List Pat) (xs : Supply)
    (hseq : ∀ ys : List Val, xs ≠ [Val.seq ys])
    (hlist : ∀ ys : List Val, xs ≠ [Val.list ys]) :
    bindDeconstruct ps xs = bindArgs ps xs := by
  have hn : openLoneStructure xs = xs := by
    cases xs with
    | nil => rfl
    | cons a t =>
      cases t with
      | nil =>
        cases a with
        | atom n => rfl
        | seq ys => exact absurd rfl (hseq ys)
        | list ys => exact absurd rfl (hlist ys)
      | cons b t2 => cases a <;> rfl
  unfold bindDeconstruct bindArgs
  rw [hn]

/-- Spread equivalence: on a single-value supply, deconstruction binds exactly
what a call binds on the value's item view. -/
theorem deconstruct_singleton_eq_args_items (ps : List Pat) (v : Val) :
    bindDeconstruct ps [v] = bindArgs ps (items v) := by
  unfold bindDeconstruct bindArgs
  rw [openLoneStructure_singleton]

/-- `variadic_is_single_rest`, generalized to an arbitrary rest name. -/
theorem bindArgs_lone_rest (r : String) (xs : Supply) :
    bindArgs [Pat.rest r] xs = some [(r, collect xs)] := by
  unfold bindArgs
  simp [bindPats, bindFixed, Pat.isRest, Pat.key, List.take_length, List.drop_length]

/-- Grouped/spread DISTINCTION for a rest-only variadic parameter: `F(A)` with
a stored sequence `A` binds `rest = [A]` (one collected argument), while
`F(A...)` binds `rest = [a1, …, an]` (the collected opened items) — always
different bindings. Supersedes the obsolete paper theorem
`variadic_capture_unchanged_by_spread`. -/
theorem variadic_collect_distinguishes_spread (r : String) (ys : Supply) :
    bindArgs [Pat.rest r] [Val.seq ys]
      ≠ bindArgs [Pat.rest r] (items (Val.seq ys)) := by
  rw [bindArgs_lone_rest, bindArgs_lone_rest]
  intro he
  have hv : collect [Val.seq ys] = collect (items (Val.seq ys)) := by
    have := Option.some.inj he
    have hpair := List.cons.inj this
    have := congrArg Prod.snd hpair.1
    simpa [items] using this
  exact collect_lone_seq_ne_collect_items ys (by simpa [items] using hv)

/-- Exact bound value, grouped side: `F(A)` binds `r` to `collect [A]` — the
one-element list holding the grouped argument. -/
theorem variadic_collect_value_grouped (r : String) (ys : Supply) :
    bindArgs [Pat.rest r] [Val.seq ys]
      = some [(r, Val.list [Val.seq ys])] :=
  bindArgs_lone_rest r [Val.seq ys]

/-- Exact bound value, spread side: `F(A...)` binds `r` to `collect ys` — the
exact list of `A`'s stored items. -/
theorem variadic_collect_value_spread (r : String) (ys : Supply) :
    bindArgs [Pat.rest r] (items (Val.seq ys))
      = some [(r, Val.list ys)] :=
  bindArgs_lone_rest r ys

/-- The shared binder fails whenever the supply is at least two items shorter
than the pattern list: even a rest binding cannot stand in for two missing
fixed positions. -/
theorem bindPats_none_of_undersupplied (ps : List Pat) (xs : Supply)
    (h : xs.length + 1 < ps.length) : bindPats ps xs = none := by
  unfold bindPats
  split
  · exact if_neg (by omega)
  · cases hidx : ps.findIdx? Pat.isRest with
    | none => rfl
    | some i => exact if_pos (by omega)
  · rfl

private theorem list_payload_not_self (ys : List Val) (hkind : Val) (hpay : [hkind] = ys)
    (hmem : ∀ w ∈ ys, w ≠ hkind) : False := by
  cases ys with
  | nil => cases hpay
  | cons w t =>
      have hw : hkind = w := (List.cons.inj hpay).1
      exact absurd hw.symm (hmem w List.mem_cons_self)

/-- Receiver disagreement on a lone sequence value, in full generality: for
EVERY pattern list, the call receiver and the deconstruction receiver never
both succeed with the same environment on a supply of exactly one sequence
value. The pre-list model's rest-only agreement was a canonical-capture
coincidence; exact rest collection removes it. -/
theorem receivers_never_agree_on_lone_seq (ps : List Pat) (ys : List Val) :
    ¬ ∃ env, bindArgs ps [Val.seq ys] = some env
        ∧ bindDeconstruct ps [Val.seq ys] = some env := by
  rintro ⟨env, hA, hD⟩
  rw [bindDeconstruct, openLoneStructure_singleSeq] at hD
  cases ps with
  | nil =>
    simp [bindArgs, bindPats] at hA
  | cons p ps1 =>
    cases ps1 with
    | nil =>
      cases p with
      | rest r =>
        rw [bindArgs_lone_rest] at hA
        rw [show bindPats [Pat.rest r] ys = bindArgs [Pat.rest r] ys from rfl,
            bindArgs_lone_rest] at hD
        rw [← hA] at hD
        have hv : collect ys = collect [Val.seq ys] := by
          have := Option.some.inj hD
          have hpair := List.cons.inj this
          simpa using congrArg Prod.snd hpair.1
        have hpay : [Val.seq ys] = ys := by
          simpa [collect] using hv.symm
        exact list_payload_not_self ys (Val.seq ys) hpay (fun w hw => mem_ne_seq hw)
      | name x =>
        have eA : bindArgs [Pat.name x] [Val.seq ys]
            = some [(x, Val.seq ys)] := rfl
        rw [eA] at hA
        cases ys with
        | nil =>
          have h0 : bindPats [Pat.name x] ([] : Supply) = none := rfl
          rw [h0] at hD
          cases hD
        | cons w t =>
          cases t with
          | nil =>
            have eD : bindPats [Pat.name x] [w] = some [(x, w)] := rfl
            rw [eD] at hD
            rw [← hA] at hD
            simp at hD
            have hne : w ≠ Val.seq [w] := mem_ne_seq List.mem_cons_self
            first
            | exact absurd hD hne
            | exact absurd hD.symm hne
          | cons b t2 =>
            have h0 : bindPats [Pat.name x] (w :: b :: t2) = none := by
              unfold bindPats
              simp [Pat.isRest]
            rw [h0] at hD
            cases hD
    | cons q ps2 =>
      cases ps2 with
      | nil =>
        cases p with
        | name x =>
          cases q with
          | name y =>
            simp [bindArgs, bindPats, Pat.isRest] at hA
          | rest r =>
            have eA : bindArgs [Pat.name x, Pat.rest r] [Val.seq ys]
                = some [(x, Val.seq ys), (r, Val.list [])] := rfl
            rw [eA] at hA
            cases ys with
            | nil =>
              have h0 : bindPats [Pat.name x, Pat.rest r] ([] : Supply) = none := rfl
              rw [h0] at hD
              cases hD
            | cons w t =>
              have eD : bindPats [Pat.name x, Pat.rest r] (w :: t)
                  = some [(x, w), (r, collect t)] := by
                simp [bindPats, Pat.isRest, Pat.key, bindFixed,
                      show List.findIdx? Pat.isRest [Pat.name x, Pat.rest r]
                        = some 1 from rfl]
              rw [eD] at hD
              rw [← hD] at hA
              simp at hA
              have hne : w ≠ Val.seq (w :: t) := mem_ne_seq List.mem_cons_self
              first
              | exact absurd hA.1 hne
              | exact absurd hA.1.symm hne
        | rest r =>
          cases q with
          | rest b =>
            simp [bindArgs, bindPats, Pat.isRest] at hA
          | name y =>
            have eA : bindArgs [Pat.rest r, Pat.name y] [Val.seq ys]
                = some [(r, Val.list []), (y, Val.seq ys)] := rfl
            rw [eA] at hA
            cases ys with
            | nil =>
              have h0 : bindPats [Pat.rest r, Pat.name y] ([] : Supply) = none := rfl
              rw [h0] at hD
              cases hD
            | cons w t =>
              have eD : bindPats [Pat.rest r, Pat.name y] (w :: t)
                  = some ((r, collect ((w :: t).take t.length))
                      :: bindFixed [Pat.name y] ((w :: t).drop t.length)) := by
                simp [bindPats, Pat.isRest, Pat.key, bindFixed,
                      show List.findIdx? Pat.isRest [Pat.rest r, Pat.name y]
                        = some 0 from rfl]
              rw [eD] at hD
              rw [← hD] at hA
              cases hbv : (w :: t).drop t.length with
              | nil =>
                rw [hbv] at hA
                simp [bindFixed] at hA
              | cons b bs =>
                rw [hbv] at hA
                simp [bindFixed, Pat.key] at hA
                have hbdrop : b ∈ (w :: t).drop t.length := by
                  rw [hbv]
                  exact List.mem_cons_self
                have hbmem : b ∈ (w :: t) := by
                  first
                  | exact List.mem_of_mem_drop hbdrop
                  | exact List.drop_subset _ _ hbdrop
                  | exact List.drop_subset _ hbdrop
                have hne : b ≠ Val.seq (w :: t) := mem_ne_seq hbmem
                first
                | exact absurd hA.2 hne
                | exact absurd hA.2.symm hne
                | exact absurd hA.2.1 hne
                | exact absurd hA.2.1.symm hne
      | cons s ps3 =>
        have hnone : bindPats (p :: q :: s :: ps3) [Val.seq ys] = none := by
          apply bindPats_none_of_undersupplied
          simp
        rw [bindArgs] at hA
        rw [hnone] at hA
        cases hA

/-- The lone-rest disagreement on a lone LIST supply: call binding collects
the one supplied argument (`rest = [[1, 2]]`-style nesting), while
deconstruction opens the lone list and collects its items — never the same
binding. -/
theorem lone_rest_disagrees_on_lone_list (r : String) (ys : List Val) :
    bindArgs [Pat.rest r] [Val.list ys]
      ≠ bindDeconstruct [Pat.rest r] [Val.list ys] := by
  rw [bindArgs_lone_rest, bindDeconstruct, openLoneStructure_singleList,
      show bindPats [Pat.rest r] ys = bindArgs [Pat.rest r] ys from rfl,
      bindArgs_lone_rest]
  intro he
  have hv : collect [Val.list ys] = collect ys := by
    have := Option.some.inj he
    have hpair := List.cons.inj this
    simpa using congrArg Prod.snd hpair.1
  have hpay : [Val.list ys] = ys := by
    simpa [collect] using hv
  exact list_payload_not_self ys (Val.list ys) hpay (fun w hw => mem_ne_list hw)

/-! ## Canonical-form theorems (general)

The shape-specific checks earlier in this file pin `normalize`/`capture` on
concrete values. The theorems below establish the general canonical-form
story over all values:

* `normalize_idempotent` — `normalize` is a projection onto canonical values;
* `orphanFree_normalize` — canonical values contain no redundant singleton
  sequence boundary anywhere in their tree (no literal-unwritable "orphans";
  exact list values carry no singleton-orphan rule, since `[x]` is
  literal-writable);
* `capture_canonical` / `capture_orphanFree` — capture boundaries only ever
  produce canonical, orphan-free values;
* `collect_normalize_elementwise` — collected rest values normalize
  element-wise only: the collected boundary itself is stable;
* `capture_items_of_canonical` — capture after spread is the identity on
  canonical NON-LIST values; spreading a list opens its boundary, so
  re-capture converts it to the canonical capture of its elements
  (`capture_items_of_list`).
-/

/-- Unfolding case split for `normalize` on a sequence value: an empty
normalized payload yields the empty sequence value. -/
theorem normalize_seq_of_list_nil {xs : List Val} (h : normalizeList xs = []) :
    normalize (Val.seq xs) = Val.seq [] := by
  simp only [normalize, h]

/-- Unfolding case split for `normalize` on a sequence value: a singleton
normalized payload collapses the redundant boundary. -/
theorem normalize_seq_of_list_singleton {xs : List Val} {v : Val}
    (h : normalizeList xs = [v]) :
    normalize (Val.seq xs) = v := by
  simp only [normalize, h]

/-- Unfolding case split for `normalize` on a sequence value: a multi-item
normalized payload keeps the boundary intact. -/
theorem normalize_seq_of_list_multi {xs : List Val} {a b : Val} {tl : List Val}
    (h : normalizeList xs = a :: b :: tl) :
    normalize (Val.seq xs) = Val.seq (a :: b :: tl) := by
  simp only [normalize, h]

mutual
  /-- General idempotence: `normalize` is a projection, so normalizing an
  already-normalized value changes nothing. Canonical values are exactly the
  fixed points of `normalize`. -/
  theorem normalize_idempotent : ∀ v : Val, normalize (normalize v) = normalize v
    | .atom _ => rfl
    | .seq xs => by
        have hl := normalizeList_idempotent xs
        cases h : normalizeList xs with
        | nil =>
            rw [normalize_seq_of_list_nil h]
            exact normalize_empty
        | cons v tl =>
            cases tl with
            | nil =>
                rw [normalize_seq_of_list_singleton h]
                rw [h] at hl
                have h2 : ([normalize v] : List Val) = [v] := hl
                simpa using h2
            | cons w tl2 =>
                rw [normalize_seq_of_list_multi h]
                rw [h] at hl
                exact normalize_seq_of_list_multi hl
    | .list xs => by
        have hl := normalizeList_idempotent xs
        rw [normalize_list_exact, normalize_list_exact, hl]
  termination_by v => sizeOf v

  /-- Element-wise idempotence for the mutual payload traversal of
  `normalize_idempotent`. -/
  theorem normalizeList_idempotent : ∀ xs : List Val,
      normalizeList (normalizeList xs) = normalizeList xs
    | [] => rfl
    | x :: xs => by
        show normalize (normalize x) :: normalizeList (normalizeList xs)
            = normalize x :: normalizeList xs
        rw [normalize_idempotent x, normalizeList_idempotent xs]
  termination_by xs => sizeOf xs
end

/-- Collected rest values normalize element-wise only: the collect boundary is
already canonical (`normalize (collect xs) = collect (normalizeList xs)`). -/
theorem collect_normalize_elementwise (xs : Supply) :
    normalize (collect xs) = collect (normalizeList xs) := rfl

mutual
  /-- Orphan-freedom: `true` iff no singleton sequence boundary `Val.seq [x]`
  appears anywhere in the value. A singleton sequence boundary is a
  literal-unwritable "orphan" (a stored `(5)` distinct from `5`): `normalize`
  erases such boundaries at every construction/capture site, so no canonical
  value contains one (`orphanFree_normalize`). Exact list values carry NO
  singleton-orphan rule — `[x]` is literal-writable — so only their elements
  are checked. -/
  def orphanFree : Val -> Bool
    | .atom _ => true
    | .seq xs => xs.length != 1 && orphanFreeList xs
    | .list xs => orphanFreeList xs

  /-- List traversal for `orphanFree`. -/
  def orphanFreeList : List Val -> Bool
    | [] => true
    | x :: xs => orphanFree x && orphanFreeList xs
end

example : orphanFree (Val.atom 5) = true := by decide
example : orphanFree (Val.seq []) = true := by decide
example : orphanFree (Val.seq [Val.atom 1]) = false := by decide
example : orphanFree (Val.seq [Val.atom 1, Val.seq [Val.atom 2]]) = false := by decide
example : orphanFree (Val.seq [Val.atom 1, Val.seq []]) = true := by decide
example : orphanFree (Val.list []) = true := by decide
example : orphanFree (Val.list [Val.atom 1]) = true := by decide
example : orphanFree (Val.list [Val.list [Val.atom 1]]) = true := by decide
example : orphanFree (Val.list [Val.seq [Val.atom 1]]) = false := by decide

mutual
  /-- Orphan-freedom of canonical values: normalization never leaves a
  redundant singleton sequence boundary anywhere in the tree. -/
  theorem orphanFree_normalize : ∀ v : Val, orphanFree (normalize v) = true
    | .atom _ => rfl
    | .seq xs => by
        have hl := orphanFreeList_normalizeList xs
        cases h : normalizeList xs with
        | nil =>
            rw [normalize_seq_of_list_nil h]
            rfl
        | cons v tl =>
            cases tl with
            | nil =>
                rw [normalize_seq_of_list_singleton h]
                rw [h] at hl
                have h2 : (orphanFree v && true) = true := hl
                simpa using h2
            | cons w tl2 =>
                rw [normalize_seq_of_list_multi h]
                rw [h] at hl
                have hlen : ((v :: w :: tl2).length != 1) = true := by
                  simp only [List.length_cons, bne_iff_ne, ne_eq]
                  omega
                show ((v :: w :: tl2).length != 1 && orphanFreeList (v :: w :: tl2)) = true
                rw [hlen, hl]
                rfl
    | .list xs => by
        have hl := orphanFreeList_normalizeList xs
        rw [normalize_list_exact]
        show orphanFreeList (normalizeList xs) = true
        exact hl
  termination_by v => sizeOf v

  /-- List form of `orphanFree_normalize` for the mutual payload traversal. -/
  theorem orphanFreeList_normalizeList : ∀ xs : List Val,
      orphanFreeList (normalizeList xs) = true
    | [] => rfl
    | x :: xs => by
        show (orphanFree (normalize x) && orphanFreeList (normalizeList xs)) = true
        rw [orphanFree_normalize x, orphanFreeList_normalizeList xs]
        rfl
  termination_by xs => sizeOf xs
end

/-- Capture canonicity: a captured item supply is already canonical, so capture
is a fixed point of `normalize` (corollary of `normalize_idempotent`, since
`capture xs = normalize (Val.seq xs)`). -/
theorem capture_canonical (xs : Supply) : normalize (capture xs) = capture xs :=
  normalize_idempotent (Val.seq xs)

/-- Capture never mints an orphan: every captured value is orphan-free
(corollary of `orphanFree_normalize`). -/
theorem capture_orphanFree (xs : Supply) : orphanFree (capture xs) = true :=
  orphanFree_normalize (Val.seq xs)

/-- Spread/capture round-trip, restricted to non-list values: on a canonical
value that is not an exact list, re-capturing the item view (the supply an
explicit spread `...` provides) reproduces the value exactly. -/
theorem capture_items_of_canonical (v : Val) (h : normalize v = v)
    (hl : ∀ xs, v ≠ Val.list xs) :
    capture (items v) = v := by
  cases v with
  | atom n => rfl
  | seq xs => exact h
  | list xs => exact absurd rfl (hl xs)

/-- Spread-then-CAPTURE on a list yields the canonical capture of its
elements — never the same list back: `x = A...` re-groups list items into
the sequence world. (Spread-then-COLLECT, by contrast, reproduces the list:
`items_collect`.) -/
theorem capture_items_of_list (xs : Supply) :
    capture (items (Val.list xs)) = capture xs := rfl

/-- Collect/spread/collect collapse: re-collecting a collected value's items
is the identity — the list-side round trip composes (corollary of
`items_collect`). -/
theorem collect_items_collect (xs : Supply) :
    collect (items (collect xs)) = collect xs := rfl

end CoreArityAlgebra
