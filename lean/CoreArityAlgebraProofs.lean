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
    | .atom _, .seq _ => .isFalse (by intro he; cases he)
    | .seq _, .atom _ => .isFalse (by intro he; cases he)

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

theorem spread_seq (xs : Supply) : spread (Val.seq xs) = some xs := rfl

theorem items_seq (xs : Supply) : items (Val.seq xs) = xs := rfl

theorem seq_items_seq (xs : Supply) : Val.seq (items (Val.seq xs)) = Val.seq xs := rfl

theorem seq_items_atom (n : Int) : Val.seq (items (Val.atom n)) = Val.seq [Val.atom n] := rfl

example : Val.seq (items (Val.atom 7)) ≠ Val.atom 7 := by decide

theorem items_eq_spread (v : Val) : items v = (spread v).getD [v] := by
  cases v <;> rfl

example : (Val.seq [Val.atom 1, Val.atom 2]) = (Val.seq [Val.atom 1, Val.atom 2]) := rfl

theorem nesting_matters :
    Val.seq [Val.atom 1, Val.seq [Val.atom 2, Val.atom 3]]
      ≠ Val.seq [Val.seq [Val.atom 1, Val.atom 2], Val.atom 3] := by
  decide

theorem normalize_atom (n : Int) : normalize (Val.atom n) = Val.atom n := rfl

theorem normalize_empty : normalize (Val.seq []) = Val.seq [] := rfl

theorem normalize_singleton (v : Val) : normalize (Val.seq [v]) = normalize v := rfl

theorem normalize_nested_empty_collapses :
    normalize (Val.seq [Val.seq []]) = Val.seq [] := rfl

theorem normalize_deep_nested_empty_collapses :
  normalize (Val.seq [Val.seq [Val.seq []]]) = Val.seq [] := rfl

theorem normalize_keeps_pair (a b : Val) :
    normalize (Val.seq [a, b]) = Val.seq [normalize a, normalize b] := rfl

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

theorem spread_capture_pair :
    spread (capture [Val.atom 1, Val.atom 2])
      = some [Val.atom 1, Val.atom 2] := by
  decide

theorem spread_capture_singleton_atom :
    spread (capture [Val.atom 1]) = none := by
  decide

theorem normalizeSupply_empty : normalizeSupply [] = [] := rfl

theorem normalizeSupply_singleSeq (xs : Supply) :
    normalizeSupply [Val.seq xs] = xs := rfl

theorem normalizeSupply_singleAtom (n : Int) :
    normalizeSupply [Val.atom n] = [Val.atom n] := rfl

theorem normalizeSupply_multi (a b : Val) (rest : Supply) :
    normalizeSupply (a :: b :: rest) = a :: b :: rest := rfl

theorem normalizeSupply_nested_empty_opens_one_boundary :
    normalizeSupply [Val.seq [Val.seq []]] = [Val.seq []] := rfl

theorem variadic_empty : captureVariadic [] = Val.seq [] := rfl

theorem variadic_singleton_empty : captureVariadic [Val.seq []] = Val.seq [] := rfl

theorem variadic_singleton_scalar (n : Int) :
    captureVariadic [Val.atom n] = Val.atom n := rfl

theorem variadic_two_scalars (m n : Int) :
    captureVariadic [Val.atom m, Val.atom n] = Val.seq [Val.atom m, Val.atom n] := rfl

theorem variadic_grouped_eq_spread :
    captureVariadic [Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]]
      = captureVariadic (items (Val.seq [Val.atom 1, Val.atom 2, Val.atom 3])) := by
  decide

theorem variadic_grouped_eq_spread_value :
    captureVariadic [Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]]
      = Val.seq [Val.atom 1, Val.atom 2, Val.atom 3] := by
  decide

theorem rest_tail :
    bindArgs [Pat.name "x", Pat.rest "rest"] [Val.atom 1, Val.atom 2, Val.atom 3]
      = some [("x", Val.atom 1), ("rest", Val.seq [Val.atom 2, Val.atom 3])] := by
  decide

theorem rest_empty :
    bindArgs [Pat.name "x", Pat.rest "rest"] [Val.atom 1]
      = some [("x", Val.atom 1), ("rest", Val.seq [])] := by
  decide

theorem rest_head :
    bindArgs [Pat.rest "head", Pat.name "last"] [Val.atom 1, Val.atom 2, Val.atom 3]
      = some [("head", Val.seq [Val.atom 1, Val.atom 2]), ("last", Val.atom 3)] := by
  decide

theorem rest_middle :
    bindArgs [Pat.name "first", Pat.rest "middle", Pat.name "last"]
        [Val.atom 1, Val.atom 2, Val.atom 3, Val.atom 4]
      = some [("first", Val.atom 1),
              ("middle", Val.seq [Val.atom 2, Val.atom 3]),
              ("last", Val.atom 4)] := by
  decide

theorem rest_singleton_collapses :
    bindArgs [Pat.name "x", Pat.rest "rest"] [Val.atom 1, Val.atom 2]
      = some [("x", Val.atom 1), ("rest", Val.atom 2)] := by
  decide

theorem call_bind_rest_does_not_normalize_supply :
    bindArgs [Pat.name "x", Pat.rest "rest"] [Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]]
      = some [("x", Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]), ("rest", Val.seq [])] := by
  decide

-- Assignment deconstruction is an unpacking receiver (Option A, Python-style): a
-- single stored sequence value is opened and matched element-by-element. Function
-- calls (`bindArgs`) do NOT open. These checks pin that contrast.

/-- `Add(A)` / function parameter binding: a single sequence-valued argument against
two fixed parameters is an arity error — the call binder does not open `A`. -/
theorem args_fixed_single_sequence_rejected :
    bindArgs [Pat.name "x", Pat.name "y"]
      [Val.seq [Val.atom 1, Val.atom 2]]
      = none := by
  decide

/-- `x, y = A`: deconstruction opens the single sequence-valued right-hand side, so
the two targets bind `x = 1`, `y = 2`. -/
theorem deconstruct_fixed_single_sequence_opens :
    bindDeconstruct [Pat.name "x", Pat.name "y"]
      [Val.seq [Val.atom 1, Val.atom 2]]
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
captures the remaining items as one grouped value `(2, 3)`. -/
theorem deconstruct_rest_single_sequence_opens :
    bindDeconstruct [Pat.name "first", Pat.rest "rest"]
      [Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]]
      = some [("first", Val.atom 1),
              ("rest", Val.seq [Val.atom 2, Val.atom 3])] := by
  decide

/-- `first, rest... = A...`: the explicit spread supplies the same opened items as
the bare unpack above. -/
theorem deconstruct_rest_explicit_spread :
    bindDeconstruct [Pat.name "first", Pat.rest "rest"]
      (items (Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]))
      = some [("first", Val.atom 1),
              ("rest", Val.seq [Val.atom 2, Val.atom 3])] := by
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
    bindArgs [Pat.rest "x"] xs = some [("x", captureVariadic xs)] := by
  unfold bindArgs captureVariadic
  simp [bindPats, bindFixed, Pat.isRest, Pat.key, List.take_length, List.drop_length]

/-! ## Receiver-agreement theorems

The concrete checks above pin the call/deconstruction contrast on specific
values. The theorems below establish the contrast in general:

* `receivers_agree_of_not_lone_seq` — the two receivers agree on every supply
  that is not a single sequence value, so the entire asymmetry is confined to
  the lone-sequence-value case;
* `deconstruct_singleton_eq_args_items` — on a single-value supply the
  deconstruction receiver binds exactly the value's item view, the item supply
  an explicit spread provides (`x, y = A` binds as `x, y = A...`);
* `agree_on_lone_seq_iff_lone_rest` — on a lone sequence value the two
  receivers produce the same successful binding exactly when the pattern list
  is a single rest binding (the `Sum(A) = Sum(A...)` coincidence, and only it).
-/

/-- No value is an element of its own payload list: an element of `ys` is
structurally smaller than `Val.seq ys`. -/
theorem mem_ne_seq {w : Val} {ys : List Val} (h : w ∈ ys) : w ≠ Val.seq ys := by
  intro he
  have hlt : sizeOf w < sizeOf ys := List.sizeOf_lt_of_mem h
  have hsz : sizeOf (Val.seq ys) = 1 + sizeOf ys := by simp
  rw [he, hsz] at hlt
  omega

/-- The deconstruction receiver's implicit opening of a single-value supply is
the total item view `items` — the same item supply the surface spread `...`
provides. -/
theorem normalizeSupply_singleton (v : Val) : normalizeSupply [v] = items v := by
  cases v <;> rfl

/-- Localization: the call and deconstruction receivers agree on every supply
that is not a single sequence value. -/
theorem receivers_agree_of_not_lone_seq (ps : List Pat) (xs : Supply)
    (h : ∀ ys : List Val, xs ≠ [Val.seq ys]) :
    bindDeconstruct ps xs = bindArgs ps xs := by
  have hn : normalizeSupply xs = xs := by
    cases xs with
    | nil => rfl
    | cons a t =>
      cases t with
      | nil =>
        cases a with
        | atom n => rfl
        | seq ys => exact absurd rfl (h ys)
      | cons b t2 => rfl
  unfold bindDeconstruct bindArgs
  rw [hn]

/-- Spread equivalence: on a single-value supply, deconstruction binds exactly
what a call binds on the value's item view. -/
theorem deconstruct_singleton_eq_args_items (ps : List Pat) (v : Val) :
    bindDeconstruct ps [v] = bindArgs ps (items v) := by
  unfold bindDeconstruct bindArgs
  rw [normalizeSupply_singleton]

/-- `variadic_is_single_rest`, generalized to an arbitrary rest name. -/
theorem bindArgs_lone_rest (r : String) (xs : Supply) :
    bindArgs [Pat.rest r] xs = some [(r, captureVariadic xs)] := by
  unfold bindArgs captureVariadic
  simp [bindPats, bindFixed, Pat.isRest, Pat.key, List.take_length, List.drop_length]

/-- Rest-only coincidence (agreement direction): a lone rest pattern binds a
single sequence value and its opened items to the same environment. -/
theorem lone_rest_agrees_on_lone_seq (r : String) (ys : List Val) :
    bindArgs [Pat.rest r] [Val.seq ys] = bindDeconstruct [Pat.rest r] [Val.seq ys] := by
  have h1 : bindDeconstruct [Pat.rest r] [Val.seq ys] = bindArgs [Pat.rest r] ys := by
    unfold bindDeconstruct bindArgs
    rw [normalizeSupply_singleSeq]
  have hcap : captureVariadic [Val.seq ys] = captureVariadic ys := by
    show normalize (Val.seq [Val.seq ys]) = normalize (Val.seq ys)
    exact normalize_singleton (Val.seq ys)
  rw [h1, bindArgs_lone_rest, bindArgs_lone_rest, hcap]

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

/-- Rest-only coincidence (uniqueness direction): if the call receiver and the
deconstruction receiver both succeed with the same environment on a supply of
exactly one sequence value, the pattern list is a single rest binding. -/
theorem lone_rest_of_agree_on_lone_seq (ps : List Pat) (ys : List Val) (env : Env)
    (hA : bindArgs ps [Val.seq ys] = some env)
    (hD : bindDeconstruct ps [Val.seq ys] = some env) :
    ∃ r, ps = [Pat.rest r] := by
  rw [bindDeconstruct, normalizeSupply_singleSeq] at hD
  cases ps with
  | nil =>
    simp [bindArgs, bindPats] at hA
  | cons p ps1 =>
    cases ps1 with
    | nil =>
      cases p with
      | rest r => exact ⟨r, rfl⟩
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
            rw [← hD] at hA
            simp at hA
            have hne : w ≠ Val.seq [w] := mem_ne_seq List.mem_cons_self
            first
            | exact absurd hA hne
            | exact absurd hA.symm hne
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
                = some [(x, Val.seq ys), (r, Val.seq [])] := rfl
            rw [eA] at hA
            cases ys with
            | nil =>
              have h0 : bindPats [Pat.name x, Pat.rest r] ([] : Supply) = none := rfl
              rw [h0] at hD
              cases hD
            | cons w t =>
              have eD : bindPats [Pat.name x, Pat.rest r] (w :: t)
                  = some [(x, w), (r, capture t)] := by
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
                = some [(r, Val.seq []), (y, Val.seq ys)] := rfl
            rw [eA] at hA
            cases ys with
            | nil =>
              have h0 : bindPats [Pat.rest r, Pat.name y] ([] : Supply) = none := rfl
              rw [h0] at hD
              cases hD
            | cons w t =>
              have eD : bindPats [Pat.rest r, Pat.name y] (w :: t)
                  = some ((r, capture ((w :: t).take t.length))
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

/-- Receiver agreement on a lone sequence value, characterized: the two
receivers produce the same successful binding exactly when the pattern list is
one rest binding. -/
theorem agree_on_lone_seq_iff_lone_rest (ps : List Pat) (ys : List Val) :
    (∃ env, bindArgs ps [Val.seq ys] = some env ∧
            bindDeconstruct ps [Val.seq ys] = some env)
      ↔ ∃ r, ps = [Pat.rest r] := by
  constructor
  · intro ⟨env, hA, hD⟩
    exact lone_rest_of_agree_on_lone_seq ps ys env hA hD
  · intro ⟨r, hp⟩
    subst hp
    refine ⟨[(r, captureVariadic [Val.seq ys])], bindArgs_lone_rest r _, ?_⟩
    rw [← lone_rest_agrees_on_lone_seq, bindArgs_lone_rest]

/-! ## Canonical-form theorems (general)

The shape-specific checks earlier in this file pin `normalize`/`capture` on
concrete values. The theorems below establish the general canonical-form
story over all values:

* `normalize_idempotent` — `normalize` is a projection onto canonical values;
* `orphanFree_normalize` — canonical values contain no redundant singleton
  sequence boundary anywhere in their tree (no literal-unwritable "orphans");
* `capture_canonical` / `capture_orphanFree` — capture boundaries only ever
  produce canonical, orphan-free values;
* `capture_items_of_canonical` — capture after spread is the identity on
  canonical values, so re-capturing a spread supply loses nothing.
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

mutual
  /-- Orphan-freedom: `true` iff no singleton sequence boundary `Val.seq [x]`
  appears anywhere in the value. A singleton boundary is a literal-unwritable
  "orphan" (a stored `(5)` distinct from `5`): `normalize` erases such
  boundaries at every construction/capture site, so no canonical value
  contains one (`orphanFree_normalize`). -/
  def orphanFree : Val -> Bool
    | .atom _ => true
    | .seq xs => xs.length != 1 && orphanFreeList xs

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

/-- Spread/capture round-trip: on a canonical value, re-capturing the item view
(the supply an explicit spread `...` provides) reproduces the value exactly.
Opening a canonical value and grouping it back is lossless. -/
theorem capture_items_of_canonical (v : Val) (h : normalize v = v) :
    capture (items v) = v := by
  cases v with
  | atom n => rfl
  | seq xs => exact h

/-- Capture/spread/capture collapse: since captured values are canonical, a
second capture of a captured value's items is just the first capture. -/
theorem capture_items_capture (xs : Supply) :
    capture (items (capture xs)) = capture xs :=
  capture_items_of_canonical _ (capture_canonical xs)

end CoreArityAlgebra
