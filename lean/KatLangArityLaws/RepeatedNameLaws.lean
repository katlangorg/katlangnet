import KatLangArityLaws.BinderCorrespondence
import KatLangArityLaws.NeedControl

open KatLang KatLang.BinderTrace

/-!
# Repeated-name group laws (NEED-04 group-aware, ALIAS-UNIFY-1, October 2026)

R3 proved the production binder's per-occurrence repeated-name order and verdict
(`KatLangArityLaws/BinderTrace.lean`: `repeated_name_binding`, `traced_repeated_failure_points`,
`repeated_events_are_a_prefix_of_the_canonical_order`). Since ALIAS-UNIFY-1 (superseding FU2's
VALUE-first rule and S5's `retain` fold) each occurrence of a repeated name projects its CALLABLE
first: a callable-bearing contribution is compared by identity and checked against a data anchor
only once the group has one, a value-only contribution demands its own counted VALUE and anchors
the group. This module proves the group's DECLARATIVE laws on an explicit domain and connects them
to that same production traversal.

THE DOMAIN. A REPEATED NAME's contributions are a nonempty finite list of STABLE COMPLETED
observations (`Contribution`): the address the binder would bind, the contribution's complete
counted VALUE (`CountedResult`, value AND emitted count) and its independently available
CALLABLE identity (`Option Algorithm`). The laws are about such observations, not about
arbitrary expressions: moving a stateful or failing expression changes the work performed and
which failure is reached, and NO law here says that.

THE EQUALITY LAWS THE PROOFS USE, and where they come from:

* counted-value equality `==` on `CountedResult` is `=` — `Result.beq` is structural and total,
  and `LawfulBEq Result` is proved below, so the count is part of every comparison
  (`counted_beq_iff`);
* callable identity `sameRepeatedCallableIdentity` is REFLEXIVE and SYMMETRIC for every
  algorithm (`same_identity_refl`, `same_identity_symm`) and TRANSITIVE on the stated domain of
  equal `parentProfile` (`same_identity_trans`). Outside that domain the anonymous-declaration
  fallback compares opaque `reprStr` strings, and transitivity across a MIXED profile is NOT
  proved here — the premise is explicit wherever it is used (`CallableTransOn`).
  `CallableIdentityDomain.lean` proves transitivity whenever no compared level is decided by such
  a mixed fallback.

RESULTS (for `gfold`, the group-aware agreement fold, proved to be the production traversal):

1. STABLE-DOMAIN CORRECTNESS (§6 statement 6): success ⇔ `GroupCompatible` — every two PRESENT
   callable identities agree, and only when some contribution is value-only, every
   contribution's own counted VALUE agrees (`gfold_ok_iff_compatible`);
2. STABLE SATISFIABILITY PERMUTATION (§6 statement 7): acceptance is permutation invariant
   (`gfold_satisfiable_perm`) — never the schedule, the effects or which failure is first;
3. THE ORIGINAL REPRESENTATIVE (§6 statement 8): the first callable-bearing contribution if any,
   otherwise the first one — ONE supplied contribution, never a synthesized pairing
   (`gfold_rep_first_richest`, `gfold_rep_mem`);
4. CONDITIONAL VALUE PRESERVATION (§6 statement 9, the approved change to Q-28): a MIXED group
   binds the same counted VALUE in every successful order (`gfold_perm_preserves_value_mixed`);
   a reference-only group needs the explicit `Coherent` premise
   (`gfold_perm_preserves_value_of_coherent`); identity and availability are preserved in every
   case (`gfold_perm_preserves_identity`); a value anchor checks EVERY reference's own VALUE
   (`gfold_anchor_checks_every_reference`, the pairwise-shortcut counterexample);
5. THE PRODUCTION BRIDGE (§6 statement 13): over a flat level of name patterns with stable
   capabilities, the production binder returns exactly the pure `flatBind`, and each repeated
   name's binding is its own `gfold` over its own occurrences in written order
   (`production_flat_head_is_flatBind`, `production_flat_binding_is_gfold`,
   `production_flat_binding_succeeds_iff_compatible`).

REFERENCE-GROUP INERTNESS (§6 statement 5) is an event law and lives with the schedule
(`BinderTrace.reference_contribution_without_anchor_demands_nothing`; `BinderGuards`, the
`groupChannels` witnesses). NESTED and mixed heads, with fresh-cell provenance, are
`NestedRepeatedNames.lean`. Repeated collecting names and repeated META binders are invalid
signatures. Lean numbers are `Int`: "the original representative" is results 3 and 5 (an original
contribution by address); Decimal128 representation is C# evidence
(`NumericRepresentativeSelectionTests`, `GroupAwareRepeatedNameTests`).
-/

namespace KatLang.RepeatedNameLaws

/-! ## Counted-value equality is equality -/

mutual
  theorem result_beq_refl : ∀ r : Result, Result.beq r r = true
    | .atom _ => by simp [Result.beq]
    | .str _ => by simp [Result.beq]
    | .bool _ => by simp [Result.beq]
    | .sequenceValue xs => by simp only [Result.beq]; exact result_beqList_refl xs
    | .listValue xs => by simp only [Result.beq]; exact result_beqList_refl xs
    | .callRef _ => by simp [Result.beq]
    | .argView _ => by simp [Result.beq]

  theorem result_beqList_refl : ∀ xs : List Result, Result.beqList xs xs = true
    | [] => by simp [Result.beqList]
    | x :: xs => by
        simp only [Result.beqList, result_beq_refl x, result_beqList_refl xs, Bool.and_self]
end

mutual
  theorem result_eq_of_beq : ∀ a b : Result, Result.beq a b = true → a = b
    | .atom x, b, h => by cases b <;> simp_all [Result.beq]
    | .str x, b, h => by cases b <;> simp_all [Result.beq]
    | .bool x, b, h => by cases b <;> simp_all [Result.beq]
    | .callRef x, b, h => by cases b <;> simp_all [Result.beq]
    | .argView x, b, h => by cases b <;> simp_all [Result.beq]
    | .sequenceValue xs, b, h => by
        cases b with
        | sequenceValue ys =>
            rw [result_eqList_of_beq xs ys (by simpa only [Result.beq] using h)]
        | _ => simp [Result.beq] at h
    | .listValue xs, b, h => by
        cases b with
        | listValue ys =>
            rw [result_eqList_of_beq xs ys (by simpa only [Result.beq] using h)]
        | _ => simp [Result.beq] at h

  theorem result_eqList_of_beq : ∀ a b : List Result, Result.beqList a b = true → a = b
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [Result.beqList] at h
    | _ :: _, [], h => by simp [Result.beqList] at h
    | x :: xs, y :: ys, h => by
        simp only [Result.beqList, Bool.and_eq_true] at h
        rw [result_eq_of_beq x y h.1, result_eqList_of_beq xs ys h.2]
end

instance : LawfulBEq Result where
  eq_of_beq {a b} h := result_eq_of_beq a b h
  rfl {a} := result_beq_refl a

/-- THE COUNTED COMPARISON IS EQUALITY, value and emitted count together: two counted results
    compare equal under the binder's `==` exactly when they are equal. -/
theorem counted_beq_iff (a b : CountedResult) : (a == b) = true ↔ a = b := beq_iff_eq

/-- Equal displayed values with different emitted counts are UNEQUAL contributions. -/
theorem counted_beq_needs_equal_counts (v : Result) (m n : Nat) (h : m ≠ n) :
    ((v, m) == (v, n)) = false := by
  simp [h]

/-! ## Callable identity: the total helpers and their laws -/

/-- The former `partial` body of `sameDeclaringScope`, accessor for accessor, is the defining
    equation of the total definition: the function is unchanged (the recursion is structural
    over a finite chain, so this equation determines it). -/
theorem same_declaring_scope_equation (left right : ScopeCtx) :
    sameDeclaringScope left right =
      match left.declarationId, right.declarationId with
      | some a, some b => a == b && left.params == right.params &&
          match left.parent, right.parent with
          | none, none => true
          | some p, some q => sameDeclaringScope p q
          | _, _ => false
      | _, _ => reprStr left.declaration == reprStr right.declaration := by
  cases left with
  | mk lp lps _ _ _ _ _ lid =>
    cases right with
    | mk rp rps _ _ _ _ _ rid =>
      cases lid <;> cases rid <;> cases lp <;> cases rp <;>
        simp [sameDeclaringScope, ScopeCtx.declarationId, ScopeCtx.params, ScopeCtx.parent]

/-- The former `partial` body of `compatibleActivations` is the total definition's equation. -/
theorem compatible_activations_equation (required actual : Option ScopeCtx) :
    compatibleActivations required actual =
      match required, actual with
      | none, none => true
      | some r, some a =>
          (r.activation.isNone || r.activation == a.activation) &&
            compatibleActivations r.parent a.parent
      | _, _ => false := by
  cases required with
  | none => cases actual <;> simp [compatibleActivations]
  | some r =>
    cases actual with
    | none => simp [compatibleActivations]
    | some a =>
      cases r; cases a
      simp [compatibleActivations, ScopeCtx.activation, ScopeCtx.parent]

/-! ### The identity components are lawful -/

theorem property_identity_eq_of_beq : ∀ a b : PropertyIdentity, (a == b) = true → a = b := by
  intro a b h; cases a <;> cases b <;> simp_all [BEq.beq, instBEqPropertyIdentity.beq]

theorem property_identity_beq_refl : ∀ a : PropertyIdentity, (a == a) = true := by
  intro a; cases a <;> simp [BEq.beq, instBEqPropertyIdentity.beq]

instance : LawfulBEq PropertyIdentity where
  eq_of_beq {a b} h := property_identity_eq_of_beq a b h
  rfl {a} := property_identity_beq_refl a

theorem builtin_eq_of_beq : ∀ a b : Builtin, (a == b) = true → a = b := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem builtin_beq_refl : ∀ a : Builtin, (a == a) = true := by
  intro a; cases a <;> decide

instance : LawfulBEq Builtin where
  eq_of_beq {a b} h := builtin_eq_of_beq a b h
  rfl {a} := builtin_beq_refl a

theorem beq_comm_of_lawful {α : Type} [BEq α] [LawfulBEq α] (a b : α) : (a == b) = (b == a) := by
  cases h : (a == b) <;> cases h' : (b == a) <;> simp_all

/-! ### `sameDeclaringScope`: reflexive, symmetric, transitive on equal id profiles -/

theorem same_declaring_scope_refl : ∀ s : ScopeCtx, sameDeclaringScope s s = true
  | .mk p _ _ _ _ _ _ (some _) => by
      cases p with
      | none => simp [sameDeclaringScope]
      | some q => simp [sameDeclaringScope, same_declaring_scope_refl q]
  | .mk p _ _ _ _ _ _ none => by cases p <;> simp [sameDeclaringScope]

theorem same_declaring_scope_symm : ∀ l r : ScopeCtx, sameDeclaringScope l r = sameDeclaringScope r l
  | .mk lp lps _ _ _ _ _ (some a), .mk rp rps _ _ _ _ _ (some b) => by
      rcases lp with _ | p <;> rcases rp with _ | q
      · simp only [sameDeclaringScope]; rw [beq_comm_of_lawful a b, beq_comm_of_lawful lps rps]
      · simp [sameDeclaringScope]
      · simp [sameDeclaringScope]
      · simp only [sameDeclaringScope]
        rw [beq_comm_of_lawful a b, beq_comm_of_lawful lps rps, same_declaring_scope_symm p q]
  | .mk lp _ _ _ _ _ _ none, .mk rp _ _ _ _ _ _ rid => by
      rcases lp with _ | p <;> rcases rp with _ | q <;> rcases rid with _ | b <;>
        simp only [sameDeclaringScope] <;> exact beq_comm_of_lawful _ _
  | .mk lp _ _ _ _ _ _ (some a), .mk rp _ _ _ _ _ _ none => by
      rcases lp with _ | p <;> rcases rp with _ | q <;>
        simp only [sameDeclaringScope] <;> exact beq_comm_of_lawful _ _

/-- The DECLARATION-ID PRESENCE PROFILE of a scope chain: whether each level, innermost first,
    carries a declaration identity. `sameDeclaringScope` compares two levels structurally when
    both carry one and falls back to comparing printed declarations otherwise. -/
def idProfile : ScopeCtx → List Bool
  | .mk none _ _ _ _ _ _ id => [id.isSome]
  | .mk (some p) _ _ _ _ _ _ id => id.isSome :: idProfile p

/-- TRANSITIVITY of declaring-scope sameness on chains with the SAME id-presence profile. On
    such chains every compared level is either identified in all three (a structural
    comparison) or anonymous in all three (equality of printed declarations). A MIXED profile
    is not covered: there the fallback compares opaque `reprStr` strings of differently shaped
    levels, and no kernel fact relates them. -/
theorem same_declaring_scope_trans : ∀ x y z : ScopeCtx,
    idProfile x = idProfile y → idProfile y = idProfile z →
    sameDeclaringScope x y = true → sameDeclaringScope y z = true → sameDeclaringScope x z = true
  | .mk xp xps _ _ _ _ _ xid, .mk yp yps _ _ _ _ _ yid, .mk zp zps _ _ _ _ _ zid => by
      intro hxy hyz h1 h2
      rcases xid with _ | a <;> rcases yid with _ | b <;> rcases zid with _ | c <;>
        rcases xp with _ | p <;> rcases yp with _ | q <;> rcases zp with _ | r <;>
        simp only [idProfile, List.cons.injEq, Option.isSome_some, Option.isSome_none,
          Bool.false_eq_true, Bool.true_eq_false, false_and, true_and,
          List.nil_eq, and_true] at hxy hyz <;>
        simp only [sameDeclaringScope, Bool.and_eq_true, beq_iff_eq, and_true,
          Bool.false_eq_true, and_false] at h1 h2 ⊢
      all_goals first
        | exact h1.trans h2
        | exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
        | exact ⟨⟨h1.1.1.trans h2.1.1, h1.1.2.trans h2.1.2⟩,
            same_declaring_scope_trans p q r hxy hyz h1.2 h2.2⟩

/-! ### `compatibleActivations` in both directions is equality of activation chains -/

/-- The activation of each level of a chain, innermost first. -/
def activationChain : Option ScopeCtx → List (Option Nat)
  | none => []
  | some (.mk p _ _ _ _ _ activation _) => activation :: activationChain p

theorem compatible_activations_both_iff : ∀ r a : Option ScopeCtx,
    (compatibleActivations r a = true ∧ compatibleActivations a r = true) ↔
      activationChain r = activationChain a
  | none, none => by simp [compatibleActivations, activationChain]
  | none, some (.mk _ _ _ _ _ _ _ _) => by simp [compatibleActivations, activationChain]
  | some (.mk _ _ _ _ _ _ _ _), none => by simp [compatibleActivations, activationChain]
  | some (.mk rp _ _ _ _ _ ra _), some (.mk ap _ _ _ _ _ aa _) => by
      have ih := compatible_activations_both_iff rp ap
      simp only [compatibleActivations, activationChain, Bool.and_eq_true, List.cons.injEq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        refine ⟨?_, ih.mp ⟨h2, h4⟩⟩
        cases ra <;> cases aa <;> simp_all
      · rintro ⟨rfl, h⟩
        have := ih.mpr h
        cases ra <;> simp_all

theorem compatible_activations_refl (s : Option ScopeCtx) : compatibleActivations s s = true :=
  ((compatible_activations_both_iff s s).mpr rfl).1

/-! ### Repeated callable identity: reflexive, symmetric, transitive on its domain -/

/-- Declaring-scope sameness of two optional parents (the parent comparison of
    `sameRepeatedCallableIdentity`). -/
def sameParent : Option ScopeCtx → Option ScopeCtx → Bool
  | none, none => true
  | some p, some q => sameDeclaringScope p q
  | _, _ => false

/-- The builtin an algorithm is, if it is one. -/
def asBuiltin? : Algorithm → Option Builtin
  | .builtin b => some b
  | _ => none

/-- The comparison of two non-builtin algorithms. -/
def identityCore (a b : Algorithm) : Bool :=
  PropertyIdentity.callableDeclaration a.declarationId == PropertyIdentity.callableDeclaration b.declarationId && sameParent a.parent b.parent &&
    compatibleActivations a.parent b.parent && compatibleActivations b.parent a.parent

/-- `sameRepeatedCallableIdentity` in two layers: builtins by their tag, two non-builtins by
    `identityCore`, a builtin and a non-builtin never. -/
theorem same_identity_eq (a b : Algorithm) :
    sameRepeatedCallableIdentity a b =
      match asBuiltin? a, asBuiltin? b with
      | some x, some y => x == y
      | none, none => identityCore a b
      | _, _ => false := by
  cases a <;> cases b <;> rfl

theorem same_parent_refl (p : Option ScopeCtx) : sameParent p p = true := by
  cases p <;> simp [sameParent, same_declaring_scope_refl]

theorem same_parent_symm (p q : Option ScopeCtx) : sameParent p q = sameParent q p := by
  cases p <;> cases q <;> simp [sameParent, same_declaring_scope_symm]

theorem same_parent_trans (p q r : Option ScopeCtx)
    (h1 : p.map idProfile = q.map idProfile) (h2 : q.map idProfile = r.map idProfile)
    (hpq : sameParent p q = true) (hqr : sameParent q r = true) : sameParent p r = true := by
  rcases p with _ | p <;> rcases q with _ | q <;> rcases r with _ | r <;>
    simp_all [sameParent]
  exact same_declaring_scope_trans p q r (h1.trans h2.symm) h2 hpq hqr

theorem identity_core_refl (a : Algorithm) : identityCore a a = true := by
  simp [identityCore, same_parent_refl, compatible_activations_refl]

theorem identity_core_symm (a b : Algorithm) : identityCore a b = identityCore b a := by
  simp only [identityCore]
  rw [beq_comm_of_lawful (PropertyIdentity.callableDeclaration a.declarationId), same_parent_symm a.parent]
  cases compatibleActivations a.parent b.parent <;> cases compatibleActivations b.parent a.parent <;>
    simp

/-- The parent chain's id profile: the transitivity DOMAIN of callable identity. -/
def parentProfile (a : Algorithm) : Option (List Bool) := a.parent.map idProfile

theorem identity_core_trans (a b c : Algorithm)
    (h1 : parentProfile a = parentProfile b) (h2 : parentProfile b = parentProfile c)
    (hab : identityCore a b = true) (hbc : identityCore b c = true) : identityCore a c = true := by
  simp only [identityCore, Bool.and_eq_true, beq_iff_eq] at hab hbc ⊢
  obtain ⟨⟨⟨d1, s1⟩, c1⟩, c1'⟩ := hab
  obtain ⟨⟨⟨d2, s2⟩, c2⟩, c2'⟩ := hbc
  have e1 := (compatible_activations_both_iff a.parent b.parent).mp ⟨c1, c1'⟩
  have e2 := (compatible_activations_both_iff b.parent c.parent).mp ⟨c2, c2'⟩
  have e := (compatible_activations_both_iff a.parent c.parent).mpr (e1.trans e2)
  exact ⟨⟨⟨d1.trans d2, same_parent_trans _ _ _ h1 h2 s1 s2⟩, e.1⟩, e.2⟩

/-- REFLEXIVITY of repeated callable identity, for every algorithm. -/
theorem same_identity_refl (a : Algorithm) : sameRepeatedCallableIdentity a a = true := by
  rw [same_identity_eq]
  cases h : asBuiltin? a <;> simp [identity_core_refl]

/-- SYMMETRY of repeated callable identity, for every pair of algorithms. -/
theorem same_identity_symm (a b : Algorithm) :
    sameRepeatedCallableIdentity a b = sameRepeatedCallableIdentity b a := by
  rw [same_identity_eq, same_identity_eq]
  cases asBuiltin? a <;> cases asBuiltin? b <;> simp [identity_core_symm, beq_comm_of_lawful]

/-- TRANSITIVITY of repeated callable identity on its DOMAIN: three algorithms whose parent
    chains have the same id profile (`parentProfile`; builtins and parentless algorithms
    have profile `none`). -/
theorem same_identity_trans (a b c : Algorithm)
    (h1 : parentProfile a = parentProfile b) (h2 : parentProfile b = parentProfile c)
    (hab : sameRepeatedCallableIdentity a b = true) (hbc : sameRepeatedCallableIdentity b c = true) :
    sameRepeatedCallableIdentity a c = true := by
  rw [same_identity_eq] at hab hbc ⊢
  cases ha : asBuiltin? a <;> cases hb : asBuiltin? b <;> cases hc : asBuiltin? c <;>
    simp_all [beq_iff_eq]
  exact identity_core_trans a b c (h1.trans h2.symm) h2 hab hbc

/-! ## The group-aware agreement fold over stable completed contributions (NEED-04, ALIAS-UNIFY-1) -/

/-- One STABLE COMPLETED contribution to a repeated name: the address the binder would bind,
    its complete counted VALUE and its CALLABLE identity, if any. -/
structure Contribution where
  address : Nat
  value : CountedResult
  callable : Option Algorithm

/-- Which comparison of NEED-04 refused a contribution: the counted VALUE (the binder's
    `badArity` under the repeated-parameter context) or the CALLABLE identity (its
    `typeMismatch`); in family mode either is a non-match. -/
inductive Conflict where
  | value
  | callable
  deriving DecidableEq, Repr

/-- THE PURE AGREEMENT STATE of one repeated name — the observation-level twin of the binder's
    `RepeatedGroup` plus the name's representative: the representative so far, the FIRST callable
    identity, the data ANCHOR (the first value-only contribution's counted VALUE) and the
    callable-bearing contributions still waiting for an anchor, in occurrence order. -/
structure GState where
  rep : Option Contribution := none
  identity : Option Algorithm := none
  anchor : Option CountedResult := none
  pending : List Contribution := []

/-- Whether a callable-bearing contribution conflicts with the group's first identity. -/
def GState.conflictsWith (g : GState) (a : Algorithm) : Bool :=
  match g.identity with
  | some i => !sameRepeatedCallableIdentity i a
  | none => false

/-- An agreed callable-bearing contribution (`NeedBindState.withCallable`). -/
def GState.withCallable (g : GState) (c : Contribution) (a : Algorithm) : GState :=
  { rep := if g.identity.isSome then g.rep else some c
    identity := g.identity <|> some a
    anchor := g.anchor
    pending := if g.anchor.isSome then g.pending else g.pending ++ [c] }

/-- The group's first value-only contribution, after the pending ones agreed
    (`NeedBindState.withAnchor`). -/
def GState.withAnchor (g : GState) (c : Contribution) : GState :=
  { rep := if g.identity.isSome then g.rep else some c
    identity := g.identity
    anchor := some c.value
    pending := [] }

/-- ONE OCCURRENCE against the agreement state, exactly as `NeedBinder.bindName` decides it
    (proved below: `nameStep_view`): a callable-bearing contribution is compared by identity with
    the group's first one, and by its own counted VALUE only once the group has an anchor; a
    value-only contribution is compared with the anchor or, as the group's first one, checks every
    pending contribution's own counted VALUE and becomes the anchor. -/
def gstep (g : GState) (c : Contribution) : Except Conflict GState :=
  match c.callable with
  | some a =>
    if g.conflictsWith a then .error .callable
    else
      match g.anchor with
      | some v => if c.value == v then .ok (g.withCallable c a) else .error .value
      | none => .ok (g.withCallable c a)
  | none =>
    match g.anchor with
    | some v => if c.value == v then .ok g else .error .value
    | none => if g.pending.all (fun p => p.value == c.value) then .ok (g.withAnchor c) else .error .value

/-- The agreement state after the contributions `cs`, in written order; the first refused
    contribution ends the fold. -/
def gfold (g : GState) : List Contribution → Except Conflict GState
  | [] => .ok g
  | c :: cs =>
    match gstep g c with
    | .error e => .error e
    | .ok next => gfold next cs

/-- A callable identity some contribution of `l` carries. -/
def Present (l : List Contribution) (a : Algorithm) : Prop := ∃ x ∈ l, x.callable = some a

/-- NEED-04's DECLARATIVE GROUP PREDICATE (ALIAS-UNIFY-1 §5.4): every two PRESENT callable
    identities are the same identity, AND — only when some contribution has no callable identity —
    every contribution's own counted value (value and emitted count) is equal. A reference-only
    group needs no VALUE premise. -/
def GroupCompatible (l : List Contribution) : Prop :=
  (∀ x ∈ l, ∀ y ∈ l, ∀ a b, x.callable = some a → y.callable = some b →
    sameRepeatedCallableIdentity a b = true) ∧
  ((∃ x ∈ l, x.callable = none) → ∀ x ∈ l, ∀ y ∈ l, x.value = y.value)

/-- TRANSITIVITY of callable identity among the identities present in `l` (the premise the
    laws need; `callable_trans_on_of_profiles` discharges it on the identity domain). -/
def CallableTransOn (l : List Contribution) : Prop :=
  ∀ a b c, Present l a → Present l b → Present l c →
    sameRepeatedCallableIdentity a b = true → sameRepeatedCallableIdentity b c = true →
    sameRepeatedCallableIdentity a c = true

/-- The premise is met whenever every present callable identity lies in the identity domain
    with one common parent profile (for instance: all builtins, or all declared under the same
    shape of scope chain). -/
theorem callable_trans_on_of_profiles (l : List Contribution) (profile : Option (List Bool))
    (h : ∀ a, Present l a → parentProfile a = profile) : CallableTransOn l := by
  intro a b c ha hb hc hab hbc
  exact same_identity_trans a b c ((h a ha).trans (h b hb).symm) ((h b hb).trans (h c hc).symm) hab hbc

/-! ### The fold invariant -/

/-- THE FOLD INVARIANT after the contributions `seen`: the representative is the first richest of
    them; the identity is present and agrees with every identity seen, and it exists exactly when a
    callable-bearing contribution was seen; the anchor exists exactly when a value-only one was seen,
    is the value of one, and every contribution seen has it; without an anchor every contribution
    seen is still pending. -/
structure GInv (seen : List Contribution) (g : GState) : Prop where
  rep : g.rep = (seen.find? (fun x => x.callable.isSome)).or seen.head?
  idPresent : ∀ i, g.identity = some i → Present seen i
  idAgrees : ∀ x ∈ seen, ∀ a, x.callable = some a →
    ∃ i, g.identity = some i ∧ sameRepeatedCallableIdentity i a = true
  idSome : g.identity.isSome = seen.any (fun x => x.callable.isSome)
  anchorNone : g.anchor = none ↔ ∀ x ∈ seen, x.callable.isSome = true
  anchorWitness : ∀ v, g.anchor = some v → ∃ x ∈ seen, x.callable = none ∧ x.value = v
  anchorAll : ∀ v, g.anchor = some v → ∀ x ∈ seen, x.value = v
  pendingNone : g.anchor = none → g.pending = seen
  pendingSome : g.anchor.isSome = true → g.pending = []

theorem ginv_empty : GInv [] {} where
  rep := rfl
  idPresent := fun _ h => by cases h
  idAgrees := fun _ hx => by cases hx
  idSome := rfl
  anchorNone := by simp
  anchorWitness := fun _ h => by cases h
  anchorAll := fun _ h => by cases h
  pendingNone := fun _ => rfl
  pendingSome := fun h => by cases h

theorem find?_some_of_any {l : List Contribution} (h : l.any (fun x => x.callable.isSome) = true) :
    ∃ x, l.find? (fun x => x.callable.isSome) = some x := by
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  cases hf : l.find? (fun x => x.callable.isSome) with
  | some y => exact ⟨y, rfl⟩
  | none => exact absurd hp (by simpa using List.find?_eq_none.mp hf x hx)

theorem find?_none_of_not_any {l : List Contribution} (h : l.any (fun x => x.callable.isSome) = false) :
    l.find? (fun x => x.callable.isSome) = none := by
  apply List.find?_eq_none.mpr
  intro x hx
  have := List.any_eq_false.mp h x hx
  simpa using this

/-- One successful step keeps the invariant. -/
theorem ginv_step {seen : List Contribution} {g g' : GState} {c : Contribution} (hinv : GInv seen g)
    (hstep : gstep g c = .ok g') : GInv (seen ++ [c]) g' := by
  unfold gstep at hstep
  cases hc : c.callable with
  | some a =>
    rw [hc] at hstep
    simp only at hstep
    by_cases hcf : g.conflictsWith a = true
    · simp [hcf] at hstep
    · simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hstep
      have hcs : c.callable.isSome = true := by simp [hc]
      have agreeNew : ∃ i, (g.identity <|> some a) = some i ∧ sameRepeatedCallableIdentity i a = true := by
        cases hid : g.identity with
        | none => exact ⟨a, rfl, same_identity_refl a⟩
        | some i =>
          refine ⟨i, rfl, ?_⟩
          simp only [GState.conflictsWith, hid] at hcf
          simpa using hcf
      have idKeep : ∀ i, g.identity = some i → (g.identity <|> some a) = some i := by
        intro i hi; simp [hi]
      have common : ∀ (pend : List Contribution) (g2 : GState),
          g2 = { rep := if g.identity.isSome then g.rep else some c
                 identity := g.identity <|> some a, anchor := g.anchor, pending := pend } →
          (g.anchor = none → pend = seen ++ [c]) → (g.anchor.isSome = true → pend = []) →
          (∀ v, g.anchor = some v → c.value = v) → GInv (seen ++ [c]) g2 := by
        intro pend g2 hg2 hpn hps hcv
        subst hg2
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- rep
          simp only [List.find?_append, List.head?_append]
          cases hany : seen.any (fun x => x.callable.isSome) with
          | true =>
            obtain ⟨x, hx⟩ := find?_some_of_any hany
            have hids : g.identity.isSome = true := by rw [hinv.idSome]; exact hany
            simp only [hids, ↓reduceIte, hinv.rep, hx, Option.some_or]
          | false =>
            have hx := find?_none_of_not_any hany
            have hids : g.identity.isSome = false := by rw [hinv.idSome]; exact hany
            simp only [hids, Bool.false_eq_true, ↓reduceIte, hx, Option.none_or, List.find?_singleton, hcs,
              Option.some_or]
        · intro i hi
          cases hid : g.identity with
          | none =>
            rw [hid] at hi
            have hai : a = i := by simpa using hi
            subst hai
            exact ⟨c, List.mem_append_right _ List.mem_cons_self, hc⟩
          | some j =>
            rw [hid] at hi
            have hji : j = i := by simpa using hi
            subst hji
            obtain ⟨x, hx, hxa⟩ := hinv.idPresent j hid
            exact ⟨x, List.mem_append_left _ hx, hxa⟩
        · intro x hx b hb
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨i, hi, hs⟩ := hinv.idAgrees x hx b hb
            exact ⟨i, idKeep i hi, hs⟩
          · simp only [List.mem_singleton] at hx
            subst hx
            rw [hc] at hb
            cases hb
            exact agreeNew
        · simp only [List.any_append, List.any_cons, List.any_nil, hcs, Bool.or_false, Bool.or_true]
          cases hid : g.identity <;> simp
        · constructor
          · intro hn x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact (hinv.anchorNone.mp hn) x hx
            · simp only [List.mem_singleton] at hx; subst hx; exact hcs
          · intro hall
            exact hinv.anchorNone.mpr (fun x hx => hall x (List.mem_append_left _ hx))
        · intro v hv
          obtain ⟨x, hx, h1, h2⟩ := hinv.anchorWitness v hv
          exact ⟨x, List.mem_append_left _ hx, h1, h2⟩
        · intro v hv x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hinv.anchorAll v hv x hx
          · simp only [List.mem_singleton] at hx; subst hx; exact hcv v hv
        · exact hpn
        · exact hps
      cases han : g.anchor with
      | some v =>
        rw [han] at hstep
        simp only at hstep
        by_cases hcv : (c.value == v) = true
        · simp only [hcv, ↓reduceIte, Except.ok.injEq] at hstep
          subst hstep
          refine common g.pending _ ?_ (by simp [han]) (by intro _; exact hinv.pendingSome (by simp [han]))
            (by intro w hw; rw [han] at hw; cases hw; simpa using hcv)
          simp [GState.withCallable, han]
        · simp [hcv] at hstep
      | none =>
        rw [han] at hstep
        simp only [Except.ok.injEq] at hstep
        subst hstep
        refine common (g.pending ++ [c]) _ ?_ (by intro _; rw [hinv.pendingNone han]) (by simp [han])
          (by intro w hw; rw [han] at hw; cases hw)
        simp [GState.withCallable, han]
  | none =>
    rw [hc] at hstep
    simp only at hstep
    have hcn : c.callable.isSome = false := by simp [hc]
    cases han : g.anchor with
    | some v =>
      rw [han] at hstep
      simp only at hstep
      by_cases hcv : (c.value == v) = true
      · simp only [hcv, ↓reduceIte, Except.ok.injEq] at hstep
        subst hstep
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- the representative stays: `seen` is nonempty (the anchor's witness)
          obtain ⟨w, hw, -, -⟩ := hinv.anchorWitness v han
          obtain ⟨h0, t0, rfl⟩ : ∃ h0 t0, seen = h0 :: t0 := by
            cases seen with
            | nil => cases hw
            | cons h0 t0 => exact ⟨h0, t0, rfl⟩
          simp only [hinv.rep, List.find?_append, List.head?_append, List.find?_singleton, hcn,
            Bool.false_eq_true, ↓reduceIte, Option.or_none, List.head?_cons, Option.some_or]
        · intro i hi
          obtain ⟨x, hx, hxa⟩ := hinv.idPresent i hi
          exact ⟨x, List.mem_append_left _ hx, hxa⟩
        · intro x hx b hb
          rcases List.mem_append.mp hx with hx | hx
          · exact hinv.idAgrees x hx b hb
          · simp only [List.mem_singleton] at hx; subst hx; rw [hc] at hb; cases hb
        · simp [List.any_append, hinv.idSome, hcn]
        · constructor
          · intro hn; rw [han] at hn; cases hn
          · intro hall
            have := hall c (List.mem_append_right _ List.mem_cons_self)
            rw [hcn] at this; cases this
        · intro w hw
          obtain ⟨x, hx, h1, h2⟩ := hinv.anchorWitness w hw
          exact ⟨x, List.mem_append_left _ hx, h1, h2⟩
        · intro w hw x hx
          rw [han] at hw; cases hw
          rcases List.mem_append.mp hx with hx | hx
          · exact hinv.anchorAll v han x hx
          · simp only [List.mem_singleton] at hx; subst hx; simpa using hcv
        · intro hn; rw [han] at hn; cases hn
        · intro _; exact hinv.pendingSome (by simp [han])
      · simp [hcv] at hstep
    | none =>
      rw [han] at hstep
      simp only at hstep
      by_cases hall : (g.pending.all (fun p => p.value == c.value)) = true
      · simp only [hall, ↓reduceIte, Except.ok.injEq] at hstep
        subst hstep
        have hpend := hinv.pendingNone han
        have allCallable := hinv.anchorNone.mp han
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [GState.withAnchor]
          cases hany : seen.any (fun x => x.callable.isSome) with
          | true =>
            obtain ⟨x, hx⟩ := find?_some_of_any hany
            have hids : g.identity.isSome = true := by rw [hinv.idSome]; exact hany
            simp only [hids, ↓reduceIte, hinv.rep, List.find?_append, List.head?_append, hx, Option.some_or]
          | false =>
            -- every contribution seen is callable-bearing and none is: nothing was seen
            have hnil : seen = [] := by
              cases seen with
              | nil => rfl
              | cons x xs =>
                have h1 := allCallable x List.mem_cons_self
                have h2 := List.any_eq_false.mp hany x List.mem_cons_self
                simp [h1] at h2
            subst hnil
            have hids : g.identity.isSome = false := by rw [hinv.idSome]; rfl
            simp [hids, hcn]
        · intro i hi
          obtain ⟨x, hx, hxa⟩ := hinv.idPresent i hi
          exact ⟨x, List.mem_append_left _ hx, hxa⟩
        · intro x hx b hb
          rcases List.mem_append.mp hx with hx | hx
          · exact hinv.idAgrees x hx b hb
          · simp only [List.mem_singleton] at hx; subst hx; rw [hc] at hb; cases hb
        · simp [GState.withAnchor, List.any_append, hinv.idSome, hcn]
        · constructor
          · intro hn; cases hn
          · intro hall'
            have := hall' c (List.mem_append_right _ List.mem_cons_self)
            rw [hcn] at this; cases this
        · intro w hw
          simp only [GState.withAnchor, Option.some.injEq] at hw
          subst hw
          exact ⟨c, List.mem_append_right _ List.mem_cons_self, hc, rfl⟩
        · intro w hw x hx
          simp only [GState.withAnchor, Option.some.injEq] at hw
          subst hw
          rcases List.mem_append.mp hx with hx | hx
          · rw [hpend] at hall
            have := List.all_eq_true.mp hall x hx
            simpa using this
          · simp only [List.mem_singleton] at hx; subst hx; rfl
        · intro hn; cases hn
        · intro _; rfl
      · simp [hall] at hstep

/-- The fold keeps the invariant. -/
theorem ginv_fold : ∀ (seen : List Contribution) (g : GState) (cs : List Contribution) (r : GState),
    GInv seen g → gfold g cs = .ok r → GInv (seen ++ cs) r
  | seen, g, [], r, hinv, h => by simp [gfold] at h; subst h; simpa using hinv
  | seen, g, c :: cs, r, hinv, h => by
    simp only [gfold] at h
    split at h
    · cases h
    · rename_i next hstep
      have := ginv_fold (seen ++ [c]) next cs r (ginv_step hinv hstep) h
      simpa using this

/-! ### The laws on the stable domain -/

/-- RESULT 1 (§6 statement 6, the forward half): a successful fold is a compatible group, on the
    identity domain `CallableTransOn`. -/
theorem gfold_ok_compatible (L : List Contribution) (hT : CallableTransOn L) (r : GState)
    (h : gfold {} L = .ok r) : GroupCompatible L := by
  have hinv := ginv_fold [] {} L r ginv_empty h
  simp only [List.nil_append] at hinv
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb
    obtain ⟨i, hi, hsa⟩ := hinv.idAgrees x hx a ha
    obtain ⟨j, hj, hsb⟩ := hinv.idAgrees y hy b hb
    rw [hi] at hj; cases hj
    have hpi : Present L i := hinv.idPresent i hi
    exact hT a i b ⟨x, hx, ha⟩ hpi ⟨y, hy, hb⟩ (by rw [same_identity_symm]; exact hsa) hsb
  · rintro ⟨w, hw, hwn⟩ x hx y hy
    cases han : r.anchor with
    | none =>
      have := hinv.anchorNone.mp han w hw
      rw [hwn] at this; cases this
    | some v =>
      exact (hinv.anchorAll v han x hx).trans (hinv.anchorAll v han y hy).symm

/-- Success from a compatible group: every step of the fold succeeds. -/
theorem gfold_ok_of_compatible (L : List Contribution) (hL : GroupCompatible L) :
    ∀ (seen : List Contribution) (g : GState) (cs : List Contribution), GInv seen g →
      (∀ x ∈ seen, x ∈ L) → (∀ x ∈ cs, x ∈ L) → ∃ r, gfold g cs = .ok r
  | _, g, [], _, _, _ => ⟨g, rfl⟩
  | seen, g, c :: cs, hinv, hseen, hcs => by
    have hcL : c ∈ L := hcs c List.mem_cons_self
    have step : ∃ next, gstep g c = .ok next := by
      unfold gstep
      cases hc : c.callable with
      | some a =>
        simp only
        have hnc : g.conflictsWith a = false := by
          cases hid : g.identity with
          | none => simp [GState.conflictsWith, hid]
          | some i =>
            obtain ⟨x, hx, hxi⟩ := hinv.idPresent i hid
            have := hL.1 x (hseen x hx) c hcL i a hxi hc
            simp [GState.conflictsWith, hid, this]
        simp only [hnc, Bool.false_eq_true, ↓reduceIte]
        cases han : g.anchor with
        | none => exact ⟨_, rfl⟩
        | some v =>
          obtain ⟨w, hw, hwn, hwv⟩ := hinv.anchorWitness v han
          have heq := hL.2 ⟨w, hseen w hw, hwn⟩ c hcL w (hseen w hw)
          simp only [heq, hwv, beq_self_eq_true, ↓reduceIte]
          exact ⟨_, rfl⟩
      | none =>
        simp only
        cases han : g.anchor with
        | some v =>
          obtain ⟨w, hw, hwn, hwv⟩ := hinv.anchorWitness v han
          have heq := hL.2 ⟨c, hcL, hc⟩ c hcL w (hseen w hw)
          simp only [heq, hwv, beq_self_eq_true, ↓reduceIte]
          exact ⟨_, rfl⟩
        | none =>
          have hall : g.pending.all (fun p => p.value == c.value) = true := by
            rw [hinv.pendingNone han]
            apply List.all_eq_true.mpr
            intro x hx
            have := hL.2 ⟨c, hcL, hc⟩ x (hseen x hx) c hcL
            simp [this]
          simp only [hall, ↓reduceIte]
          exact ⟨_, rfl⟩
    obtain ⟨next, hnext⟩ := step
    obtain ⟨r, hr⟩ := gfold_ok_of_compatible L hL (seen ++ [c]) next cs (ginv_step hinv hnext)
      (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hseen x hx
        · simp only [List.mem_singleton] at hx; subst hx; exact hcL)
      (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
    exact ⟨r, by simp only [gfold, hnext]; exact hr⟩

/-- RESULT 1 (§6 statement 6): NEED-04 STABLE-DOMAIN CORRECTNESS — the group-aware fold succeeds
    exactly when the declarative group predicate holds, on the identity domain. -/
theorem gfold_ok_iff_compatible (L : List Contribution) (hT : CallableTransOn L) :
    (∃ r, gfold {} L = .ok r) ↔ GroupCompatible L :=
  ⟨fun ⟨r, hr⟩ => gfold_ok_compatible L hT r hr,
   fun h => gfold_ok_of_compatible L h [] {} L ginv_empty (fun _ hx => by cases hx) (fun _ hx => hx)⟩

theorem group_compatible_perm {l l' : List Contribution} (hp : l.Perm l') (h : GroupCompatible l) :
    GroupCompatible l' :=
  ⟨fun x hx y hy => h.1 x (hp.mem_iff.mpr hx) y (hp.mem_iff.mpr hy),
   fun ⟨w, hw, hwn⟩ x hx y hy => h.2 ⟨w, hp.mem_iff.mpr hw, hwn⟩ x (hp.mem_iff.mpr hx) y (hp.mem_iff.mpr hy)⟩

theorem callable_trans_on_perm {l l' : List Contribution} (hp : l.Perm l') (h : CallableTransOn l) :
    CallableTransOn l' := by
  intro a b c ha hb hc
  have pres : ∀ x, Present l' x → Present l x := fun x ⟨y, hy, hyx⟩ => ⟨y, hp.mem_iff.mpr hy, hyx⟩
  exact h a b c (pres a ha) (pres b hb) (pres c hc)

/-- RESULT 2 (§6 statement 7): STABLE SATISFIABILITY IS PERMUTATION INVARIANT — a permutation of
    the same stable contributions succeeds exactly when the original does. Nothing more: the
    demand schedule, which failure is reached first and its category are not invariant. -/
theorem gfold_satisfiable_perm (L L' : List Contribution) (hp : L.Perm L') (hT : CallableTransOn L) :
    (∃ r, gfold {} L = .ok r) ↔ (∃ r, gfold {} L' = .ok r) := by
  rw [gfold_ok_iff_compatible L hT, gfold_ok_iff_compatible L' (callable_trans_on_perm hp hT)]
  exact ⟨group_compatible_perm hp, group_compatible_perm hp.symm⟩

/-- RESULT 3 (§6 statement 8): THE ORIGINAL REPRESENTATIVE — for a fixed written order the
    representative is the FIRST callable-bearing contribution if there is one, otherwise the first
    contribution: one supplied contribution, carrying its own address, counted VALUE and CALLABLE
    together — never a pairing of one contribution's identity with another's VALUE. -/
theorem gfold_rep_first_richest (c : Contribution) (cs : List Contribution) (r : GState)
    (h : gfold {} (c :: cs) = .ok r) :
    r.rep = some (((c :: cs).find? (fun x => x.callable.isSome)).getD c) := by
  have hinv := ginv_fold [] {} (c :: cs) r ginv_empty h
  simp only [List.nil_append] at hinv
  rw [hinv.rep, List.head?_cons, Option.or_some]

theorem gfold_rep_mem (c : Contribution) (cs : List Contribution) (r : GState)
    (h : gfold {} (c :: cs) = .ok r) : ∃ x ∈ c :: cs, r.rep = some x := by
  refine ⟨_, ?_, gfold_rep_first_richest c cs r h⟩
  cases hf : (c :: cs).find? (fun x => x.callable.isSome) with
  | none => exact List.mem_cons_self
  | some x => exact List.mem_of_find?_eq_some hf

/-- The representative has a callable identity iff some contribution has. -/
theorem gfold_rep_callable_isSome_iff (c : Contribution) (cs : List Contribution) (r : GState)
    (h : gfold {} (c :: cs) = .ok r) (x : Contribution) (hx : r.rep = some x) :
    x.callable.isSome = true ↔ ∃ y ∈ c :: cs, y.callable.isSome = true := by
  rw [gfold_rep_first_richest c cs r h] at hx
  cases hx
  constructor
  · intro hs
    cases hf : (c :: cs).find? (fun x => x.callable.isSome) with
    | none =>
      rw [hf] at hs
      exact ⟨c, List.mem_cons_self, hs⟩
    | some y =>
      exact ⟨y, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
  · rintro ⟨y, hy, hys⟩
    obtain ⟨z, hz⟩ := find?_some_of_any (List.any_eq_true.mpr ⟨y, hy, hys⟩)
    rw [hz]
    simpa using List.find?_some hz

/-- RESULT 4 (§6 statement 9, mixed half): CONDITIONAL VALUE PRESERVATION — when some
    contribution is value-only, every successful order binds a representative of the SAME counted
    VALUE. -/
theorem gfold_perm_preserves_value_mixed (c d : Contribution) (cs ds : List Contribution)
    (hp : (c :: cs).Perm (d :: ds)) (hT : CallableTransOn (c :: cs))
    (hmix : ∃ x ∈ c :: cs, x.callable = none) (r r' : GState)
    (h : gfold {} (c :: cs) = .ok r) (h' : gfold {} (d :: ds) = .ok r') :
    ∃ x y, r.rep = some x ∧ r'.rep = some y ∧ x.value = y.value := by
  have hcomp := gfold_ok_compatible (c :: cs) hT r h
  obtain ⟨x, hx, hrx⟩ := gfold_rep_mem c cs r h
  obtain ⟨y, hy, hry⟩ := gfold_rep_mem d ds r' h'
  exact ⟨x, y, hrx, hry, hcomp.2 hmix x hx y (hp.mem_iff.mpr hy)⟩

/-- The explicit COHERENCE premise a reference-only group needs for VALUE preservation:
    contributions of the same identity have the same counted VALUE. NEED-04 never checks it. -/
def Coherent (l : List Contribution) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, ∀ a b, x.callable = some a → y.callable = some b →
    sameRepeatedCallableIdentity a b = true → x.value = y.value

/-- RESULT 4 (§6 statement 9, reference half): under the COHERENCE premise every successful order
    binds a representative of the same counted VALUE; without it a reference-only group may bind
    representatives of different VALUEs (`RepeatedNameGuards`: the equal-identity, unequal-VALUE
    witness). -/
theorem gfold_perm_preserves_value_of_coherent (c d : Contribution) (cs ds : List Contribution)
    (hp : (c :: cs).Perm (d :: ds)) (hT : CallableTransOn (c :: cs)) (hcoh : Coherent (c :: cs))
    (r r' : GState) (h : gfold {} (c :: cs) = .ok r) (h' : gfold {} (d :: ds) = .ok r') :
    ∃ x y, r.rep = some x ∧ r'.rep = some y ∧ x.value = y.value := by
  by_cases hmix : ∃ x ∈ c :: cs, x.callable = none
  · exact gfold_perm_preserves_value_mixed c d cs ds hp hT hmix r r' h h'
  · have hcomp := gfold_ok_compatible (c :: cs) hT r h
    obtain ⟨x, hx, hrx⟩ := gfold_rep_mem c cs r h
    obtain ⟨y, hy, hry⟩ := gfold_rep_mem d ds r' h'
    have hy' := hp.mem_iff.mpr hy
    have callableOf : ∀ z ∈ c :: cs, ∃ a, z.callable = some a := by
      intro z hz
      cases hzc : z.callable with
      | none => exact absurd ⟨z, hz, hzc⟩ hmix
      | some a => exact ⟨a, rfl⟩
    obtain ⟨a, ha⟩ := callableOf x hx
    obtain ⟨b, hb⟩ := callableOf y hy'
    exact ⟨x, y, hrx, hry, hcoh x hx y hy' a b ha hb (hcomp.1 x hx y hy' a b ha hb)⟩

/-- PERMUTATION PRESERVES IDENTITY AND AVAILABILITY of a successful binding's representative:
    callable availability and callable identity (up to `sameRepeatedCallableIdentity`). -/
theorem gfold_perm_preserves_identity (c d : Contribution) (cs ds : List Contribution)
    (hp : (c :: cs).Perm (d :: ds)) (hT : CallableTransOn (c :: cs)) (r r' : GState)
    (h : gfold {} (c :: cs) = .ok r) (h' : gfold {} (d :: ds) = .ok r') :
    ∃ x y, r.rep = some x ∧ r'.rep = some y ∧ x.callable.isSome = y.callable.isSome ∧
      (∀ a b, x.callable = some a → y.callable = some b → sameRepeatedCallableIdentity a b = true) := by
  have hcomp := gfold_ok_compatible (c :: cs) hT r h
  obtain ⟨x, hx, hrx⟩ := gfold_rep_mem c cs r h
  obtain ⟨y, hy, hry⟩ := gfold_rep_mem d ds r' h'
  refine ⟨x, y, hrx, hry, ?_, fun a b ha hb => hcomp.1 x hx y (hp.mem_iff.mpr hy) a b ha hb⟩
  have e1 := gfold_rep_callable_isSome_iff c cs r h x hrx
  have e2 := gfold_rep_callable_isSome_iff d ds r' h' y hry
  have e3 : (∃ z ∈ c :: cs, z.callable.isSome = true) ↔ (∃ z ∈ d :: ds, z.callable.isSome = true) :=
    ⟨fun ⟨z, hz, h⟩ => ⟨z, hp.mem_iff.mp hz, h⟩, fun ⟨z, hz, h⟩ => ⟨z, hp.mem_iff.mpr hz, h⟩⟩
  rw [Bool.eq_iff_iff, e1, e2]
  exact e3

/-- THE PAIRWISE SHORTCUT IS WRONG: a value-only contribution must check EVERY callable
    contribution's own VALUE, so two equal identities with different VALUEs never agree with a
    value anchor, whichever of them the anchor would meet first. -/
theorem gfold_anchor_checks_every_reference (x y z : Contribution) (a : Algorithm)
    (hx : x.callable = some a) (hy : y.callable = some a) (hz : z.callable = none)
    (hxz : x.value = z.value) (hyz : y.value ≠ z.value) :
    gfold {} [x, y, z] = .error .value ∧ gfold {} [y, x, z] = .error .value := by
  have hya : (y.value == z.value) = false := by simpa using hyz
  constructor
  · simp [gfold, gstep, GState.conflictsWith, GState.withCallable, hx, hy, hz, same_identity_refl, hxz, hya]
  · simp [gfold, gstep, GState.conflictsWith, GState.withCallable, hx, hy, hz, same_identity_refl, hya]

/-! ## The production traversal computes the fold (§6 statement 13) -/

/-- STABLE OBSERVATIONS of a capability record on the cells `cells`, along an invariant `Inv` of
    the semantic state: every VALUE demand and CALLABLE projection of such a cell returns the
    cell's FIXED observation `obs` and re-establishes `Inv`. This is the "stable completed
    contribution" domain: it does NOT hold of a cell whose first demand fails, depends on the
    state, or is still suspended with a state-dependent outcome. -/
structure Stable (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat) : Prop where
  value : ∀ a ∈ cells, ∀ s, Inv s → ∃ t, runEval (k.value a) s = (.ok (obs a).1, t) ∧ Inv t
  callable : ∀ a ∈ cells, ∀ s, Inv s → ∃ t, runEval (k.callable a) s = (.ok (obs a).2, t) ∧ Inv t

/-- The contribution a stable cell makes. -/
def contrib (obs : Nat → CountedResult × Option Algorithm) (a : Nat) : Contribution :=
  ⟨a, (obs a).1, (obs a).2⟩

/-- LOCAL pure form of NEED-04's data-anchor check over fixed observations. -/
def checkAnchorPure (obs : Nat → CountedResult × Option Algorithm) (name : Ident) (anchor : CountedResult)
    (family : Bool) : List Nat → Except Error Bool
  | [] => .ok true
  | cell :: rest =>
    if ((obs cell).1 == anchor) = true then checkAnchorPure obs name anchor family rest
    else if family then .ok false
    else .error (Error.withContext (repeatedParameterContext name) Error.badArity)

/-- The pure check agrees exactly when every cell's VALUE equals the anchor. -/
theorem checkAnchorPure_eq (obs : Nat → CountedResult × Option Algorithm) (name : Ident)
    (anchor : CountedResult) (family : Bool) : ∀ cells : List Nat,
    checkAnchorPure obs name anchor family cells
      = if cells.all (fun c => (obs c).1 == anchor) then .ok true
        else if family then .ok false
        else .error (Error.withContext (repeatedParameterContext name) Error.badArity)
  | [] => rfl
  | cell :: rest => by
    simp only [checkAnchorPure, List.all_cons]
    by_cases h : ((obs cell).1 == anchor) = true
    · simp only [h, ↓reduceIte, Bool.true_and]
      exact checkAnchorPure_eq obs name anchor family rest
    · simp [h]

/-- The data-anchor check, production: on stable cells it returns `checkAnchorPure`. -/
theorem checkAnchor_production (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat) (hk : Stable k Inv obs cells)
    (name : Ident) (anchor : CountedResult) (family : Bool) :
    ∀ (cs : List Nat) (s : EvalState), (∀ a ∈ cs, a ∈ cells) → Inv s →
      ∃ t, Inv t ∧ runEval (NeedBinder.checkAnchor k name anchor family cs) s
        = (checkAnchorPure obs name anchor family cs, t)
  | [], s, _, hs => ⟨s, hs, rfl⟩
  | cell :: rest, s, hc, hs => by
    rw [checkAnchor_run k name anchor family cell rest s]
    obtain ⟨t1, h1, i1⟩ := hk.value cell (hc cell List.mem_cons_self) s hs
    simp only [h1]
    by_cases h : ((obs cell).1 == anchor) = true
    · simp only [h, ↓reduceIte, checkAnchorPure]
      exact checkAnchor_production k Inv obs cells hk name anchor family rest t1
        (fun a ha => hc a (List.mem_cons_of_mem _ ha)) i1
    · exact ⟨t1, i1, by simp only [h, checkAnchorPure, Bool.false_eq_true, ↓reduceIte]⟩

/-- LOCAL pure form of one `NeedBinder.bindName` occurrence over fixed observations (NEED-04,
    group-aware); proved to be the production run by `name_step_production`. -/
def nameStep (obs : Nat → CountedResult × Option Algorithm) (repeated : List Ident) (family : Bool)
    (state : NeedBindState) (name : Ident) (address : Nat) : Except Error (Option NeedBindState) :=
  if repeated.contains name then
    match (obs address).2 with
    | some identity =>
      if (state.groupOf name).conflictsWith identity = true then
        (if family then .ok none
          else .error (Error.typeMismatch "Repeated bind equality requires the same callable identity"))
      else
        match (state.groupOf name).anchor with
        | some anchor =>
          match checkAnchorPure obs name anchor family [address] with
          | .error e => .error e
          | .ok agreed => .ok (if agreed then some (state.withCallable name address identity) else none)
        | none => .ok (some (state.withCallable name address identity))
    | none =>
      match (state.groupOf name).anchor with
      | some anchor =>
        if ((obs address).1 == anchor) = true then .ok (some state)
        else (if family then .ok none
          else .error (Error.withContext (repeatedParameterContext name) Error.badArity))
      | none =>
        match checkAnchorPure obs name (obs address).1 family (state.groupOf name).pending with
        | .error e => .error e
        | .ok agreed => .ok (if agreed then some (state.withAnchor name address (obs address).1) else none)
  else .ok (some (state.withPlain name address))

/-- The cells a binder state holds: its representatives and its pending obligations. -/
def StateIn (cells : List Nat) (state : NeedBindState) : Prop :=
  (∀ e ∈ state.bound, e.2 ∈ cells) ∧ ∀ name, ∀ a ∈ (state.groupOf name).pending, a ∈ cells

theorem stateIn_empty (cells : List Nat) : StateIn cells {} :=
  ⟨fun _ h => (by cases h), fun name a ha => (by simp [NeedBindState.groupOf, lookupAssoc] at ha)⟩

theorem rebind_cells (cells : List Nat) (bound : NeedEnv) (name : Ident) (address : Nat)
    (ha : address ∈ cells) (hb : ∀ e ∈ bound, e.2 ∈ cells) : ∀ e ∈ bound.rebind name address, e.2 ∈ cells := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hb e (List.mem_filter.mp he).1
  · simp at he; subst he; exact ha

theorem stateIn_withPlain {cells : List Nat} {state : NeedBindState} (h : StateIn cells state) (name : Ident)
    {address : Nat} (ha : address ∈ cells) : StateIn cells (state.withPlain name address) :=
  ⟨rebind_cells cells _ name address ha h.1, h.2⟩

theorem stateIn_withCallable {cells : List Nat} {state : NeedBindState} (h : StateIn cells state) (name : Ident)
    {address : Nat} (ha : address ∈ cells) (identity : Algorithm) :
    StateIn cells (state.withCallable name address identity) := by
  refine ⟨?_, ?_⟩
  · unfold NeedBindState.withCallable
    dsimp only
    show ∀ e ∈ (if (state.groupOf name).identity.isSome then state.bound else state.bound.rebind name address),
      e.2 ∈ cells
    split
    · exact h.1
    · exact rebind_cells cells _ name address ha h.1
  · intro n a hmem
    rw [BinderCorrespondence.groupOf_withCallable] at hmem
    split at hmem
    · dsimp only at hmem
      split at hmem
      · exact h.2 name a hmem
      · rcases List.mem_append.mp hmem with hmem | hmem
        · exact h.2 name a hmem
        · simp only [List.mem_singleton] at hmem; subst hmem; exact ha
    · exact h.2 n a hmem

theorem stateIn_withAnchor {cells : List Nat} {state : NeedBindState} (h : StateIn cells state) (name : Ident)
    {address : Nat} (ha : address ∈ cells) (anchor : CountedResult) :
    StateIn cells (state.withAnchor name address anchor) := by
  refine ⟨?_, ?_⟩
  · unfold NeedBindState.withAnchor
    dsimp only
    show ∀ e ∈ (if (state.groupOf name).identity.isSome then state.bound else state.bound.rebind name address),
      e.2 ∈ cells
    split
    · exact h.1
    · exact rebind_cells cells _ name address ha h.1
  · intro n a hmem
    rw [BinderCorrespondence.groupOf_withAnchor] at hmem
    split at hmem
    · simp at hmem
    · exact h.2 n a hmem

/-- ONE OCCURRENCE, production: on stable cells the generic core's `bindName` (hence the
    production `bindNeedName`) returns exactly `nameStep`. -/
theorem name_step_production (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat) (hk : Stable k Inv obs cells)
    (name : Ident) (address : Nat) (repeated : List Ident) (bound : NeedBindState) (family : Bool)
    (s : EvalState) (ha : address ∈ cells) (hb : StateIn cells bound) (hs : Inv s) :
    ∃ t, Inv t ∧ runEval (NeedBinder.bindName k name address repeated bound family) s
      = (nameStep obs repeated family bound name address, t) := by
  by_cases hr : repeated.contains name = true
  · rw [repeated_name_binding k name address repeated bound family s hr]
    obtain ⟨t1, h1, i1⟩ := hk.callable address ha s hs
    rw [h1]
    cases hc : (obs address).2 with
    | some identity =>
      simp only
      by_cases hcf : (bound.groupOf name).conflictsWith identity = true
      · exact ⟨t1, i1, by simp only [hcf, ↓reduceIte, nameStep, hr, hc]⟩
      · cases hanc : (bound.groupOf name).anchor with
        | none => exact ⟨t1, i1, by simp only [hcf, Bool.false_eq_true, ↓reduceIte, hanc, nameStep, hr, hc]⟩
        | some anchor =>
          obtain ⟨t2, i2, h2⟩ := checkAnchor_production k Inv obs cells hk name anchor family [address] t1
            (by simpa using ha) i1
          refine ⟨t2, i2, ?_⟩
          simp only [hcf, Bool.false_eq_true, ↓reduceIte, hanc, h2, nameStep, hr, hc]
          cases checkAnchorPure obs name anchor family [address] <;> rfl
    | none =>
      simp only
      obtain ⟨t2, h2, i2⟩ := hk.value address ha t1 i1
      rw [h2]
      simp only
      cases hanc : (bound.groupOf name).anchor with
      | some anchor =>
        refine ⟨t2, i2, ?_⟩
        simp only [hanc, nameStep, hr, hc, ↓reduceIte]
        by_cases hv : ((obs address).fst == anchor) = true <;> simp [hv]
      | none =>
        obtain ⟨t3, i3, h3⟩ := checkAnchor_production k Inv obs cells hk name (obs address).1 family
          (bound.groupOf name).pending t2 (hb.2 name) i2
        refine ⟨t3, i3, ?_⟩
        simp only [hanc, h3, nameStep, hr, hc, ↓reduceIte]
        cases checkAnchorPure obs name (obs address).1 family (bound.groupOf name).pending <;> rfl
  · have hr' : repeated.contains name = false := by simpa using hr
    rw [BinderCore.core_plain_name_is_pure k name address repeated bound family hr']
    exact ⟨s, hs, by simp only [runEval_pure, nameStep, hr', Bool.false_eq_true, ↓reduceIte]⟩

/-- A successful occurrence keeps the binder state's cells among `cells`. -/
theorem nameStep_cells (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat)
    (repeated : List Ident) (family : Bool) (bound : NeedBindState) (name : Ident) (address : Nat)
    (next : NeedBindState) (ha : address ∈ cells) (hb : StateIn cells bound)
    (h : nameStep obs repeated family bound name address = .ok (some next)) : StateIn cells next := by
  unfold nameStep at h
  split at h
  · split at h
    · split at h
      · cases family <;> simp at h
      · split at h
        · split at h
          · cases h
          · split at h
            · cases h; exact stateIn_withCallable hb name ha _
            · cases h
        · cases h; exact stateIn_withCallable hb name ha _
    · split at h
      · split at h
        · cases h; exact hb
        · cases family <;> simp at h
      · split at h
        · cases h
        · split at h
          · cases h; exact stateIn_withAnchor hb name ha _
          · cases h
  · cases h; exact stateIn_withPlain hb name ha

/-- LOCAL pure form of a flat level of name patterns over fixed observations: the occurrences
    in written order, the first non-match or failure ending the level. -/
def flatBind (obs : Nat → CountedResult × Option Algorithm) (repeated : List Ident) (family : Bool) :
    NeedBindState → List (Ident × Nat) → Except Error (Option NeedBindState)
  | bound, [] => .ok (some bound)
  | bound, (n, a) :: rest =>
    match nameStep obs repeated family bound n a with
    | .ok (some next) => flatBind obs repeated family next rest
    | other => other

/-- The name patterns of a flat level. -/
def namePatterns (pairs : List (Ident × Nat)) : List NeedPattern := pairs.map (fun p => NeedPattern.bind p.1)

/-- Its supplied cells, one per pattern. -/
def cellSources (pairs : List (Ident × Nat)) : List (NeedSource Nat) := pairs.map (fun p => NeedSource.cell p.2)

/-- A FLAT LEVEL, production: the generic core's `bindSources` over a flat level of name
    patterns, each from its supplied stable cell, returns exactly `flatBind`. -/
theorem flat_level_is_flatBind (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat) (hk : Stable k Inv obs cells)
    (repeated : List Ident) (family : Bool) :
    ∀ (pairs : List (Ident × Nat)) (bound : NeedBindState) (s : EvalState),
      (∀ p ∈ pairs, p.2 ∈ cells) → StateIn cells bound → Inv s →
      ∃ t, Inv t ∧ runEval (NeedBinder.bindSources k (namePatterns pairs) (cellSources pairs) repeated bound family) s
        = (flatBind obs repeated family bound pairs, t)
  | [], bound, s, _, _, hs => ⟨s, hs, rfl⟩
  | (n, a) :: rest, bound, s, hp, hb, hs => by
      have ha : a ∈ cells := hp (n, a) List.mem_cons_self
      obtain ⟨t1, i1, h1⟩ := name_step_production k Inv obs cells hk n a repeated bound family s ha hb hs
      simp only [namePatterns, cellSources, List.map_cons, NeedBinder.bindSources, List.headD_cons,
        List.tail_cons, NeedBinder.sourceAddress, runEval_bind, runEval_pure, thenRun_ok, NeedBinder.bindOne]
      rw [h1]
      cases hns : nameStep obs repeated family bound n a with
      | error e => exact ⟨t1, i1, by simp [flatBind, hns]⟩
      | ok r =>
        cases r with
        | none => exact ⟨t1, i1, by simp [flatBind, hns]⟩
        | some next =>
          have hnext := nameStep_cells obs cells repeated family bound n a next ha hb hns
          obtain ⟨t, it, ht⟩ := flat_level_is_flatBind k Inv obs cells hk repeated family rest next t1
            (fun p hp' => hp p (List.mem_cons_of_mem _ hp')) hnext i1
          refine ⟨t, it, ?_⟩
          simp only [namePatterns, cellSources] at ht
          simp only [thenRun_ok]
          rw [ht]
          simp [flatBind, hns]

/-! ### Each repeated name's binding is its own `gfold` over its own occurrences -/

/-- The occurrences of `X` in a flat level, in written order. -/
def occ (X : Ident) (pairs : List (Ident × Nat)) : List Nat :=
  (pairs.filter (fun p => p.1 == X)).map Prod.snd

theorem occ_cons (X n : Ident) (a : Nat) (rest : List (Ident × Nat)) :
    occ X ((n, a) :: rest) = if n = X then a :: occ X rest else occ X rest := by
  by_cases h : n = X <;> simp [occ, h]

/-- The observation-level VIEW of a binder state at one name: its representative's contribution
    and its agreement state, pending cells as contributions. -/
def view (obs : Nat → CountedResult × Option Algorithm) (state : NeedBindState) (X : Ident) : GState where
  rep := (lookupAssoc X state.bound).map (contrib obs)
  identity := (state.groupOf X).identity
  anchor := (state.groupOf X).anchor
  pending := (state.groupOf X).pending.map (contrib obs)

theorem view_empty (obs : Nat → CountedResult × Option Algorithm) (X : Ident) : view obs {} X = {} := rfl

/-- How a mismatch surfaces: the family's non-match, or the refusing comparison's ordinary error. -/
def conflictOutcome (name : Ident) (c : Conflict) (family : Bool) : Except Error (Option NeedBindState) :=
  if family then .ok none
  else match c with
    | .value => .error (Error.withContext (repeatedParameterContext name) Error.badArity)
    | .callable => .error (Error.typeMismatch "Repeated bind equality requires the same callable identity")

@[simp] theorem setGroup_bound (state : NeedBindState) (n : Ident) (g : RepeatedGroup) :
    (state.setGroup n g).bound = state.bound := rfl

theorem withCallable_bound (state : NeedBindState) (n : Ident) (a : Nat) (identity : Algorithm) :
    (state.withCallable n a identity).bound
      = if (state.groupOf n).identity.isSome then state.bound else state.bound.rebind n a := rfl

theorem withAnchor_bound (state : NeedBindState) (n : Ident) (a : Nat) (anchor : CountedResult) :
    (state.withAnchor n a anchor).bound
      = if (state.groupOf n).identity.isSome then state.bound else state.bound.rebind n a := rfl

theorem view_withCallable_self (obs : Nat → CountedResult × Option Algorithm) (state : NeedBindState)
    (n : Ident) (a : Nat) (identity : Algorithm) :
    view obs (state.withCallable n a identity) n = (view obs state n).withCallable (contrib obs a) identity := by
  have hg := BinderCorrespondence.groupOf_withCallable state n n a identity
  rw [if_pos rfl] at hg
  simp only [view, GState.withCallable, withCallable_bound, hg]
  by_cases h1 : (state.groupOf n).identity.isSome = true <;>
    by_cases h2 : (state.groupOf n).anchor.isSome = true <;>
    simp [h1, h2, NeedEnv.rebind, BinderCorrespondence.lookupAssoc_rebind]

theorem view_withAnchor_self (obs : Nat → CountedResult × Option Algorithm) (state : NeedBindState)
    (n : Ident) (a : Nat) :
    view obs (state.withAnchor n a (obs a).1) n = (view obs state n).withAnchor (contrib obs a) := by
  have hg := BinderCorrespondence.groupOf_withAnchor state n n a (obs a).1
  rw [if_pos rfl] at hg
  simp only [view, GState.withAnchor, withAnchor_bound, hg]
  by_cases h1 : (state.groupOf n).identity.isSome = true <;>
    simp [h1, NeedEnv.rebind, BinderCorrespondence.lookupAssoc_rebind, contrib]

theorem view_withCallable_other (obs : Nat → CountedResult × Option Algorithm) (state : NeedBindState)
    (n X : Ident) (a : Nat) (identity : Algorithm) (hX : X ≠ n) :
    view obs (state.withCallable n a identity) X = view obs state X := by
  have hg := BinderCorrespondence.groupOf_withCallable state n X a identity
  rw [if_neg hX] at hg
  simp only [view, withCallable_bound, hg]
  by_cases h1 : (state.groupOf n).identity.isSome = true <;>
    simp [h1, NeedEnv.rebind, BinderCorrespondence.lookupAssoc_rebind, hX]

theorem view_withAnchor_other (obs : Nat → CountedResult × Option Algorithm) (state : NeedBindState)
    (n X : Ident) (a : Nat) (anchor : CountedResult) (hX : X ≠ n) :
    view obs (state.withAnchor n a anchor) X = view obs state X := by
  have hg := BinderCorrespondence.groupOf_withAnchor state n X a anchor
  rw [if_neg hX] at hg
  simp only [view, withAnchor_bound, hg]
  by_cases h1 : (state.groupOf n).identity.isSome = true <;>
    simp [h1, NeedEnv.rebind, BinderCorrespondence.lookupAssoc_rebind, hX]

theorem view_withPlain_other (obs : Nat → CountedResult × Option Algorithm) (state : NeedBindState)
    (n X : Ident) (a : Nat) (hX : X ≠ n) : view obs (state.withPlain n a) X = view obs state X := by
  simp [view, NeedBindState.withPlain, NeedEnv.rebind, BinderCorrespondence.lookupAssoc_rebind, hX,
    NeedBindState.groupOf]

/-- THE PRODUCTION VERDICT OF A REPEATED OCCURRENCE IS `gstep` OF ITS VIEW: when `gstep` accepts,
    the occurrence binds, its name's view becomes `gstep`'s state and every other name's view is
    unchanged; when `gstep` refuses, the occurrence's outcome is that conflict's. -/
theorem nameStep_view (obs : Nat → CountedResult × Option Algorithm) (repeated : List Ident)
    (family : Bool) (state : NeedBindState) (n : Ident) (a : Nat) (hr : repeated.contains n = true) :
    (∀ g', gstep (view obs state n) (contrib obs a) = .ok g' →
      ∃ next, nameStep obs repeated family state n a = .ok (some next) ∧ view obs next n = g' ∧
        ∀ X, X ≠ n → view obs next X = view obs state X) ∧
    (∀ c, gstep (view obs state n) (contrib obs a) = .error c →
      nameStep obs repeated family state n a = conflictOutcome n c family) := by
  have hrm : n ∈ repeated := by simpa using hr
  have hconf : ∀ i, (view obs state n).conflictsWith i = (state.groupOf n).conflictsWith i := by
    intro i
    simp only [GState.conflictsWith, RepeatedGroup.conflictsWith, view]
    cases (state.groupOf n).identity <;> rfl
  have hpend : ((view obs state n).pending.all (fun p => p.value == (contrib obs a).value))
      = ((state.groupOf n).pending.all (fun c => (obs c).1 == (obs a).1)) := by
    simp [view, contrib, List.all_map]
    rfl
  constructor
  · intro g' hg
    unfold gstep at hg
    cases hc : (obs a).2 with
    | some identity =>
      have hca : (contrib obs a).callable = some identity := by simp [contrib, hc]
      rw [hca] at hg
      simp only [hconf] at hg
      by_cases hcf : (state.groupOf n).conflictsWith identity = true
      · simp [hcf] at hg
      · simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hg
        cases hanc : (state.groupOf n).anchor with
        | none =>
          have hva : (view obs state n).anchor = none := by simp [view, hanc]
          rw [hva] at hg
          simp only [Except.ok.injEq] at hg
          subst hg
          refine ⟨state.withCallable n a identity, ?_, view_withCallable_self obs state n a identity,
            fun X hX => view_withCallable_other obs state n X a identity hX⟩
          simp [nameStep, hrm, hc, hcf, hanc]
        | some anchor =>
          have hva : (view obs state n).anchor = some anchor := by simp [view, hanc]
          rw [hva] at hg
          simp only at hg
          by_cases hv : ((contrib obs a).value == anchor) = true
          · simp only [hv, ↓reduceIte, Except.ok.injEq] at hg
            subst hg
            have hv' : ((obs a).1 == anchor) = true := by simpa [contrib] using hv
            refine ⟨state.withCallable n a identity, ?_, view_withCallable_self obs state n a identity,
              fun X hX => view_withCallable_other obs state n X a identity hX⟩
            simp [nameStep, hrm, hc, hcf, hanc, checkAnchorPure, hv']
          · simp [hv] at hg
    | none =>
      have hca : (contrib obs a).callable = none := by simp [contrib, hc]
      rw [hca] at hg
      simp only at hg
      cases hanc : (state.groupOf n).anchor with
      | some anchor =>
        have hva : (view obs state n).anchor = some anchor := by simp [view, hanc]
        rw [hva] at hg
        simp only at hg
        by_cases hv : ((contrib obs a).value == anchor) = true
        · simp only [hv, ↓reduceIte, Except.ok.injEq] at hg
          subst hg
          have hv' : ((obs a).1 == anchor) = true := by simpa [contrib] using hv
          exact ⟨state, by simp [nameStep, hrm, hc, hanc, hv'], rfl, fun _ _ => rfl⟩
        · simp [hv] at hg
      | none =>
        have hva : (view obs state n).anchor = none := by simp [view, hanc]
        rw [hva] at hg
        simp only at hg
        rw [hpend] at hg
        by_cases hall : ((state.groupOf n).pending.all (fun c => (obs c).1 == (obs a).1)) = true
        · simp only [hall, ↓reduceIte, Except.ok.injEq] at hg
          subst hg
          refine ⟨state.withAnchor n a (obs a).1, ?_, view_withAnchor_self obs state n a,
            fun X hX => view_withAnchor_other obs state n X a _ hX⟩
          simp [nameStep, hrm, hc, hanc, checkAnchorPure_eq, hall]
        · simp [hall] at hg
  · intro c hg
    unfold gstep at hg
    cases hc : (obs a).2 with
    | some identity =>
      have hca : (contrib obs a).callable = some identity := by simp [contrib, hc]
      rw [hca] at hg
      simp only [hconf] at hg
      by_cases hcf : (state.groupOf n).conflictsWith identity = true
      · simp only [hcf, ↓reduceIte, Except.error.injEq] at hg
        subst hg
        cases family <;> simp [nameStep, hrm, hc, hcf, conflictOutcome]
      · simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hg
        cases hanc : (state.groupOf n).anchor with
        | none =>
          have hva : (view obs state n).anchor = none := by simp [view, hanc]
          rw [hva] at hg
          simp at hg
        | some anchor =>
          have hva : (view obs state n).anchor = some anchor := by simp [view, hanc]
          rw [hva] at hg
          simp only at hg
          by_cases hv : ((contrib obs a).value == anchor) = true
          · simp [hv] at hg
          · simp only [hv, Bool.false_eq_true, ↓reduceIte, Except.error.injEq] at hg
            subst hg
            have hv' : ((obs a).1 == anchor) = false := by simpa [contrib] using hv
            cases family <;> simp [nameStep, hrm, hc, hcf, hanc, checkAnchorPure, hv', conflictOutcome]
    | none =>
      have hca : (contrib obs a).callable = none := by simp [contrib, hc]
      rw [hca] at hg
      simp only at hg
      cases hanc : (state.groupOf n).anchor with
      | some anchor =>
        have hva : (view obs state n).anchor = some anchor := by simp [view, hanc]
        rw [hva] at hg
        simp only at hg
        by_cases hv : ((contrib obs a).value == anchor) = true
        · simp [hv] at hg
        · simp only [hv, Bool.false_eq_true, ↓reduceIte, Except.error.injEq] at hg
          subst hg
          have hv' : ((obs a).1 == anchor) = false := by simpa [contrib] using hv
          cases family <;> simp [nameStep, hrm, hc, hanc, hv', conflictOutcome]
      | none =>
        have hva : (view obs state n).anchor = none := by simp [view, hanc]
        rw [hva] at hg
        simp only at hg
        rw [hpend] at hg
        by_cases hall : ((state.groupOf n).pending.all (fun c => (obs c).1 == (obs a).1)) = true
        · simp [hall] at hg
        · simp only [hall, Bool.false_eq_true, ↓reduceIte, Except.error.injEq] at hg
          subst hg
          have hall' : ((state.groupOf n).pending.all (fun c => (obs c).1 == (obs a).1)) = false := by
            simpa using hall
          cases family <;> simp [nameStep, hrm, hc, hanc, checkAnchorPure_eq, hall', conflictOutcome]

/-- A conflict outcome never continues the level. -/
theorem conflictOutcome_stops (name : Ident) (c : Conflict) (family : Bool) (next : NeedBindState) :
    conflictOutcome name c family ≠ .ok (some next) := by
  unfold conflictOutcome
  cases family <;> cases c <;> simp

/-- A non-repeated name never changes a repeated name's view. -/
theorem nameStep_plain_view (obs : Nat → CountedResult × Option Algorithm) (repeated : List Ident)
    (family : Bool) (state : NeedBindState) (n : Ident) (a : Nat) (hr : repeated.contains n = false) :
    nameStep obs repeated family state n a = .ok (some (state.withPlain n a)) := by
  simp only [nameStep, hr, Bool.false_eq_true, ↓reduceIte]

/-- SOUNDNESS OF THE PROJECTION: when the flat level binds, every repeated name's final view is
    its own `gfold` over its own occurrences, from its view before the level. -/
theorem flatBind_per_name (obs : Nat → CountedResult × Option Algorithm) (repeated : List Ident)
    (family : Bool) :
    ∀ (pairs : List (Ident × Nat)) (bound env : NeedBindState),
      flatBind obs repeated family bound pairs = .ok (some env) → ∀ X, repeated.contains X = true →
        gfold (view obs bound X) ((occ X pairs).map (contrib obs)) = .ok (view obs env X)
  | [], bound, env, h, X, _ => by
      simp [flatBind] at h; subst h; rfl
  | (n, a) :: rest, bound, env, h, X, hX => by
      simp only [flatBind] at h
      by_cases hrn : repeated.contains n = true
      · obtain ⟨hok, herr⟩ := nameStep_view obs repeated family bound n a hrn
        cases hg : gstep (view obs bound n) (contrib obs a) with
        | error c =>
          rw [herr c hg] at h
          unfold conflictOutcome at h
          cases family <;> cases c <;> simp at h
        | ok g' =>
          obtain ⟨next, hns, hv, hother⟩ := hok g' hg
          rw [hns] at h
          have ih := flatBind_per_name obs repeated family rest next env h X hX
          rw [occ_cons]
          by_cases hnX : n = X
          · subst hnX
            simp only [↓reduceIte, List.map_cons, gfold, hg]
            rw [← hv]; exact ih
          · simp only [hnX, ↓reduceIte]
            rw [← hother X (Ne.symm hnX)]; exact ih
      · have hrn' : repeated.contains n = false := by simpa using hrn
        rw [nameStep_plain_view obs repeated family bound n a hrn'] at h
        have ih := flatBind_per_name obs repeated family rest _ env h X hX
        have hnX : n ≠ X := by intro he; subst he; rw [hrn'] at hX; cases hX
        rw [occ_cons]
        simp only [hnX, ↓reduceIte]
        rw [← view_withPlain_other obs bound n X a (Ne.symm hnX)]; exact ih

/-- COMPLETENESS OF THE PROJECTION: when every repeated name's own fold succeeds, the flat
    level binds. -/
theorem flatBind_complete (obs : Nat → CountedResult × Option Algorithm) (repeated : List Ident)
    (family : Bool) :
    ∀ (pairs : List (Ident × Nat)) (bound : NeedBindState),
      (∀ X, repeated.contains X = true → ∃ g, gfold (view obs bound X) ((occ X pairs).map (contrib obs)) = .ok g) →
      ∃ env, flatBind obs repeated family bound pairs = .ok (some env)
  | [], bound, _ => ⟨bound, rfl⟩
  | (n, a) :: rest, bound, h => by
      have step : ∃ next, nameStep obs repeated family bound n a = .ok (some next) ∧
          ∀ X, repeated.contains X = true →
            ∃ g, gfold (view obs next X) ((occ X rest).map (contrib obs)) = .ok g := by
        by_cases hrn : repeated.contains n = true
        · obtain ⟨hok, -⟩ := nameStep_view obs repeated family bound n a hrn
          obtain ⟨g, hgn⟩ := h n hrn
          rw [occ_cons] at hgn
          simp only [↓reduceIte, List.map_cons, gfold] at hgn
          cases hg : gstep (view obs bound n) (contrib obs a) with
          | error c => rw [hg] at hgn; cases hgn
          | ok g' =>
            rw [hg] at hgn
            obtain ⟨next, hns, hv, hother⟩ := hok g' hg
            refine ⟨next, hns, ?_⟩
            intro X hX
            by_cases hnX : n = X
            · subst hnX; rw [hv]; exact ⟨g, hgn⟩
            · rw [hother X (Ne.symm hnX)]
              obtain ⟨gx, hgx⟩ := h X hX
              rw [occ_cons] at hgx
              simp only [hnX, ↓reduceIte] at hgx
              exact ⟨gx, hgx⟩
        · have hrn' : repeated.contains n = false := by simpa using hrn
          refine ⟨bound.withPlain n a, nameStep_plain_view obs repeated family bound n a hrn', ?_⟩
          intro X hX
          have hnX : n ≠ X := by intro he; subst he; rw [hrn'] at hX; cases hX
          rw [view_withPlain_other obs bound n X a (Ne.symm hnX)]
          obtain ⟨gx, hgx⟩ := h X hX
          rw [occ_cons] at hgx
          simp only [hnX, ↓reduceIte] at hgx
          exact ⟨gx, hgx⟩
      obtain ⟨next, hns, hrest⟩ := step
      obtain ⟨env, henv⟩ := flatBind_complete obs repeated family rest next hrest
      exact ⟨env, by simp [flatBind, hns, henv]⟩

/-! ### The production head -/

theorem flat_head_accepts (names : List Ident) :
    needAcceptsCardinality (names.map (fun n => NeedPattern.bind n)) names.length = true := by
  have hf : (names.map (fun n => NeedPattern.bind n)).filter NeedPattern.isCollecting = [] := by
    induction names with
    | nil => rfl
    | cons n ns ih => simp [NeedPattern.isCollecting, ih]
  simp [needAcceptsCardinality, needMinimumSuppliedSlots, hf]

theorem flat_head_sources (names : List Ident) (cells : List Nat) (hlen : cells.length = names.length) :
    needLevelSources (names.map (fun n => NeedPattern.bind n)) cells = cells.map NeedSource.cell := by
  apply need_level_sources_without_collector
  · induction names with
    | nil => rfl
    | cons n ns ih => simp [List.findIdx?_cons, NeedPattern.isCollecting]
  · simpa using hlen

theorem flat_head_shape (names : List Ident) (cells : List Nat) (hlen : cells.length = names.length) :
    names.map (fun n => NeedPattern.bind n) = namePatterns (names.zip cells) ∧
      cells.map NeedSource.cell = cellSources (names.zip cells) := by
  induction names generalizing cells with
  | nil => cases cells with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => simp at hlen
  | cons n ns ih => cases cells with
    | nil => simp at hlen
    | cons c cs =>
      obtain ⟨h1, h2⟩ := ih cs (by simpa using hlen)
      exact ⟨by simp [namePatterns] at h1 ⊢; exact h1, by simp [cellSources] at h2 ⊢; exact h2⟩

/-- THE PRODUCTION BRIDGE (§6 statement 13): the generic core's `bindPatterns` (by definition the
    production `bindNeedPatterns` at `NeedChannels.capabilities`) over a flat head of name
    patterns and its stable supplied cells returns exactly `flatBind` over the written
    (name, cell) pairs, projected to its representatives. -/
theorem production_flat_head_is_flatBind (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (names : List Ident) (cells : List Nat)
    (hk : Stable k Inv obs cells) (hlen : cells.length = names.length) (family : Bool)
    (s : EvalState) (hs : Inv s) :
    ∃ t, Inv t ∧ runEval (NeedBinder.bindPatterns k (names.map (fun n => NeedPattern.bind n)) cells family) s
      = ((flatBind obs (needRepeatedNames (names.map (fun n => NeedPattern.bind n))) family {}
          (names.zip cells)).map (Option.map NeedBindState.bound), t) := by
  obtain ⟨hps, hsrc⟩ := flat_head_shape names cells hlen
  have hacc := flat_head_accepts names
  rw [← hlen] at hacc
  obtain ⟨t, it, ht⟩ := flat_level_is_flatBind k Inv obs cells hk
    (needRepeatedNames (names.map (fun n => NeedPattern.bind n))) family (names.zip cells) {} s
    (fun p hp => (List.of_mem_zip hp).2) (stateIn_empty cells) hs
  refine ⟨t, it, ?_⟩
  simp only [NeedBinder.bindPatterns, NeedBinder.bindLevel, NeedBinder.cardinalityGate, hacc,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, flat_head_sources names cells hlen, hsrc, runEval_bind]
  conv => enter [1, 1, 1, 2]; rw [hps]
  rw [ht]
  cases flatBind obs (needRepeatedNames (names.map (fun n => NeedPattern.bind n))) family {} (names.zip cells) <;>
    rfl

/-- THE PRODUCTION BINDING OF A FLAT HEAD IS EACH NAME'S `gfold`: when the production binding
    succeeds, each repeated name is bound to the representative `gfold` keeps over that name's own
    supplied contributions in written order — so results 1–4 describe the production binding. -/
theorem production_flat_binding_is_gfold (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (names : List Ident) (cells : List Nat)
    (hk : Stable k Inv obs cells) (hlen : cells.length = names.length) (family : Bool)
    (s t : EvalState) (hs : Inv s) (env : NeedEnv)
    (hrun : runEval (NeedBinder.bindPatterns k (names.map (fun n => NeedPattern.bind n)) cells family) s
      = (.ok (some env), t))
    (X : Ident) (hX : (needRepeatedNames (names.map (fun n => NeedPattern.bind n))).contains X = true) :
    ∃ g, gfold {} ((occ X (names.zip cells)).map (contrib obs)) = .ok g ∧
      (lookupAssoc X env).map (contrib obs) = g.rep := by
  obtain ⟨t', -, h⟩ := production_flat_head_is_flatBind k Inv obs names cells hk hlen family s hs
  rw [hrun] at h
  have hfb := congrArg Prod.fst h
  simp only at hfb
  cases hf : flatBind obs (needRepeatedNames (names.map (fun n => NeedPattern.bind n))) family {} (names.zip cells) with
  | error e => rw [hf] at hfb; cases hfb
  | ok o =>
    cases o with
    | none => rw [hf] at hfb; cases hfb
    | some st =>
      rw [hf] at hfb
      simp only [Except.map, Option.map_some, Except.ok.injEq, Option.some.injEq] at hfb
      have hp := flatBind_per_name obs _ family (names.zip cells) {} st hf X hX
      rw [view_empty] at hp
      refine ⟨view obs st X, hp, ?_⟩
      have henv : env = st.bound := by simpa [Except.map] using hfb
      subst henv
      rfl

/-- SATISFIABILITY, PRODUCTION: the production binding of a flat head with stable cells succeeds
    exactly when every repeated name's own fold succeeds. -/
theorem production_flat_binding_succeeds_iff (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (names : List Ident) (cells : List Nat)
    (hk : Stable k Inv obs cells) (hlen : cells.length = names.length) (family : Bool)
    (s : EvalState) (hs : Inv s) :
    (∃ env t, runEval (NeedBinder.bindPatterns k (names.map (fun n => NeedPattern.bind n)) cells family) s
      = (.ok (some env), t)) ↔
    ∀ X, (needRepeatedNames (names.map (fun n => NeedPattern.bind n))).contains X = true →
      ∃ g, gfold {} ((occ X (names.zip cells)).map (contrib obs)) = .ok g := by
  obtain ⟨t', -, h⟩ := production_flat_head_is_flatBind k Inv obs names cells hk hlen family s hs
  constructor
  · rintro ⟨env, t, hrun⟩ X hX
    obtain ⟨g, hg, -⟩ := production_flat_binding_is_gfold k Inv obs names cells hk hlen family s t hs env hrun X hX
    exact ⟨g, hg⟩
  · intro hall
    obtain ⟨env, henv⟩ := flatBind_complete obs (needRepeatedNames (names.map (fun n => NeedPattern.bind n)))
      family (names.zip cells) {} (by
        intro X hX
        obtain ⟨g, hg⟩ := hall X hX
        exact ⟨g, by rw [view_empty]; exact hg⟩)
    exact ⟨env.bound, t', by rw [h, henv]; rfl⟩

/-- THE PRODUCTION BINDING AGREES WITH THE DECLARATIVE PREDICATE: on stable cells, the production
    binding of a flat head succeeds exactly when every repeated name's contributions are a
    `GroupCompatible` group, on the identity domain. -/
theorem production_flat_binding_succeeds_iff_compatible (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (names : List Ident) (cells : List Nat)
    (hk : Stable k Inv obs cells) (hlen : cells.length = names.length) (family : Bool)
    (s : EvalState) (hs : Inv s)
    (hT : ∀ X, CallableTransOn ((occ X (names.zip cells)).map (contrib obs))) :
    (∃ env t, runEval (NeedBinder.bindPatterns k (names.map (fun n => NeedPattern.bind n)) cells family) s
      = (.ok (some env), t)) ↔
    ∀ X, (needRepeatedNames (names.map (fun n => NeedPattern.bind n))).contains X = true →
      GroupCompatible ((occ X (names.zip cells)).map (contrib obs)) := by
  rw [production_flat_binding_succeeds_iff k Inv obs names cells hk hlen family s hs]
  exact forall_congr' fun X => imp_congr_right fun _ => gfold_ok_iff_compatible _ (hT X)

/-! ### A production instance of the VALUE half of stability -/

/-- Cells whose VALUE is already COMPLETED with the fixed observation. -/
def CompletedWith (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat) (s : EvalState) : Prop :=
  ∀ a ∈ cells, ∃ cell, s.needs[a]? = some cell ∧ cell.state = .completed (.ok (obs a).1)

/-- The total public VALUE channel `demandNeed` is stable on completed cells: it returns the
    memoized counted value and leaves the state unchanged (`NeedControl.completed_reuse`). The
    CALLABLE half is stable on completed and Ready cells for the binder channels the evaluator
    passes (`NeedChannels.shell`; `NestedRepeatedNames.shell_model_caps`). -/
theorem demand_need_stable_on_completed (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat)
    (a : Nat) (ha : a ∈ cells) (s : EvalState) (hs : CompletedWith obs cells s) :
    ∃ t, runEval (demandNeed a) s = (.ok (obs a).1, t) ∧ CompletedWith obs cells t := by
  obtain ⟨cell, hc, hst⟩ := hs a ha
  exact ⟨s, KatLang.NeedControl.Production.completed_reuse a s cell (.ok (obs a).1) hc hst, hs⟩

end KatLang.RepeatedNameLaws
