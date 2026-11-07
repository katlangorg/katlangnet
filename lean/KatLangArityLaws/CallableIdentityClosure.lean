import KatLangArityLaws.CallableIdentityProvenance

open KatLang KatLang.RepeatedNameLaws KatLang.CallableIdentityDomain
open KatLang.CallableIdentityProvenance

/-!
# FG-I1: what closes the production identity obligation (November 2026)

`CallableIdentityProvenance` derives `CallableTransOn` from `ModelFollows`. This module answers the
question that premise leaves open: what must a group-local invariant, weaker than `HeapFollows`,
establish on a list containing a fork? The theorem below shows that transitivity there entails a
printer fact. It is not a proof that every possible group-local approach is impossible.

THE COMPARATOR, OPENED. `sameScopeVia fallback` is `sameDeclaringScope` with its one non-structural
arm as a parameter; `sameScopeVia_printed` proves production is the instance `printed`.

RESULTS.
1. FORK. A triple of levels that agrees on identity and binders down to a pair `u, w` of identified
   levels with an anonymous `v` between them (`forkOf?`) makes two comparisons depend on the
   fallback alone and one depend on `u, w` alone (`fork_comparisons`).
2. `use_site_is_a_printer_fact`: on such a triple of callables, `CallableTransOn` of ANY list holding
   them IMPLIES that `reprStr` separates the printed declarations. So every proof of the use-site
   obligation on a list containing an admitted fork entails a fact about the core printer's output.
   `success_aligned_fork_iff`: under its explicit misalignment premise, `SuccessAligned` on such a
   pair IS the inequality. This does not prove full `ReprSeparatesPresence` necessary for transitivity.
3. `some_fallback_is_intransitive`: under its explicit outer-pair refusal premise, the fallback
   that accepts every mixed pair makes the triple intransitive. Fork structure alone does not
   establish transitivity independently of the fallback's actual values.
   `CallableIdentityProvenanceGuards` § An equal-depth fork runs the real program that reaches the
   shape, through host input the differential corpus also runs in C# (HP-14t).
4. THE CANDIDATE, a definition of this module and of no production path. `sameScopeCandidate`
   refuses a mixed pair instead of asking the printer, and keeps the printed comparison of two
   anonymous levels. Unconditionally: `candidate_identity_trans` (no `ModelFollows`, no printer
   premise), `candidate_scope_presence` (`SitePresence` becomes a theorem).
5. THE COST OF ADOPTING IT, exactly: `candidate_eq_production_iff`, the candidate is production on
   every pair of levels IFF `ReprSeparatesPresence`. This is sufficient for preserving observable
   behaviour, not an iff about program observations: that needs a separate reachability and
   observation argument. Replacing production with the candidate is an OWNER decision;
   nothing in this module does it.

`sameDeclaringScope` and every production definition are untouched. FG-I1 stays conditional.
-/

namespace KatLang.CallableIdentityClosure

/-! ## The comparator with its fallback as a parameter -/

/-- `sameDeclaringScope` over any fallback for the pairs that are not both identified. -/
def sameScopeVia (fallback : ScopeCtx → ScopeCtx → Bool) (left right : ScopeCtx) : Bool :=
  match left, right with
  | .mk leftParent leftParams _ _ _ _ _ (some a), .mk rightParent rightParams _ _ _ _ _ (some b) =>
      a == b && leftParams == rightParams &&
      match leftParent, rightParent with
      | none, none => true
      | some p, some q => sameScopeVia fallback p q
      | _, _ => false
  | _, _ => fallback left right

/-- Production's fallback: the two printed declarations. -/
def printed (left right : ScopeCtx) : Bool :=
  reprStr left.declaration == reprStr right.declaration

/-- Production is the instance `printed`. -/
theorem sameScopeVia_printed : ∀ left right : ScopeCtx,
    sameScopeVia printed left right = sameDeclaringScope left right
  | .mk lp _ _ _ _ _ _ (some _), .mk rp _ _ _ _ _ _ (some _) => by
      rcases lp with _ | p <;> rcases rp with _ | q <;>
        simp only [sameScopeVia, sameDeclaringScope, sameScopeVia_printed]
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ (some _) => by
      simp only [sameScopeVia, sameDeclaringScope, printed]
  | .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ none => by
      simp only [sameScopeVia, sameDeclaringScope, printed]
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none => by
      simp only [sameScopeVia, sameDeclaringScope, printed]

/-! ## Forks -/

/-- Where three chains that agree on identity and binders first meet an identified, anonymous,
    identified triple of levels. Printer-free and executable. -/
def forkOf? : ScopeCtx → ScopeCtx → ScopeCtx → Option (ScopeCtx × ScopeCtx × ScopeCtx)
  | .mk (some p) ps _ _ _ _ _ (some a), .mk (some q) qs _ _ _ _ _ (some b),
    .mk (some r) rs _ _ _ _ _ (some c) =>
      if a == b && b == c && ps == qs && qs == rs then forkOf? p q r else none
  | x@(.mk _ _ _ _ _ _ _ (some _)), y@(.mk _ _ _ _ _ _ _ none), z@(.mk _ _ _ _ _ _ _ (some _)) =>
      some (x, y, z)
  | _, _, _ => none

/-- RESULT 1: along a fork the outer comparisons are the fallback at the fork, and the comparison
    of the two identified chains is the comparison at the fork. For every fallback. -/
theorem fork_comparisons (f : ScopeCtx → ScopeCtx → Bool) : ∀ (x y z u v w : ScopeCtx),
    forkOf? x y z = some (u, v, w) →
      sameScopeVia f x y = f u v ∧ sameScopeVia f y z = f v w ∧
        sameScopeVia f x z = sameScopeVia f u w
  | .mk (some p) ps _ _ _ _ _ (some a), .mk (some q) qs _ _ _ _ _ (some b),
    .mk (some r) rs _ _ _ _ _ (some c), u, v, w, h => by
      simp only [forkOf?] at h
      split at h
      · rename_i hif
        simp only [Bool.and_eq_true, beq_iff_eq] at hif
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hif
        obtain ⟨h1, h2, h3⟩ := fork_comparisons f p q r u v w h
        simp [sameScopeVia, h1, h2, h3]
      · cases h
  | .mk (some _) _ _ _ _ _ _ (some _), .mk (some _) _ _ _ _ _ _ none,
    .mk (some _) _ _ _ _ _ _ (some _), u, v, w, h => by
      simp only [forkOf?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [sameScopeVia]
  | .mk none _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ (some _), u, v, w, h => by
      simp only [forkOf?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [sameScopeVia]
  | .mk (some _) _ _ _ _ _ _ (some _), .mk none _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ (some _), u, v, w, h => by
      simp only [forkOf?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [sameScopeVia]
  | .mk (some _) _ _ _ _ _ _ (some _), .mk (some _) _ _ _ _ _ _ none, .mk none _ _ _ _ _ _ (some _), u, v, w, h => by
      simp only [forkOf?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [sameScopeVia]
  | .mk _ _ _ _ _ _ _ none, _, _, _, _, _, h => by simp [forkOf?] at h
  | .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ none, _, _, _, h => by
      simp [forkOf?] at h
  | .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none, _, _, _, h => by
      simp [forkOf?] at h
  | .mk none _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ (some _), _, _, _, h => by
      simp [forkOf?] at h
  | .mk (some _) _ _ _ _ _ _ (some _), .mk none _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ (some _), _, _, _, h => by
      simp [forkOf?] at h
  | .mk (some _) _ _ _ _ _ _ (some _), .mk (some _) _ _ _ _ _ _ (some _), .mk none _ _ _ _ _ _ (some _), _, _, _, h => by
      simp [forkOf?] at h

/-- Three non-builtin callables of one declaration, with pairwise compatible parents in both
    directions, forked at `u, v, w`, where `u` and `w` are different declaring scopes. Printer-free:
    an executable reading of it is checked on real runs. -/
structure CallableFork (a b c : Algorithm) (x y z u v w : ScopeCtx) : Prop where
  builtin_a : asBuiltin? a = none
  builtin_b : asBuiltin? b = none
  builtin_c : asBuiltin? c = none
  declaration_ab : PropertyIdentity.callableDeclaration a.declarationId =
    PropertyIdentity.callableDeclaration b.declarationId
  declaration_bc : PropertyIdentity.callableDeclaration b.declarationId =
    PropertyIdentity.callableDeclaration c.declarationId
  parent_a : a.parent = some x
  parent_b : b.parent = some y
  parent_c : c.parent = some z
  compatible_xy : compatibleActivations (some x) (some y) = true
  compatible_yx : compatibleActivations (some y) (some x) = true
  compatible_yz : compatibleActivations (some y) (some z) = true
  compatible_zy : compatibleActivations (some z) (some y) = true
  fork : forkOf? x y z = some (u, v, w)
  apart : sameDeclaringScope u w = false

variable {a b c : Algorithm} {x y z u v w : ScopeCtx}

/-- On a fork the identity verdicts of the two outer pairs are the printed comparisons. -/
theorem fork_identity_ab (h : CallableFork a b c x y z u v w) :
    sameRepeatedCallableIdentity a b = printed u v := by
  have hs : sameDeclaringScope x y = printed u v := by
    rw [← sameScopeVia_printed]; exact (fork_comparisons printed x y z u v w h.fork).1
  rw [same_identity_eq, h.builtin_a, h.builtin_b]
  simp only [identityCore, h.parent_a, h.parent_b, h.declaration_ab, h.compatible_xy,
    h.compatible_yx, sameParent, hs, beq_self_eq_true, Bool.true_and, Bool.and_true]

theorem fork_identity_bc (h : CallableFork a b c x y z u v w) :
    sameRepeatedCallableIdentity b c = printed v w := by
  have hs : sameDeclaringScope y z = printed v w := by
    rw [← sameScopeVia_printed]; exact (fork_comparisons printed x y z u v w h.fork).2.1
  rw [same_identity_eq, h.builtin_b, h.builtin_c]
  simp only [identityCore, h.parent_b, h.parent_c, h.declaration_bc, h.compatible_yz,
    h.compatible_zy, sameParent, hs, beq_self_eq_true, Bool.true_and, Bool.and_true]

/-- The two identified chains of a fork are different identities, whatever the printer says. -/
theorem fork_identity_ac (h : CallableFork a b c x y z u v w) :
    sameRepeatedCallableIdentity a c = false := by
  have hs : sameDeclaringScope x z = false := by
    rw [← sameScopeVia_printed, (fork_comparisons printed x y z u v w h.fork).2.2,
      sameScopeVia_printed]
    exact h.apart
  rw [same_identity_eq, h.builtin_a, h.builtin_c]
  simp only [identityCore, h.parent_a, h.parent_c, sameParent, hs, Bool.and_false, Bool.false_and]

/-- RESULT 2: on a fork, the use-site obligation IS a fact about printed text. Whatever list holds
    the three callables, `CallableTransOn` of that list refutes the two printed equalities. Any
    proof of the obligation, by any invariant, therefore proves this statement about `reprStr`. -/
theorem use_site_is_a_printer_fact (h : CallableFork a b c x y z u v w) (l : List Contribution)
    (ha : Present l a) (hb : Present l b) (hc : Present l c) (ht : CallableTransOn l) :
    ¬ (reprStr u.declaration = reprStr v.declaration ∧
        reprStr v.declaration = reprStr w.declaration) := by
  rintro ⟨huv, hvw⟩
  have hab : sameRepeatedCallableIdentity a b = true := by
    rw [fork_identity_ab h]; simp [printed, huv]
  have hbc : sameRepeatedCallableIdentity b c = true := by
    rw [fork_identity_bc h]; simp [printed, hvw]
  have hac := ht a b c ha hb hc hab hbc
  rw [fork_identity_ac h] at hac
  cases hac

/-- `SuccessAligned`, the weakest pairwise condition of the transitivity proof, is on a fork
    exactly the printed inequality. -/
theorem success_aligned_fork_iff (h : CallableFork a b c x y z u v w)
    (hmis : ¬ ParentAligned (some x) (some y)) :
    SuccessAligned a b ↔ reprStr u.declaration ≠ reprStr v.declaration := by
  unfold SuccessAligned
  rw [fork_identity_ab h, h.parent_a, h.parent_b]
  constructor
  · intro hs heq
    exact hmis (hs (by simp [printed, heq]))
  · intro hne hs
    simp [printed, hne] at hs

/-- RESULT 3: identity over any fallback, production's definition otherwise. -/
def sameIdentityVia (f : ScopeCtx → ScopeCtx → Bool) (l r : Algorithm) : Bool :=
  match asBuiltin? l, asBuiltin? r with
  | some p, some q => p == q
  | none, none =>
      PropertyIdentity.callableDeclaration l.declarationId ==
          PropertyIdentity.callableDeclaration r.declarationId &&
        (match l.parent, r.parent with
         | none, none => true
         | some p, some q => sameScopeVia f p q
         | _, _ => false) &&
        compatibleActivations l.parent r.parent && compatibleActivations r.parent l.parent
  | _, _ => false

/-- Production is the instance `printed`. -/
theorem sameIdentityVia_printed (l r : Algorithm) :
    sameIdentityVia printed l r = sameRepeatedCallableIdentity l r := by
  rw [same_identity_eq]
  unfold sameIdentityVia identityCore sameParent
  cases asBuiltin? l <;> cases asBuiltin? r <;> try rfl
  cases l.parent <;> cases r.parent <;> simp only [sameScopeVia_printed]

/-- The fallback that accepts every pair. -/
def acceptAll (_ _ : ScopeCtx) : Bool := true

/-- RESULT 3: for one fallback the very same fork is INTRANSITIVE, unless its two identified
    chains already agree through their fork. So nothing about the comparator's structure, the
    chains, the depths or the activations implies transitivity here: the values of the fallback
    are the whole question. -/
theorem some_fallback_is_intransitive (h : CallableFork a b c x y z u v w)
    (happart : sameScopeVia acceptAll u w = false) :
    sameIdentityVia acceptAll a b = true ∧ sameIdentityVia acceptAll b c = true ∧
      sameIdentityVia acceptAll a c = false := by
  obtain ⟨h1, h2, h3⟩ := fork_comparisons acceptAll x y z u v w h.fork
  have hac : PropertyIdentity.callableDeclaration a.declarationId =
      PropertyIdentity.callableDeclaration c.declarationId := h.declaration_ab.trans h.declaration_bc
  refine ⟨?_, ?_, ?_⟩
  · simp only [sameIdentityVia, h.builtin_a, h.builtin_b, h.parent_a, h.parent_b, h.declaration_ab,
      h.compatible_xy, h.compatible_yx, h1, acceptAll, beq_self_eq_true, Bool.and_self]
  · simp only [sameIdentityVia, h.builtin_b, h.builtin_c, h.parent_b, h.parent_c, h.declaration_bc,
      h.compatible_yz, h.compatible_zy, h2, acceptAll, beq_self_eq_true, Bool.and_self]
  · simp only [sameIdentityVia, h.builtin_a, h.builtin_c, h.parent_a, h.parent_c, h3, happart,
      Bool.and_false, Bool.false_and]

/-! ## The candidate (no production path uses it) -/

/-- A mixed pair is refused; two anonymous levels keep the printed comparison. -/
def anonymousOnly (left right : ScopeCtx) : Bool :=
  left.declarationId.isNone && right.declarationId.isNone && printed left right

def sameScopeCandidate : ScopeCtx → ScopeCtx → Bool := sameScopeVia anonymousOnly

/-- RESULT 4: a successful candidate comparison is presence-aligned, with no premise. -/
theorem candidate_aligned : ∀ left right : ScopeCtx,
    sameScopeCandidate left right = true → Aligned left right
  | .mk lp _ _ _ _ _ _ (some _), .mk rp _ _ _ _ _ _ (some _), h => by
      rcases lp with _ | p <;> rcases rp with _ | q <;> simp only [Aligned]
      simp only [sameScopeCandidate, sameScopeVia, Bool.and_eq_true] at h
      exact candidate_aligned p q h.2
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none, _ => by simp only [Aligned]
  | .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ none, h => by
      simp [sameScopeCandidate, sameScopeVia, anonymousOnly, ScopeCtx.declarationId] at h
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ (some _), h => by
      simp [sameScopeCandidate, sameScopeVia, anonymousOnly, ScopeCtx.declarationId] at h

/-- RESULT 4: `SitePresence` is a theorem of the candidate. -/
theorem candidate_scope_presence (left right : ScopeCtx) (h : sameScopeCandidate left right = true) :
    right.declarationId.isSome = left.declarationId.isSome := by
  have := candidate_aligned left right h
  cases left with
  | mk _ _ _ _ _ _ _ i =>
    cases right with
    | mk _ _ _ _ _ _ _ j =>
      cases i <;> cases j <;> simp_all [Aligned, ScopeCtx.declarationId]

/-- RESULT 4: the candidate is transitive on levels, with no premise. -/
theorem candidate_trans : ∀ x y z : ScopeCtx,
    sameScopeCandidate x y = true → sameScopeCandidate y z = true → sameScopeCandidate x z = true
  | .mk xp xps _ _ _ _ _ (some a), .mk yp yps _ _ _ _ _ (some b), .mk zp zps _ _ _ _ _ (some c),
      h1, h2 => by
      rcases xp with _ | p <;> rcases yp with _ | q <;> rcases zp with _ | r <;>
        simp only [sameScopeCandidate, sameScopeVia, Bool.and_eq_true, beq_iff_eq,
          Bool.false_eq_true, and_false, and_true] at h1 h2 ⊢
      all_goals first
        | exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
        | exact ⟨⟨h1.1.1.trans h2.1.1, h1.1.2.trans h2.1.2⟩, candidate_trans p q r h1.2 h2.2⟩
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none, h1, h2 => by
      simp only [sameScopeCandidate, sameScopeVia, anonymousOnly, printed, Bool.and_eq_true,
        beq_iff_eq] at h1 h2 ⊢
      exact ⟨h1.1, h2.2.symm ▸ h1.2 ▸ rfl⟩
  | .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ none, _, h1, _ => by
      simp [sameScopeCandidate, sameScopeVia, anonymousOnly, ScopeCtx.declarationId] at h1
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ (some _), _, h1, _ => by
      simp [sameScopeCandidate, sameScopeVia, anonymousOnly, ScopeCtx.declarationId] at h1
  | .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ none, _, h2 => by
      simp [sameScopeCandidate, sameScopeVia, anonymousOnly, ScopeCtx.declarationId] at h2
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ (some _), _, h2 => by
      simp [sameScopeCandidate, sameScopeVia, anonymousOnly, ScopeCtx.declarationId] at h2

/-- Identity over the candidate. -/
def candidateIdentity : Algorithm → Algorithm → Bool := sameIdentityVia anonymousOnly

/-- RESULT 4: TRANSITIVITY over the candidate, for every three algorithms, with no provenance
    premise and no printer premise. -/
theorem candidate_identity_trans (a b c : Algorithm)
    (hab : candidateIdentity a b = true) (hbc : candidateIdentity b c = true) :
    candidateIdentity a c = true := by
  simp only [candidateIdentity, sameIdentityVia] at hab hbc ⊢
  cases ha : asBuiltin? a <;> cases hb : asBuiltin? b <;> cases hc : asBuiltin? c <;>
    rw [ha, hb] at hab <;> rw [hb, hc] at hbc <;>
    simp only [Bool.false_eq_true, beq_iff_eq, Bool.and_eq_true] at hab hbc ⊢
  · obtain ⟨⟨⟨d1, s1⟩, c1⟩, c1'⟩ := hab
    obtain ⟨⟨⟨d2, s2⟩, c2⟩, c2'⟩ := hbc
    have e1 := (compatible_activations_both_iff a.parent b.parent).mp ⟨c1, c1'⟩
    have e2 := (compatible_activations_both_iff b.parent c.parent).mp ⟨c2, c2'⟩
    have e := (compatible_activations_both_iff a.parent c.parent).mpr (e1.trans e2)
    refine ⟨⟨⟨d1.trans d2, ?_⟩, e.1⟩, e.2⟩
    cases hp : a.parent <;> cases hq : b.parent <;> cases hr : c.parent <;>
      simp only [hp, hq, hr, Bool.false_eq_true] at s1 s2 ⊢
    exact candidate_trans _ _ _ s1 s2
  · exact hab.trans hbc

/-! ## What adopting the candidate costs -/

theorem anonymousOnly_eq_printed (hsep : ReprSeparatesPresence) :
    ∀ left right : ScopeCtx, (left.declarationId.isSome && right.declarationId.isSome) = false →
      anonymousOnly left right = printed left right
  | .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ (some _), h => by
      simp [ScopeCtx.declarationId] at h
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none, _ => by
      simp [anonymousOnly, ScopeCtx.declarationId]
  | .mk xp xps xo xpr xout xb xa (some i), .mk yp yps yo ypr yout yb ya none, _ => by
      have hne := hsep (.mk xp xps xo xpr xout xb xa (some i)) (.mk yp yps yo ypr yout yb ya none)
        rfl rfl
      simp [anonymousOnly, ScopeCtx.declarationId, printed, hne]
  | .mk xp xps xo xpr xout xb xa none, .mk yp yps yo ypr yout yb ya (some i), _ => by
      have hne := hsep (.mk yp yps yo ypr yout yb ya (some i)) (.mk xp xps xo xpr xout xb xa none)
        rfl rfl
      have hne' : reprStr (ScopeCtx.mk xp xps xo xpr xout xb xa none).declaration ≠
          reprStr (ScopeCtx.mk yp yps yo ypr yout yb ya (some i)).declaration :=
        fun e => hne e.symm
      simp [anonymousOnly, ScopeCtx.declarationId, printed, hne']

theorem candidate_eq_production_of_separating (hsep : ReprSeparatesPresence) :
    ∀ left right : ScopeCtx, sameScopeCandidate left right = sameDeclaringScope left right
  | .mk lp _ _ _ _ _ _ (some _), .mk rp _ _ _ _ _ _ (some _) => by
      rcases lp with _ | p <;> rcases rp with _ | q <;>
        simp only [sameScopeCandidate, sameScopeVia, sameDeclaringScope]
      have := candidate_eq_production_of_separating hsep p q
      simp only [sameScopeCandidate] at this
      rw [this]
  | .mk xp xps xo xpr xout xb xa none, .mk yp yps yo ypr yout yb ya (some i) => by
      have := anonymousOnly_eq_printed hsep (.mk xp xps xo xpr xout xb xa none)
        (.mk yp yps yo ypr yout yb ya (some i)) (by simp [ScopeCtx.declarationId])
      simp only [sameScopeCandidate, sameScopeVia, sameDeclaringScope, this, printed]
  | .mk xp xps xo xpr xout xb xa (some i), .mk yp yps yo ypr yout yb ya none => by
      have := anonymousOnly_eq_printed hsep (.mk xp xps xo xpr xout xb xa (some i))
        (.mk yp yps yo ypr yout yb ya none) (by simp [ScopeCtx.declarationId])
      simp only [sameScopeCandidate, sameScopeVia, sameDeclaringScope, this, printed]
  | .mk xp xps xo xpr xout xb xa none, .mk yp yps yo ypr yout yb ya none => by
      have := anonymousOnly_eq_printed hsep (.mk xp xps xo xpr xout xb xa none)
        (.mk yp yps yo ypr yout yb ya none) (by simp [ScopeCtx.declarationId])
      simp only [sameScopeCandidate, sameScopeVia, sameDeclaringScope, this, printed]

/-- RESULT 5: the candidate agrees with production on every pair of levels EXACTLY when the printer
    separates presence. A mixed pair with equal printed text is the only possible difference. -/
theorem candidate_eq_production_iff :
    (∀ left right : ScopeCtx, sameScopeCandidate left right = sameDeclaringScope left right) ↔
      ReprSeparatesPresence := by
  refine ⟨?_, candidate_eq_production_of_separating⟩
  intro h l r hl hr heq
  cases l with
  | mk lp lps lo lpr lout lb la li =>
    cases r with
    | mk rp rps ro rpr rout rb ra ri =>
      cases li with
      | none => simp [ScopeCtx.declarationId] at hl
      | some i =>
        cases ri with
        | some _ => simp [ScopeCtx.declarationId] at hr
        | none =>
          have hc := h (.mk lp lps lo lpr lout lb la (some i)) (.mk rp rps ro rpr rout rb ra none)
          simp only [sameScopeCandidate, sameScopeVia, sameDeclaringScope, anonymousOnly,
            ScopeCtx.declarationId, Option.isNone_some, Bool.false_and] at hc
          rw [heq] at hc
          simp at hc

/-- Identity agreement under the same residual. -/
theorem candidate_identity_eq_production (hsep : ReprSeparatesPresence) (a b : Algorithm) :
    candidateIdentity a b = sameRepeatedCallableIdentity a b := by
  rw [← sameIdentityVia_printed]
  unfold candidateIdentity sameIdentityVia
  cases asBuiltin? a <;> cases asBuiltin? b <;> try rfl
  cases a.parent <;> cases b.parent <;> try rfl
  have hc := candidate_eq_production_of_separating hsep
  simp only [sameScopeCandidate] at hc
  simp only [hc, sameScopeVia_printed]

end KatLang.CallableIdentityClosure
