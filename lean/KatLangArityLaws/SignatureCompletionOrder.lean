import KatLangArityLaws.SignatureCompletionEvaluation

open KatLang

/-!
# SC-1: bounds decide nothing, and the acyclic case is plain dependency order

Over the reference kernel only. `select_verdict_stable`: a verdict of `select` is the same under every larger bound, so
only `.exhausted` depends on the bound. `acyclic_agrees`: an acyclic read graph evaluates to the composition law applied
in any topological order, with no gate and no rounds.
-/

namespace KatLang.SignatureCompletion

private theorem any_congr_on {α} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem all_congr_on {α} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-! ## Larger bounds -/

/-- A reading under a larger bound refines one under a smaller: an exhausted cell may become a verdict; nothing else
    changes, and pending stays pending. -/
def Refines (c c' : Nat → Cell) : Prop := ∀ k, (c k = .exhausted ∧ c' k ≠ .pending) ∨ c k = c' k

section Bound

variable (sys : System) (opened : Nat → Bool)

private theorem refines_pending {c c' : Nat → Cell} (h : Refines c c') (k : Nat) :
    (c k != .pending) = (c' k != .pending) := by
  rcases h k with ⟨he, hn⟩ | e
  · have hb : (c' k != .pending) = true := by simpa using hn
    rw [hb, he]
    rfl
  · rw [e]

theorem evalComponent_refines {c c' : Nat → Cell} (hr : Refines c c') (fuel more : Nat) (members : List Nat) (k : Nat) :
    (evalComponent sys opened fuel members c k = .exhausted
        ∧ evalComponent sys opened (fuel + more) members c' k ≠ .pending)
      ∨ evalComponent sys opened fuel members c k = evalComponent sys opened (fuel + more) members c' k := by
  by_cases hE : evalComponent sys opened fuel members c k = .exhausted
  · exact .inl ⟨hE, evalComponent_not_pending sys opened _ _ _ _⟩
  right
  have hex : (outsideReads sys opened members).any (fun t => c t == .exhausted) = false := by
    cases h : (outsideReads sys opened members).any (fun t => c t == .exhausted) with
    | false => rfl
    | true =>
      exfalso
      apply hE
      unfold evalComponent
      simp only
      rw [if_pos h]
  have heq : ∀ t ∈ outsideReads sys opened members, c t = c' t := by
    intro t ht
    rcases hr t with ⟨he, _⟩ | e
    · have := List.any_eq_false.1 hex t ht
      simp [he] at this
    · exact e
  have hlower : lowerReads sys opened members c' = lowerReads sys opened members c := by
    funext t
    unfold lowerReads
    by_cases ht : t ∈ outsideReads sys opened members
    · simp [ht, heq t ht]
    · simp [ht]
  have h1 : (outsideReads sys opened members).any (fun t => c' t == .exhausted)
      = (outsideReads sys opened members).any (fun t => c t == .exhausted) :=
    any_congr_on fun t ht => by rw [heq t ht]
  have h2 : (outsideReads sys opened members).any (fun t => c' t == .meaningless)
      = (outsideReads sys opened members).any (fun t => c t == .meaningless) :=
    any_congr_on fun t ht => by rw [heq t ht]
  revert hE
  unfold evalComponent
  simp only
  rw [h1, h2, hlower]
  intro hE
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rename_i n1 n2 n3
        rw [if_neg n1, if_neg n2, if_neg n3] at hE
        generalize lowerReads sys opened members c = lower at hE ⊢
        cases hc : completeLoop (roundStep sys opened members lower) (sameState members) fuel
            (gateState sys opened members lower) (gateState sys opened members lower) 0 1 with
        | settled state =>
          rw [(completeLoop_verdict_stable _ _ fuel more _ _ 0 1).1 state hc]
        | nonSettling =>
          rw [(completeLoop_verdict_stable _ _ fuel more _ _ 0 1).2 hc]
        | exhausted =>
          rw [hc] at hE
          exact absurd rfl hE

theorem layer_refines (reach : Nat → List Nat) {c c' : Memo Cell} (hr : Refines c.get c'.get) (fuel more : Nat) :
    Refines (layer sys opened fuel reach c).get (layer sys opened (fuel + more) reach c').get := by
  intro k
  by_cases hk : k ∈ sys.keys
  · rw [layer_apply sys opened fuel reach c hk, layer_apply sys opened _ reach c' hk]
    rcases hr k with ⟨he, hn⟩ | e
    · left
      rw [he]
      cases hc : c'.get k with
      | pending => exact absurd hc hn
      | fact f => exact ⟨rfl, by simp⟩
      | meaningless => exact ⟨rfl, by simp⟩
      | exhausted => exact ⟨rfl, by simp⟩
    · rw [e]
      cases hc : c'.get k with
      | fact f => exact .inr rfl
      | meaningless => exact .inr rfl
      | exhausted => exact .inr rfl
      | pending =>
        simp only
        have hready : layerReady sys opened (componentOf sys reach k) c.get
            = layerReady sys opened (componentOf sys reach k) c'.get :=
          all_congr_on fun t _ => refines_pending hr t
        rw [hready]
        by_cases hrd : layerReady sys opened (componentOf sys reach k) c'.get = true
        · rw [if_pos hrd, if_pos hrd]
          exact evalComponent_refines sys opened hr fuel more _ k
        · rw [if_neg hrd, if_neg hrd]
          exact .inr rfl
  · right
    rw [show (layer sys opened fuel reach c).get k = .pending from tabulate_of_not_mem _ _ _ hk,
      show (layer sys opened (fuel + more) reach c').get k = .pending from tabulate_of_not_mem _ _ _ hk]

theorem layers_refines (reach : Nat → List Nat) (fuel more n : Nat) : ∀ {c c' : Memo Cell}, Refines c.get c'.get →
    Refines (layers sys opened fuel reach n c).get (layers sys opened (fuel + more) reach n c').get := by
  induction n with
  | zero => exact fun h => h
  | succ n ih => exact fun h => ih (layer_refines sys opened reach h fuel more)

theorem evalVector_refines (fuel more : Nat) :
    Refines (evalVector sys opened fuel).get (evalVector sys opened (fuel + more)).get :=
  layers_refines sys opened _ fuel more _ (c := ⟨fun _ => .pending⟩) (c' := ⟨fun _ => .pending⟩) fun _ => .inr rfl

/-- A reading with a verdict everywhere is the same reading under every larger bound. -/
theorem evalVector_stable (wf : sys.WellFormed) (fuel more : Nat)
    (h : noVerdict sys (evalVector sys opened fuel).get = false) :
    (evalVector sys opened (fuel + more)).get = (evalVector sys opened fuel).get := by
  funext k
  rcases evalVector_refines sys opened fuel more k with ⟨he, _⟩ | e
  · by_cases hk : k ∈ sys.keys
    · have := List.any_eq_false.1 h k hk
      simp [he] at this
    · have := (goodCells_evalVector sys opened fuel wf).outside k hk
      rw [he] at this
      cases this
  · exact e.symm

end Bound

section BoundSelect

variable (sys : System) (wf : sys.WellFormed) (fuel more : Nat)
include wf

private theorem readings_congr {linkSet : List Nat} {assigned : Nat → Bool}
    (h : ((subsetsOf (linkSet.filter assigned)).filter (!·.isEmpty)).any
      (fun support => noVerdict sys (evalVector sys (fun k => assigned k && !classOf support k) fuel).get) = false) :
    ∀ support ∈ (subsetsOf (linkSet.filter assigned)).filter (!·.isEmpty),
      (evalVector sys (fun k => assigned k && !classOf support k) (fuel + more)).get
        = (evalVector sys (fun k => assigned k && !classOf support k) fuel).get :=
  fun support hs => evalVector_stable sys _ wf fuel more (by simpa using List.any_eq_false.1 h support hs)

theorem groundednessOf_stable {linkSet : List Nat} {assigned : Nat → Bool}
    (h : groundednessOf sys fuel linkSet assigned ≠ .noVerdict) :
    groundednessOf sys (fuel + more) linkSet assigned = groundednessOf sys fuel linkSet assigned := by
  have hshape : ∀ bound, groundednessOf sys bound linkSet assigned =
      (let supports := (subsetsOf (linkSet.filter assigned)).filter (!·.isEmpty)
       if supports.any (fun support => noVerdict sys (evalVector sys (fun k => assigned k && !classOf support k) bound).get)
       then .noVerdict
       else
         let verdicts := supports.map fun support =>
           refutedWithout (evalVector sys (fun k => assigned k && !classOf support k) bound).get support
         if verdicts.contains (some false) then .ungrounded
         else if verdicts.contains none then .undetermined
         else .grounded) := by
    intro bound
    unfold groundednessOf
    simp only [List.any_map, List.map_map, Function.comp_def]
  rw [hshape] at h ⊢
  rw [hshape]
  simp only at h ⊢
  by_cases h0 : ((subsetsOf (linkSet.filter assigned)).filter (!·.isEmpty)).any
      (fun support => noVerdict sys (evalVector sys (fun k => assigned k && !classOf support k) fuel).get) = true
  · rw [if_pos h0] at h
    exact absurd rfl h
  have h0' := Bool.eq_false_iff.2 h0
  have hsame := readings_congr sys wf fuel more h0'
  have hany : ((subsetsOf (linkSet.filter assigned)).filter (!·.isEmpty)).any
      (fun support => noVerdict sys (evalVector sys (fun k => assigned k && !classOf support k) (fuel + more)).get)
      = ((subsetsOf (linkSet.filter assigned)).filter (!·.isEmpty)).any
        (fun support => noVerdict sys (evalVector sys (fun k => assigned k && !classOf support k) fuel).get) :=
    any_congr_on fun s hs => by rw [hsame s hs]
  have hmap : ((subsetsOf (linkSet.filter assigned)).filter (!·.isEmpty)).map (fun support =>
        refutedWithout (evalVector sys (fun k => assigned k && !classOf support k) (fuel + more)).get support)
      = ((subsetsOf (linkSet.filter assigned)).filter (!·.isEmpty)).map (fun support =>
        refutedWithout (evalVector sys (fun k => assigned k && !classOf support k) fuel).get support) :=
    List.map_congr_left fun s hs => by rw [hsame s hs]
  rw [hany, hmap]

theorem rowOf_stable {linkSet : List Nat} {assigned : Nat → Bool}
    (h : (rowOf sys fuel linkSet assigned).isExhausted = false) :
    rowOf sys (fuel + more) linkSet assigned = rowOf sys fuel linkSet assigned := by
  unfold rowOf at h ⊢
  simp only at h ⊢
  by_cases h1 : noVerdict sys (evalVector sys assigned fuel).get = true
  · rw [if_pos h1] at h; cases h
  have hsame := evalVector_stable sys assigned wf fuel more (Bool.eq_false_iff.2 h1)
  rw [hsame]
  rw [if_neg h1] at h ⊢
  split
  · rfl
  · rename_i h2
    rw [if_neg h2] at h
    split
    · rfl
    · rename_i h3
      rw [if_neg h3] at h
      have hg : groundednessOf sys fuel linkSet assigned ≠ .noVerdict := by
        intro e
        rw [e] at h
        cases h
      rw [groundednessOf_stable sys wf fuel more hg]

/-- ONLY `.exhausted` DEPENDS ON THE BOUND: a selected answer or a refusal is the same under every larger bound. So
    exhaustion is the absence of a verdict, never evidence for one. -/
theorem select_verdict_stable (h : (select sys fuel).isExhausted = false) :
    select sys (fuel + more) = select sys fuel := by
  unfold select at h ⊢
  simp only at h ⊢
  have hrows : ((subsetsOf (links sys)).map fun gamma => rowOf sys fuel (links sys) (classOf gamma)).any Row.isExhausted = false := by
    cases hc : ((subsetsOf (links sys)).map fun gamma => rowOf sys fuel (links sys) (classOf gamma)).any Row.isExhausted with
    | false => rfl
    | true =>
      unfold rule at h
      rw [if_pos hc] at h
      cases h
  have heq : ((subsetsOf (links sys)).map fun gamma => rowOf sys (fuel + more) (links sys) (classOf gamma))
      = (subsetsOf (links sys)).map fun gamma => rowOf sys fuel (links sys) (classOf gamma) :=
    List.map_congr_left fun gamma hg =>
      rowOf_stable sys wf fuel more (by
        have := List.any_eq_false.1 hrows _ (List.mem_map.2 ⟨gamma, hg, rfl⟩)
        simpa using this)
  rw [heq]

end BoundSelect

/-! ## The acyclic case -/

private theorem idx_inj : ∀ {l : List Nat} {a b : Nat}, a ∈ l → l.idxOf a = l.idxOf b → a = b := by
  intro l
  induction l with
  | nil => intro a b h; cases h
  | cons x xs ih =>
    intro a b ha hab
    simp only [List.idxOf_cons] at hab
    by_cases e1 : x = a
    · by_cases e2 : x = b
      · exact e1.symm.trans e2
      · simp [e1, show (a == b) = false by simpa [e1] using e2] at hab
    · have ha' : a ∈ xs := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm e1
        · exact h
      by_cases e2 : x = b
      · have e3 : (x == a) = false := by simpa using e1
        have e4 : (x == b) = true := by simpa using e2
        simp [e3, e4] at hab
      · have e3 : (x == a) = false := by simpa using e1
        have e4 : (x == b) = false := by simpa using e2
        simp only [e3, e4, cond_false, if_false, Bool.false_eq_true] at hab
        exact ih ha' (by omega)

private theorem idx_split {k : Nat} {rest : List Nat} : ∀ (pre : List Nat) {d : Nat}, k ∉ pre → d ∈ pre →
    (pre ++ k :: rest).idxOf d < (pre ++ k :: rest).idxOf k := by
  intro pre
  induction pre with
  | nil => intro d _ h; cases h
  | cons x xs ih =>
    intro d hk hd
    have hkx : (x == k) = false := by
      have : x ≠ k := fun e => hk (by simp [e])
      simpa using this
    have hk' : k ∉ xs := fun m => hk (List.mem_cons_of_mem _ m)
    simp only [List.cons_append, List.idxOf_cons, hkx]
    by_cases e : x = d
    · simp [e]
    · have hdx : (x == d) = false := by simpa using e
      have hd' : d ∈ xs := by
        rcases List.mem_cons.1 hd with h | h
        · exact absurd h.symm e
        · exact h
      have := ih hk' hd'
      simp only [hdx, Bool.false_eq_true, cond_false, if_false]
      omega

/-- The composition law applied once per key, in the given order, each from what came before it. -/
def applyOrder (sys : System) (opened : Nat → Bool) : List Nat → (Nat → Fact) → Nat → Fact
  | [], facts => facts
  | k :: rest, facts =>
      applyOrder sys opened rest fun x =>
        if x = k then composeWith (sys.equation k) opened (fun t => (facts t).patterns) else facts x

/-- `order` lists the keys so that every active read of a key comes strictly before it. No such order exists for a
    cyclic read graph, so this is the statement of acyclicity of the ACTIVE READS under one classification. -/
structure Topological (sys : System) (opened : Nat → Bool) (order : List Nat) : Prop where
  nodup : order.Nodup
  keys : ∀ k, k ∈ order ↔ k ∈ sys.keys
  before : ∀ k ∈ sys.keys, ∀ t ∈ activeTargets (sys.equation k) opened, order.idxOf t < order.idxOf k

section Acyclic

variable (sys : System) (opened : Nat → Bool) (fuel : Nat) (wf : sys.WellFormed)
variable {order : List Nat} (topo : Topological sys opened order)
include wf topo

private theorem rank_le_of_reach {a x : Nat} (ha : a ∈ sys.keys) (hx : x ∈ reachOf sys opened a) :
    order.idxOf x ≤ order.idxOf a := by
  have step : ∀ S : List Nat, (∀ y ∈ S, order.idxOf y ≤ order.idxOf a ∧ y ∈ sys.keys) →
      ∀ y ∈ grow sys opened S, order.idxOf y ≤ order.idxOf a ∧ y ∈ sys.keys := by
    intro S hS y hy
    rcases (mem_grow sys opened).1 hy with ⟨hk, hy | ⟨i, hi, ht⟩⟩
    · exact hS y hy
    · have h1 := hS i hi
      have h2 := topo.before i h1.2 y ht
      exact ⟨by omega, hk⟩
  have base : ∀ y ∈ grow sys opened [a], order.idxOf y ≤ order.idxOf a ∧ y ∈ sys.keys :=
    step [a] (fun y hy => by simp only [List.mem_singleton] at hy; subst hy; exact ⟨Nat.le_refl _, ha⟩)
  have all : ∀ n S, (∀ y ∈ S, order.idxOf y ≤ order.idxOf a ∧ y ∈ sys.keys) →
      ∀ y ∈ growN sys opened n S, order.idxOf y ≤ order.idxOf a ∧ y ∈ sys.keys := by
    intro n
    induction n with
    | zero => exact fun S h => h
    | succ n ih => exact fun S h => ih _ (step S h)
  exact (all _ _ base x hx).1

private theorem component_singleton {a b : Nat} (ha : a ∈ sys.keys) (hb : b ∈ sys.keys)
    (h : sameComponent (reachTable sys opened) a b = true) : a = b := by
  obtain ⟨h1, h2⟩ := (sameComponent_iff sys opened ha hb).1 h
  have e1 := rank_le_of_reach sys opened wf topo ha h1
  have e2 := rank_le_of_reach sys opened wf topo hb h2
  have hao : a ∈ order := (topo.keys a).2 ha
  have hbo : b ∈ order := (topo.keys b).2 hb
  exact idx_inj hao (by omega)

private theorem no_self_read {k t : Nat} (hk : k ∈ sys.keys) (ht : t ∈ activeTargets (sys.equation k) opened) : t ≠ k := by
  intro e
  have := topo.before k hk t ht
  rw [e] at this
  omega

/-- In the acyclic case a pending key with settled reads gets a fact: no gate lifts, no rounds run, nothing fails. -/
private theorem layer_clean {cells : Memo Cell}
    (hclean : ∀ k, cells.get k = .pending ∨ ∃ f, cells.get k = .fact f) :
    ∀ k, (layer sys opened fuel (reachTable sys opened) cells).get k = .pending
      ∨ ∃ f, (layer sys opened fuel (reachTable sys opened) cells).get k = .fact f := by
  intro k
  by_cases hk : k ∈ sys.keys
  · rw [layer_apply sys opened fuel _ cells hk]
    rcases hclean k with hp | ⟨f, hf⟩
    · rw [hp]
      simp only
      by_cases hr : layerReady sys opened (componentOf sys (reachTable sys opened) k) cells.get = true
      · rw [if_pos hr]
        right
        generalize hm : componentOf sys (reachTable sys opened) k = members
        have hmem : ∀ x ∈ members, x = k := by
          intro x hx
          rw [← hm] at hx
          obtain ⟨hxk, hs⟩ := (mem_componentOf sys).1 hx
          exact (component_singleton sys opened wf topo hk hxk hs).symm
        have hnoex : (outsideReads sys opened members).any (fun t => cells.get t == .exhausted) = false := by
          apply List.any_eq_false.2
          intro t _
          rcases hclean t with h | ⟨g, h⟩ <;> simp [h]
        have hnome : (outsideReads sys opened members).any (fun t => cells.get t == .meaningless) = false := by
          apply List.any_eq_false.2
          intro t _
          rcases hclean t with h | ⟨g, h⟩ <;> simp [h]
        have hgate : gateLifts sys opened members (lowerReads sys opened members cells.get) = false := by
          unfold gateLifts
          apply List.any_eq_false.2
          intro m hmm
          intro hany
          obtain ⟨t, ht, hrest⟩ := List.any_eq_true.1 hany
          have tm : t ∈ members := by
            simp only [Bool.and_eq_true, List.contains_iff_mem] at hrest
            exact hrest.1
          have emk := hmem m hmm
          have etk := hmem t tm
          subst emk
          exact no_self_read sys opened wf topo hk ht etk
        unfold evalComponent
        simp only
        rw [if_neg (by simp [hnoex]), if_neg (by simp [hnome]), if_pos (by simp [hgate])]
        exact ⟨_, rfl⟩
      · rw [if_neg hr]
        exact .inl rfl
    · rw [hf]
      exact .inr ⟨f, rfl⟩
  · left
    exact tabulate_of_not_mem _ _ _ hk

private theorem layers_clean (n : Nat) : ∀ {cells : Memo Cell},
    (∀ k, cells.get k = .pending ∨ ∃ f, cells.get k = .fact f) →
    ∀ k, (layers sys opened fuel (reachTable sys opened) n cells).get k = .pending
      ∨ ∃ f, (layers sys opened fuel (reachTable sys opened) n cells).get k = .fact f := by
  induction n with
  | zero => exact fun h => h
  | succ n ih => exact fun h => ih (layer_clean sys opened fuel wf topo h)

/-- The acyclic reading: every key has a fact. -/
theorem acyclic_all_facts {k : Nat} (hk : k ∈ sys.keys) : ∃ f, (evalVector sys opened fuel).get k = .fact f := by
  have h := layers_clean sys opened fuel wf topo sys.keys.length (cells := ⟨fun _ => .pending⟩) (fun _ => .inl rfl) k
  rcases h with h | h
  · exact absurd h (no_pending_cell sys opened fuel wf hk)
  · exact h

private theorem solutions_agree {F G : Nat → Fact}
    (hF : ∀ k ∈ sys.keys, F k = composeWith (sys.equation k) opened (fun t => (F t).patterns))
    (hG : ∀ k ∈ sys.keys, G k = composeWith (sys.equation k) opened (fun t => (G t).patterns)) :
    ∀ k ∈ sys.keys, F k = G k := by
  have main : ∀ n, ∀ k ∈ sys.keys, order.idxOf k = n → F k = G k := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro k hk hn
      rw [hF k hk, hG k hk]
      apply composeWith_congr
      intro t ht
      left
      have tk : t ∈ sys.keys := by
        obtain ⟨r, hr, e, _⟩ := mem_activeTargets.1 ht
        exact (wf.targets k hk r hr).1 t e
      have hlt := topo.before k hk t ht
      rw [ih (order.idxOf t) (by omega) t tk rfl]
  exact fun k hk => main _ k hk rfl

private theorem idx_before {pre rest : List Nat} {d k : Nat} (ho : order = pre ++ k :: rest) (hn : order.Nodup)
    (hd : d ∈ pre) : order.idxOf d < order.idxOf k := by
  subst ho
  have hk : k ∉ pre := by
    intro h
    have := List.nodup_append.1 hn
    exact this.2.2 k h k List.mem_cons_self rfl
  exact idx_split pre hk hd

private theorem applyOrder_solves : ∀ (rest pre : List Nat) (facts : Nat → Fact), order = pre ++ rest →
    (∀ d ∈ pre, facts d = composeWith (sys.equation d) opened (fun t => (facts t).patterns)) →
    ∀ d ∈ order, applyOrder sys opened rest facts d
      = composeWith (sys.equation d) opened (fun t => (applyOrder sys opened rest facts t).patterns) := by
  intro rest
  induction rest with
  | nil =>
    intro pre facts ho h d hd
    rw [ho] at hd
    simp only [List.append_nil] at hd
    exact h d hd
  | cons k rest ih =>
    intro pre facts ho h
    apply ih (pre ++ [k]) _ (by simp [ho])
    have hk : k ∈ sys.keys := (topo.keys k).1 (by rw [ho]; simp)
    have reads : ∀ d, (d ∈ pre ∨ d = k) → ∀ t ∈ activeTargets (sys.equation d) opened, t ≠ k := by
      intro d hd t ht e
      have hdk : d ∈ sys.keys := by
        rcases hd with hd | rfl
        · exact (topo.keys d).1 (by rw [ho]; simp [hd])
        · exact hk
      have h1 := topo.before d hdk t ht
      rcases hd with hd | hd
      · have h2 := idx_before sys opened wf topo ho topo.nodup hd
        rw [e] at h1
        omega
      · rw [e, hd] at h1
        omega
    intro d hd
    have hcases : d ∈ pre ∨ d = k := by simpa using hd
    have hcongr : composeWith (sys.equation d) opened (fun t => (facts t).patterns)
        = composeWith (sys.equation d) opened (fun t => ((fun x =>
            if x = k then composeWith (sys.equation k) opened (fun t => (facts t).patterns) else facts x) t).patterns) := by
      apply composeWith_congr
      intro t ht
      left
      simp [reads d hcases t ht]
    rcases hcases with hp | e
    · have hne : d ≠ k := by
        intro e
        subst e
        have := idx_before sys opened wf topo ho topo.nodup hp
        omega
      simp only [hne, if_false]
      rw [h d hp]
      exact hcongr
    · subst e
      simp only [if_true]
      exact hcongr

/-- THE ACYCLIC CASE IS PLAIN DEPENDENCY ORDER. For a topological order of the active reads, the reading of the system is
    the composition law applied once per key in that order, whatever the bound: no gate lifts and no round runs. -/
theorem acyclic_agrees {k : Nat} (hk : k ∈ sys.keys) :
    (evalVector sys opened fuel).get k = .fact (applyOrder sys opened order (fun _ => closedFact) k) := by
  have hcells : ∀ x ∈ sys.keys, (evalVector sys opened fuel).get x
      = .fact (factOf ((evalVector sys opened fuel).get x)) := by
    intro x hx
    obtain ⟨f, hf⟩ := acyclic_all_facts sys opened fuel wf topo hx
    rw [hf]
    rfl
  have hF : ∀ x ∈ sys.keys, factOf ((evalVector sys opened fuel).get x) = composeWith (sys.equation x) opened
      (fun t => (factOf ((evalVector sys opened fuel).get t)).patterns) := by
    intro x hx
    have := ((goodCells_evalVector sys opened fuel wf).closed x hx _ (hcells x hx)).2
    rw [this]
    apply composeWith_congr
    intro t _
    left
    exact Cell.patterns_factOf _
  have hG : ∀ x ∈ sys.keys, applyOrder sys opened order (fun _ => closedFact) x = composeWith (sys.equation x) opened
      (fun t => (applyOrder sys opened order (fun _ => closedFact) t).patterns) := by
    intro x hx
    exact applyOrder_solves sys opened wf topo order [] _ (by simp) (by simp) x ((topo.keys x).2 hx)
  rw [hcells k hk, solutions_agree sys opened wf topo hF hG k hk]

/-- Any two dependency orders give the same facts: no topological sort is privileged. -/
theorem acyclic_order_independent {other : List Nat} (topo' : Topological sys opened other)
    {k : Nat} (hk : k ∈ sys.keys) :
    applyOrder sys opened order (fun _ => closedFact) k = applyOrder sys opened other (fun _ => closedFact) k := by
  have h1 := acyclic_agrees sys opened 0 wf topo hk
  have h2 := acyclic_agrees sys opened 0 wf topo' hk
  rw [h1] at h2
  exact Cell.fact.inj h2

end Acyclic

end KatLang.SignatureCompletion
