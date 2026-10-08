/-!
# Grace movement (PAR-06; X-49, decided 2026-10-08) — standalone specification model

Grace is a C#-only front-end operation (`src/KatLang/GraceMovement.cs`, applied by the parameter
detector to an owner's OWN inferred parameters): the Lean semantics receives the elaborated
parameter list and never sees Grace, so this module imports nothing from `KatLang` and changes
nothing in the evaluator model. It states the movement law over first-occurrence identities
`0 … n-1` and their exact summed weights `ws` (prefix `~` −1, postfix `~` +1 per marker), and
checks it.

The law: every identity with a POSITIVE weight takes one turn, from the last-occurring to the
first-occurring; then every identity with a NEGATIVE weight, from the first-occurring to the
last-occurring. In its turn an identity exchanges with its neighbour on the side its remaining
weight points to, one unit per exchange, until the remaining weight is zero, it reaches an end, or
the neighbour moves the same way with at least as much REMAINING weight (strict comparison of
current remaining weights). A passed identity keeps its weight; unused weight stays and blocks.

The `#guard move [w…] == [order…]` table below is shared with C#: the test
`GraceMovementLawTests.TheLeanGuardTable_MatchesTheFrontEnd` reads every such line and checks the
real front end against it.

Proved: the result is a permutation of the identities (`move_perm`), and a list without weights is
unchanged (`move_unweighted`). Every definition is total by construction (a turn has fuel `n`; a
turn makes at most `n − 1` exchanges, since its mover moves one way). Checked by `#guard` over the
finite domain of every weight vector of length 1–4 with weights −2…2 (evaluation, not proof): the
single-mover law, equal-weight order, own-direction monotonicity, final-state blocking, fuel
sufficiency, and agreement with the source-order-with-yielding formulation (`yieldMove`). General
proofs of those properties, and of `move = yieldMove`, are open follow-up work.
-/

namespace KatLang.GraceMovement

/-- Exchanges the elements at positions `i` and `i + 1` (no change when there is no `i + 1`). -/
def swapAt : List Nat → Nat → List Nat
  | [], _ => []
  | [a], _ => [a]
  | a :: b :: rest, 0 => b :: a :: rest
  | a :: b :: rest, i + 1 => a :: swapAt (b :: rest) i

theorem swapAt_perm : ∀ (l : List Nat) (i : Nat), (swapAt l i).Perm l
  | [], _ => List.Perm.refl _
  | [_], _ => List.Perm.refl _
  | a :: b :: rest, 0 => List.Perm.swap a b rest
  | a :: b :: rest, i + 1 => (swapAt_perm (b :: rest) i).cons a

/-- The movement state: identities in their current order, and each identity's remaining weight. -/
structure State where
  order : List Nat
  remaining : List Int
  deriving Repr

def weightOf (remaining : List Int) (p : Nat) : Int := remaining.getD p 0

def positionOf : List Nat → Nat → Nat
  | [], _ => 0
  | q :: rest, p => if q == p then 0 else positionOf rest p + 1

/-- One exchange of `p` toward the side its remaining weight points to, if the law allows it. -/
def step? (s : State) (p : Nat) : Option State :=
  let r := weightOf s.remaining p
  let i := positionOf s.order p
  if 0 < r then
    if i + 1 < s.order.length ∧ weightOf s.remaining (s.order.getD (i + 1) 0) < r then
      some { order := swapAt s.order i, remaining := s.remaining.set p (r - 1) }
    else none
  else if r < 0 then
    if 0 < i ∧ r < weightOf s.remaining (s.order.getD (i - 1) 0) then
      some { order := swapAt s.order (i - 1), remaining := s.remaining.set p (r + 1) }
    else none
  else none

/-- One turn: exchanges while the law allows, at most `fuel` of them. -/
def turn : Nat → State → Nat → State
  | 0, s, _ => s
  | fuel + 1, s, p =>
    match step? s p with
    | none => s
    | some s' => turn fuel s' p

/-- The schedule, fixed by the initial weights: positive weights from the last-occurring, then
    negative weights from the first-occurring. -/
def turns (ws : List Int) : List Nat :=
  (List.range ws.length).reverse.filter (fun p => decide (0 < ws.getD p 0))
    ++ (List.range ws.length).filter (fun p => decide (ws.getD p 0 < 0))

def settleWith (fuel : Nat) (ws : List Int) : State :=
  (turns ws).foldl (fun s p => turn fuel s p) { order := List.range ws.length, remaining := ws }

def settle (ws : List Int) : State := settleWith ws.length ws

/-- THE movement law: identities `0 … n-1` in their final order. -/
def move (ws : List Int) : List Nat := (settle ws).order

/-! ## Proofs -/

theorem step?_perm {s s' : State} {p : Nat} (h : step? s p = some s') : s'.order.Perm s.order := by
  unfold step? at h
  dsimp only at h
  split at h
  · split at h
    · cases h
      exact swapAt_perm _ _
    · cases h
  · split at h
    · split at h
      · cases h
        exact swapAt_perm _ _
      · cases h
    · cases h

theorem turn_perm : ∀ (fuel : Nat) (s : State) (p : Nat), (turn fuel s p).order.Perm s.order
  | 0, _, _ => List.Perm.refl _
  | fuel + 1, s, p => by
    unfold turn
    split
    · exact List.Perm.refl _
    · rename_i s' h
      exact (turn_perm fuel s' p).trans (step?_perm h)

theorem foldl_turn_perm (fuel : Nat) :
    ∀ (ps : List Nat) (s : State), (ps.foldl (fun s p => turn fuel s p) s).order.Perm s.order
  | [], _ => List.Perm.refl _
  | p :: ps, s => (foldl_turn_perm fuel ps (turn fuel s p)).trans (turn_perm fuel s p)

/-- No identity is lost, duplicated or invented. -/
theorem move_perm (ws : List Int) : (move ws).Perm (List.range ws.length) :=
  foldl_turn_perm ws.length (turns ws) _

theorem getD_replicate_zero : ∀ (n p : Nat), (List.replicate n (0 : Int)).getD p 0 = 0
  | 0, _ => by simp
  | _ + 1, 0 => by simp [List.replicate_succ]
  | n + 1, p + 1 => by simpa [List.replicate_succ] using getD_replicate_zero n p

/-- Without weights nothing moves: the schedule is empty. -/
theorem move_unweighted (n : Nat) : move (List.replicate n 0) = List.range n := by
  have hturns : turns (List.replicate n 0) = [] := by
    simp only [turns, getD_replicate_zero]
    simp
  simp [move, settle, settleWith, hturns]

/-! ## The shared table (read by the C# test as well) -/

-- A. K = s * 100 + ~x * 10 + ~y ↦ K(x, y, s)
#guard move [0, -1, -1] == [1, 2, 0]
-- B. Z = s~ * 100 + x~ * 10 + y ↦ Z(y, s, x): x moves first, making room for s
#guard move [1, 1, 0] == [2, 0, 1]
-- C. the X-49 witness K = a * 100 + b~ * 10 + ~~c ↦ K(c, a, b)
#guard move [0, 1, -2] == [2, 0, 1]
#guard move [0, 0, -2] == [2, 0, 1]
-- D. opposing movements, postfix first: K = a~ * 100 + b * 10 + ~c ↦ K(b, c, a)
#guard move [1, 0, -1] == [1, 2, 0]
-- E. residual weight: F = ~a * 100 + b * 10 + ~~c ↦ F(a, c, b)
#guard move [-1, 0, -2] == [0, 2, 1]
-- F. equal prefix weights at the front: K = ~a * 100 + ~b * 10 + c ↦ K(a, b, c)
#guard move [-1, -1, 0] == [0, 1, 2]
-- G. patent FIG. 12: SumOfParams = a~~ + b~ ↦ SumOfParams(b, a)
#guard move [2, 1] == [1, 0]
-- H, I. equal-weight groups move as a unit when all outside weights are zero
#guard move [1, 1, 1, 0] == [3, 0, 1, 2]
#guard move [0, -1, -1, -1] == [1, 2, 3, 0]
-- J. passive displacement: K = a + b~ + c~ + d~ + ~e ↦ K(e, a, b, c, d)
#guard move [0, 1, 1, 1, -1] == [4, 0, 1, 2, 3]
-- the patent's worked examples (FIG. 6, 7, 9, 10, 11, 14; FIG. 12 is G)
#guard move [0, -1] == [1, 0]
#guard move [1, 0] == [1, 0]
#guard move [2, 0, -1] == [2, 1, 0]
#guard move [1, 0, -2] == [2, 1, 0]
#guard move [3, 0, -1] == [2, 1, 0]
#guard move [0, 0, -2] == [2, 0, 1]
-- residual weight, saturation and stronger pushes
#guard move [1, 1] == [0, 1]
#guard move [0, 1, 1] == [0, 1, 2]
#guard move [-1, 0, -3] == [2, 0, 1]
#guard move [0, -1, -2] == [2, 1, 0]
#guard move [0, 0, -5] == [2, 0, 1]
#guard move [4, 0, 0] == [1, 2, 0]
#guard move [2, -1, -2] == [2, 1, 0]
-- unequal neighbours each make their own moves
#guard move [1, 2, 0] == [2, 0, 1]
#guard move [2, 1, 0] == [2, 1, 0]
#guard move [0, -2, -1] == [1, 2, 0]
#guard move [0, 1, 2, 0, 0] == [0, 3, 1, 4, 2]
#guard move [0, 2, 1, 0, 0] == [0, 3, 2, 1, 4]
#guard move [0, 0, -1, -2, 0] == [0, 3, 2, 1, 4]
#guard move [0, 0, -2, -1, 0] == [2, 0, 3, 1, 4]
-- opposite directions in longer lists
#guard move [2, 0, 0, -2] == [1, 3, 2, 0]
#guard move [1, 1, -1] == [2, 0, 1]
#guard move [1, 1, -1, -1] == [2, 0, 3, 1]
#guard move [0, -1, 1, 0] == [1, 0, 3, 2]
-- single names, no weights
#guard move [] == []
#guard move [-3] == [0]
#guard move [0, 0, 0] == [0, 1, 2]

/-! ## Bounded checks over every weight vector of length 1–4 with weights −2…2 (780 states) -/

def weightsVectors : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (weightsVectors n).flatMap (fun v => [-2, -1, 0, 1, 2].map (fun w => v ++ [w]))

def domain : List (List Int) := [1, 2, 3, 4].flatMap weightsVectors

#guard domain.length == 780

/-- Where identity `p` ends up. -/
def placeOf (order : List Nat) (p : Nat) : Nat := positionOf order p

/-- A lone weighted identity moves exactly its weight, stopping at the end; the rest keep their order. -/
def singleMoverHolds (ws : List Int) : Bool :=
  let weighted := (List.range ws.length).filter (fun p => ws.getD p 0 != 0)
  match weighted with
  | [p] =>
    let n := ws.length
    let target : Int := max 0 (min ((n : Int) - 1) ((p : Int) + ws.getD p 0))
    let order := move ws
    placeOf order p == target.toNat
      && (order.filter (· != p)) == ((List.range n).filter (· != p))
  | _ => true

def equalWeightsKeepOrder (ws : List Int) : Bool :=
  let order := move ws
  (List.range ws.length).all fun p => (List.range ws.length).all fun q =>
    !(decide (p < q) && ws.getD p 0 == ws.getD q 0) || decide (placeOf order p < placeOf order q)

/-- One more postfix marker never moves its identity earlier (read backwards: one more prefix
    marker never later), and never lets it overtake leftward an identity it was behind. -/
def monotoneHolds (ws : List Int) : Bool :=
  (List.range ws.length).all fun p =>
    let w := ws.getD p 0
    !(decide (w < 2)) || (
      let before := move ws
      let after := move (ws.set p (w + 1))
      decide (placeOf before p ≤ placeOf after p)
        && (List.range ws.length).all fun q =>
          !(decide (placeOf before q < placeOf before p)) || decide (placeOf after q < placeOf after p))

/-- Every leftover is held by the end it points to or by a neighbour moving the same way with at
    least as much remaining weight. -/
def finalBlockingHolds (ws : List Int) : Bool :=
  let s := settle ws
  let n := s.order.length
  (List.range n).all fun k =>
    let r := weightOf s.remaining (s.order.getD k 0)
    if 0 < r then k + 1 == n || decide (r ≤ weightOf s.remaining (s.order.getD (k + 1) 0))
    else if r < 0 then k == 0 || decide (weightOf s.remaining (s.order.getD (k - 1) 0) ≤ r)
    else true

#guard domain.all singleMoverHolds
#guard domain.all equalWeightsKeepOrder
#guard domain.all monotoneHolds
#guard domain.all finalBlockingHolds
-- fuel `n` per turn is enough: more fuel changes nothing
#guard domain.all fun ws => (settleWith (ws.length + 5) ws).order == move ws

/-! ## The source-order-with-yielding formulation

Identities take turns in first-occurrence order; a mover blocked by a same-direction neighbour that
has not had its turn lets that neighbour move first, then tries again. -/

structure YieldState where
  order : List Nat
  remaining : List Int
  started : List Bool

/-- Continues `p`'s turn (fuel bounds every recursion path). -/
def yieldRun : Nat → YieldState → Nat → YieldState
  | 0, s, _ => s
  | fuel + 1, s, p =>
    let r := weightOf s.remaining p
    let i := positionOf s.order p
    if r = 0 then s
    else if 0 < r ∧ i + 1 ≥ s.order.length then s
    else if r < 0 ∧ i = 0 then s
    else
      let j := if 0 < r then i + 1 else i - 1
      let q := s.order.getD j 0
      let rq := weightOf s.remaining q
      let passes := if 0 < r then decide (rq < r) else decide (r < rq)
      if passes then
        yieldRun fuel
          { s with
            order := swapAt s.order (min i j)
            remaining := s.remaining.set p (if 0 < r then r - 1 else r + 1) } p
      else if !(s.started.getD q true) && (if 0 < r then decide (0 < rq) else decide (rq < 0)) then
        yieldRun fuel (yieldRun fuel { s with started := s.started.set q true } q) p
      else s

def yieldMove (ws : List Int) : List Nat :=
  let n := ws.length
  let fuel := 4 * (n + 1) * (n + 1)
  let start : YieldState := { order := List.range n, remaining := ws, started := List.replicate n false }
  let final := (List.range n).foldl
    (fun s p =>
      if s.started.getD p true || ws.getD p 0 == 0 then s
      else yieldRun fuel { s with started := s.started.set p true } p)
    start
  final.order

#guard domain.all fun ws => yieldMove ws == move ws

end KatLang.GraceMovement
