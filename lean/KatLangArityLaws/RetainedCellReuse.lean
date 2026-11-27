import KatLangArityLaws

open KatLang

/-!
# Detached reuse of retained runtime-alias binding cells (ledger R-1, November 2026)

THE RULE. A retained runtime-alias binding cell — the cell of a non-parameter row, established by
`aliasBindingCellRecorded` — carries an INPUT RECORD (`CellInputs`): the number of lexical activations
recorded when the cell was established (`watermark`), the LEAST activation below that watermark its
computation has read an input through (`least`, `CellInputs.note`) with all such reads, each once
(`reads`), and what a detached reuse reports
(`refusal`, the alias's own `localOnlyProperty`). The row's context is MARKED with the cell
(`EvalCtx.inputRecord`) and every context derived from it inherits the mark, so the three input reads
that go through an activation — a captured parameter operation (`capturedParameterActivation?`), an
admitted local-only property read (`noteLocalOnlyRead`) and an admitted access of a local-only member
(`noteMemberAccess`) — record themselves on the cell whose computation they belong to
(`noteCellInputsAt`), and on every cell that reused it of which they are an
input too (`CellInputs.forwards`, `noteForwarded`).

A READER's use of a retained cell's VALUE or CALLABLE (`reuseRetainedCell`: the alias's bare read, the
value view's zero-supply invocation, the runtime step of the alias chase) is JUDGED BEFORE THE CHANNEL
RUNS (`judgeRetainedCellReuse`): a reader that DETACHES an input the cell is KNOWN to have read
(`CellInputs.dependsFor`: one of the cell's recorded reads, `CellInputs.reads`, is an enclosing call of the
reader below its watermark) is refused with the cell's refusal and nothing of the cell runs; any other
reader is ADMITTED
(`CellInputs.admit`) and the channel runs serving the reader's detached owners (`servingDetached`).

THE DEMAND DECIDES (owner decision, November 24 2026). A computation can go on after its channel
answered — a lazy position or a captured call's argument created in it runs later, in the context it
was created in, and notes its reads then. Such a note is REFUSED, with its own refusal in the state it
started from, exactly when a detached evaluation that detaches the activation is being served
(`CellRecords.serving`: an exported evaluation in progress, or a reader whose reuse is running a
retained cell's channel) and the read is an input of a cell that admitted a reader detaching it
(`CellRecords.lateRefused`). A read an ATTACHED reader demands is never refused: after a detached
reader counted a lazy list, the list's own row may read every position with its own inputs. Membership in both the served and admitted owner sets decides a deferred read.

What is proved here (all about the production definitions):
1. THE RECORD IS EXACT FOR WATERMARKS (`trace_dependsBelow`, `trace_refusalFor`): for every reader
   watermark, the record a trace of notes builds depends below it exactly when some read of the WHOLE
   trace lies below both the cell's and the reader's watermark. Its watermark and refusal never change
   (`note_watermark`, `note_refusal`); nothing is detached at the default watermark
   (`dependsBelow_default`, `refusalFor_default`). THE JUDGMENT (§ 1b, RETURNED CALLABLES ACROSS
   DETACHED READS, November 2026) asks the reader's ENCLOSING CALLS instead (`CellInputs.dependsFor`
   over every read, `CellInputs.reads`): it is EXACT — it refuses a reader exactly when the reader
   detaches an activation some read of the trace went through (`trace_dependsFor`,
   `trace_dependsFor_false`) — and refuses no reader the watermark's test admits
   (`trace_dependsFor_dependsBelow`).
2. OWN WORK IS NO INPUT (`noteCellInputsAt_own`, `lateRefused_own`): a read through an activation the
   cell's own computation recorded — one not below the cell's watermark — changes no record, reaches
   no record the cell forwards to, and is never refused.
3. THE DEMAND DECIDES (`lateRefused_unserved`, `lateRefused_attached`, `noteCellInput_unserved`): while
   no detached evaluation is served — or none that detaches the activation — the note is never
   refused: it writes the input records only.
4. SERVING (`servingDetached_served`, `servingDetached_default`, `servingDetached_raised`): an
   owner set the records already serve, the empty set in particular, runs the evaluation itself;
   otherwise the evaluation runs under the extended owner set, which is restored whatever its completed
   outcome.
5. THE REUSE. NEUTRALITY: at the default watermark, outside every cell's computation, the reuse IS the
   channel (`reuseRetainedCell_default`, `reuseRetainedCell_quiet`); a cell without a record is never
   judged (`reuseRetainedCell_unrecorded`). REFUSAL BEFORE THE CHANNEL: a reader that detaches an
   input the cell is known to have read gets the cell's refusal IN THE STATE THE REUSE STARTED FROM —
   the channel does not run, so no effect of the cell is executed (`reuseRetainedCell_refused`).
   SHARING: every other reader is admitted — the input records alone change — and the channel runs
   served from there (`reuseRetainedCell_admitted`).

What is NOT proved: that the notes a run makes are ALL the input reads of a cell's computation in the
sense of an independent trace semantics (there is none to compare with — the guards and the C# tests
pin the witnesses); that every deferred read an exported evaluation causes happens while it is served
(a deferred part it created itself runs later in its own detached context, whose own reads are
refused there, but the reads it then causes in a retained cell's computation are judged against
whatever is served at that time); the C#/Lean correspondence of the record (tested, not proved); and
the open half of E-22, reader independence of an exported miss across binding contexts.
-/

namespace KatLang.RetainedCellReuse

/-! ## 1. The record -/

/-- The record a trace of input reads builds from an empty record under the watermark `wm`. -/
def traceRecord (wm : Nat) (refusal : Error) (trace : List Nat) : CellInputs :=
  trace.foldl (fun r a => r.note a) { watermark := wm, refusal := refusal }

theorem note_watermark (r : CellInputs) (a : Nat) : (r.note a).watermark = r.watermark := by
  unfold CellInputs.note
  split <;> rfl

theorem note_refusal (r : CellInputs) (a : Nat) : (r.note a).refusal = r.refusal := by
  unfold CellInputs.note
  split <;> rfl

theorem note_readers (r : CellInputs) (a : Nat) : (r.note a).readers = r.readers := by
  unfold CellInputs.note
  split <;> rfl

theorem note_forwards (r : CellInputs) (a : Nat) : (r.note a).forwards = r.forwards := by
  unfold CellInputs.note
  split <;> rfl

/-- Nothing is detached at the default watermark. -/
theorem dependsBelow_default (r : CellInputs) : r.dependsBelow 0 = false := by
  unfold CellInputs.dependsBelow
  split <;> simp

/-- Nothing is refused at the default watermark. -/
theorem refusalFor_default (r : CellInputs) : r.refusalFor 0 = none := by
  unfold CellInputs.refusalFor
  rw [dependsBelow_default]
  rfl

/-- THE STEP: after one more read the record depends below a reader's watermark exactly when it did,
    or the new read lies below both the cell's watermark and the reader's. -/
theorem dependsBelow_note (r : CellInputs) (a w : Nat) :
    (r.note a).dependsBelow w = (r.dependsBelow w || (decide (a < r.watermark) && decide (a < w))) := by
  unfold CellInputs.note CellInputs.dependsBelow
  by_cases ha : a < r.watermark
  · simp only [ha, ↓reduceIte]
    cases hl : r.least with
    | none => simp
    | some l =>
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true, true_and]
      omega
  · simp [ha]

/-- What a record built from the trace `q` knows: its watermark, and for every reader watermark
    whether some read of `q` lies below both. -/
def Answers (wm : Nat) (r : CellInputs) (q : List Nat) : Prop :=
  r.watermark = wm ∧ ∀ w, r.dependsBelow w = q.any (fun a => decide (a < wm) && decide (a < w))

theorem answers_note (wm : Nat) (r : CellInputs) (q : List Nat) (a : Nat) (h : Answers wm r q) :
    Answers wm (r.note a) (q ++ [a]) := by
  obtain ⟨hwm, hans⟩ := h
  refine ⟨by rw [note_watermark, hwm], fun w => ?_⟩
  rw [dependsBelow_note, hans w, hwm]
  simp [List.any_append]

theorem answers_foldl (wm : Nat) (trace : List Nat) :
    ∀ (r : CellInputs) (q : List Nat), Answers wm r q →
      Answers wm (trace.foldl (fun r a => r.note a) r) (q ++ trace) := by
  induction trace with
  | nil => intro r q h; simpa using h
  | cons x rest ih =>
    intro r q h
    have := ih (r.note x) (q ++ [x]) (answers_note wm r q x h)
    simpa using this

/-- **THE RECORD IS EXACT.** For every reader watermark `w`, the record a trace of input reads builds
    depends below `w` exactly when some read of the WHOLE trace lies below both the cell's watermark
    and `w`: the least activation answers every reader as the full trace would. -/
theorem trace_dependsBelow (wm : Nat) (refusal : Error) (w : Nat) (trace : List Nat) :
    (traceRecord wm refusal trace).dependsBelow w =
      trace.any (fun a => decide (a < wm) && decide (a < w)) := by
  have h0 : Answers wm { watermark := wm, refusal := refusal } [] := ⟨rfl, fun w => rfl⟩
  have := (answers_foldl wm trace _ [] h0).2 w
  rw [List.nil_append] at this
  exact this

theorem foldl_note_refusal (trace : List Nat) :
    ∀ r : CellInputs, (trace.foldl (fun r a => r.note a) r).refusal = r.refusal := by
  induction trace with
  | nil => intro r; rfl
  | cons x rest ih => intro r; rw [List.foldl_cons, ih, note_refusal]

/-- A cell's least read answers every watermark: `refusalFor` refuses exactly the readers whose
    watermark lies above an activation its computation read through, with its own refusal. -/
theorem trace_refusalFor (wm : Nat) (refusal : Error) (w : Nat) (trace : List Nat) :
    (traceRecord wm refusal trace).refusalFor w =
      if trace.any (fun a => decide (a < wm) && decide (a < w)) then some refusal else none := by
  unfold CellInputs.refusalFor
  rw [trace_dependsBelow]
  unfold traceRecord
  rw [foldl_note_refusal]

/-! ## 1b. The judgment over the reader's enclosing calls (RETURNED CALLABLES ACROSS DETACHED READS)

A reader detaches only its ENCLOSING CALLS below its watermark (`EvalCtx.isDetached`), so the record keeps
every read below the cell's watermark (`CellInputs.reads`), and the judgment asks whether the reader
detaches one of them (`CellInputs.dependsFor`) rather than whether its watermark lies above the least one
(`dependsBelow`). It is EXACT for the trace of notes (`trace_dependsFor`): a reader is refused exactly when it
detaches an activation some read of the trace went through. It refuses no reader the watermark's test
admits (`trace_dependsFor_dependsBelow`), and it admits the readers the watermark's test refused only
because a read went through the level of a callable another computation returned, which encloses none of
them. -/

/-- Nothing is refused at the default watermark. -/
theorem dependsFor_default (r : CellInputs) (owners : List Nat) : r.dependsFor 0 owners = false := by
  unfold CellInputs.dependsFor
  simp

/-- The reads after one more note: the former ones, and the new read when it is below the watermark. -/
theorem mem_note_reads (r : CellInputs) (a x : Nat) :
    x ∈ (r.note a).reads ↔ x ∈ r.reads ∨ (x = a ∧ a < r.watermark) := by
  unfold CellInputs.note
  by_cases ha : a < r.watermark
  · simp only [ha, ↓reduceIte, and_true]
    split
    · rename_i hc
      have hmem : a ∈ r.reads := by simpa using hc
      constructor
      · exact Or.inl
      · rintro (h | rfl)
        · exact h
        · exact hmem
    · simp [List.mem_append]
  · simp [ha]

/-- What a record built from the trace `q` reads: exactly the reads of `q` below its watermark. -/
def ReadsOf (wm : Nat) (r : CellInputs) (q : List Nat) : Prop :=
  r.watermark = wm ∧ ∀ x, x ∈ r.reads ↔ x ∈ q ∧ x < wm

theorem readsOf_note (wm : Nat) (r : CellInputs) (q : List Nat) (a : Nat) (h : ReadsOf wm r q) :
    ReadsOf wm (r.note a) (q ++ [a]) := by
  obtain ⟨hwm, hmem⟩ := h
  refine ⟨by rw [note_watermark, hwm], fun x => ?_⟩
  rw [mem_note_reads, hmem x, hwm, List.mem_append, List.mem_singleton]
  constructor
  · rintro (⟨hq, hlt⟩ | ⟨rfl, hlt⟩)
    · exact ⟨.inl hq, hlt⟩
    · exact ⟨.inr rfl, hlt⟩
  · rintro ⟨hq | rfl, hlt⟩
    · exact .inl ⟨hq, hlt⟩
    · exact .inr ⟨rfl, hlt⟩

theorem readsOf_foldl (wm : Nat) (trace : List Nat) :
    ∀ (r : CellInputs) (q : List Nat), ReadsOf wm r q →
      ReadsOf wm (trace.foldl (fun r a => r.note a) r) (q ++ trace) := by
  induction trace with
  | nil => intro r q h; simpa using h
  | cons x rest ih =>
    intro r q h
    have := ih (r.note x) (q ++ [x]) (readsOf_note wm r q x h)
    simpa using this

/-- The record of a trace reads exactly the trace's reads below the cell's watermark. -/
theorem trace_reads (wm : Nat) (refusal : Error) (trace : List Nat) (x : Nat) :
    x ∈ (traceRecord wm refusal trace).reads ↔ x ∈ trace ∧ x < wm := by
  have h0 : ReadsOf wm { watermark := wm, refusal := refusal } [] := ⟨rfl, fun x => by simp⟩
  have := (readsOf_foldl wm trace _ [] h0).2 x
  simpa [traceRecord] using this

/-- **THE JUDGMENT IS EXACT.** The record a trace of notes builds refuses a reader exactly when the reader
    DETACHES an activation some read of the trace went through below the cell's watermark — an enclosing
    call of the reader recorded before its evaluation started. -/
theorem trace_dependsFor (wm : Nat) (refusal : Error) (trace : List Nat) (ctx : EvalCtx) :
    (traceRecord wm refusal trace).dependsFor ctx.detachedBefore ctx.detachedOwners = true ↔
      ∃ a ∈ trace, a < wm ∧ ctx.isDetached a = true := by
  unfold CellInputs.dependsFor
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, ha, hp⟩
    obtain ⟨hq, hlt⟩ := (trace_reads wm refusal trace a).mp ha
    exact ⟨a, hq, hlt, by simpa [EvalCtx.isDetached] using hp⟩
  · rintro ⟨a, hq, hlt, hd⟩
    exact ⟨a, (trace_reads wm refusal trace a).mpr ⟨hq, hlt⟩, by simpa [EvalCtx.isDetached] using hd⟩

/-- **AN ADMITTED READER DETACHES NO RECORDED READ.** -/
theorem trace_dependsFor_false (wm : Nat) (refusal : Error) (trace : List Nat) (ctx : EvalCtx)
    (h : (traceRecord wm refusal trace).dependsFor ctx.detachedBefore ctx.detachedOwners = false)
    (a : Nat) (hq : a ∈ trace) (hlt : a < wm) : ctx.isDetached a = false := by
  cases hd : ctx.isDetached a with
  | false => rfl
  | true =>
    have := (trace_dependsFor wm refusal trace ctx).mpr ⟨a, hq, hlt, hd⟩
    rw [this] at h
    cases h

/-- The judgment refuses no reader the watermark's test admits: a refused reader's watermark lies above a
    read of the trace. -/
theorem trace_dependsFor_dependsBelow (wm : Nat) (refusal : Error) (trace : List Nat) (ctx : EvalCtx)
    (h : (traceRecord wm refusal trace).dependsFor ctx.detachedBefore ctx.detachedOwners = true) :
    (traceRecord wm refusal trace).dependsBelow ctx.detachedBefore = true := by
  obtain ⟨a, hq, hlt, hd⟩ := (trace_dependsFor wm refusal trace ctx).mp h
  have hw : a < ctx.detachedBefore := by
    have := hd
    simp only [EvalCtx.isDetached, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  rw [trace_dependsBelow, List.any_eq_true]
  exact ⟨a, hq, by simp [hlt, hw]⟩

/-! ## 2. Own work is no input -/

/-- A read through an activation the cell's own computation recorded — one not below the cell's
    watermark — is noted on no record: neither the cell's nor any it forwards to. -/
theorem noteForwarded_own (fuel address activation : Nat) (records : List (Nat × CellInputs))
    (record : CellInputs) (hr : cellInputsAt? address records = some record)
    (hown : record.watermark ≤ activation) :
    noteForwarded fuel address activation records = records := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [noteForwarded, hr, show ¬ activation < record.watermark from by omega, ↓reduceIte]

/-- **OWN WORK IS NO INPUT.** A read inside the computation of the cell at `address` through an
    activation that computation recorded itself changes no input record. -/
theorem noteCellInputsAt_own (address activation : Nat) (records : List (Nat × CellInputs))
    (record : CellInputs) (hr : cellInputsAt? address records = some record)
    (hown : record.watermark ≤ activation) :
    noteCellInputsAt address activation records = records :=
  noteForwarded_own _ address activation records record hr hown

theorem lateRefusedFrom_own (fuel address activation : Nat) (records : List (Nat × CellInputs))
    (record : CellInputs) (hr : cellInputsAt? address records = some record)
    (hown : record.watermark ≤ activation) :
    lateRefusedFrom fuel address activation records = false := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [lateRefusedFrom, hr]
    have : decide (activation < record.watermark) = false := by simp; omega
    rw [this]
    rfl

/-- **OWN WORK IS NEVER REFUSED.** Whatever reader was admitted to the cell or to a cell that reused
    it, and whatever is served, a read through an activation the cell's own computation recorded is
    not refused: it is an input of no cell. -/
theorem lateRefused_own (inputs : CellRecords) (address activation : Nat) (record : CellInputs)
    (hr : cellInputsAt? address inputs.records = some record) (hown : record.watermark ≤ activation) :
    inputs.lateRefused address activation = false := by
  unfold CellRecords.lateRefused
  rw [lateRefusedFrom_own _ address activation inputs.records record hr hown]
  simp

/-! ## 3. The demand decides -/

/-- **NOTHING IS REFUSED WHILE NOTHING DETACHED IS SERVED.** -/
theorem lateRefused_unserved (inputs : CellRecords) (address activation : Nat)
    (h : inputs.serving = []) : inputs.lateRefused address activation = false := by
  simp [CellRecords.lateRefused, h]

/-- A read through an activation the served evaluation does not detach is not refused. -/
theorem lateRefused_attached (inputs : CellRecords) (address activation : Nat)
    (h : inputs.serving.contains activation = false) : inputs.lateRefused address activation = false := by
  unfold CellRecords.lateRefused
  rw [h]
  rfl

theorem noteCellInput_unmarked (ctx : EvalCtx) (activation : Nat) (refusal : Error) (s : EvalState)
    (h : ctx.inputRecord = none) :
    (noteCellInput ctx activation refusal).runState s = (.ok (), s) := by
  rw [noteCellInput_run, EvalState.lateRefusedFor_unmarked s ctx activation h,
    EvalState.noteInput_unmarked s ctx activation h]
  rfl

/-- **THE DEMAND DECIDES.** While no detached evaluation is served, an input read is never refused,
    whichever readers the cell admitted before: it is recorded, and the input records alone change.
    So a read an attached reader demands — a position of a lazy list a detached reader counted, read
    by the list's own row afterwards — uses the inputs of its own level. -/
theorem noteCellInput_unserved (ctx : EvalCtx) (activation : Nat) (refusal : Error) (s : EvalState)
    (h : s.cellInputs.serving = []) :
    (noteCellInput ctx activation refusal).runState s = (.ok (), s.noteInput ctx activation) :=
  noteCellInput_run_of_admitted ctx activation refusal s
    (EvalState.lateRefusedFor_unserved s ctx activation h)

/-! ## 4. Serving -/

/-- Two computations with the same run from every state are equal. -/
theorem evalM_ext {α : Type} {m n : EvalM α} (h : ∀ s, m.runState s = n.runState s) : m = n := by
  cases m with
  | mk r =>
    cases n with
    | mk r' =>
      congr 1
      funext s
      exact h s

/-- An owner set the records already serve runs the evaluation itself. -/
theorem servingDetached_served {α : Type} (owners : List Nat) (m : EvalM α) (s : EvalState)
    (h : owners.all s.cellInputs.serving.contains = true) :
    (servingDetached owners m).runState s = m.runState s := by
  simp only [servingDetached_runState, h, ↓reduceIte]

/-- At the empty owner set serving is the evaluation, as a computation. -/
theorem servingDetached_default {α : Type} (m : EvalM α) : servingDetached [] m = m :=
  evalM_ext (fun s => servingDetached_served [] m s rfl)

/-- Additional detached owners are served for the evaluation and RESTORED when it completes, whatever its
    outcome: the evaluation runs from the state with the served owner set extended, and the reuse
    leaves the state the evaluation left with the entry owner set back. -/
theorem servingDetached_raised {α : Type} (owners : List Nat) (m : EvalM α) (s t : EvalState)
    (o : Except Error α) (h : owners.all s.cellInputs.serving.contains = false)
    (hm : m.runState { s with cellInputs := { s.cellInputs with serving := owners ++ s.cellInputs.serving } } = (o, t))
    (hc : o.isIncomplete = false) :
    (servingDetached owners m).runState s =
      (o, { t with cellInputs := { t.cellInputs with serving := s.cellInputs.serving } }) := by
  simp only [servingDetached_runState, h, Bool.false_eq_true, ↓reduceIte, hm, hc]

/-! ## 5. The reuse -/

/-- The judgment is the admission step over the reader's watermark and input record. -/
theorem judge_run (cell : Nat) (ctx : EvalCtx) (s : EvalState) :
    (judgeRetainedCellReuse cell ctx).runState s =
      match s.cellInputs.admit cell ctx.detachedBefore ctx.detachedOwners ctx.inputRecord with
      | .error refusal => (.error refusal, s)
      | .ok (_, inputs) => (.ok (), { s with cellInputs := inputs }) := by
  unfold judgeRetainedCellReuse
  rw [cellInputsStep_run]
  cases s.cellInputs.admit cell ctx.detachedBefore ctx.detachedOwners ctx.inputRecord <;> rfl

/-- The admission of a reader at the default watermark outside every retained cell's computation
    changes no record. -/
theorem CellInputs.admit_default (record : CellInputs) (address : Nat) : record.admit address [] none = record := by
  cases record
  simp [CellInputs.admit]

theorem admitReaderAt_default (address : Nat) (records : List (Nat × CellInputs)) :
    admitReaderAt address [] none records = records := by
  induction records with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨c, r⟩ := head
    simp only [admitReaderAt]
    split
    · rw [CellInputs.admit_default]
    · rw [ih]

/-- A quiet reader — the default watermark, outside every retained cell's computation — is admitted
    to every cell, and the input records are unchanged. -/
theorem admit_default (inputs : CellRecords) (cell : Nat) (owners : List Nat) :
    inputs.admit cell 0 owners none = .ok ((), inputs) := by
  unfold CellRecords.admit
  cases cellInputsAt? cell inputs.records with
  | none => rfl
  | some record =>
    simp only [dependsFor_default, Bool.false_eq_true, ↓reduceIte, show owners.filter (· < 0) = [] by simp, admitReaderAt_default]

theorem judge_quiet (cell : Nat) (ctx : EvalCtx) (s : EvalState)
    (hw : ctx.detachedBefore = 0) (hu : ctx.inputRecord = none) :
    (judgeRetainedCellReuse cell ctx).runState s = (.ok (), s) := by
  rw [judge_run, hw, hu, admit_default]

/-- **NEUTRALITY.** At the default watermark, outside every retained cell's computation, the reuse of
    a cell IS its channel: the same outcome in the same state, whatever the cell recorded. -/
theorem reuseRetainedCell_default {α : Type} (cell : Nat) (ctx : EvalCtx) (m : EvalM α) (s : EvalState)
    (hw : ctx.detachedBefore = 0) (hu : ctx.inputRecord = none) :
    (reuseRetainedCell cell ctx m).runState s = m.runState s := by
  unfold reuseRetainedCell
  rw [EvalM.bind_runState, judge_quiet cell ctx s hw hu, show ctx.servingOwners = [] by simp [EvalCtx.servingOwners, hw], servingDetached_default]

/-- **QUIET READERS.** For a reader at the default watermark outside every retained cell's computation
    the reuse of a cell IS its channel, as a computation. -/
theorem reuseRetainedCell_quiet {α : Type} (cell : Nat) (ctx : EvalCtx) (m : EvalM α)
    (hw : ctx.detachedBefore = 0) (hu : ctx.inputRecord = none) :
    reuseRetainedCell cell ctx m = m :=
  evalM_ext (fun s => reuseRetainedCell_default cell ctx m s hw hu)

/-- A cell without an input record — a parameter row's own cell — is never judged: its reuse is its
    channel, served. -/
theorem reuseRetainedCell_unrecorded {α : Type} (cell : Nat) (ctx : EvalCtx) (m : EvalM α) (s : EvalState)
    (hr : cellInputsAt? cell s.cellInputs.records = none) :
    (reuseRetainedCell cell ctx m).runState s = (servingDetached ctx.servingOwners m).runState s := by
  unfold reuseRetainedCell
  rw [EvalM.bind_runState, judge_run]
  unfold CellRecords.admit
  rw [hr]

/-- **REFUSAL BEFORE THE CHANNEL.** A reader that DETACHES an input the cell is KNOWN to have read
    (`CellInputs.dependsFor`, exact for the trace: `trace_dependsFor`) is refused with the cell's own
    refusal IN THE STATE THE REUSE STARTED FROM: the channel does not run — no demand, no effect, no
    resource use of the cell is spent on a reader that may not have it — whichever channel is requested
    and whatever it would answer. -/
theorem reuseRetainedCell_refused {α : Type} (cell : Nat) (ctx : EvalCtx) (m : EvalM α) (s : EvalState)
    (record : CellInputs)
    (hr : cellInputsAt? cell s.cellInputs.records = some record)
    (hrefused : record.dependsFor ctx.detachedBefore ctx.detachedOwners = true) :
    (reuseRetainedCell cell ctx m).runState s = (.error record.refusal, s) := by
  unfold reuseRetainedCell
  rw [EvalM.bind_runState, judge_run]
  unfold CellRecords.admit
  rw [hr]
  simp only [hrefused, ↓reduceIte]

/-- **SHARING.** A reader the judgment admits gets the channel — the same cell, so the same value and
    the same identity — run SERVING it from the state the reuse started from with the input records
    alone changed (the reader admitted; inside a retained cell's computation, the reused cell's
    recorded read taken into that cell's record). -/
theorem reuseRetainedCell_admitted {α : Type} (cell : Nat) (ctx : EvalCtx) (m : EvalM α) (s : EvalState)
    (inputs : CellRecords)
    (hadmit : s.cellInputs.admit cell ctx.detachedBefore ctx.detachedOwners ctx.inputRecord = .ok ((), inputs)) :
    (reuseRetainedCell cell ctx m).runState s =
      (servingDetached ctx.servingOwners m).runState { s with cellInputs := inputs } := by
  unfold reuseRetainedCell
  rw [EvalM.bind_runState, judge_run, hadmit]

/-- The judgment's two outcomes: a refusal in the state it started from, or the input records alone
    rewritten. -/
theorem judge_outcome (cell : Nat) (ctx : EvalCtx) (s : EvalState) :
    (∃ refusal, (judgeRetainedCellReuse cell ctx).runState s = (.error refusal, s)) ∨
      ∃ inputs, (judgeRetainedCellReuse cell ctx).runState s = (.ok (), { s with cellInputs := inputs }) := by
  unfold judgeRetainedCellReuse
  rcases cellInputsStep_outcome
      (fun inputs => inputs.admit cell ctx.detachedBefore ctx.detachedOwners ctx.inputRecord) s with ⟨e, he⟩ | ⟨_, inputs, hi⟩
  · exact .inl ⟨e, he⟩
  · exact .inr ⟨inputs, hi⟩

end KatLang.RetainedCellReuse
