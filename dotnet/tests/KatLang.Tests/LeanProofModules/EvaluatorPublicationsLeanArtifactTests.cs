using System.Text.RegularExpressions;

namespace KatLang.Tests.LeanProofModules;

/// <summary>
/// Generates and pins <c>lean/KatLangArityLaws/EvaluatorPublications.lean</c>: the publication discipline of
/// the evaluator's per-body proof family.
///
/// <para>The module is GENERATED text. Its per-body proofs are those of
/// <c>lean/KatLangArityLaws/EvaluatorMemoLinks.lean</c> — the <c>link_tac</c> procedure and its body lemmas —
/// re-instantiated for the PUBLICATION relation under a mechanical renaming (<see cref="Generate"/>). The
/// relation, its API lemmas, the one publishing writer (<c>NeedProjection.step</c>) and the whole-run tail are
/// written by hand HERE, in <see cref="Header"/>, <see cref="Step"/> and <see cref="Tail"/>.</para>
///
/// <para><b>Two inputs, one output.</b> A change to the copied part of <c>EvaluatorMemoLinks.lean</c> (the two
/// ranges <see cref="Generate"/> cuts by their anchors) changes this module too: this test then fails until the
/// module is regenerated. A change the renaming cannot follow stops the generator with the anchor or the
/// rewrite it could not apply; nothing is emitted from a source it does not recognize.</para>
///
/// <para>This generator replaces a Python script, and three hand-written fragment files beside it, that
/// existed only in an ignored scratch folder of one machine. On the day it was ported (2026-11-16) both
/// produced the tracked module byte for byte.</para>
///
/// Regenerate with:
///   $env:KATLANG_REGENERATE_EVALUATOR_PUBLICATIONS = "1"
///   dotnet test ./dotnet/tests/KatLang.Tests/KatLang.Tests.csproj --filter EvaluatorPublicationsLeanArtifact
/// That run writes the module and then fails by design (see <see cref="ArtifactRegeneration"/>); review the
/// diff, clear the flag, rerun, and run <c>lake build KatLangArityLaws</c>.
/// </summary>
public class EvaluatorPublicationsLeanArtifactTests
{
    internal const string ArtifactRelativePath = "lean/KatLangArityLaws/EvaluatorPublications.lean";

    /// <summary>The module whose per-body proofs are copied under the renaming.</summary>
    internal const string SourceRelativePath = "lean/KatLangArityLaws/EvaluatorMemoLinks.lean";

    [Fact]
    public void GeneratedLeanModule_IsItsGeneratorsOutput()
        => LeanProofModuleArtifact.VerifyOrRegenerate(
            RegenerationFlags.EvaluatorPublications, ArtifactRelativePath, GenerateArtifact());

    /// <summary>
    /// The generator recognizes its source or stops: a source without the four anchors yields no module, and a
    /// source in which a pinned rewrite applies a different number of times is refused by that rewrite.
    /// </summary>
    [Fact]
    public void AnUnrecognizedSource_IsRefused_NotRenamedBlindly()
    {
        var missingAnchor = Assert.Throws<InvalidOperationException>(() => Generate("theorem unrelated : True := trivial\n"));
        Assert.Contains(FirstRangeStart, missingAnchor.Message, StringComparison.Ordinal);

        // The tracked source with one of the two pinned allocation sites of the first copied range removed.
        const string Allocation = "exact LinkHeapKept.push _ _";
        var source = ReadSource();
        var firstRange = source.IndexOf("\n" + FirstRangeStart, StringComparison.Ordinal);
        Assert.True(firstRange >= 0);
        var allocation = source.IndexOf(Allocation, firstRange, StringComparison.Ordinal);
        Assert.True(allocation >= 0);
        var altered = source.Remove(allocation, Allocation.Length).Insert(allocation, "sorry");

        var refused = Assert.Throws<InvalidOperationException>(() => Generate(altered));
        Assert.Contains("Expected 2 occurrence(s)", refused.Message, StringComparison.Ordinal);
        Assert.Contains("exact PubHeapKept.push _ _", refused.Message, StringComparison.Ordinal);
    }

    /// <summary>The module's whole text, generated from the tracked source module.</summary>
    internal static string GenerateArtifact() => Generate(ReadSource());

    private static string ReadSource()
    {
        var path = Path.Combine(RepoRoot.Find(), SourceRelativePath);
        Assert.True(File.Exists(path), $"{SourceRelativePath}, the source of {ArtifactRelativePath}, is missing.");
        return File.ReadAllText(path);
    }

    // ── The generator ───────────────────────────────────────────────────────────────────────────

    // The copied text is two ranges of the source module, each from the line that starts with its first anchor
    // up to (not including) the line that starts with its second.
    private const string FirstRangeStart = "theorem linkDisc_of_needs";
    private const string FirstRangeEnd = "/-! ## The three guarded writers -/";
    private const string SecondRangeStart = "/-- **Callee establishment keeps entry facts.**";
    private const string SecondRangeEnd = "/-! ## Whole-run link discipline of the production evaluator -/";

    /// <summary>
    /// <see cref="Header"/>, the first copied range, <see cref="Step"/>, the second copied range,
    /// <see cref="Tail"/>. <paramref name="memoLinksSource"/> is the text of <see cref="SourceRelativePath"/>.
    /// </summary>
    internal static string Generate(string memoLinksSource)
    {
        var lines = memoLinksSource.ReplaceLineEndings("\n").Split('\n');

        var firstStart = FindLine(lines, FirstRangeStart);
        var firstEnd = FindLine(lines, FirstRangeEnd);
        var secondStart = FindLine(lines, SecondRangeStart);
        var secondEnd = FindLine(lines, SecondRangeEnd);
        if (!(firstStart < firstEnd && firstEnd <= secondStart && secondStart < secondEnd))
        {
            throw new InvalidOperationException(
                $"The anchors of {SourceRelativePath} are out of order (lines {firstStart + 1}, {firstEnd + 1}, {secondStart + 1}, {secondEnd + 1}).");
        }

        var first = Rename(string.Join("\n", lines[firstStart..firstEnd]));
        var second = Rename(string.Join("\n", lines[secondStart..secondEnd]));

        // A pushed cell publishes nothing: every allocation site pushes a cell with the default CALLABLE.
        const string Push = "exact PubHeapKept.push _ _";
        const string PushPublishingNothing = "exact PubHeapKept.push _ _ (fun g h => by cases h)";
        first = LeanProofModuleArtifact.ReplaceExactly(first, Push, PushPublishingNothing, expectedCount: 2);
        second = LeanProofModuleArtifact.ReplaceExactly(second, Push, PushPublishingNothing, expectedCount: 1);

        // The two anchored record writes (callee, receiver) keep the CALLABLE field of the cell they rewrite.
        const string KeepsCallable = "(fun c1 _ => pubKept_of_callable _ _ rfl)";
        second = LeanProofModuleArtifact.ReplaceExactly(second, CalleeRecordWrite, KeepsCallable, expectedCount: 1);
        second = LeanProofModuleArtifact.ReplaceExactly(second, ReceiverRecordWrite, KeepsCallable, expectedCount: 1);

        // Every body (and every local helper over `rec`) also carries the result contract of the projection
        // callback, which the publishing writer needs.
        first = CarryResultContract(first);
        second = CarryResultContract(second);

        // The procedure closes the result-contract premise of the publishing writer from `hres`.
        const string RecursiveAlternative = "  | pub_rec\n";
        second = LeanProofModuleArtifact.ReplaceExactly(
            second, RecursiveAlternative, "  | pub_res\n" + RecursiveAlternative, expectedCount: 2);

        return (Header + first + "\n" + Step + second + "\n" + Tail).ReplaceLineEndings("\n");
    }

    /// <summary>The first line that starts with <paramref name="anchor"/>.</summary>
    private static int FindLine(string[] lines, string anchor)
    {
        var index = Array.FindIndex(lines, line => line.StartsWith(anchor, StringComparison.Ordinal));
        return index >= 0
            ? index
            : throw new InvalidOperationException($"The anchor is not in {SourceRelativePath}: {anchor}");
    }

    // "Not preceded / not followed by a word character", spelled out: a letter, any numeric character (subscript
    // digits included) or an underscore.
    private const string NotAfterWord = @"(?<![\p{L}\p{N}_])";
    private const string NotBeforeWord = @"(?![\p{L}\p{N}_])";

    private static readonly Regex LinkPrefix = new(NotAfterWord + "link_", RegexOptions.CultureInvariant);
    private static readonly Regex RecursiveApplication = new(NotAfterWord + "rec hrec" + NotBeforeWord, RegexOptions.CultureInvariant);

    /// <summary>The link relation's names to the publication relation's, most specific first (the order matters).</summary>
    private static string Rename(string text)
    {
        text = text.Replace("KatLang.MemoLinks", "KatLang.Publications", StringComparison.Ordinal);
        text = text.Replace("LinkHeapKept", "PubHeapKept", StringComparison.Ordinal);
        text = text.Replace("linkKept_of_same", "pubKept_of_same", StringComparison.Ordinal);
        text = text.Replace("LinkKept", "PubKept", StringComparison.Ordinal);
        text = text.Replace("CapsLink", "CapsPub", StringComparison.Ordinal);
        text = text.Replace("LinkDisc", "PubDisc", StringComparison.Ordinal);
        text = text.Replace("LinkAt", "PubAt", StringComparison.Ordinal);
        text = text.Replace("linkAt_", "pubAt_", StringComparison.Ordinal);
        text = text.Replace("linkDisc", "pubDisc", StringComparison.Ordinal);
        return LinkPrefix.Replace(text, "pub_");
    }

    private static string CarryResultContract(string text)
    {
        text = text.Replace(
            "(hrec : ∀ c, PubDisc (rec c))", "(hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec)", StringComparison.Ordinal);
        text = text.Replace("include hrec", "include hrec hres", StringComparison.Ordinal);
        return RecursiveApplication.Replace(text, "rec hrec hres");
    }

    // ── The module text ─────────────────────────────────────────────────────────────────────────
    //
    // Lean text, verbatim.

    /// <summary>The callee record write as the renamed source states it; the publication relation closes it by <c>pubKept_of_callable</c>.</summary>
    private const string CalleeRecordWrite = """
        (fun c0 c1 h0 kk => by
                        rw [hc] at h0; cases h0
                        exact ⟨kk.callable, kk.projecting, fun y h => (by rw [hcal] at h; cases h), kk.receiver⟩)
        """;

    /// <summary>The receiver record write as the renamed source states it; the publication relation closes it by <c>pubKept_of_callable</c>.</summary>
    private const string ReceiverRecordWrite = """
        (fun c0 c1 h0 kk => by
                      rw [hc] at h0; cases h0
                      exact ⟨kk.callable, kk.projecting, kk.callee, fun y h => (by rw [hrec] at h; cases h)⟩)
        """;

    /// <summary>
    /// Imports, the module documentation, the publication relation and its API lemmas. Hand-written; the first
    /// copied range follows it.
    /// </summary>
    private const string Header = """
        import Lean
        import KatLangArityLaws.EvaluatorMemoLinks
        import KatLangArityLaws.PlanRouteBridge

        open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.AlgorithmProjectionLaws

        /-!
        # E-18 step 1 (M1): every CALLABLE identity production PUBLISHES is accounted for

        `MemoLinks.LinkHeapKept` says what a production operation KEEPS of the CALLABLE memos it found. It
        says nothing of the memos the operation WRITES: a state could hold any algorithm as a completed
        CALLABLE (`StoredCallableNormal.storedCallableNeedNotBeNormal`), and nothing so far excluded that a
        production projection publishes a transparent reference. This module proves the companion
        relation, in the same per-body style:

        * `Accounted h g`: the identity `g` is STRUCTURE-NORMAL (`PlanRouteBridge.structureNormal`: no
          transparent reference), or it is a completed CALLABLE identity of some cell of the heap `h`;
        * `PubHeapKept h h'`: **every identity published in `h'` is accounted for in `h`** — it is
          structure-normal, or it was already a published identity of `h` (at any address);
        * `PubDisc m`: `m` relates EVERY entry heap to its exit heap by `PubHeapKept`, whatever its outcome.

        The relation is UNCONDITIONAL — no premise on the entry heap — which is what makes it a whole-run
        relation: an arbitrary heap may hold a reference as a completed CALLABLE, and a parameter that
        forwards that cell publishes the same reference again; that identity is accounted for by the cell
        it came from. On a heap whose published identities are all structure-normal (`NormalHeap`, the
        empty heap first) the relation leaves only the first disjunct (`PubHeapKept.normal`).

        The CALLABLE field has ONE writer, `NeedProjection.step`, which publishes its callback's outcome.
        `pubDisc_projectionStep` therefore needs, besides the callback's own `PubDisc`, a RESULT contract:
        an identity the callback returns is accounted for in the callback's exit heap (`hres`). Every other
        writer keeps the field of the cell it rewrites (`pubKept_of_same`) or pushes a cell with the
        default CALLABLE (`PubHeapKept.push`). `evalStep_pubDisc` is the per-body step: every evaluator
        body keeps the relation whenever its recursive answer does AND the answer's written-projection
        callback satisfies the result contract (`ResSusp`). The result contracts themselves, the transfer
        through the fuel core and production, and the consequences for `structureNormal` are in
        `PublishedCallableNormal`.

        GENERATED text, never edited by hand: from `EvaluatorMemoLinks.lean` (the `link_tac` procedure and
        its body lemmas under a renaming) by
        `dotnet/tests/KatLang.Tests/LeanProofModules/EvaluatorPublicationsLeanArtifactTests.cs`; the relation, its
        API lemmas and `pubDisc_projectionStep` are hand-written in that generator's `Header`, `Step` and
        `Tail` texts, and are edited there. After a change to the generator, or to the copied part of
        `EvaluatorMemoLinks.lean`, regenerate from the repo root with
          $env:KATLANG_REGENERATE_EVALUATOR_PUBLICATIONS = "1"
          dotnet test ./dotnet/tests/KatLang.Tests/KatLang.Tests.csproj --filter EvaluatorPublicationsLeanArtifact
        (that run writes this file and then fails by design), then run `lake build KatLangArityLaws`: the
        generator writes the text, and only Lean checks the proofs.

        Not claimed: anything about a cell's VALUE, addresses, activations, or C#.
        -/

        -- Every body lemma carries the result contract `hres`; only the bodies that reach the publishing
        -- writer use it.
        set_option linter.unusedVariables false
        set_option linter.unusedSectionVars false

        namespace KatLang.Publications

        open KatLang.PlanRouteBridge (structureNormal)

        /-! ## The relation -/

        /-- **Accounted for in `h`.** The identity `g` is structure-normal, or it is the completed
            CALLABLE identity of some cell of `h`. -/
        def Accounted (h : Array NeedCell) (g : Algorithm) : Prop :=
          structureNormal g = true ∨ ∃ (b : Nat) (c : NeedCell), h[b]? = some c ∧ c.callable = .projected (.ok (some g))

        theorem Accounted.normal {h : Array NeedCell} {g : Algorithm} (hg : structureNormal g = true) :
            Accounted h g := .inl hg

        theorem Accounted.published {h : Array NeedCell} {g : Algorithm} {b : Nat} {c : NeedCell}
            (hc : h[b]? = some c) (hg : c.callable = .projected (.ok (some g))) : Accounted h g :=
          .inr ⟨b, c, hc, hg⟩

        /-- An optional identity, accounted for when present. -/
        def OptAccounted (h : Array NeedCell) (o : Option Algorithm) : Prop := ∀ g, o = some g → Accounted h g

        theorem OptAccounted.none {h : Array NeedCell} : OptAccounted h none := fun _ e => by cases e

        theorem OptAccounted.some {h : Array NeedCell} {g : Algorithm} (hg : Accounted h g) :
            OptAccounted h (some g) := fun _ e => by cases e; exact hg

        /-- The cell relation of a write that publishes NOTHING at the cell it rewrites: an identity the
            cell holds afterwards, it held before. -/
        def PubKept (c c' : NeedCell) : Prop :=
          ∀ g, c'.callable = .projected (.ok (some g)) → c.callable = .projected (.ok (some g))

        theorem PubKept.refl (c : NeedCell) : PubKept c c := fun _ h => h

        theorem PubKept.trans {c d e : NeedCell} (h1 : PubKept c d) (h2 : PubKept d e) : PubKept c e :=
          fun g h => h1 g (h2 g h)

        /-- A write that leaves the CALLABLE field alone publishes nothing. (The two further premises keep
            the statement interchangeable with `MemoLinks.linkKept_of_same`.) -/
        theorem pubKept_of_same (c c' : NeedCell) (hc : c'.callable = c.callable)
            (_he : c'.callee = c.callee) (_hr : c'.receiver = c.receiver) : PubKept c c' :=
          fun _ h => hc ▸ h

        theorem pubKept_of_callable (c c' : NeedCell) (hc : c'.callable = c.callable) : PubKept c c' :=
          fun _ h => hc ▸ h

        /-- **THE PUBLICATION RELATION.** Every identity published in `h'` is accounted for in `h`. -/
        def PubHeapKept (h h' : Array NeedCell) : Prop :=
          ∀ (a : Nat) (c' : NeedCell) (g : Algorithm), h'[a]? = some c' →
            c'.callable = .projected (.ok (some g)) → Accounted h g

        theorem PubHeapKept.refl (h : Array NeedCell) : PubHeapKept h h :=
          fun _ _ _ hc hg => Accounted.published hc hg

        /-- An identity accounted for in the later heap is accounted for in the earlier one. -/
        theorem Accounted.back {h h' : Array NeedCell} (k : PubHeapKept h h') {g : Algorithm}
            (hg : Accounted h' g) : Accounted h g := by
          rcases hg with hn | ⟨b, c, hc, hp⟩
          · exact .inl hn
          · exact k b c g hc hp

        theorem OptAccounted.back {h h' : Array NeedCell} (k : PubHeapKept h h') {o : Option Algorithm}
            (ho : OptAccounted h' o) : OptAccounted h o := fun g e => (ho g e).back k

        theorem PubHeapKept.trans {h1 h2 h3 : Array NeedCell} (k1 : PubHeapKept h1 h2) (k2 : PubHeapKept h2 h3) :
            PubHeapKept h1 h3 := fun a c g hc hg => (k2 a c g hc hg).back k1

        /-- Heap extension by a cell that holds no completed identity publishes nothing. -/
        theorem PubHeapKept.push (h : Array NeedCell) (c : NeedCell)
            (hc : ∀ g, c.callable = .projected (.ok (some g)) → False) : PubHeapKept h (h.push c) := by
          intro a d g hd hg
          rw [Array.getElem?_push] at hd
          split at hd
          · cases hd
            exact absurd hg (hc g)
          · exact Accounted.published hd hg

        /-- A write at `a` that publishes nothing at the cell it rewrites. -/
        theorem PubHeapKept.modify (h : Array NeedCell) (a : Nat) (f : NeedCell → NeedCell)
            (hf : ∀ c, h[a]? = some c → PubKept c (f c)) : PubHeapKept h (h.modify a f) := by
          intro b c' g hc hg
          rw [modify_get] at hc
          by_cases hab : a = b
          · subst hab
            rw [ite_eq_left rfl] at hc
            cases hcur : h[a]? with
            | none => rw [hcur] at hc; cases hc
            | some c =>
              rw [hcur] at hc
              cases hc
              exact Accounted.published hcur (hf c hcur g hg)
          · rw [ite_eq_right hab] at hc
            exact Accounted.published hc hg

        /-- After `h0 ↦ h1`, a write at `a` that publishes nothing at the cell CURRENTLY there. -/
        theorem PubHeapKept.modify_anchor {h0 h1 : Array NeedCell} (k : PubHeapKept h0 h1) (a : Nat)
            (g : NeedCell → NeedCell) (hg : ∀ c1, h1[a]? = some c1 → PubKept c1 (g c1)) :
            PubHeapKept h0 (h1.modify a g) :=
          k.trans (PubHeapKept.modify h1 a g hg)

        /-- A whole-cell write of the cell CURRENTLY at `a` that publishes nothing there. -/
        theorem PubHeapKept.set_bang (h : Array NeedCell) (a : Nat) (c c' : NeedCell) (hc : h[a]? = some c)
            (hk : PubKept c c') : PubHeapKept h (h.set! a c') := by
          intro b d g hd hg
          have ha : a < h.size := KatLang.MemoLinks.lt_of_get hc
          by_cases hab : a = b
          · subst hab
            have hd' : (h.set! a c')[a]? = some c' := by simp [Array.set!, ha]
            rw [hd'] at hd
            cases hd
            exact Accounted.published hc (hk g hg)
          · have hd' : (h.set! a c')[b]? = h[b]? := by simp [Array.set!, hab]
            rw [hd'] at hd
            exact Accounted.published hd hg

        /-- `m` publishes only accounted identities, over EVERY entry state, whatever its outcome. -/
        def PubDisc {α : Type} (m : EvalM α) : Prop :=
          ∀ s, PubHeapKept s.needs (m.runState s).2.needs

        /-- **The result contract of the written-projection callback** of an answer `rec`: an identity the
            callback of `NeedProjection.step` returns is accounted for in the heap the callback leaves. -/
        def ResSusp (rec : EvalRec) : Prop :=
          ∀ (a : Nat) (x : NeedSuspension) (s : EvalState) (g : Algorithm) (t : EvalState),
            (NeedProjection.suspended (rec.projectNeedWrittenAt a) x).runState s = (.ok (some g), t) →
            Accounted t.needs g

        set_option hygiene false in
        /-- Closes the result-contract premise of the publishing writer from the local `hres`. -/
        macro "pub_res" : tactic => `(tactic| exact hres _)


        """;

    /// <summary>
    /// The one publishing writer, <c>NeedProjection.step</c>, with its result contract. Hand-written; it stands
    /// between the two copied ranges.
    /// </summary>
    private const string Step = """
        /-! ## The publishing writer, and the two record writers -/

        /-- **CALLABLE publication is accounted for.** A completed outcome is returned with no write; an
            active projection is a cycle with no write; an UNPROJECTED entry cell is marked `projecting`
            (no identity) and then holds the callback's outcome — an identity that the callback's result
            contract accounts for in the callback's exit heap (`hres`), hence in the entry heap. -/
        theorem pubDisc_projectionStep (project : NeedSuspension → EvalM (Option Algorithm))
            (hp : ∀ x, PubDisc (project x))
            (hres : ∀ x s g t, (project x).runState s = (.ok (some g), t) → Accounted t.needs g)
            (a : Nat) : PubDisc (NeedProjection.step project a) := by
          intro s
          cases hc : s.needs[a]? with
          | none =>
            rw [KatLang.NeedControl.Projection.invalid_address project a s hc]; exact PubHeapKept.refl _
          | some cell =>
            cases hs : cell.callable with
            | projected o =>
              rw [KatLang.NeedControl.Projection.projected_sticky project a s cell o hc hs]
              exact PubHeapKept.refl _
            | projecting =>
              rw [KatLang.NeedControl.Projection.projecting_reentry_cycle project a s cell hc hs]
              exact PubHeapKept.refl _
            | unprojected =>
              have k1 : PubHeapKept s.needs (KatLang.NeedControl.Projection.setCallable a .projecting s).needs :=
                PubHeapKept.modify _ a _ (fun c _ g h => by cases h)
              have k2 := hp cell.suspension (KatLang.NeedControl.Projection.setCallable a .projecting s)
              generalize hr : (project cell.suspension).runState
                (KatLang.NeedControl.Projection.setCallable a .projecting s) = r at k2
              rcases r with ⟨outcome, t⟩
              have k12 := k1.trans k2
              cases hinc : outcome.isIncomplete with
              | false =>
                rw [KatLang.NeedControl.Projection.unprojected_publishes project a s t cell outcome hc hs hr hinc]
                show PubHeapKept s.needs (t.needs.modify a (fun c => { c with callable := .projected outcome }))
                intro b c' g hb hg
                rw [modify_get] at hb
                by_cases hab : a = b
                · subst hab
                  rw [ite_eq_left rfl] at hb
                  cases hcur : t.needs[a]? with
                  | none => rw [hcur] at hb; cases hb
                  | some cur =>
                    rw [hcur] at hb
                    cases hb
                    have ho : outcome = .ok (some g) := by
                      have h' : NeedCallableState.projected outcome = .projected (.ok (some g)) := hg
                      cases h'
                      rfl
                    subst ho
                    exact (hres cell.suspension _ g t hr).back k12
                · rw [ite_eq_right hab] at hb
                  exact k12 b c' g hb hg
              | true =>
                have hrun : (NeedProjection.step project a).runState s = (.error .fuelExhausted, t) := by
                  simp only [NeedProjection.step, bind_run, get_run, hc, hs, EvalM.modify_runState]
                  simp only [KatLang.NeedControl.Projection.setCallable] at hr
                  rw [evalAttempt_run, hr]
                  simp only [hinc, ite_true]
                rw [hrun]; exact k12


        """;

    /// <summary>The whole-run publication discipline of the production evaluator. Hand-written; it closes the module.</summary>
    private const string Tail = """
        /-! ## Normal heaps -/

        /-- **A normal heap**: every completed CALLABLE identity it holds is structure-normal. -/
        def NormalHeap (h : Array NeedCell) : Prop :=
          ∀ (a : Nat) (c : NeedCell) (g : Algorithm), h[a]? = some c →
            c.callable = .projected (.ok (some g)) → structureNormal g = true

        theorem NormalHeap.empty : NormalHeap #[] := fun _ _ _ h => by simp at h

        /-- On a normal heap, accounted for IS structure-normal. -/
        theorem NormalHeap.accounted {h : Array NeedCell} (hn : NormalHeap h) {g : Algorithm}
            (hg : Accounted h g) : structureNormal g = true := by
          rcases hg with hg | ⟨b, c, hc, hp⟩
          · exact hg
          · exact hn b c g hc hp

        /-- **The publication relation keeps a heap normal.** -/
        theorem PubHeapKept.normal {h h' : Array NeedCell} (k : PubHeapKept h h') (hn : NormalHeap h) :
            NormalHeap h' := fun a c g hc hg => hn.accounted (k a c g hc hg)

        /-- A publishing-disciplined computation keeps a normal heap normal, whatever its outcome. -/
        theorem PubDisc.normal {α : Type} {m : EvalM α} (hm : PubDisc m) (s : EvalState)
            (hn : NormalHeap s.needs) : NormalHeap (m.runState s).2.needs := (hm s).normal hn

        end KatLang.Publications

        """;
}
