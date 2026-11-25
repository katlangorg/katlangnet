using System.Collections.Frozen;
using System.Text;

namespace KatLang.Tests;

/// <summary>
/// Finding #4 of the 2026-11-21 adversarial performance and reliability investigation (baseline <c>8947d21e</c>).
/// FE-1 made a promotion only CAPTURE its suggestion context, so a valid program compares no candidate — but a FAILED
/// run still evaluated every captured note when its message rendered. Lifting gathers the promotions of every callee
/// into one signature, so one <see cref="EvalError.UnresolvedImplicitParams"/> or <see cref="EvalError.ArityMismatch"/>
/// message compared notes × up to 512 candidates × a 64 × 64 distance table each (2,560 notes over 400 candidates:
/// 11.5 s of rendering after a 0.6 s front end, Release), in the public <see cref="KatLangError.FromEvalError"/> and on
/// the run's projection path, which never observed the run's evaluation token. The repair, pinned here:
/// <list type="number">
/// <item>the distance kernel computes only the band of the accepted distance and stops once no alignment can stay
/// within it — equal to the retained full reference table, capped, at every accepted threshold;</item>
/// <item>the selection policies (thresholds, case respelling, the member initial guard, tie refusal) are the
/// pre-change policy exactly, and the member policy cases each member once per surface;</item>
/// <item>a message reads suggestions under ONE deterministic allowance (<see cref="MessageSuggestionAllowance"/>):
/// first fit in note order by captured candidate count, charged whether or not a suggestion was already computed;
/// a note past it renders as a note without a suggestion under the existing contract;</item>
/// <item>the run's projection observes its evaluation token before each charged suggestion, so cancellation escapes
/// with that token.</item>
/// </list>
/// Tests assert counters, rendered text and token identity — never elapsed time. C#-only diagnostics: Lean models no
/// suggestion, rendering or cancellation, so no Lean case corresponds.
/// </summary>
public sealed class SuggestionRenderingBoundTests
{
    // ── Fixtures ─────────────────────────────────────────────────────────────────────────────────

    /// <summary><c>Value000 = 0</c> … : the candidates every note is a near miss of.</summary>
    private static string Candidates(int count)
        => string.Concat(Enumerable.Range(0, count).Select(static i => $"Value{i:D3} = {i}\n"));

    /// <summary>A one-transposition typo of <c>Value{index}</c> (distance 1, every other candidate at least 2).</summary>
    private static string Typo(int index) => $"Vaule{index:D3}";

    private static string Fix(string typo) => "Value" + typo[5..];

    /// <summary>
    /// <paramref name="bodies"/> helper properties, each promoting <paramref name="namesPerBody"/> distinct names
    /// (<paramref name="name"/> of the running index), so lifting gathers them all into one signature.
    /// </summary>
    private static string Helpers(int bodies, int namesPerBody, Func<int, string> name)
        => string.Concat(Enumerable.Range(0, bodies).Select(body =>
            $"H{body} = {string.Join(" + ", Enumerable.Range(body * namesPerBody, namesPerBody).Select(name))}\n"));

    private static string HelperSum(int bodies) => string.Join(" + ", Enumerable.Range(0, bodies).Select(static body => $"H{body}"));

    /// <summary>The root lifts every helper's names: <see cref="EvalError.UnresolvedImplicitParams"/>.</summary>
    private static string RootProgram(int bodies, int namesPerBody, int candidates, Func<int, string>? name = null)
        => Candidates(candidates) + Helpers(bodies, namesPerBody, name ?? Typo) + HelperSum(bodies) + "\n";

    /// <summary><c>G</c> lifts every helper's names; <c>G(1)</c> is the arity mismatch with a rendered signature.</summary>
    private static string CallProgram(int bodies, int namesPerBody, int candidates, string prefix = "")
        => Candidates(candidates) + Helpers(bodies, namesPerBody, Typo) + $"G = {HelperSum(bodies)}\n{prefix}G(1)\n";

    /// <summary>A sole root row <c>G</c>: the signatureless property-form arity mismatch.</summary>
    private static string PropertyProgram(int bodies, int namesPerBody, int candidates)
        => Candidates(candidates) + Helpers(bodies, namesPerBody, Typo) + $"G = {HelperSum(bodies)}\nG\n";

    private sealed record Failure(
        FrontEndTraversalObservations Observations,
        EvalError Error,
        EvalError Terminal,
        IReadOnlyList<ImplicitParameterProvenance> Notes);

    private static EvalError TerminalOf(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    /// <summary>Compiles <paramref name="source"/> cleanly under an observer and evaluates it to its failure.</summary>
    private static Failure Fail(string source)
    {
        var observations = new FrontEndTraversalObservations();
        var compiled = FrontEndPipeline.Process(source, options: null, comparisonObservations: null, observations);
        Assert.False(compiled.HasErrors, string.Join("\n", compiled.Diagnostics.Select(static d => d.Message)));
        var result = Evaluator.Run(new Expr.AlgorithmExpr(compiled.ElaboratedRoot));
        Assert.True(result.IsError);
        var terminal = TerminalOf(result.Error);
        var notes = terminal switch
        {
            EvalError.UnresolvedImplicitParams unresolved => unresolved.InferredImplicitParameters,
            EvalError.ArityMismatch arity => arity.InferredImplicitParameters,
            var other => throw new Xunit.Sdk.XunitException($"expected an arity/unresolved-implicit-params error, got {other.GetType().Name}"),
        };
        Assert.NotNull(notes);
        return new(observations, result.Error, terminal, notes);
    }

    /// <summary>The allowance's contract restated: first fit in note order by captured candidate count.</summary>
    private static HashSet<ImplicitParameterProvenance> Admitted(IReadOnlyList<ImplicitParameterProvenance> notes)
    {
        var remaining = NameSuggestions.MaxCandidatesPerMessage;
        var confirmationsLeft = NameSuggestions.MaxConfirmationsPerMessage;
        var admitted = new HashSet<ImplicitParameterProvenance>(ReferenceEqualityComparer.Instance);
        foreach (var note in notes)
        {
            if (note.CycleOrigin is not null || note.SuggestionCandidateCount == 0
                || note.SuggestionCandidateCount > remaining || note.SuggestionConfirmationCount > confirmationsLeft)
                continue;
            remaining -= note.SuggestionCandidateCount;
            confirmationsLeft -= note.SuggestionConfirmationCount;
            admitted.Add(note);
        }

        return admitted;
    }

    private static string[] SuggestionLines(string message)
        => message.Split('\n').Where(static line => line.StartsWith("Did you mean", StringComparison.Ordinal)).ToArray();

    private static string InferredAt(ImplicitParameterProvenance note)
    {
        var span = Assert.NotNull(note.Span);
        return $"An implicit parameter '{note.Name}' was inferred at [{span.Start.Line}:{span.Start.Column}].";
    }

    private static (long Candidates, long Cells) Work(FrontEndTraversalObservations observations)
        => (observations.SuggestionCandidatesExamined, observations.SuggestionDistanceCells);

    /// <summary>The work one rendering did: bounded by the allowance, exactly the admitted notes' candidates.</summary>
    private static void AssertBoundedWork(Failure failure, (long Candidates, long Cells) before, IReadOnlySet<ImplicitParameterProvenance> admitted)
    {
        var (candidates, cells) = Work(failure.Observations);
        var examined = candidates - before.Candidates;
        Assert.Equal(admitted.Sum(static note => (long)note.SuggestionCandidateCount), examined);
        Assert.InRange(examined, 1, NameSuggestions.MaxCandidatesPerMessage);
        Assert.InRange(cells - before.Cells, 1, examined * NameSuggestions.MaxDistanceCellsPerCandidate);
        Assert.All(failure.Notes, note => Assert.Equal(admitted.Contains(note), note.IsSuggestionEvaluated));
    }

    // ── 1. The kernel is the capped reference ────────────────────────────────────────────────────

    private static IEnumerable<string> AllStrings(string alphabet, int maxLength)
    {
        var level = new List<string> { string.Empty };
        for (var length = 0; length <= maxLength; length++)
        {
            foreach (var text in level)
                yield return text;
            level = [.. level.SelectMany(text => alphabet.Select(character => text + character))];
        }
    }

    private static string? KernelMismatch(string a, string b, int maxDistance)
    {
        var reference = NameSuggestions.OptimalStringAlignmentDistance(a, b);
        var bounded = NameSuggestions.BoundedOptimalStringAlignmentDistance(a, b, maxDistance, out var cells);
        if (bounded != Math.Min(reference, maxDistance + 1))
            return $"'{a}' / '{b}' at {maxDistance}: banded {bounded}, reference {reference}";
        return cells > a.Length * (2 * maxDistance + 1)
            ? $"'{a}' / '{b}' at {maxDistance}: {cells} cells exceed the band"
            : null;
    }

    /// <summary>
    /// Every pair of strings of up to five characters over <c>a</c>, <c>b</c>, <c>A</c> (transpositions, case-distinct
    /// units, every length difference), at every accepted threshold and one beyond: the banded kernel returns
    /// <c>min(reference, k + 1)</c> and computes at most one band per row.
    /// </summary>
    [Fact]
    public void BandedKernel_IsTheCappedReference_OnEveryShortPair()
    {
        var strings = AllStrings("abA", 5).ToArray();
        Assert.Equal(364, strings.Length);
        foreach (var a in strings)
        {
            foreach (var b in strings)
            {
                for (var maxDistance = 0; maxDistance <= NameSuggestions.MaxAcceptedDistance + 1; maxDistance++)
                {
                    if (KernelMismatch(a, b, maxDistance) is { } mismatch)
                        Assert.Fail(mismatch);
                }
            }
        }
    }

    private static string RandomName(Random random, int length, string alphabet)
        => string.Create(length, (random, alphabet), static (span, state) =>
        {
            for (var index = 0; index < span.Length; index++)
                span[index] = state.alphabet[state.random.Next(state.alphabet.Length)];
        });

    /// <summary>
    /// <paramref name="edits"/> random substitutions, insertions, deletions, adjacent transpositions and (optionally)
    /// case flips of <paramref name="text"/>, kept within <see cref="NameSuggestions.MaxNameLength"/>.
    /// </summary>
    private static string Mutate(Random random, string text, int edits, string alphabet, bool caseFlips = false)
    {
        var builder = new StringBuilder(text);
        for (var edit = 0; edit < edits; edit++)
        {
            var position = builder.Length == 0 ? 0 : random.Next(builder.Length);
            switch (random.Next(caseFlips ? 5 : 4))
            {
                case 0 when builder.Length > 0:
                    builder[position] = alphabet[random.Next(alphabet.Length)];
                    break;
                case 1 when builder.Length < NameSuggestions.MaxNameLength:
                    builder.Insert(random.Next(builder.Length + 1), alphabet[random.Next(alphabet.Length)]);
                    break;
                case 2 when builder.Length > 1:
                    builder.Remove(position, 1);
                    break;
                case 3 when builder.Length > 1:
                    var left = Math.Min(position, builder.Length - 2);
                    (builder[left], builder[left + 1]) = (builder[left + 1], builder[left]);
                    break;
                case 4 when builder.Length > 0:
                    var character = builder[position];
                    builder[position] = char.IsUpper(character) ? char.ToLowerInvariant(character) : char.ToUpperInvariant(character);
                    break;
            }
        }

        return builder.ToString();
    }

    /// <summary>Long names and their near misses — up to five random edits — at every threshold.</summary>
    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    public void BandedKernel_IsTheCappedReference_OnLongNearMisses(int seed)
    {
        const string alphabet = "abcAB_1";
        var random = new Random(seed);
        for (var trial = 0; trial < 3000; trial++)
        {
            var a = RandomName(random, random.Next(1, NameSuggestions.MaxNameLength + 1), alphabet);
            var b = Mutate(random, a, random.Next(0, 6), alphabet);
            for (var maxDistance = 0; maxDistance <= NameSuggestions.MaxAcceptedDistance + 1; maxDistance++)
            {
                if ((KernelMismatch(a, b, maxDistance) ?? KernelMismatch(b, a, maxDistance)) is { } mismatch)
                    Assert.Fail(mismatch);
            }
        }
    }

    /// <summary>
    /// The early exit: two unrelated 64-character names leave the threshold after k + 1 rows, so at most
    /// <c>(k + 1)(2k + 1)</c> cells are computed instead of 64 × 64; a shared 60-character prefix keeps every row within
    /// it until the difference — the whole band, still never the table.
    /// </summary>
    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    public void BandedKernel_StopsOnceNoAlignmentCanStayWithinTheThreshold(int maxDistance)
    {
        var unrelated = NameSuggestions.BoundedOptimalStringAlignmentDistance(new string('a', 64), new string('b', 64), maxDistance, out var cells);
        Assert.Equal(maxDistance + 1, unrelated);
        Assert.InRange(cells, 1, (maxDistance + 1) * (2 * maxDistance + 1));

        var near = new string('a', 60) + "wxyz";
        var far = new string('a', 60) + "zyxw";
        Assert.Equal(3, NameSuggestions.OptimalStringAlignmentDistance(near, far));
        Assert.Equal(Math.Min(3, maxDistance + 1), NameSuggestions.BoundedOptimalStringAlignmentDistance(near, far, maxDistance, out cells));
        Assert.InRange(cells, 60, 64 * (2 * maxDistance + 1));
    }

    // ── 2. The policies are the pre-change policies ─────────────────────────────────────────────

    /// <summary>The pre-change lexical policy, verbatim but for the kernel: the full reference table.</summary>
    private static string? ReferenceLexical(string name, IEnumerable<string> candidates)
    {
        var maxDistance = name.Length switch { < 3 => 0, <= 5 => 1, _ => 2 };
        string? best = null;
        var bestDistance = int.MaxValue;
        var ambiguous = false;
        foreach (var candidate in candidates)
        {
            int? distance;
            if (string.Equals(name, candidate, StringComparison.Ordinal))
                distance = null;
            else if (string.Equals(name, candidate, StringComparison.OrdinalIgnoreCase))
                distance = 0;
            else if (maxDistance == 0 || Math.Abs(name.Length - candidate.Length) > maxDistance)
                distance = null;
            else
            {
                var full = NameSuggestions.OptimalStringAlignmentDistance(name, candidate);
                distance = full <= maxDistance ? full : null;
            }

            if (distance is null)
                continue;
            if (distance.Value < bestDistance)
                (best, bestDistance, ambiguous) = (candidate, distance.Value, false);
            else if (distance.Value == bestDistance && !string.Equals(candidate, best, StringComparison.Ordinal))
                ambiguous = true;
        }

        return ambiguous ? null : best;
    }

    /// <summary>The pre-change member policy, verbatim but for the kernel: per-comparison casing and the full table.</summary>
    private static string? ReferenceMember(string name, IEnumerable<string> members)
    {
        var maxDistance = name.Length switch { < 3 => 0, <= 4 => 1, _ => Math.Min(3, name.Length / 2) };
        string? best = null;
        var bestDistance = int.MaxValue;
        var ambiguous = false;
        foreach (var candidate in members)
        {
            int? distance;
            if (string.Equals(name, candidate, StringComparison.Ordinal))
                distance = null;
            else if (string.Equals(name, candidate, StringComparison.OrdinalIgnoreCase))
                distance = 0;
            else if (maxDistance == 0 || Math.Abs(name.Length - candidate.Length) > maxDistance)
                distance = null;
            else
            {
                var full = NameSuggestions.OptimalStringAlignmentDistance(name.ToUpperInvariant(), candidate.ToUpperInvariant());
                var sameInitial = char.ToUpperInvariant(name[0]) == char.ToUpperInvariant(candidate[0]);
                distance = full <= maxDistance && (sameInitial || (Math.Min(name.Length, candidate.Length) >= 5 && full == 1))
                    ? full : null;
            }

            if (distance is null)
                continue;
            if (distance.Value < bestDistance)
                (best, bestDistance, ambiguous) = (candidate, distance.Value, false);
            else if (distance.Value == bestDistance && !string.Equals(candidate, best, StringComparison.Ordinal))
                ambiguous = true;
        }

        return ambiguous ? null : best;
    }

    /// <summary>
    /// Random names of one to nine characters — every lexical threshold (0, 1, 2) and every member threshold (0, 1, 2, 3)
    /// — against near misses at zero to four edits, case flips (respellings and the member initial guard), unrelated
    /// names and repeated spellings (the tie rule's distinct-candidate clause): both policies select exactly what the
    /// pre-change policies select, through the list entry and through a captured surface alike.
    /// </summary>
    [Theory]
    [InlineData(11)]
    [InlineData(12)]
    [InlineData(13)]
    [InlineData(14)]
    public void SelectionPolicies_AgreeWithThePreChangePolicies_AroundEveryAcceptedThreshold(int seed)
    {
        const string alphabet = "abcdeABCDE";
        var random = new Random(seed);
        for (var trial = 0; trial < 1500; trial++)
        {
            var name = RandomName(random, random.Next(1, 10), alphabet);
            var candidates = Enumerable.Range(0, random.Next(1, 12))
                .Select(_ => random.Next(4) == 0
                    ? RandomName(random, random.Next(1, 10), alphabet)
                    : Mutate(random, name, random.Next(0, 5), alphabet, caseFlips: true))
                .Where(NameSuggestions.IsSuggestible)
                .ToList();
            if (candidates.Count > 0 && random.Next(5) == 0)
                candidates.Add(candidates[0]);

            Assert.Equal(ReferenceLexical(name, candidates), NameSuggestions.SelectLexicalName(name, candidates, observations: null)?.EligibleName);
            var expectedMember = ReferenceMember(name, candidates) is { } member ? "R." + member : null;
            Assert.Equal(expectedMember, NameSuggestions.SelectReceiverMember(name, candidates, "R", observations: null)?.EligibleName);
            Assert.Equal(
                expectedMember,
                NameSuggestions.SelectReceiverMember(name, new ReceiverMemberSurface([.. candidates]), "R", observations: null)?.EligibleName);
        }
    }

    /// <summary>The lexical thresholds and tie rule, case by case: 0 below three characters, 1 up to five, 2 beyond.</summary>
    [Theory]
    [InlineData("ab", "AB", "AB")]               // a case respelling qualifies at any length
    [InlineData("ab", "ac", null)]               // otherwise nothing below three characters
    [InlineData("abc", "abd", "abd")]            // three to five characters: one edit
    [InlineData("abcde", "abced", "abced")]      // an adjacent transposition is one edit
    [InlineData("abc", "bcd", null)]             // two edits are too far
    [InlineData("abcdef", "abcxyf", "abcxyf")]   // six and more: two edits
    [InlineData("abcdef", "axcxyf", null)]       // three are too far
    [InlineData("abcd", "abce|abcf", null)]      // two distinct candidates equally close: no suggestion
    [InlineData("abcd", "abce|abce", "abce")]    // one spelling twice is no tie
    public void LexicalThresholds_AndTieRefusal_AreUnchanged(string name, string candidates, string? expected)
    {
        var list = candidates.Split('|');
        Assert.Equal(expected, ReferenceLexical(name, list));
        Assert.Equal(expected, NameSuggestions.SelectLexicalName(name, list, observations: null)?.EligibleName);
    }

    /// <summary>The member thresholds and initial guard: 1 up to four characters, then half the length, at most three.</summary>
    [Theory]
    [InlineData("Ceiling", "Ceil", "Ceil")]      // three edits over seven characters
    [InlineData("Dubel", "Double", "Double")]    // two over five
    [InlineData("Min", "Sin", null)]             // a short name keeps its initial
    [InlineData("Mni", "Min", "Min")]            // a transposition keeping the initial
    [InlineData("Xalue", "Value", "Value")]      // five characters may mistype the initial with one edit
    [InlineData("Xalux", "Value", null)]         // but not with two
    [InlineData("pi", "PI", "PI")]               // a case respelling qualifies at any length
    [InlineData("Valeu", "Value|Valet", null)]   // equally close distinct members: no suggestion
    public void MemberThresholds_AndInitialGuard_AreUnchanged(string name, string members, string? expected)
    {
        var list = members.Split('|');
        var qualified = expected is null ? null : "R." + expected;
        Assert.Equal(expected, ReferenceMember(name, list));
        Assert.Equal(qualified, NameSuggestions.SelectReceiverMember(name, list, "R", observations: null)?.EligibleName);
    }

    // ── 3. Casing once per surface ───────────────────────────────────────────────────────────────

    /// <summary>
    /// A surface's members are cased once and every evaluation reads that one casing; promotions against one receiver
    /// share one surface.
    /// </summary>
    [Fact]
    public void MemberSurface_IsCasedOnce_AndSharedByEveryPromotionAgainstItsReceiver()
    {
        var surface = new ReceiverMemberSurface(["Value", "Double", "Half"]);
        var casing = surface.UpperInvariantNames;
        Assert.Equal(["VALUE", "DOUBLE", "HALF"], casing);
        Assert.Equal("R.Value", NameSuggestions.SelectReceiverMember("Vlaue", surface, "R", observations: null)?.EligibleName);
        Assert.Equal("R.Double", NameSuggestions.SelectReceiverMember("Dubel", surface, "R", observations: null)?.EligibleName);
        Assert.Same(casing, surface.UpperInvariantNames);

        var receiver = SourceProvenance.ParseValid("Value = 1\nDouble = 2\n1").Root;
        var scope = ElaboratedScopeLookup.CreateScope(SourceProvenance.ParseValid("1").Root);
        var contexts = new SuggestionContexts();
        var first = Assert.IsType<ReceiverMemberSuggestionQuery>(
            contexts.Capture("Vlaue", scope, ParameterOwnership.Empty, new DotMemberReceiver(receiver, "M")));
        var second = Assert.IsType<ReceiverMemberSuggestionQuery>(
            contexts.Capture("Dubel", scope, ParameterOwnership.Empty, new DotMemberReceiver(receiver, "M")));
        Assert.Same(first.Members, second.Members);
        Assert.Equal("M.Value", first.Evaluate()?.EligibleName);
        Assert.Equal("M.Double", second.Evaluate()?.EligibleName);
    }

    /// <summary>
    /// The member policy no longer cases a candidate per comparison: once a surface's casing exists, a whole evaluation
    /// over 512 64-character members that all reach the distance comparison allocates about the written name's casing
    /// and the suggestion — where casing both spellings per comparison allocated about 150 KB. A coarse in-process
    /// bound: 16 KB absorbs the allocation counter's ~8 KB quantum and the name, far below one re-cased surface.
    /// </summary>
    [Fact]
    public void MemberEvaluation_DoesNotCaseCandidatesPerComparison()
    {
        var members = Enumerable.Range(0, NameSuggestions.MaxCandidates).Select(static i => $"M{i:D5}" + new string('m', 58)).ToArray();
        var surface = new ReceiverMemberSurface(members);
        var written = "N00001" + new string('m', 58);
        Assert.Equal("R." + members[1], NameSuggestions.SelectReceiverMember(written, surface, "R", observations: null)?.EligibleName);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var suggestion = NameSuggestions.SelectReceiverMember("M00002" + new string('m', 57) + "n", surface, "R", observations: null);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal("R." + members[2], suggestion?.EligibleName);
        Assert.True(allocated < 16 * 1024, $"one evaluation over a cased surface allocated {allocated} bytes");
    }

    // ── 4. One allowance per message ─────────────────────────────────────────────────────────────

    /// <summary>
    /// 256 notes from four bodies over about 300 candidates each: the message offers suggestions exactly for the notes
    /// the allowance admits — first fit in note order — compares exactly their candidates (at most
    /// <see cref="NameSuggestions.MaxCandidatesPerMessage"/>, each within one band), evaluates no other note, and keeps
    /// the rest of the message: the formatted sentence that names every parameter.
    /// </summary>
    [Fact]
    public void UnresolvedImplicitParams_SuggestsWithinOneAllowance_InNoteOrder()
    {
        var failure = Fail(RootProgram(bodies: 4, namesPerBody: 64, candidates: 256));
        Assert.IsType<EvalError.UnresolvedImplicitParams>(failure.Terminal);
        Assert.Equal(256, failure.Notes.Count);
        Assert.All(failure.Notes, static note => Assert.False(note.IsSuggestionEvaluated));
        var admitted = Admitted(failure.Notes);
        Assert.InRange(admitted.Count, 64, failure.Notes.Count - 1);

        var before = Work(failure.Observations);
        var message = KatLangError.FromEvalError(failure.Error).Message;

        AssertBoundedWork(failure, before, admitted);
        Assert.Equal(
            failure.Notes.Where(admitted.Contains).Select(static note => $"Did you mean '{Fix(note.Name)}' instead of '{note.Name}'?"),
            SuggestionLines(message));
        Assert.Equal(
            KatLangError.FormatEvalError(failure.Error) + "\n" + string.Join("\n", SuggestionLines(message)),
            message);
    }

    /// <summary>
    /// First fit, not a prefix: after the wide notes have spent what they can, a later note whose surface is one member
    /// (<c>Box.Vlaue</c>) still fits and is still offered, although wide notes before it were not.
    /// </summary>
    [Fact]
    public void Allowance_IsFirstFit_ALaterCheaperNoteIsStillOffered()
    {
        var failure = Fail(Candidates(256) + Helpers(4, 64, Typo) + "Box = { Value = 0 }\nH4 = Box.Vlaue\n" + HelperSum(5) + "\n");
        Assert.IsType<EvalError.UnresolvedImplicitParams>(failure.Terminal);
        var member = Assert.Single(failure.Notes, static note => note.Name == "Vlaue");
        Assert.Same(member, failure.Notes[^1]);
        Assert.Equal(1, member.SuggestionCandidateCount);
        var admitted = Admitted(failure.Notes);
        Assert.Contains(member, admitted);
        Assert.Contains(failure.Notes, note => !admitted.Contains(note));

        var before = Work(failure.Observations);
        var message = KatLangError.FromEvalError(failure.Error).Message;

        AssertBoundedWork(failure, before, admitted);
        Assert.Equal("Did you mean 'Box.Value' instead of 'Vlaue'?", SuggestionLines(message)[^1]);
        Assert.Equal(admitted.Count, SuggestionLines(message).Length);
    }

    /// <summary>
    /// The message is a function of the error alone: reading every note's suggestion directly first (each one alone
    /// has its suggestion) computes the notes past the allowance too, yet a rendering then offers exactly what a first
    /// rendering of an identical, untouched failure offers, compares nothing again, and the terminal-safe re-rendering,
    /// under its own allowance, agrees.
    /// </summary>
    [Fact]
    public void RenderedSuggestions_DoNotDependOnWhatWasAlreadyComputed()
    {
        var source = RootProgram(bodies: 4, namesPerBody: 64, candidates: 256);
        var touched = Fail(source);
        Assert.All(touched.Notes, static note => Assert.Equal(Fix(note.Name), note.SuggestedName));
        var before = Work(touched.Observations);

        var error = KatLangError.FromEvalError(touched.Error);

        Assert.Equal(before, Work(touched.Observations));
        var untouched = Fail(source);
        Assert.Equal(KatLangError.FromEvalError(untouched.Error).Message, error.Message);
        Assert.Equal(Admitted(untouched.Notes).Count, SuggestionLines(error.Message).Length);
        Assert.Equal(error.ToString(), error.ToTerminalSafeString());
    }

    /// <summary>
    /// The arity mismatch with a rendered signature keeps its contract under the allowance: an admitted note adds its
    /// origin and its suggestion; a note past the allowance — rendered as a note without a suggestion — adds nothing.
    /// </summary>
    [Fact]
    public void ArityMismatchWithSignature_RendersAdmittedNotesOnly()
    {
        var failure = Fail(CallProgram(bodies: 4, namesPerBody: 64, candidates: 256));
        var arity = Assert.IsType<EvalError.ArityMismatch>(failure.Terminal);
        Assert.NotNull(arity.Signature);
        var admitted = Admitted(failure.Notes);
        Assert.InRange(admitted.Count, 64, failure.Notes.Count - 1);

        var before = Work(failure.Observations);
        var message = KatLangError.FromEvalError(failure.Error).Message;

        AssertBoundedWork(failure, before, admitted);
        var expected = new StringBuilder(KatLangError.FormatEvalError(failure.Error));
        foreach (var note in failure.Notes.Where(admitted.Contains))
            expected.Append('\n').Append(InferredAt(note)).Append('\n').Append($"Did you mean '{Fix(note.Name)}'?");
        Assert.Equal(expected.ToString(), message);
    }

    /// <summary>
    /// The signatureless property form names no parameter, so every note keeps its origin line whether or not the
    /// allowance admits its suggestion.
    /// </summary>
    [Fact]
    public void ArityMismatchWithoutSignature_KeepsEveryOrigin_AndSuggestsWithinTheAllowance()
    {
        var failure = Fail(PropertyProgram(bodies: 4, namesPerBody: 64, candidates: 256));
        var arity = Assert.IsType<EvalError.ArityMismatch>(failure.Terminal);
        Assert.Null(arity.Signature);
        var admitted = Admitted(failure.Notes);
        Assert.InRange(admitted.Count, 64, failure.Notes.Count - 1);

        var before = Work(failure.Observations);
        var message = KatLangError.FromEvalError(failure.Error).Message;

        AssertBoundedWork(failure, before, admitted);
        var expected = new StringBuilder(KatLangError.FormatEvalError(failure.Error));
        foreach (var note in failure.Notes)
        {
            expected.Append('\n').Append(InferredAt(note));
            if (admitted.Contains(note))
                expected.Append('\n').Append($"Did you mean '{Fix(note.Name)}'?");
        }

        Assert.Equal(expected.ToString(), message);
    }

    /// <summary>
    /// A message whose notes fit the allowance — here two bodies of 32 typos over 64 candidates — renders every
    /// suggestion, as before the allowance existed.
    /// </summary>
    [Fact]
    public void AMessageWithinTheAllowance_RendersEverySuggestion()
    {
        var failure = Fail(RootProgram(bodies: 2, namesPerBody: 32, candidates: 64));
        Assert.Equal(failure.Notes.Count, Admitted(failure.Notes).Count);

        var message = KatLangError.FromEvalError(failure.Error).Message;

        Assert.All(failure.Notes, static note => Assert.True(note.IsSuggestionEvaluated));
        Assert.Equal(
            failure.Notes.Select(static note => $"Did you mean '{Fix(note.Name)}' instead of '{note.Name}'?"),
            SuggestionLines(message));
    }

    /// <summary>
    /// Long and no-match controls. Sixty-four-character typos of sixty-four-character candidates are still suggested,
    /// within one band each. Names that match nothing spend the allowance like any other — the work stays bounded — and
    /// render no line. A name too long to be suggested captures nothing, so it costs nothing: placed before the typos,
    /// it leaves their suggestions exactly as they are without it.
    /// </summary>
    [Fact]
    public void LongAndNoMatchNotes_StayBounded_AndUnsuggestibleNotesCostNothing()
    {
        string LongCandidate(int index) => $"Value{index:D3}" + new string('q', 56);
        string LongTypo(int index) => $"Vaule{index:D3}" + new string('q', 56);
        var longSource = string.Concat(Enumerable.Range(0, 96).Select(i => $"{LongCandidate(i)} = {i}\n"))
            + Helpers(2, 48, LongTypo) + HelperSum(2) + "\n";
        var longFailure = Fail(longSource);
        Assert.Equal(NameSuggestions.MaxNameLength, longFailure.Notes[0].Name.Length);
        var before = Work(longFailure.Observations);
        var longMessage = KatLangError.FromEvalError(longFailure.Error).Message;
        var admitted = Admitted(longFailure.Notes);
        AssertBoundedWork(longFailure, before, admitted);
        Assert.Equal(
            longFailure.Notes.Where(admitted.Contains).Select(note => $"Did you mean '{LongCandidate(int.Parse(note.Name[5..8]))}' instead of '{note.Name}'?"),
            SuggestionLines(longMessage));
        Assert.True(Work(longFailure.Observations).Cells - before.Cells <= (Work(longFailure.Observations).Candidates - before.Candidates) * 64 * 5);

        var noMatch = Fail(RootProgram(bodies: 4, namesPerBody: 64, candidates: 256, name: static i => $"Zq{i:D4}zz"));
        var noMatchAdmitted = Admitted(noMatch.Notes);
        Assert.InRange(noMatchAdmitted.Count, 64, noMatch.Notes.Count - 1);
        before = Work(noMatch.Observations);
        var noMatchMessage = KatLangError.FromEvalError(noMatch.Error).Message;
        AssertBoundedWork(noMatch, before, noMatchAdmitted);
        Assert.Equal(KatLangError.FormatEvalError(noMatch.Error), noMatchMessage);

        string Mixed(int index) => index < 64 ? $"Unsuggestible{index:D3}" + new string('u', 52) : Typo(index - 64);
        var mixed = Fail(Candidates(64) + Helpers(3, 32, Mixed) + HelperSum(3) + "\n");
        Assert.All(mixed.Notes.Take(64), static note => Assert.Equal(0, note.SuggestionCandidateCount));
        var mixedLines = SuggestionLines(KatLangError.FromEvalError(mixed.Error).Message);
        Assert.Equal(
            mixed.Notes.Skip(64).Select(static note => $"Did you mean '{Fix(note.Name)}' instead of '{note.Name}'?"),
            mixedLines);
    }

    /// <summary>Concurrent first renderings of one failure agree, and each compares at most one allowance.</summary>
    [Fact]
    public async Task ConcurrentRenderings_AgreeAndStayBounded()
    {
        var failure = Fail(RootProgram(bodies: 4, namesPerBody: 64, candidates: 256));
        const int Renderers = 8;
        using var start = new ManualResetEventSlim();
        var renderers = Enumerable.Range(0, Renderers).Select(_ => Task.Run(() =>
        {
            start.Wait();
            return KatLangError.FromEvalError(failure.Error).Message;
        })).ToArray();
        start.Set();
        var messages = await Task.WhenAll(renderers);

        Assert.Single(messages.Distinct(StringComparer.Ordinal));
        Assert.Equal(Admitted(failure.Notes).Count, SuggestionLines(messages[0]).Length);
        var admittedCandidates = Admitted(failure.Notes).Sum(static note => (long)note.SuggestionCandidateCount);
        Assert.InRange(failure.Observations.SuggestionCandidatesExamined, admittedCandidates, Renderers * admittedCandidates);
        Assert.InRange(failure.Observations.SuggestionDistanceCells, 1,
            failure.Observations.SuggestionCandidatesExamined * NameSuggestions.MaxDistanceCellsPerCandidate);
    }

    [Fact]
    public void SharedNotesSpendOneReceiverConfirmationAllowanceAcrossTheMessage()
    {
        var observations = new FrontEndTraversalObservations();
        var members = new ReceiverMemberSurface(["Double"]);
        var confirmed = new[] { "Double" }.ToFrozenSet(StringComparer.Ordinal);
        ImplicitParameterProvenance Note(string qualifier, int confirmations)
        {
            var note = new ImplicitParameterProvenance("Duoble", null,
                new ReceiverMemberSuggestionQuery("Duoble", members, qualifier, observations), new(qualifier));
            for (var i = 0; i < confirmations; i++)
                note.ConfirmDotMemberReceiver(confirmed);
            return note;
        }

        var first = Note("First", NameSuggestions.MaxConfirmationsPerMessage - 1);
        var skipped = Note("Skipped", 2);
        var last = Note("Last", 1);
        var error = new EvalError.ArityMismatch(3, 0) { InferredImplicitParameters = [first, skipped, last] };
        var message = KatLangError.FromEvalError(error).Message;
        Assert.Equal(2, observations.SuggestionCandidatesExamined);
        Assert.False(skipped.IsSuggestionEvaluated);
        Assert.Equal(["Did you mean 'First.Double'?", "Did you mean 'Last.Double'?"], SuggestionLines(message));
        Assert.Contains("Skipped", message, StringComparison.Ordinal);
        Assert.Equal("Skipped.Double", skipped.SuggestedName);
        Assert.Equal(message, KatLangError.FromEvalError(error).Message);
    }

    // ── 5. The run token on the projection path ──────────────────────────────────────────────────

    /// <summary>A one-candidate query that cancels <paramref name="source"/> at its <paramref name="cancelAt"/>-th evaluation.</summary>
    private sealed class CancellingQuery(CancellationTokenSource source, int cancelAt, int[] evaluations) : SuggestionQuery
    {
        internal override int CandidateCount => 1;

        public override NameSuggestion? Evaluate()
        {
            if (Interlocked.Increment(ref evaluations[0]) == cancelAt)
                source.Cancel();
            return new NameSuggestion("Alpha");
        }
    }

    private static ImplicitParameterProvenance[] CancellingNotes(int count, CancellationTokenSource source, int cancelAt, int[] evaluations)
        => [.. Enumerable.Range(0, count).Select(i => new ImplicitParameterProvenance($"alpah{i}", span: null, new CancellingQuery(source, cancelAt, evaluations)))];

    /// <summary>
    /// <see cref="KatLangError.FromRunEvalError"/> — what the run's projection renders a failure with — observes the
    /// token before each charged suggestion: a cancellation requested while the third note's suggestion is computed
    /// lets that evaluation finish (nothing partial is published) and stops at the next note, with the run's token, for
    /// both message kinds. No later note is evaluated.
    /// </summary>
    [Theory]
    [InlineData(false, 6)]
    [InlineData(true, 6)]
    [InlineData(false, 3)]
    [InlineData(true, 3)]
    public void RunProjection_ObservesTheEvaluationToken_ThroughTheFinalSuggestion(bool arity, int count)
    {
        using var source = new CancellationTokenSource();
        var evaluations = new int[1];
        var notes = CancellingNotes(count, source, cancelAt: 3, evaluations);
        EvalError error = arity
            ? new EvalError.ArityMismatch(count, 0) { InferredImplicitParameters = notes }
            : new EvalError.UnresolvedImplicitParams([.. notes.Select(static note => note.Name)]) { InferredImplicitParameters = notes };

        var thrown = Assert.Throws<OperationCanceledException>(() => KatLangError.FromRunEvalError(error, source.Token));

        Assert.Equal(source.Token, thrown.CancellationToken);
        Assert.Equal(3, evaluations[0]);
        for (var i = 0; i < notes.Length; i++)
            Assert.Equal(i < 3, notes[i].IsSuggestionEvaluated);
    }

    /// <summary>
    /// An already-cancelled token stops failure projection before any suggestion work. The public
    /// <see cref="KatLangError.FromEvalError"/> carries none and
    /// renders what an uncancelled projection renders.
    /// </summary>
    [Fact]
    public void PreCancelledProjectionStopsBeforeSuggestionWork()
    {
        using var cancelled = new CancellationTokenSource();
        cancelled.Cancel();
        var evaluations = new int[1];
        var notes = CancellingNotes(2, cancelled, cancelAt: 0, evaluations);
        var error = new EvalError.UnresolvedImplicitParams(["alpah0", "alpah1"]) { InferredImplicitParameters = notes };
        var thrown = Assert.Throws<OperationCanceledException>(() => KatLangError.FromRunEvalError(error, cancelled.Token));
        Assert.Equal(cancelled.Token, thrown.CancellationToken);
        Assert.Equal(0, evaluations[0]);

        var silent = new EvalError.UnresolvedImplicitParams(["x"]) { InferredImplicitParameters = [new ImplicitParameterProvenance("x", span: null, suggestion: null)] };
        Assert.Equal(cancelled.Token, Assert.Throws<OperationCanceledException>(
            () => KatLangError.FromRunEvalError(silent, cancelled.Token)).CancellationToken);

        using var live = new CancellationTokenSource();
        var fresh = CancellingNotes(2, live, cancelAt: 0, new int[1]);
        var rendered = new EvalError.UnresolvedImplicitParams(["alpah0", "alpah1"]) { InferredImplicitParameters = fresh };
        Assert.Equal(KatLangError.FromEvalError(rendered).Message, KatLangError.FromRunEvalError(rendered, live.Token).Message);
        Assert.Contains("Did you mean 'Alpha' instead of 'alpah0'?", KatLangError.FromEvalError(rendered).Message, StringComparison.Ordinal);
    }

    private static HostOperations IdentityProbe(bool asynchronous)
        => HostOperations.Create(asynchronous
            ? HostOperation.CreateAsync("probe", async (arguments, _) =>
            {
                await Task.Yield();
                return arguments[0];
            }, "x")
            : HostOperation.Create("probe", static (arguments, _) => arguments[0], "x"));

    private static async Task<object> Outcome(Func<RunOptions, Task<object>> operation, RunOptions options)
    {
        try
        {
            return await operation(options);
        }
        catch (OperationCanceledException cancelled)
        {
            return cancelled;
        }
    }

    /// <summary>The four public engine operations, each reporting its outcome (a result, or the failure's errors).</summary>
    private static IEnumerable<(string Name, bool Asynchronous, Func<RunOptions, Task<object>> Invoke)> PublicOperations(string source)
    {
        yield return ("Run", false, options => Task.FromResult<object>(KatLangEngine.Run(source, options)));
        yield return ("EvaluateToAtoms", false, options =>
        {
            try { return Task.FromResult<object>(KatLangEngine.EvaluateToAtoms(source, options)); }
            catch (KatLangException failed) { return Task.FromResult<object>(failed); }
        });
        yield return ("RunAsync", true, async options => await KatLangEngine.RunAsync(source, options));
        yield return ("EvaluateToAtomsAsync", true, async options =>
        {
            try { return await KatLangEngine.EvaluateToAtomsAsync(source, options); }
            catch (KatLangException failed) { return failed; }
        });
    }

    /// <summary>
    /// Through every public sync and async operation, a failure whose message overflows the allowance: with the run's
    /// evaluation token cancelled during the last admitted suggestion (synchronous, and genuinely suspending on the
    /// asynchronous entries), every operation escapes with an <see cref="OperationCanceledException"/> carrying exactly
    /// that token — never a rendered failure or a <see cref="KatLangException"/>. With the SOURCE-processing token cancelled
    /// the same way (the front end is over), the projection observes only the run's evaluation token, so every operation
    /// reports the failure, and all of them the same bounded message as the public facade over the evaluator's error.
    /// </summary>
    [Theory]
    [InlineData(4, 64, 256, true)]
    [InlineData(1, 2, 2, false)]
    public async Task PublicOperations_CarryTheRunToken_AndRenderOneBoundedMessage(int bodies, int names, int candidates, bool exceedsAllowance)
    {
        var source = CallProgram(bodies, names, candidates, prefix: "probe(1) + ");
        var (expected, notes) = ExpectedFailure(source);
        var admitted = Admitted(notes);
        Assert.Equal(exceedsAllowance, admitted.Count < notes.Count);
        Assert.Equal(admitted.Count, SuggestionLines(expected).Length);

        foreach (var (name, asynchronous, invoke) in PublicOperations(source))
        {
            foreach (var suspending in asynchronous ? new[] { false, true } : new[] { false })
            {
                using var evaluation = new CancellationTokenSource();
                var compared = 0;
                FrontEndTraversalObservations CancelOnLastSuggestion(CancellationTokenSource tokenSource) => new()
                {
                    SuggestionCompared = () =>
                    {
                        if (++compared == admitted.Count)
                            tokenSource.Cancel();
                    },
                };
                var cancelledRun = await Outcome(invoke, new RunOptions
                {
                    HostOperations = IdentityProbe(suspending),
                    TraversalObservations = CancelOnLastSuggestion(evaluation),
                    EvaluationCancellationToken = evaluation.Token,
                });
                var thrown = Assert.IsAssignableFrom<OperationCanceledException>(cancelledRun);
                Assert.Equal(admitted.Count, compared);
                Assert.True(evaluation.Token == thrown.CancellationToken, $"{name} (suspending: {suspending}) escaped with another token");

                using var sourceProcessing = new CancellationTokenSource();
                using var uncancelled = new CancellationTokenSource();
                compared = 0;
                var reported = await Outcome(invoke, new RunOptions
                {
                    HostOperations = IdentityProbe(suspending),
                    TraversalObservations = CancelOnLastSuggestion(sourceProcessing),
                    SourceProcessingCancellationToken = sourceProcessing.Token,
                    EvaluationCancellationToken = uncancelled.Token,
                });
                Assert.True(sourceProcessing.IsCancellationRequested);
                var errors = reported switch
                {
                    RunResult.EvalFailure failure => failure.Errors,
                    KatLangException failed => failed.Errors,
                    var other => throw new Xunit.Sdk.XunitException($"{name}: expected the failure, got {other.GetType().Name}"),
                };
                Assert.Equal(expected, Assert.Single(errors).Message);
            }
        }
    }

    /// <summary>
    /// The public facade's message for the arity failure <paramref name="source"/> evaluates to with an inert
    /// identity host operation, and the failure's notes.
    /// </summary>
    private static (string Message, IReadOnlyList<ImplicitParameterProvenance> Notes) ExpectedFailure(string source)
    {
        var operations = IdentityProbe(asynchronous: false);
        var compiled = FrontEndPipeline.Process(source, new RunOptions { HostOperations = operations });
        Assert.False(compiled.HasErrors, string.Join("\n", compiled.Diagnostics.Select(static d => d.Message)));
        var result = Evaluator.Run(new Expr.AlgorithmExpr(compiled.ElaboratedRoot), operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.ArityMismatch>(TerminalOf(result.Error));
        Assert.NotNull(arity.InferredImplicitParameters);
        return (KatLangError.FromEvalError(result.Error).Message, arity.InferredImplicitParameters);
    }
}
