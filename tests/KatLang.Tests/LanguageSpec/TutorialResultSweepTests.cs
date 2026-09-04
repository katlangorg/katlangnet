namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// The tutorial result-claim sweep (M13): every tutorial fence that documents
/// an executable outcome with a <c>**Result(s):**</c> claim is executed
/// through the public runtime (<see cref="KatLangEngine.Run(string, RunOptions?)"/>)
/// and its canonical display must match the documented claim. No marker is
/// needed — writing an ordinary fence followed by a Result claim automatically
/// enters the sweep. The only escape hatch is an explicit
/// <c>&lt;!-- spec:skip reason --&gt;</c> marker for a genuinely
/// non-standalone example, and the skip inventory is pinned exactly, so the
/// accounting identity holds mechanically:
///
/// <code>result-bearing fences == engine-verified + explicitly skipped</code>
///
/// with zero silently unclassified claims (the shared parser fails loudly on
/// any unrecognized or detached result label — see <see cref="TutorialCorpus"/>).
/// </summary>
public class TutorialResultSweepTests
{
    private sealed record ReviewedSkip(
        string Section,
        string Source,
        TutorialClaimKind ClaimKind,
        string ClaimedDisplay,
        string Reason);

    private sealed record ReviewedDetailedError(
        string Source,
        string ClaimText,
        KatLangErrorCode ErrorCode);

    private static readonly IReadOnlyList<ReviewedDetailedError> DetailedErrorPins =
        Array.AsReadOnly<ReviewedDetailedError>(
            [
                new(
                    "A = {\n}\nA",
                    "**Result:** error — `A` has no defined output.",
                    KatLangErrorCode.MissingOutput),
                new(
                    "A = {\n}\nA == ()",
                    "**Result:** error — `A` has no defined output.",
                    KatLangErrorCode.MissingOutput),
                new(
                    "A = q + 1\nAdd1(x) = x + 1\nF(x) = Add1(A)\n\nF(7)",
                    "**Result:** error — `Add1`'s parameter `x` is bound to the callable `A`, and `A` still needs its implicit `q`, so demanding `x` as a value is an arity error.",
                    KatLangErrorCode.ArityMismatch),
                new(
                    "A = [1, 2, 3]\nA*.count",
                    "**Result:** error — `A*.count` is the fluent supply chain, exactly `count(A*)`: the three items become three separate argument slots, and the fixed `count(collection)` signature reports an arity error.",
                    KatLangErrorCode.ArityMismatch),
            ]);

    private static readonly IReadOnlyList<TutorialExample> ResultBearing =
        TutorialCorpus.Examples.Where(e => e.HasResultClaim).ToArray();

    private static readonly IReadOnlyList<TutorialExample> Verified =
        ResultBearing.Where(e => e.SkipReason is null).ToArray();

    private static readonly IReadOnlyList<TutorialExample> Skipped =
        ResultBearing.Where(e => e.SkipReason is not null).ToArray();

    public static TheoryData<int, string> VerifiedExampleData()
    {
        var data = new TheoryData<int, string>();
        for (var i = 0; i < Verified.Count; i++)
            data.Add(i, $"L{Verified[i].FenceLine}: {Verified[i].FirstSourceRow}");
        return data;
    }

    /// <summary>
    /// The sweep proper: parse + evaluate through the public engine and
    /// compare the canonical display against the documented claim. The
    /// identity argument only names the case in test output; the example is
    /// addressed by its ordinal among verified result-bearing fences.
    /// </summary>
    [Theory]
    [MemberData(nameof(VerifiedExampleData))]
    public void VerifiedExample_EngineOutcomeMatchesClaim(int index, string identity)
    {
        _ = identity;
        var example = Verified[index];
        var run = KatLangEngine.Run(example.Source);
        var actualDisplay = run.ToDisplayString().ReplaceLineEndings("\n");

        if (example.ClaimKind == TutorialClaimKind.Error)
        {
            Assert.True(run is not RunResult.ParseFailure,
                $"Tutorial error-claim example does not parse.\n{example.Identity}\n"
                + $"Claim: {example.ErrorClaimText}\nSource:\n{example.Source}\nDiagnostics:\n{actualDisplay}");
            Assert.True(run is RunResult.EvalFailure or RunResult.NoProgramOutput,
                $"Tutorial example claims an error but evaluated successfully.\n{example.Identity}\n"
                + $"Claim: {example.ErrorClaimText}\nSource:\n{example.Source}\nActual display:\n{actualDisplay}");

            if (run is RunResult.EvalFailure failure
                && DetailedErrorPins.SingleOrDefault(pin =>
                    pin.Source == example.Source && pin.ClaimText == example.ErrorClaimText) is { } detailedPin)
            {
                Assert.Contains(failure.Errors, error => error.Code == detailedPin.ErrorCode);
            }

            return;
        }

        Assert.True(run is RunResult.Success,
            $"Tutorial example claims a value result but did not evaluate ({run.GetType().Name}).\n"
            + $"{example.Identity}\nSource:\n{example.Source}\nDocumented:\n{example.ClaimedDisplay}\n"
            + $"Actual:\n{actualDisplay}");

        Assert.True(example.ClaimedDisplay == actualDisplay,
            $"Tutorial result mismatch.\n{example.Identity}\nSource:\n{example.Source}\n"
            + $"Documented:\n{example.ClaimedDisplay}\nActual:\n{actualDisplay}");
    }

    /// <summary>
    /// Monotonic coverage ratchet: the reviewed baseline of result-bearing
    /// tutorial claims. RAISE it when result-bearing examples are added —
    /// though ordinary additions need no immediate edit, because the assertion
    /// is <c>&gt;=</c> — and LOWER it only in a reviewed diff that deliberately
    /// removes tutorial result coverage. Deleting (or mis-labelling) even one
    /// existing claim fails the ratchet below; the verified/skipped split is
    /// governed separately (partition identity + exact skip inventory), so
    /// converting a claim into a reviewed skip does not move this count.
    /// </summary>
    private const int MinimumResultBearingClaims = 180;

    /// <summary>
    /// Coarse parser-sanity floor on total source fences, NOT a coverage
    /// ratchet: it exists so a fence-detection regression cannot silently
    /// ignore a large part of the tutorial. Claim-less fences (syntax
    /// fragments, style demos) are ordinary prose-level content whose
    /// individual removal carries no verification consequence, so this floor
    /// is deliberately loose — the one-claim-tight guarantee lives in
    /// <see cref="MinimumResultBearingClaims"/>.
    /// </summary>
    private const int SourceFenceSanityFloor = 200;

    private static string AccountingSummary() =>
        $"tutorial sweep accounting: {TutorialCorpus.Examples.Count} source fences; "
        + $"{ResultBearing.Count} result-bearing = {Verified.Count} engine-verified + {Skipped.Count} skipped; "
        + $"claims by kind: inline={ResultBearing.Count(e => e.ClaimKind == TutorialClaimKind.InlineValue)}, "
        + $"fenced={ResultBearing.Count(e => e.ClaimKind == TutorialClaimKind.FencedRows)}, "
        + $"error={ResultBearing.Count(e => e.ClaimKind == TutorialClaimKind.Error)}; "
        + $"marker-linked={TutorialCorpus.Examples.Count(e => e.SpecCaseId is not null)}.";

    /// <summary>
    /// Partition identity: every result-bearing fence is either engine-verified
    /// or explicitly skipped — the parser classifies claims into exactly the
    /// recognized forms and throws on near-misses, so nothing can be silently
    /// unclassified. Shrinkage of the claim corpus itself is guarded by the
    /// monotonic ratchet in
    /// <see cref="CoverageRatchet_ResultBearingClaimsCannotSilentlyShrink"/>.
    /// </summary>
    [Fact]
    public void Accounting_ResultClaimPartitionIsComplete()
    {
        Assert.True(ResultBearing.Count == Verified.Count + Skipped.Count,
            $"Result-claim partition broke. {AccountingSummary()}");
        Assert.True(TutorialCorpus.Examples.Count >= SourceFenceSanityFloor,
            $"Tutorial source-fence count collapsed; fences may have been mass-removed or a fence-detection "
            + $"regression is ignoring part of the file. {AccountingSummary()}");
    }

    /// <summary>
    /// M13 coverage ratchet. Result-bearing tutorial coverage is monotonic:
    /// new claims are automatically accepted and tested with no pin to update,
    /// while removing an existing claim fails here and requires a deliberate
    /// baseline reduction in the same reviewed diff. (Mirrors the corpus-side
    /// <c>FidelityRatchet_LeanGuardedCoverageCannotSilentlyShrink</c>.)
    /// </summary>
    [Fact]
    public void CoverageRatchet_ResultBearingClaimsCannotSilentlyShrink()
    {
        Assert.True(ResultBearing.Count >= MinimumResultBearingClaims,
            $"Result-bearing tutorial coverage shrank below the reviewed baseline: minimum "
            + $"{MinimumResultBearingClaims}, actual {ResultBearing.Count} "
            + $"({Verified.Count} engine-verified + {Skipped.Count} skipped). Removing an existing "
            + "Result claim is a deliberate coverage decision — restore the claim, or lower the pinned "
            + $"baseline in the same reviewed diff. {AccountingSummary()}");
    }

    /// <summary>
    /// Skips are exceptional and reviewed: the exact inventory is pinned by
    /// line-independent identity (section + complete source + complete claim)
    /// with the exact reason, so a new skip, a removed skip, source/result
    /// drift, or any reason rewrite is conspicuous in this test's diff — never
    /// a silent reclassification.
    /// </summary>
    [Theory]
    [MemberData(nameof(CheckoutText.LineEndingData), MemberType = typeof(CheckoutText))]
    public void SkipInventory_IsExactlyTheReviewedSet(string checkoutLineEnding)
    {
        ReviewedSkip[] expected =
        [
            new(
                "Loading External Algorithms",
                """
                # Load and bind to property 'Lib':
                Lib = load('https://katlang.org/algorithm.kat')

                # Access a public property 'X' from the loaded algorithm:
                Lib.X + 3

                # Use the second output value of the loaded algorithm (index 1):
                Lib:1 + 10
                """,
                TutorialClaimKind.FencedRows,
                "23\n16",
                "module loading needs a host-configured network downloader; the URL and its outputs are illustrative"),
            new(
                "`open`: Import Properties Directly",
                """
                open 'https://katlang.org/algorithm.kat'

                # X is now directly accessible:
                X + 3
                """,
                TutorialClaimKind.InlineValue,
                "23",
                "open 'url' needs a host-configured network downloader; the URL and its output are illustrative"),
        ];

        var actual = Skipped
            .Select(e => new ReviewedSkip(
                e.Section,
                CheckoutText.Normalize(e.Source),
                e.ClaimKind,
                CheckoutText.Normalize(e.ClaimedDisplay!),
                e.SkipReason!))
            .OrderBy(e => e.Section, StringComparer.Ordinal)
            .ToArray();

        expected = expected
            .Select(e => e with
            {
                Source = CheckoutText.Normalize(
                    CheckoutText.WithLineEndings(e.Source, checkoutLineEnding)),
                ClaimedDisplay = CheckoutText.Normalize(
                    CheckoutText.WithLineEndings(e.ClaimedDisplay, checkoutLineEnding)),
            })
            .OrderBy(e => e.Section, StringComparer.Ordinal)
            .ToArray();

        string Inventory() => actual.Length == 0
            ? "(none)"
            : string.Join("\n", actual.Select(e =>
                $"  [{e.Section}] `{e.Source.Split('\n').FirstOrDefault(l => l.Length > 0)}` "
                + $"=> {e.ClaimedDisplay.ReplaceLineEndings("\\n")} — {e.Reason}"));

        Assert.True(expected.SequenceEqual(actual),
            $"Exact skip inventory changed: expected {expected.Length} reviewed skips, found {actual.Length}.\n"
            + $"Current inventory:\n{Inventory()}\n"
            + "Adding/removing a spec:skip, changing its complete source/result identity, or rewriting its reason "
            + "is a reviewed decision — update this exact pin in the same diff.");
    }

    /// <summary>
    /// The ordinary error-claim contract is intentionally coarse (clean parse
    /// plus evaluation failure). The current tutorial goes further: all three
    /// labels name a specific failure family. Pin those complete detailed
    /// claims and check the public structured code, never rendered-message
    /// substrings. A future generic <c>**Result:** error</c> needs no entry;
    /// adding or rewriting detailed error prose is deliberately reviewed here.
    /// </summary>
    [Fact]
    public void DetailedErrorClaims_MatchTheirReviewedStructuredErrors()
    {
        var detailed = ResultBearing
            .Where(e => e.ClaimKind == TutorialClaimKind.Error
                && e.ErrorClaimText is not "**Result:** error"
                && e.ErrorClaimText is not "**Results:** error")
            .ToArray();

        Assert.Equal(DetailedErrorPins.Count, detailed.Length);
        for (var i = 0; i < DetailedErrorPins.Count; i++)
        {
            var pin = DetailedErrorPins[i];
            var example = detailed[i];
            Assert.True(pin.Source == example.Source && pin.ClaimText == example.ErrorClaimText,
                $"Detailed tutorial error-claim inventory changed at {example.Identity}.\n"
                + $"Expected source/claim:\n{pin.Source}\n{pin.ClaimText}\n"
                + $"Actual source/claim:\n{example.Source}\n{example.ErrorClaimText}");
        }
    }

    /// <summary>
    /// Marker-linked examples stay inside the sweep: linkage adds canonical-case
    /// pinning on top of engine verification, never replaces it. (A skip on a
    /// marker-linked fence is structurally impossible — one fence takes one
    /// marker — so every linked result claim is engine-verified here too.)
    /// </summary>
    [Fact]
    public void MarkerLinkedResultClaims_AreEngineVerifiedBySweep()
    {
        var linkedWithClaims = TutorialCorpus.Examples
            .Where(e => e.SpecCaseId is not null && e.HasResultClaim)
            .ToArray();

        Assert.True(linkedWithClaims.Length > 0,
            "No marker-linked example carries a result claim; the linkage conventions may have drifted.");
        Assert.All(linkedWithClaims, e => Assert.Contains(e, Verified));
    }
}
