using System.Collections.Immutable;

namespace KatLang.ParserFuzz;

/// <summary>
/// Which check of <see cref="SemanticRunner"/> produced a finding. The set is STABLE: every member
/// has a fixed serialized name (<see cref="SemanticFindingFacets.Name"/>) and a fixed reduction
/// signature facet (<see cref="SemanticFindingFacets.SignatureFacet"/>). Rewording a finding's text
/// never changes either; adding a check adds a member (fuzz/README.md § Reduction).
/// </summary>
internal enum SemanticFindingFacet
{
    // ── Case contract ───────────────────────────────────────────────────────

    /// <summary>The case has no members or profiles (or transformations without sync-optimized).</summary>
    CaseContract,

    // ── Front end (CheckFrontEnd) ───────────────────────────────────────────

    /// <summary>A VALID member was rejected; the location is the first error's diagnostic code.</summary>
    FrontEndRejected,

    /// <summary>An INVALID member was accepted.</summary>
    FrontEndAccepted,

    /// <summary>An invalid member was rejected in the wrong phase.</summary>
    FrontEndPhase,

    /// <summary>An invalid member was rejected without the expected diagnostic.</summary>
    FrontEndDiagnostic,

    // ── Anchors (CheckAnchors) ──────────────────────────────────────────────

    /// <summary>The profile run reported a harness problem (watchdog, unscheduled cancellation, …).</summary>
    Harness,

    /// <summary>The surface ran but returned no observation.</summary>
    ObservationMissing,

    /// <summary>The observation does not carry the declared surface and facets.</summary>
    FacetContract,

    /// <summary>An invalid source reached a parsing surface's evaluator.</summary>
    FrontEndReached,

    /// <summary>A pipeline surface did not report a front-end failure for an invalid source.</summary>
    FrontEndFailure,

    /// <summary>Host effects ran for a front-end-rejected program.</summary>
    FrontEndEffects,

    /// <summary>A cancellation profile did not observe its scheduled cancellation.</summary>
    Cancellation,

    /// <summary>A cancellation profile's events differ from the constructed prefix.</summary>
    CancellationEvents,

    /// <summary>A non-cancellation profile was cancelled.</summary>
    UnscheduledCancellation,

    /// <summary>The surface refused a valid source.</summary>
    SurfaceRefused,

    /// <summary>A run stopped at a resource limit.</summary>
    ResourceLimit,

    /// <summary>Success expected and failure observed, or the reverse.</summary>
    Outcome,

    /// <summary>The structure facet carries no value.</summary>
    StructureMissing,

    /// <summary>The value differs from the constructed value.</summary>
    Value,

    /// <summary>The emitted-count facet is empty.</summary>
    EmittedCountMissing,

    /// <summary>The emitted count differs from the constructed count.</summary>
    EmittedCount,

    /// <summary>The structured-error facet is empty.</summary>
    ErrorMissing,

    /// <summary>The error kind differs from the constructed kind.</summary>
    ErrorKind,

    /// <summary>A pipeline surface failed in a stage other than evaluation.</summary>
    FailureStage,

    /// <summary>The host events differ from the constructed events.</summary>
    HostEvents,

    // ── Paths (JudgePaths) ──────────────────────────────────────────────────

    /// <summary>A claimed path was not admitted; the location is the path name.</summary>
    Path,

    // ── Declared parity and relations ───────────────────────────────────────

    /// <summary>A declared profile pair disagrees; the location is the compared class and field (or <c>observation-missing</c>).</summary>
    Parity,

    /// <summary>A declared profile pair saw different host events.</summary>
    ParityHostEvents,

    /// <summary>The two cancellation profiles ended differently.</summary>
    CancellationParity,

    /// <summary>A transformation differs from the base; the location is the compared class and field (or <c>observation-missing</c>).</summary>
    Relation,
}

/// <summary>
/// The structured form of one runner finding, produced beside its text at the same site.
///
/// <list type="bullet">
/// <item><see cref="Member"/> — the member role checked (<c>base</c>, <c>alpha-rename</c>, …), or <c>-</c>.</item>
/// <item><see cref="Profile"/> — the execution profile id, the declared pair id (<c>parity:L~R</c>),
/// <c>cancellation parity</c>, <c>front-end</c> for front-end checks, or <c>-</c>.</item>
/// <item><see cref="Facet"/> — which check failed (<see cref="SemanticFindingFacet"/>).</item>
/// <item><see cref="Location"/> — the facet's VALUE-FREE qualifier: the path name, the compared
/// <c>&lt;class&gt; relation violated on &lt;field&gt;</c>, <c>observation-missing</c>, or the first
/// diagnostic code; empty for an unqualified facet. Observed values, events and messages never enter it.</item>
/// </list>
/// </summary>
internal sealed record SemanticFinding(SemanticVerdict Verdict, string Member, string Profile, SemanticFindingFacet Facet, string Location)
{
    internal const string None = "-";
    internal const string FrontEndProfile = "front-end";
    internal const string CancellationParityProfile = "cancellation parity";
    internal const string ObservationMissingLocation = "observation-missing";

    /// <summary>The value-free comparison label of a comparator mismatch (its class and compared field).</summary>
    internal static string ComparisonLocation(MetamorphicMismatch mismatch)
        => $"{mismatch.Class} relation violated on {mismatch.ComparedProperty}";
}

/// <summary>Stable names and signature facets of <see cref="SemanticFindingFacet"/>.</summary>
internal static class SemanticFindingFacets
{
    private static readonly ImmutableArray<(SemanticFindingFacet Facet, string Name)> Names =
    [
        (SemanticFindingFacet.CaseContract, "case-contract"),
        (SemanticFindingFacet.FrontEndRejected, "front-end-rejected"),
        (SemanticFindingFacet.FrontEndAccepted, "front-end-accepted"),
        (SemanticFindingFacet.FrontEndPhase, "front-end-phase"),
        (SemanticFindingFacet.FrontEndDiagnostic, "front-end-diagnostic"),
        (SemanticFindingFacet.Harness, "harness"),
        (SemanticFindingFacet.ObservationMissing, "observation-missing"),
        (SemanticFindingFacet.FacetContract, "facet-contract"),
        (SemanticFindingFacet.FrontEndReached, "front-end-reached"),
        (SemanticFindingFacet.FrontEndFailure, "front-end-failure"),
        (SemanticFindingFacet.FrontEndEffects, "front-end-effects"),
        (SemanticFindingFacet.Cancellation, "cancellation"),
        (SemanticFindingFacet.CancellationEvents, "cancellation-events"),
        (SemanticFindingFacet.UnscheduledCancellation, "unscheduled-cancellation"),
        (SemanticFindingFacet.SurfaceRefused, "surface-refused"),
        (SemanticFindingFacet.ResourceLimit, "resource-limit"),
        (SemanticFindingFacet.Outcome, "outcome"),
        (SemanticFindingFacet.StructureMissing, "structure-missing"),
        (SemanticFindingFacet.Value, "value"),
        (SemanticFindingFacet.EmittedCountMissing, "emitted-count-missing"),
        (SemanticFindingFacet.EmittedCount, "emitted-count"),
        (SemanticFindingFacet.ErrorMissing, "error-missing"),
        (SemanticFindingFacet.ErrorKind, "error-kind"),
        (SemanticFindingFacet.FailureStage, "failure-stage"),
        (SemanticFindingFacet.HostEvents, "host-events"),
        (SemanticFindingFacet.Path, "path"),
        (SemanticFindingFacet.Parity, "parity"),
        (SemanticFindingFacet.ParityHostEvents, "parity-host-events"),
        (SemanticFindingFacet.CancellationParity, "cancellation-parity"),
        (SemanticFindingFacet.Relation, "relation"),
    ];

    internal static IEnumerable<SemanticFindingFacet> All => Names.Select(static n => n.Facet);

    /// <summary>The serialized name (worker result documents). Never derived from the enum identifier.</summary>
    internal static string Name(SemanticFindingFacet facet)
    {
        foreach (var (f, name) in Names)
            if (f == facet) return name;
        throw new ArgumentOutOfRangeException(nameof(facet), facet, "unregistered finding facet");
    }

    internal static bool TryParse(string? name, out SemanticFindingFacet facet)
    {
        foreach (var (f, n) in Names)
        {
            if (string.Equals(n, name, StringComparison.Ordinal))
            {
                facet = f;
                return true;
            }
        }

        facet = default;
        return false;
    }

    /// <summary>
    /// The reduction-signature facet. These strings are the ones <c>kl-sem2b-reduction</c> v1
    /// records already carry (the former text classifier's), so a structured signature equals the
    /// text-derived one for every current template and old records keep their meaning.
    /// </summary>
    internal static string SignatureFacet(SemanticFinding finding) => finding.Facet switch
    {
        SemanticFindingFacet.CaseContract => "case",
        SemanticFindingFacet.FrontEndRejected => "front-end:" + finding.Location,
        SemanticFindingFacet.FrontEndAccepted => "front-end:accepted",
        SemanticFindingFacet.FrontEndPhase => "front-end:phase",
        SemanticFindingFacet.FrontEndDiagnostic => "front-end:diagnostic",
        SemanticFindingFacet.Harness => "other",
        SemanticFindingFacet.Path => "path:" + finding.Location,
        SemanticFindingFacet.Parity => "parity:" + finding.Location,
        SemanticFindingFacet.ParityHostEvents => "parity-host-events",
        SemanticFindingFacet.CancellationParity => "parity",
        SemanticFindingFacet.Relation => "relation:" + finding.Location,
        var facet => Name(facet),
    };
}
