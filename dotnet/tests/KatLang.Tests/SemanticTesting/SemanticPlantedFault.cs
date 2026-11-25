using KatLang.ParserFuzz;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// The TEST-ONLY planted-fault seam of the semantic campaign (SEM-2C, fuzz/README.md § Campaigns): a
/// forged observation that is WRONG but WELL-FORMED for every case kind — a success, an expected
/// runtime failure and an intended front-end refusal alike — so a supervised worker writes it and every
/// result reader accepts it as an ordinary <see cref="SemanticVerdict.Mismatch"/>. It adds ONE host event
/// the program never performed, <see cref="PlantedEvent"/>, to <c>base@sync-optimized</c>; the run's
/// outcome, value, error and every other profile stay as observed. The anchor that disagrees is the
/// host-event anchor of a valid case (<see cref="ValidSignature"/>) or the front-end-effect anchor of a
/// refusal (<see cref="RefusalSignature"/>).
///
/// <para>By contrast <see cref="SemanticReductionTests.WrongValue"/> forges a VALUE observation that only a
/// success can carry: on an expected failure it lacks the emitted count every successful observation
/// has, so the result reader rejects it as <see cref="SemanticVerdict.MalformedOutput"/>.</para>
///
/// <para>A <see cref="Defect"/> plants the fault in ONE worker process through the runner's inert
/// observation filter (<see cref="SemanticReplay.WorkBatch"/>, <see cref="SemanticReplay.Work"/>). With a
/// trigger it is armed only once the trigger case has run in that process, which makes a failure that
/// exists only inside a batch: alone, the victim passes. Production commands never install it.</para>
/// </summary>
internal static class SemanticPlantedFault
{
    /// <summary>The forged host event: no generated program traces 4242.</summary>
    internal const string PlantedEvent = "trace:4242";

    /// <summary>The planted failure's signature on a valid case (a success or an expected runtime failure).</summary>
    internal static readonly SemanticFailureSignature ValidSignature =
        new(SemanticVerdict.Mismatch, SemanticMember.BaseRole, SemanticProfiles.SyncOptimized, "host-events");

    /// <summary>The planted failure's signature on an intended front-end refusal.</summary>
    internal static readonly SemanticFailureSignature RefusalSignature =
        new(SemanticVerdict.Mismatch, SemanticMember.BaseRole, SemanticProfiles.SyncOptimized, "front-end-effects");

    /// <summary>The well-formed wrong observation: one extra host event on <c>base@sync-optimized</c>.</summary>
    internal static SemanticProfileRun WrongEvent(SemanticProfileRun run)
        => run.Profile == SemanticProfiles.SyncOptimized && run.Member == SemanticMember.BaseRole
            ? run with { Events = [.. run.Events, PlantedEvent] }
            : run;

    /// <summary>
    /// The fault planted in one process for the <paramref name="victims"/> (by case id; a reduced case of a
    /// victim keeps it, so a reducer's candidates and its reduced case fail alike). With a
    /// <paramref name="trigger"/> it fires only after a case with that id was handed to the worker in the
    /// same process: state an earlier batch member leaves behind.
    /// </summary>
    internal sealed class Defect(IReadOnlyCollection<string> victims, string? trigger)
    {
        private bool _armed;

        public Func<SemanticProfileRun, SemanticProfileRun>? For(SemanticCase semanticCase)
        {
            if (victims.Any(victim => Is(semanticCase.CaseId, victim)) && (trigger is null || _armed)) return WrongEvent;
            if (trigger is not null && semanticCase.CaseId == trigger) _armed = true;
            return null;
        }

        private static bool Is(string caseId, string planted)
            => caseId == planted
                || caseId.StartsWith(SemanticRecipe.CasePrefix + SemanticReduction.ReducedLocalPrefix + planted[SemanticRecipe.CasePrefix.Length..] + "/", StringComparison.Ordinal);
    }
}
