using System.Globalization;
using System.Text;
using KatLang.ParserFuzz;
using KatLang.Tests.LanguageSpec;
using KatLang.Tests.SemanticTesting;

namespace KatLang.Tests;

/// <summary>
/// Generates and pins <c>lean/KatLangArityLaws/MayCaptureCallsCorpus.lean</c>: Lean's program gate
/// (<c>Expr.mayCaptureCalls</c>, <c>lean/KatLangArityLaws/MayCaptureCalls.lean</c>) checked against C#'s gate of
/// invocation-plan retention (J7, <see cref="AstStructuralPreflight.MayCaptureCalls"/>) on every Lean-comparable
/// program of the differential corpora: <see cref="LanguageSpecCorpus"/>, <see cref="SemanticExplorerCorpus"/>
/// (surface and internal-node cases), the SEM-2C generated cases (<see cref="SemanticGeneratedLeanArtifactTests"/>,
/// base and transformation members), <see cref="HostParentDifferentialCorpus"/> (host-attached parent scopes),
/// <see cref="ModuleDifferentialCorpus"/> (loaded modules), and <see cref="PlannedLoopTempFamily"/> (loop steps).
///
/// <para><b>The two sides.</b> C#'s verdict is the fact the run's own admission walk decides
/// (<see cref="AstStructuralPreflight.CheckAdmittedProgram"/>: <c>MayCaptureCalls</c>) over the elaborated tree the
/// corpus evaluates. The Lean program is the definition the corpus's own generated module already holds for that tree
/// (<c>LanguageSpecCases.case_…</c>, <c>SemanticExplorerCases.case_…</c>, <c>SemanticGeneratedCases.case_…</c>,
/// <c>HostParentDifferential.hp_…</c>, <c>ModuleDifferential.same_url</c>): the generated file imports the programs. Each
/// program's tree is re-encoded here (<see cref="LeanAstEncoder"/>) and required to equal the text that module
/// defines, so the verdict and the definition are of the SAME tree.</para>
///
/// <para><b>Nothing is sampled.</b> Every corpus program is either guarded or excluded by a counted rule
/// (<see cref="GateExclusion"/>): it has no Lean program (a parse-level case, a C#-only case, an invalid generated
/// case, a generated case excluded by id), its Lean program is hand-authored, the structural preflight refuses its
/// tree, or its tree holds a deferred module region (C#'s first clause, which has no Lean form).</para>
///
/// <para>If C#'s verdict on a program changes, this test fails (regenerate and review the diff); if Lean's predicate
/// disagrees with a recorded verdict, <c>lake build KatLangArityLaws</c> fails on that program's guard.</para>
///
/// Regenerate with:
///   $env:KATLANG_REGENERATE_MAY_CAPTURE_CALLS = "1"
///   dotnet test ./dotnet/tests/KatLang.Tests/KatLang.Tests.csproj --filter MayCaptureCallsLeanArtifact
/// That run writes the artifact and then fails by design (see <see cref="ArtifactRegeneration"/>); review the diff,
/// clear the flag, rerun.
/// </summary>
public class MayCaptureCallsLeanArtifactTests
{
    private const string ArtifactRelativePath = "lean/KatLangArityLaws/MayCaptureCallsCorpus.lean";

    internal const string SpecCorpus = "language-spec";
    internal const string ExplorerCorpus = "explorer";
    internal const string ExplorerInternalCorpus = "explorer-internal";
    internal const string GeneratedCorpus = "generated";
    internal const string HostParentCorpus = "host-parent";
    internal const string ModuleCorpus = "modules";
    private const string LoopTempCorpus = "planned-loop-temps";

    /// <summary>The corpora in emission order, each with the Lean namespace of its generated module.</summary>
    internal static readonly IReadOnlyList<(string Corpus, string LeanNamespace, string ListName)> Corpora =
    [
        (SpecCorpus, "LanguageSpecCases", "languageSpecPrograms"),
        (ExplorerCorpus, "SemanticExplorerCases", "explorerPrograms"),
        (ExplorerInternalCorpus, "SemanticExplorerCases", "explorerInternalPrograms"),
        (GeneratedCorpus, "SemanticGeneratedCases", "generatedPrograms"),
        (HostParentCorpus, "HostParentDifferential", "hostParentPrograms"),
        (ModuleCorpus, "ModuleDifferential", "modulePrograms"),
        (LoopTempCorpus, "PlannedLoopTempFamily", "plannedLoopTempPrograms"),
    ];

    /// <summary>Why a corpus program has no guard.</summary>
    internal enum GateExclusion
    {
        /// <summary>The source does not parse (Lean has no surface parser), so no tree exists.</summary>
        ParseLevel,

        /// <summary>The corpus excludes the case from Lean with a reviewed reason (a C#-only model boundary).</summary>
        CSharpOnly,

        /// <summary>A generated front-end-invalid case (Lean has no surface front end).</summary>
        InvalidFrontEnd,

        /// <summary>A valid generated case its Lean artifact excludes by exact id.</summary>
        ExcludedById,

        /// <summary>The Lean program is hand-authored, not the encoding of the evaluated tree.</summary>
        HandAuthoredLeanProgram,

        /// <summary>The structural preflight refuses the tree: no run admits it, so it has no gate fact.</summary>
        RefusedByPreflight,

        /// <summary>The tree holds a deferred module region: C#'s first clause, which has no Lean form.</summary>
        DeferredRegion,
    }

    /// <summary>
    /// One corpus program: guarded (<see cref="LeanReference"/> and <see cref="MayCaptureCalls"/> set) or excluded
    /// (<see cref="Exclusion"/> set).
    /// </summary>
    internal sealed record GateProgram(
        string Corpus, string Id, string? LeanReference, bool MayCaptureCalls, bool HasMetaBinder, GateExclusion? Exclusion);

    private static readonly Lazy<Task<IReadOnlyList<GateProgram>>> Programs = new(BuildProgramsAsync);

    [Fact]
    public async Task GeneratedLeanArtifact_MatchesCurrentCSharpGateVerdicts()
    {
        var expected = GenerateArtifact(await Programs.Value);
        var path = Path.Combine(RepoRoot.Find(), ArtifactRelativePath);
        var flag = RegenerationFlags.MayCaptureCalls;

        ArtifactRegeneration.VerifyOrRegenerate(
            flag,
            ArtifactRelativePath,
            regenerate: () => expected,
            verify: () =>
            {
                Assert.True(File.Exists(path),
                    $"{ArtifactRelativePath} is missing. Set {flag}=1 and rerun this test to generate it (that run fails by design).");

                var actual = File.ReadAllText(path).ReplaceLineEndings("\n");
                Assert.True(expected == actual,
                    $"{ArtifactRelativePath} is out of date with C#'s current plan-retention gate verdicts. " +
                    $"Set {flag}=1 and rerun this test to regenerate it (that run fails by design), review the diff, and run " +
                    "`lake build KatLangArityLaws` to check the Lean side. " +
                    SemanticExplorerLeanArtifactTests.DescribeFirstDifference(expected, actual));
            },
            afterRegenerating: "run `lake build KatLangArityLaws` to check the Lean side");
    }

    /// <summary>
    /// The partition is exact and nothing is sampled: every program of every corpus is enumerated once, each is
    /// guarded or excluded by one counted rule, and the exclusions are exactly the corpora's own Lean exclusions —
    /// every comparable tree passes preflight without a deferred region and has a derived Lean program.
    /// </summary>
    [Fact]
    public async Task Partition_IsExact_AndExclusionsAreTheCorporaOwn()
    {
        var programs = await Programs.Value;
        Assert.Equal(programs.Count, programs.Select(static p => p.Corpus + ":" + p.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.All(programs, static p => Assert.True((p.LeanReference is null) == (p.Exclusion is not null), p.Corpus + ":" + p.Id));

        var spec = LanguageSpecCorpus.AllCases();
        var explorer = SemanticExplorerCorpus.AllCases();
        var generated = SemanticCorpus.All();
        var generatedIncluded = SemanticGeneratedLeanArtifactTests.IncludedCases(generated);
        var hostParent = HostParentDifferentialCorpus.AllCases();

        Assert.Equal(spec.Count, CountOf(SpecCorpus));
        Assert.Equal(explorer.Count, CountOf(ExplorerCorpus));
        Assert.Equal(SemanticExplorerCorpus.InternalNodeCases().Count, CountOf(ExplorerInternalCorpus));
        // A generated case is one program per member when included, and one program when excluded.
        Assert.Equal(
            generatedIncluded.Sum(static c => c.Members.Length) + (generated.Count - generatedIncluded.Count),
            CountOf(GeneratedCorpus));
        Assert.Equal(hostParent.Count, CountOf(HostParentCorpus));
        Assert.Equal(ModuleDifferentialCorpus.Cases.Count, CountOf(ModuleCorpus));
        Assert.Equal(PlannedLoopTempFamily.Cases.Count, CountOf(LoopTempCorpus));

        Assert.Equal(spec.Count(static c => c.IsLeanRepresentable), Guarded(SpecCorpus));
        Assert.Equal(explorer.Count(static c => c.LeanProgram is not null), Guarded(ExplorerCorpus));
        Assert.Equal(SemanticExplorerCorpus.InternalNodeCases().Count, Guarded(ExplorerInternalCorpus));
        Assert.Equal(generatedIncluded.Sum(static c => c.Members.Length), Guarded(GeneratedCorpus));
        Assert.Equal(hostParent.Count, Guarded(HostParentCorpus));
        Assert.Equal(ModuleDifferentialCorpus.Cases.Count(c => c.Exclusion is null), Guarded(ModuleCorpus));
        Assert.Equal(PlannedLoopTempFamily.Cases.Count, Guarded(LoopTempCorpus));
        Assert.All(Corpora, corpus => Assert.True(Guarded(corpus.Corpus) > 0, corpus.Corpus));

        // The three rules below exclude a program that HAS a Lean program. Each is counted in the artifact's
        // header; the pins move only in a reviewed diff that names the programs.
        RequireExcluded(GateExclusion.RefusedByPreflight, ExpectedRefusedByPreflight);
        RequireExcluded(GateExclusion.DeferredRegion, ExpectedDeferredRegion);
        RequireExcluded(GateExclusion.HandAuthoredLeanProgram, ExpectedHandAuthoredLeanPrograms);

        int CountOf(string corpus) => programs.Count(p => p.Corpus == corpus);
        int Guarded(string corpus) => programs.Count(p => p.Corpus == corpus && p.LeanReference is not null);

        void RequireExcluded(GateExclusion rule, int expected)
        {
            var excluded = programs.Where(p => p.Exclusion == rule).Select(static p => p.Corpus + ":" + p.Id).ToList();
            Assert.True(excluded.Count == expected,
                $"{excluded.Count} corpus program(s) with a Lean program are excluded from the gate agreement by the rule " +
                $"'{Describe(rule)}' (pinned: {expected}): {string.Join(", ", excluded)}. Review them and move the pin.");
        }
    }

    private const int ExpectedRefusedByPreflight = 0;
    private const int ExpectedDeferredRegion = 0;
    private const int ExpectedHandAuthoredLeanPrograms = 0;

    /// <summary>
    /// Coverage ratchet: both verdicts are checked, on every corpus that can produce them, and the guarded totals may
    /// only be RAISED (or lowered in a reviewed diff that deliberately removes corpus cases). The fired programs
    /// include both kinds C# distinguishes: a <c>meta</c> binder and a loop spelling without one.
    /// </summary>
    [Fact]
    public async Task CoverageRatchet_BothVerdictsAreGuardedInEveryCorpusThatHoldsThem()
    {
        var guarded = (await Programs.Value).Where(static p => p.LeanReference is not null).ToList();
        var fired = guarded.Where(static p => p.MayCaptureCalls).ToList();

        Assert.True(guarded.Count >= MinimumGuardedPrograms, $"guarded programs {guarded.Count} < {MinimumGuardedPrograms}");
        Assert.True(fired.Count >= MinimumFiredPrograms, $"programs that may capture calls {fired.Count} < {MinimumFiredPrograms}");
        Assert.True(guarded.Count - fired.Count >= MinimumQuietPrograms,
            $"programs that cannot capture calls {guarded.Count - fired.Count} < {MinimumQuietPrograms}");
        Assert.Contains(fired, static p => p.HasMetaBinder);
        Assert.Contains(fired, static p => !p.HasMetaBinder);
        Assert.All(guarded.Where(p => p.Corpus == LoopTempCorpus),
            p => Assert.True(p.MayCaptureCalls && !p.HasMetaBinder, p.Id));

        foreach (var corpus in new[] { SpecCorpus, ExplorerCorpus, GeneratedCorpus, HostParentCorpus })
        {
            Assert.Contains(guarded, p => p.Corpus == corpus && p.MayCaptureCalls);
            Assert.Contains(guarded, p => p.Corpus == corpus && !p.MayCaptureCalls);
        }
    }

    private const int MinimumGuardedPrograms = 3865;
    private const int MinimumFiredPrograms = 499;
    private const int MinimumQuietPrograms = 3366;

    /// <summary>
    /// Every comparable program has exactly one guard, with its own verdict and corpus definition.
    /// </summary>
    [Fact]
    public async Task GeneratedArtifact_GuardsReconcileWithThePartition()
    {
        var programs = await Programs.Value;
        var guardLines = GenerateArtifact(programs).Split('\n')
            .Where(static line => line.StartsWith("#guard Expr.mayCaptureCalls ", StringComparison.Ordinal));
        var guarded = programs.Where(static p => p.LeanReference is not null).ToList();
        Assert.Equal(guarded.Count, guarded.Select(static p => p.LeanReference).Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(guarded.Select(static p =>
            $"#guard Expr.mayCaptureCalls {p.LeanReference} == {(p.MayCaptureCalls ? "true" : "false")}"), guardLines);
    }

    // Each corpus generator emits an Expr definition followed by its observation guard. Read its
    // full body once so two cases with the same gate verdict cannot be paired with one another.
    private static Dictionary<string, string> ReadProgramDefinitions()
    {
        var definitions = new Dictionary<string, string>(StringComparer.Ordinal);
        string[] paths =
        [
            "lean/LanguageSpecCases.lean",
            "lean/SemanticExplorerCases.lean",
            "lean/CoreTests/SemanticGeneratedCases.lean",
            "lean/CoreTests/HostParentDifferential.lean",
            "lean/CoreTests/ModuleDifferential.lean",
            "lean/CoreTests/PlannedLoopTempFamily.lean",
        ];
        foreach (var path in paths)
        {
            var module = Path.GetFileNameWithoutExtension(path);
            var lines = File.ReadAllLines(Path.Combine(RepoRoot.Find(), path));
            for (var i = 0; i < lines.Length; i++)
            {
                var header = lines[i];
                if (!header.StartsWith("def ", StringComparison.Ordinal) || !header.EndsWith(" : Expr :=", StringComparison.Ordinal))
                    continue;

                var name = header["def ".Length..^" : Expr :=".Length];
                var start = ++i;
                while (i < lines.Length && !lines[i].StartsWith("#guard ", StringComparison.Ordinal))
                    i++;
                Assert.True(i > start && i < lines.Length, $"{path} has no guarded definition body for {name}.");
                definitions.Add($"{module}.{name}", string.Join("\n", lines, start, i - start));
            }
        }

        return definitions;
    }

    // ── The corpus walk ─────────────────────────────────────────────────────

    private static async Task<IReadOnlyList<GateProgram>> BuildProgramsAsync()
    {
        var programs = new List<GateProgram>();
        var definitions = ReadProgramDefinitions();

        foreach (var specCase in LanguageSpecCorpus.AllCases())
        {
            if (specCase.LeanProgram is null)
            {
                programs.Add(Excluded(SpecCorpus, specCase.Id,
                    specCase.Outcome == SpecOutcome.ParseError ? GateExclusion.ParseLevel : GateExclusion.CSharpOnly));
                continue;
            }

            if (specCase.LeanProgramOverride is not null)
            {
                programs.Add(Excluded(SpecCorpus, specCase.Id, GateExclusion.HandAuthoredLeanProgram));
                continue;
            }

            var root = ParseRoot(SpecCorpus, specCase.Id, specCase.Source);
            programs.Add(Decide(SpecCorpus, specCase.Id,
                "LanguageSpecCases.case_" + specCase.Id.Replace('-', '_'), new Expr.AlgorithmExpr(root)));
        }

        foreach (var explorerCase in SemanticExplorerCorpus.AllCases())
        {
            if (explorerCase.LeanProgram is null)
            {
                programs.Add(Excluded(ExplorerCorpus, explorerCase.Id, GateExclusion.ParseLevel));
                continue;
            }

            var root = ParseRoot(ExplorerCorpus, explorerCase.Id, explorerCase.Source);
            programs.Add(Decide(ExplorerCorpus, explorerCase.Id,
                "SemanticExplorerCases.case_" + explorerCase.Id, new Expr.AlgorithmExpr(root)));
        }

        foreach (var internalCase in SemanticExplorerCorpus.InternalNodeCases())
        {
            // The one-slot root the explorer's artifact encodes and its harness evaluates (ObserveAst).
            var root = new Algorithm.User(
                Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: [internalCase.RootOutput()]);
            programs.Add(Decide(ExplorerInternalCorpus, internalCase.Id,
                "SemanticExplorerCases.case_internal__" + internalCase.Id, new Expr.AlgorithmExpr(root)));
        }

        foreach (var generatedCase in SemanticCorpus.All())
        {
            if (!SemanticGeneratedLeanArtifactTests.IsValid(generatedCase))
            {
                programs.Add(Excluded(GeneratedCorpus, generatedCase.CaseId, GateExclusion.InvalidFrontEnd));
                continue;
            }

            if (SemanticGeneratedLeanArtifactTests.ExcludedById.ContainsKey(generatedCase.CaseId))
            {
                programs.Add(Excluded(GeneratedCorpus, generatedCase.CaseId, GateExclusion.ExcludedById));
                continue;
            }

            // The identity-prelude members the SEM-2C artifact encodes: the base, then each transformation.
            var baseRoot = ParseRoot(GeneratedCorpus, generatedCase.CaseId, SemanticGeneratedLeanArtifactTests.BuildMember(generatedCase));
            programs.Add(Decide(GeneratedCorpus, generatedCase.CaseId,
                "SemanticGeneratedCases." + SemanticGeneratedLeanArtifactTests.LeanName(generatedCase.CaseId),
                new Expr.AlgorithmExpr(baseRoot)));
            foreach (var member in generatedCase.Members.Skip(1))
            {
                var id = SemanticGeneratedLeanArtifactTests.MemberListEntry(generatedCase.CaseId, member.Role);
                var memberRoot = ParseRoot(GeneratedCorpus, id, SemanticGeneratedLeanArtifactTests.IdentityPrelude + member.Source);
                programs.Add(Decide(GeneratedCorpus, id,
                    "SemanticGeneratedCases." + SemanticGeneratedLeanArtifactTests.MemberLeanName(generatedCase.CaseId, member.Role),
                    new Expr.AlgorithmExpr(memberRoot)));
            }
        }

        // Every host-parent case has a Lean definition of its ONE program graph, a known-divergence case included:
        // a divergence is about what the two evaluators observe, and the gate reads the tree.
        foreach (var hostCase in HostParentDifferentialCorpus.AllCases())
            programs.Add(Decide(HostParentCorpus, hostCase.Id, "HostParentDifferential." + hostCase.LeanName, hostCase.Program));

        foreach (var fixture in ModuleDifferentialCorpus.Cases)
        {
            if (fixture.Exclusion is not null)
            {
                programs.Add(Excluded(ModuleCorpus, fixture.Id, GateExclusion.CSharpOnly));
                continue;
            }

            var parsed = await SourceProvenance.ParseValidAsync(fixture.Source, ModuleDifferentialCorpus.Server().Options());
            programs.Add(Decide(ModuleCorpus, fixture.Id, "ModuleDifferential." + fixture.Id, new Expr.AlgorithmExpr(parsed.Root)));
        }

        foreach (var loopCase in PlannedLoopTempFamily.Cases)
        {
            var root = ParseRoot(LoopTempCorpus, loopCase.Id, loopCase.Source);
            programs.Add(Decide(LoopTempCorpus, loopCase.Id,
                "PlannedLoopTempFamily." + loopCase.LeanName, new Expr.AlgorithmExpr(root)));
        }

        return programs.AsReadOnly();

        GateProgram Decide(string corpus, string id, string leanReference, Expr tree)
        {
            var rejection = AstStructuralPreflight.CheckAdmittedProgram(
                tree, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines, out var facts);
            if (rejection is not null)
                return Excluded(corpus, id, GateExclusion.RefusedByPreflight);
            if (facts.HasDeferredModuleRegion)
                return Excluded(corpus, id, GateExclusion.DeferredRegion);

            var encoding = corpus == HostParentCorpus
                ? LeanAstEncoder.EncodeExpr(tree)
                : LeanAstEncoder.EncodeProgram(((Expr.AlgorithmExpr)tree).Algorithm);
            Assert.True(definitions.TryGetValue(leanReference, out var definition),
                $"{corpus}:{id}: the Lean corpus has no definition {leanReference}.");
            Assert.True(definition == "  " + encoding,
                $"{corpus}:{id}: the admitted tree differs from the Lean definition {leanReference}.");
            return new GateProgram(corpus, id, leanReference, facts.MayCaptureCalls, facts.HasMetaBinder, Exclusion: null);
        }
    }

    private static Algorithm ParseRoot(string corpus, string id, string source)
    {
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
        {
            throw new InvalidOperationException(
                $"{corpus}:{id} has a Lean program but its source does not parse cleanly: "
                + string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message.Split('\n')[0])));
        }

        return parsed.Root;
    }

    private static GateProgram Excluded(string corpus, string id, GateExclusion exclusion)
        => new(corpus, id, LeanReference: null, MayCaptureCalls: false, HasMetaBinder: false, exclusion);

    // ── The artifact ────────────────────────────────────────────────────────

    private static string GenerateArtifact(IReadOnlyList<GateProgram> programs)
    {
        var guarded = programs.Where(static p => p.LeanReference is not null).ToList();
        var fired = guarded.Count(static p => p.MayCaptureCalls);

        var builder = new StringBuilder();
        builder.Append($"""
            import KatLangArityLaws.MayCaptureCalls
            import LanguageSpecCases
            import SemanticExplorerCases
            import CoreTests.SemanticGeneratedCases
            import CoreTests.HostParentDifferential
            import CoreTests.ModuleDifferential
            import CoreTests.PlannedLoopTempFamily

            /-!
            GENERATED FILE - DO NOT EDIT BY HAND.

            Lean's program gate against C#'s gate of invocation-plan retention (ledger E-21).

            C# retains invocation plans only in a run whose admitted program may capture calls
            (J7, `AstStructuralPreflight.MayCaptureCalls`, decided by the admission walk
            `CheckAdmittedProgram`). `Expr.mayCaptureCalls` (`MayCaptureCalls.lean`) is the Lean form of
            that gate. Each `#guard` below pins C#'s verdict on one program of a differential corpus
            (dotnet/tests/KatLang.Tests/MayCaptureCallsLeanArtifactTests.cs): a failing guard is a program on
            which the two gates disagree.

            The Lean program of a guard is the definition the corpus's own generated module holds for
            the tree C# decided (imported above; no program is re-emitted here), so both verdicts are
            of the same elaborated tree. This file depends on no proof.

            Partition (machine-checked by the `*.length` guards below; nothing is sampled):
            - corpus programs: {Count(programs.Count)}
            - guarded: {Count(guarded.Count)} ({Count(fired)} may capture calls, {Count(guarded.Count - fired)} cannot)
            - excluded: {Count(programs.Count - guarded.Count)}

            """.ReplaceLineEndings("\n"));

        foreach (var (corpus, _, _) in Corpora)
        {
            var ofCorpus = programs.Where(p => p.Corpus == corpus).ToList();
            var guardedOfCorpus = ofCorpus.Where(static p => p.LeanReference is not null).ToList();
            builder.Append(CultureInfo.InvariantCulture,
                $"  {corpus}: {Count(ofCorpus.Count)} programs, {Count(guardedOfCorpus.Count)} guarded " +
                $"({Count(guardedOfCorpus.Count(static p => p.MayCaptureCalls))} may capture calls)");
            foreach (var group in ofCorpus.Where(static p => p.Exclusion is not null).GroupBy(static p => p.Exclusion!.Value).OrderBy(static g => g.Key))
                builder.Append(CultureInfo.InvariantCulture, $", {Count(group.Count())} excluded: {Describe(group.Key)}");
            builder.Append('\n');
        }

        builder.Append("""

            Exclusion rules that currently exclude nothing: a tree the structural preflight refuses (no
            run admits it); a tree that holds a deferred module region (C#'s first clause; Lean has no
            deferred region); a hand-authored Lean program.

            Regenerate from the repo root with:
              $env:KATLANG_REGENERATE_MAY_CAPTURE_CALLS = "1"
              dotnet test ./dotnet/tests/KatLang.Tests/KatLang.Tests.csproj --filter MayCaptureCallsLeanArtifact
            -/

            namespace KatLang.MayCaptureCallsCorpus
            open KatLang


            """.ReplaceLineEndings("\n"));

        foreach (var (corpus, _, listName) in Corpora)
        {
            var guardedOfCorpus = guarded.Where(p => p.Corpus == corpus).ToList();
            builder.Append(CultureInfo.InvariantCulture, $"/-! ## {corpus} -/\n\n");
            foreach (var program in guardedOfCorpus)
                builder.Append(CultureInfo.InvariantCulture, $"#guard Expr.mayCaptureCalls {program.LeanReference} == {(program.MayCaptureCalls ? "true" : "false")}\n");

            builder.Append('\n');
            builder.Append("/-- The guarded programs of this corpus, listed by the loop that emits the guards above; the\n");
            builder.Append("    expected totals are computed independently from the corpus partition and from C#'s verdicts. -/\n");
            builder.Append(CultureInfo.InvariantCulture, $"def {listName} : List Expr := [\n");
            builder.Append(string.Join(",\n", guardedOfCorpus.Select(static p => "  " + p.LeanReference)));
            builder.Append("\n]\n");
            builder.Append(CultureInfo.InvariantCulture, $"#guard {listName}.length == {guardedOfCorpus.Count}\n");
            builder.Append(CultureInfo.InvariantCulture,
                $"#guard ({listName}.filter Expr.mayCaptureCalls).length == {guardedOfCorpus.Count(static p => p.MayCaptureCalls)}\n\n");
        }

        builder.Append(CultureInfo.InvariantCulture, $"-- {guarded.Count} gate guards over {programs.Count} corpus programs.\n");
        builder.Append("end KatLang.MayCaptureCallsCorpus\n");
        return builder.ToString();

        static string Count(int value) => value.ToString(CultureInfo.InvariantCulture);
    }

    private static string Describe(GateExclusion exclusion) => exclusion switch
    {
        GateExclusion.ParseLevel => "the source does not parse (Lean has no surface parser)",
        GateExclusion.CSharpOnly => "C#-only by the corpus's reviewed reason",
        GateExclusion.InvalidFrontEnd => "invalid front-end programs (Lean has no surface front end)",
        GateExclusion.ExcludedById => "excluded from the SEM-2C artifact by exact id",
        GateExclusion.HandAuthoredLeanProgram => "the Lean program is hand-authored",
        GateExclusion.RefusedByPreflight => "the structural preflight refuses the tree",
        GateExclusion.DeferredRegion => "the tree holds a deferred module region",
        _ => throw new InvalidOperationException($"Unhandled gate exclusion {exclusion}."),
    };
}
