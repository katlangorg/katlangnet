namespace KatLang.Tests;

internal enum ModuleLeanExclusion { FrontEndRejected, LoadRefused, DeferredRegion }

internal sealed record ModuleDifferentialCase(
    string Id, string Rule, string Source, string Expected, string[] Fetches,
    ModuleLeanExclusion? Exclusion = null, DiagnosticCode? Diagnostic = null, SourceSpan? Span = null,
    SharedErrorPayload? Payload = null, string[]? ParseFetches = null);

/// <summary>Hand-pinned examples from ModuleIdentityTests and ModuleHygieneTests.</summary>
internal static class ModuleDifferentialCorpus
{
    private const string Tick = "https://mods.test/t.kat";
    private const string TickAlias = "https://MODS.test:443/./t.kat#alias";
    private const string TickTwin = "https://mods.test/t2.kat";
    private const string Nested = "https://mods.test/nest.kat";
    private const string Sum = "https://mods.test/sum.kat";
    private const string F = "https://mods.test/f.kat";
    private const string FTwin = "https://mods.test/f2.kat";
    private const string Missing = "https://mods.test/missing.kat";
    private const string TickText = "public T = tick()";
    private const string SumText = "public V = sum((1, 2))";
    private const string FText = "public F(v) = v * 10";

    private static readonly (string Url, string Source)[] Files =
    [
        (Tick, TickText), (TickTwin, TickText), (Nested, $"S = load('{Tick}')\npublic T2 = S.T"),
        (Sum, SumText), (F, FText), (FTwin, FText),
    ];

    internal static ModuleRouteAgreement.Modules Server(bool reverseFiles = false)
        => new(reverseFiles ? Files.Reverse().ToArray() : Files);

    private const string DirectHolder = $"A = load('{TickAlias}')";
    private const string NestedHolder = $"N = load('{Nested}')";
    private const string ReadMembers = "A.T, N.T2, A.T()";
    private const string CallerShadow = "sum(xs) = 999";
    private const string Fallback = "K(q) = q.F\nK(1)";
    private static string OpenProviders(string second, string use)
        => $"open A, B\nA = load('{F}')\nB = load('{second}')\n{use}";

    // Each URL in Fetches denotes one request. The parse and run use independent servers.
    internal static readonly IReadOnlyList<ModuleDifferentialCase> Cases =
    [
        new("same_url", "Q-32 I-U", $"{DirectHolder}\n{NestedHolder}\n{ReadMembers}",
            "ok raw=S[1, 1, 2] n=3", [Tick, Nested]),
        new("nested_first", "Q-32 I-U", $"{NestedHolder}\n{DirectHolder}\n{ReadMembers}",
            "ok raw=S[1, 1, 2] n=3", [Tick, Nested]),
        new("distinct_url", "Q-32 I-U", $"A = load('{TickTwin}')\n{NestedHolder}\n{ReadMembers}",
            "ok raw=S[1, 2, 3] n=3", [TickTwin, Nested, Tick]),

        new("module_shadow", "Q-31 H-P", $"{CallerShadow}\nM = load('{Sum}')\nM.V", "ok raw=3 n=1", [Sum]),
        new("inline_shadow", "Q-31 H-P", $"{CallerShadow}\nM = {{ {SumText} }}\nM.V", "ok raw=999 n=1", []),

        new("one_provider", "Q-32 I-U, Q-19 D-I", OpenProviders(F, Fallback), "ok raw=10 n=1", [F]),
        new("two_providers", "Q-32 I-U, Q-29 A-U", OpenProviders(FTwin, Fallback), "err ambiguousOpen", [F, FTwin],
            Payload: new("ambiguousOpen", ["F"], [])),
        new("written_ambiguity", "Q-29 A-U", OpenProviders(FTwin, "F"), "parse", [F, FTwin],
            ModuleLeanExclusion.FrontEndRejected, DiagnosticCode.AmbiguousOpen, new(4, 1, 4, 2)),
        new("missing_module", "load refusal", $"M = load('{Missing}')\nM.T", "parse", [Missing],
            ModuleLeanExclusion.LoadRefused, DiagnosticCode.LoadFetchFailed, new(1, 5, 1, 42)),
        new("selected_branch", "Q-71", $"F(0) = 0\nF(k) = {{\n    M = load('{Tick}')\n    M.T + k * 0\n}}\nF(1)",
            "ok raw=1 n=1", [Tick], ModuleLeanExclusion.DeferredRegion, ParseFetches: []),
    ];
}
