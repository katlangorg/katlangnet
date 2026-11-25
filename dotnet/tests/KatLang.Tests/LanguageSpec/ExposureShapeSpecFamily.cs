namespace KatLang.Tests.LanguageSpec;

/// <summary>The .NET-specific deferred module companion to conformance/features/exposure-shapes.json.</summary>
internal static class ExposureShapeSpecFamily
{
    internal enum Container
    {
        Member,
        Reference,
        Carrier,
        InlineHead,
    }

    internal enum Capture
    {
        OutputRow,
        Member,
    }

    internal const string InsideRows = "F(5), F(7)";
    internal const string OutsideAfterCall = "F(5), F.A";
    internal const string OutsideBeforeCall = "F.A, F(5)";

    private static IReadOnlyList<string> SubDeclaration(Capture capture)
        => Block("public Sub", capture == Capture.OutputRow ? ["public Q = 1", "y"] : ["public Q = y", "0"]);

    private static IReadOnlyList<string> Block(string head, IReadOnlyList<string> body)
        => [head + " = {", .. Indent(body), "}"];

    private static IReadOnlyList<string> Indent(IReadOnlyList<string> lines)
        => [.. lines.Select(line => "  " + line)];

    // `prefix` before the first line of a written target and `suffix` after its last one.
    private static IReadOnlyList<string> Written(string prefix, IReadOnlyList<string> target, string suffix = "")
    {
        var lines = target.ToList();
        lines[0] = prefix + lines[0];
        lines[^1] += suffix;
        return lines;
    }

    private static string Slug(Container container)
        => container switch
        {
            Container.Member => "member",
            Container.Reference => "reference",
            Container.Carrier => "carrier",
            Container.InlineHead => "inline-head",
            _ => throw new InvalidOperationException(container.ToString()),
        };

    private static string Slug(Capture capture)
        => capture == Capture.OutputRow ? "row-capture" : "member-capture";

    // ── The deferred-branch companion (C#-only, async; run by ExposureShapeDeferredRouteTests) ──────
    //
    // ROUTE: `A = D(1)`, where `D` is a clause family of `F` whose second clause LOADS A MODULE ON
    // DEMAND and reads `Q` in its body:
    //
    //     F(y) = {
    //       …                          -- the container, when it is declared at the site
    //       D(0) = 0
    //       D(n) = {
    //         open 'https://modules.example/….kat'
    //         <container>.Sub.Q + …
    //       }
    //       A = D(1)
    //       A
    //     }
    //
    // The declarations around a load-bearing clause are classified BEFORE its module exists, from the
    // clause's provisional body resolved as if the module were empty; a materialized body that needs
    // an enclosing binding the family never charged is refused when the branch is selected
    // (`DeferredBranchForwardsEnclosingParameter`). The matrix crosses that route with:
    //
    // * the four CONTAINERS and the two CAPTURE positions of the shared exposure-shape family;
    // * a PLACEMENT of the container — at the SITE (declared in `F`, so the branch's read of `y`
    //   through it is written in the program and charged; the module contributes the self-contained
    //   `K`), or in the MODULE the branch loads (so only the module decides that `Q` needs `y`: the
    //   uncharged, inadmissible shape). An inline block head is written in the branch itself and has
    //   no module placement;
    // * the access sites and row orders of the shared exposure-shape family;
    // * three VARIANTS of each cell: the SELECTED branch (the module is downloaded and the unit
    //   materialized), its EAGER TWIN (the module held at the root and opened through the holder, so
    //   nothing is deferred: the oracle of every accepted shape), and the NEVER-SELECTED control
    //   (`A = D(0)`: no download, no module work, no judgement).
    //
    // The EXPECTATIONS are hand-written from the rule, one row per cell (DeferredCells), never taken
    // from a run.

    /// <summary>Where the container of a deferred cell is declared.</summary>
    internal enum Placement
    {
        /// <summary>In <c>F</c>, beside the family: the branch's dependence on <c>y</c> is written in the program.</summary>
        Site,

        /// <summary>In the module the branch loads on demand: only the module decides the dependence.</summary>
        Module,
    }

    internal enum DeferredVariant
    {
        Selected,
        EagerTwin,
        NeverSelected,
    }

    /// <summary>One run's expected outcome (<see cref="DeferredOutcomeOf"/>'s text) and its number of module downloads.</summary>
    internal sealed record Expected(string Outcome, int Downloads);

    /// <summary>The expected outcomes of one variant of a cell, per root-row program.</summary>
    internal sealed record RowOutcomes(Expected Inside, Expected OutsideAfterCall, Expected OutsideBeforeCall);

    /// <summary>One cell of the deferred companion with its HAND-WRITTEN expectations.</summary>
    internal sealed record DeferredCell(
        Container Container,
        Capture Capture,
        Placement Placement,
        RowOutcomes Selected,
        RowOutcomes EagerTwin,
        RowOutcomes NeverSelected);

    internal const string DeferredLocalOnly = "error LocalOnlyProperty";
    internal const string DeferredForwardingRefused = "error DeferredBranchForwardsEnclosingParameter";

    // SITE placement. `A` reaches the owner's `y` through a route written in the program, so the
    // family charges it and `A` is local-only: one value per call inside, refused outside in both
    // row orders. Outside AFTER a call the first row already selected the branch (one download);
    // outside BEFORE a call the refused access is the first row, so nothing was selected yet. The
    // eager twin loads its holder before the run, whatever the rows do. The never-selected control
    // keeps the classification (it never depends on what a run selects) and downloads nothing.
    private static readonly RowOutcomes SiteRowCaptureSelected = new(new("ok 1, 1", 1), new(DeferredLocalOnly, 1), new(DeferredLocalOnly, 0));
    private static readonly RowOutcomes SiteRowCaptureEager = new(new("ok 1, 1", 1), new(DeferredLocalOnly, 1), new(DeferredLocalOnly, 1));
    private static readonly RowOutcomes SiteMemberCaptureSelected = new(new("ok 5, 7", 1), new(DeferredLocalOnly, 1), new(DeferredLocalOnly, 0));
    private static readonly RowOutcomes SiteMemberCaptureEager = new(new("ok 5, 7", 1), new(DeferredLocalOnly, 1), new(DeferredLocalOnly, 1));
    private static readonly RowOutcomes SiteNeverSelected = new(new("ok 0, 0", 0), new(DeferredLocalOnly, 0), new(DeferredLocalOnly, 0));

    // MODULE placement, MEMBER capture. In module text the free `y` of `Q` is `Q`'s own implicit
    // parameter, so the branch's formula would forward the enclosing `y` to a member of the module
    // it loads on demand. Nothing in the program charged that, so `A` is exported, and EVERY
    // selection of the branch is refused when it materializes — inside a call and from outside one
    // alike, with the download charged. The eager twin forwards `y` as usual: `A` is local-only
    // there. Never selected, the branch is never judged: `A` stays the exported `0`.
    private static readonly RowOutcomes ModuleMemberCaptureSelected = new(new(DeferredForwardingRefused, 1), new(DeferredForwardingRefused, 1), new(DeferredForwardingRefused, 1));
    private static readonly RowOutcomes ModuleMemberCaptureEager = new(new("ok 5, 7", 1), new(DeferredLocalOnly, 1), new(DeferredLocalOnly, 1));
    private static readonly RowOutcomes ModuleNeverSelected = new(new("ok 0, 0", 0), new("ok 0, 0", 0), new("ok 0, 0", 0));

    // MODULE placement, OUTPUT-ROW capture. In module text the free `y` of `Sub`'s output row is
    // `Sub`'s own parameter; reading the self-contained member `Q` neither calls `Sub` nor needs an
    // enclosing binding. The shape is admissible and `A` is exported: the value 1 from every access
    // site, exactly as in the eager twin.
    private static readonly RowOutcomes ModuleRowCaptureSelected = new(new("ok 1, 1", 1), new("ok 1, 1", 1), new("ok 1, 1", 1));
    private static readonly RowOutcomes ModuleRowCaptureEager = new(new("ok 1, 1", 1), new("ok 1, 1", 1), new("ok 1, 1", 1));

    /// <summary>The reviewed expectation table of the deferred-branch route.</summary>
    internal static readonly IReadOnlyList<DeferredCell> DeferredCells =
    [
        new(Container.Member, Capture.OutputRow, Placement.Site, SiteRowCaptureSelected, SiteRowCaptureEager, SiteNeverSelected),
        new(Container.Member, Capture.Member, Placement.Site, SiteMemberCaptureSelected, SiteMemberCaptureEager, SiteNeverSelected),
        new(Container.Reference, Capture.OutputRow, Placement.Site, SiteRowCaptureSelected, SiteRowCaptureEager, SiteNeverSelected),
        new(Container.Reference, Capture.Member, Placement.Site, SiteMemberCaptureSelected, SiteMemberCaptureEager, SiteNeverSelected),
        new(Container.Carrier, Capture.OutputRow, Placement.Site, SiteRowCaptureSelected, SiteRowCaptureEager, SiteNeverSelected),
        new(Container.Carrier, Capture.Member, Placement.Site, SiteMemberCaptureSelected, SiteMemberCaptureEager, SiteNeverSelected),
        new(Container.InlineHead, Capture.OutputRow, Placement.Site, SiteRowCaptureSelected, SiteRowCaptureEager, SiteNeverSelected),
        new(Container.InlineHead, Capture.Member, Placement.Site, SiteMemberCaptureSelected, SiteMemberCaptureEager, SiteNeverSelected),

        new(Container.Member, Capture.OutputRow, Placement.Module, ModuleRowCaptureSelected, ModuleRowCaptureEager, ModuleNeverSelected),
        new(Container.Member, Capture.Member, Placement.Module, ModuleMemberCaptureSelected, ModuleMemberCaptureEager, ModuleNeverSelected),
        new(Container.Reference, Capture.OutputRow, Placement.Module, ModuleRowCaptureSelected, ModuleRowCaptureEager, ModuleNeverSelected),
        new(Container.Reference, Capture.Member, Placement.Module, ModuleMemberCaptureSelected, ModuleMemberCaptureEager, ModuleNeverSelected),
        new(Container.Carrier, Capture.OutputRow, Placement.Module, ModuleRowCaptureSelected, ModuleRowCaptureEager, ModuleNeverSelected),
        new(Container.Carrier, Capture.Member, Placement.Module, ModuleMemberCaptureSelected, ModuleMemberCaptureEager, ModuleNeverSelected),
    ];

    internal const string DeferredModuleHost = "modules.example";

    internal static string DeferredModuleUrl(string name) => $"https://{DeferredModuleHost}/{name}.kat";

    /// <summary>The module a cell's branch loads: the shared self-contained one, or the cell's own container.</summary>
    internal static string DeferredModuleName(DeferredCell cell)
        => cell.Placement == Placement.Site ? "exposure-k" : $"exposure-{Slug(cell.Container)}-{Slug(cell.Capture)}";

    /// <summary>Every module text of the companion, by name: generated, like the programs.</summary>
    internal static IReadOnlyDictionary<string, string> DeferredModules()
    {
        var modules = new Dictionary<string, string>(StringComparer.Ordinal) { ["exposure-k"] = "public K = 0\n" };
        foreach (var cell in DeferredCells)
        {
            if (cell.Placement != Placement.Module)
                continue;

            var sub = SubDeclaration(cell.Capture);
            IReadOnlyList<string> lines = cell.Container switch
            {
                Container.Member => Block("public Lib", [.. sub, "0"]),
                Container.Reference => [.. Block("public Lib", [.. sub, "0"]), "public Ref = Lib"],
                Container.Carrier => [.. Block("public Base", ["0"]), .. Block("public Car", [.. sub, "Base"])],
                _ => throw new InvalidOperationException($"{cell.Container} has no module placement."),
            };
            modules[DeferredModuleName(cell)] = string.Join("\n", lines) + "\n";
        }

        return modules;
    }

    /// <summary>The program of one deferred cell and variant, followed by the given root output rows.</summary>
    internal static string DeferredProgram(DeferredCell cell, DeferredVariant variant, string rows)
    {
        var declarations = new List<string>();
        IReadOnlyList<string> target;
        switch (cell.Container)
        {
            case Container.Member:
                if (cell.Placement == Placement.Site)
                    declarations.AddRange(Block("Lib", [.. SubDeclaration(cell.Capture), "0"]));
                target = ["Lib.Sub"];
                break;
            case Container.Reference:
                if (cell.Placement == Placement.Site)
                {
                    declarations.AddRange(Block("Lib", [.. SubDeclaration(cell.Capture), "0"]));
                    declarations.Add("Ref = Lib");
                }

                target = ["Ref.Sub"];
                break;
            case Container.Carrier:
                if (cell.Placement == Placement.Site)
                {
                    declarations.AddRange(Block("Base", ["0"]));
                    declarations.AddRange(Block("Car", [.. SubDeclaration(cell.Capture), "Base"]));
                }

                target = ["Car.Sub"];
                break;
            case Container.InlineHead:
                target = ["{", .. Indent(SubDeclaration(cell.Capture)), "}.Sub"];
                break;
            default:
                throw new InvalidOperationException(cell.Container.ToString());
        }

        var url = DeferredModuleUrl(DeferredModuleName(cell));
        var open = variant == DeferredVariant.EagerTwin ? "open Hm" : $"open '{url}'";
        // At the site the selected branch also reads the module's own `K`, so its value needs the
        // materialized unit; a module-placed container is itself what the unit provides.
        var read = Written(string.Empty, target, cell.Placement == Placement.Site ? ".Q + K" : ".Q + 0");
        declarations.Add("D(0) = 0");
        declarations.AddRange(["D(n) = {", .. Indent([open, .. read]), "}"]);
        declarations.Add(variant == DeferredVariant.NeverSelected ? "A = D(0)" : "A = D(1)");

        IEnumerable<string> lines = ["F(y) = {", .. Indent([.. declarations, "A"]), "}", rows];
        var program = string.Join("\n", lines);
        return variant == DeferredVariant.EagerTwin ? $"Hm = load('{url}')\n{program}" : program;
    }

    internal static string DeferredSlug(DeferredCell cell)
        => $"{Slug(cell.Container)}-{Slug(cell.Capture)}-{(cell.Placement == Placement.Site ? "site" : "module")}";
}
