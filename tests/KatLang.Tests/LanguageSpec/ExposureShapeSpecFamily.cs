namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// The EXPOSURE-SHAPE family of the language spec (EXPORTED-DETACHED, November 2026).
///
/// <para>A property that reaches an input of its enclosing owner's call is LOCAL-ONLY: it has
/// one value per activation of that owner, and it is refused from outside the owner. The
/// front end decides that statically, by charging the reads and access checks of every route
/// the property takes. Both evaluators ENFORCE the answer — an exported property is evaluated
/// detached from the activations that exist when its evaluation starts — so a route the
/// classification misses is no longer a value shared across calls: the program is refused
/// (<c>unknownName</c>, <c>localOnlyProperty</c>). Every case here is therefore an
/// exposure-completeness test in C# and in Lean: its INSIDE program has the per-activation
/// values only when the route was charged, and its OUTSIDE programs are refused in both row
/// orders only when the property was classified local-only.</para>
///
/// <para>The SOURCES are generated from four dimensions, so that no cell of the matrix is
/// forgotten; the EXPECTATIONS are hand-written, one row per cell
/// (<see cref="Cells"/>), and are never derived from an evaluator.</para>
/// <list type="bullet">
/// <item><b>Container</b> — what holds <c>Sub</c>, the algorithm whose member <c>Q</c> is read:
/// a member of a block, a transparent reference to that block, a structural forwarding
/// carrier's own member, an inline block head.</item>
/// <item><b>Route</b> — how <c>A</c> reaches <c>Q</c>: a dot path, a dotted <c>open</c> in
/// <c>A</c>'s own body, an <c>open</c> of a reference, an <c>open</c> of the enclosing
/// level.</item>
/// <item><b>Capture position</b> — where <c>Sub</c> reads the owner's parameter <c>y</c>: its
/// output row (selecting <c>Sub</c> is then the access check that requires <c>y</c>; the value
/// read is <c>1</c>) or the member <c>Q</c> itself (the value read is <c>y</c>).</item>
/// <item><b>Access site and row order</b> — inside the owner (<c>F(5), F(7)</c>), and outside
/// it after and before a call (<c>F(5), F.A</c>; <c>F.A, F(5)</c>).</item>
/// </list>
/// <para>Two cells have no evaluation at all: an inline block written directly as an
/// <c>open</c> target is no part of the opening body's lexical chain, so the <c>y</c> in the
/// output row of its <c>Sub</c> is <c>Sub</c>'s own parameter, and a provider that takes a
/// parameter cannot be opened (<c>IllegalInOpen</c>, a front-end refusal). Their expectation is
/// that diagnostic; the member capture of the same shape evaluates, and so does the same
/// block behind a reference (<c>L = { … }.Sub</c>, <c>open L</c>).</para>
/// <para>THE DEFERRED-BRANCH ROUTE of the design's matrix is the ASYNC COMPANION at the end of this
/// file (<see cref="DeferredCells"/>): <c>A</c> reads <c>Q</c> inside a clause that loads a module on
/// demand. It needs a module downloader and <c>KatLangEngine.RunAsync</c>, and Lean has no
/// deferred-region model, so it is C#-only and no part of the Lean-comparable spec corpus above; it
/// is run, with its own coverage checks, by <c>ExposureShapeDeferredRouteTests</c>.
/// (<c>DeferredBranchForwardingRefusalTests</c> pins the forwarding refusal's own rule — its routes,
/// wording and positions — and does not cross this matrix's containers, capture positions, access
/// sites and row orders.)</para>
/// </summary>
internal static class ExposureShapeSpecFamily
{
    internal enum Container
    {
        Member,
        Reference,
        Carrier,
        InlineHead,
    }

    internal enum Route
    {
        DotPath,
        DottedOpen,
        OpenOfReference,
        EnclosingOpen,
    }

    internal enum Capture
    {
        OutputRow,
        Member,
    }

    /// <summary>
    /// One cell of the matrix with its HAND-WRITTEN expectations: the raw value of
    /// <c>F(5), F(7)</c>, and the error category of <c>F(5), F.A</c> and of <c>F.A, F(5)</c> —
    /// or, for a shape the front end refuses, the fragment of its <c>IllegalInOpen</c>
    /// diagnostic (<see cref="RefusedOpen"/>), which every row order of the cell then reports.
    /// </summary>
    internal sealed record Cell(Container Container, Route Route, Capture Capture, string InsideRaw, string OutsideError)
    {
        internal bool IsRefusedOpen => InsideRaw == RefusedOpen;
    }

    private const string PerCallOne = "S[1, 1]";
    private const string PerCallValue = "S[5, 7]";
    private const string Refused = "localOnlyProperty";

    /// <summary>The front end's refusal of an open provider that takes a parameter.</summary>
    internal const string RefusedOpen = "cannot be opened because open providers must have an empty effective parameter list (found: y)";

    /// <summary>
    /// The reviewed expectation table. An output-row capture makes the read value the constant
    /// <c>1</c> of each call; a member capture makes it that call's own <c>y</c>. Outside the
    /// owner every cell is the refusal that names <c>A</c>, whichever row runs first.
    /// </summary>
    internal static readonly IReadOnlyList<Cell> Cells =
    [
        new(Container.Member, Route.DotPath, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Member, Route.DotPath, Capture.Member, PerCallValue, Refused),
        new(Container.Member, Route.DottedOpen, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Member, Route.DottedOpen, Capture.Member, PerCallValue, Refused),
        new(Container.Member, Route.OpenOfReference, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Member, Route.OpenOfReference, Capture.Member, PerCallValue, Refused),
        new(Container.Member, Route.EnclosingOpen, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Member, Route.EnclosingOpen, Capture.Member, PerCallValue, Refused),

        new(Container.Reference, Route.DotPath, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Reference, Route.DotPath, Capture.Member, PerCallValue, Refused),
        new(Container.Reference, Route.DottedOpen, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Reference, Route.DottedOpen, Capture.Member, PerCallValue, Refused),
        new(Container.Reference, Route.OpenOfReference, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Reference, Route.OpenOfReference, Capture.Member, PerCallValue, Refused),
        new(Container.Reference, Route.EnclosingOpen, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Reference, Route.EnclosingOpen, Capture.Member, PerCallValue, Refused),

        new(Container.Carrier, Route.DotPath, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Carrier, Route.DotPath, Capture.Member, PerCallValue, Refused),
        new(Container.Carrier, Route.DottedOpen, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Carrier, Route.DottedOpen, Capture.Member, PerCallValue, Refused),
        new(Container.Carrier, Route.OpenOfReference, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Carrier, Route.OpenOfReference, Capture.Member, PerCallValue, Refused),
        new(Container.Carrier, Route.EnclosingOpen, Capture.OutputRow, PerCallOne, Refused),
        new(Container.Carrier, Route.EnclosingOpen, Capture.Member, PerCallValue, Refused),

        new(Container.InlineHead, Route.DotPath, Capture.OutputRow, PerCallOne, Refused),
        new(Container.InlineHead, Route.DotPath, Capture.Member, PerCallValue, Refused),
        new(Container.InlineHead, Route.DottedOpen, Capture.OutputRow, RefusedOpen, RefusedOpen),
        new(Container.InlineHead, Route.DottedOpen, Capture.Member, PerCallValue, Refused),
        new(Container.InlineHead, Route.OpenOfReference, Capture.OutputRow, PerCallOne, Refused),
        new(Container.InlineHead, Route.OpenOfReference, Capture.Member, PerCallValue, Refused),
        new(Container.InlineHead, Route.EnclosingOpen, Capture.OutputRow, RefusedOpen, RefusedOpen),
        new(Container.InlineHead, Route.EnclosingOpen, Capture.Member, PerCallValue, Refused),
    ];

    internal const string InsideRows = "F(5), F(7)";
    internal const string OutsideAfterCall = "F(5), F.A";
    internal const string OutsideBeforeCall = "F.A, F(5)";

    /// <summary>The two spec cases of every cell: inside the owner, and outside it.</summary>
    internal static IEnumerable<SpecCase> Cases()
    {
        foreach (var cell in Cells)
        {
            var shape = $"{Slug(cell.Container)}-{Slug(cell.Route)}-{Slug(cell.Capture)}";
            var description = $"{Describe(cell.Container)}, {Describe(cell.Route)}, {Describe(cell.Capture)}";
            if (cell.IsRefusedOpen)
            {
                yield return new SpecCase
                {
                    Id = $"exposure-shape-{shape}-refused-open",
                    Category = "access-boundaries",
                    Source = Program(cell, InsideRows),
                    Outcome = SpecOutcome.ParseError,
                    ExpectedParseDiagnosticFragment = RefusedOpen,
                    ExpectedDiagnosticCode = DiagnosticCode.IllegalInOpen,
                    Notes = FamilyNote + " A front-end rejection, so no elaborated Lean program exists.",
                    Explanation = $"Exposure shape ({description}): an inline block written directly as an `open` "
                        + "target is not inside the opening body's lexical chain, so the `y` its `Sub` reads in the "
                        + "output row is `Sub`'s own parameter, and a provider that takes a parameter cannot be "
                        + "opened. The shape is refused before any evaluation; behind a reference (`L = { … }.Sub`, "
                        + "`open L`) the same block is inside `F` and evaluates.",
                };
                continue;
            }

            yield return new SpecCase
            {
                Id = $"exposure-shape-{shape}-inside",
                Category = "access-boundaries",
                Source = Program(cell, InsideRows),
                Outcome = SpecOutcome.Evaluates,
                ExpectedDisplay = Display(cell.InsideRaw),
                ExpectedRaw = cell.InsideRaw,
                ExpectedEmittedCount = 2,
                Notes = FamilyNote,
                Explanation = $"Exposure shape ({description}), read INSIDE the owner: `A` reaches the owner's `y` "
                    + "through this route, so it is local-only and each call of `F` computes its own `A`. An `A` "
                    + "classified exported would be evaluated detached from the call and refused, and before "
                    + "EXPORTED-DETACHED would have given both calls the first call's value.",
            };
            yield return new SpecCase
            {
                Id = $"exposure-shape-{shape}-outside",
                Category = "access-boundaries",
                Source = Program(cell, OutsideAfterCall),
                Outcome = SpecOutcome.EvalError,
                ExpectedErrorCategory = cell.OutsideError,
                Probes = [new SpecProbe(Program(cell, OutsideBeforeCall), $"err {cell.OutsideError}")],
                Notes = FamilyNote,
                Explanation = $"Exposure shape ({description}), read OUTSIDE the owner: `F.A` needs an activation of "
                    + "`F` that the access site does not have, so it is refused naming `A` — after a call of `F` "
                    + "(no entry of that call is reused) and, as the probe pins, before one.",
            };
        }
    }

    private const string FamilyNote =
        "EXPORTED-DETACHED exposure-shape family (November 2026): generated sources, hand-written expectations "
        + "(ExposureShapeSpecFamily.Cells).";

    /// <summary>The program of one cell followed by the given root output rows.</summary>
    internal static string Program(Cell cell, string rows)
    {
        var declarations = new List<string>();
        var opens = new List<string>();
        IReadOnlyList<string> target;
        switch (cell.Container)
        {
            case Container.Member:
                declarations.AddRange(Block("Lib", [.. SubDeclaration(cell.Capture), "0"]));
                target = ["Lib.Sub"];
                break;
            case Container.Reference:
                declarations.AddRange(Block("Lib", [.. SubDeclaration(cell.Capture), "0"]));
                declarations.Add("Ref = Lib");
                target = ["Ref.Sub"];
                break;
            case Container.Carrier:
                declarations.AddRange(Block("Base", ["0"]));
                declarations.AddRange(Block("Car", [.. SubDeclaration(cell.Capture), "Base"]));
                target = ["Car.Sub"];
                break;
            case Container.InlineHead:
                target = ["{", .. Indent(SubDeclaration(cell.Capture)), "}.Sub"];
                break;
            default:
                throw new InvalidOperationException(cell.Container.ToString());
        }

        IReadOnlyList<string> property;
        switch (cell.Route)
        {
            case Route.DotPath:
                property = Written("A = ", target, ".Q + 0");
                break;
            case Route.DottedOpen:
                property = ["A = {", .. Indent(Written("open ", target)), "  Q + 0", "}"];
                break;
            case Route.OpenOfReference:
                declarations.AddRange(Written("L = ", target));
                property = ["A = {", "  open L", "  Q + 0", "}"];
                break;
            case Route.EnclosingOpen:
                opens.AddRange(Written("open ", target));
                property = ["A = Q + 0"];
                break;
            default:
                throw new InvalidOperationException(cell.Route.ToString());
        }

        IEnumerable<string> lines =
            ["F(y) = {", .. Indent([.. opens, .. declarations, .. property, "A"]), "}", rows];
        return string.Join("\n", lines);
    }

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

    private static string Display(string raw)
        => raw switch
        {
            PerCallOne => "1\n1",
            PerCallValue => "5\n7",
            _ => throw new InvalidOperationException(raw),
        };

    private static string Slug(Container container)
        => container switch
        {
            Container.Member => "member",
            Container.Reference => "reference",
            Container.Carrier => "carrier",
            Container.InlineHead => "inline-head",
            _ => throw new InvalidOperationException(container.ToString()),
        };

    private static string Slug(Route route)
        => route switch
        {
            Route.DotPath => "dot-path",
            Route.DottedOpen => "dotted-open",
            Route.OpenOfReference => "open-of-reference",
            Route.EnclosingOpen => "enclosing-open",
            _ => throw new InvalidOperationException(route.ToString()),
        };

    private static string Slug(Capture capture)
        => capture == Capture.OutputRow ? "row-capture" : "member-capture";

    private static string Describe(Container container)
        => container switch
        {
            Container.Member => "`Sub` is a member of the block `Lib`",
            Container.Reference => "`Sub` is reached through the transparent reference `Ref = Lib`",
            Container.Carrier => "`Sub` is an own member of the forwarding carrier `Car = { … ⏎ Base }`",
            Container.InlineHead => "`Sub` is a member of an inline block head",
            _ => throw new InvalidOperationException(container.ToString()),
        };

    private static string Describe(Route route)
        => route switch
        {
            Route.DotPath => "`A` reads `Q` by a dot path",
            Route.DottedOpen => "`A`'s own body opens the path",
            Route.OpenOfReference => "`A`'s own body opens the reference `L`",
            Route.EnclosingOpen => "`A` reads `Q` through an open of the enclosing level",
            _ => throw new InvalidOperationException(route.ToString()),
        };

    private static string Describe(Capture capture)
        => capture == Capture.OutputRow
            ? "`Sub`'s output row reads `y`"
            : "`Sub`'s member `Q` reads `y`";

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
    // * the four CONTAINERS and the two CAPTURE positions of the family above;
    // * a PLACEMENT of the container — at the SITE (declared in `F`, so the branch's read of `y`
    //   through it is written in the program and charged; the module contributes the self-contained
    //   `K`), or in the MODULE the branch loads (so only the module decides that `Q` needs `y`: the
    //   uncharged, inadmissible shape). An inline block head is written in the branch itself and has
    //   no module placement;
    // * the access sites and row orders of the family above;
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
